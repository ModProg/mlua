use itertools::Itertools;
use proc_macro::TokenStream;
use proc_macro2::{Ident, Span};
use proc_macro_error::{abort, ResultExt};
use quote::{quote, ToTokens};
use quote_use::{format_ident_namespaced, quote_use};
use syn::{
    parse_macro_input, parse_quote, parse_quote_spanned, punctuated::Punctuated, spanned::Spanned,
    Attribute, AttributeArgs, DataEnum, DataStruct, DataUnion, DeriveInput, Error, Expr, Field,
    Fields, FieldsNamed, FieldsUnnamed, ItemFn, Token, Variant,
};

#[cfg(feature = "macros")]
use {
    crate::chunk::Chunk, proc_macro::TokenTree, proc_macro2::TokenStream as TokenStream2,
    proc_macro_error::proc_macro_error,
};

#[proc_macro_attribute]
pub fn lua_module(attr: TokenStream, item: TokenStream) -> TokenStream {
    let args = parse_macro_input!(attr as AttributeArgs);
    let func = parse_macro_input!(item as ItemFn);

    if !args.is_empty() {
        let err = Error::new(Span::call_site(), "the macro does not support arguments")
            .to_compile_error();
        return err.into();
    }

    let func_name = func.sig.ident.clone();
    let ext_entrypoint_name = Ident::new(&format!("luaopen_{}", func_name), Span::call_site());

    let wrapped = quote! {
        ::mlua::require_module_feature!();

        #func

        #[no_mangle]
        unsafe extern "C" fn #ext_entrypoint_name(state: *mut ::mlua::lua_State) -> ::std::os::raw::c_int {
            ::mlua::Lua::init_from_ptr(state)
                .entrypoint1(#func_name)
                .expect("cannot initialize module")
        }
    };

    wrapped.into()
}

#[cfg(feature = "macros")]
fn to_ident(tt: &TokenTree) -> TokenStream2 {
    let s: TokenStream = tt.clone().into();
    s.into()
}

#[cfg(feature = "macros")]
#[proc_macro]
#[proc_macro_error]
pub fn chunk(input: TokenStream) -> TokenStream {
    let chunk = Chunk::new(input);

    let source = chunk.source();

    let caps_len = chunk.captures().len();
    let caps = chunk.captures().iter().map(|cap| {
        let cap_name = cap.as_rust().to_string();
        let cap = to_ident(cap.as_rust());
        quote! { env.raw_set(#cap_name, #cap)?; }
    });

    let wrapped_code = quote! {{
        use ::mlua::{AsChunk, ChunkMode, Lua, Result, Value};
        use ::std::borrow::Cow;
        use ::std::io::Result as IoResult;
        use ::std::marker::PhantomData;
        use ::std::sync::Mutex;

        fn annotate<'a, F: FnOnce(&'a Lua) -> Result<Value<'a>>>(f: F) -> F { f }

        struct InnerChunk<'a, F: FnOnce(&'a Lua) -> Result<Value<'a>>>(Mutex<Option<F>>, PhantomData<&'a ()>);

        impl<'lua, F> AsChunk<'lua> for InnerChunk<'lua, F>
        where
            F: FnOnce(&'lua Lua) -> Result<Value<'lua>>,
        {
            fn source(&self) -> IoResult<Cow<[u8]>> {
                Ok(Cow::Borrowed((#source).as_bytes()))
            }

            fn env(&self, lua: &'lua Lua) -> Result<Option<Value<'lua>>> {
                if #caps_len > 0 {
                    if let Ok(mut make_env) = self.0.lock() {
                        if let Some(make_env) = make_env.take() {
                            return make_env(lua).map(Some);
                        }
                    }
                }
                Ok(None)
            }

            fn mode(&self) -> Option<ChunkMode> {
                Some(ChunkMode::Text)
            }
        }

        let make_env = annotate(move |lua: &Lua| -> Result<Value> {
            let globals = lua.globals();
            let env = lua.create_table()?;
            let meta = lua.create_table()?;
            meta.raw_set("__index", globals.clone())?;
            meta.raw_set("__newindex", globals)?;

            // Add captured variables
            #(#caps)*

            env.set_metatable(Some(meta));
            Ok(Value::Table(env))
        });

        &InnerChunk(Mutex::new(Some(make_env)), PhantomData)
    }};

    wrapped_code.into()
}

fn should_skip_field(attrs: &[Attribute]) -> bool {
    let attr = attrs.iter().find(|attr| attr.path.is_ident("mlua"));
    // TODO handle multiple attributes

    attr.and_then(|attr| attr.parse_args().ok())
        .map_or(false, |ident: Ident| ident == "lua" || ident == "skip")
}

fn named_fields_to_lua(fields: impl IntoIterator<Item = Field>) -> TokenStream2 {
    let (right, left): (Vec<_>, Vec<_>) = fields
        .into_iter()
        .filter_map(|Field { ident, attrs, .. }| {
            (!should_skip_field(&attrs)).then(|| {
                let ident = ident.expect("named fields always have idents");
                let ident_str = ident.to_string();
                (quote_use!($value.set(#ident_str, #ident)?;), ident)
            })
        })
        .unzip();
    let count = left.len() as i32;

    quote_use! {
        # use mlua::prelude::LuaValue;
        {#(#left),*} => {
            let $value = lua.create_table_with_capacity(0, #count)?;
            #(#right)*
            LuaValue::Table($value)
        }
    }
}

fn unnamed_fields_to_lua(fields: impl IntoIterator<Item = Field>) -> TokenStream2 {
    let (right, left): (Vec<_>, Vec<_>) = fields
        .into_iter()
        .enumerate()
        .filter_map(|(i, Field { attrs, .. })| {
            (!should_skip_field(&attrs)).then(|| {
                let ident = format_ident_namespaced!("$field_{i}");
                (quote_use!(::mlua::ToLua(#ident)?), ident)
            })
        })
        .unzip();
    quote_use! {
        # use mlua::prelude::LuaValue;
        (#(#left),*) => Ok(LuaValue::Table(lua.create_sequence_from([#(#right),*])))
    }
}

#[proc_macro_error]
#[proc_macro_derive(ToLua, attributes(mlua))]
pub fn to_lua(item: TokenStream) -> TokenStream {
    let DeriveInput {
        ident,
        mut generics,
        data,
        ..
    } = parse_macro_input!(item as DeriveInput);

    let body = match data {
        syn::Data::Struct(DataStruct {
            fields: Fields::Named(FieldsNamed { named, .. }),
            ..
        }) => {
            let named = named_fields_to_lua(named);
            quote_use!(Self #named)
        }
        syn::Data::Struct(DataStruct {
            fields: Fields::Unnamed(FieldsUnnamed { unnamed, .. }),
            ..
        }) => {
            let unnamed = unnamed_fields_to_lua(unnamed);
            quote_use!(Self #unnamed)
        }
        syn::Data::Struct(DataStruct {
            fields: Fields::Unit,
            ..
        }) => abort!(ident, "unit structs are not supported"),
        syn::Data::Enum(DataEnum { variants, .. }) => {
            variants.into_iter().map(
                |Variant {
                     ident,
                     fields,
                     discriminant,
                     attrs
                 }| {
                    match fields {
                        Fields::Named(FieldsNamed { named, .. }) => {
                            let named = named_fields_to_lua(named);
                            quote_use!(Self::#ident #named)
                        }
                        Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => {
                            if unnamed.len() == 1 {
                                quote_use!(Self::#ident($field) => ::mlua::ToLua::to_lua($field, lua)?)
                            } else {
                                let unnamed = unnamed_fields_to_lua(unnamed);
                                quote_use!(#ident #unnamed)
                            }
                        }
                        Fields::Unit => {
                            use attribute_derive::Attribute;
                            #[derive(Attribute)]
                            #[attribute(ident = "mlua")]
                            struct Attr {
                                value: Option<Expr>
                            }
                            let Attr{value} = Attr::from_attributes(&attrs).unwrap_or_abort();
                            // TODO casing/explicit value/int repr
                            let value = value.map(ToTokens::into_token_stream).unwrap_or_else(|| if let Some((_, discriminant)) = discriminant {
                                discriminant.into_token_stream()
                            } else {
                                ident.to_string().into_token_stream()
                            });
                            quote_use!(Self::#ident => ::mlua::ToLua::to_lua(#value, lua)?)
                        }
                    }
                },
            ).collect::<Punctuated<_, Token![,]>>().into_token_stream()
        }
        syn::Data::Union(DataUnion { union_token, .. }) => {
            abort!(union_token, "unions are not supported")
        }
    };

    // Setup lifetimes and generics
    let generics_clone = generics.clone();
    let (_, type_generics, _) = generics_clone.split_for_impl();

    let lifetimes = generics.lifetimes().cloned().collect_vec();
    for lifetime in lifetimes {
        generics
            .make_where_clause()
            .predicates
            .push(parse_quote_spanned!(lifetime.span()=> #lifetime: '__lua))
    }

    let mut generics = generics.clone();
    generics.params.push(parse_quote!('__lua));
    let (impl_generics, _, where_clause) = generics.split_for_impl();

    quote_use! {
        # use mlua::{prelude::{Lua, LuaResult, LuaValue}, ToLua};

        #[allow(unreachable_code)]
        impl #impl_generics ToLua<'__lua> for #ident #type_generics #where_clause {
            fn to_lua(self, lua: &'__lua Lua) -> LuaResult<LuaValue<'__lua>> {
                Ok(match self {
                    #body
                })
            }
        }
    }
    .into()
}

#[proc_macro_error]
#[proc_macro_derive(FromLua, attributes(mlua))]
pub fn from_lua(item: TokenStream) -> TokenStream {
    let DeriveInput {
        ident,
        mut generics,
        data,
        ..
    } = parse_macro_input!(item as DeriveInput);

    let mut lua = None;

    let fields = match data {
        syn::Data::Struct(DataStruct {
            fields: Fields::Named(FieldsNamed { named: fields, .. }),
            ..
        }) => {
            let fields = fields.into_iter().map(|Field { ident, attrs, .. }| {
            let ident = ident.expect("named fields always have idents");
            let attr = attrs
                .into_iter()
                .find(|attr| attr.path.is_ident("mlua"));
            // TODO handle multiple attributes
            if matches!(&attr, Some(attr) if matches!(attr.parse_args::<Ident>(), Ok(ident) if ident == "lua")) {
                lua = Some(ident.clone());
                quote_use!(#ident: lua)
            } else {
                let ident_str = ident.to_string();
                quote_use!(#ident: $value.get(#ident_str)?)
            }}).collect_vec();
            quote!({#(#fields),*})
        }
        // TODO verify len
        syn::Data::Struct(DataStruct {
            fields: Fields::Unnamed(fields),
            ..
        }) => {
            let fields = fields
                .unnamed
                .into_iter()
                .enumerate()
                .map(|(idx, _)| quote_use!($value.get(#idx)?))
                .collect_vec();
            quote!((#(#fields),*))
        }
        syn::Data::Struct(DataStruct {
            fields: Fields::Unit,
            ..
        }) => abort!(ident, "unit structs are not supported"),
        syn::Data::Enum(DataEnum { enum_token, .. }) => {
            abort!(enum_token, "enums are not (yet) supported")
        }
        syn::Data::Union(DataUnion { union_token, .. }) => {
            abort!(union_token, "unions are not supported")
        }
    };

    let generics_clone = generics.clone();
    let (_, type_generics, _) = generics_clone.split_for_impl();

    // Setup lifetimes and generics
    let lifetimes = generics.lifetimes().cloned().collect_vec();
    for lifetime in lifetimes {
        generics
            .make_where_clause()
            .predicates
            .push(parse_quote_spanned!(lifetime.span()=> '__lua: #lifetime))
    }

    let mut generics = generics.clone();
    generics.params.push(parse_quote!('__lua));
    let (impl_generics, _, where_clause) = generics.split_for_impl();

    quote_use! {
        # use mlua::prelude::{FromLua, Lua, LuaResult, LuaTable, LuaValue};

        #[allow(unreachable_code)]
        impl #impl_generics FromLua<'__lua> for #ident #type_generics #where_clause {
            fn from_lua($value: LuaValue<'__lua>, lua: &'__lua Lua) -> LuaResult<Self> {
                let $value: LuaTable = FromLua::from_lua($value, lua)?;
                Ok(Self #fields)
            }
        }
    }
    .into()
}

#[cfg(feature = "macros")]
mod chunk;
#[cfg(feature = "macros")]
mod token;
