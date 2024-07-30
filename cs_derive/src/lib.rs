#![allow(dead_code)]

use proc_macro::TokenStream;

mod allocatable;
mod selectable;
pub(crate) mod utils;
mod var_length_encodable;
mod witness_hook;
mod witness_var_length_encodable;

#[proc_macro_derive(CSSelectable, attributes(CSSelectableBound))]
#[proc_macro_error::proc_macro_error]
pub fn derive_selectable(input: TokenStream) -> TokenStream {
    self::selectable::derive_select(input)
}

#[proc_macro_derive(CSAllocatable, attributes(DerivePrettyComparison))]
#[proc_macro_error::proc_macro_error]
pub fn derive_allocatable(input: TokenStream) -> TokenStream {
    self::allocatable::derive_allocatable(input)
}

#[proc_macro_derive(WitnessHookable, attributes(WitnessHookBound))]
#[proc_macro_error::proc_macro_error]
pub fn derive_witness_hook(input: TokenStream) -> TokenStream {
    self::witness_hook::derive_witness_hook(input)
}

#[proc_macro_derive(CSVarLengthEncodable, attributes(CSVarLengthEncodableBound))]
#[proc_macro_error::proc_macro_error]
pub fn derive_var_length_encodable(input: TokenStream) -> TokenStream {
    self::var_length_encodable::derive_var_length_encodable(input)
}

#[proc_macro_derive(WitVarLengthEncodable, attributes(WitnessVarLengthEncodableBound))]
#[proc_macro_error::proc_macro_error]
pub fn derive_witness_length_encodable(input: TokenStream) -> TokenStream {
    self::witness_var_length_encodable::derive_witness_var_length_encodable(input)
}

use quote::quote;
use syn::{parse_macro_input, ItemFn, ReturnType};

#[proc_macro_attribute]
pub fn add_context_label(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);

    let func_name = &input_fn.sig.ident;
    let func_name_str = func_name.to_string();
    let ItemFn {
        attrs,
        vis,
        sig,
        block,
    } = input_fn;

    let return_expression = match &sig.output {
        ReturnType::Default => quote!(),
        _ => quote! { ret },
    };

    let gen = quote! {
        #(#attrs)*
        #vis #sig {
            cs.push_context_label(String::from(#func_name_str));
            let ret = (|| #block)();
            cs.pop_context_label();
            #return_expression
        }
    };

    gen.into()
}
