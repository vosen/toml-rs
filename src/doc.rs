use std::cell::{RefCell, UnsafeCell};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt::{Display, Error, Formatter};
use std::rc::Rc;
use super::parser::{Builder, ParserError, ShowType};

pub struct ContainerData {
    direct_children_vec: Vec<(Key, Rc<DirectChild>)>,
    direct_children_map: HashMap<String, Rc<DirectChild>>,
    indirect_children: HashMap<String, Rc<Container>>
}
impl ContainerData {
    fn new() -> ContainerData {
        ContainerData {
            direct_children_vec: Vec::new(),
            direct_children_map: HashMap::new(),
            indirect_children: HashMap::new()
        }
    }

    fn print(&self, buf: &mut String) {

    }
}

enum ContainerKind {
    Root,
    Table,
    Array,
}

struct Container {
    kind: ContainerKind,
    data: ContainerData,
    lead: String
}
impl Container {
    fn new(k: ContainerKind, s: String) -> Container {
        Container {
            kind: k,
            data: ContainerData::new(),
            lead: s
        }
    }

    fn print(&self, buf: &mut String) {
        buf.push_str(&*self.lead);
        match self.kind {
            ContainerKind::Table => buf.push_str("["),
            ContainerKind::Array => buf.push_str("[["),
            ContainerKind::Root => {}
        }
        self.data.print(buf);
        match self.kind {
            ContainerKind::Table => buf.push_str("]"),
            ContainerKind::Array => buf.push_str("]]"),
            ContainerKind::Root => {}
        }
    }
}


enum DirectChild {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Datetime(String),
    Array(Vec<ArrayElement>),
    InlineTable(Container),
}

enum ArrayElement {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Datetime(String),
    Array(Vec<ArrayElement>),
}

#[derive(PartialEq, Eq, Hash)]
pub struct Key {
    text: String,
    lead: String,
    trail: String
}

impl Display for Key {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        unimplemented!()
    }
}

impl ShowType for () {
    fn type_str(&self) -> &'static str {
        unimplemented!()
    }
}

struct DocBuilder;
impl Builder for DocBuilder {
    type Table = Container;
    type Array = Container;
    type Key = Key;
    type Value = ();

    fn root_table(lead_ws: &str) -> Self::Table { Container::new(ContainerKind::Root, lead_ws.to_string()) }
    fn table(lead_ws: &str) -> Self::Table { Container::new(ContainerKind::Table, lead_ws.to_string()) }
    fn array(vals: Vec<Self::Value>, lead_ws: &str) -> Self::Array { unimplemented!() }
    fn key(val: String, lead_ws: &str) -> Self::Key { unimplemented!()}
    fn value_string(parsed: String, raw: &str, lead_ws: &str) -> Self::Value { unimplemented!() }
    fn value_integer(parsed: i64, raw: &str, lead_ws: &str) -> Self::Value { unimplemented!() }
    fn value_float(parsed: f64, raw: &str, lead_ws: &str) -> Self::Value  { unimplemented!() }
    fn value_boolean(parsed: bool, raw: &str, lead_ws: &str) -> Self::Value  { unimplemented!() }
    fn value_datetime(parsed: String, raw: &str, lead_ws: &str) -> Self::Value { unimplemented!() }
    fn value_array(parsed: Self::Array, raw: &str, lead_ws: &str) -> Self::Value  { unimplemented!() }
    fn value_table(parsed: Self::Table, raw: &str, lead_ws: &str) -> Self::Value  { unimplemented!() }
    fn insert(table: &mut Self::Table, key: Self::Key, v: Self::Value) -> bool  {
        unimplemented!()
    }
    fn insert_container<'b>(mut cur: &'b mut Self::Table, keys: &[String],
                            key_lo: usize, key_hi: usize)
        -> Result<&'b mut Self::Table, ParserError> {
        unimplemented!()

    }
    fn get_table<'b>(t: &'b mut Self::Table, key: &'b str) -> Option<&'b mut Self::Table>  { 
        unimplemented!()
    }
    fn get_array<'b>(t: &'b mut Self::Table, key: &'b str) -> Option<&'b mut Self::Array> { unimplemented!() }
    fn contains_table(t: &Self::Table) -> bool  { 
        unimplemented!()
    }
    fn merge(table: &mut Self::Table, value: Self::Table) -> Result<(), String> {
        unimplemented!()
    }
    fn push<'b>(vec: &'b mut Self::Array, value: Self::Value) -> Result<(), &'b str>  { unimplemented!() }
    fn set_trailing_aux(table: &mut Self::Table, aux: &str) {
        unimplemented!()
    }
}

#[cfg(test)]
mod test {
    use super::DocBuilder;
    use super::super::parser::ParseSession;

    macro_rules! round_trip {
        ($text: expr) => ({
            let mut p = ParseSession::new($text, DocBuilder);
            let table = p.parse().unwrap();
            let mut buf = String::new();
            table.print(&mut buf);
            println!("\"{}\"", buf);
            assert!($text == buf);
        })
    }

    #[test]
    fn empty() { round_trip!("  #asd \n ") }
    #[test]
    fn single_table() { round_trip!("  #asd\t  \n [a] \t \n\n  #asdasdad\n ") }

}