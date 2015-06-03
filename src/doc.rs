use std::cell::{RefCell, UnsafeCell};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt::{Display, Error, Formatter};
use std::rc::Rc;
use super::parser::{Builder, ParserError, ShowType};

type RcCell<T> = Rc<RefCell<T>>;

struct DocBuilder;
impl Builder for DocBuilder {
    type Table = Table;
    type Array = Array;
    type Key = Key;
    type Value = Value;

    fn table(lead_ws: &str)-> Table { Table::new(lead_ws.to_string()) }
    fn array(vals: Vec<Value>, lead_ws: &str) -> Array { unimplemented!() }
    fn key(val: String, lead_ws: &str) -> Key { Key::new(val) }
    fn value_string(parsed: String, raw: &str, lead_ws: &str) -> Value { unimplemented!() }
    fn value_integer(parsed: i64, raw: &str, lead_ws: &str) -> Value { unimplemented!() }
    fn value_float(parsed: f64, raw: &str, lead_ws: &str) -> Value  { unimplemented!() }
    fn value_boolean(parsed: bool, raw: &str, lead_ws: &str) -> Value  { unimplemented!() }
    fn value_datetime(parsed: String, raw: &str, lead_ws: &str) -> Value { unimplemented!() }
    fn value_array(parsed: Array, raw: &str, lead_ws: &str) -> Value  { unimplemented!() }
    fn value_table(parsed: Table, raw: &str, lead_ws: &str) -> Value  { Value::Table(parsed) }
    fn insert(table: &mut Table, key: Key, v: Value) -> bool  {
        table.insert(key, Box::new(UnsafeCell::new(v)))
    }
    fn insert_container<'b>(mut cur: &'b mut Table, keys: &[String],
                            key_lo: usize, key_hi: usize)
        -> Result<&'b mut Table, ParserError> {
        for part in keys {
            let tmp = cur;

            if tmp.map.contains_key(part) {
                match unsafe { &mut *tmp.map.get_mut(part).unwrap().get() } {
                    &mut Value::Table(ref mut table) => {
                        cur = table;
                        continue
                    }
                    &mut Value::Array(ref mut array) => {
                        match array.vec.last_mut() {
                            Some(&mut Value::Table(ref mut table)) => cur = table,
                            _ => {
                                return Err(ParserError {
                                    lo: key_lo,
                                    hi: key_hi,
                                    desc: format!("array `{}` does not contain \
                                                   tables", part)
                                });
                            }
                        }
                        continue
                    }
                    _ => {
                        return Err(ParserError {
                            lo: key_lo,
                            hi: key_hi,
                            desc: format!("key `{}` was not previously a table",
                                          part)
                        });
                    }
                }
            }

            // Initialize an empty table as part of this sub-key
            tmp.insert(DocBuilder::key(part.clone(), ""), Box::new(UnsafeCell::new(Value::Table(Table::null()))));
            match unsafe { &mut *tmp.map.get_mut(part).unwrap().get() } {
                &mut Value::Table(ref mut inner) => cur = inner,
                _ => unreachable!(),
            }
        }
        Ok(cur)

    }
    fn get_table<'b>(t: &'b mut Table, key: &'b str) -> Option<&'b mut Table>  { 
        t.map.get_mut::<'b>(key).and_then(|x| match unsafe { &mut *x.get() } { &mut Value::Table(ref mut s) => Some(s), _ => None })
    }
    fn get_array<'b>(t: &'b mut Table, key: &'b str) -> Option<&'b mut Array> { unimplemented!() }
    fn contains_table(t: &Table) -> bool  { 
        t.map.values().any(|v| if let &mut Value::Table(_) = unsafe { &mut *v.get() } { true } else { false })
    }
    fn merge(table: &mut Table, value: Table) -> Result<(), String> {
        for (k, v) in value.map.into_iter() {
            if !table.insert(DocBuilder::key(k.clone(), ""), v) {
                return Err(k);
            }
        }
        Ok(())
    }
    fn push<'b>(vec: &'b mut Array, value: Value) -> Result<(), &'b str>  { unimplemented!() }
    fn set_trailing_aux(table: &mut Table, aux: &str) {
        table.trail = aux.to_string();
    }
}

pub struct Table {
    map: HashMap<String, Box<UnsafeCell<Value>>>,
    vec: Vec<(Key, *mut UnsafeCell<Value>)>,
    lead: Option<String>, // anonymous tables contain no text
    trail: String
}

impl Table {
    fn new(s: String) -> Table {
        Table {
            map: HashMap::new(),
            vec: Vec::new(),
            lead: Some(s),
            trail: String::new()
        }
    }

    fn null() -> Table {
        Table {
            map: HashMap::new(),
            vec: Vec::new(),
            lead: None,
            trail: String::new()
        }
    }

    fn insert(&mut self, k: Key, mut value: Box<UnsafeCell<Value>>) -> bool {
        let key_string = k.text.clone();
        match self.map.entry(key_string) {
            Entry::Vacant(entry) => {
                self.vec.push((k, &mut *value));
                entry.insert(value);
                true
            },
            Entry::Occupied(_) => false
        }
    }

    fn print(&self, buf: &mut String) {
        buf.push_str(self.lead.as_ref().unwrap());
        for &(ref k, ref v) in self.vec.iter() {
            buf.push_str("[");
            k.print(buf);
            buf.push_str("]");
            unsafe { &*(**v).get() }.print(buf);
        }
        buf.push_str(&*self.trail);
    }
}

pub struct Array {
    vec: Vec<Value>
}


#[derive(PartialEq, Eq, Hash)]
enum KeyKind {
    Plain,
    Table
}
#[derive(PartialEq, Eq, Hash)]
pub struct Key {
    kind: KeyKind,
    text: String,
    lead: String,
    trail: String
}
impl Key {
    fn new(s: String) -> Key {
        Key {
            kind: KeyKind::Plain,
            text: s,
            lead: String::new(),
            trail: String::new()
        }
    }
    fn new_table(s: String) -> Key {
        Key {
            kind: KeyKind::Table,
            text: s,
            lead: String::new(),
            trail: String::new()
        }
    }

    fn print(&self, buf: &mut String) {
        buf.push_str(&*self.lead);
        buf.push_str(&*self.text);
        buf.push_str(&*self.trail);
    }
}

impl Display for Key {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        unimplemented!()
    }
}

pub enum Value {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Datetime(String),
    Array(Array),
    Table(Table),
}
impl ShowType for Value {
    fn type_str(&self) -> &'static str {
        unimplemented!()
    }
}
impl Value {
    fn print(&self, buf: &mut String) {
        match self {
            &Value::Table(ref t) => t.print(buf),
            _ => unimplemented!()
        }
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