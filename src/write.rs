use crate::builtins::Value;

pub fn write_value(value: &Value) -> String {
    let mut res = Default::default();
    write_value_in(value, &mut res);
    return res;
}

pub fn write_value_pretty(value: &Value) -> String {
    let mut res = Default::default();
    write_value_pretty_in(value, &mut res, 0);
    return res;
}

pub fn as_hex(byte: u8) -> [char; 2] {
    fn hexdigit(byte: u8) -> char {
        (if byte < 10 {
            b'0' + byte
        } else {
            b'a' - 10 + byte
        }) as char
    }
    return [byte / 0x10, byte % 0x10].map(hexdigit);
}

fn write_value_in(value: &Value, sink: &mut String) {
    match value {
        Value::Bytes(eval_slice) => {
            sink.push('"');
            eval_slice.iter().for_each(|b| match *b {
                b'"' => sink.push_str("\\\""),
                b'\\' => sink.push_str("\\\\"),
                b @ b' '..=b'~' => sink.push(b as char),
                b => {
                    sink.push_str("\\x");
                    as_hex(b).into_iter().for_each(|c| sink.push(c));
                }
            });
            sink.push('"');
        }
        Value::Aggregate(eval_slice) => {
            sink.push('(');
            eval_slice.iter().enumerate().for_each(|(i, e)| {
                if i != 0 {
                    sink.push(' ')
                }
                write_value_in(e, sink);
            });
            sink.push(')');
        }
    }
}

fn write_padding_in(padding: u64, sink: &mut String) {
    (0..padding).for_each(|_| sink.push_str("    "));
}

fn write_value_pretty_in(value: &Value, sink: &mut String, padding: u64) {
    match value {
        Value::Bytes(eval_slice) => {
            write_padding_in(padding, sink);
            sink.push('"');
            eval_slice.iter().for_each(|b| match *b {
                b'"' => sink.push_str("\\\""),
                b'\\' => sink.push_str("\\\\"),
                b @ b' '..=b'~' => sink.push(b as char),
                b => {
                    sink.push_str("\\x");
                    as_hex(b).into_iter().for_each(|c| sink.push(c));
                }
            });
            sink.push_str("\"\n");
        }
        Value::Aggregate(eval_slice) => {
            write_padding_in(padding, sink);
            sink.push_str("(\n");
            eval_slice.iter().for_each(|e| {
                write_value_pretty_in(e, sink, padding + 1);
            });
            write_padding_in(padding, sink);
            sink.push_str(")\n");
        }
    }
}
