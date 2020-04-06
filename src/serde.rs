use crate::{Operation, OperationSeq};
use serde::{
    de::{self, Deserializer, SeqAccess, Visitor},
    ser::{SerializeSeq, Serializer},
    Deserialize, Serialize,
};
use std::fmt;

impl Serialize for Operation {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Operation::Retain(i) => serializer.serialize_u64(*i),
            Operation::Delete(i) => serializer.serialize_i64(-(*i as i64)),
            Operation::Insert(s) => serializer.serialize_str(s),
        }
    }
}

impl<'de> Deserialize<'de> for Operation {
    fn deserialize<D>(deserializer: D) -> Result<Operation, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct OperationVisitor;

        impl<'de> Visitor<'de> for OperationVisitor {
            type Value = Operation;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("an integer between -2^64 and 2^63 or a string")
            }

            fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Operation::Retain(value as u64))
            }

            fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Operation::Delete((-value) as u64))
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Operation::Insert(value.to_owned()))
            }
        }

        deserializer.deserialize_any(OperationVisitor)
    }
}

impl Serialize for OperationSeq {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.ops.len()))?;
        for op in self.ops.iter() {
            seq.serialize_element(op)?;
        }
        seq.end()
    }
}

impl<'de> Deserialize<'de> for OperationSeq {
    fn deserialize<D>(deserializer: D) -> Result<OperationSeq, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct OperationSeqVisitor;

        impl<'de> Visitor<'de> for OperationSeqVisitor {
            type Value = OperationSeq;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut o = OperationSeq::default();
                while let Some(op) = seq.next_element()? {
                    o.add(op);
                }
                Ok(o)
            }
        }

        deserializer.deserialize_seq(OperationSeqVisitor)
    }
}
