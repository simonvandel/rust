// compile-flags: -Z mir-opt-level=2
// EMIT_MIR rustc.id.SimplifyArmIdentity.diff

enum MyResult<T,E>{
    Ok(T),
    Err(E)
}

fn id(r: Result<u8, i32>) -> MyResult<u8, i32> {
    match r {
        Ok(x) => MyResult::Ok(x),
        Err(y) => MyResult::Err(y),
    }
}

fn main() {
    id(Ok(2));
}
