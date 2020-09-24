// compile-flags: -Z mir-opt-level=3
// EMIT_MIR early_otherwise_branch.opt1.EarlyOtherwiseBranch.diff
fn opt1(x: Option<u32>, y: Option<u32>) -> u32 {
    match (x, y) {
        (Some(a), Some(b)) => 0,
        _ => 1,
    }
}

// EMIT_MIR early_otherwise_branch.opt2.EarlyOtherwiseBranch.diff
fn opt2(x: Option<u32>, y: Option<u32>) -> u32 {
    match (x, y) {
        (Some(a), Some(b)) => 0,
        (None, None) => 0,
        _ => 1,
    }
}

enum MyOption1<T> {
    Some(T),
    None,
}

enum MyOption2<T> {
    Some(T),
    None,
}

// must optimize as the tag encoding of the discriminant are the same
// EMIT_MIR early_otherwise_branch.opt3.EarlyOtherwiseBranch.diff
fn opt3(x: MyOption1<u32>, y: MyOption2<u32>) -> u32 {
    match (x, y) {
        (MyOption1::Some(a), MyOption2::Some(b)) => 0,
        _ => 1,
    }
}

fn main() {
    opt1(None, Some(0));
    opt2(None, Some(0));
    opt3(MyOption1::None, MyOption2::Some(0));
}
