// EMIT_MIR remove_deref.simple_opt.RemoveDeref.diff
fn simple_opt() -> u64 {
    let x = 5;
    let y = &x;
    let z = *y;
    z
}

// EMIT_MIR remove_deref.deep_opt.RemoveDeref.diff
fn deep_opt() -> (u64, u64, u64) {
    let x1 = 1;
    let x2 = 2;
    let x3 = 3;
    let y1 = &x1;
    let y2 = &x2;
    let y3 = &x3;
    let z1 = *y1;
    let z2 = *y2;
    let z3 = *y3;
    (z1, z2, z3)
}

struct S {
    a: u64,
    b: u64,
}

// EMIT_MIR remove_deref.opt_struct.RemoveDeref.diff
fn opt_struct(s: S) -> u64 {
    let a = &s.a;
    let b = &s.b;
    let x = *a;
    *b + x
}

// EMIT_MIR remove_deref.dont_opt.RemoveDeref.diff
// do not optimize a sequence looking like this:
// _1 = &_2;
// _1 = _3;
// _4 = *_1;
// as the _1 = _3 assignment makes it not legal to replace the last statement with _4 = _2
fn dont_opt() -> u64 {
    let y = 5;
    let _ref = &y;
    let x = 5;
    let mut _1 = &x;
    _1 = _ref;
    let _4 = *_1;
    0
}

// EMIT_MIR remove_deref.do_not_miscompile.RemoveDeref.diff
fn do_not_miscompile() {
    let x = 42;
    let a = 99;
    let mut y = &x;
    let z = &mut y;
    *z = &a;
    assert!(*y == 99);
}

fn main() {
    simple_opt();
    deep_opt();
    opt_struct(S { a: 0, b: 1 });
    dont_opt();
    do_not_miscompile();
}
