use typed_arena::*;

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io;
use std::ops::{Add, BitAnd, Mul, Not, Shr, Sub};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DataType {
    Bool,
    I32,
}

struct Expr<'a> {
    arena: &'a Arena<Expr<'a>>,
    data: ExprData<'a>,
}

impl<'a> Expr<'a> {
    fn data_type(&self) -> DataType {
        self.data.data_type()
    }

    fn eq(&'a self, other: &'a Expr<'a>) -> &Expr<'a> {
        assert_eq!(self.data_type(), other.data_type());
        self.arena.alloc(Expr {
            arena: self.arena,
            data: ExprData::Eq {
                lhs: self,
                rhs: other,
            },
        })
    }

    fn ge(&'a self, other: &'a Expr<'a>) -> &Expr<'a> {
        assert_eq!(self.data_type(), DataType::I32);
        assert_eq!(other.data_type(), DataType::I32);
        self.arena.alloc(Expr {
            arena: self.arena,
            data: ExprData::Ge {
                lhs: self,
                rhs: other,
            },
        })
    }

    fn gt(&'a self, other: &'a Expr<'a>) -> &Expr<'a> {
        assert_eq!(self.data_type(), DataType::I32);
        assert_eq!(other.data_type(), DataType::I32);
        self.arena.alloc(Expr {
            arena: self.arena,
            data: ExprData::Gt {
                lhs: self,
                rhs: other,
            },
        })
    }

    fn lt(&'a self, other: &'a Expr<'a>) -> &Expr<'a> {
        assert_eq!(self.data_type(), DataType::I32);
        assert_eq!(other.data_type(), DataType::I32);
        self.arena.alloc(Expr {
            arena: self.arena,
            data: ExprData::Lt {
                lhs: self,
                rhs: other,
            },
        })
    }

    fn ne(&'a self, other: &'a Expr<'a>) -> &Expr<'a> {
        assert_eq!(self.data_type(), other.data_type());
        self.arena.alloc(Expr {
            arena: self.arena,
            data: ExprData::Not {
                expr: self.eq(other),
            },
        })
    }
}

impl<'a> Add<&'a Expr<'a>> for &'a Expr<'a> {
    type Output = &'a Expr<'a>;

    fn add(self, other: Self) -> Self::Output {
        assert_eq!(self.data_type(), DataType::I32);
        assert_eq!(other.data_type(), DataType::I32);
        self.arena.alloc(Expr {
            arena: self.arena,
            data: ExprData::Add {
                lhs: self,
                rhs: other,
            },
        })
    }
}

impl<'a> BitAnd<&'a Expr<'a>> for &'a Expr<'a> {
    type Output = &'a Expr<'a>;

    fn bitand(self, other: Self) -> Self::Output {
        assert_eq!(self.data_type(), DataType::Bool);
        assert_eq!(other.data_type(), DataType::Bool);
        self.arena.alloc(Expr {
            arena: self.arena,
            data: ExprData::And {
                lhs: self,
                rhs: other,
            },
        })
    }
}

impl<'a> Mul<&'a Expr<'a>> for &'a Expr<'a> {
    type Output = &'a Expr<'a>;

    fn mul(self, other: Self) -> Self::Output {
        assert_eq!(self.data_type(), DataType::I32);
        assert_eq!(other.data_type(), DataType::I32);
        self.arena.alloc(Expr {
            arena: self.arena,
            data: ExprData::Mul {
                lhs: self,
                rhs: other,
            },
        })
    }
}

impl<'a> Not for &'a Expr<'a> {
    type Output = &'a Expr<'a>;

    fn not(self) -> Self::Output {
        assert_eq!(self.data_type(), DataType::Bool);
        self.arena.alloc(Expr {
            arena: self.arena,
            data: ExprData::Not { expr: self },
        })
    }
}

impl<'a> Shr<u32> for &'a Expr<'a> {
    type Output = &'a Expr<'a>;

    fn shr(self, other: u32) -> Self::Output {
        assert_eq!(self.data_type(), DataType::I32);
        self.arena.alloc(Expr {
            arena: self.arena,
            data: ExprData::Shr {
                lhs: self,
                rhs: self.arena.alloc(Expr {
                    arena: self.arena,
                    data: ExprData::ConstI32 { value: other as _ },
                }),
            },
        })
    }
}

impl<'a> Sub<&'a Expr<'a>> for &'a Expr<'a> {
    type Output = &'a Expr<'a>;

    fn sub(self, other: Self) -> Self::Output {
        assert_eq!(self.data_type(), DataType::I32);
        assert_eq!(other.data_type(), DataType::I32);
        self.arena.alloc(Expr {
            arena: self.arena,
            data: ExprData::Sub {
                lhs: self,
                rhs: other,
            },
        })
    }
}

enum ExprData<'a> {
    Add { lhs: &'a Expr<'a>, rhs: &'a Expr<'a> },
    And { lhs: &'a Expr<'a>, rhs: &'a Expr<'a> },
    ConstI32 { value: i32 },
    Eq { lhs: &'a Expr<'a>, rhs: &'a Expr<'a> },
    Ge { lhs: &'a Expr<'a>, rhs: &'a Expr<'a> },
    Gt { lhs: &'a Expr<'a>, rhs: &'a Expr<'a> },
    Lt { lhs: &'a Expr<'a>, rhs: &'a Expr<'a> },
    Mul { lhs: &'a Expr<'a>, rhs: &'a Expr<'a> },
    Not { expr: &'a Expr<'a> },
    Shr { lhs: &'a Expr<'a>, rhs: &'a Expr<'a> },
    Sub { lhs: &'a Expr<'a>, rhs: &'a Expr<'a> },
    Var { name: String, data_type: DataType },
}

impl<'a> ExprData<'a> {
    fn data_type(&self) -> DataType {
        match self {
            ExprData::Add { .. } => DataType::I32,
            ExprData::And { .. } => DataType::Bool,
            ExprData::ConstI32 { .. } => DataType::I32,
            ExprData::Eq { .. } => DataType::Bool,
            ExprData::Ge { .. } => DataType::Bool,
            ExprData::Gt { .. } => DataType::Bool,
            ExprData::Lt { .. } => DataType::Bool,
            ExprData::Mul { .. } => DataType::I32,
            ExprData::Not { .. } => DataType::Bool,
            ExprData::Shr { .. } => DataType::I32,
            ExprData::Sub { .. } => DataType::I32,
            ExprData::Var { data_type, .. } => *data_type,
        }
    }
}

struct Context<'a> {
    expr_arena: Arena<Expr<'a>>,
    vars: RefCell<BTreeMap<String, DataType>>,
    assertions: RefCell<Vec<&'a Expr<'a>>>,
}

impl<'a> Context<'a> {
    fn new() -> Context<'a> {
        Context {
            expr_arena: Arena::new(),
            vars: RefCell::new(BTreeMap::new()),
            assertions: RefCell::new(Vec::new()),
        }
    }

    fn const_i32(&'a self, value: i32) -> &Expr<'a> {
        self.expr_arena.alloc(Expr {
            arena: &self.expr_arena,
            data: ExprData::ConstI32 { value },
        })
    }

    fn var_bool(&'a self, name: impl Into<String>) -> &Expr<'a> {
        let name = name.into();

        self.var(name, DataType::Bool)
    }

    fn var_i32(&'a self, name: impl Into<String>) -> &Expr<'a> {
        let name = name.into();

        self.var(name, DataType::I32)
    }

    fn var(&'a self, name: String, data_type: DataType) -> &'a Expr<'a> {
        let mut vars = self.vars.borrow_mut();
        if vars.contains_key(&name) {
            panic!("Duplicated var name: {}", name);
        }

        vars.insert(name.clone(), data_type);

        self.expr_arena.alloc(Expr {
            arena: &self.expr_arena,
            data: ExprData::Var { name, data_type },
        })
    }

    fn assert(&'a self, expr: &'a Expr<'a>) {
        assert_eq!(expr.data_type(), DataType::Bool);
        self.assertions.borrow_mut().push(expr);
    }

    fn write_smt2(&self, mut w: impl io::Write) -> io::Result<()> {
        writeln!(w, "(set-logic QF_BV)")?;

        for (name, data_type) in self.vars.borrow().iter() {
            write!(w, "(declare-const {} ", name)?;
            match data_type {
                DataType::Bool => {
                    write!(w, "Bool")?;
                }
                DataType::I32 => {
                    write!(w, "(_ BitVec 32)")?;
                }
            }
            writeln!(w, ")")?;
        }

        struct CodegenContext;

        impl CodegenContext {
            fn visit<'a>(&mut self, expr: &'a Expr<'a>, w: &mut impl io::Write) -> io::Result<()> {
                match &expr.data {
                    ExprData::Add { lhs, rhs } => {
                        write!(w, "(bvadd ")?;
                        self.visit(lhs, w)?;
                        write!(w, " ")?;
                        self.visit(rhs, w)?;
                        write!(w, ")")?;
                    }
                    ExprData::And { lhs, rhs } => {
                        write!(w, "(and ")?;
                        self.visit(lhs, w)?;
                        write!(w, " ")?;
                        self.visit(rhs, w)?;
                        write!(w, ")")?;
                    }
                    ExprData::ConstI32 { value } => {
                        write!(w, "(_ bv{} 32)", *value as u32)?;
                    }
                    ExprData::Eq { lhs, rhs } => {
                        write!(w, "(= ")?;
                        self.visit(lhs, w)?;
                        write!(w, " ")?;
                        self.visit(rhs, w)?;
                        write!(w, ")")?;
                    }
                    ExprData::Ge { lhs, rhs } => {
                        write!(w, "(bvsge ")?;
                        self.visit(lhs, w)?;
                        write!(w, " ")?;
                        self.visit(rhs, w)?;
                        write!(w, ")")?;
                    }
                    ExprData::Gt { lhs, rhs } => {
                        write!(w, "(bvsgt ")?;
                        self.visit(lhs, w)?;
                        write!(w, " ")?;
                        self.visit(rhs, w)?;
                        write!(w, ")")?;
                    }
                    ExprData::Lt { lhs, rhs } => {
                        write!(w, "(bvslt ")?;
                        self.visit(lhs, w)?;
                        write!(w, " ")?;
                        self.visit(rhs, w)?;
                        write!(w, ")")?;
                    }
                    ExprData::Mul { lhs, rhs } => {
                        write!(w, "(bvmul ")?;
                        self.visit(lhs, w)?;
                        write!(w, " ")?;
                        self.visit(rhs, w)?;
                        write!(w, ")")?;
                    }
                    ExprData::Not { expr } => {
                        write!(w, "(not ")?;
                        self.visit(expr, w)?;
                        write!(w, ")")?;
                    }
                    ExprData::Shr { lhs, rhs } => {
                        write!(w, "(bvashr ")?;
                        self.visit(lhs, w)?;
                        write!(w, " ")?;
                        self.visit(rhs, w)?;
                        write!(w, ")")?;
                    }
                    ExprData::Sub { lhs, rhs } => {
                        write!(w, "(bvsub ")?;
                        self.visit(lhs, w)?;
                        write!(w, " ")?;
                        self.visit(rhs, w)?;
                        write!(w, ")")?;
                    }
                    ExprData::Var { name, .. } => {
                        write!(w, "{}", name)?;
                    }
                }

                Ok(())
            }
        }

        let mut c = CodegenContext;

        for assertion in self.assertions.borrow().iter() {
            write!(w, "(assert ")?;
            c.visit(assertion, &mut w)?;
            writeln!(w, ")")?;
        }

        writeln!(w, "(check-sat)")?;
        writeln!(w, "(get-model)")?;

        Ok(())
    }
}

const EDGE_FRACT_BITS: u32 = 3;

fn orient2d<'a>(
    ax: &'a Expr<'a>,
    ay: &'a Expr<'a>,
    bx: &'a Expr<'a>,
    by: &'a Expr<'a>,
    cx: &'a Expr<'a>,
    cy: &'a Expr<'a>,
) -> &'a Expr<'a> {
    (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)
}

fn coverage<'a>(
    x1: &'a Expr<'a>,
    y1: &'a Expr<'a>,
    x2: &'a Expr<'a>,
    y2: &'a Expr<'a>,
    sample_x: &'a Expr<'a>,
    sample_y: &'a Expr<'a>,
    fill_rule_bias: &'a Expr<'a>,
    c: &'a Context<'a>,
) -> &'a Expr<'a> {
    // Shift _after_ bias is the key!
    ((orient2d(x1, y1, x2, y2, sample_x, sample_y) + fill_rule_bias) >> EDGE_FRACT_BITS).ge(c.const_i32(0))
}

fn main() -> io::Result<()> {
    let c = Context::new();

    // Edge coords
    let x1 = c.var_i32("x1");
    let y1 = c.var_i32("y1");
    let x2 = c.var_i32("x2");
    let y2 = c.var_i32("y2");

    // Sample coords
    let sample_x = c.var_i32("sample_x");
    let sample_y = c.var_i32("sample_y");

    // Coverages
    let coverage_a = c.var_bool("coverage_a");
    let coverage_b = c.var_bool("coverage_b");

    // Avoid degenerate cases
    c.assert(!(x1.eq(x2) & y1.eq(y2)));

    // Limit "viewport" bounds to ease interpretation
    /*let bound_lower = c.const_i32(-8);
    let bound_upper = c.const_i32(8);
    c.assert(x1.gt(bound_lower) & x1.lt(bound_upper));
    c.assert(y1.gt(bound_lower) & y1.lt(bound_upper));
    c.assert(x2.gt(bound_lower) & x2.lt(bound_upper));
    c.assert(y2.gt(bound_lower) & y2.lt(bound_upper));
    c.assert(sample_x.gt(bound_lower) & sample_x.lt(bound_upper));
    c.assert(sample_y.gt(bound_lower) & sample_y.lt(bound_upper));*/

    // Calculate coverage from both orientations
    //  We pick one of the two to be biased. It shouldn't matter that this isn't an actual fill rule impl.
    c.assert(coverage_a.eq(coverage(x1, y1, x2, y2, sample_x, sample_y, c.const_i32(0), &c)));
    c.assert(coverage_b.eq(coverage(x2, y2, x1, y1, sample_x, sample_y, c.const_i32(-1), &c)));

    // The invariant we want to check for is that each pixel is covered exactly once, so we'll use the
    //  complement of that condition to ensure the solver finds a counterexample.
    c.assert(coverage_a.eq(coverage_b));

    c.write_smt2(io::stdout())
}
