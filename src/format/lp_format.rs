use std::fs::File;
use std::io::prelude::*;
use std::io::Result;

use dsl::*;
use dsl::Constraint::*;
use dsl::LpExpression::*;

pub trait LpFileFormat {
    fn format<W: std::fmt::Write>(&self, w: &mut W) -> std::fmt::Result;

    fn to_lp_file_format(&self) -> String {
        let mut buffer = String::new();
        self.format(&mut buffer).unwrap();
        buffer
    }

    fn write_lp(&self, file_model: &str) -> Result<()> {
        let mut buffer = File::create(file_model)?;
        buffer.write(self.to_lp_file_format().as_bytes())?;
        Ok(())
    }
}

impl LpFileFormat for LpProblem {

    fn format<W: std::fmt::Write>(&self, w: &mut W) -> std::fmt::Result {
        write!(w, "\\ {}\n\n", &self.name)?;

        format_objective_lp_file_block(self, w)?;

        write!(w, "\n\nSubject To\n")?; // TODO: check emptyness
        format_constraints_lp_file_block(self, w)?;

        writeln!(w, "\nBounds")?; // TODO: check emptyness
        format_bounds_lp_file_block(self, w)?;

        write!(w, "\nGenerals\n  ")?; // TODO: check emptyness
        format_integers_lp_file_block(self, w)?;

        write!(w, "\nBinary\n  ")?; // TODO: check emptyness
        format_binaries_lp_file_block(self, w)?;

        write!(w, "\nEnd")
    }
}

fn format_objective_lp_file_block<W: std::fmt::Write>(
        prob: &LpProblem, w: &mut W) -> std::fmt::Result {
    // Write objectives
    let obj_type = match prob.objective_type {
        LpObjective::Maximize => "Maximize\n  ",
        LpObjective::Minimize => "Minimize\n  "
    };
    match prob.obj_expr {
        Some(ref expr) => {
            write!(w, "{}obj: ", obj_type)?; 
            expr.format(w)
        },
        _ => Ok(()),
    }
}

fn format_constraints_lp_file_block<W: std::fmt::Write>(
        prob: &LpProblem, w: &mut W) -> std::fmt::Result {
    let mut constraints = prob.constraints.iter();
    let mut index = 1;
    while let Some(ref constraint) = constraints.next() {
        write!(w, "  c{}: ", index.to_string())?;
        constraint.format(w)?;
        writeln!(w)?;
        index += 1;
    }
    Ok(())
}

fn format_bounds_lp_file_block<W: std::fmt::Write>(
        prob: &LpProblem, w: &mut W) -> std::fmt::Result {
    for (_, v) in prob.variables() {
        match v {
            &ConsInt(LpInteger {
                         ref name,
                         lower_bound,
                         upper_bound,
                     })
            | &ConsCont(LpContinuous {
                            ref name,
                            lower_bound,
                            upper_bound,
                        }) => {
                if let Some(l) = lower_bound {
                    write!(w, "  {} <= {}", &l.to_string(), &name)?;
                    if let Some(u) = upper_bound {
                        write!(w, " <= {}", u.to_string())?;
                    }
                    writeln!(w)?;
                } else if let Some(u) = upper_bound {
                    writeln!(w, "  {} <= {}", &name, &u.to_string())?;
                } else {
                    match v {
                        &ConsCont(LpContinuous { .. }) => {
                            writeln!(w, "  {} free", &name)?;
                        } // TODO: IntegerVar => -INF to INF
                        _ => (),
                    }
                }
            }
            _ => (),
        }
    }
    Ok(())
}

fn format_integers_lp_file_block<W: std::fmt::Write>(
        prob: &LpProblem, w: &mut W) -> std::fmt::Result {
    for (_, v) in prob.variables() {
        match v {
            &ConsInt(LpInteger { ref name, .. }) => {
                write!(w, "{} ", name)?;
            }
            _ => (),
        }
    }
    Ok(())
}

fn format_binaries_lp_file_block<W: std::fmt::Write>(
        prob: &LpProblem, w: &mut W) -> std::fmt::Result {
    for (_, v) in prob.variables() {
        match v {
            &ConsBin(LpBinary { ref name }) => {
                write!(w, "{} ", name)?;
            }
            _ => (),
        }
    }
    Ok(())
}

impl LpFileFormat for LpExpression {
    fn format<W: std::fmt::Write>(&self, w: &mut W) -> std::fmt::Result {
        format(&self, w, false)
    }

}

fn format<W: std::fmt::Write>(
        e: &LpExpression, w: &mut W, with_parenthesis: bool
        ) -> std::fmt::Result {
    let str_left_mult = if with_parenthesis { "(" } else { "" };
    let str_right_mult = if with_parenthesis { ")" } else { "" };
    let str_op_mult = if with_parenthesis { " * " } else { " " };
    match e {
        &LitVal(n) => { 
            write!(w, "{}", n.to_string())
        },
        &AddExpr(ref e1, ref e2) => {
            write!(w, "{}", str_left_mult.to_string())?;
            format(e1, w, with_parenthesis)?;
            write!(w, " + ")?;
            format(e2, w, with_parenthesis)?;
            write!(w, "{}", str_right_mult.to_string())
        }
        &SubExpr(ref e1, ref e2) => {
            write!(w, "{}", str_left_mult.to_string())?;
            format(e1, w, with_parenthesis)?;
            write!(w, " - ")?;
            format(e2, w, with_parenthesis)?;
            write!(w, "{}", str_right_mult.to_string())
        }
        &MulExpr(ref e1, ref e2) => {
            let ref deref_e1 = **e1;

            match deref_e1 {
                &LitVal(v) if v == 1.0 => {
                    //e2.to_lp_file_format()
                    write!(w, "{} ", str_left_mult.to_string())?;
                    format(e2, w, with_parenthesis)?;
                    write!(w, "{} ", str_right_mult.to_string())
                }
                &LitVal(v) if v == -1.0 => {
                    //"-".to_string() + &e2.to_lp_file_format()
                    write!(w, "{}-", str_left_mult.to_string())?;
                    format(e2, w, with_parenthesis)?;
                    write!(w, "{} ", str_right_mult.to_string())
                }
                _ => {
                    write!(w, "{}", str_left_mult.to_string())?;
                    format(e1, w, with_parenthesis)?;
                    write!(w, "{}", str_op_mult)?;
                    format(e2, w, with_parenthesis)?;
                    write!(w, "{} ", str_right_mult.to_string())
                }
            }
        }
        &ConsBin(LpBinary { name: ref n, .. }) => {
            write!(w, "{}", n.to_string())
        },
        &ConsInt(LpInteger { name: ref n, .. }) => {
            write!(w, "{}", n.to_string())
        },
        &ConsCont(LpContinuous { name: ref n, .. }) => {
            write!(w, "{}", n.to_string())
        },
        _ => {
            write!(w, "EmptyExpr!!")
        },
    }
}

impl LpFileFormat for LpConstraint {
    fn format<W: std::fmt::Write>(&self, w: &mut W) -> std::fmt::Result {
        self.0.format(w)?;
        match self.1 {
            GreaterOrEqual => write!(w, " >= ")?,
            LessOrEqual => write!(w, " <= ")?,
            Equal => write!(w, " = ")?,
        };
        self.2.format(w)
    }
}
