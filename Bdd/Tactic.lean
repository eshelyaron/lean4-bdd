module

public import Mathlib.Init

/--
A simp attribute that is used in `BDD.lean` to infer the size of `BDDs` during evaluation. -/
register_simp_attr bdd_nvars

macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| simp only [bdd_nvars] at *; omega)
