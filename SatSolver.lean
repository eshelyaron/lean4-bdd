module

import Bdd.Sat
import Std.Sat.CNF.Basic

def parseDimacs (n : Nat) [NeZero n] (lines : Array String) : Std.Sat.CNF (Fin n) :=
  Std.Sat.CNF.mk <| lines.filter (fun l => ¬l.startsWith "p" ∧ ¬l.startsWith "c")
    |>.map (fun l =>
      String.splitOn l.trimAscii.copy " "
      |>.filterMap (fun s =>
        match s.toInt? with
        | some 0 => none
        | some i =>
          let i' := ⟨i.natAbs % n, by exact Nat.mod_lt i.natAbs (Nat.pos_of_neZero n)⟩
          some ⟨i', decide (i > 0)⟩
        | none   => none)
      )

public def main (args : List String) : IO Unit := do
  match args with
  | [ns, fs] =>
    try
      let handle ← (IO.FS.Handle.mk fs .read)
      let lines ← handle.lines
      let cnf := parseDimacs (ns.toNat! + 1) lines
      if Std.Sat.CNF.Unsat cnf
      then IO.println "UNSAT"
      else IO.println "SAT"
    catch e =>
      IO.println s!"Error reading file {fs}: {e}"
  | _ => IO.println "Usage: ./SatSolver <number-of-variables> <input-file>"
