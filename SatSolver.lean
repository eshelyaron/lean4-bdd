import Bdd.Sat
import Std.Sat.CNF.Basic

def parseDimacs (n : Nat) [NeZero n] (lines : List String) : Std.Sat.CNF (Fin n) :=
  lines.filter (fun l => ¬l.startsWith "p" ∧ ¬l.startsWith "c")
       |>.map (fun l =>
         l.trim.splitOn " "
         |>.filterMap (fun s =>
           match s.toInt? with
           | some 0 => none
           | some i => some (if i > 0 then ⟨i.natAbs, true⟩ else ⟨i.natAbs, false⟩)
           | none   => none)
       )

partial def readLines (s : IO.FS.Stream) : IO (List String) := do
  let line ← s.getLine
  if line == "" then pure []
  else let rest ← readLines s; pure (line :: rest)

def main (args : List String) : IO Unit := do
  match args with
  | [ns, fs] =>
    try
      let handle ← (IO.FS.Handle.mk fs .read)
      let stream := IO.FS.Stream.ofHandle handle
      let lines ← readLines stream
      let cnf := parseDimacs (ns.toNat! + 1) lines
      if Std.Sat.CNF.Unsat cnf
      then IO.println "UNSAT"
      else IO.println "SAT"
    catch e =>
      IO.println s!"Error reading file {fs}: {e}"
  | _ => IO.println "Usage: ./SatSolver <number-of-variables> <input-file>"
