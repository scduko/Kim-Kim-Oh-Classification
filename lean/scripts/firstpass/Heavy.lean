import KimKimOh.Enum
import KimKimOh.Tables.Data.ProfileData

/-!
# The pairs `(a, t)` to enumerate in the first pass

Run from the Lake project root: `lake env lean --run scripts/firstpass/Heavy.lean 3` (or `9`).
For each `t < 27` and `a ≤ amaxT t` with `needEnum` (the pairs of Certificate 4.2, `cert:ranges`),
writes a line `a t n` to `scripts/firstpass/data/heavy{h}.txt`, where `n` is the number of
blocks `enumOK` iterates (the cost estimate of `gen_enum.py`). Prints `amaxT t` for `t < 27`,
the constants `AMAX` of `gen_enum.py`.
-/

open KimKimOh KimKimOh.Tables

def args (h : ℕ) := if h = 3 then (3, 2, prof32, prof33) else (9, 1, prof92, prof93)

def main (xs : List String) : IO Unit := do
  let h := xs.head!.toNat!
  unless h = 3 ∨ h = 9 do throw <| IO.userError "the determinant of K must be 3 or 9"
  let (j, s, p2, p3) := args h
  let mut out := ""
  let mut amax : List ℕ := []
  for t in List.range 27 do
    let am := amaxT j s p2 p3 t
    amax := amax ++ [am]
    for a in List.range (am + 1) do
      if needEnum j s p2 p3 a t then
        let hc := hiClass j s p2 p3 a t
        let mut n := 0
        for b in List.range (a / 2 + 1) do
          n := n + ((hc + b * b) / a + 1 - cLo a b t)
        out := out ++ s!"{a} {t} {n}\n"
  IO.FS.writeFile s!"scripts/firstpass/data/heavy{h}.txt" out
  IO.println s!"amaxT: {amax}"
