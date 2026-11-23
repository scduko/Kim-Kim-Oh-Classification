import KimKimOh.Enum
import KimKimOh.Tables.Data.ProfileData

/-!
# The blocks left by the whole-block test

Run from the Lake project root: `lake env lean --run scripts/firstpass/RegionEval.lean 3` (or
`9`). Enumerates the region as `enumOK` does: for each `t < 27` and each `a` allowed by the class
bounds, the blocks `0 ≤ 2b ≤ a`, `cLo ≤ c` with `δ ≤ hiOf …`, and tests each with `blockOKRaw`.
Writes the blocks that fail to `scripts/firstpass/data/left{h}.txt` and prints the number of
blocks in the region for each `t` (Table 4: 534,827 and 8,521,181 in total).
-/
open KimKimOh KimKimOh.Tables

def hostArgs (h : ℕ) : ℕ × ℕ × (ℕ → List (List (List (ℕ × ℕ)))) × (ℕ → List (List (List (ℕ × ℕ)))) × (ℕ → List ℕ) × (ℕ → List ℕ) × ℕ × ℕ × ℕ × ℕ :=
  if h = 3 then (3, 2, prof32, prof33, mlist32, mlist33, pidx32, pidx33, wst2_3, wst3_3)
  else (9, 1, prof92, prof93, mlist92, mlist93, pidx92, pidx93, wst2_9, wst3_9)

def classInfo (h t a0 : ℕ) : Bool × ℕ :=
  let (j, s, p2, p3, _, _, _, _, _, _) := hostArgs h
  (classSkip j s (p2 (a0 % 4)) (p3 (a0 % 3)) a0 t, Acap j s (p2 (a0 % 4)) (p3 (a0 % 3)) a0 t)

def pairsAll (h : ℕ) : Bool :=
  let (j, s, p2, p3, _, _, _, _, _, _) := hostArgs h
  (List.range 83).all fun i => pairsOK j s (p2 ((i + 2) % 4)) (p3 ((i + 2) % 3)) (i + 2)

/-- The `a` to scan for `t`: `2 ≤ a ≤ 72`, and the `a` from 73 to `amaxT t` (the bound of the
dispatcher) whose class modulo 12 is not skipped and has `a ≤ Acap`. -/
def aRange (h t : ℕ) : List ℕ :=
  let (j, s, p2, p3, _, _, _, _, _, _) := hostArgs h
  let cis := (List.range 12).map fun i => classInfo h t (73 + i)
  (List.range 71).map (· + 2) |>.append
    ((List.range (amaxT j s p2 p3 t - 72)).map (· + 73) |>.filter fun a =>
      let ci := cis.getD ((a - 73) % 12) (true, 0); !ci.1 && Nat.ble a ci.2)

partial def scan (h t : ℕ) : ℕ × List (ℕ × ℕ × ℕ) := Id.run do
  let (j, s, p2, p3, m2, m3, i2, i3, w2, w3) := hostArgs h
  let mut cnt := 0
  let mut lefts : List (ℕ × ℕ × ℕ) := []
  for a in aRange h t do
    let a₀ := if a < 73 then a else a0Of a
    let hc := high j s (p2 (a % 4)) (p3 (a % 3)) a a₀ t
    if hc < Pc t || 4 * hc < 3 * a * a then continue
    let tab := hiTab j s p2 p3 m2 m3 a t
    for b in List.range (a / 2 + 1) do
      let clo := cLo a b t
      let chi := (Pc (t + 1) - 1 + b * b) / a
      for c in List.range (chi + 1 - clo) do
        let c := c + clo
        let δ := a * c - b * b
        if δ ≤ hiOf tab i2 i3 a b c then
          cnt := cnt + 1
          if !blockOKRaw s w2 w3 a b c then
            lefts := (a, b, c) :: lefts
  return (cnt, lefts)

def main (args : List String) : IO Unit := do
  let h := args.head!.toNat!
  unless h = 3 ∨ h = 9 do throw <| IO.userError "the determinant of K must be 3 or 9"
  IO.println s!"pairsOK all: {pairsAll h}"
  let mut tot := 0
  let mut allL : List (ℕ × ℕ × ℕ) := []
  for t in List.range 27 do
    let ar := aRange h t
    let (cnt, l) := scan h t
    IO.println s!"t={t} amax={ar.foldl max 0} blocks={cnt} left={l.length}"
    (← IO.getStdout).flush
    tot := tot + cnt
    allL := allL ++ l
  IO.println s!"total {tot} leftovers {allL.length}"
  IO.FS.writeFile s!"scripts/firstpass/data/left{h}.txt" (toString allL)
