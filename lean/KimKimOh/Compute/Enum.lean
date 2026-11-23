import KimKimOh.Compute.Region
import KimKimOh.Compute.Pass

/-!
# The enumeration of the region (computational definitions)
-/

namespace KimKimOh

open Tables

/-- The class bound for `(a, t)`, capped by `P_{t+1} - 1`. -/
def hiClass (j s : ℕ) (prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))) (a t : ℕ) : ℕ :=
  min (high j s (prof2 (a % 4)) (prof3 (a % 3)) a a t) (Pc (t + 1) - 1)

/-- The least `c` of a block in the region for `(a, t)` with this `b`: `c ≥ a` and
`a c - b² ≥ P_t`. -/
def cLo (a b t : ℕ) : ℕ := max a ((Pc t + b * b + a - 1) / a)

/-- **The enumeration check for `(a, t)`**: for `2 b ≤ a` and `cLo ≤ c ≤ (hiClass + b²) / a`,
the block is outside the region, passes the first pass, or is listed in `lefts`. -/
def enumOK (j s : ℕ) (prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))) (ml2 ml3 : ℕ → List ℕ)
    (pi2 pi3 wt2 wt3 a t : ℕ) (lefts : List (ℕ × ℕ)) : Bool :=
  natAllR (a / 2 + 1) fun b =>
    natAllR ((hiClass j s prof2 prof3 a t + b * b) / a + 1 - cLo a b t)
      fun i =>
        Nat.blt (hiOf (hiTab j s prof2 prof3 ml2 ml3 a t) pi2 pi3 a b (cLo a b t + i))
          (a * (cLo a b t + i) - b * b) ||
        blockOKRaw s wt2 wt3 a b (cLo a b t + i) ||
        memR lefts b (cLo a b t + i)

/-- The largest `a` allowed by the class bounds for `t`. -/
def amaxT (j s : ℕ) (prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))) (t : ℕ) : ℕ :=
  (List.range 12).foldl (fun m i =>
    max m (cond (classSkip j s (prof2 ((73 + i) % 4)) (prof3 ((73 + i) % 3)) (73 + i) t) 0
      (Acap j s (prof2 ((73 + i) % 4)) (prof3 ((73 + i) % 3)) (73 + i) t))) 72

/-- The pair `(a, t)` may hold a block of the region. -/
def needEnum (j s : ℕ) (prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))) (a t : ℕ) : Bool :=
  Nat.ble 2 a && (Nat.ble a 72 || (!classSkip j s (prof2 (a0Of a % 4)) (prof3 (a0Of a % 3)) (a0Of a) t &&
      Nat.ble a (Acap j s (prof2 (a0Of a % 4)) (prof3 (a0Of a % 3)) (a0Of a) t))) &&
    Nat.ble (Pc t) (hiClass j s prof2 prof3 a t) &&
    Nat.ble (3 * a * a) (4 * hiClass j s prof2 prof3 a t)

/-- **The dispatcher for `t`**: every `a ≤ amaxT t` that may hold a block is listed. -/
def dispatchOK (j s : ℕ) (prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))) (heavy : ℕ → List ℕ)
    (t : ℕ) : Bool :=
  natAllR (amaxT j s prof2 prof3 t + 1) fun a => !needEnum j s prof2 prof3 a t || memN (heavy t) a

/-- The leftover blocks of `(a, t)` `((a, t), [(b, c), …])` in a list of groups (the first entry for `(a, t)`). -/
def leftsLookup (L : List ((ℕ × ℕ) × List (ℕ × ℕ))) (a t : ℕ) : List (ℕ × ℕ) :=
  List.rec [] (fun e _ r => cond (Nat.beq e.1.1 a && Nat.beq e.1.2 t) e.2 r) L

end KimKimOh
