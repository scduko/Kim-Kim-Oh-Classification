import KimKimOh.Compute.Enum

/-!
# The dispatcher by ranges of `a` (computational definitions)

`dispatchOK` for a given `t` evaluates the class bounds for every `a ≤ amaxT t`. The kernel
caches every intermediate value of a declaration, so the check is split into ranges of `a`.
-/

namespace KimKimOh

open Tables

/-- The dispatcher on `lo ≤ a < lo + n` (the condition `a ≤ amaxT t` is part of the check). -/
def dispatchRange (j s : ℕ) (prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))) (heavy : ℕ → List ℕ)
    (t lo n : ℕ) : Bool :=
  natAllR n fun i => !Nat.ble (lo + i) (amaxT j s prof2 prof3 t) ||
    !needEnum j s prof2 prof3 (lo + i) t || memN (heavy t) (lo + i)

end KimKimOh
