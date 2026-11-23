import Mathlib.Data.List.Basic
import Mathlib.Util.CompileInductive
import Mathlib.Tactic.Ring

/-!
# The windows `g_t` (computational definitions)
-/

namespace KimKimOh.Windows

/-- The windows `g_t` for `t < 27`: the least `g` with `Σ_{i < t} ⌈g / qᵢ⌉ < g`. -/
def gList : List ℕ :=
  [1, 2, 3, 4, 5, 7, 9, 10, 13, 17, 19, 25, 28, 33, 49, 55, 73, 82, 102, 109, 140, 182, 230, 340,
    468, 979, 6135]

/-- The window `g_t`: `gList` for `t < 27` and `(t + 4) 2^{t-2}` beyond. -/
def gWin (t : ℕ) : ℕ := if h : t < 27 then gList[t]'(by simp [gList]; omega) else (t + 4) * 2 ^ (t - 2)

end KimKimOh.Windows
