import Mathlib.Data.Nat.Basic
import Mathlib.Util.CompileInductive

/-!
# Loops for the kernel (computational definitions)

The kernel evaluates structural recursion through auxiliary `brecOn` terms, which is slow, and
`∀ i < n` through `Nat.decidableBallLT`, which costs milliseconds per step. The checks therefore
loop with the recursors directly. The specifications are in `KimKimOh/Loops.lean`.

* `natAllR n f`: `f i` for every `i < n`; `natFoldOr n f`: `⋁_{i < n} f i`; `natFlat n F`: the
  concatenation of `F 0, …, F (n - 1)`.
* `anyR`, `allR`, `idxAll`, `zipOK`: some entry, every entry, every entry with its index, and
  pairwise checks of two lists of equal length.
* `memN`, `memR`: membership of a number and of a pair `(b, c)`.
-/

namespace KimKimOh

/-- `∀ i < n, f i` by the recursor. -/
def natAllR (n : ℕ) (f : ℕ → Bool) : Bool := Nat.rec true (fun i r => f i && r) n

/-- Membership of a block in a list by the recursor. -/
def memR (l : List (ℕ × ℕ)) (b c : ℕ) : Bool :=
  List.rec false (fun p _ r => (Nat.beq p.1 b && Nat.beq p.2 c) || r) l

/-- Membership of a natural number in a list by the recursor. -/
def memN (l : List ℕ) (a : ℕ) : Bool := List.rec false (fun p _ r => Nat.beq p a || r) l

/-- `List.any` by the recursor (fast in the kernel). -/
def anyR {α : Type} (l : List α) (f : α → Bool) : Bool := List.rec false (fun h _ r => f h || r) l

/-- `⋁_{i < n} f i`. -/
def natFoldOr (n : ℕ) (f : ℕ → ℕ) : ℕ := Nat.rec 0 (fun i r => r ||| f i) n

/-- `∀ x ∈ l, f x` by the recursor. -/
def allR {α : Type} (l : List α) (f : α → Bool) : Bool := List.rec true (fun h _ r => f h && r) l

/-- The concatenation of `F 0, …, F (n - 1)`. -/
def natFlat {α : Type} (n : ℕ) (F : ℕ → List α) : List α := Nat.rec [] (fun i r => r ++ F i) n

/-- `F i xᵢ` for every entry `xᵢ` of `l`. -/
def idxAll {α : Type} (l : List α) (F : ℕ → α → Bool) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true) (fun x _ r i => F i x && r (i + 1)) l 0

/-- Pairwise checks of two lists of equal length. -/
def zipOK {α β : Type} (F : α → β → Bool) (l : List α) : List β → Bool :=
  List.rec (fun W => List.rec true (fun _ _ _ => false) W)
    (fun x _ r W => List.rec false (fun y ys _ => F x y && r ys) W) l

end KimKimOh
