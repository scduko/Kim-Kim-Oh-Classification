import KimKimOh.Compute.Loops
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bitwise

/-!
# Specifications of the kernel loops

Each loop of `KimKimOh/Compute/Loops.lean` returns `true` only if the property it checks holds.
-/

namespace KimKimOh

theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.mpr fun h' => h (Nat.eq_of_beq_eq_true h')

theorem natAllR_spec {n : ℕ} {f : ℕ → Bool} (h : natAllR n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    simp only [natAllR, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h.2 i hi
    · exact h.1

theorem memR_spec {l : List (ℕ × ℕ)} {b c : ℕ} (h : memR l b c = true) : (b, c) ∈ l := by
  induction l with
  | nil => simp [memR] at h
  | cons p l ih =>
    simp only [memR, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · rw [← h1, ← h2]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem memN_spec {l : List ℕ} {a : ℕ} (h : memN l a = true) : a ∈ l := by
  induction l with
  | nil => simp [memN] at h
  | cons p l ih =>
    simp only [memN, Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with h | h
    · rw [← h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem natAllR_of_forall {n : ℕ} {f : ℕ → Bool} (h : ∀ i < n, f i = true) : natAllR n f = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (f n && natAllR n f) = true
    rw [Bool.and_eq_true]
    exact ⟨h n (by omega), ih fun i hi => h i (by omega)⟩

theorem anyR_spec {α : Type} {f : α → Bool} : ∀ {l : List α}, anyR l f = true → ∃ x ∈ l, f x = true
  | [], h => by simp [anyR] at h
  | x :: l, h => by
    simp only [anyR, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨x, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, hfy⟩ := anyR_spec (l := l) h
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

theorem natFoldOr_succ (n : ℕ) (f : ℕ → ℕ) : natFoldOr (n + 1) f = natFoldOr n f ||| f n := rfl

theorem natFoldOr_testBit {n : ℕ} {f : ℕ → ℕ} {b : ℕ} :
    (natFoldOr n f).testBit b = true ↔ ∃ i < n, (f i).testBit b = true := by
  induction n with
  | zero => simp [natFoldOr]
  | succ n ih =>
    rw [natFoldOr_succ, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

theorem allR_spec {α : Type} {l : List α} {f : α → Bool} (h : allR l f = true) :
    ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp
  | cons y l ih =>
    simp only [allR, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx

theorem natFlat_succ {α : Type} (n : ℕ) (F : ℕ → List α) :
    natFlat (n + 1) F = natFlat n F ++ F n := rfl

theorem mem_natFlat {α : Type} {n : ℕ} {F : ℕ → List α} {x : α} :
    x ∈ natFlat n F ↔ ∃ i < n, x ∈ F i := by
  induction n with
  | zero => simp [natFlat]
  | succ n ih =>
    rw [natFlat_succ, List.mem_append, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

theorem idxAll_spec {α : Type} {F : ℕ → α → Bool} :
    ∀ (l : List α) (i : ℕ), (List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun x _ r i => F i x && r (i + 1)) l i) = true → ∀ x ∈ l, ∃ k, F k x = true
  | [], _, _, x, hx => by simp at hx
  | y :: l, i, h, x, hx => by
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨i, h.1⟩
    · exact idxAll_spec l (i + 1) h.2 x hx

theorem zipOK_spec {α β : Type} {F : α → β → Bool} :
    ∀ (l : List α) (W : List β), zipOK F l W = true → ∀ x ∈ l, ∃ y, F x y = true
  | [], _, _, x, hx => by simp at hx
  | x :: l, [], h, _, _ => by simp [zipOK] at h
  | x :: l, w :: W, h, y, hy => by
    have h' : (F x w && zipOK F l W) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨w, h'.1⟩
    · exact zipOK_spec l W h'.2 y hy

end KimKimOh

