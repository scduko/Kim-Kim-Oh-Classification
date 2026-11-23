import KimKimOh.Loops
import KimKimOh.Compute.Terminal
import Mathlib.Data.List.Basic

/-!
# Assembling the batch checks of the last-column test

`termAll_of_batches`: if each batch of a list of blocks passes `termBatch`, and the batches cover
the list, every block has a certificate passing `termOK`. `mem_blocks_of_mem_lookup`: a block left
by the first pass for `(a, t)` lies in the flattened list of blocks.
-/

namespace KimKimOh

open Tables

theorem cover_of_batches {α β : Type} (F : α → β → Bool) :
    ∀ (sizes : List ℕ) (L : List α) (certs : ℕ → List β),
      (∀ i < sizes.length, zipOK F ((L.drop (sizes.take i).sum).take (sizes.getD i 0)) (certs i)
        = true) →
      L.length ≤ sizes.sum → ∀ x ∈ L, ∃ y, F x y = true
  | [], L, _, _, hlen, x, hx => by
    simp only [List.sum_nil, Nat.le_zero, List.length_eq_zero_iff] at hlen
    subst hlen; simp at hx
  | s :: sizes, L, certs, h, hlen, x, hx => by
    rw [← List.take_append_drop s L, List.mem_append] at hx
    rcases hx with hx | hx
    · have h0 := h 0 (by simp)
      simp only [List.take_zero, List.sum_nil, List.drop_zero, List.getD_cons_zero] at h0
      exact zipOK_spec _ _ h0 x hx
    · refine cover_of_batches F sizes (L.drop s) (fun i => certs (i + 1)) (fun i hi => ?_) ?_ x hx
      · have := h (i + 1) (by simp; omega)
        simpa [List.take_succ_cons, List.sum_cons, List.drop_drop, Nat.add_comm] using this
      · simp only [List.length_drop, List.sum_cons] at hlen ⊢; omega

/-- **All batches**: every block has a certificate passing `termOK`. -/
theorem termAll_of_batches {j s : ℕ} {acc2 acc3 : BT ℕ} {r2 mx : ℕ} {blocks : List (ℕ × ℕ × ℕ)}
    {sizes : List ℕ} (certs : ℕ → List TermCert)
    (h : ∀ i < sizes.length, termBatch j s acc2 acc3 r2 mx blocks sizes i (certs i) = true)
    (hlen : blocks.length ≤ sizes.sum) :
    ∀ x ∈ blocks, ∃ cert, termOK j s acc2 acc3 r2 mx x.1 x.2.1 x.2.2 cert = true :=
  cover_of_batches _ sizes blocks certs h hlen

theorem mem_flatBlocks {L : List ((ℕ × ℕ) × List (ℕ × ℕ))} {e : (ℕ × ℕ) × List (ℕ × ℕ)}
    (he : e ∈ L) {bc : ℕ × ℕ} (hbc : bc ∈ e.2) : (e.1.1, bc.1, bc.2) ∈ flatBlocks L := by
  induction L with
  | nil => simp at he
  | cons e' L ih =>
    have key : ∀ (l : List (ℕ × ℕ)) (r : List (ℕ × ℕ × ℕ)) (x : ℕ × ℕ × ℕ), x ∈ r →
        x ∈ (List.rec r (fun bc _ r' => (e'.1.1, bc.1, bc.2) :: r') l : List (ℕ × ℕ × ℕ)) := by
      intro l r x hx
      induction l with
      | nil => exact hx
      | cons y l ihl => exact List.mem_cons_of_mem _ ihl
    have key2 : ∀ (l : List (ℕ × ℕ)) (r : List (ℕ × ℕ × ℕ)) (bc : ℕ × ℕ), bc ∈ l →
        (e'.1.1, bc.1, bc.2) ∈
          (List.rec r (fun bc _ r' => (e'.1.1, bc.1, bc.2) :: r') l : List (ℕ × ℕ × ℕ)) := by
      intro l r bc hbc
      induction l with
      | nil => simp at hbc
      | cons y l ihl =>
        rcases List.mem_cons.mp hbc with rfl | hbc
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ihl hbc)
    show (e.1.1, bc.1, bc.2) ∈ (List.rec (flatBlocks L)
      (fun bc _ r' => (e'.1.1, bc.1, bc.2) :: r') e'.2 : List (ℕ × ℕ × ℕ))
    rcases List.mem_cons.mp he with rfl | he
    · exact key2 _ _ _ hbc
    · exact key _ _ _ (ih he)

/-- The leftover blocks of `(a, t)`: the first entry of the list for `(a, t)`. -/
theorem mem_of_mem_lookup {L : List ((ℕ × ℕ) × List (ℕ × ℕ))} {a t : ℕ} {bc : ℕ × ℕ}
    (h : bc ∈ leftsLookup L a t) : ∃ e ∈ L, e.1.1 = a ∧ bc ∈ e.2 := by
  induction L with
  | nil => simp [leftsLookup] at h
  | cons e L ih =>
    have h' : bc ∈ cond (Nat.beq e.1.1 a && Nat.beq e.1.2 t) e.2
        (leftsLookup L a t) := h
    cases hc : (Nat.beq e.1.1 a && Nat.beq e.1.2 t)
    · rw [hc, Bool.cond_false] at h'
      obtain ⟨e', he', h1, h2⟩ := ih h'
      exact ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩
    · rw [hc, Bool.cond_true] at h'
      simp only [Bool.and_eq_true] at hc
      exact ⟨e, List.mem_cons_self, Nat.eq_of_beq_eq_true hc.1, h'⟩

theorem mem_blocks_of_mem_lookup {L : List ((ℕ × ℕ) × List (ℕ × ℕ))} {a t b c : ℕ}
    (h : (b, c) ∈ leftsLookup L a t) : (a, b, c) ∈ flatBlocks L := by
  obtain ⟨e, he, rfl, hbc⟩ := mem_of_mem_lookup h
  exact mem_flatBlocks he hbc

end KimKimOh
