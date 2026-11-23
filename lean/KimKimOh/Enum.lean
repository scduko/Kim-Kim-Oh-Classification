import KimKimOh.Loops
import KimKimOh.RegionCover
import KimKimOh.Compute.Enum

/-!
# Enumerating the region (`sec:finite`, `app:bounded`)

For each pair `(a, t)` the check `enumOK` runs over the blocks `0 ≤ 2b ≤ a ≤ c` with
`P_t ≤ δ ≤ min(P_{t+1} - 1, high_class)` and asks, for each block in the region
(`δ ≤ hiOf …`), that it passes the first-pass test or appears in the list of blocks left for the
last-column test (`enumOK_sound`). The class bound `high` over the profiles of the class of `a`
dominates every chunk bound (`high_mono`). The pairs `(a, t)` with a nonempty interval in
Certificate 4.2 (`cert:ranges`) are the lists `heavy3`, `heavy9` (536 and 1,136 pairs), checked by
`dispatchOK`.
-/

namespace KimKimOh

open GramLattice Tables

/-! ### Soundness -/

/-- The bound `high` decreases on fewer local cases. -/
theorem high_mono {j s a a₀ t : ℕ} {L₂ L₃ L₂' L₃' : List (List (List (ℕ × ℕ)))}
    (h₂ : ∀ P ∈ L₂', P ∈ L₂) (h₃ : ∀ P ∈ L₃', P ∈ L₃) :
    high j s L₂' L₃' a a₀ t ≤ high j s L₂ L₃ a a₀ t := by
  unfold high
  refine foldl_max_le _ _ 0 (Nat.zero_le _) fun pr hpr => ?_
  refine (le_foldl_max (fun pr : List (List (ℕ × ℕ)) × List (List (ℕ × ℕ)) =>
    minL ((validOpts j s a₀ pr.1 pr.2).map (thr s a a₀ (Windows.gWin t)))) _ 0).2 pr ?_
  unfold pairsOf at hpr ⊢
  obtain ⟨P₂, hP₂, hpr⟩ := List.mem_flatMap.mp hpr
  obtain ⟨P₃, hP₃, rfl⟩ := List.mem_map.mp hpr
  exact List.mem_flatMap.mpr ⟨P₂, h₂ _ hP₂, List.mem_map.mpr ⟨P₃, h₃ _ hP₃, rfl⟩⟩

/-- **Soundness of the enumeration check**: a block in the region for `(a, t)` passes the
first-pass test or lies in the list. -/
theorem enumOK_sound {j s : ℕ} {prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))}
    {ml2 ml3 : ℕ → List ℕ} {pi2 pi3 wt2 wt3 a t : ℕ} {lefts : List (ℕ × ℕ)}
    (h : enumOK j s prof2 prof3 ml2 ml3 pi2 pi3 wt2 wt3 a t lefts = true)
    (ha : 0 < a) {b c : ℕ} (hb : 2 * b ≤ a) (hc : a ≤ c) (hbc : b * b ≤ a * c)
    (hlo : Pc t ≤ a * c - b * b) (hhi : a * c - b * b < Pc (t + 1))
    (hreg : a * c - b * b ≤ hiOf (hiTab j s prof2 prof3 ml2 ml3 a t) pi2 pi3 a b c)
    (hcls : hiOf (hiTab j s prof2 prof3 ml2 ml3 a t) pi2 pi3 a b c ≤
      high j s (prof2 (a % 4)) (prof3 (a % 3)) a a t) :
    blockOKRaw s wt2 wt3 a b c = true ∨ (b, c) ∈ lefts := by
  unfold enumOK at h
  have hb' := natAllR_spec h b (by omega)
  set clo := cLo a b t with hclo
  have hclo_le : clo ≤ c := by
    refine max_le hc ?_
    rw [Nat.div_le_iff_le_mul_add_pred ha]
    have : Pc t + b * b ≤ a * c := by omega
    omega
  have hc_le : c ≤ (hiClass j s prof2 prof3 a t + b * b) / a := by
    rw [Nat.le_div_iff_mul_le ha]
    unfold hiClass
    have h1 : a * c - b * b ≤ high j s (prof2 (a % 4)) (prof3 (a % 3)) a a t := hreg.trans hcls
    have h2 : a * c - b * b ≤ Pc (t + 1) - 1 := by omega
    have := le_min h1 h2
    have : c * a = (a * c - b * b) + b * b := by rw [Nat.sub_add_cancel hbc]; ring
    omega
  have hi := natAllR_spec hb' (c - clo) (by omega)
  rw [show clo + (c - clo) = c by omega] at hi
  simp only [Bool.or_eq_true, Nat.blt_eq] at hi
  rcases hi with (hi | hi) | hi
  · omega
  · exact Or.inl hi
  · exact Or.inr (memR_spec hi)

/-! ### Which pairs `(a, t)` need an enumeration -/

theorem le_amaxT {j s : ℕ} {prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))} {a t : ℕ}
    (h : a ≤ 72 ∨ (classSkip j s (prof2 (a0Of a % 4)) (prof3 (a0Of a % 3)) (a0Of a) t = false ∧
      a ≤ Acap j s (prof2 (a0Of a % 4)) (prof3 (a0Of a % 3)) (a0Of a) t)) :
    a ≤ amaxT j s prof2 prof3 t := by
  unfold amaxT
  have key := le_foldl_max (fun i => cond (classSkip j s (prof2 ((73 + i) % 4)) (prof3 ((73 + i) % 3))
      (73 + i) t) 0 (Acap j s (prof2 ((73 + i) % 4)) (prof3 ((73 + i) % 3)) (73 + i) t))
    (List.range 12) 72
  rcases h with h | ⟨h1, h2⟩
  · exact h.trans key.1
  · by_cases h73 : a ≤ 72
    · exact h73.trans key.1
    · have hi := key.2 ((a - 73) % 12) (List.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
      have e : 73 + (a - 73) % 12 = a0Of a := rfl
      simp only [e, h1, Bool.cond_false] at hi
      exact h2.trans hi

end KimKimOh
