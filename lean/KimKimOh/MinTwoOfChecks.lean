import KimKimOh.Normalize
import KimKimOh.TermBatches
import KimKimOh.RegionCover

/-!
# The finite part of §4 from its checks

`minTwo_of_checks`: for a host decomposition `H` with its region data `R`, if
* every pair `(a, t)` that may hold a block of the region is enumerated (`dispatchOK`),
* every enumerated block passes the whole-block test or is listed (`enumOK`),
* every listed block passes the last-column test (`termOK`),

then `L` represents every maximal reduced ternary of minimum at least 2. The chain is
`region_cover` (the region), `enumOK_sound` and `blockOK_sound` (the first pass),
`exists_normal` and `termOK_sound` (the last-column test, enumeration and witnesses).

The manuscript's certificates enter as follows: Certificate 4.1 (`cert:progressions`) is
`RegionData.hpairs`; Certificate 4.2 (`cert:ranges`) is the list `heavy` with `dispatchOK`;
Certificate 4.3 (`cert:finite`) is `enumOK` (part (a)) with `termOK`, which bounds the last-column
classes (part (b)) and checks the bounded matrices and their witnesses (part (c)).
-/

namespace KimKimOh

open GramLattice Tables

/-- **The finite part of §4.** -/
theorem minTwo_of_checks (H : HostSpec) (R : RegionData H)
    (hK : H.LocalGlobal) {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (hL : H.Target L)
    (ht2 : tableOK2 H.wt2 = true) (ht3 : tableOK3 H.wt3 = true)
    (heavy : ℕ → List ℕ) (lefts : List ((ℕ × ℕ) × List (ℕ × ℕ)))
    (hdisp : ∀ t < 27, dispatchOK H.j H.s H.prof2 H.prof3 heavy t = true)
    (henum : ∀ t < 27, ∀ a ∈ heavy t, enumOK H.j H.s H.prof2 H.prof3 R.ml2 R.ml3 R.pi2 R.pi3
      H.wt2 H.wt3 a t (leftsLookup lefts a t) = true)
    {r2 mx mw : ℕ} (hr2 : r2OK r2 = true)
    (hmx : ∀ blk < 729, mxRowOK (tget mx 729 blk) (tget mw 3645 blk) blk = true)
    (hterm : ∀ x ∈ flatBlocks lefts, ∃ cert,
      termOK H.j H.s H.acc2 H.acc3 r2 mx x.1 x.2.1 x.2.2 cert = true) :
    ∀ S : GramLattice (Fin 3), IsMaximal S.gram → (ternOf S).IsReduced → 2 ≤ (ternOf S).a →
      L.Represents S := by
  intro S hmax hred ha2
  rcases region_cover H R hK L hL S hmax hred ha2 with h | ⟨t, ht, hlo, hhi, hacap, hreg⟩
  · exact h
  set g := ternOf S with hg
  have hb0 := hred.b_nonneg
  have hac := hred.a_le_c
  have h2b := hred.two_b_le_a
  have hδ0 : 0 < g.delta := delta_pos S
  set a := g.a.toNat with hadef
  set b := g.b.toNat with hbdef
  set c := g.c.toNat with hcdef
  have ha : g.a = a := (Int.toNat_of_nonneg (by omega)).symm
  have hb : g.b = b := (Int.toNat_of_nonneg hb0).symm
  have hc : g.c = c := (Int.toNat_of_nonneg (by omega)).symm
  obtain ⟨hbc, hdelta⟩ := delta_natCast S ha hb hc
  have hδ : g.delta.toNat = a * c - b * b := by rw [hdelta]; rfl
  rw [hδ] at hlo hhi hreg
  have ha2' : 2 ≤ a := by omega
  have hb2 : 2 * b ≤ a := by omega
  have hac' : a ≤ c := by omega
  -- the class bound dominates the table bound
  have hcls : hiOf (hiTab H.j H.s H.prof2 H.prof3 R.ml2 R.ml3 a t) R.pi2 R.pi3 a b c ≤
      high H.j H.s (H.prof2 (a % 4)) (H.prof3 (a % 3)) a a t := by
    rw [hiOf_hiTab _ _ _ _ _ _ ht]
    exact (min_le_left _ _).trans
      (high_mono (fun P hP => mem_maskedProfs hP) (fun P hP => mem_maskedProfs hP))
  -- `a` is enumerated for `t`
  have hneed : needEnum H.j H.s H.prof2 H.prof3 a t = true := by
    unfold needEnum
    have hhc : a * c - b * b ≤ hiClass H.j H.s H.prof2 H.prof3 a t := by
      unfold hiClass; exact le_min (hreg.trans hcls) (by omega)
    have h3a : 3 * a * a ≤ 4 * (a * c - b * b) := by
      have : 4 * (b * b) ≤ a * a := by nlinarith
      have : a * a ≤ a * c := Nat.mul_le_mul_left a hac'
      rw [show 3 * a * a = 3 * (a * a) by ring]
      omega
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Bool.not_eq_true']
    refine ⟨⟨⟨ha2', ?_⟩, by omega⟩, by omega⟩
    rcases hacap with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  have hmemA : a ∈ heavy t := by
    have := natAllR_spec (hdisp t ht) a (Nat.lt_succ_of_le (le_amaxT hacap))
    rw [hneed] at this
    exact memN_spec (by simpa using this)
  -- the first pass, or the list of leftover blocks
  rcases enumOK_sound (henum t ht a hmemA) (by omega) hb2 hac' hbc.le hlo hhi hreg hcls with
    hblk | hleft
  · rw [blockOKRaw_eq] at hblk
    exact blockOK_sound H hK L hL ht2 ht3 S hmax hred ha hb hc hblk
  · obtain ⟨cert, hcert⟩ := hterm (a, b, c) (mem_blocks_of_mem_lookup hleft)
    obtain ⟨S', hmax', hred', hnorm', ha', hb', hc', hrep⟩ := exists_normal S hmax hred
    rw [← hg] at ha' hb' hc'
    exact (termOK_sound H hK L hL hr2 hmx S' hmax' hred' hnorm' (ha'.trans ha) (hb'.trans hb)
      (hc'.trans hc) hcert).trans hrep

end KimKimOh
