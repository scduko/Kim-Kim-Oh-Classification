import KimKimOh.MinTwoOfChecks
import KimKimOh.HostDataChecks
import KimKimOh.Tables.ProfChecks
import KimKimOh.Tables.Soundness
import KimKimOh.Local.LargePrimes

/-!
# The two host decompositions

`host3`: `L₆ ⊇ K₃ ⊥ ⟨2⟩` with `K₃ = I₃ ⊥ A₂` (`j = 3`, `s = 2`); `host9`: `L₉ ⊇ K₉ ⊥ ⟨1⟩` with
`K₉ = I₂ ⊥ A₂ ⊥ ⟨3⟩` (`j = 9`, `s = 1`). Each carries its acceptance tables at 2 and 3, the
profiles and step tables with their kernel checks, and the local lemmas at `p ≥ 5`.
-/

namespace KimKimOh

open Tables

/-- `L₆ ⊇ K₃ ⊥ ⟨2⟩`. -/
def host3 : HostSpec where
  κ := Fin 3 ⊕ Fin 2
  K := K3
  j := 3
  s := 2
  hs := Or.inr rfl
  acc2 := acc32
  acc3 := acc33
  prof2 := prof32
  prof3 := prof33
  pm2 := pmask32
  pm3 := pmask33
  wt2 := wst2_3
  wt3 := wst3_3
  ok2 := profOK32
  ok3 := profOK33
  acc2_sound := local2_K3
  acc3_sound := local3_K3
  okAt_sound := fun p hp h5 C hC =>
    hC.elim (rank_K3 p hp h5 C) (square_K3 p hp h5 C)

/-- `L₉ ⊇ K₉ ⊥ ⟨1⟩`. -/
def host9 : HostSpec where
  κ := (Fin 2 ⊕ Fin 2) ⊕ Fin 1
  K := K9
  j := 9
  s := 1
  hs := Or.inl rfl
  acc2 := acc92
  acc3 := acc93
  prof2 := prof92
  prof3 := prof93
  pm2 := pmask92
  pm3 := pmask93
  wt2 := wst2_9
  wt3 := wst3_9
  ok2 := profOK92
  ok3 := profOK93
  acc2_sound := local2_K9
  acc3_sound := local3_K9
  okAt_sound := fun p hp h5 C hC =>
    hC.elim (rank_K9 p hp h5 C) (square_K9 p hp h5 C)

/-- The region data of `host3`. -/
def region3 : RegionData host3 where
  ml2 := mlist32
  ml3 := mlist33
  pi2 := pidx32
  pi3 := pidx33
  hm2 := fun blk hblk => Nat.eq_of_beq_eq_true (natAllR_spec masks2_3 blk hblk)
  hm3 := fun blk hblk => Nat.eq_of_beq_eq_true (natAllR_spec masks3_3 blk hblk)
  hpairs := fun a₀ h2 h84 => by
    have := natAllR_spec pairs_3 (a₀ - 2) (by omega)
    rwa [show a₀ - 2 + 2 = a₀ by omega] at this

/-- The region data of `host9`. -/
def region9 : RegionData host9 where
  ml2 := mlist92
  ml3 := mlist93
  pi2 := pidx92
  pi3 := pidx93
  hm2 := fun blk hblk => Nat.eq_of_beq_eq_true (natAllR_spec masks2_9 blk hblk)
  hm3 := fun blk hblk => Nat.eq_of_beq_eq_true (natAllR_spec masks3_9 blk hblk)
  hpairs := fun a₀ h2 h84 => by
    have := natAllR_spec pairs_9 (a₀ - 2) (by omega)
    rwa [show a₀ - 2 + 2 = a₀ by omega] at this

end KimKimOh
