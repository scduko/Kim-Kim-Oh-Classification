import KimKimOh.Compute.Enum
import KimKimOh.Tables.Data.ProfileData
import KimKimOh.Tables.Data.ChunkData

/-!
# Kernel checks of the data of the two host decompositions

The step tables take the values 1, 2, 4 (at 2) or 1, 3 (at 3), or 15 for no step
(`tableOK2`, `tableOK3`); the profile masks are read through the class lists and indices
(`RegionData.hm2`, `hm3`); every local case of `2 ≤ a₀ ≤ 84` has a valid option
(`RegionData.hpairs`, Certificate 4.1, `cert:progressions`).
-/

namespace KimKimOh

open Tables

theorem tableOK2_3 : tableOK2 wst2_3 = true := by decide +kernel
theorem tableOK3_3 : tableOK3 wst3_3 = true := by decide +kernel
theorem tableOK2_9 : tableOK2 wst2_9 = true := by decide +kernel
theorem tableOK3_9 : tableOK3 wst3_9 = true := by decide +kernel

theorem masks2_3 : natAllR 256 (fun blk =>
    Nat.beq (mget pmask32 blk) ((mlist32 (blk / 32 % 4)).getD (pget pidx32 blk) 0)) = true := by
  decide +kernel
theorem masks3_3 : natAllR 729 (fun blk =>
    Nat.beq (mget pmask33 blk) ((mlist33 (blk / 81 % 3)).getD (pget pidx33 blk) 0)) = true := by
  decide +kernel
theorem masks2_9 : natAllR 256 (fun blk =>
    Nat.beq (mget pmask92 blk) ((mlist92 (blk / 32 % 4)).getD (pget pidx92 blk) 0)) = true := by
  decide +kernel
theorem masks3_9 : natAllR 729 (fun blk =>
    Nat.beq (mget pmask93 blk) ((mlist93 (blk / 81 % 3)).getD (pget pidx93 blk) 0)) = true := by
  decide +kernel

/-- Every pair of local cases has a valid option, for the classes `a₀ = 2, …, 84` (`2 ≤ a ≤ 72`,
and the class representatives `a0Of a ≤ 84` for `a ≥ 73`). -/
theorem pairs_3 : natAllR 83 (fun i =>
    pairsOK 3 2 (prof32 ((i + 2) % 4)) (prof33 ((i + 2) % 3)) (i + 2)) = true := by
  decide +kernel
theorem pairs_9 : natAllR 83 (fun i =>
    pairsOK 9 1 (prof92 ((i + 2) % 4)) (prof93 ((i + 2) % 3)) (i + 2)) = true := by
  decide +kernel

end KimKimOh
