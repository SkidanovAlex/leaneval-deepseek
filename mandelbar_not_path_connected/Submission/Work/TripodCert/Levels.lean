/-
# TripodCert — the per-level checks as a function of the level (generated)

The `decide`d level theorems of `Check.lean` are indexed by the numeral of the level; the
chain argument needs them as a function of `k`.  This module is the dispatcher. -/
import Mathlib
import Submission.Work.TripodCert.Check

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

open Work.SeedCertRay

/-- The (D1) check of level `k`, for `k ≤ KT - 2`. -/
theorem chkTAt : ∀ k : Nat, k ≤ KT - 2 → chkLevelT (dskT k) (dskT (k + 1)) (crtT k) PXM PYM RADM = true
  | 0, _ => chkT_0
  | 1, _ => chkT_1
  | 2, _ => chkT_2
  | 3, _ => chkT_3
  | 4, _ => chkT_4
  | 5, _ => chkT_5
  | 6, _ => chkT_6
  | 7, _ => chkT_7
  | 8, _ => chkT_8
  | 9, _ => chkT_9
  | 10, _ => chkT_10
  | 11, _ => chkT_11
  | 12, _ => chkT_12
  | 13, _ => chkT_13
  | 14, _ => chkT_14
  | 15, _ => chkT_15
  | 16, _ => chkT_16
  | 17, _ => chkT_17
  | 18, _ => chkT_18
  | 19, _ => chkT_19
  | 20, _ => chkT_20
  | 21, _ => chkT_21
  | 22, _ => chkT_22
  | 23, _ => chkT_23
  | 24, _ => chkT_24
  | 25, _ => chkT_25
  | 26, _ => chkT_26
  | 27, _ => chkT_27
  | 28, _ => chkT_28
  | 29, _ => chkT_29
  | 30, _ => chkT_30
  | 31, _ => chkT_31
  | 32, _ => chkT_32
  | 33, _ => chkT_33
  | 34, _ => chkT_34
  | 35, _ => chkT_35
  | 36, _ => chkT_36
  | 37, _ => chkT_37
  | 38, _ => chkT_38
  | n + 39, h => by unfold KT at h; omega

/-- The (D2) check of level `k`, for `k ≤ KT - 2`. -/
theorem chkDirTAt : ∀ k : Nat, k ≤ KT - 2 → chkDirT (dirT k) (dskT (k + 1)) (dskT k) = true
  | 0, _ => chkDirT_0
  | 1, _ => chkDirT_1
  | 2, _ => chkDirT_2
  | 3, _ => chkDirT_3
  | 4, _ => chkDirT_4
  | 5, _ => chkDirT_5
  | 6, _ => chkDirT_6
  | 7, _ => chkDirT_7
  | 8, _ => chkDirT_8
  | 9, _ => chkDirT_9
  | 10, _ => chkDirT_10
  | 11, _ => chkDirT_11
  | 12, _ => chkDirT_12
  | 13, _ => chkDirT_13
  | 14, _ => chkDirT_14
  | 15, _ => chkDirT_15
  | 16, _ => chkDirT_16
  | 17, _ => chkDirT_17
  | 18, _ => chkDirT_18
  | 19, _ => chkDirT_19
  | 20, _ => chkDirT_20
  | 21, _ => chkDirT_21
  | 22, _ => chkDirT_22
  | 23, _ => chkDirT_23
  | 24, _ => chkDirT_24
  | 25, _ => chkDirT_25
  | 26, _ => chkDirT_26
  | 27, _ => chkDirT_27
  | 28, _ => chkDirT_28
  | 29, _ => chkDirT_29
  | 30, _ => chkDirT_30
  | 31, _ => chkDirT_31
  | 32, _ => chkDirT_32
  | 33, _ => chkDirT_33
  | 34, _ => chkDirT_34
  | 35, _ => chkDirT_35
  | 36, _ => chkDirT_36
  | 37, _ => chkDirT_37
  | 38, _ => chkDirT_38
  | n + 39, h => by unfold KT at h; omega

end Work.TripodCert
