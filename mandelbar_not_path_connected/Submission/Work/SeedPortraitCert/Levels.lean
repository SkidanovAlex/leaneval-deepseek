/-
# SeedPortraitCert — the per-level checks as a function of the level (generated)

The `decide`d level theorems of `Check.lean` are indexed by the numeral of the level; the
chain argument needs them as a function of `k`.  This module is the dispatcher. -/
import Mathlib
import Submission.Work.SeedPortraitCert.Check

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedPortraitCert

open Work.SeedCertRay

/-- The (D1) check of level `k`, for `k ≤ KT - 2`. -/
theorem chkPAt : ∀ k : Nat, k ≤ KT - 2 → chkLevelP (dskP k) (dskP (k + 1)) (crtP k) PXM PYM RADM = true
  | 0, _ => chkP_0
  | 1, _ => chkP_1
  | 2, _ => chkP_2
  | 3, _ => chkP_3
  | 4, _ => chkP_4
  | 5, _ => chkP_5
  | 6, _ => chkP_6
  | 7, _ => chkP_7
  | 8, _ => chkP_8
  | 9, _ => chkP_9
  | 10, _ => chkP_10
  | 11, _ => chkP_11
  | 12, _ => chkP_12
  | 13, _ => chkP_13
  | 14, _ => chkP_14
  | 15, _ => chkP_15
  | 16, _ => chkP_16
  | 17, _ => chkP_17
  | 18, _ => chkP_18
  | 19, _ => chkP_19
  | 20, _ => chkP_20
  | 21, _ => chkP_21
  | 22, _ => chkP_22
  | 23, _ => chkP_23
  | 24, _ => chkP_24
  | 25, _ => chkP_25
  | 26, _ => chkP_26
  | 27, _ => chkP_27
  | 28, _ => chkP_28
  | 29, _ => chkP_29
  | 30, _ => chkP_30
  | 31, _ => chkP_31
  | 32, _ => chkP_32
  | 33, _ => chkP_33
  | 34, _ => chkP_34
  | n + 35, h => by unfold KT at h; omega

/-- The (D2) check of level `k`, for `k ≤ KT - 2`. -/
theorem chkDirPAt : ∀ k : Nat, k ≤ KT - 2 → chkDirP (dirP k) (dskP (k + 1)) (dskP k) = true
  | 0, _ => chkDirP_0
  | 1, _ => chkDirP_1
  | 2, _ => chkDirP_2
  | 3, _ => chkDirP_3
  | 4, _ => chkDirP_4
  | 5, _ => chkDirP_5
  | 6, _ => chkDirP_6
  | 7, _ => chkDirP_7
  | 8, _ => chkDirP_8
  | 9, _ => chkDirP_9
  | 10, _ => chkDirP_10
  | 11, _ => chkDirP_11
  | 12, _ => chkDirP_12
  | 13, _ => chkDirP_13
  | 14, _ => chkDirP_14
  | 15, _ => chkDirP_15
  | 16, _ => chkDirP_16
  | 17, _ => chkDirP_17
  | 18, _ => chkDirP_18
  | 19, _ => chkDirP_19
  | 20, _ => chkDirP_20
  | 21, _ => chkDirP_21
  | 22, _ => chkDirP_22
  | 23, _ => chkDirP_23
  | 24, _ => chkDirP_24
  | 25, _ => chkDirP_25
  | 26, _ => chkDirP_26
  | 27, _ => chkDirP_27
  | 28, _ => chkDirP_28
  | 29, _ => chkDirP_29
  | 30, _ => chkDirP_30
  | 31, _ => chkDirP_31
  | 32, _ => chkDirP_32
  | 33, _ => chkDirP_33
  | 34, _ => chkDirP_34
  | n + 35, h => by unfold KT at h; omega

end Work.SeedPortraitCert
