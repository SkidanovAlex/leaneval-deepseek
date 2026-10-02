/-
# SeedPortraitCert — soundness of the level checkers

Area `Submission/Work/SeedPortraitCert/`.  This module extracts the per-`(j,i)` geometric facts
from the `decide`d level checkers of `Check.lean`, in the index form in which the chain induction
(`Work.SeedCertRay.chain_sound_sets`) consumes them:

* `level_D1P` — the (D1) cover condition of one step, for every angle class and sub-disk;
* `level_HPP` — the (D2) half-plane condition of one level, for every angle class.

This is the `10`-class analogue of `Work.TripodCert.{level_D1, level_HP}`, with the successor map
`Work.SeedPortraitCert.sucP` of the two `5`-cycles.
-/
import Mathlib
import Submission.Work.SeedPortraitCert.Num
import Submission.Work.SeedPortraitCert.stepOKBP_sound
import Submission.Work.SeedCertRay.dirOKB_sound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedPortraitCert

open Work.SeedCertRay

/-- Extraction of the per-`(j,i)` (D1) certificate of one level: for `j < 10` and `i < 6`, the
checker of the class `j` and the sub-disk `i` is satisfied with source disk `(sucP j, i)` of the
source level and target disk `(j, i)` of the target level. -/
theorem chkLevelP_sound (s t c : List Int) (h : chkLevelP s t c PXM PYM RADM = true)
    (j : ℕ) (hj : j ∈ angQsP) (i : ℕ) (hi : i ∈ subQsP) :
    stepOKBP s t c PXM PYM RADM (sucP j * NC + i) (j * NC + i) = true := by
  simp only [chkLevelP] at h
  exact allS_sound (allS_sound h j hj) i hi

/-- **(D1) of one level**, in the index form of the chain: the preimage of the `sucP j`-th disk
of the source level lies in the `j`-th disk of the target level up to sign. -/
theorem level_D1P (s t c : List Int) (h : chkLevelP s t c PXM PYM RADM = true) (j : ℕ)
    (i : Fin NC) :
    Work.SeedCertRay.DiskCover (Work.SeedCertRay.dskOf s (sucP (j % 10) * NC + i.val))
      Work.SeedCertRay.Xb (Work.SeedCertRay.dskOf t ((j % 10) * NC + i.val)) := by
  have hj : j % 10 ∈ angQsP := mem_angQsP (Nat.mod_lt j (by norm_num))
  have hi : i.val ∈ subQsP := mem_subQsP i.isLt
  have hstep := chkLevelP_sound s t c h (j % 10) hj i.val hi
  exact stepOKBP_sound s t c _ _ hstep

/-- **(D2) of one level**, in the index form of the chain: one open half-plane contains the
sub-disks of the target level and those of the source level of the angle class `j % 10`. -/
theorem level_HPP (dl t s : List Int) (h : chkDirP dl t s = true) (j : ℕ) :
    (∀ i : Fin NC, (Work.SeedCertRay.dskOf t ((j % 10) * NC + i.val)).toSet
        ⊆ Work.SeedCertRay.halfplane (vdirOfP dl j))
    ∧ (∀ i : Fin NC, (Work.SeedCertRay.dskOf s ((j % 10) * NC + i.val)).toSet
        ⊆ Work.SeedCertRay.halfplane (vdirOfP dl j)) := by
  simp only [chkDirP] at h
  have h1 := allS_sound h (j % 10) (mem_angQsP (Nat.mod_lt j (by norm_num)))
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hi := allS_sound h1 i.val
      (mem_subQsP i.isLt)
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at hi
    exact Work.SeedCertRay.dskOf_subset_halfplane dl t (j % 10) i.val
      (by simpa [hpDiskB] using hi.1)
  · have hi := allS_sound h1 i.val
      (mem_subQsP i.isLt)
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at hi
    exact Work.SeedCertRay.dskOf_subset_halfplane dl s (j % 10) i.val
      (by simpa [hpDiskB] using hi.2)

end Work.SeedPortraitCert
