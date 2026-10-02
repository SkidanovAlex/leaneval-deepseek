/-
# TripodCert — soundness of the level checkers

Area `Submission/Work/TripodCert/`.  This module extracts the per-`(j,i)` geometric facts from
the `decide`d level checkers of `Check.lean`, in the index form in which the chain induction
(`Work.SeedCertRay.chain_sound_sets`) consumes them:

* `level_D1` — the (D1) cover condition of one step, for every angle class and sub-disk;
* `level_HP` — the (D2) half-plane condition of one level, for every angle class.
-/
import Mathlib
import Submission.Work.TripodCert.Num
import Submission.Work.TripodCert.stepOKBT_sound
import Submission.Work.SeedCertRay.dirOKB_sound
import Submission.Work.TripodCert.Num2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

open Work.SeedCertRay

/-- Extraction of the per-`(j,i)` (D1) certificate of one level. -/
theorem chkLevelT_sound (s t c : List Int) (h : chkLevelT s t c PXM PYM RADM = true)
    (j : Fin 6) (i : Fin NC) :
    stepOKBT s t c PXM PYM RADM (((j.val + 1) % 6) * NC + i.val) (j.val * NC + i.val) = true := by
  simp only [chkLevelT] at h
  exact allS_sound (allS_sound h j.val (mem_angQsT j.isLt)) i.val
    (by rw [angQsT_eq]; exact List.mem_range.mpr i.isLt)

/-- **(D1) of one level**, in the index form of the chain: the preimage of the `(j+1)`-th disk of
the source level lies in the `j`-th disk of the target level up to sign. -/
theorem level_D1 (s t c : List Int) (h : chkLevelT s t c PXM PYM RADM = true) (j : ℕ)
    (i : Fin NC) :
    Work.SeedCertRay.DiskCover (Work.SeedCertRay.dskOf s (((j + 1) % 6) * NC + i.val))
      Work.SeedCertRay.Xb (Work.SeedCertRay.dskOf t ((j % 6) * NC + i.val)) := by
  have hstep := chkLevelT_sound s t c h ⟨j % 6, Nat.mod_lt j (by norm_num)⟩ i
  have hidx : ((j % 6 + 1) % 6) = ((j + 1) % 6) := by rw [Nat.add_mod]; norm_num
  rw [hidx] at hstep
  exact stepOKBT_sound s t c _ _ hstep

/-- **(D2) of one level**, in the index form of the chain: one open half-plane contains the
sub-disks of the target level and those of the source level of the angle class `j % 6`. -/
theorem level_HP (dl t s : List Int) (h : chkDirT dl t s = true) (j : ℕ) :
    (∀ i : Fin NC, (Work.SeedCertRay.dskOf t ((j % 6) * NC + i.val)).toSet
        ⊆ Work.SeedCertRay.halfplane (vdirOf dl j))
    ∧ (∀ i : Fin NC, (Work.SeedCertRay.dskOf s ((j % 6) * NC + i.val)).toSet
        ⊆ Work.SeedCertRay.halfplane (vdirOf dl j)) := by
  simp only [chkDirT] at h
  have h1 := allS_sound h (j % 6) (mem_angQsT (Nat.mod_lt j (by norm_num)))
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hi := allS_sound h1 i.val
      (by rw [angQsT_eq]; exact List.mem_range.mpr i.isLt)
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at hi
    exact Work.SeedCertRay.dskOf_subset_halfplane dl t (j % 6) i.val
      (by simpa [hpDiskB] using hi.1)
  · have hi := allS_sound h1 i.val
      (by rw [angQsT_eq]; exact List.mem_range.mpr i.isLt)
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at hi
    exact Work.SeedCertRay.dskOf_subset_halfplane dl s (j % 6) i.val
      (by simpa [hpDiskB] using hi.2)

/-- Extraction of the radius check of the uniqueness disc. -/
theorem radLeT_sound (R : Int) (l : List Int) (j : ℕ) (h : radLeT R l j = true) (i : Fin NC) :
    Work.SeedCertRay.gI l (3 * ((j % 6) * NC + i.val) + 2) ≤ R := by
  simp only [radLeT] at h
  have h1 := allS_sound h i.val (by rw [angQsT_eq]; exact List.mem_range.mpr i.isLt)
  simpa using decide_eq_true_iff.mp h1

/-- Extraction of the containment checks of the uniqueness disc. -/
theorem chkUBall_sound (zx zy R : Int) (l : List Int) (j : ℕ)
    (h : chkUBall zx zy R l j = true) (i : Fin NC) :
    inUBall zx zy R l j i.val = true := by
  simp only [chkUBall] at h
  exact allS_sound h i.val (by rw [angQsT_eq]; exact List.mem_range.mpr i.isLt)

end Work.TripodCert
