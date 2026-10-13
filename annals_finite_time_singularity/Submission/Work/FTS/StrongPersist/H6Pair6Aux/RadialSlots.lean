import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkSlots
import Submission.Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff
import Submission.Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.IPGen.OpenBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem slots_radial_mul {X r : ℝ → ℝ} {M : ℝ}
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hr : ContDiffOn ℝ 6 r (Set.Ioi 0))
    (hXint : ∀ b : ℕ, b ≤ 6 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    (hM : ∀ m : ℕ, m ≤ 6 → ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter m r z| ≤ M) :
    ∀ j : ℕ, j ≤ 6 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (fun z => X z * r z) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
  have hXc : ∀ b ≤ 6, ContinuousOn (fun z : ℝ => Work.Elliptic.DzdIter b X z) (Set.Ioi 0) :=
    fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := X) (n := 6)
      (fun m hm => hX.of_le (by exact_mod_cast hm)) (a := b) (t := 0) (by omega)).continuousOn
  have hrc : ∀ b ≤ 6, ContinuousOn (fun z : ℝ => Work.Elliptic.DzdIter b r z) (Set.Ioi 0) :=
    fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := r) (n := 6)
      (fun m hm => hr.of_le (by exact_mod_cast hm)) (a := b) (t := 0) (by omega)).continuousOn
  have hwc : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    simp only [Work.Spaces.w]
    exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  intro j hj
  -- the Leibniz identity on `(0,∞)`
  have hleib : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (fun z => X z * r z) z
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b X z * Work.Elliptic.DzdIter (j - b) r z) :=
    fun z hz => Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff j X r
      (fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := X)
        (n := 6) (fun m hm => hX.of_le (by exact_mod_cast hm)) (a := b) (t := 1)
        (by omega)).differentiableOn (by norm_num))
      (fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := r)
        (n := 6) (fun m hm => hr.of_le (by exact_mod_cast hm)) (a := b) (t := 1)
        (by omega)).differentiableOn (by norm_num)) z hz
  have hXc : ∀ b ≤ 6, ContinuousOn (fun z : ℝ => Work.Elliptic.DzdIter b X z) (Set.Ioi 0) :=
    fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := X) (n := 6)
      (fun m hm => hX.of_le (by exact_mod_cast hm)) (a := b) (t := 0) (by omega)).continuousOn
  have hrc : ∀ b ≤ 6, ContinuousOn (fun z : ℝ => Work.Elliptic.DzdIter b r z) (Set.Ioi 0) :=
    fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := r) (n := 6)
      (fun m hm => hr.of_le (by exact_mod_cast hm)) (a := b) (t := 0) (by omega)).continuousOn
  have hwc : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    simp only [Work.Spaces.w]
    exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  -- the (continuous) representative of the integrand on `(0,∞)`
  have hcont : ContinuousOn (fun z : ℝ =>
      (Work.Elliptic.DzdIter j (fun z => X z * r z) z * Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.congr ?_ (fun z hz => by rw [hleib z hz])
    show ContinuousOn (fun z : ℝ => ((∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
      * (Work.Elliptic.DzdIter b X z * Work.Elliptic.DzdIter (j - b) r z))
      * Work.Spaces.w z) ^ 2) (Set.Ioi 0)
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.mul (continuousOn_finsetSum _ fun b hb => ?_) hwc
    have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    exact ContinuousOn.mul continuousOn_const
      ((hXc b (by omega)).mul (hrc (j - b) (by omega)))
  -- the majorant
  have hmaj : MeasureTheory.IntegrableOn (fun z : ℝ =>
      (7 * 4096 * M ^ 2 + 1) * ∑ b ∈ Finset.range 7,
        (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    (MeasureTheory.integrable_finsetSum (Finset.range 7) (fun b hb =>
      hXint b (Nat.le_of_lt_succ (Finset.mem_range.mp hb)))).const_mul _
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.Elliptic.DzdIter j (fun z => X z * r z) z * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => (Work.Elliptic.DzdIter j (fun z => X z * r z) z * Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      hcont.aestronglyMeasurable isOpen_Ioi.measurableSet
    rwa [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))] at h1
  refine hmaj.mono' haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
  have hz0 : (0 : ℝ) ≤ z := hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  rcases eq_or_lt_of_le hz0 with hz00 | hzpos
  · rw [← hz00]
    simp only [Work.Spaces.w]
    norm_num
  · have hkey : ((∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b X z * Work.Elliptic.DzdIter (j - b) r z))
        * Work.Spaces.w z)
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Elliptic.DzdIter (j - b) r z * Work.Spaces.w z)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hleib z hzpos, hkey]
    set f : ℕ → ℝ := fun b => (j.choose b : ℝ) * (Work.Elliptic.DzdIter b X z
      * (Work.Elliptic.DzdIter (j - b) r z * Work.Spaces.w z)) with hf
    have hch : ∀ b ∈ Finset.range (j + 1), (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := by
      intro b _
      have h1 : (((j.choose b : ℕ) : ℝ)) ≤ 64 := by
        have h2 : j.choose b ≤ 2 ^ j := Nat.choose_le_two_pow j b
        have h3 : 2 ^ j ≤ 64 := by
          calc 2 ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hj
            _ = 64 := by norm_num
        exact_mod_cast le_trans h2 h3
      have h0 : (0 : ℝ) ≤ (((j.choose b : ℕ) : ℝ)) := by positivity
      nlinarith [h1, h0]
    have hterm : ∀ b ∈ Finset.range (j + 1),
        (f b) ^ 2 ≤ 4096 * M ^ 2 * (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2 := by
      intro b hb
      have hM' : (Work.Elliptic.DzdIter (j - b) r z) ^ 2 ≤ M ^ 2 := by
        have h := hM (j - b) (by omega) z hzpos
        have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        rwa [sq_abs] at h2
      have hstep2 : (((j.choose b : ℕ) : ℝ)) ^ 2
          * ((Work.Elliptic.DzdIter (j - b) r z) ^ 2) ≤ 4096 * M ^ 2 :=
        mul_le_mul (hch b hb) hM' (sq_nonneg _) (by norm_num)
      have hgoal : (f b) ^ 2 = (((j.choose b : ℕ) : ℝ)) ^ 2
          * ((Work.Elliptic.DzdIter (j - b) r z) ^ 2)
          * ((Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2) := by
        simp only [hf]
        push_cast
        ring
      rw [hgoal]
      exact mul_le_mul_of_nonneg_right hstep2 (sq_nonneg _)
    have hstep : (∑ b ∈ Finset.range (j + 1), (f b) ^ 2)
        ≤ ∑ b ∈ Finset.range (j + 1),
            4096 * M ^ 2 * (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2 :=
      Finset.sum_le_sum hterm
    have hstepM : (∑ b ∈ Finset.range (j + 1), (f b) ^ 2)
        ≤ 4096 * M ^ 2 * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2) := by
      refine hstep.trans (le_of_eq ?_)
      rw [Finset.mul_sum]
    have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := f)
    have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 7 := by
      rw [Finset.card_range]; exact_mod_cast (by omega : j + 1 ≤ 7)
    have hsum7 : (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2)
        ≤ ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun b hb => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hb) (by omega)))
        (fun b _ _ => sq_nonneg _)
    have hnn7 : 0 ≤ ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2 :=
      Finset.sum_nonneg fun b _ => sq_nonneg _
    have hM2 : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
    calc (∑ b ∈ Finset.range (j + 1), f b) ^ 2
        ≤ (((Finset.range (j + 1)).card : ℕ) : ℝ) * (∑ b ∈ Finset.range (j + 1), (f b) ^ 2) :=
          hsq
      _ ≤ 7 * (∑ b ∈ Finset.range (j + 1), (f b) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun b _ => sq_nonneg _)
      _ ≤ 7 * (4096 * M ^ 2 * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstepM (by norm_num)
      _ ≤ 7 * (4096 * M ^ 2 * (∑ b ∈ Finset.range 7,
            (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsum7 (by positivity)) (by norm_num)
      _ ≤ (7 * 4096 * M ^ 2 + 1) * (∑ b ∈ Finset.range 7,
            (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2) := by
          nlinarith [hnn7, hM2]

end Work.FTS.StrongPersist.H6Pair6Aux
