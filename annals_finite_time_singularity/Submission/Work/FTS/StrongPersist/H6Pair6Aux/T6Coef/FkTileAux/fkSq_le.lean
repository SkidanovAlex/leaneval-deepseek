import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.QangAe6
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.H2.L12HQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem fkSq_le : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK f z)
      ≤ C * (1 + Work.Spaces.HkNorm α 6 f) := by
  -- the two universal angular constants
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hCθnn : 0 ≤ Cθ := by
    rw [hCθdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  refine ⟨Real.sqrt (7 * AK * Cθ) + 1, ?_, ?_⟩
  · have h := Real.sqrt_nonneg (7 * AK * Cθ)
    linarith
  intro α _hα f hsm hmem
  -- the angular moment is the radial function `u := Qang f 0`
  set u : ℝ → ℝ := fun z => Work.Elliptic.Qang f 0 z with hudef
  -- ## the a.e. identity `D_z^i (Qang f 0) = Qang f i` on `Iz`, `i ≤ 6`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 7,
      Work.Elliptic.DzdIter i u z = Work.Elliptic.Qang f i z := by
    filter_upwards [QangAe6 hsm hmem, MeasureTheory.Measure.ae_ne volume (0 : ℝ)]
      with z hz hne hzI
    exact hz (lt_of_le_of_ne hzI (Ne.symm hne))
  have htransfer : ∀ i : ℕ, i ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae] with z hz hzI
    rw [← hz hzI i (Finset.mem_range.mpr (by omega : i < 7))]
  -- ## the per-slot integrability and the weighted `L²`-bound
  have hInt : ∀ i : ℕ, i ≤ 6 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => (QangSq6Full (α := α) hsm hmem i hi).1.congr (htransfer i hi)
  have hBnd : ∀ i : ℕ, i ≤ 6 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ AK * Work.Spaces.HkSq α 6 f := by
    intro i hi
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htransfer i hi)]
    exact (QangSq6Full (α := α) hsm hmem i hi).2
  have hsum_int : ∀ i ∈ Finset.range 7, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 7,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 7 * (AK * Work.Spaces.HkSq α 6 f) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 7) hsum_int]
    calc ∑ i ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range 7, (AK * Work.Spaces.HkSq α 6 f) :=
          Finset.sum_le_sum fun i hi =>
            hBnd i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 7 * (AK * Work.Spaces.HkSq α 6 f) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ## the `ℋ⁶`-energy of the radial function
  have hHkSq : Work.Spaces.HkSq α 6 (fun z θ => u z) = (∫ z in Work.Spaces.Iz,
        ∑ i ∈ Finset.range 7,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ := by
    rw [Work.Elliptic.HkSq_rad, hCθdef]
  have hbound : Work.Spaces.HkSq α 6 (fun z θ => u z)
      ≤ (7 * AK * Cθ) * Work.Spaces.HkSq α 6 f := by
    rw [hHkSq]
    refine le_trans (mul_le_mul_of_nonneg_right hsum_le hCθnn) (le_of_eq ?_)
    ring
  -- ## `FK f` is the radial function `u`
  have hfun : (fun z (_ : ℝ) => Work.Construction.FK f z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    simp only [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
    rw [← Work.Elliptic.Ktheta_eq_K]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
  rw [hfun]
  -- ## the norm bound
  have h7nn : 0 ≤ 7 * AK * Cθ := by nlinarith
  have hle : Work.Spaces.HkNorm α 6 (fun z θ => u z)
      ≤ Real.sqrt (7 * AK * Cθ) * Work.Spaces.HkNorm α 6 f := by
    calc Work.Spaces.HkNorm α 6 (fun z θ => u z)
        = Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => u z)) := rfl
      _ ≤ Real.sqrt ((7 * AK * Cθ) * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (7 * AK * Cθ) * Work.Spaces.HkNorm α 6 f := by
          rw [Real.sqrt_mul h7nn]
          rfl
  refine le_trans hle ?_
  have ha : 0 ≤ Real.sqrt (7 * AK * Cθ) := Real.sqrt_nonneg _
  have hf : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have h1 : Real.sqrt (7 * AK * Cθ) * Work.Spaces.HkNorm α 6 f
      ≤ Real.sqrt (7 * AK * Cθ) * (1 + Work.Spaces.HkNorm α 6 f) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) ha
  have h2 : Real.sqrt (7 * AK * Cθ) * (1 + Work.Spaces.HkNorm α 6 f)
      ≤ (Real.sqrt (7 * AK * Cθ) + 1) * (1 + Work.Spaces.HkNorm α 6 f) :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by linarith)
  exact le_trans h1 h2

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
