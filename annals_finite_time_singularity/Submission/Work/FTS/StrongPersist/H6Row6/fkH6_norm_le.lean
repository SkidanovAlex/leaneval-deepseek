import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The sharp form of the `FK`-bound.**  The angular average
`FK f z = ∫_θ f z θ · K(θ) dθ` is a radial function whose `ℋ⁶`-norm is controlled by the
`ℋ⁶`-norm of `f` with the *universal* constant `√(7 · ∫_θ K(θ)² · ∫_θ sin(2θ)^{-η})` —
no additive `1` (this is the estimate the sibling `fkSq_le` proves and then deliberately
weakens to the shape `C(1 + |f|)`).

The proof is the Cauchy–Schwarz argument in `θ` (via `QangSq6Full`), summed over the
levels `i ≤ 6` (via `HkSq_rad`). -/
private theorem fkH6_norm_le_sqrt (α : ℝ) (hα : α ∈ Set.Ioc 0 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK f z)
      ≤ Real.sqrt (7 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        * Work.Spaces.HkNorm α 6 f := by
  have hαpos : 0 < α := hα.1
  have hαle : α ≤ 1 := hα.2
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
  calc Work.Spaces.HkNorm α 6 (fun z θ => u z)
      = Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => u z)) := rfl
    _ ≤ Real.sqrt ((7 * AK * Cθ) * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (7 * AK * Cθ) * Work.Spaces.HkNorm α 6 f := by
        rw [Real.sqrt_mul h7nn]
        rfl

theorem fkH6_norm_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK f z)
      ≤ C * Work.Spaces.HkNorm α 6 f := by
  refine ⟨Real.sqrt (7 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) + 1, ?_, ?_⟩
  · have h := Real.sqrt_nonneg (7 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
    linarith
  intro α hα0 hα1 f hsm hmem
  refine le_trans (fkH6_norm_le_sqrt α ⟨hα0, hα1⟩ f hsm hmem) ?_
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (Work.Spaces.HkNorm_nonneg α 6 f)

end Work.FTS.StrongPersist.H6Row6
