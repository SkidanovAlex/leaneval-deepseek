/-
# The `fk` field of the interface `N4Norm`: `FK g ∈ ℋ⁴` with `|FK g|_{ℋ⁴} ≤ C |g|_{ℋ⁴}`

The angular moment `FK g z = ∫_θ K(θ) g z θ dθ` is the radial function `Qang g 0 = -D_z L₁₂(g)`
of the paper.  This file proves that for `g` of class `Work.FTS.Nonlin.RegQ α 4` (with
`α ∈ (0, α₂]`, `α₂ ≤ 1`) the radial function `z ↦ FK g z` lies in `ℋ⁴` and its `ℋ⁴`-norm is
controlled by that of `g`, with a constant independent of `α` and `g`; this is exactly the
field `N4Norm.fkH` of `Submission/Work/FTS/Nonlinear/Interface.lean` (design §3.2).

A function of `z` alone has no angular derivatives, so only the pure `D_z`-summands of
`HkIntegrand α 4 (fun z _ => FK g z)` survive (`Work.FTS.H2.HkIntegrand_rad'`), and by
`DzdIter_Qang_ae` each of them is the angular moment `D_z^i (FK g) = Qang g i` (exactly for
`i ≤ 3`, almost everywhere for `i = 4`).  Cauchy–Schwarz in `θ` (`Qang_sq_w_sq_integral`)
then bounds every summand by `(∫_θ K²) · HkSq α 4 g`, and the structure of `HkSq α 4 g`
(its pure `D_z` slots) supplies the right-hand side.  The zero mode hypothesis
`L₁₂(g)(0) = 0` is not needed for this estimate (unlike `L12HQ`, no Hardy inequality is used).

Written by the `fk_field` task; the two analytic inputs are the separately proved modules
`DzdIter_Qang_ae` and `Qang_sq_w_sq_integral` of the same directory.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.Nonlinear.N4Fields.DzdIter_Qang_ae
import Submission.Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral
import Submission.Work.FTS.H2.L12HQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.N4Fields

set_option autoImplicit false

theorem fk_field {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.RegQ α 4 g → Work.Construction.L12 g 0 = 0 → Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧ Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z) ≤ C * Work.FTS.Nonlin.Xn α g := by
  -- the two universal constants: `∫_θ K(θ)²` and `∫_θ sin(2θ)^{-η}`
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hCθnn : 0 ≤ Cθ := by
    rw [hCθdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  refine ⟨Real.sqrt (5 * AK * Cθ) + 1, ?_, ?_⟩
  · have h := Real.sqrt_nonneg (5 * AK * Cθ)
    linarith
  intro α hαIoc g hreg _
  obtain ⟨hαpos, hαα₂⟩ := Set.mem_Ioc.mp hαIoc
  have hα1 : α ≤ 1 := le_trans hαα₂ hα₂1
  obtain ⟨hsm, hmem, -⟩ := hreg
  set u : ℝ → ℝ := fun z => Work.Elliptic.Qang g 0 z with hudef
  -- ## the a.e. identity `D_z^i (FK g) = Qang g i` for `i ≤ 4`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i u z = Work.Elliptic.Qang g i z := by
    filter_upwards [DzdIter_Qang_ae hsm hmem, MeasureTheory.Measure.ae_ne volume (0 : ℝ)]
      with z hz hne hzI
    exact hz (lt_of_le_of_ne hzI (Ne.symm hne))
  have htransfer : ∀ i : ℕ, i ≤ 4 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae] with z hz hzI
    rw [← hz hzI i (Finset.mem_range.mpr (by omega : i < 5))]
  -- ## the per-slot integrability and bound
  have hInt : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi
    exact (Qang_sq_w_sq_integral hαpos hα1 hsm hmem hi).1.congr (htransfer i hi)
  have hBnd : ∀ i : ℕ, i ≤ 4 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ AK * Work.Spaces.HkSq α 4 g := by
    intro i hi
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htransfer i hi)]
    exact (Qang_sq_w_sq_integral hαpos hα1 hsm hmem hi).2
  have hsum_int : ∀ i ∈ Finset.range 5, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 5 * (AK * Work.Spaces.HkSq α 4 g) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 5) hsum_int]
    calc ∑ i ∈ Finset.range 5, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range 5, (AK * Work.Spaces.HkSq α 4 g) :=
          Finset.sum_le_sum fun i hi => hBnd i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 5 * (AK * Work.Spaces.HkSq α 4 g) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ## the `ℋ⁴`-energy and the norm bound
  have hHkSq : Work.Spaces.HkSq α 4 (fun z θ => u z) = (∫ z in Work.Spaces.Iz,
        ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ := by
    rw [Work.Elliptic.HkSq_rad, hCθdef]
  have hbound : Work.Spaces.HkSq α 4 (fun z θ => u z) ≤ (5 * AK * Cθ) * Work.Spaces.HkSq α 4 g := by
    rw [hHkSq]
    refine le_trans (mul_le_mul_of_nonneg_right hsum_le hCθnn) (le_of_eq ?_)
    ring
  have hXng : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => u z)
      ≤ Real.sqrt (5 * AK * Cθ) * Work.FTS.Nonlin.Xn α g := by
    have h5 : 0 ≤ 5 * AK * Cθ := by nlinarith
    calc Work.FTS.Nonlin.Xn α (fun z θ => u z)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => u z)) := rfl
      _ ≤ Real.sqrt ((5 * AK * Cθ) * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (5 * AK * Cθ) * Work.FTS.Nonlin.Xn α g := by
          rw [Real.sqrt_mul h5]
          rfl
  -- ## membership in `ℋ⁴`
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hHkMem : Work.Spaces.HkMem α 4 (fun z θ => u z) := by
    constructor
    · intro z hz
      refine MeasureTheory.Integrable.congr (f := fun θ =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ).symm)
    · refine MeasureTheory.Integrable.congr (f := fun z =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 5) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθdef]
        rw [setIntegral_congr_fun (f := fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => u z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 5,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ)]
        rw [MeasureTheory.integral_const_mul]
  -- ## `FK g` is the radial function `u`
  have hfun : (fun z (_ : ℝ) => Work.Construction.FK g z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    simp only [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
    rw [← Work.Elliptic.Ktheta_eq_K]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHkMem
  · rw [hfun]
    exact le_trans hXn
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hXng)

end Work.FTS.Nonlinear.N4Fields
