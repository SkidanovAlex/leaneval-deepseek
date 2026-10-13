import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The high-order `z`-terms of the `H⁴`-norm of `L₁₂(g)`: for `1 ≤ i ≤ 4` the `i`-th pure
`D_z`-term of `L₁₂(g)` is `-Q_i(g)`, and Cauchy–Schwarz in `θ` bounds its square by
`(∫_θ K²)·∫_θ (D_z^{i-1}g)²`; integrating against the radial weight `w²` and using that
`∫ w² ∫_θ (D_z^j g)² ≤ HkSq α 4 g` for `j ≤ 4` gives the estimate. -/
theorem L12TermHigh (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (hmem : Work.Spaces.HkMem α 4 g)
    (hid : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      Work.Spaces.DzIter k (fun z θ => Work.Elliptic.L12 g z) z θ = - Work.Elliptic.Qang g (k - 1) z)
    {i : ℕ} (hi : 1 ≤ i) (hi4 : i ≤ 4) :
    MeasureTheory.IntegrableOn (fun z =>
        (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz
      ∧ (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
  -- write `i = j + 1` so that `DzdIter i` is a genuine derivative
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  -- the pointwise identification of the high `D_z`-derivative
  have hpt : ∀ z : ℝ, 0 < z →
      DzdIter (j + 1) (fun z => L12 g z) z = -Qang g j z := by
    intro z hz
    have h1 : DzdIter (j + 1) (fun z => L12 g z) z
        = Work.Spaces.DzIter (j + 1) (fun z θ => L12 g z) z 0 :=
      (DzIter_rad (fun z => L12 g z) (j + 1) z 0).symm
    rw [h1, hid (j + 1) (by omega) (by omega) z hz 0, Nat.add_sub_cancel]
  -- measurability: any iterated derivative is measurable, and so is the weight
  have hmeas : AEStronglyMeasurable (fun z =>
      (DzdIter (j + 1) (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    have h1 : Measurable (fun z => DzdIter (j + 1) (fun z => L12 g z) z) := by
      simp only [DzdIter_succ, Dzd]
      exact measurable_id.mul (measurable_deriv (DzdIter j (fun z => L12 g z)))
    have h2 : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
      simp only [Work.Spaces.w]
      fun_prop
    exact ((h1.pow_const 2).mul h2).aestronglyMeasurable
  -- the dominating integrable function
  have hH : Integrable (fun z => (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2) *
      ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2))
      (volume.restrict Work.Spaces.Iz) :=
    (integrableOn_w_sq_mul_int_sq α g hsm hmem (by omega : j ≤ 4)).1.const_mul _
  -- the pointwise bound, almost everywhere
  have hbound : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      ‖(DzdIter (j + 1) (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2‖ ≤
        (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2) *
          ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
    change ∀ᵐ z ∂(volume.restrict (Set.Ici (0:ℝ))), _
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0:ℝ)] with z hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    have hcs := Qang_sq_le g hsm j (z := z) (by linarith : -1 < z)
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    rw [hpt z hzpos, neg_sq, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) hw2)]
    calc (Qang g j z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ((∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hcs hw2
      _ = (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2)
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
          ring
  have hFint : Integrable (fun z =>
      (DzdIter (j + 1) (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iz) := Integrable.mono' hH hmeas hbound
  refine ⟨hFint, ?_⟩
  have hle : (∫ z in Work.Spaces.Iz,
        (DzdIter (j + 1) (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2) *
          ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) :=
    MeasureTheory.integral_mono_ae hFint hH (hbound.mono fun z hz => by
      rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))] at hz)
  calc (∫ z in Work.Spaces.Iz,
        (DzdIter (j + 1) (fun z => L12 g z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2) *
          ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := hle
    _ = (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2) *
          (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g :=
        mul_le_mul_of_nonneg_left
          (integrableOn_w_sq_mul_int_sq α g hsm hmem (by omega : j ≤ 4)).2
          (integral_nonneg fun θ => sq_nonneg (Ktheta θ))

end Work.Elliptic
