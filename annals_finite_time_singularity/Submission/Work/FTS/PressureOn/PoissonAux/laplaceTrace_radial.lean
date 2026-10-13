import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.PressureOn.PoissonAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Laplacian of a radial function on `ℝ³`

The classical formula

  `Δ (g ∘ ‖·‖) (x) = g''(‖x‖) + 2 g'(‖x‖) / ‖x‖`   (`x ≠ 0`)

for the Laplacian of a radially symmetric function `x ↦ g ‖x‖` on `ℝ³`, in the form computed by the
trace `laplaceTrace` of the Hessian along the standard basis `FiniteTimeSingularity.e`.

The proof is the classical computation, split into the following pieces (all in this file):

* `hasFDerivAt_norm_ne` — the Fréchet derivative of the norm on `ℝ³` at `x ≠ 0`:
  `fderiv ℝ (‖·‖) x = ‖x‖⁻¹ • innerSL ℝ x`, obtained from `hasStrictFDerivAt_norm_sq` by the chain
  rule with `Real.sqrt`.  (Mathlib does not provide this in this explicit form.)
* `hasFDerivAt_radial_comp` — the chain rule for radially symmetric functions:
  `fderiv ℝ (fun w => G ‖w‖) x = (deriv G ‖x‖) • fderiv ℝ (‖·‖) x`.
* `laplaceTrace_radial_diag` — the diagonal entries of the Hessian,
  `∂ᵢ∂ᵢ (g ∘ ‖·‖) (x) = g'(‖x‖)/‖x‖ + (g''(‖x‖)‖x‖⁻² - g'(‖x‖)‖x‖⁻³)·(xᵢ)²`,
  computed by the product rule from the two lemmas above.
* the assembly `laplaceTrace_radial`, using `∑ i, (xᵢ)² = ‖x‖²`.
-/

open FiniteTimeSingularity Set MeasureTheory Metric
open scoped Topology RealInnerProductSpace

namespace Work.FTS.PressureOn.PoissonAux

/-- The Fréchet derivative of the norm of `ℝ³` at a nonzero point: `fderiv ℝ (‖·‖) x` is the
continuous linear functional `v ↦ ‖x‖⁻¹ * ⟪x, v⟫`, i.e. `‖x‖⁻¹ • innerSL ℝ x`. -/
lemma hasFDerivAt_norm_ne {x : R3} (hx : x ≠ 0) :
    HasFDerivAt (fun y : R3 => ‖y‖) ((‖x‖)⁻¹ • innerSL ℝ x) x := by
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h1 : HasFDerivAt (fun y : R3 => ‖y‖ ^ 2) ((2 : ℝ) • innerSL ℝ x) x := by
    have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    rwa [← ofNat_smul_eq_nsmul (R := ℝ) 2 (innerSL ℝ x)] at h
  have h2 := h1.sqrt (pow_ne_zero 2 hnorm_ne)
  have hfun : (fun y : R3 => √(‖y‖ ^ 2)) = fun y : R3 => ‖y‖ := by
    funext y
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg y)]
  rw [hfun] at h2
  convert h2 using 1
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
  rw [show (1 / (2 * ‖x‖)) • ((2 : ℝ) • (innerSL ℝ x))
        = ((1 / (2 * ‖x‖)) * 2) • (innerSL ℝ x) from smul_smul (M := ℝ) _ _ _]
  have hc : (1 / (2 * ‖x‖)) * 2 = (‖x‖)⁻¹ := by field_simp
  rw [hc]

/-- The chain rule for radially symmetric functions on `ℝ³`: if `G` has derivative `c` at `‖x‖`
with `x ≠ 0`, then `w ↦ G ‖w‖` has Fréchet derivative `c • fderiv ℝ (‖·‖) x` at `x`. -/
lemma hasFDerivAt_radial_comp {G : ℝ → ℝ} {c : ℝ} {x : R3} (hx : x ≠ 0)
    (hG : HasDerivAt G c ‖x‖) :
    HasFDerivAt (fun w : R3 => G ‖w‖) (c • ((‖x‖)⁻¹ • innerSL ℝ x)) x := by
  have h := hG.comp_hasFDerivAt x (hasFDerivAt_norm_ne hx)
  simpa only [Function.comp_def] using h

/-- The diagonal entry `∂ᵢ∂ᵢ` of the Hessian of the radial function `g ∘ ‖·‖` in the standard
basis `FiniteTimeSingularity.e`:

  `∂ᵢ∂ᵢ (g ∘ ‖·‖) (x) = g'(‖x‖)/‖x‖ + (g''(‖x‖)‖x‖⁻² - g'(‖x‖)‖x‖⁻³)·(xᵢ)²`

for `x ≠ 0` and `g` of class `C²`. -/
lemma laplaceTrace_radial_diag {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {x : R3} (hx : x ≠ 0)
    (i : Fin 3) :
    fderiv ℝ (fun w : R3 => fderiv ℝ (fun y : R3 => g ‖y‖) w (FiniteTimeSingularity.e i)) x
        (FiniteTimeSingularity.e i)
      = deriv g ‖x‖ / ‖x‖
        + (deriv (deriv g) ‖x‖ * (‖x‖ ^ 2)⁻¹ - deriv g ‖x‖ * (‖x‖ ^ 3)⁻¹)
            * (x i) ^ 2 := by
  have hne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  -- the first derivative of `g ∘ ‖·‖` away from the origin
  have hφ : ∀ w : R3, w ≠ 0 → fderiv ℝ (fun y : R3 => g ‖y‖) w
      = (deriv g ‖w‖) • ((‖w‖)⁻¹ • innerSL ℝ w) := by
    intro w hw
    have hG : HasDerivAt g (deriv g ‖w‖) ‖w‖ :=
      ((hg.differentiable (by norm_num)) ‖w‖).hasDerivAt
    rw [(hasFDerivAt_radial_comp hw hG).fderiv]
  -- hence the diagonal-entry function agrees with an explicit product near `x`
  have hdiag : (fun w : R3 => fderiv ℝ (fun y : R3 => g ‖y‖) w (FiniteTimeSingularity.e i))
      =ᶠ[𝓝 x]
        (fun w : R3 =>
          deriv g ‖w‖ * ((‖w‖)⁻¹ * (innerSL ℝ (FiniteTimeSingularity.e i)) w)) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with w hw
    rw [hφ w hw]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [real_inner_comm w (FiniteTimeSingularity.e i)]
  rw [hdiag.fderiv_eq]
  -- the derivative of the radial factor `w ↦ deriv g ‖w‖`
  have hA : HasFDerivAt (fun w : R3 => deriv g ‖w‖)
      ((deriv (deriv g) ‖x‖) • ((‖x‖)⁻¹ • innerSL ℝ x)) x := by
    refine hasFDerivAt_radial_comp hx ?_
    exact ((hg.differentiable_deriv_two ‖x‖)).hasDerivAt
  -- the derivative of `w ↦ ‖w‖⁻¹`
  have hD : HasFDerivAt (fun w : R3 => (‖w‖)⁻¹)
      ((-(‖x‖ ^ 2)⁻¹) • ((‖x‖)⁻¹ • innerSL ℝ x)) x := by
    have hdd : HasDerivAt (fun r : ℝ => r⁻¹) (-(‖x‖ ^ 2)⁻¹) ‖x‖ := hasDerivAt_inv hne
    have h := hdd.comp_hasFDerivAt x (hasFDerivAt_norm_ne hx)
    simpa only [Function.comp_def] using h
  -- the (linear) factor `w ↦ ⟪eᵢ, w⟫`
  have hM : HasFDerivAt (fun w : R3 => (innerSL ℝ (FiniteTimeSingularity.e i)) w)
      (innerSL ℝ (FiniteTimeSingularity.e i)) x := ContinuousLinearMap.hasFDerivAt _
  have hB := hD.mul hM
  have hAB := hA.mul hB
  -- put the derivative in the form needed by the rewrite (the function is the explicit product)
  have hAB' : HasFDerivAt
      (fun w : R3 => deriv g ‖w‖ * ((‖w‖)⁻¹ * (innerSL ℝ (FiniteTimeSingularity.e i)) w))
      (deriv g ‖x‖ • ((‖x‖)⁻¹ • innerSL ℝ (FiniteTimeSingularity.e i) +
          (innerSL ℝ (FiniteTimeSingularity.e i)) x • (-(‖x‖ ^ 2)⁻¹ • (‖x‖)⁻¹ • innerSL ℝ x)) +
        ((fun w : R3 => (‖w‖)⁻¹) *
          fun w : R3 => (innerSL ℝ (FiniteTimeSingularity.e i)) w) x •
          deriv (deriv g) ‖x‖ • (‖x‖)⁻¹ • innerSL ℝ x) x := hAB
  rw [hAB'.fderiv]
  simp only [add_apply, smul_apply, Pi.mul_apply, innerSL_apply_apply, smul_eq_mul]
  -- the standard basis is orthonormal
  have hee : inner ℝ (FiniteTimeSingularity.e i) (FiniteTimeSingularity.e i) = 1 := by
    rw [FiniteTimeSingularity.e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hze : inner ℝ x (FiniteTimeSingularity.e i) = x i := by
    rw [FiniteTimeSingularity.e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hez : inner ℝ (FiniteTimeSingularity.e i) x = x i := by
    rw [real_inner_comm, hze]
  rw [hee, hze, hez]
  field_simp
  ring

theorem laplaceTrace_radial {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {x : R3} (hx : x ≠ 0) :
    laplaceTrace (fun y : R3 => g ‖y‖) x = deriv (deriv g) ‖x‖ + 2 * deriv g ‖x‖ / ‖x‖ := by
  have hne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  -- `∑ i, (xᵢ)² = ‖x‖²`
  have hsum : ∑ i : Fin 3, (x i) ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [laplaceTrace]
  rw [Finset.sum_congr rfl (fun i _ => laplaceTrace_radial_diag hg hx i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  field_simp
  ring

end Work.FTS.PressureOn.PoissonAux
