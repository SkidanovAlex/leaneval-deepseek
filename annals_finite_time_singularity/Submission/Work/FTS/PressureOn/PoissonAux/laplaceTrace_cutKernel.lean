/-
# The Laplacian of the truncated Newtonian kernel

This module computes the classical Laplacian identity for the truncated Newtonian kernel

`Δ (smallCut ε · newtonKernel) x = massKernel ε x`  (`x ≠ 0`),

i.e. `Δ ((1 - χ(‖·‖²/ε²))/(4π‖·‖)) x = (4π‖x‖)⁻¹ · ρ_ε''(‖x‖)` with `ρ_ε(r) = 1 - χ(r²/ε²)`.

The point is that on `x ≠ 0` the *harmonic* factor `(4π‖·‖)⁻¹` contributes nothing: for the
radial function `r ↦ h r / (4π r)` one has `f'' + 2f'/r = h''/(4π r)`.

## Structure of the proof

The truncated kernel is the *radial* function `x ↦ g ‖x‖` with `g r = ρ_ε(r)·(4π r)⁻¹`; we write
it instead as a function of `t = ‖x‖²`, namely `cutProfile ε t = (1 - χ(t/ε²))/(4π √t)`, so that
`cutProfile ε (‖y‖²) = smallCut ε y * newtonKernel y` and so that the existing Hessian formula
`Work.FTS.PressureOn.Auxiliary.normSq_hessian` (for functions of `‖·‖²`) applies:

* `laplaceTrace_normSq`:  `Δ (F ∘ ‖·‖²) x = 6 F'(‖x‖²) + 4‖x‖² F''(‖x‖²)`;
* `deriv_deriv_comp_sq`:  the two-variable change of variables `r ↦ r²` in the radial Laplacian,
  `deriv (deriv (F ∘ (·)²)) ρ + 2 deriv (F ∘ (·)²) ρ / ρ = 6 F'(ρ²) + 4ρ² F''(ρ²)`;
* `oneDim_radial_laplace`: `f'' + 2f'/r = h''/(4π r)` for `f = h/(4π r)`.

(The last two are the sibling modules `deriv_deriv_comp_sq` and `oneDim_radial_laplace`.)
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.Auxiliary.normSq_hessian
import Submission.Work.FTS.PressureOn.PoissonAux.deriv_deriv_comp_sq
import Submission.Work.FTS.PressureOn.PoissonAux.oneDim_radial_laplace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-! ## The `t`-variable profile of the truncated kernel -/

/-- The profile of the truncated Newtonian kernel, viewed as a function of `t = ‖y‖²`:
`cutProfile ε t = (1 - χ(t/ε²))/(4π√t)`, so that
`cutProfile ε (‖y‖²) = smallCut ε y * newtonKernel y`. -/
noncomputable def cutProfile (ε t : ℝ) : ℝ :=
  (1 - radialCut (t / ε ^ 2)) / (4 * Real.pi * Real.sqrt t)

theorem cutProfile_apply (ε : ℝ) (t : ℝ) :
    cutProfile ε t = (1 - radialCut (t / ε ^ 2)) / (4 * Real.pi * Real.sqrt t) := rfl

/-- `cutProfile ε (‖y‖²)` *is* the truncated Newtonian kernel. -/
theorem cutProfile_normSq (ε : ℝ) (y : R3) :
    cutProfile ε (‖y‖ ^ 2) = smallCut ε y * newtonKernel y := by
  rw [cutProfile_apply, Real.sqrt_sq (norm_nonneg y), smallCut_apply, newtonKernel,
    div_eq_mul_inv]

/-- `cutProfile ε` is `C²` on `ℝ`: on `t < ε²` it vanishes identically, and for `t > 0` it is the
quotient of the smooth numerator `1 - χ(t/ε²)` by the smooth nonvanishing denominator `4π√t`. -/
theorem contDiff_cutProfile (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ 2 (cutProfile ε) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < ε ^ 2
  · have hmem : Iio (ε ^ 2) ∈ 𝓝 t := Iio_mem_nhds ht
    refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : ℝ => (0 : ℝ)) (f₁ := cutProfile ε)
      (x := t) contDiffAt_const ?_
    filter_upwards [hmem] with s hs
    rw [cutProfile_apply]
    have hs1 : s / ε ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact le_of_lt hs
    rw [radialCut_eq_one hs1, sub_self, zero_div]
  · have htpos : 0 < t := lt_of_lt_of_le (by positivity) (not_lt.mp ht)
    have hnum : ContDiffAt ℝ 2 (fun s : ℝ => 1 - radialCut (s / ε ^ 2)) t :=
      (contDiff_const.sub ((contDiff_radialCut 2).comp (contDiff_id.div_const (ε ^ 2)))).contDiffAt
    have hsqrt : ContDiffAt ℝ 2 (fun s : ℝ => Real.sqrt s) t :=
      Real.contDiffAt_sqrt (x := t) (n := 2) (ne_of_gt htpos)
    have hden : ContDiffAt ℝ 2 (fun s : ℝ => 4 * Real.pi * Real.sqrt s) t :=
      (contDiffAt_const (c := 4 * Real.pi)).mul hsqrt
    have hne : (4 * Real.pi * Real.sqrt t) ≠ 0 := by
      have h1 : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
      have h2 : 0 < 4 * Real.pi := by positivity
      positivity
    have hquot : ContDiffAt ℝ 2
        (fun s : ℝ => (1 - radialCut (s / ε ^ 2)) / (4 * Real.pi * Real.sqrt s)) t :=
      hnum.div hden hne
    exact hquot

/-- The one-dimensional profile `rhoProfile ε` of the cutoff is `C²`. -/
theorem contDiff_rhoProfile (ε : ℝ) : ContDiff ℝ 2 (rhoProfile ε) :=
  contDiff_const.sub ((contDiff_radialCut 2).comp ((contDiff_id (𝕜 := ℝ)).pow 2 |>.div_const (ε ^ 2)))

/-! ## The Laplacian of a function of `‖·‖²` -/

/-- **The Laplacian of a function of `‖x‖²`**: `Δ (F ∘ ‖·‖²) x = 6F'(‖x‖²) + 4‖x‖²F''(‖x‖²)`.
This is the trace, in the standard basis `FiniteTimeSingularity.e`, of the Hessian formula
`Work.FTS.PressureOn.Auxiliary.normSq_hessian`. -/
theorem laplaceTrace_normSq (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (x : R3) :
    laplaceTrace (fun y : R3 => F (‖y‖ ^ 2)) x
      = 6 * deriv F (‖x‖ ^ 2) + 4 * ‖x‖ ^ 2 * deriv (deriv F) (‖x‖ ^ 2) := by
  have hsum : ∑ i : Fin 3, (x i) ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
    simp only [Real.norm_eq_abs, sq_abs]
  have hee : ∀ i : Fin 3, inner ℝ (e i) (e i) = (1 : ℝ) := by
    intro i
    rw [e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hxe : ∀ i : Fin 3, inner ℝ x (e i) = x i := by
    intro i
    rw [e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hterm : ∀ i : Fin 3,
      (fderiv ℝ (fun w : R3 => fderiv ℝ (fun y : R3 => F (‖y‖ ^ 2)) w (e i)) x) (e i)
        = 2 * deriv F (‖x‖ ^ 2) + 4 * deriv (deriv F) (‖x‖ ^ 2) * (x i) ^ 2 := by
    intro i
    rw [Work.FTS.PressureOn.Auxiliary.normSq_hessian F hF x (e i) (e i), hee i, hxe i]
    ring
  rw [laplaceTrace, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum, hsum]
  simp only [nsmul_eq_mul]
  ring

/-! ## The main computation -/

/-- **The Laplacian of the truncated Newtonian kernel.**
For `ε > 0` and `x ≠ 0`, the Laplacian of `y ↦ smallCut ε y * newtonKernel y` at `x` is
`massKernel ε x = (4π‖x‖)⁻¹ ρ_ε''(‖x‖)`. -/
theorem laplaceTrace_cutKernel (ε : ℝ) (hε : 0 < ε) {x : R3} (hx : x ≠ 0) :
    laplaceTrace (fun y : R3 => smallCut ε y * newtonKernel y) x = massKernel ε x := by
  have hρ : 0 < ‖x‖ := norm_pos_iff.mpr hx
  -- the truncated kernel is the one-dimensional profile composed with `‖·‖²`
  have hfun : (fun y : R3 => smallCut ε y * newtonKernel y)
      = fun y : R3 => cutProfile ε (‖y‖ ^ 2) := by
    funext y
    exact (cutProfile_normSq ε y).symm
  -- near `‖x‖ > 0`, `r ↦ cutProfile ε (r²)` is `r ↦ rhoProfile ε r / (4π r)`
  have hev : (fun r : ℝ => cutProfile ε (r ^ 2))
      =ᶠ[𝓝 ‖x‖] (fun r : ℝ => rhoProfile ε r / (4 * Real.pi * r)) := by
    filter_upwards [Ioi_mem_nhds hρ] with r hr
    rw [cutProfile_apply, rhoProfile_apply, Real.sqrt_sq (le_of_lt hr)]
  have hd1 : deriv (fun r : ℝ => cutProfile ε (r ^ 2)) ‖x‖
      = deriv (fun r : ℝ => rhoProfile ε r / (4 * Real.pi * r)) ‖x‖ := hev.deriv_eq
  have hd2 : deriv (deriv (fun r : ℝ => cutProfile ε (r ^ 2))) ‖x‖
      = deriv (deriv (fun r : ℝ => rhoProfile ε r / (4 * Real.pi * r))) ‖x‖ :=
    hev.deriv.deriv_eq
  rw [hfun, laplaceTrace_normSq (cutProfile ε) (contDiff_cutProfile ε hε) x,
    ← deriv_deriv_comp_sq (cutProfile ε) (contDiff_cutProfile ε hε) hρ, hd2, hd1,
    oneDim_radial_laplace (rhoProfile ε) (contDiff_rhoProfile ε) hρ]
  rw [massKernel_eq, newtonKernel, div_eq_mul_inv, mul_comm]

end Work.FTS.PressureOn.PoissonAux
