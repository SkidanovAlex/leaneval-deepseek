import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs
import Submission.Work.Rigidity.periodic_lambdaFun_ofComplex

namespace Work.Rigidity

open UpperHalfPlane Filter Topology

/--
The `q`-expansion of `λ` divided by `q` tends to `16` as `q → 0` (through `q ≠ 0`).

Indeed `Flam` is by definition the `q`-expansion of `λ = Work.Kernels.lambdaFun`, i.e.
`Flam q = λ (𝕢₂)⁻¹(q)`, and `𝕢₂ ((𝕢₂)⁻¹ q) = q`, so along `q ≠ 0` the quotient
`Flam q / q` is the value of `λ(τ)/𝕢₂ τ` at `τ = (𝕢₂)⁻¹ q`.  Since `𝕢₂` is invertible
with inverse asymptotically sending `q → 0, q ≠ 0` to `i∞`, the limit is that of
`λ(τ)/𝕢₂ τ`, namely `16`.
-/
theorem Flam_div_tendsto
    (hper : Function.Periodic
      (fun z : ℂ => Work.Kernels.lambdaFun (UpperHalfPlane.ofComplex z)) 2)
    (hlim : Filter.Tendsto (fun τ : UpperHalfPlane => Work.Kernels.lambdaFun τ /
      Function.Periodic.qParam 2 (τ : ℂ)) UpperHalfPlane.atImInfty (nhds 16)) :
    Filter.Tendsto (fun q : ℂ => Work.Rigidity.Flam q / q)
      (nhdsWithin 0 {q : ℂ | q ≠ 0}) (nhds 16) := by
  -- `(𝕢₂)⁻¹` sends `q → 0` (with `q ≠ 0`) to `i∞` in the upper half plane.
  have hinv : Tendsto (Function.Periodic.invQParam 2) (𝓝[≠] 0) (comap Complex.im atTop) :=
    Function.Periodic.invQParam_tendsto (by norm_num : (0 : ℝ) < 2)
  have hcomp : Tendsto (fun q : ℂ => UpperHalfPlane.ofComplex (Function.Periodic.invQParam 2 q))
      (𝓝[≠] 0) UpperHalfPlane.atImInfty :=
    UpperHalfPlane.tendsto_comap_im_ofComplex.comp hinv
  have hmain := hlim.comp hcomp
  refine Filter.Tendsto.congr' ?_ hmain
  -- Eventually `q ≠ 0` and `‖q‖ < 1`, so `(𝕢₂)⁻¹ q` is in `ℍ`.
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hball
  rw [Metric.mem_ball, dist_zero_right] at hball
  have him : 0 < (Function.Periodic.invQParam 2 q).im :=
    Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hball hq
  have hFlam : Flam q = Work.Kernels.lambdaFun
      (UpperHalfPlane.ofComplex (Function.Periodic.invQParam 2 q)) := by
    unfold Flam UpperHalfPlane.cuspFunction
    exact Function.Periodic.cuspFunction_eq_of_nonzero 2 _ hq
  have hden : Function.Periodic.qParam 2
      ((UpperHalfPlane.ofComplex (Function.Periodic.invQParam 2 q) : ℍ) : ℂ) = q := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    exact Function.Periodic.qParam_right_inv (by norm_num) hq
  simp only [Function.comp_apply]
  rw [hFlam, hden]

end Work.Rigidity
