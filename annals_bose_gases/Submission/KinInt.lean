import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Submission.BoxEnergy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Whole-space integrability of the single-particle kinetic terms

For `f : X N → ℝ` twice continuously differentiable with compact support, each
kinetic integrand `x ↦ f x * (-(partialLaplacian i f) x)` is genuinely
integrable over `X N`.

Ingredients (all available upstream):
  * `partialLaplacian_eq_sum_secondDir` expresses `Δ[i] f` as a finite sum of
    second directional derivatives;
  * `ContDiff ℝ 2 f` makes the second directional derivatives continuous
    (via `ContDiff.fderiv_right`, evaluation on the direction, composition),
    so `partialLaplacian i f` is continuous;
  * products of continuous functions with compact support are integrable
    (`Continuous.integrable_of_hasCompactSupport`).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- One summand of the bridge identity is continuous for a `C²` `f`:
`x ↦ (fderiv (z ↦ fderiv f z u) x) u` with `u = coordDir N i k`.

Indeed `z ↦ fderiv f z u` is `C¹` (it is the derivative of `f` in the constant
direction `u`, and `f` is `C²`), so its Fréchet derivative is continuous; and
evaluation at `u` is a continuous linear map. -/
lemma secondDir_contDiff_c2 {N : ℕ} {f : X N → ℝ} (hf : ContDiff ℝ 2 f) (u : X N) :
    Continuous (fun x : X N =>
      (fderiv ℝ (fun z : X N => fderiv ℝ f z u) x) u) := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) :=
    ContDiff.fderiv_right (m := 1) hf (by norm_num)
  have heval : ContDiff ℝ 1 (fun (L : X N →L[ℝ] ℝ) => L u) := by
    exact ((ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) u : (X N →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff)
      |>.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have h0 : ContDiff ℝ 1 (fun z : X N => fderiv ℝ f z u) := by
    simpa [Function.comp_def] using heval.comp hf1
  have hd : ContDiff ℝ 0 (fderiv ℝ (fun z : X N => fderiv ℝ f z u)) :=
    ContDiff.fderiv_right (m := 0) h0 (by norm_num)
  have hdcont : Continuous (fun x : X N => fderiv ℝ (fun z : X N => fderiv ℝ f z u) x) :=
    hd.continuous
  have hevalcont : Continuous (fun (L : X N →L[ℝ] ℝ) => L u) :=
    (ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) u : (X N →L[ℝ] ℝ) →L[ℝ] ℝ).continuous
  simpa [Function.comp_def] using hevalcont.comp hdcont

/-- The partial Laplacian of a `C²` function is continuous. -/
lemma continuous_partialLaplacian_c2 {N : ℕ} {f : X N → ℝ} (hf : ContDiff ℝ 2 f)
    (i : Fin N) :
    Continuous (fun x : X N => partialLaplacian i f x) := by
  have hbridge := partialLaplacian_eq_sum_secondDir N i (f := f) hf
  rw [hbridge]
  refine continuous_finsetSum (s := Finset.univ) (f := fun k x =>
    (fderiv ℝ (fun z : X N => fderiv ℝ f z (coordDir N i k)) x) (coordDir N i k)) ?_
  intro k hk
  exact secondDir_contDiff_c2 hf (coordDir N i k)

/-- The per-particle kinetic integrand `x ↦ f x · (−Δ[i]f x)` of a `C²`
compactly supported `f` is integrable over the whole space. -/
lemma kinInt_term {N : ℕ} {f : X N → ℝ} (hf : ContDiff ℝ 2 f) (hcs : HasCompactSupport f)
    (i : Fin N) :
    Integrable (fun x : X N => f x * (-(partialLaplacian i f) x)) volume := by
  have hcont : Continuous (fun x : X N => f x * (-(partialLaplacian i f) x)) := by
    exact hf.continuous.mul (continuous_partialLaplacian_c2 hf i).neg
  have hcs' : HasCompactSupport (fun x : X N => f x * (-(partialLaplacian i f) x)) := by
    exact hcs.mul_right
  exact Continuous.integrable_of_hasCompactSupport hcont hcs'

end BoseGases

end Submission
