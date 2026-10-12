import Mathlib.Analysis.Calculus.ContDiff.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Topology

namespace Work.BoseFixB1

/-- For `0 < r`, every point of the closed exterior `{y | r ≤ ‖y‖}` of the ball of radius `r`
about the origin is a limit point of the open exterior `{y | r < ‖y‖}`: move the point away
from the origin along its own ray by a small amount. -/
private lemma le_norm_subset_closure_lt_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℝ} (hr : 0 < r) :
    {y : E | r ≤ ‖y‖} ⊆ closure {y : E | r < ‖y‖} := by
  intro y hy
  have hy' : r ≤ ‖y‖ := hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases lt_or_eq_of_le hy' with hlt | heq
  · exact ⟨y, hlt, by simpa using hε⟩
  · -- `‖y‖ = r`: the point `y + (δ/2) • y` lies in the open exterior and is `ε`-close to `y`.
    have hyn : 0 < ‖y‖ := by rw [← heq]; exact hr
    have hcont : ContinuousAt (fun t : ℝ => y + t • y) 0 := by
      have h1 : Continuous fun t : ℝ => t • y :=
        continuous_id.smul (continuous_const : Continuous fun _ : ℝ => y)
      exact (continuous_const.add h1).continuousAt
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousAt_iff.mp hcont) ε hε
    refine ⟨y + (δ / 2) • y, ?_, ?_⟩
    · rw [Set.mem_ofPred_eq]
      have hnorm : ‖y + (δ / 2) • y‖ = (1 + δ / 2) * ‖y‖ := by
        rw [show y + (δ / 2) • y = (1 + δ / 2) • y by rw [add_smul, one_smul],
          norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 1 + δ / 2)]
      rw [hnorm]
      have hpos : 0 < δ / 2 * ‖y‖ := mul_pos (by linarith) hyn
      nlinarith [heq, hpos]
    · have hd : dist (δ / 2) (0 : ℝ) < δ := by
        rw [dist_eq_norm, sub_zero, Real.norm_eq_abs,
          abs_of_pos (by linarith : (0 : ℝ) < δ / 2)]
        linarith
      rw [dist_comm]
      simpa using hδ hd

/-- If `f : E → F` is `C¹` and vanishes on the closed exterior of the ball of radius `2`,
then its Fréchet derivative vanishes on that closed exterior as well.

Proof sketch: for `2 < ‖x‖` the function `f` is locally `0` at `x`, so
`Filter.EventuallyEq.fderiv_eq` gives `fderiv ℝ f x = 0`; at `‖x‖ = 2` use that
`fderiv ℝ f` is continuous (`ContDiff.continuous_fderiv`) and `{y | 2 < ‖y‖}` is a
neighbourhood-dense subset of `{y | 2 ≤ ‖y‖}`. -/
theorem fderiv_eq_zero_exterior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (hzero : ∀ x, 2 ≤ ‖x‖ → f x = 0) :
    ∀ x, 2 ≤ ‖x‖ → fderiv ℝ f x = 0 := by
  -- `fderiv ℝ f` is continuous since `f` is `C¹`.
  have hg : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  -- On the open exterior `2 < ‖y‖` the function `f` is locally `0`, hence so is `fderiv`.
  have hinner : ∀ y : E, 2 < ‖y‖ → fderiv ℝ f y = 0 := by
    intro y hy
    have hmem : {z : E | 2 < ‖z‖} ∈ 𝓝 y :=
      (isOpen_lt (continuous_const : Continuous fun _ : E => (2 : ℝ))
        continuous_norm).mem_nhds hy
    have hev : f =ᶠ[𝓝 y] (fun _ : E => (0 : F)) :=
      Filter.mem_of_superset hmem (fun z hz => hzero z (le_of_lt hz))
    calc fderiv ℝ f y = fderiv ℝ (fun _ : E => (0 : F)) y := hev.fderiv_eq (𝕜 := ℝ)
      _ = 0 := fderiv_const_apply 0
  -- Extend the vanishing to the closed exterior by continuity of `fderiv ℝ f`.
  intro x hx
  have hxcl : x ∈ closure {y : E | 2 < ‖y‖} :=
    le_norm_subset_closure_lt_norm (E := E) (r := 2) (by norm_num) hx
  exact Set.EqOn.closure (f := fderiv ℝ f) (g := fun _ : E => (0 : E →L[ℝ] F))
    (s := {y : E | 2 < ‖y‖}) (fun y hy => hinner y hy) hg continuous_const hxcl

end Work.BoseFixB1
