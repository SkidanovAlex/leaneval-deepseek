import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.CutSeq
import Submission.Work.FTS.EllipticEst.PropL2CutKids.Wc_deriv_bdd
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The rescaled bounds for the shifted cutoff family `Vn`

`Vn n z = ψ((n+1)z - 2)·χ(z/(n+1))` where `ψ = Real.smoothTransition` is the smooth step and
`χ = Work.Stability.chi` the bump (`0` off `(-2,2)`, `1` on `[-1,1]`).

The lemma proved here is that the rescaled first and second derivatives of `Vn n` are bounded
*uniformly in `n`*:

* `|z ∂_z Vn n z| ≤ 2M`,
* `|z² ∂_z² Vn n z| ≤ 4M²`,

for a single constant `M ≥ 1`.  Although the sup-norm of `∂_z²Vn n` grows like `n²`, the
two-scale structure (`∂_z` hits the `ψ`-part through the variable `u = (n+1)z - 2` and the
`χ`-part through `v = z/(n+1)`) means that only the *products* `u·ψ'(u)`, `u²·ψ''(u)` and
`v·χ'(v)`, `v²·χ''(v)` occur, and each of those is bounded uniformly (the derivatives of `ψ`
are supported in `[0,1]`, those of `χ` in `[-2,2]`).

The proof is the exact analogue of the sibling estimate `PropL2CutKids.Wc_deriv_bdd` for the
*unshifted* family `Wc n z = ψ((n+1)z)·χ(z/(n+1))`; the only difference is the shift `-2` in
the argument of `ψ`, which is why the auxiliary bounds are taken for the shifted functions
`t ↦ t·ψ'(t-2)` and `t ↦ t²·ψ''(t-2)`.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

set_option autoImplicit false

/-! ### The auxiliary bounds for the shifted step `ψ(· - 2)` -/

/-- The two weighted derivatives of the *shifted* step `t ↦ ψ(t - 2)` are bounded. -/
lemma shiftedPsi_aux_bounds :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ t : ℝ, |t * deriv Real.smoothTransition (t - 2)| ≤ M) ∧
      (∀ t : ℝ, |t ^ 2 * deriv (deriv Real.smoothTransition) (t - 2)| ≤ M) := by
  have hψ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hone : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hdψ : Continuous (deriv Real.smoothTransition) := hψ.continuous_deriv hone
  have hd2ψ : Continuous (deriv (deriv Real.smoothTransition)) := (hψ.deriv').continuous_deriv hone
  have hshift : Continuous (fun t : ℝ => t - 2) := continuous_id.sub continuous_const
  obtain ⟨M1, hM1nn, hM1⟩ := PropL2CutKids.exists_bound_of_continuous_zero_off
    (fun t : ℝ => t * deriv Real.smoothTransition (t - 2))
    (continuous_id.mul (hdψ.comp hshift)) (a := 2) (b := 3) (fun x hx => by
      rcases hx with h | h
      · rw [PropL2CutKids.deriv_smoothTransition_eq_zero_of_lt (by linarith : x - 2 < 0), mul_zero]
      · rw [PropL2CutKids.deriv_smoothTransition_eq_zero_of_gt (by linarith : 1 < x - 2), mul_zero])
  obtain ⟨M2, hM2nn, hM2⟩ := PropL2CutKids.exists_bound_of_continuous_zero_off
    (fun t : ℝ => t ^ 2 * deriv (deriv Real.smoothTransition) (t - 2))
    ((continuous_id.pow 2).mul (hd2ψ.comp hshift)) (a := 2) (b := 3) (fun x hx => by
      rcases hx with h | h
      · rw [PropL2CutKids.deriv2_smoothTransition_eq_zero_of_lt (by linarith : x - 2 < 0),
          mul_zero]
      · rw [PropL2CutKids.deriv2_smoothTransition_eq_zero_of_gt (by linarith : 1 < x - 2),
          mul_zero])
  exact ⟨max M1 M2, le_trans hM1nn (le_max_left _ _), fun t => le_trans (hM1 t) (le_max_left _ _),
    fun t => le_trans (hM2 t) (le_max_right _ _)⟩

/-- The four weighted derivative bounds (two for the shifted step `ψ(·-2)`, two for the bump
`χ`) hold simultaneously, with a single constant `M ≥ 1`. -/
lemma Vn_aux_bounds :
    ∃ M : ℝ, 1 ≤ M ∧
      (∀ t : ℝ, |t * deriv Real.smoothTransition (t - 2)| ≤ M) ∧
      (∀ t : ℝ, |t ^ 2 * deriv (deriv Real.smoothTransition) (t - 2)| ≤ M) ∧
      (∀ t : ℝ, |t * deriv Work.Stability.chi t| ≤ M) ∧
      (∀ t : ℝ, |t ^ 2 * deriv (deriv Work.Stability.chi) t| ≤ M) := by
  obtain ⟨Ms, _, hs1, hs2⟩ := shiftedPsi_aux_bounds
  obtain ⟨Mc, _, _, _, hc1, hc2⟩ := PropL2CutKids.Wc_aux_bounds
  refine ⟨max 1 (max Ms Mc), le_max_left _ _,
    fun t => le_trans (hs1 t) (le_trans (le_max_left _ _) (le_max_right _ _)),
    fun t => le_trans (hs2 t) (le_trans (le_max_left _ _) (le_max_right _ _)),
    fun t => le_trans (hc1 t) (le_trans (le_max_right _ _) (le_max_right _ _)),
    fun t => le_trans (hc2 t) (le_trans (le_max_right _ _) (le_max_right _ _))⟩

/-! ### Derivatives of an affinely rescaled function -/

lemma hasDerivAt_affine_sub (F : ℝ → ℝ) (c d x : ℝ) (hF : DifferentiableAt ℝ F (c * x - d)) :
    HasDerivAt (fun y : ℝ => F (c * y - d)) (deriv F (c * x - d) * c) x := by
  have h1 : HasDerivAt (fun y : ℝ => c * y - d) c x :=
    (hasDerivAt_const_mul c).sub_const d
  simpa [Function.comp_def] using hF.hasDerivAt.comp x h1

/-! ### The two derivative formulas for `Vn` -/

lemma deriv_Vn (n : ℕ) (z : ℝ) :
    deriv (Vn n) z
      = ((n : ℝ) + 1) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * (deriv Work.Stability.chi (z / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹) := by
  have hψ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hχ : ContDiff ℝ ∞ Work.Stability.chi := Work.Stability.chi_contDiff
  have hA := hasDerivAt_affine_sub Real.smoothTransition ((n : ℝ) + 1) 2 z
    ((hψ.differentiable (by simp)).differentiableAt)
  have hB := PropL2CutKids.hasDerivAt_div_const_comp Work.Stability.chi ((n : ℝ) + 1) z
    ((hχ.differentiable (by simp)).differentiableAt)
  have h := hA.mul hB
  have hder : deriv (fun y : ℝ => Real.smoothTransition (((n : ℝ) + 1) * y - 2)
      * Work.Stability.chi (y / ((n : ℝ) + 1))) z
      = deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2) * ((n : ℝ) + 1)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * (deriv Work.Stability.chi (z / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹) := h.deriv
  rw [show Vn n = fun y : ℝ => Real.smoothTransition (((n : ℝ) + 1) * y - 2)
      * Work.Stability.chi (y / ((n : ℝ) + 1)) from rfl, hder]
  ring

lemma deriv_deriv_Vn (n : ℕ) (z : ℝ) :
    deriv (deriv (Vn n)) z
      = ((n : ℝ) + 1) ^ 2 * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z - 2)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + 2 * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * deriv Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * (deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)) * (((n : ℝ) + 1) ^ 2)⁻¹) := by
  have hψ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hχ : ContDiff ℝ ∞ Work.Stability.chi := Work.Stability.chi_contDiff
  have hdψC : ContDiff ℝ ∞ (deriv Real.smoothTransition) := hψ.deriv'
  have hdχC : ContDiff ℝ ∞ (deriv Work.Stability.chi) := hχ.deriv'
  have hdψ : DifferentiableAt ℝ (deriv Real.smoothTransition) (((n : ℝ) + 1) * z - 2) :=
    (hdψC.differentiable (by simp)).differentiableAt
  have hψd : DifferentiableAt ℝ Real.smoothTransition (((n : ℝ) + 1) * z - 2) :=
    (hψ.differentiable (by simp)).differentiableAt
  have hdχ : DifferentiableAt ℝ Work.Stability.chi (z / ((n : ℝ) + 1)) :=
    (hχ.differentiable (by simp)).differentiableAt
  have hd2χ : DifferentiableAt ℝ (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)) :=
    (hdχC.differentiable (by simp)).differentiableAt
  have h1 := hasDerivAt_affine_sub (deriv Real.smoothTransition) ((n : ℝ) + 1) 2 z hdψ
  have h2 := PropL2CutKids.hasDerivAt_div_const_comp Work.Stability.chi ((n : ℝ) + 1) z hdχ
  have h3 := hasDerivAt_affine_sub Real.smoothTransition ((n : ℝ) + 1) 2 z hψd
  have h4 := PropL2CutKids.hasDerivAt_div_const_comp (deriv Work.Stability.chi) ((n : ℝ) + 1) z
    hd2χ
  have hsum := ((h1.mul h2).const_mul ((n : ℝ) + 1)).add
    (h3.mul (h4.mul_const ((n : ℝ) + 1)⁻¹))
  have hg : ∀ y : ℝ, deriv (Vn n) y
      = ((n : ℝ) + 1) * (deriv Real.smoothTransition (((n : ℝ) + 1) * y - 2)
            * Work.Stability.chi (y / ((n : ℝ) + 1)))
        + Real.smoothTransition (((n : ℝ) + 1) * y - 2)
          * (deriv Work.Stability.chi (y / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹) := by
    intro y
    rw [deriv_Vn n y]
    ring
  have hgd : deriv (deriv (Vn n)) z
      = deriv (fun y : ℝ => ((n : ℝ) + 1)
            * (deriv Real.smoothTransition (((n : ℝ) + 1) * y - 2)
              * Work.Stability.chi (y / ((n : ℝ) + 1)))
          + Real.smoothTransition (((n : ℝ) + 1) * y - 2)
            * (deriv Work.Stability.chi (y / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹)) z :=
    Filter.EventuallyEq.deriv_eq (Eventually.of_forall hg)
  -- `hsum` differentiates the same function, only written with the pointwise (`Pi`) operations;
  -- `congr_of_eventuallyEq` transfers it to the explicit `λ`-form used in `hgd`.
  have hgoal : HasDerivAt (fun y : ℝ => ((n : ℝ) + 1)
            * (deriv Real.smoothTransition (((n : ℝ) + 1) * y - 2)
              * Work.Stability.chi (y / ((n : ℝ) + 1)))
          + Real.smoothTransition (((n : ℝ) + 1) * y - 2)
            * (deriv Work.Stability.chi (y / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹))
      (((n : ℝ) + 1) * (deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z - 2)
            * ((n : ℝ) + 1)
            * Work.Stability.chi (z / ((n : ℝ) + 1))
          + deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)
            * (deriv Work.Stability.chi (z / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹))
        + (deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2) * ((n : ℝ) + 1)
            * (deriv Work.Stability.chi (z / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹)
          + Real.smoothTransition (((n : ℝ) + 1) * z - 2)
            * (deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹
              * ((n : ℝ) + 1)⁻¹))) z :=
    hsum.congr_of_eventuallyEq (Eventually.of_forall (fun y => by
      simp only [Pi.mul_apply, Pi.add_apply]))
  have hp : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [hgd, hgoal.deriv]
  field_simp
  ring

/-! ### The two scaled bounds for `Vn` -/

lemma Vn_z_mul_deriv_bound (n : ℕ) (z M : ℝ)
    (h1 : ∀ t : ℝ, |t * deriv Real.smoothTransition (t - 2)| ≤ M)
    (h2 : ∀ t : ℝ, |t * deriv Work.Stability.chi t| ≤ M) :
    |z * deriv (Vn n) z| ≤ 2 * M := by
  have hp : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (h2 0)
  rw [deriv_Vn n z]
  rw [show z * (((n : ℝ) + 1) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * (deriv Work.Stability.chi (z / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹))
      = (((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))) from by
    field_simp]
  have c1 : |Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ 1 := by
    rw [abs_of_nonneg (Work.Stability.chi_nonneg _)]
    exact Work.Stability.chi_le_one _
  have c2 : |Real.smoothTransition (((n : ℝ) + 1) * z - 2)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have b1 : |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)| ≤ M :=
    h1 _
  have b2 : |(z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ M := h2 _
  have t1 : |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)|
      * |Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ M := by
    calc _ ≤ M * 1 := mul_le_mul b1 c1 (abs_nonneg _) (by linarith)
      _ = M := by ring
  have t2 : |Real.smoothTransition (((n : ℝ) + 1) * z - 2)|
      * |(z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ M := by
    calc _ ≤ 1 * M := mul_le_mul c2 b2 (abs_nonneg _) (by linarith)
      _ = M := by ring
  calc |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))|
      ≤ |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)
            * Work.Stability.chi (z / ((n : ℝ) + 1))|
        + |Real.smoothTransition (((n : ℝ) + 1) * z - 2)
            * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))| :=
        abs_add_le _ _
    _ = |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)|
          * |Work.Stability.chi (z / ((n : ℝ) + 1))|
        + |Real.smoothTransition (((n : ℝ) + 1) * z - 2)|
          * |(z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))| := by
        simp only [abs_mul]
    _ ≤ M + M := add_le_add t1 t2
    _ = 2 * M := by ring

lemma Vn_zsq_mul_deriv2_bound (n : ℕ) (z M : ℝ)
    (h1 : ∀ t : ℝ, |t * deriv Real.smoothTransition (t - 2)| ≤ M)
    (h2 : ∀ t : ℝ, |t ^ 2 * deriv (deriv Real.smoothTransition) (t - 2)| ≤ M)
    (h3 : ∀ t : ℝ, |t * deriv Work.Stability.chi t| ≤ M)
    (h4 : ∀ t : ℝ, |t ^ 2 * deriv (deriv Work.Stability.chi) t| ≤ M)
    (hM1 : 1 ≤ M) :
    |z ^ 2 * deriv (deriv (Vn n)) z| ≤ 4 * M ^ 2 := by
  have hp : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (h3 0)
  rw [deriv_deriv_Vn n z]
  rw [show z ^ 2 * (((n : ℝ) + 1) ^ 2
          * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z - 2)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + 2 * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * deriv Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * (deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1))
            * (((n : ℝ) + 1) ^ 2)⁻¹))
      = ((((n : ℝ) + 1) * z) ^ 2 * deriv (deriv Real.smoothTransition)
            (((n : ℝ) + 1) * z - 2))
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + 2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2))
          * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))
        + Real.smoothTransition (((n : ℝ) + 1) * z - 2)
          * ((z / ((n : ℝ) + 1)) ^ 2
            * deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1))) from by
    field_simp]
  have c1 : |Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ 1 := by
    rw [abs_of_nonneg (Work.Stability.chi_nonneg _)]
    exact Work.Stability.chi_le_one _
  have c2 : |Real.smoothTransition (((n : ℝ) + 1) * z - 2)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hb : |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)| ≤ M :=
    h1 _
  have hc : |(z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ M := h3 _
  have hA : |((((n : ℝ) + 1) * z) ^ 2
        * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z - 2))
      * Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ M := by
    rw [abs_mul]
    calc _ ≤ M * 1 := mul_le_mul (h2 _) c1 (abs_nonneg _) hM
      _ = M := by ring
  have hB : |2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2))
      * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))| ≤ 2 * (M * M) := by
    have hX : |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)
        * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))| ≤ M * M := by
      rw [abs_mul]
      exact mul_le_mul hb hc (abs_nonneg _) hM
    calc |2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2))
          * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))|
        = 2 * |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)
            * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))| := by
          rw [show 2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2))
                * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))
              = 2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2)
                * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))) from by
            ring]
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      _ ≤ 2 * (M * M) := by linarith
  have hC : |Real.smoothTransition (((n : ℝ) + 1) * z - 2)
      * ((z / ((n : ℝ) + 1)) ^ 2 * deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)))| ≤ M := by
    rw [abs_mul]
    calc _ ≤ 1 * M := mul_le_mul c2 (h4 _) (abs_nonneg _) (by linarith)
      _ = M := by ring
  have key : |((((n : ℝ) + 1) * z) ^ 2 * deriv (deriv Real.smoothTransition)
          (((n : ℝ) + 1) * z - 2))
        * Work.Stability.chi (z / ((n : ℝ) + 1))
      + 2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2))
        * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))
      + Real.smoothTransition (((n : ℝ) + 1) * z - 2)
        * ((z / ((n : ℝ) + 1)) ^ 2 * deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)))|
      ≤ M + 2 * (M * M) + M := by
    have h12 := abs_add_le
      (((((n : ℝ) + 1) * z) ^ 2 * deriv (deriv Real.smoothTransition)
            (((n : ℝ) + 1) * z - 2)) * Work.Stability.chi (z / ((n : ℝ) + 1)))
      (2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2))
        * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))))
    have h123 := abs_add_le
      (((((n : ℝ) + 1) * z) ^ 2 * deriv (deriv Real.smoothTransition)
            (((n : ℝ) + 1) * z - 2)) * Work.Stability.chi (z / ((n : ℝ) + 1))
        + 2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z - 2))
          * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))))
      (Real.smoothTransition (((n : ℝ) + 1) * z - 2)
        * ((z / ((n : ℝ) + 1)) ^ 2 * deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1))))
    linarith
  calc _ ≤ M + 2 * (M * M) + M := key
    _ = 2 * M + 2 * M ^ 2 := by ring
    _ ≤ 4 * M ^ 2 := by nlinarith [hM1, hM]

/-! ### The result -/

theorem VnRescaledBounds : ∃ M : ℝ, 1 ≤ M ∧
    (∀ n : ℕ, ∀ z : ℝ, |z * deriv (Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n) z| ≤ 2 * M) ∧
    (∀ n : ℕ, ∀ z : ℝ, |z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n)) z| ≤ 4 * M ^ 2) := by
  obtain ⟨M, hM1, h1, h2, h3, h4⟩ := Vn_aux_bounds
  refine ⟨M, hM1, fun n z => ?_, fun n z => ?_⟩
  · exact le_trans (Vn_z_mul_deriv_bound n z M h1 h3) (by linarith)
  · exact Vn_zsq_mul_deriv2_bound n z M h1 h2 h3 h4 hM1

end Work.FTS.EllipticEst.H2W.AeProof.ae
