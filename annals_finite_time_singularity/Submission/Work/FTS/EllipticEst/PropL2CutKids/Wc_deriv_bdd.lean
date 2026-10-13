import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.PropL2Cut

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.PropL2CutKids

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-! ## Boundedness of the derivatives of the cutoff `Wc`

`Wc n z = ψ((n+1)z)·χ(z/(n+1))` where `ψ = Real.smoothTransition` and `χ = Work.Stability.chi`.
We prove that the derivatives of `z * (Wc n z)^2` and of `z^2 * (Wc n z)^2` are bounded
*uniformly in `n` and `z`*.

The reason this is true (although the sup-norm of the second derivative of `Wc n` grows like
`n^2`) is the two-scale structure: the `ψ`-part is differentiated with respect to the variable
`u = (n+1)z` and the `χ`-part with respect to `v = z/(n+1)`, and the combinations
`u·ψ'(u)`, `u^2·ψ''(u)`, `v·χ'(v)`, `v^2·χ''(v)` are all uniformly bounded (each derivative of
`ψ` is supported in `[0,1]` and each derivative of `χ` in `[-2,2]`).

The auxiliary finite bound is provided by `Wc_aux_bounds`; the two derivative formulas by
`deriv_Wc`/`deriv_deriv_Wc`; the uniform bounds on `z·(Wc n)'` and `z^2·(Wc n)''` by
`Wc_z_mul_deriv_bound`/`Wc_zsq_mul_deriv2_bound`; and the final passage to the derivatives of
`z·(Wc n)^2` and `z^2·(Wc n)^2` by `mul_sq_deriv_bound`/`sq_mul_sq_deriv_bound`. -/

/-! ### A generic sup-bound for a continuous function vanishing off a compact interval -/

lemma exists_bound_of_continuous_zero_off (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ}
    (hsupp : ∀ x, x < a ∨ b < x → f x = 0) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b) hf.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun x => by
    rcases lt_or_ge x a with h | h
    · rw [hsupp x (Or.inl h), abs_zero]; exact le_max_right _ _
    · rcases lt_or_ge b x with h1 | h1
      · rw [hsupp x (Or.inr h1), abs_zero]; exact le_max_right _ _
      · have hx : x ∈ Set.Icc a b := ⟨h, h1⟩
        have h2 := hM x hx
        rw [Real.norm_eq_abs] at h2
        exact le_trans h2 (le_max_left _ _)⟩

/-! ### The supports of the derivatives of `ψ` and `χ` -/

lemma deriv_smoothTransition_eq_zero_of_lt {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, y < 0 := IsOpen.mem_nhds isOpen_Iio hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => Real.smoothTransition.zero_of_nonpos hy.le
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

lemma deriv_smoothTransition_eq_zero_of_gt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, 1 < y := IsOpen.mem_nhds isOpen_Ioi hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) :=
    hmem.mono fun y hy => Real.smoothTransition.one_of_one_le hy.le
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

lemma deriv2_smoothTransition_eq_zero_of_lt {x : ℝ} (hx : x < 0) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, y < 0 := IsOpen.mem_nhds isOpen_Iio hx
  have heq : (deriv Real.smoothTransition) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => deriv_smoothTransition_eq_zero_of_lt hy
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

lemma deriv2_smoothTransition_eq_zero_of_gt {x : ℝ} (hx : 1 < x) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, 1 < y := IsOpen.mem_nhds isOpen_Ioi hx
  have heq : (deriv Real.smoothTransition) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => deriv_smoothTransition_eq_zero_of_gt hy
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

lemma deriv_chi_eq_zero {x : ℝ} (hx : 2 < |x|) : deriv Work.Stability.chi x = 0 := by
  have hopen : IsOpen {y : ℝ | 2 < |y|} := isOpen_lt continuous_const continuous_abs
  have hmem : ∀ᶠ y in 𝓝 x, 2 < |y| := hopen.mem_nhds hx
  have heq : Work.Stability.chi =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => Work.Stability.chi_eq_zero hy.le
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

lemma deriv2_chi_eq_zero {x : ℝ} (hx : 2 < |x|) :
    deriv (deriv Work.Stability.chi) x = 0 := by
  have hopen : IsOpen {y : ℝ | 2 < |y|} := isOpen_lt continuous_const continuous_abs
  have hmem : ∀ᶠ y in 𝓝 x, 2 < |y| := hopen.mem_nhds hx
  have heq : (deriv Work.Stability.chi) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => deriv_chi_eq_zero hy
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

lemma two_lt_abs_of {x : ℝ} (h : x < -2 ∨ 2 < x) : 2 < |x| := by
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-! ### The common finite bound -/

/-- All the weighted derivatives of `ψ` and `χ` that occur are bounded by a single constant. -/
lemma Wc_aux_bounds :
    ∃ M : ℝ, 1 ≤ M ∧
      (∀ t : ℝ, |t * deriv Real.smoothTransition t| ≤ M) ∧
      (∀ t : ℝ, |t ^ 2 * deriv (deriv Real.smoothTransition) t| ≤ M) ∧
      (∀ t : ℝ, |t * deriv Work.Stability.chi t| ≤ M) ∧
      (∀ t : ℝ, |t ^ 2 * deriv (deriv Work.Stability.chi) t| ≤ M) := by
  have hψ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hχ : ContDiff ℝ ∞ Work.Stability.chi := Work.Stability.chi_contDiff
  have hone : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hdψ : Continuous (deriv Real.smoothTransition) := hψ.continuous_deriv hone
  have hd2ψ : Continuous (deriv (deriv Real.smoothTransition)) :=
    (hψ.deriv').continuous_deriv hone
  have hdχ : Continuous (deriv Work.Stability.chi) := hχ.continuous_deriv hone
  have hd2χ : Continuous (deriv (deriv Work.Stability.chi)) :=
    (hχ.deriv').continuous_deriv hone
  obtain ⟨M1, _, hM1⟩ := exists_bound_of_continuous_zero_off
    (fun t : ℝ => t * deriv Real.smoothTransition t) (continuous_id.mul hdψ)
    (a := 0) (b := 1) (fun x hx => by
      rcases hx with h | h
      · rw [deriv_smoothTransition_eq_zero_of_lt h, mul_zero]
      · rw [deriv_smoothTransition_eq_zero_of_gt h, mul_zero])
  obtain ⟨M2, _, hM2⟩ := exists_bound_of_continuous_zero_off
    (fun t : ℝ => t ^ 2 * deriv (deriv Real.smoothTransition) t)
    ((continuous_id.pow 2).mul hd2ψ) (a := 0) (b := 1) (fun x hx => by
      rcases hx with h | h
      · rw [deriv2_smoothTransition_eq_zero_of_lt h, mul_zero]
      · rw [deriv2_smoothTransition_eq_zero_of_gt h, mul_zero])
  obtain ⟨M3, _, hM3⟩ := exists_bound_of_continuous_zero_off
    (fun t : ℝ => t * deriv Work.Stability.chi t) (continuous_id.mul hdχ)
    (a := -2) (b := 2) (fun x hx => by
      rw [deriv_chi_eq_zero (two_lt_abs_of hx), mul_zero])
  obtain ⟨M4, _, hM4⟩ := exists_bound_of_continuous_zero_off
    (fun t : ℝ => t ^ 2 * deriv (deriv Work.Stability.chi) t)
    ((continuous_id.pow 2).mul hd2χ) (a := -2) (b := 2) (fun x hx => by
      rw [deriv2_chi_eq_zero (two_lt_abs_of hx), mul_zero])
  refine ⟨max 1 (max (max M1 M2) (max M3 M4)), le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · intro t
    exact le_trans (hM1 t)
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _)))
  · intro t
    exact le_trans (hM2 t)
      (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _)))
  · intro t
    exact le_trans (hM3 t)
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  · intro t
    exact le_trans (hM4 t)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))

/-! ### Derivatives of an affinely rescaled function -/

lemma hasDerivAt_const_mul_comp (F : ℝ → ℝ) (c x : ℝ) (hF : DifferentiableAt ℝ F (c * x)) :
    HasDerivAt (fun y : ℝ => F (c * y)) (deriv F (c * x) * c) x := by
  have h1 : HasDerivAt (fun y : ℝ => c * y) c x := hasDerivAt_const_mul c
  have h := (hF.hasDerivAt).comp x h1
  convert h using 1
  funext y
  rfl

lemma hasDerivAt_div_const_comp (F : ℝ → ℝ) (c x : ℝ) (hF : DifferentiableAt ℝ F (x / c)) :
    HasDerivAt (fun y : ℝ => F (y / c)) (deriv F (x / c) * c⁻¹) x := by
  have h1 : HasDerivAt (fun y : ℝ => y / c) c⁻¹ x := by
    simpa using (hasDerivAt_id x).div_const c
  have h := (hF.hasDerivAt).comp x h1
  convert h using 1
  funext y
  simp only [Function.comp_apply]

/-! ### The two derivative formulas for `Wc` -/

lemma deriv_Wc (n : ℕ) (z : ℝ) :
    deriv (Work.FTS.EllipticEst.PropL2Cut.Wc n) z
      = ((n : ℝ) + 1) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z)
          * (deriv Work.Stability.chi (z / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹) := by
  have hψ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hχ : ContDiff ℝ ∞ Work.Stability.chi := Work.Stability.chi_contDiff
  have hA := hasDerivAt_const_mul_comp Real.smoothTransition ((n : ℝ) + 1) z
    ((hψ.differentiable (by simp)).differentiableAt)
  have hB := hasDerivAt_div_const_comp Work.Stability.chi ((n : ℝ) + 1) z
    ((hχ.differentiable (by simp)).differentiableAt)
  have h := hA.mul hB
  have hder : deriv (Work.FTS.EllipticEst.PropL2Cut.Wc n) z =
      deriv Real.smoothTransition (((n : ℝ) + 1) * z) * ((n : ℝ) + 1)
        * Work.Stability.chi (z / ((n : ℝ) + 1))
      + Real.smoothTransition (((n : ℝ) + 1) * z)
        * (deriv Work.Stability.chi (z / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹) := h.deriv
  rw [hder]
  ring

lemma deriv_deriv_Wc (n : ℕ) (z : ℝ) :
    deriv (deriv (Work.FTS.EllipticEst.PropL2Cut.Wc n)) z
      = ((n : ℝ) + 1) ^ 2 * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + 2 * deriv Real.smoothTransition (((n : ℝ) + 1) * z)
          * deriv Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z)
          * (deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)) * (((n : ℝ) + 1) ^ 2)⁻¹) := by
  have hψ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hχ : ContDiff ℝ ∞ Work.Stability.chi := Work.Stability.chi_contDiff
  have hdψC : ContDiff ℝ ∞ (deriv Real.smoothTransition) := hψ.deriv'
  have hdχC : ContDiff ℝ ∞ (deriv Work.Stability.chi) := hχ.deriv'
  have hdψ : DifferentiableAt ℝ (deriv Real.smoothTransition) (((n : ℝ) + 1) * z) :=
    (hdψC.differentiable (by simp)).differentiableAt
  have hdχ : DifferentiableAt ℝ Work.Stability.chi (z / ((n : ℝ) + 1)) :=
    (hχ.differentiable (by simp)).differentiableAt
  have hψd : DifferentiableAt ℝ Real.smoothTransition (((n : ℝ) + 1) * z) :=
    (hψ.differentiable (by simp)).differentiableAt
  have hd2χ : DifferentiableAt ℝ (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)) :=
    (hdχC.differentiable (by simp)).differentiableAt
  have h1 := hasDerivAt_const_mul_comp (deriv Real.smoothTransition) ((n : ℝ) + 1) z hdψ
  have h2 := hasDerivAt_div_const_comp Work.Stability.chi ((n : ℝ) + 1) z hdχ
  have h3 := hasDerivAt_const_mul_comp Real.smoothTransition ((n : ℝ) + 1) z hψd
  have h4 := hasDerivAt_div_const_comp (deriv Work.Stability.chi) ((n : ℝ) + 1) z hd2χ
  have hsum := ((h1.mul h2).const_mul ((n : ℝ) + 1)).add (h3.mul (h4.mul_const ((n : ℝ) + 1)⁻¹))
  have hgoal : HasDerivAt (fun y => ((n : ℝ) + 1)
        * (deriv Real.smoothTransition (((n : ℝ) + 1) * y)
            * Work.Stability.chi (y / ((n : ℝ) + 1)))
        + Real.smoothTransition (((n : ℝ) + 1) * y)
          * (deriv Work.Stability.chi (y / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹))
      (((n : ℝ) + 1) ^ 2 * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + 2 * deriv Real.smoothTransition (((n : ℝ) + 1) * z)
          * deriv Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z)
          * (deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)) * (((n : ℝ) + 1) ^ 2)⁻¹)) z := by
    convert hsum using 1
    have hp : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hg : ∀ y : ℝ, deriv (Work.FTS.EllipticEst.PropL2Cut.Wc n) y
      = ((n : ℝ) + 1) * (deriv Real.smoothTransition (((n : ℝ) + 1) * y)
            * Work.Stability.chi (y / ((n : ℝ) + 1)))
        + Real.smoothTransition (((n : ℝ) + 1) * y)
          * (deriv Work.Stability.chi (y / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹) := by
    intro y
    rw [deriv_Wc n y]
    ring
  have hgd : deriv (deriv (Work.FTS.EllipticEst.PropL2Cut.Wc n)) z
      = deriv (fun y => ((n : ℝ) + 1)
          * (deriv Real.smoothTransition (((n : ℝ) + 1) * y)
              * Work.Stability.chi (y / ((n : ℝ) + 1)))
          + Real.smoothTransition (((n : ℝ) + 1) * y)
            * (deriv Work.Stability.chi (y / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹)) z :=
    Filter.EventuallyEq.deriv_eq (Eventually.of_forall hg)
  rw [hgd, hgoal.deriv]

/-! ### The two scaled bounds for `Wc` -/

lemma Wc_z_mul_deriv_bound (n : ℕ) (z M : ℝ)
    (h1 : ∀ t : ℝ, |t * deriv Real.smoothTransition t| ≤ M)
    (h2 : ∀ t : ℝ, |t * deriv Work.Stability.chi t| ≤ M) :
    |z * deriv (Work.FTS.EllipticEst.PropL2Cut.Wc n) z| ≤ 2 * M := by
  have hp : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hM : 0 ≤ M := by simpa using h1 0
  rw [deriv_Wc n z]
  rw [show z * (((n : ℝ) + 1) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z)
          * (deriv Work.Stability.chi (z / ((n : ℝ) + 1)) * ((n : ℝ) + 1)⁻¹))
      = (((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z)
          * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))) from by
    field_simp]
  have c1 : |Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ 1 := by
    rw [abs_of_nonneg (Work.Stability.chi_nonneg _)]
    exact Work.Stability.chi_le_one _
  have c2 : |Real.smoothTransition (((n : ℝ) + 1) * z)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have b1 : |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)| ≤ M := h1 _
  have b2 : |(z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ M := h2 _
  have t1 : |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)|
      * |Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ M := by
    calc _ ≤ M * 1 := mul_le_mul b1 c1 (abs_nonneg _) (by linarith)
      _ = M := by ring
  have t2 : |Real.smoothTransition (((n : ℝ) + 1) * z)|
      * |(z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ M := by
    calc _ ≤ 1 * M := mul_le_mul c2 b2 (abs_nonneg _) (by linarith)
      _ = M := by ring
  calc |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z)
          * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))|
      ≤ |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)
            * Work.Stability.chi (z / ((n : ℝ) + 1))|
        + |Real.smoothTransition (((n : ℝ) + 1) * z)
            * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))| :=
        abs_add_le _ _
    _ = |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)|
          * |Work.Stability.chi (z / ((n : ℝ) + 1))|
        + |Real.smoothTransition (((n : ℝ) + 1) * z)|
          * |(z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))| := by
        simp only [abs_mul]
    _ ≤ M + M := add_le_add t1 t2
    _ = 2 * M := by ring

lemma Wc_zsq_mul_deriv2_bound (n : ℕ) (z M : ℝ)
    (h1 : ∀ t : ℝ, |t * deriv Real.smoothTransition t| ≤ M)
    (h2 : ∀ t : ℝ, |t * deriv Work.Stability.chi t| ≤ M)
    (h3 : ∀ t : ℝ, |t ^ 2 * deriv (deriv Real.smoothTransition) t| ≤ M)
    (h4 : ∀ t : ℝ, |t ^ 2 * deriv (deriv Work.Stability.chi) t| ≤ M) :
    |z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.PropL2Cut.Wc n)) z| ≤ 2 * M + 2 * M ^ 2 := by
  have hp : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hM : 0 ≤ M := by simpa using h1 0
  rw [deriv_deriv_Wc n z]
  rw [show z ^ 2 * (((n : ℝ) + 1) ^ 2 * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z)
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + 2 * deriv Real.smoothTransition (((n : ℝ) + 1) * z)
          * deriv Work.Stability.chi (z / ((n : ℝ) + 1))
        + Real.smoothTransition (((n : ℝ) + 1) * z)
          * (deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)) * (((n : ℝ) + 1) ^ 2)⁻¹))
      = ((((n : ℝ) + 1) * z) ^ 2 * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z))
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + 2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z))
          * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))
        + Real.smoothTransition (((n : ℝ) + 1) * z)
          * ((z / ((n : ℝ) + 1)) ^ 2 * deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1))) from by
    field_simp]
  have c1 : |Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ 1 := by
    rw [abs_of_nonneg (Work.Stability.chi_nonneg _)]
    exact Work.Stability.chi_le_one _
  have c2 : |Real.smoothTransition (((n : ℝ) + 1) * z)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hb : |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)| ≤ M := h1 _
  have hc : |(z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ M := h2 _
  have hA : |((((n : ℝ) + 1) * z) ^ 2 * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z))
      * Work.Stability.chi (z / ((n : ℝ) + 1))| ≤ M := by
    rw [abs_mul]
    calc _ ≤ M * 1 := mul_le_mul (h3 _) c1 (abs_nonneg _) hM
      _ = M := by ring
  have hB : |2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z))
      * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))| ≤ 2 * (M * M) := by
    have hX : |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)
        * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))| ≤ M * M := by
      rw [abs_mul]
      exact mul_le_mul hb hc (abs_nonneg _) hM
    calc |2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z))
          * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))|
        = 2 * |(((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)
            * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))| := by
          rw [show 2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z))
                * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))
              = 2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z)
                * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))) from by ring]
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      _ ≤ 2 * (M * M) := by linarith
  have hC : |Real.smoothTransition (((n : ℝ) + 1) * z)
      * ((z / ((n : ℝ) + 1)) ^ 2 * deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)))| ≤ M := by
    rw [abs_mul]
    calc _ ≤ 1 * M := mul_le_mul c2 (h4 _) (abs_nonneg _) (by linarith)
      _ = M := by ring
  calc |((((n : ℝ) + 1) * z) ^ 2 * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z))
          * Work.Stability.chi (z / ((n : ℝ) + 1))
        + 2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z))
          * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))
        + Real.smoothTransition (((n : ℝ) + 1) * z)
          * ((z / ((n : ℝ) + 1)) ^ 2 * deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)))|
      ≤ |((((n : ℝ) + 1) * z) ^ 2 * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z))
            * Work.Stability.chi (z / ((n : ℝ) + 1))
          + 2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z))
            * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))|
        + |Real.smoothTransition (((n : ℝ) + 1) * z)
            * ((z / ((n : ℝ) + 1)) ^ 2 * deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)))| :=
        abs_add_le _ _
    _ ≤ (|((((n : ℝ) + 1) * z) ^ 2 * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z))
            * Work.Stability.chi (z / ((n : ℝ) + 1))|
          + |2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z))
            * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1)))|)
        + |Real.smoothTransition (((n : ℝ) + 1) * z)
            * ((z / ((n : ℝ) + 1)) ^ 2 * deriv (deriv Work.Stability.chi) (z / ((n : ℝ) + 1)))| := by
        have hh := abs_add_le
          ((((n : ℝ) + 1) * z) ^ 2 * deriv (deriv Real.smoothTransition) (((n : ℝ) + 1) * z)
            * Work.Stability.chi (z / ((n : ℝ) + 1)))
          (2 * ((((n : ℝ) + 1) * z) * deriv Real.smoothTransition (((n : ℝ) + 1) * z))
            * ((z / ((n : ℝ) + 1)) * deriv Work.Stability.chi (z / ((n : ℝ) + 1))))
        linarith
    _ ≤ (M + 2 * (M * M)) + M := by linarith
    _ = 2 * M + 2 * M ^ 2 := by ring

/-! ### Derivatives of `y ↦ y (W y)^2` and `y ↦ y^2 (W y)^2` -/

lemma deriv_mul_sq (W : ℝ → ℝ) (hW : Differentiable ℝ W) (z : ℝ) :
    deriv (fun y : ℝ => y * (W y)^2) z = (W z)^2 + 2 * (W z) * (z * deriv W z) := by
  have hWz : HasDerivAt W (deriv W z) z := hW.differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => (W y)^2) (2 * (W z) * deriv W z) z := by
    have h := hWz.pow 2
    have hd : HasDerivAt (fun y : ℝ => (W y)^2) (↑2 * (W z) ^ (2 - 1) * deriv W z) z := h
    convert hd using 1
    ring_nf
  have h := (hasDerivAt_id z).mul h2
  have hder : deriv (fun y : ℝ => y * (W y)^2) z
      = 1 * (W z)^2 + z * (2 * (W z) * deriv W z) := h.deriv
  rw [hder]
  ring

lemma deriv_sq_mul_sq (W : ℝ → ℝ) (hW : Differentiable ℝ W) (y : ℝ) :
    deriv (fun y : ℝ => y^2 * (W y)^2) y = 2 * y * (W y)^2 + 2 * y^2 * (W y) * deriv W y := by
  have hWy : HasDerivAt W (deriv W y) y := hW.differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => y^2) (2 * y) y := by
    have h := (hasDerivAt_id y).pow 2
    have hd : HasDerivAt (fun y : ℝ => y^2) (↑2 * y ^ (2 - 1) * 1) y := h
    convert hd using 1
    ring_nf
  have h2 : HasDerivAt (fun y : ℝ => (W y)^2) (2 * (W y) * deriv W y) y := by
    have h := hWy.pow 2
    have hd : HasDerivAt (fun y : ℝ => (W y)^2) (↑2 * (W y) ^ (2 - 1) * deriv W y) y := h
    convert hd using 1
    ring_nf
  have h := h1.mul h2
  have hder : deriv (fun y : ℝ => y^2 * (W y)^2) y
      = 2 * y * (W y)^2 + y^2 * (2 * (W y) * deriv W y) := h.deriv
  rw [hder]
  ring

lemma deriv_sq_mul_sq_deriv (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (z : ℝ) :
    deriv (deriv (fun y : ℝ => y^2 * (W y)^2)) z
      = 2 * (W z)^2 + 8 * z * (W z) * deriv W z + 2 * z^2 * (deriv W z)^2
        + 2 * z^2 * (W z) * deriv (deriv W) z := by
  have hWdiff : Differentiable ℝ W := hW.differentiable (by simp)
  have hW1diff : Differentiable ℝ (deriv W) :=
    (ContDiff.iterate_deriv 1 hW).differentiable (by simp)
  have hWz : HasDerivAt W (deriv W z) z := hWdiff.differentiableAt.hasDerivAt
  have hW1z : HasDerivAt (deriv W) (deriv (deriv W) z) z := hW1diff.differentiableAt.hasDerivAt
  have hfun : deriv (fun y : ℝ => y^2 * (W y)^2)
      = fun y => 2 * y * (W y)^2 + 2 * y^2 * (W y) * deriv W y := by
    funext y
    exact deriv_sq_mul_sq W hWdiff y
  rw [hfun]
  have hA : HasDerivAt (fun y : ℝ => 2 * y * (W y)^2)
      (2 * (W z)^2 + (2 * z) * (2 * (W z) * deriv W z)) z := by
    have hid : HasDerivAt (fun y : ℝ => 2 * y) 2 z := hasDerivAt_const_mul (2 : ℝ)
    have hWs : HasDerivAt (fun y : ℝ => (W y)^2) (2 * (W z) * deriv W z) z := by
      have h := hWz.pow 2
      have hd : HasDerivAt (fun y : ℝ => (W y)^2) (↑2 * (W z) ^ (2 - 1) * deriv W z) z := h
      convert hd using 1
      ring_nf
    have h := hid.mul hWs
    have hd : HasDerivAt (fun y : ℝ => 2 * y * (W y)^2)
        (2 * (W z)^2 + (2 * z) * (2 * (W z) * deriv W z)) z := h
    convert hd using 1
  have hB : HasDerivAt (fun y : ℝ => 2 * y^2 * (W y) * deriv W y)
      ((2 * (2 * z)) * (W z) * (deriv W z)
        + (2 * z^2) * ((deriv W z) * (deriv W z) + (W z) * (deriv (deriv W) z))) z := by
    have h1 : HasDerivAt (fun y : ℝ => 2 * y^2) (2 * (2 * z)) z := by
      have h := (hasDerivAt_id z).pow 2
      have h2 : HasDerivAt (fun y : ℝ => y^2) (2 * z) z := by
        have hd : HasDerivAt (fun y : ℝ => y^2) (↑2 * z ^ (2 - 1) * 1) z := h
        convert hd using 1
        ring_nf
      have hc := h2.const_mul (2 : ℝ)
      have hd : HasDerivAt (fun y : ℝ => 2 * y^2) (2 * (2 * z)) z := hc
      convert hd using 1
    have h := (h1.mul hWz).mul hW1z
    have hd : HasDerivAt (fun y : ℝ => 2 * y^2 * (W y) * deriv W y)
        ((2 * (2 * z) * (W z) + 2 * z^2 * (deriv W z)) * (deriv W z)
          + (2 * z^2 * (W z)) * (deriv (deriv W) z)) z := h
    convert hd using 1
    ring
  have hsum := hA.add hB
  have hder : deriv (fun y : ℝ => 2 * y * (W y)^2 + 2 * y^2 * (W y) * deriv W y) z
      = 2 * (W z)^2 + (2 * z) * (2 * (W z) * deriv W z)
        + ((2 * (2 * z)) * (W z) * (deriv W z)
          + (2 * z^2) * ((deriv W z) * (deriv W z) + (W z) * (deriv (deriv W) z))) := hsum.deriv
  rw [hder]
  ring

/-! ### The two final bounds, for an abstract function `W` -/

lemma mul_sq_deriv_bound (W : ℝ → ℝ) (hW : Differentiable ℝ W) (z M : ℝ) (hM : 1 ≤ M)
    (hWle : |W z| ≤ 1) (hb : |z * deriv W z| ≤ 2 * M) :
    |deriv (fun y : ℝ => y * (W y)^2) z| ≤ 1 + 4 * M := by
  rw [deriv_mul_sq W hW z]
  have h1 : |(W z)^2| ≤ 1 := by
    rw [abs_pow]
    nlinarith [hWle, abs_nonneg (W z)]
  have h2 : |2 * (W z) * (z * deriv W z)| ≤ 2 * (1 * (2 * M)) := by
    rw [show (2 : ℝ) * (W z) * (z * deriv W z) = 2 * ((W z) * (z * deriv W z)) from by ring,
      abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    nlinarith [mul_le_mul hWle hb (abs_nonneg _) (by linarith)]
  have key := abs_add_le ((W z)^2) (2 * (W z) * (z * deriv W z))
  linarith

lemma sq_mul_sq_deriv_bound (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (z M : ℝ) (hM : 1 ≤ M)
    (hWle : |W z| ≤ 1) (hb : |z * deriv W z| ≤ 2 * M)
    (hb2 : |z^2 * deriv (deriv W) z| ≤ 2 * M + 2 * M^2) :
    |deriv (deriv (fun y : ℝ => y^2 * (W y)^2)) z| ≤ 2 + 20 * M + 12 * M^2 := by
  rw [deriv_sq_mul_sq_deriv W hW z]
  rw [show 8 * z * (W z) * deriv W z = 8 * (W z) * (z * deriv W z) from by ring,
      show 2 * z^2 * (deriv W z)^2 = 2 * (z * deriv W z)^2 from by ring,
      show 2 * z^2 * (W z) * deriv (deriv W) z = 2 * (W z) * (z^2 * deriv (deriv W) z) from by ring]
  have b1 : |2 * (W z)^2| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_pow]
    nlinarith [hWle, abs_nonneg (W z)]
  have b2 : |8 * (W z) * (z * deriv W z)| ≤ 8 * (2 * M) := by
    rw [show (8 : ℝ) * (W z) * (z * deriv W z) = 8 * ((W z) * (z * deriv W z)) from by ring,
      abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 8 by norm_num)]
    nlinarith [mul_le_mul hWle hb (abs_nonneg _) (by linarith)]
  have b3 : |2 * (z * deriv W z)^2| ≤ 2 * (2 * M)^2 := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_pow]
    nlinarith [hb, abs_nonneg (z * deriv W z)]
  have b4 : |2 * (W z) * (z^2 * deriv (deriv W) z)| ≤ 2 * (1 * (2 * M + 2 * M^2)) := by
    rw [show (2 : ℝ) * (W z) * (z^2 * deriv (deriv W) z)
          = 2 * ((W z) * (z^2 * deriv (deriv W) z)) from by ring,
      abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    nlinarith [mul_le_mul hWle hb2 (abs_nonneg _) (by nlinarith [hM])]
  have key : |2 * (W z)^2 + 8 * (W z) * (z * deriv W z) + 2 * (z * deriv W z)^2
        + 2 * (W z) * (z^2 * deriv (deriv W) z)|
      ≤ |2 * (W z)^2| + |8 * (W z) * (z * deriv W z)| + |2 * (z * deriv W z)^2|
        + |2 * (W z) * (z^2 * deriv (deriv W) z)| := by
    have h12 := abs_add_le (2 * (W z)^2) (8 * (W z) * (z * deriv W z))
    have h123 := abs_add_le (2 * (W z)^2 + 8 * (W z) * (z * deriv W z)) (2 * (z * deriv W z)^2)
    have h1234 := abs_add_le ((2 * (W z)^2 + 8 * (W z) * (z * deriv W z))
      + 2 * (z * deriv W z)^2) (2 * (W z) * (z^2 * deriv (deriv W) z))
    linarith
  linarith

/-! ### The result -/

lemma Wc_abs_le_one (n : ℕ) (z : ℝ) : |Work.FTS.EllipticEst.PropL2Cut.Wc n z| ≤ 1 := by
  rw [abs_of_nonneg (Work.FTS.EllipticEst.PropL2Cut.Wc_nonneg n z)]
  exact Work.FTS.EllipticEst.PropL2Cut.Wc_le_one n z

lemma Wc_differentiable (n : ℕ) : Differentiable ℝ (Work.FTS.EllipticEst.PropL2Cut.Wc n) :=
  (Work.FTS.EllipticEst.PropL2Cut.Wc_contDiff n).differentiable (by simp)

theorem Wc_deriv_bdd :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ z : ℝ,
      |deriv (fun y => deriv (fun y => y ^ 2 * (Work.FTS.EllipticEst.PropL2Cut.Wc n y) ^ 2) y) z| ≤ C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ z : ℝ,
      |deriv (fun y => y * (Work.FTS.EllipticEst.PropL2Cut.Wc n y) ^ 2) z| ≤ C) := by
  obtain ⟨M, hM1, h1, h2, h3, h4⟩ := Wc_aux_bounds
  refine ⟨⟨2 + 20 * M + 12 * M ^ 2, by nlinarith, fun n z => ?_⟩,
    ⟨1 + 4 * M, by linarith, fun n z => ?_⟩⟩
  · exact sq_mul_sq_deriv_bound (Work.FTS.EllipticEst.PropL2Cut.Wc n)
      (Work.FTS.EllipticEst.PropL2Cut.Wc_contDiff n) z M hM1 (Wc_abs_le_one n z)
      (Wc_z_mul_deriv_bound n z M h1 h3) (Wc_zsq_mul_deriv2_bound n z M h1 h3 h2 h4)
  · exact mul_sq_deriv_bound (Work.FTS.EllipticEst.PropL2Cut.Wc n) (Wc_differentiable n)
      z M hM1 (Wc_abs_le_one n z) (Wc_z_mul_deriv_bound n z M h1 h3)

end Work.FTS.EllipticEst.PropL2CutKids
