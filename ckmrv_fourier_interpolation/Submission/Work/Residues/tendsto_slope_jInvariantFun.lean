import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Modular.ramanujan_E4
import Submission.Work.Modular.ramanujan_E6
import Submission.Work.Modular.EisensteinDelta
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic

/-!
# The derivative of the `j`-invariant at a point of `ℍ`

We prove that the difference quotient of `j = E₄³/Δ` along the upper half plane converges to
the paper's value `j' = -2πi E₄²E₆/Δ`.

The route is:

* `D Δ = E₂ Δ` and `D E₄ = (E₂E₄ - E₆)/3` (the latter is `Work.Modular.ramanujan_E4`), where
  `D = (2πi)⁻¹ d/dτ = Derivative.normalizedDerivOfComplex`;
* hence `D j = -E₄²E₆/Δ`, by differentiating the identity `Δ · j = E₄³`;
* the honest complex derivative of the lift `j ∘ ofComplex` is `2πi · D j`, and `j` is
  holomorphic on `ℍ`, so the slope limit along `ℍ` is that derivative.
-/

namespace Work.Residues

open Filter UpperHalfPlane ModularForm
open scoped Topology Manifold MatrixGroups

/-! ## The dictionary between `D` and the honest complex derivative -/

/-- For any `f : ℍ → ℂ`, the complex derivative of the lift `f ∘ ofComplex` is `2πi` times the
normalized derivative `D f = (2πi)⁻¹ d/dτ`.  This holds for every `f` (no differentiability
assumption); it is the dictionary used to turn the `D`-identities below into limits. -/
private lemma deriv_comp_ofComplex_eq (f : ℍ → ℂ) (z : ℍ) :
    deriv (f ∘ UpperHalfPlane.ofComplex) (z : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I) * Derivative.normalizedDerivOfComplex f z := by
  rw [Derivative.normalizedDerivOfComplex, mul_inv_cancel_left₀]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- The coefficient embedding `ℍ → ℂ` sends the punctured neighbourhood filter of `z` to the
punctured neighbourhood filter of `(z : ℂ)`. -/
private lemma tendsto_coe_nhdsNE (z : ℍ) :
    Tendsto (fun τ : ℍ => (τ : ℂ)) (𝓝[≠] z) (𝓝[≠] (z : ℂ)) := by
  rw [show 𝓝[≠] (z : ℂ) = nhds (z : ℂ) ⊓ 𝓟 {(z : ℂ)}ᶜ from rfl]
  rw [tendsto_inf]
  constructor
  · exact (continuous_coe.continuousAt (x := z)).tendsto.mono_left nhdsWithin_le_nhds
  · rw [tendsto_principal]
    apply Filter.mem_of_superset self_mem_nhdsWithin
    intro τ hτ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hτ ⊢
    exact fun h => hτ (UpperHalfPlane.coe_inj.mp h)

/-! ## Holomorphy -/

private lemma mdifferentiable_E4Fun :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Kernels.E4Fun :=
  ModularFormClass.holo ModularForm.E₄

private lemma mdifferentiable_E6Fun :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Kernels.E6Fun :=
  ModularFormClass.holo ModularForm.E₆

private lemma mdifferentiable_DeltaFun :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Kernels.DeltaFun :=
  ModularFormClass.holo
    (CuspForm.discriminant : CuspForm (Matrix.SpecialLinearGroup.mapGL ℝ).range 12)

private lemma mdifferentiable_jInvariantFun :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Kernels.jInvariantFun :=
  (mdifferentiable_E4Fun.pow 3).div mdifferentiable_DeltaFun
    (fun w => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero w)

/-! ## Ramanujan's identity for the discriminant -/

/-- The discriminant in the `E₄, E₆` normalization. -/
private lemma DeltaFun_eq (z : ℍ) :
    Work.Kernels.DeltaFun z
      = (Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E6Fun z ^ 2) / 1728 := by
  simpa [Work.Kernels.DeltaFun, Work.Kernels.E4Fun, Work.Kernels.E6Fun] using
    ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z

/-- **Ramanujan's identity for the discriminant**: `D Δ = E₂ Δ`. -/
private lemma normalizedDeriv_DeltaFun :
    Derivative.normalizedDerivOfComplex Work.Kernels.DeltaFun
      = fun z => Work.Kernels.E2Fun z * Work.Kernels.DeltaFun z := by
  have hE4' : Derivative.normalizedDerivOfComplex Work.Kernels.E4Fun
      = fun z => (Work.Kernels.E2Fun z * Work.Kernels.E4Fun z - Work.Kernels.E6Fun z) / 3 :=
    Work.Modular.ramanujan_E4
  have hE6' : Derivative.normalizedDerivOfComplex Work.Kernels.E6Fun
      = fun z => (Work.Kernels.E2Fun z * Work.Kernels.E6Fun z - Work.Kernels.E4Fun z ^ 2) / 2 :=
    Work.Modular.ramanujan_E6
  have hsplit : Work.Kernels.DeltaFun
      = (1 / 1728 : ℂ) • (Work.Kernels.E4Fun ^ 3 - Work.Kernels.E6Fun ^ 2) := by
    ext z
    rw [DeltaFun_eq]
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul]
    ring
  rw [hsplit,
    Derivative.normalizedDerivOfComplex_smul _ _
      ((mdifferentiable_E4Fun.pow 3).sub (mdifferentiable_E6Fun.pow 2)),
    Derivative.normalizedDerivOfComplex_sub _ _
      (mdifferentiable_E4Fun.pow 3) (mdifferentiable_E6Fun.pow 2),
    Derivative.normalizedDerivOfComplex_pow _ _ mdifferentiable_E4Fun,
    Derivative.normalizedDerivOfComplex_pow _ _ mdifferentiable_E6Fun,
    hE4', hE6']
  ext z
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, smul_eq_mul,
    Pi.natCast_apply]
  ring

/-! ## The derivative of `j` -/

/-- **The derivative of the `j`-invariant**: `D j = -E₄²E₆/Δ`. -/
private lemma normalizedDeriv_jInvariantFun :
    Derivative.normalizedDerivOfComplex Work.Kernels.jInvariantFun
      = fun z => -(Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z)
          / Work.Kernels.DeltaFun z := by
  have hE4' : Derivative.normalizedDerivOfComplex Work.Kernels.E4Fun
      = fun z => (Work.Kernels.E2Fun z * Work.Kernels.E4Fun z - Work.Kernels.E6Fun z) / 3 :=
    Work.Modular.ramanujan_E4
  -- The identity `Δ · j = E₄³` is differentiated with the product rule.
  have hfun : Work.Kernels.DeltaFun * Work.Kernels.jInvariantFun = Work.Kernels.E4Fun ^ 3 := by
    ext τ
    exact Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ
  have h3 : Derivative.normalizedDerivOfComplex
        (Work.Kernels.DeltaFun * Work.Kernels.jInvariantFun)
      = Derivative.normalizedDerivOfComplex (Work.Kernels.E4Fun ^ 3) := by rw [hfun]
  rw [Derivative.normalizedDerivOfComplex_mul _ _ mdifferentiable_DeltaFun
        mdifferentiable_jInvariantFun,
    Derivative.normalizedDerivOfComplex_pow _ _ mdifferentiable_E4Fun,
    normalizedDeriv_DeltaFun, hE4'] at h3
  ext z
  have hz := congrFun h3 z
  have hz0 : ModularForm.discriminant z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hΔeqz : Work.Kernels.DeltaFun z = ModularForm.discriminant z := rfl
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply] at hz
  rw [show Work.Kernels.jInvariantFun z
        = Work.Kernels.E4Fun z ^ 3 / Work.Kernels.DeltaFun z from rfl, hΔeqz] at hz
  norm_num at hz
  field_simp [hz0] at hz
  ring_nf at hz
  rw [hΔeqz, eq_div_iff hz0]
  linear_combination hz

/-- The honest complex derivative of the lift of `j` to `ℂ`, evaluated at `z`. -/
private lemma deriv_jInvariantFun_comp_ofComplex (z : ℍ) :
    deriv (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) (z : ℂ)
      = -(2 * Real.pi * Complex.I) * (Work.Kernels.E4Fun z) ^ 2 * Work.Kernels.E6Fun z
        / Work.Kernels.DeltaFun z := by
  rw [deriv_comp_ofComplex_eq, normalizedDeriv_jInvariantFun]
  ring

/-! ## The limit of the difference quotient -/

/-- **The derivative of the `j`-invariant.**  `j = E₄³/Δ` has complex derivative
`-2πi E₄²E₆/Δ`; here this is stated as the limit of the difference quotient along `ℍ`
(paper (2.7): `j' = -2πiE₄²E₆/Δ`, equivalently `1/j' = iΔ/(2πE₁₄)`). -/
theorem tendsto_slope_jInvariantFun (z : UpperHalfPlane) :
    Filter.Tendsto
      (fun τ : UpperHalfPlane =>
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) / ((τ : ℂ) - (z : ℂ)))
      (𝓝[≠] z)
      (𝓝 (-(2 * Real.pi * Complex.I) * (Work.Kernels.E4Fun z) ^ 2 * Work.Kernels.E6Fun z
        / Work.Kernels.DeltaFun z)) := by
  set c : ℂ := -(2 * Real.pi * Complex.I) * (Work.Kernels.E4Fun z) ^ 2 * Work.Kernels.E6Fun z
        / Work.Kernels.DeltaFun z with hc
  have hFdiff : DifferentiableAt ℂ (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex)
      (z : ℂ) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (mdifferentiable_jInvariantFun z)
  have hFderiv : deriv (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) (z : ℂ) = c := by
    rw [hc, deriv_jInvariantFun_comp_ofComplex]
  set F : ℂ → ℂ := Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex with hFdef
  have hslope : Tendsto (slope F (z : ℂ)) (𝓝[≠] (z : ℂ)) (𝓝 c) := by
    have h := hFdiff.hasDerivAt.tendsto_slope
    rwa [hFderiv] at h
  have hcomp := hslope.comp (tendsto_coe_nhdsNE z)
  have hfun : slope F (z : ℂ) ∘ (fun τ : ℍ => (τ : ℂ)) =
      fun τ : ℍ =>
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) / ((τ : ℂ) - (z : ℂ)) := by
    ext τ
    simp only [Function.comp_apply, hFdef]
    rw [slope_def_module]
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hfun, hc] at hcomp
  exact hcomp

end Work.Residues
