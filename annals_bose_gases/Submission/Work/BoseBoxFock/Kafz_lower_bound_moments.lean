import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.gauss_moments_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Kafz_lower_bound_moments`

The lower bound delivered by FS `thm:Kafz` when the coefficient multiplying the state
`Φ Ψ z` in the anti-Wick symbol is **not constant in `z`**, but of the form
`d - (a‖z‖² + b‖z‖ + c)` with `a, b ≥ 0`.  In FS §9–§11 the symbol of the box
Hamiltonian, read along a fixed state, has precisely this shape: a constant `d`, minus a
`z`-dependent error whose quadratic and linear parts in `‖z‖` are controlled by the two
Gaussian moments

    `∫ ‖z‖² ‖Φ Ψ z‖² dν ≤ A ‖Ψ‖²`,   `∫ ‖z‖ ‖Φ Ψ z‖² dν ≤ B ‖Ψ‖²`.

The proof is that of `Work.BoseB4.Kafz_lower_bound_pointwise`, with the constant folded
into the moments:

* the `c`-number substitution `Work.BoseB4.Kafz_sum` writes the Fock expectation as
  `∫ dν(z)` of the symbol expectation;
* the hypothesis `h` bounds the integrand pointwise from below by
  `(d - (a‖z‖² + b‖z‖ + c)) ‖Φ Ψ z‖²`, and `integral_mono` integrates this;
* linearity of the integral computes

      `∫ (d - (a‖z‖² + b‖z‖ + c)) ‖Φ Ψ z‖² dν = d M₀ - (a M₂ + b M₁ + c M₀)`,

  with `M₀ = ∫ ‖Φ Ψ z‖² dν`, `M₂`, `M₁` the moments above;
* the Bargmann isometry gives `M₀ = ‖Ψ‖²`, and the two moment bounds give
  `a M₂ + b M₁ ≤ (a A + b B) M₀ ≤ (err - c) M₀`, whence
  `(d - err) M₀ ≤ d M₀ - (a M₂ + b M₁ + c M₀)`.

Everything is `sorry`-free and rests on the standard axioms only.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false

theorem Kafz_lower_bound_moments {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} (s : Finset ι) (p q : ι → ℕ) (B : ι → E →ₗ[ℂ] E)
    (d a b c A Bm err : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (Ψ : Work.BoseB4.FockCore E)
    (h : ∀ z : ℂ, (d - (a * ‖z‖ ^ 2 + b * ‖z‖ + c)) * ‖Work.BoseB4.Phi Ψ z‖ ^ 2
        ≤ (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i)
            * inner ℂ (Work.BoseB4.Phi Ψ z) (B i (Work.BoseB4.Phi Ψ z))).re)
    (hm2 : (∫ z : ℂ, ‖z‖ ^ 2 * ‖Work.BoseB4.Phi Ψ z‖ ^ 2 ∂Work.BoseB4.gauss)
        ≤ A * ‖Work.BoseB4.Embed E Ψ‖ ^ 2)
    (hm1 : (∫ z : ℂ, ‖z‖ * ‖Work.BoseB4.Phi Ψ z‖ ^ 2 ∂Work.BoseB4.gauss)
        ≤ Bm * ‖Work.BoseB4.Embed E Ψ‖ ^ 2)
    (herr : a * A + b * Bm + c ≤ err) :
    (d - err) * ‖Work.BoseB4.Embed E Ψ‖ ^ 2
      ≤ (inner ℂ (Work.BoseB4.Embed E Ψ)
          (Work.BoseB4.Embed E (∑ i ∈ s, Work.BoseB4.monoOp (p i) (q i) (B i) Ψ))).re := by
  classical
  -- The three scalars carrying the `z`-dependence of the symbol.
  set I0 : ℝ := ∫ z : ℂ, ‖Work.BoseB4.Phi Ψ z‖ ^ 2 ∂Work.BoseB4.gauss with hI0
  set I1 : ℝ := ∫ z : ℂ, ‖z‖ * ‖Work.BoseB4.Phi Ψ z‖ ^ 2 ∂Work.BoseB4.gauss with hI1
  set I2 : ℝ := ∫ z : ℂ, ‖z‖ ^ 2 * ‖Work.BoseB4.Phi Ψ z‖ ^ 2 ∂Work.BoseB4.gauss with hI2
  -- Integrability of the three moments of `‖Φ Ψ z‖²`.
  have hint0 : Integrable (fun z : ℂ => ‖Work.BoseB4.Phi Ψ z‖ ^ 2) Work.BoseB4.gauss :=
    gm_integrable_Phi_normSq Ψ
  have hint2 : Integrable (fun z : ℂ => ‖z‖ ^ 2 * ‖Work.BoseB4.Phi Ψ z‖ ^ 2)
      Work.BoseB4.gauss := gm_integrable_Phi_normSq_moment2 Ψ
  have hint1 : Integrable (fun z : ℂ => ‖z‖ * ‖Work.BoseB4.Phi Ψ z‖ ^ 2)
      Work.BoseB4.gauss := by
    refine Integrable.mono' (hint0.add hint2) ?_ ?_
    · exact (continuous_norm.aestronglyMeasurable).mul hint0.1
    · filter_upwards with z
      have hf : 0 ≤ ‖Work.BoseB4.Phi Ψ z‖ ^ 2 := sq_nonneg _
      have hz1 : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by
        nlinarith [sq_nonneg (‖z‖ - 1), norm_nonneg z]
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg z) hf)]
      calc ‖z‖ * ‖Work.BoseB4.Phi Ψ z‖ ^ 2
          ≤ (1 + ‖z‖ ^ 2) * ‖Work.BoseB4.Phi Ψ z‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hz1 hf
        _ = ‖Work.BoseB4.Phi Ψ z‖ ^ 2 + ‖z‖ ^ 2 * ‖Work.BoseB4.Phi Ψ z‖ ^ 2 := by ring
  have hquadint : Integrable (fun z : ℂ => inner ℂ (Work.BoseB4.Phi Ψ z) (Work.BoseB4.Phi Ψ z))
      Work.BoseB4.gauss := by
    simpa using Work.BoseB4.integrable_kafz_integrand (E := E) 0 0 (1 : E →ₗ[ℂ] E) Ψ
  -- The Bargmann isometry in the form `M₀ = ‖Ψ‖²`.
  have hI0norm : I0 = ‖Work.BoseB4.Embed E Ψ‖ ^ 2 := by
    rw [hI0]
    have hh := congrArg Complex.re (Work.BoseB4.Bargmann_inner Ψ Ψ)
    rw [Work.BoseB4.coreInner] at hh
    have hre : (∫ z : ℂ, (inner ℂ (Work.BoseB4.Phi Ψ z) (Work.BoseB4.Phi Ψ z)).re
          ∂Work.BoseB4.gauss)
        = (∫ z : ℂ, inner ℂ (Work.BoseB4.Phi Ψ z) (Work.BoseB4.Phi Ψ z)
            ∂Work.BoseB4.gauss).re := integral_re hquadint
    rw [← hre] at hh
    rw [show (inner ℂ (Work.BoseB4.Embed E Ψ) (Work.BoseB4.Embed E Ψ)).re
        = ‖Work.BoseB4.Embed E Ψ‖ ^ 2 from Work.BoseB4.re_inner_self _] at hh
    rw [show (∫ z : ℂ, (inner ℂ (Work.BoseB4.Phi Ψ z) (Work.BoseB4.Phi Ψ z)).re
          ∂Work.BoseB4.gauss)
        = ∫ z : ℂ, ‖Work.BoseB4.Phi Ψ z‖ ^ 2 ∂Work.BoseB4.gauss from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      exact Work.BoseB4.re_inner_self _] at hh
    exact hh.symm
  rw [← hI0norm] at hm1 hm2
  have hI0nn : 0 ≤ I0 := by rw [hI0norm]; positivity
  -- Integrability of the symbol of the finite sum, and its `c`-number substitution.
  have hsumint : Integrable (fun z : ℂ => ∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
      inner ℂ (Work.BoseB4.Phi Ψ z) (B i (Work.BoseB4.Phi Ψ z))) Work.BoseB4.gauss :=
    integrable_finsetSum s fun i _ => Work.BoseB4.integrable_kafz_integrand (p i) (q i) (B i) Ψ
  have hRe : (inner ℂ (Work.BoseB4.Embed E Ψ)
        (Work.BoseB4.Embed E (∑ i ∈ s, Work.BoseB4.monoOp (p i) (q i) (B i) Ψ))).re
      = ∫ z : ℂ, (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
          inner ℂ (Work.BoseB4.Phi Ψ z) (B i (Work.BoseB4.Phi Ψ z))).re ∂Work.BoseB4.gauss := by
    rw [Work.BoseB4.Kafz_sum s p q B Ψ]
    exact (integral_re hsumint).symm
  -- The pointwise identity behind the linearity of the integral.
  have hident : ∀ z : ℂ, (d - (a * ‖z‖ ^ 2 + b * ‖z‖ + c)) * ‖Work.BoseB4.Phi Ψ z‖ ^ 2
      = d * ‖Work.BoseB4.Phi Ψ z‖ ^ 2
        - (a * (‖z‖ ^ 2 * ‖Work.BoseB4.Phi Ψ z‖ ^ 2)
            + b * (‖z‖ * ‖Work.BoseB4.Phi Ψ z‖ ^ 2) + c * ‖Work.BoseB4.Phi Ψ z‖ ^ 2) := by
    intro z; ring
  have hInt12 : Integrable (fun z : ℂ => a * (‖z‖ ^ 2 * ‖Work.BoseB4.Phi Ψ z‖ ^ 2)
      + b * (‖z‖ * ‖Work.BoseB4.Phi Ψ z‖ ^ 2)) Work.BoseB4.gauss :=
    (hint2.const_mul a).add (hint1.const_mul b)
  have hIntAll : Integrable (fun z : ℂ => a * (‖z‖ ^ 2 * ‖Work.BoseB4.Phi Ψ z‖ ^ 2)
      + b * (‖z‖ * ‖Work.BoseB4.Phi Ψ z‖ ^ 2) + c * ‖Work.BoseB4.Phi Ψ z‖ ^ 2)
      Work.BoseB4.gauss := hInt12.add (hint0.const_mul c)
  have hintFull : Integrable (fun z : ℂ =>
      (d - (a * ‖z‖ ^ 2 + b * ‖z‖ + c)) * ‖Work.BoseB4.Phi Ψ z‖ ^ 2) Work.BoseB4.gauss :=
    ((hint0.const_mul d).sub hIntAll).congr
      (Filter.Eventually.of_forall fun z => (hident z).symm)
  -- Monotonicity of the integral and the hypothesis `h`.
  have hmono : (∫ z : ℂ, (d - (a * ‖z‖ ^ 2 + b * ‖z‖ + c)) * ‖Work.BoseB4.Phi Ψ z‖ ^ 2
        ∂Work.BoseB4.gauss)
      ≤ ∫ z : ℂ, (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
          inner ℂ (Work.BoseB4.Phi Ψ z) (B i (Work.BoseB4.Phi Ψ z))).re
        ∂Work.BoseB4.gauss := by
    refine integral_mono hintFull hsumint.re ?_
    intro z
    exact h z
  -- Linearity of the integral.
  have hLHSint : (∫ z : ℂ, (d - (a * ‖z‖ ^ 2 + b * ‖z‖ + c)) * ‖Work.BoseB4.Phi Ψ z‖ ^ 2
        ∂Work.BoseB4.gauss)
      = d * (∫ z : ℂ, ‖Work.BoseB4.Phi Ψ z‖ ^ 2 ∂Work.BoseB4.gauss)
        - (a * (∫ z : ℂ, ‖z‖ ^ 2 * ‖Work.BoseB4.Phi Ψ z‖ ^ 2 ∂Work.BoseB4.gauss)
            + b * (∫ z : ℂ, ‖z‖ * ‖Work.BoseB4.Phi Ψ z‖ ^ 2 ∂Work.BoseB4.gauss)
            + c * (∫ z : ℂ, ‖Work.BoseB4.Phi Ψ z‖ ^ 2 ∂Work.BoseB4.gauss)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hident)]
    rw [integral_sub (hint0.const_mul d) hIntAll,
      integral_add hInt12 (hint0.const_mul c),
      integral_add (hint2.const_mul a) (hint1.const_mul b),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  -- The two moment bounds, multiplied by `a, b ≥ 0`.
  have hkey : a * I2 + b * I1 ≤ (err - c) * I0 := by
    have h1 : a * I2 ≤ a * (A * I0) := mul_le_mul_of_nonneg_left hm2 ha
    have h2 : b * I1 ≤ b * (Bm * I0) := mul_le_mul_of_nonneg_left hm1 hb
    have h3 : (a * A + b * Bm) * I0 ≤ (err - c) * I0 :=
      mul_le_mul_of_nonneg_right (by linarith [herr]) hI0nn
    calc a * I2 + b * I1 ≤ a * (A * I0) + b * (Bm * I0) := add_le_add h1 h2
      _ = (a * A + b * Bm) * I0 := by ring
      _ ≤ (err - c) * I0 := h3
  have hmain : (d - err) * I0
      ≤ ∫ z : ℂ, (d - (a * ‖z‖ ^ 2 + b * ‖z‖ + c)) * ‖Work.BoseB4.Phi Ψ z‖ ^ 2
          ∂Work.BoseB4.gauss := by
    rw [hLHSint, ← hI0, ← hI1, ← hI2]
    linarith [hkey]
  calc (d - err) * ‖Work.BoseB4.Embed E Ψ‖ ^ 2
      = (d - err) * I0 := by rw [← hI0norm]
    _ ≤ ∫ z : ℂ, (d - (a * ‖z‖ ^ 2 + b * ‖z‖ + c)) * ‖Work.BoseB4.Phi Ψ z‖ ^ 2
          ∂Work.BoseB4.gauss := hmain
    _ ≤ ∫ z : ℂ, (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
          inner ℂ (Work.BoseB4.Phi Ψ z) (B i (Work.BoseB4.Phi Ψ z))).re
          ∂Work.BoseB4.gauss := hmono
    _ = (inner ℂ (Work.BoseB4.Embed E Ψ)
          (Work.BoseB4.Embed E (∑ i ∈ s, Work.BoseB4.monoOp (p i) (q i) (B i) Ψ))).re := hRe.symm

end Work.BoseBoxFock
