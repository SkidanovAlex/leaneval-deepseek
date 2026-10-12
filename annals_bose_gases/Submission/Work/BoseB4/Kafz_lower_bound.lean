import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB4.Kafz_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Kafz_lower_bound`

The lower bound delivered by FS `thm:Kafz`: if the anti-Wick symbol `𝓚(z)` of a
finite sum of anti-normal monomials is bounded below by the scalar `c` as a
quadratic form on the spectator space, then the second-quantised operator is
bounded below by `c` on the algebraic Fock core.

    `c ‖Ψ‖² ≤ Re ⟪Ψ, H Ψ⟫`,   `H = ∑ᵢ a₀^{pᵢ} (a₀†)^{qᵢ} (lift Bᵢ)`.

The proof is the coherent-state substitution `Kafz_sum` followed by a pointwise
lower bound and monotonicity of the integral: the substitution writes
`Re ⟪Ψ, H Ψ⟫` as `∫ dν(z)` of `Re ⟪Φ Ψ z, 𝓚(z) Φ Ψ z⟫ ≥ c ‖Φ Ψ z‖²`, and the
Bargmann isometry gives `∫ ‖Φ Ψ z‖² dν(z) = ‖Ψ‖²`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The real part of `⟪x, x⟫` is the square of the norm, in the `ℂ`-specialised
form used below (`RCLike.re` is definitionally `Complex.re` on `ℂ`). -/
lemma re_inner_self (x : E) : (inner ℂ x x).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

/-- The anti-Wick symbol of a finite sum, evaluated as a sesquilinear form:
`∑ᵢ z^{pᵢ} z̄^{qᵢ} ⟪v, Bᵢ v⟫ = ⟪v, (∑ᵢ z^{pᵢ} z̄^{qᵢ} Bᵢ) v⟫`.  This is the
pointwise (in `z`) form of `Work.BoseB4.symbol_apply` together with the fact that
the inner product is linear in its second argument. -/
lemma sum_symbol_inner {ι : Type*} (s : Finset ι) (p q : ι → ℕ) (B : ι → E →ₗ[ℂ] E)
    (z : ℂ) (v : E) :
    (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) * inner ℂ v (B i v))
      = inner ℂ v ((∑ i ∈ s, symbol (p i) (q i) (B i) z) v) := by
  rw [sum_symbol_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right]

theorem Kafz_lower_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} (s : Finset ι) (p q : ι → ℕ) (B : ι → E →ₗ[ℂ] E) (c : ℝ)
    (h : ∀ (z : ℂ) (v : E),
      c * ‖v‖ ^ 2 ≤ (inner ℂ v ((∑ i ∈ s, Work.BoseB4.symbol (p i) (q i) (B i) z) v)).re)
    (Ψ : Work.BoseB4.FockCore E) :
    c * ‖Work.BoseB4.Embed E Ψ‖ ^ 2
      ≤ (inner ℂ (Work.BoseB4.Embed E Ψ)
          (Work.BoseB4.Embed E (∑ i ∈ s, Work.BoseB4.monoOp (p i) (q i) (B i) Ψ))).re := by
  classical
  -- Integrability of each monomial summand (a polynomial against the Gaussian measure).
  have hFint : ∀ i ∈ s, Integrable (fun z : ℂ => z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
      inner ℂ (Phi Ψ z) (B i (Phi Ψ z))) gauss :=
    fun i _ => integrable_kafz_integrand (p i) (q i) (B i) Ψ
  have hsumint : Integrable (fun z : ℂ => ∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
      inner ℂ (Phi Ψ z) (B i (Phi Ψ z))) gauss :=
    integrable_finsetSum s hFint
  -- Integrability of `z ↦ ⟪Φ Ψ z, Φ Ψ z⟫` (the `B = 1`, `p = q = 0` case).
  have hquadint : Integrable (fun z : ℂ => inner ℂ (Phi Ψ z) (Phi Ψ z)) gauss := by
    simpa using integrable_kafz_integrand 0 0 (1 : E →ₗ[ℂ] E) Ψ
  have hnormint : Integrable (fun z : ℂ => ‖Phi Ψ z‖ ^ 2) gauss := by
    refine hquadint.re.congr ?_
    filter_upwards with z
    exact re_inner_self (Phi Ψ z)
  -- The Bargmann isometry in the form `∫ ‖Φ Ψ z‖² dν(z) = ‖Ψ‖²`.
  have hnorm : (∫ z : ℂ, ‖Phi Ψ z‖ ^ 2 ∂gauss) = ‖Embed E Ψ‖ ^ 2 := by
    have hh := congrArg Complex.re (Bargmann_inner Ψ Ψ)
    rw [coreInner] at hh
    have hre : (∫ z : ℂ, (inner ℂ (Phi Ψ z) (Phi Ψ z)).re ∂gauss)
        = (∫ z : ℂ, inner ℂ (Phi Ψ z) (Phi Ψ z) ∂gauss).re :=
      integral_re hquadint
    rw [← hre] at hh
    rw [show (inner ℂ (Embed E Ψ) (Embed E Ψ)).re = ‖Embed E Ψ‖ ^ 2 from
      re_inner_self (Embed E Ψ)] at hh
    rw [show (∫ z : ℂ, (inner ℂ (Phi Ψ z) (Phi Ψ z)).re ∂gauss)
        = ∫ z : ℂ, ‖Phi Ψ z‖ ^ 2 ∂gauss from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      exact re_inner_self (Phi Ψ z)] at hh
    exact hh.symm
  -- The `c`-number substitution, then real parts.
  have hRe : (inner ℂ (Embed E Ψ) (Embed E (∑ i ∈ s, monoOp (p i) (q i) (B i) Ψ))).re
      = ∫ z : ℂ, (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
          inner ℂ (Phi Ψ z) (B i (Phi Ψ z))).re ∂gauss := by
    rw [Kafz_sum s p q B Ψ]
    exact (integral_re hsumint).symm
  -- Pointwise lower bound from the hypothesis on the symbol.
  have hpt : ∀ z : ℂ, c * ‖Phi Ψ z‖ ^ 2
      ≤ (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
          inner ℂ (Phi Ψ z) (B i (Phi Ψ z))).re := by
    intro z
    rw [sum_symbol_inner s p q B z (Phi Ψ z)]
    exact h z (Phi Ψ z)
  have hbound : (∫ z : ℂ, c * ‖Phi Ψ z‖ ^ 2 ∂gauss)
      ≤ ∫ z : ℂ, (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
          inner ℂ (Phi Ψ z) (B i (Phi Ψ z))).re ∂gauss := by
    refine integral_mono (hnormint.const_mul c) hsumint.re ?_
    intro z
    exact hpt z
  calc c * ‖Embed E Ψ‖ ^ 2
      = ∫ z : ℂ, c * ‖Phi Ψ z‖ ^ 2 ∂gauss := by rw [integral_const_mul, hnorm]
    _ ≤ ∫ z : ℂ, (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
          inner ℂ (Phi Ψ z) (B i (Phi Ψ z))).re ∂gauss := hbound
    _ = (inner ℂ (Embed E Ψ)
          (Embed E (∑ i ∈ s, monoOp (p i) (q i) (B i) Ψ))).re := hRe.symm

end Work.BoseB4
