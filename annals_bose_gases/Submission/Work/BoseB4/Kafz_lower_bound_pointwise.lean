import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB4.Kafz_lower_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Kafz_lower_bound_pointwise`

The *pointwise* form of `Work.BoseB4.Kafz_lower_bound`.  There, the lower bound
was assumed for the anti-Wick symbol as a quadratic form, `c‖v‖² ≤ Re⟪v, 𝓚(z) v⟫`
for **every** `v : E`.  Here it is only assumed for the single vector
`v = Φ Ψ z` produced by the state `Ψ` under the coherent-state transform — the
form in which the hypothesis actually arises in FS §9–§11, where the symbol is a
quadratic form in the (state-dependent) Bogoliubov functional `Φ Ψ z`.

The proof is that of `Kafz_lower_bound`: the `c`-number substitution `Kafz_sum`
writes the Fock-space expectation as `∫ dν(z)` of the symbol expectation, the
pointwise hypothesis bounds the integrand from below by `c‖Φ Ψ z‖²`, and the
Bargmann isometry gives `∫ ‖Φ Ψ z‖² dν(z) = ‖Ψ‖²`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB4

set_option autoImplicit false

theorem Kafz_lower_bound_pointwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} (s : Finset ι) (p q : ι → ℕ) (B : ι → E →ₗ[ℂ] E) (c : ℝ)
    (Ψ : Work.BoseB4.FockCore E)
    (h : ∀ z : ℂ, c * ‖Work.BoseB4.Phi Ψ z‖ ^ 2 ≤
        (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i)
            * inner ℂ (Work.BoseB4.Phi Ψ z) (B i (Work.BoseB4.Phi Ψ z))).re) :
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
  -- Pointwise lower bound: here it is the hypothesis itself, at `v = Φ Ψ z`.
  have hpt : ∀ z : ℂ, c * ‖Phi Ψ z‖ ^ 2
      ≤ (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
          inner ℂ (Phi Ψ z) (B i (Phi Ψ z))).re :=
    fun z => h z
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
