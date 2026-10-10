import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.local_lifting_setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **The Kummer ratio as a homomorphism to the roots of unity.**

Let `A` be a place of `ℚ̄`, `N ≥ 1`, and `θ : ℚ̄` nonzero with `θ ^ N` fixed by `D_A` and such
that every `N`-th root of unity is fixed by every `σ ∈ D_A` (`hfixRU`). Then the ratio
`σ ↦ σ θ / θ` (a unit of `ℚ̄`) is a group homomorphism `D_A →* μ_N(ℚ̄)`: there is
`ψ : ↥(decomp ℚ A) →* ↥(rootsOfUnity N ℚ̄)` with `(ψ σ : ℚ̄ˣ) = (σ : GalQ) θ / θ` for all `σ`. -/
lemma kummerRatioHom (A : ValuationSubring SSGRoute.QBar) (N : ℕ) (hN : N ≠ 0)
    (θ : SSGRoute.QBar) (hθ : θ ≠ 0)
    (hfix : ∀ σ : ↥(SSGRoute.decomp ℚ A), (σ : SSGRoute.GalQ) (θ ^ N) = θ ^ N)
    (hfixRU : ∀ σ ∈ SSGRoute.decomp ℚ A, ∀ η : SSGRoute.QBar, η ^ N = 1 → σ η = η) :
    ∃ ψ : ↥(SSGRoute.decomp ℚ A) →* ↥(rootsOfUnity N SSGRoute.QBar),
      ∀ σ : ↥(SSGRoute.decomp ℚ A),
        (((ψ σ : ↥(rootsOfUnity N SSGRoute.QBar)) : SSGRoute.QBarˣ) : SSGRoute.QBar)
          = ((σ : SSGRoute.GalQ) θ) / θ := by
  -- `σθ/θ` is an `N`-th root of unity: `(σθ/θ)^N = σ(θ^N)/θ^N = θ^N/θ^N = 1`.
  have hmem0 : ∀ σ : ↥(SSGRoute.decomp ℚ A), (((σ : SSGRoute.GalQ) θ) / θ) ^ N = 1 := by
    intro σ
    rw [div_pow, ← map_pow, hfix σ]
    exact div_self (pow_ne_zero N hθ)
  -- The multiplicativity of the ratio: `(στ)θ/θ = (σθ/θ)·(τθ/θ)`, using that
  -- `τθ/θ` is an `N`-th root of unity, hence fixed by `σ ∈ D_A`.
  have key : ∀ σ τ : ↥(SSGRoute.decomp ℚ A),
      (((σ * τ : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) θ) / θ
        = (((σ : SSGRoute.GalQ) θ) / θ) * (((τ : SSGRoute.GalQ) θ) / θ) := by
    intro σ τ
    have hval : ((σ * τ : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)
        = (σ : SSGRoute.GalQ) * (τ : SSGRoute.GalQ) := rfl
    have hτ : (τ : SSGRoute.GalQ) θ = (((τ : SSGRoute.GalQ) θ) / θ) * θ :=
      (div_mul_cancel₀ ((τ : SSGRoute.GalQ) θ) hθ).symm
    have hσfix : (σ : SSGRoute.GalQ) (((τ : SSGRoute.GalQ) θ) / θ)
        = ((τ : SSGRoute.GalQ) θ) / θ :=
      hfixRU (σ : SSGRoute.GalQ) σ.2 (((τ : SSGRoute.GalQ) θ) / θ) (hmem0 τ)
    have hmul : (((σ * τ : ↥(SSGRoute.decomp ℚ A))) : SSGRoute.GalQ) θ
        = ((((τ : SSGRoute.GalQ) θ) / θ)) * ((σ : SSGRoute.GalQ) θ) := by
      rw [hval, AlgEquiv.mul_apply]
      conv_lhs => rw [hτ]
      rw [map_mul, hσfix]
    rw [hmul, mul_div_assoc, mul_comm]
  refine ⟨MonoidHom.codRestrict
    { toFun := fun σ : ↥(SSGRoute.decomp ℚ A) => Units.mk0 (((σ : SSGRoute.GalQ) θ) / θ)
        (div_ne_zero ((map_ne_zero (σ : SSGRoute.GalQ)).mpr hθ) hθ),
      map_one' := ?_,
      map_mul' := ?_ } (rootsOfUnity N SSGRoute.QBar) ?_, ?_⟩
  · -- `1 θ / θ = 1`
    apply Units.ext
    change (((1 : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) θ) / θ = (1 : SSGRoute.QBar)
    rw [show ((1 : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) θ = θ from rfl, div_self hθ]
  · intro σ τ
    apply Units.ext
    exact key σ τ
  · -- the values are `N`-th roots of unity
    intro σ
    rw [mem_rootsOfUnity']
    exact hmem0 σ
  · intro σ
    rfl

end Work.SSGRoute
