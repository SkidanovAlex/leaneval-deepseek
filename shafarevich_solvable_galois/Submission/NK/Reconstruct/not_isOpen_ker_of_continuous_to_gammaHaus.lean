import Mathlib
import Submission.NK.Reconstruct.gammaHaus
import Submission.NK.Reconstruct.not_isOpen_ker_of_infinite_range
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

open scoped NumberField

set_option linter.style.haveILetI false

/-- **The kernel of a non-zero continuous homomorphism from `Γ_K` into the torsion-free quotient
`Γ_M^{tf}` is not open.**  If `ker ψ` were open then `Γ_K ⧸ ker ψ` would be a discrete compact
group, hence finite, so `ψ.range` would be finite; but `Γ_M^{tf}` is torsion-free, so a finite
subgroup of it is trivial (`NK.Reconstruct.gammaHaus_finite_eq_bot`), forcing `ψ = 1`.

This is the substitute for Shimizu's rank argument in Proposition 4f.3 of arXiv:2009.10431: he
observes that `ker φ_τ` has ℓ-adic rank `< r_ℓ(L)` (hence Haar measure `0`); here the target
`Γ_M^{tf}` being torsion-free is what makes a non-zero `ψ` have non-open kernel, which is all the
Baire argument needs. -/
theorem not_isOpen_ker_of_continuous_to_gammaHaus {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    {M : Type*} [Field M] [NumberField M] {M' : Type*} [Field M'] [Algebra M M']
    [IsSepClosure M M'] (ℓ : ℕ) [Fact ℓ.Prime]
    (ψ : NK.Reconstruct.Gamma K K' ℓ →* NK.Reconstruct.GammaHaus M M' ℓ)
    (hψ : Continuous ⇑ψ) (hne : ψ ≠ 1) :
    ¬ IsOpen ((ψ.ker : Subgroup (NK.Reconstruct.Gamma K K' ℓ)) :
      Set (NK.Reconstruct.Gamma K K' ℓ)) := by
  -- An open kernel would make the quotient — hence the range — finite
  -- (`not_isOpen_ker_of_infinite_range`), and a finite subgroup of the torsion-free
  -- `Γ_M^{tf}` is trivial (`gammaHaus_finite_eq_bot`), contradicting `ψ ≠ 1`.
  refine not_isOpen_ker_of_infinite_range ψ (fun hfin => ?_)
  haveI : Finite ↥ψ.range := hfin
  have hbot : ψ.range = ⊥ := gammaHaus_finite_eq_bot
  exact hne (MonoidHom.range_eq_bot_iff.mp hbot)

end NK.Reconstruct
