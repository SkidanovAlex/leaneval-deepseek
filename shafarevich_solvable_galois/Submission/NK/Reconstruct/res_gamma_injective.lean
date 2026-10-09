import Mathlib
import Submission.NK.Reconstruct.resInjective
import Submission.NK.Reconstruct.finite_coker_gammaBaseChangeHom
import Submission.NK.Reconstruct.gammaBaseChange
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The injectivity half of Shimizu's Lemma 4f.1, concretely

Shimizu (arXiv:2009.10431, §4, Lemma 4f.1) proves that for a finite Galois extension `L/K` of number
fields the restriction

  `res_{L/K} : Hom_{cts}(Γ_K, ℤ_ℓ) → Hom_{cts}(Γ_L, ℤ_ℓ)^{G(L/K)}`

induced by the base-change map `π_{L/K} : Γ_L → Γ_K` is injective with finite cokernel.

The abstract injectivity statement — precomposition with an additive map whose cokernel is finite is
injective on the additive dual `Hom(-, ℤ_ℓ)` — is
`NK.Reconstruct.res_injective_of_finite_coker` (`Submission/Work/Reconstruct/resInjective.lean`),
and the finiteness of the cokernel of `π_{L/K} = gammaBaseChangeHom ℓ L : Γ_L → Γ_K` is
`NK.Reconstruct.finite_coker_gammaBaseChangeHom`
(`Submission/Work/Reconstruct/finite_coker_gammaBaseChangeHom.lean`): the base-change sequence

  `Γ_L --π_{L/K}--> Γ_K --proj_L--> ℓ-part(Gal(L/K)^{ab}) --> 1`

is exact, so `coker(π_{L/K}) ≅ ℓ-part(Gal(L/K)^{ab})` is finite.

This file records the resulting concrete statement
`NK.Reconstruct.res_gamma_injective`, the injectivity of Shimizu's `res_{L/K}` *before* taking
`G(L/K)`-invariants.  It is the form in which the reconstruction uses it: injectivity for the
restriction with its invariants target then follows immediately.

## Contents

* `finite_coker_toAdditive` — the finiteness of a cokernel is insensitive to the passage between
  multiplicative and additive notation (the underlying quotient types are definitionally equal);
* **`res_gamma_injective`** — the injectivity of Shimizu's `res_{L/K}` on the additive dual.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. I §1.6, Ch. X §10.3;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

/-- **The finiteness of a cokernel does not see the passage between multiplicative and additive
notation.**  If a group homomorphism `f : G →* H` has finite cokernel `H ⧸ f.range`, then its
additive form `MonoidHom.toAdditive f : Additive G →+ Additive H` has finite cokernel
`Additive H ⧸ (MonoidHom.toAdditive f).range`.  Both quotients are quotients of the same underlying
type (the type synonyms `Additive` are reducible) by logically identical relations — for
`x y : H`, `(-x) + y ∈ f.range` holds in the additive reading exactly when `x⁻¹ * y ∈ f.range` holds
in the multiplicative one — so the two `Finite` statements are definitionally equal. -/
theorem finite_coker_toAdditive {G H : Type*} [Group G] [Group H] (f : G →* H)
    (h : Finite (H ⧸ f.range)) : Finite (Additive H ⧸ (MonoidHom.toAdditive f).range) := h

/-- **The injectivity half of Shimizu's Lemma 4f.1, concretely.**  For a finite Galois level `L` of
`K'/K` and a prime `ℓ`, precomposition with the base-change map
`π_{L/K} = gammaBaseChangeHom ℓ L : Γ_L → Γ_K` is injective on the additive dual
`Hom(Γ_K, ℤ_ℓ)`.  This is Shimizu's `res_{L/K}` before taking `G(L/K)`-invariants; injectivity for
the restriction with its invariants target follows. -/
theorem res_gamma_injective {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] (L : FrobLevel K K') :
    Function.Injective (fun (φ : Additive (Gamma K K' ℓ) →+ PadicInt ℓ) =>
      φ.comp (gammaBaseChangeHom ℓ L).toAdditive) :=
  -- The cokernel of `π_{L/K}` is `coker(proj_L) ≅ ℓ-part(Gal(L/K)^{ab})`, hence finite
  -- (`finite_coker_gammaBaseChangeHom`), and precomposition with a map of finite cokernel is
  -- injective on the additive dual (`res_injective_of_finite_coker`).
  res_injective_of_finite_coker (gammaBaseChangeHom ℓ L).toAdditive
    (finite_coker_toAdditive (gammaBaseChangeHom ℓ L)
      (finite_coker_gammaBaseChangeHom ℓ L))

end NK.Reconstruct
