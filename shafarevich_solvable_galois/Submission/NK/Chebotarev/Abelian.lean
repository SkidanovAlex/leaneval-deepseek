import Mathlib.NumberTheory.NumberField.DirichletDensity
import Submission.NK.Chebotarev.CyclotomicIntermediateFieldDensity
import Submission.NK.Chebotarev.IsFrobAtPrimeAlgEquiv
import Submission.NK.Chebotarev.KroneckerWeber
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Čebotarev for abelian extensions of `ℚ`

Assuming the Kronecker–Weber theorem over `ℚ` (as the explicit `Prop`
`NK.Chebotarev.KroneckerWeber`), Čebotarev's density theorem holds for every abelian extension
of `ℚ`: for `L/ℚ` finite abelian and `σ : Gal(L/ℚ)`, the rational primes whose Frobenius is `σ`
have Dirichlet density `1/[L:ℚ]`.

The reduction is the one described in the plan: `L` is realised as an intermediate field `E` of a
cyclotomic field `F = ℚ(ζ_n)`; the cyclotomic case is `CyclotomicFrobDensity` (density `1/φ(n)` on
each `σ ∈ Gal(F/ℚ)`, via Dirichlet's theorem on primes in arithmetic progressions); the restriction
homomorphism `Gal(F/ℚ) ↠ Gal(E/ℚ)` (`AlgEquiv.restrictNormalHom`) has fibres of size `[F:E]`, and
`IsFrobAtRestrictNormalHom` identifies the Frobenius of `E` with the restriction of the Frobenius
of `F`; disjoint additivity of the density over the fibre
(`HasDirichletDensityIUnionFinset`) and insensitivity to the finitely many ramified primes
(`HasDirichletDensitySensitivity`) give `CyclotomicIntermediateFieldDensity` for `E`; finally
`IsFrobAtPrimeAlgEquiv` transports the statement from `E` to the abstract field `L`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.Chebotarev

/-- **Čebotarev's density theorem for abelian extensions of `ℚ`, from Kronecker–Weber.**

For a finite abelian extension `L/ℚ` and `σ ∈ Gal(L/ℚ)`, the set of rational primes whose
Frobenius is `σ` has Dirichlet density `1/[L:ℚ]`. -/
theorem abelianChebotarev_of_kroneckerWeber (hKW : KroneckerWeber.{u})
    {L : Type u} [Field L] [NumberField L] [IsGalois ℚ L]
    (hcomm : ∀ a b : Gal(L/ℚ), a * b = b * a) (σ : Gal(L/ℚ)) :
    NumberField.Set.HasDirichletDensity
      {p : PrimeIdeal ℚ | IsFrobAtPrime (K := ℚ) (L := L) p σ}
      (1 / (Module.finrank ℚ L : ℝ)) := by
  obtain ⟨n, hn, ⟨M⟩⟩ := hKW (L := L) hcomm
  haveI : NeZero n := ⟨hn.ne'⟩
  letI := M.fieldF
  letI := M.numberFieldF
  letI := M.cyclotomicF
  letI := M.galoisE
  -- `Gal(E/ℚ)` is abelian, because it is isomorphic to `Gal(L/ℚ)` through the `ℚ`-algebra
  -- isomorphism `M.equiv`
  have hcommE : ∀ a b : Gal(↥M.E/ℚ), a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := (AlgEquiv.autCongr M.equiv).surjective a
    obtain ⟨b', rfl⟩ := (AlgEquiv.autCongr M.equiv).surjective b
    rw [← map_mul, ← map_mul, hcomm a' b']
  -- the cyclotomic Čebotarev theorem at the intermediate field `E`
  have hE := CyclotomicIntermediateFieldDensity (n := n) (F := M.F) M.E hcommE
    (M.equiv.symm.trans (σ.trans M.equiv))
  -- the sets agree under the isomorphism `L ≃ₐ[ℚ] E`
  have hset : {p : PrimeIdeal ℚ |
        IsFrobAtPrime (K := ℚ) (L := ↥M.E) p
          (M.equiv.symm.trans (σ.trans M.equiv))}
      = {p : PrimeIdeal ℚ | IsFrobAtPrime (K := ℚ) (L := L) p σ} := by
    ext p
    exact (IsFrobAtPrimeAlgEquiv M.equiv σ p).symm
  rw [hset] at hE
  rwa [show Module.finrank ℚ ↥M.E = Module.finrank ℚ L from
    M.equiv.toLinearEquiv.finrank_eq.symm] at hE

end NK.Chebotarev
