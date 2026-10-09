import Mathlib
import Submission.NK.Chebotarev.FrobRestriction
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Prescribing the restriction of a Frobenius element, and its behaviour on a larger field

Let `K' / K` be a Galois extension of the number field `K` (possibly of infinite degree) and let
`L₀ ≤ M` be finite normal intermediate fields.  Given an arithmetic Frobenius element `τ₀` at a
prime `P₀` of `𝓞 L₀` above an unramified prime `p` of `𝓞 K`, there is `σ ∈ Gal(K'/K)` whose
restriction to `L₀` is `τ₀` and whose restriction to `M` is again a Frobenius element at `p`:

`∃ σ, σ|_L₀ = τ₀ ∧ IsFrobAtPrime p (σ|_M)`.

The proof is a two-step descent/lift:

* pick a prime `P` of `𝓞 M` above `P₀` (lying over theorem) and a Frobenius element `ρ` at `P`
  inside `Gal(M/K)`, which exists unconditionally (`exists_isFrobAt`);
* its restriction to `L₀` is a Frobenius element at `P ∩ 𝓞 L₀ = P₀`
  (`isFrobAt_restrictNormalHom_le`), so it equals `τ₀` by the *uniqueness* of the Frobenius at
  the unramified prime `P₀` (`IsFrobAt.eq_of_isFrobAt`);
* lift `ρ` to `Gal(K'/K)` along the surjection `Gal(K'/K) ↠ Gal(M/K)`
  (`AlgEquiv.restrictNormalHom_surjective`).

Note that `M` itself may well be ramified at `p`: the Frobenius element of `M` at a prime above
`p` is a coset of the inertia group, and the chosen coset is the one whose restriction to `L₀` is
`τ₀`.  Only the unramifiedness *in `L₀`* is used, and only to make `τ₀` unique.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Chebotarev

open IsDedekindDomain

theorem exists_restrictNormalHom_eq_and_isFrobAtPrime {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsGalois K K']
    (L₀ M : IntermediateField K K') (h : L₀ ≤ M)
    [FiniteDimensional K L₀] [Normal K L₀] [NumberField ↥L₀]
    [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    (p : NK.Chebotarev.PrimeIdeal K) (P₀ : NK.Chebotarev.PrimeIdeal ↥L₀) (τ₀ : Gal(↥L₀/K))
    (hP₀ : P₀.asIdeal.LiesOver p.asIdeal)
    (he₀ : P₀.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hτ₀ : NK.Chebotarev.IsFrobAt P₀ τ₀) :
    ∃ σ : Gal(K'/K), AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L₀ σ = τ₀ ∧
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥M) p
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M σ) := by
  -- The canonical `↥L₀`-algebra structure on `↥M`, and the two towers it takes part in.
  letI : Algebra ↥L₀ ↥M := (Subsemiring.inclusion h).toAlgebra
  haveI : IsScalarTower K ↥L₀ ↥M := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower ↥L₀ ↥M K' := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : FiniteDimensional ↥L₀ ↥M := Module.Finite.of_restrictScalars_finite K ↥L₀ ↥M
  -- Both `L₀` and `M` are Galois over `K` (normal and of characteristic zero).
  haveI : IsGalois K ↥L₀ := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- A prime of `𝓞 M` above `P₀`.
  obtain ⟨P, hP⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := ↥L₀) (L := ↥M) P₀
  have hPp : P.asIdeal.LiesOver p.asIdeal :=
    Ideal.LiesOver.mk (by rw [hP₀.over, hP.over, Ideal.under_under])
  -- A Frobenius element of `Gal(M/K)` at `P`.
  obtain ⟨ρ, hρ⟩ := exists_isFrobAt (K := K) (L := ↥M) p P hPp
  -- Its restriction to `L₀` is a Frobenius element at the prime of `𝓞 L₀` below `P`, i.e. `P₀`.
  have hrestrict : IsFrobAt (P.under (NumberField.RingOfIntegers ↥L₀))
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L₀ ρ) :=
    isFrobAt_restrictNormalHom_le (L := L₀) (M := M) (hLM := h) (P := P) (ρ := ρ) hρ
  have hunder : P.under (NumberField.RingOfIntegers ↥L₀) = P₀ :=
    IsDedekindDomain.HeightOneSpectrum.ext hP.over.symm
  -- Uniqueness of the Frobenius at the unramified prime `P₀` identifies it with `τ₀`.
  have heq : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L₀ ρ = τ₀ :=
    (IsFrobAt.eq_of_isFrobAt (K := K) (L := ↥L₀) (p := p) (P := P₀)
      hP₀ he₀ hτ₀ (hunder ▸ hrestrict)).symm
  -- Lift `ρ` to `Gal(K'/K)`.
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥M) K' ρ
  refine ⟨σ, ?_, ?_⟩
  · rw [restrictNormalHom_le_comp L₀ M h σ, hσ, heq]
  · exact ⟨P, hPp, by rw [hσ]; exact hρ⟩

end NK.Chebotarev
