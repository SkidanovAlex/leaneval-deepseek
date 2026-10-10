import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Submission.NK.Reconstruct.NumFieldIn
import Submission.NK.Reconstruct.exists_algEquiv_primeTransport_eq
import Submission.NK.Reconstruct.splitFrobeniusBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transporting a prime of a large level onto a prescribed prime of a subfield

This file proves `NK.Reconstruct.exists_galois_primeTransport_under_eq`: given two normal
number-field levels `K₁`, `K₂` of `Ω/ℚ` and a prime correspondence
`primeMap : PrimeIdeal K₁ ≃ PrimeIdeal K₂` which preserves the rational prime below
(`Ideal.under ℤ`), then for the prime `𝔭` of any larger normal level `L` (with `K₂.L ≤ L.L`),
some `τ ∈ Gal(L/ℚ)` transports `𝔭` to a prime whose contraction to `K₂` is the image under
`primeMap` of the contraction of `𝔭` to `K₁`.

The mathematical content is the transitivity of the Galois action on the primes above a fixed
rational prime (`NK.Reconstruct.exists_algEquiv_primeTransport_eq`), applied after lifting the
prescribed prime of `𝓞 K₂` to a prime of `𝓞 L` lying over it.  The hypothesis `hchar` — that
`primeMap` preserves the rational prime below — is exactly what makes the lifted prime lie over
the same rational prime as `𝔭`.

The auxiliary lemma `under_rat_eq_of_under_int_eq` converts an equality of contractions to `ℤ`
(where the hypothesis `hchar` lives) into an equality of contractions to `𝓞 ℚ` (the base field
used by the transitivity statement); it uses that `ℤ → 𝓞 ℚ` is surjective.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField


/-- **Contraction to `ℤ` determines contraction to `𝓞 ℚ`.**  If two ideals of the rings of
integers of two number fields have the same contraction to `ℤ`, then they have the same
contraction to `𝓞 ℚ`.  Indeed `ℤ → 𝓞 ℚ` is surjective, so contraction along it is injective on
ideals, and by `Ideal.under_under` the contraction to `ℤ` factors through `𝓞 ℚ`. -/
theorem under_rat_eq_of_under_int_eq {K₁ K₂ : Type*} [Field K₁] [Field K₂] [NumberField K₁]
    [NumberField K₂] (J : Ideal (𝓞 K₁)) (J' : Ideal (𝓞 K₂))
    (h : Ideal.under ℤ J = Ideal.under ℤ J') :
    Ideal.under (𝓞 ℚ) J = Ideal.under (𝓞 ℚ) J' := by
  refine Ideal.ext (fun x => ?_)
  obtain ⟨n, rfl⟩ := Rat.int_algebraMap_surjective (𝓞 ℚ) x
  rw [Ideal.mem_under, Ideal.mem_under]
  rw [← IsScalarTower.algebraMap_apply ℤ (𝓞 ℚ) (𝓞 K₁) n,
      ← IsScalarTower.algebraMap_apply ℤ (𝓞 ℚ) (𝓞 K₂) n]
  rw [← Ideal.mem_under (A := ℤ) (P := J) (x := n),
      ← Ideal.mem_under (A := ℤ) (P := J') (x := n), h]

theorem exists_galois_primeTransport_under_eq {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K₁ K₂ : NK.Reconstruct.NumFieldIn ℚ Ω) (L : NK.Reconstruct.FrobLevel ℚ Ω)
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [Algebra ↥K₁.L ↥L.L] [Algebra ↥K₂.L ↥L.L] [FiniteDimensional ↥K₂.L ↥L.L]
    [IsScalarTower ↥K₁.L ↥L.L Ω] [IsScalarTower ↥K₂.L ↥L.L Ω]
    (primeMap : NK.Chebotarev.PrimeIdeal ↥K₁.L ≃ NK.Chebotarev.PrimeIdeal ↥K₂.L)
    (hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L,
        Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal)
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) :
    ∃ τ : Gal(↥L.L/ℚ),
      (NK.Reconstruct.primeTransport (τ : ↥L.L ≃+* ↥L.L) 𝔭).under
          (NumberField.RingOfIntegers ↥K₂.L)
        = primeMap (𝔭.under (NumberField.RingOfIntegers ↥K₁.L)) := by
  classical
  -- the prime of `𝓞 K₁` below `𝔭`, and its prescribed image under `primeMap`
  set q' : NK.Chebotarev.PrimeIdeal ↥K₁.L := 𝔭.under (𝓞 ↥K₁.L) with hq'
  -- lift the prescribed prime of `𝓞 K₂` to a prime `P` of `𝓞 L` lying over it
  obtain ⟨P, hPq⟩ : ∃ P : NK.Chebotarev.PrimeIdeal ↥L.L,
      P.asIdeal.LiesOver (primeMap q').asIdeal := by
    obtain ⟨P⟩ := (inferInstance : Nonempty ((primeMap q').asIdeal.primesOver (𝓞 ↥L.L)))
    exact ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver (primeMap q').ne_bot P.2⟩, P.2.2⟩
  -- `P` and `𝔭` lie over the same prime of `𝓞 ℚ`
  have hPrat : Ideal.under (𝓞 ℚ) P.asIdeal = Ideal.under (𝓞 ℚ) (primeMap q').asIdeal := by
    rw [hPq.over, Ideal.under_under (A := 𝓞 ℚ) (B := 𝓞 ↥K₂.L) (C := 𝓞 ↥L.L) P.asIdeal]
  have hqrat : Ideal.under (𝓞 ℚ) (primeMap q').asIdeal = Ideal.under (𝓞 ℚ) q'.asIdeal :=
    under_rat_eq_of_under_int_eq _ _ (hchar q')
  have hq'rat : Ideal.under (𝓞 ℚ) q'.asIdeal = Ideal.under (𝓞 ℚ) 𝔭.asIdeal :=
    Ideal.under_under (A := 𝓞 ℚ) (B := 𝓞 ↥K₁.L) (C := 𝓞 ↥L.L) 𝔭.asIdeal
  set p : NK.Chebotarev.PrimeIdeal ℚ := 𝔭.under (𝓞 ℚ) with hp
  have hp_asIdeal : p.asIdeal = Ideal.under (𝓞 ℚ) 𝔭.asIdeal := rfl
  have hPp : P.asIdeal.LiesOver p.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    rw [hp_asIdeal, hPrat, hqrat, hq'rat]
  have h𝔭p : 𝔭.asIdeal.LiesOver p.asIdeal := Ideal.LiesOver.mk (by rw [hp_asIdeal])
  -- `𝓞 L` is normal over `ℚ`, so the Galois group is transitive on the primes above `p`;
  -- the instance `FrobLevel.normal` lives at the `Algebra ℚ L.L` structure of the
  -- intermediate field, which we identify with the canonical `ℚ`-algebra structure of a
  -- division ring of characteristic zero used by the transitivity statement.
  have hAlg : L.L.algebra' = (DivisionRing.toRatAlgebra : Algebra ℚ ↥L.L) :=
    Subsingleton.elim _ _
  haveI hN : Normal ℚ ↥L.L := hAlg ▸ L.normal
  obtain ⟨τ, hτ⟩ := NK.Reconstruct.exists_algEquiv_primeTransport_eq (L := L.L) h𝔭p hPp
  exact ⟨τ, by rw [hτ]; exact IsDedekindDomain.HeightOneSpectrum.ext hPq.over.symm⟩

end NK.Reconstruct
