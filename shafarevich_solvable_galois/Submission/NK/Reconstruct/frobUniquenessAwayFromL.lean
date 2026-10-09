import Mathlib
import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Reconstruct.galToGamma
import Submission.NK.Reconstruct.gammaHaus
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.IsFrobAtConj
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
import Submission.NK.Reconstruct.inertia_ellPart_pow_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Uniqueness of the ℓ-adic Frobenius element away from `ℓ`

For a number field `K`, a prime `𝔮` of `K` of residue characteristic `p ≠ ℓ` and two elements
`g, g' : Gal(K'/K)` which are Frobenius elements at `𝔮` in the sense of
`NK.Reconstruct.IsFrobElementAt` (i.e. at *every* finite normal level they are Frobenius at some
prime above `𝔮`), the images of `g` and `g'` in the Hausdorff torsion-free quotient `Γ_K^{tf}` of
the ℓ-adic abelianisation of `G_K` coincide:

`NK.Reconstruct.frobUniquenessAwayFromL`.

This is the statement that the ℓ-adic Frobenius element at a prime `𝔮 ∤ ℓ` is *well defined* in
`Γ_K^{tf}` (CoNF, Chapter X §10.3; Shimizu, arXiv:2009.10431, §4, where `Frob_𝔮` is used for every
`𝔮 ∤ ℓ`).

## Structure of the argument

1. Two Frobenius elements at a prime above `𝔮` differ by an element of the inertia subgroup
   (`AlgHom.IsArithFrobAt.mul_inv_mem_inertia`, Mathlib), hence, level by level, the difference
   `galToGamma (g * g'⁻¹)` has level components lying in the ℓ-primary part of the image of the
   inertia in the abelianisation of the level.
2. For `p ≠ ℓ`, the ℓ-primary part of the inertia at `𝔮` in the abelianisation of a finite Galois
   level is annihilated by `ℓ ^ v_ℓ(q - 1)`, `q = #(𝓞 K ⧸ 𝔮)`
   (`NK.Reconstruct.inertia_ellPart_pow_eq_one`): the wild inertia is pro-`p`, and the ℓ-primary
   part of the tame inertia is a quotient of `μ_{q-1}` (local class field theory; Neukirch, *p-adic
   fields*, or CoNF Chapter X §10.3).
3. Hence `galToGamma (g * g'⁻¹)` has finite order `ℓ ^ v_ℓ(q - 1)` in `Γ_K` (the exponent is
   independent of the level), so it is killed by the quotient map `Γ_K ↠ Γ_K^{tf}`
   (`NK.Reconstruct.gammaHausMk_eq_one_of_pow_eq_one`, since `ℤ_ℓ` is torsion free).
4. Therefore the images of `galToGamma g` and `galToGamma g'` agree in `Γ_K^{tf}`.

Steps 1, 3 and 4 (and the derivation of the level-wise bound for differences of Frobenius
elements from the inertia bound of step 2) are proved in this file; step 2 is proved in the
companion module `Submission.NK.Reconstruct.inertia_ellPart_pow_eq_one` (from the structure of
the tame inertia: the ℓ-primary part of the ramification index at `𝔮` divides `ℓ ^ v_ℓ(q - 1)`,
`NK.Reconstruct.padicValNat_ramificationIdx_le`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

/-! ## Torsion elements of `Γ_K` are invisible -/

section Torsion

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K']

/-- **A torsion element of `Γ_K` is killed by the quotient map `Γ_K ↠ Γ_K^{tf}`.**  Indeed every
continuous homomorphism out of a pro-`ℓ` group into the torsion-free group `ℤ_ℓ` kills torsion
elements, and `Γ_K^{tf}` is the quotient by the intersection of the kernels of all of them. -/
theorem gammaHausMk_eq_one_of_pow_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (x : Gamma K K' ℓ) {n : ℕ}
    (hn : n ≠ 0) (h : x ^ n = 1) : gammaHausMk K K' ℓ x = 1 := by
  rw [gammaHausMk_eq_one_iff]
  intro f
  have h1 : (f : Additive (Gamma K K' ℓ) →+ PadicInt ℓ) (Additive.ofMul (x ^ n)) = 0 := by
    rw [h, ofMul_one, map_zero]
  rw [ofMul_pow, map_nsmul, nsmul_eq_mul] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd h2 (Nat.cast_ne_zero.mpr hn)
  · exact h2

end Torsion

/-! ## The level-wise bound for differences of Frobenius elements -/

section Derive

/-- **The ℓ-primary class of the difference of two Frobenius elements at primes above `𝔮` is
annihilated by `ℓ ^ v_ℓ(q - 1)`**, derived from the corresponding statement for a single inertia
element (the hypothesis `hinertia`, supplied in the application by
`NK.Reconstruct.inertia_ellPart_pow_eq_one`).

The two Frobenius elements at primes `P, P'` above `𝔮` are made comparable by conjugating one of
them along an element of `Gal(L/K)` carrying `P'` to `P` (the Galois group acts transitively on
the primes above `𝔮`); conjugation is invisible in the abelianisation. -/
theorem frob_class_ellPart_pow_eq_one_of_inertia {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔮 : NK.Chebotarev.PrimeIdeal K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hinertia : ∀ (P : NK.Chebotarev.PrimeIdeal L) (_ : P.asIdeal.LiesOver 𝔮.asIdeal)
      (h : Gal(L/K)),
      (∀ x : NumberField.RingOfIntegers L,
        galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) h x - x ∈
          P.asIdeal) →
      (ellComp ℓ (Abelianization.of h)) ^
        (ℓ ^ padicValNat ℓ (Nat.card (NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) - 1)) = 1)
    (P P' : NK.Chebotarev.PrimeIdeal L) (hP : P.asIdeal.LiesOver 𝔮.asIdeal)
    (hP' : P'.asIdeal.LiesOver 𝔮.asIdeal) (σ σ' : Gal(L/K))
    (hσ : NK.Chebotarev.IsFrobAt P σ) (hσ' : NK.Chebotarev.IsFrobAt P' σ') :
    (ellComp ℓ (Abelianization.of (σ * σ'⁻¹))) ^
      (ℓ ^ padicValNat ℓ (Nat.card (NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) - 1)) = 1 := by
  -- transitivity of the Galois action on the primes above `𝔮`
  obtain ⟨g, hg⟩ := Ideal.exists_comap_galRestrict_eq (NumberField.RingOfIntegers K) K L
    (NumberField.RingOfIntegers L) (p := 𝔮.asIdeal) (P₁ := P'.asIdeal) (P₂ := P.asIdeal)
    ⟨P'.2, hP'⟩ ⟨P.2, hP⟩
  have hmap : Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) g :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) P.asIdeal =
        P'.asIdeal := by
    rw [← hg]
    exact Ideal.map_comap_of_surjective _ (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) g).surjective P'.asIdeal
  have hsmul : g • P = P' := IsDedekindDomain.HeightOneSpectrum.ext hmap
  have hgσ : NK.Chebotarev.IsFrobAt P' (g * σ * g⁻¹) := by
    rw [← hsmul]
    exact NK.Chebotarev.IsFrobAtConj hσ
  -- the difference lies in the inertia at `P'`
  letI act : MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  haveI hcomm : SMulCommClass Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    ⟨fun g a x => by
      change galRestrict (NumberField.RingOfIntegers K) K L
          (NumberField.RingOfIntegers L) g
          (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) a * x) =
        algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) a *
          galRestrict (NumberField.RingOfIntegers K) K L
            (NumberField.RingOfIntegers L) g x
      rw [map_mul, AlgEquiv.commutes]⟩
  have h1 : IsArithFrobAt (NumberField.RingOfIntegers K) (g * σ * g⁻¹) P'.asIdeal := hgσ
  have h2 : IsArithFrobAt (NumberField.RingOfIntegers K) σ' P'.asIdeal := hσ'
  have hm : (g * σ * g⁻¹) * σ'⁻¹ ∈ P'.asIdeal.inertia Gal(L/K) :=
    IsArithFrobAt.mul_inv_mem_inertia h1 h2
  have hh : ∀ x : NumberField.RingOfIntegers L,
      galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L)
        ((g * σ * g⁻¹) * σ'⁻¹) x - x ∈ P'.asIdeal := by
    intro x
    exact hm x
  have hD1 := hinertia P' hP' ((g * σ * g⁻¹) * σ'⁻¹) hh
  -- conjugation is invisible in the abelianisation
  have hconj : Abelianization.of (g * σ * g⁻¹) = Abelianization.of σ := by
    rw [map_mul, map_mul, map_inv]
    rw [mul_comm (Abelianization.of g) (Abelianization.of σ), mul_assoc, mul_inv_cancel, mul_one]
  have hab : Abelianization.of (σ * σ'⁻¹) =
      Abelianization.of ((g * σ * g⁻¹) * σ'⁻¹) := by
    rw [map_mul, map_inv, map_mul, map_inv, hconj]
  rw [hab]
  exact hD1

end Derive

/-! ## The reduction of the target to the level-wise bound -/

section Reduce

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsSepClosure K K']

/-- **The reduction of `NK.Reconstruct.frobUniquenessAwayFromL` to a level-wise bound**: if at
every finite normal level the images of two Frobenius elements at primes above `𝔮` have the same
ℓ-primary class up to the uniform exponent `ℓ ^ v_ℓ(q - 1)`, then the images of `galToGamma g` and
`galToGamma g'` in `Γ_K^{tf}` agree. -/
theorem frobUniquenessAwayFromL_of_frobBound (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime]
    (𝔮 : NK.Chebotarev.PrimeIdeal K)
    (hres : CharP (NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) p) (hne : p ≠ ℓ)
    (g g' : Gal(K'/K)) (hg : IsFrobElementAt 𝔮 g) (hg' : IsFrobElementAt 𝔮 g')
    (hbound : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
      [NumberField ↥L] [IsGalois K L]
      (P P' : NK.Chebotarev.PrimeIdeal ↥L) (hP : P.asIdeal.LiesOver 𝔮.asIdeal)
      (hP' : P'.asIdeal.LiesOver 𝔮.asIdeal) (σ σ' : Gal(↥L/K)),
      NK.Chebotarev.IsFrobAt P σ → NK.Chebotarev.IsFrobAt P' σ' →
      (ellComp ℓ (Abelianization.of (σ * σ'⁻¹))) ^
        (ℓ ^ padicValNat ℓ (Nat.card (NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) - 1)) = 1) :
    gammaHausMk (K := K) (K' := K') ℓ (galToGamma (K := K) (K' := K') ℓ g) =
      gammaHausMk (K := K) (K' := K') ℓ (galToGamma (K := K) (K' := K') ℓ g') := by
  have hNne : ℓ ^ padicValNat ℓ (Nat.card (NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) - 1) ≠ 0 :=
    pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  have hkey : (galToGamma (K := K) (K' := K') ℓ (g * g'⁻¹)) ^
      (ℓ ^ padicValNat ℓ (Nat.card (NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) - 1)) = 1 := by
    refine Gamma.ext fun L => ?_
    rw [map_pow, galToGamma_proj, map_one]
    obtain ⟨P, hP, hPfrob⟩ := hg L.L
    obtain ⟨P', hP', hP'frob⟩ := hg' L.L
    haveI : IsGalois K ↥L.L :=
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    have hB := hbound L.L P P' hP hP' (AlgEquiv.restrictNormalHom L.L g)
      (AlgEquiv.restrictNormalHom L.L g') hPfrob hP'frob
    have h1 : levelComponent ℓ L (g * g'⁻¹) =
        ellComp ℓ (Abelianization.of ((AlgEquiv.restrictNormalHom L.L g) *
          ((AlgEquiv.restrictNormalHom L.L g'))⁻¹)) := by
      simp only [levelComponent]
      rw [map_mul, map_inv]
    rw [h1]
    exact hB
  have hdiff : galToGamma (K := K) (K' := K') ℓ (g * g'⁻¹) =
      galToGamma (K := K) (K' := K') ℓ g * (galToGamma (K := K) (K' := K') ℓ g')⁻¹ := by
    rw [map_mul, map_inv]
  have hone : gammaHausMk (K := K) (K' := K') ℓ (galToGamma (K := K) (K' := K') ℓ g) *
      (gammaHausMk (K := K) (K' := K') ℓ (galToGamma (K := K) (K' := K') ℓ g'))⁻¹ = 1 := by
    rw [← map_inv, ← map_mul, ← hdiff, gammaHausMk_eq_one_of_pow_eq_one _ hNne hkey]
  exact mul_inv_eq_one.mp hone

end Reduce

/-! ## The requested statement -/

/-- **Uniqueness of the ℓ-adic Frobenius element away from `ℓ`**: two Frobenius elements at a prime
`𝔮` of residue characteristic `p ≠ ℓ` have the same image in `Γ_K^{tf}`. -/
theorem frobUniquenessAwayFromL {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime]
    (𝔮 : NK.Chebotarev.PrimeIdeal K)
    (hres : CharP (NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) p) (hne : p ≠ ℓ)
    (g g' : Gal(K'/K)) (hg : NK.Reconstruct.IsFrobElementAt 𝔮 g)
    (hg' : NK.Reconstruct.IsFrobElementAt 𝔮 g') :
    NK.Reconstruct.gammaHausMk (K := K) (K' := K') ℓ
        (NK.Reconstruct.galToGamma (K := K) (K' := K') ℓ g) =
      NK.Reconstruct.gammaHausMk (K := K) (K' := K') ℓ
        (NK.Reconstruct.galToGamma (K := K) (K' := K') ℓ g') :=
  frobUniquenessAwayFromL_of_frobBound ℓ p 𝔮 hres hne g g' hg hg'
    (fun L _ _ _ _ P P' hP hP' σ σ' hσ hσ' =>
      frob_class_ellPart_pow_eq_one_of_inertia 𝔮 ℓ
        (fun P hP h hh => inertia_ellPart_pow_eq_one 𝔮 P hP ℓ p hres hne h hh)
        P P' hP hP' σ σ' hσ hσ')

end NK.Reconstruct
