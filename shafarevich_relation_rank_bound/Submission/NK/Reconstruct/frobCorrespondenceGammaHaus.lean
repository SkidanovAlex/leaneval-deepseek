import Mathlib
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Reconstruct.galToGamma
import Submission.NK.Reconstruct.gammaHaus
import Submission.NK.Chebotarev.Basic
import Submission.NK.Reconstruct.frobeniusCorrespondence_of_place
import Submission.NK.Reconstruct.exists_gammaEquivOfPhi
import Submission.NK.ResidueFrob.primeOfLevel_liesOver
import Submission.NK.Reconstruct.frobUniquenessAwayFromL

namespace NK.Reconstruct

open scoped Pointwise

/-! ## The mathematical content of the target, and its single missing input

The target statement is `gammaHausMk (σbar (galToGamma g₁)) = gammaHausMk (galToGamma g₂)`.
Since `hσbar` identifies `σbar ∘ galToGamma` with `galToGamma ∘ ψ`, the left-hand side is
`gammaHausMk (galToGamma (ψ g₁))`, and by `isFrobElementAt_primeMap` below the element `ψ g₁` is a
Frobenius element at `a.primeMap 𝔭`.  The statement is therefore exactly:

> two Frobenius elements at one and the same prime of `K₂`, of residue characteristic `p ≠ ℓ`, have
> the same image in the torsion-free quotient `Γ_{K₂}^{tf}`;

i.e. the **well-definedness of the ℓ-adic Frobenius `Frob_𝔮 ∈ Γ_K^{tf}` for `𝔮 ∤ ℓ`**
(Shimizu, arXiv:2009.10431, §4, immediately before Lemma 4f.1; CoNF Ch. X §10.3).  That is the
content of the hypothesised lemma `NK.Reconstruct.frobUniquenessAwayFromL`, to which the proof
below reduces, and whose own mathematical content — the classical structure of the tame inertia
(NSW (7.5.7) Corollary, (7.5.11), (12.1.8); Iwasawa, *On Galois groups of local fields*) — is
recorded in this workspace as a *named input* (`NK.LocalTame.TameData`,
`NK.LocalStructure.TameCore`, `NK.LocalStructure.TameFrobeniusCore`), never as a theorem; see
`Submission/Work/LocalStructure/README.md`.

Everything else is proved here:
* `isFrobElementAt_primeMap` — the σ-free Frobenius correspondence (a) + (b) transfer Frobenius
  elements along `ψ`; note that this uses no uniqueness statement, the coincidence of the two
  Frobenius elements at the corresponding prime being the extra input above.
* `frobCorrespondenceGammaHaus` — the target, from that input. -/

variable {K₁ K₂ Ω : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂] [Field Ω]
  [Algebra K₁ Ω] [Algebra K₂ Ω] [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]

/-- **The σ-free Frobenius correspondence transfers Frobenius elements along `ψ`.** -/
theorem isFrobElementAt_primeMap
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ)
    (a : LocalCorrespondence ψ) (b : FrobeniusCorrespondencePlace ψ hψ a)
    (𝔭 : NK.Chebotarev.PrimeIdeal K₁) (g : Gal(Ω/K₁)) (hg : IsFrobElementAt 𝔭 g) :
    IsFrobElementAt (a.primeMap 𝔭) (ψ g) := by
  intro M _hMfd _hMn _hMnf
  have hsymm : IsHomeomorph (⇑ψ.symm : Gal(Ω/K₂) → Gal(Ω/K₁)) :=
    Submission.NeukirchUchida.isHomeomorph_symm ψ hψ
  let L : IntermediateField K₁ Ω := levelMap ψ.symm M
  haveI hLfd : FiniteDimensional K₁ L := finiteDimensional_levelMap hsymm M
  haveI hLn : Normal K₁ L := normal_levelMap hsymm M
  haveI hLnf : NumberField ↥L := numberField_levelMap hsymm M
  have hlevel : levelMap ψ L = M := levelMap_levelMap_symm' ψ hψ M
  haveI hfdc : FiniteDimensional K₂ (levelMap ψ L) := by rw [hlevel]; infer_instance
  haveI hnc : Normal K₂ (levelMap ψ L) := by rw [hlevel]; infer_instance
  haveI hnfc : NumberField ↥(levelMap ψ L) := by rw [hlevel]; infer_instance
  obtain ⟨P, hP, hfrob⟩ := hg L
  obtain ⟨A, hAcomap, hAval⟩ := exists_place_over_prime (K := K₁) (K' := Ω) L 𝔭 P hP
  have hAne : A.comap (algebraMap K₁ Ω) ≠ ⊤ := by
    rw [hAval]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔭
  let A' : FinitePlaceOf K₁ Ω := ⟨A, hAne⟩
  have hAL : A.comap (algebraMap ↥L Ω) ≠ ⊤ := comap_level_ne_top A'.2 L
  have hprime : primeOfLevel A L hAL = P := primeOfLevel_eq_of_comap_eq L hAcomap hAL
  have hb : NK.Chebotarev.IsFrobAt
      (primeOfLevel (a.placeMap A').1 (levelMap ψ L)
        (comap_level_ne_top (a.placeMap A').2 (levelMap ψ L)))
      (AlgEquiv.restrictNormalHom (levelMap ψ L) (ψ g)) :=
    b L A' g (by rw [hprime]; exact hfrob)
  have hbM : NK.Chebotarev.IsFrobAt
      (primeOfLevel (a.placeMap A').1 M (comap_level_ne_top (a.placeMap A').2 M))
      (AlgEquiv.restrictNormalHom M (ψ g)) :=
    (isFrobAt_primeOfLevel_of_eq hlevel (a.placeMap A').1 (a.placeMap A').2 (ψ g)).mp hb
  refine ⟨primeOfLevel (a.placeMap A').1 M (comap_level_ne_top (a.placeMap A').2 M), ?_, hbM⟩
  have hprimeA : Submission.NeukirchUchida.primeOf A'.1 A'.2 = 𝔭 := by
    refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K₁) ?_
    rw [← Submission.NeukirchUchida.primeOf_spec A'.1 A'.2]
    exact hAval
  have hlies := NK.ResidueFrob.primeOfLevel_liesOver
    (A := (⟨(a.placeMap A').1, (a.placeMap A').2⟩ : NK.FrobeniusBridge.FinitePlaceOf K₂ Ω)) M
  rw [← a.primeMap_spec A'] at hlies
  rw [hprimeA] at hlies
  exact hlies

/-- **The target statement, in the form in which it is provable here**: the conclusion of
`frobCorrespondenceGammaHaus`, with the classical well-definedness of the ℓ-adic Frobenius at the
prime `a.primeMap 𝔭` of `K₂` (residue characteristic `p ≠ ℓ`) supplied as the hypothesis
`hunique` — i.e. any two Frobenius elements at that prime have the same image in `Γ_{K₂}^{tf}`
(Shimizu, arXiv:2009.10431, §4, before Lemma 4f.1; CoNF Ch. X §10.3).

See `NK.Reconstruct.frobUniquenessAwayFromL` for the (not unconditionally provable in this
workspace) statement that would discharge `hunique`. -/
theorem frobCorrespondenceGammaHaus_of_unique {K₁ : Type*} [Field K₁] [NumberField K₁]
    {K₂ : Type*} [Field K₂] [NumberField K₂] {Ω : Type*} [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω]
    [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime]
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ)
    (a : NK.Reconstruct.LocalCorrespondence ψ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ψ hψ a)
    (σbar : NK.Reconstruct.Gamma K₁ Ω ℓ ≃* NK.Reconstruct.Gamma K₂ Ω ℓ)
    (hσbar : ∀ g : Gal(Ω/K₁), σbar (NK.Reconstruct.galToGamma (K := K₁) (K' := Ω) ℓ g) =
      NK.Reconstruct.galToGamma (K := K₂) (K' := Ω) ℓ (ψ g))
    (𝔭 : NK.Chebotarev.PrimeIdeal K₁)
    (hres : CharP (NumberField.RingOfIntegers K₁ ⧸ 𝔭.asIdeal) p) (hne : p ≠ ℓ)
    (hunique : ∀ g g' : Gal(Ω/K₂), NK.Reconstruct.IsFrobElementAt (a.primeMap 𝔭) g →
      NK.Reconstruct.IsFrobElementAt (a.primeMap 𝔭) g' →
      NK.Reconstruct.gammaHausMk (K := K₂) (K' := Ω) ℓ
          (NK.Reconstruct.galToGamma (K := K₂) (K' := Ω) ℓ g) =
        NK.Reconstruct.gammaHausMk (K := K₂) (K' := Ω) ℓ
          (NK.Reconstruct.galToGamma (K := K₂) (K' := Ω) ℓ g'))
    (g₁ : Gal(Ω/K₁)) (g₂ : Gal(Ω/K₂))
    (hg₁ : NK.Reconstruct.IsFrobElementAt 𝔭 g₁)
    (hg₂ : NK.Reconstruct.IsFrobElementAt (a.primeMap 𝔭) g₂) :
    NK.Reconstruct.gammaHausMk (K := K₂) (K' := Ω) ℓ
        (σbar (NK.Reconstruct.galToGamma (K := K₁) (K' := Ω) ℓ g₁))
      = NK.Reconstruct.gammaHausMk (K := K₂) (K' := Ω) ℓ
        (NK.Reconstruct.galToGamma (K := K₂) (K' := Ω) ℓ g₂) := by
  -- `σbar` is the isomorphism induced by `ψ`
  rw [hσbar g₁]
  -- `ψ g₁` is a Frobenius element at the corresponding prime
  have hψg₁ : NK.Reconstruct.IsFrobElementAt (a.primeMap 𝔭) (ψ g₁) :=
    isFrobElementAt_primeMap ψ hψ a b 𝔭 g₁ hg₁
  -- the uniqueness of the ℓ-adic Frobenius at that prime, supplied as a hypothesis
  exact hunique (ψ g₁) g₂ hψg₁ hg₂

/-- **The ℓ-adic Frobenius correspondence in the torsion-free quotient.** -/
theorem frobCorrespondenceGammaHaus {K₁ : Type*} [Field K₁] [NumberField K₁] {K₂ : Type*} [Field K₂]
    [NumberField K₂] {Ω : Type*} [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω]
    [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime]
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ)
    (a : NK.Reconstruct.LocalCorrespondence ψ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ψ hψ a)
    (σbar : NK.Reconstruct.Gamma K₁ Ω ℓ ≃* NK.Reconstruct.Gamma K₂ Ω ℓ)
    (hσbar : ∀ g : Gal(Ω/K₁), σbar (NK.Reconstruct.galToGamma (K := K₁) (K' := Ω) ℓ g) =
      NK.Reconstruct.galToGamma (K := K₂) (K' := Ω) ℓ (ψ g))
    (𝔭 : NK.Chebotarev.PrimeIdeal K₁)
    (hres : CharP (NumberField.RingOfIntegers K₁ ⧸ 𝔭.asIdeal) p) (hne : p ≠ ℓ)
    (g₁ : Gal(Ω/K₁)) (g₂ : Gal(Ω/K₂))
    (hg₁ : NK.Reconstruct.IsFrobElementAt 𝔭 g₁)
    (hg₂ : NK.Reconstruct.IsFrobElementAt (a.primeMap 𝔭) g₂) :
    NK.Reconstruct.gammaHausMk (K := K₂) (K' := Ω) ℓ
        (σbar (NK.Reconstruct.galToGamma (K := K₁) (K' := Ω) ℓ g₁))
      = NK.Reconstruct.gammaHausMk (K := K₂) (K' := Ω) ℓ
        (NK.Reconstruct.galToGamma (K := K₂) (K' := Ω) ℓ g₂) := by
  -- the prime of `K₂` corresponding to `𝔭` has residue characteristic `p`
  obtain ⟨A, hAval⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
      (K := K₁) (K' := Ω) 𝔭
  have hAne : A.comap (algebraMap K₁ Ω) ≠ ⊤ := by
    rw [hAval]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔭
  let A' : FinitePlaceOf K₁ Ω := ⟨A, hAne⟩
  have hprimeA : Submission.NeukirchUchida.primeOf A'.1 A'.2 = 𝔭 := by
    refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K₁) ?_
    rw [← Submission.NeukirchUchida.primeOf_spec A'.1 A'.2]
    exact hAval
  have hres' : CharP (NumberField.RingOfIntegers K₂ ⧸ (a.primeMap 𝔭).asIdeal) p := by
    have h1 : CharP (NumberField.RingOfIntegers K₁ ⧸
        (Submission.NeukirchUchida.primeOf A'.1 A'.2).asIdeal) p := by
      rw [hprimeA]
      exact hres
    have h2 := a.residueChar A' p h1
    rw [← a.primeMap_spec A'] at h2
    rw [hprimeA] at h2
    exact h2
  -- the classical well-definedness of the ℓ-adic Frobenius at `a.primeMap 𝔭`
  -- (`NK.Reconstruct.frobUniquenessAwayFromL`) is the one input not available unconditionally
  -- in this workspace; with it the statement follows from the conditional form above
  exact frobCorrespondenceGammaHaus_of_unique ℓ p ψ hψ a b σbar hσbar 𝔭 hres hne
    (fun g g' hg hg' => frobUniquenessAwayFromL ℓ p (a.primeMap 𝔭) hres' hne g g' hg hg')
    g₁ g₂ hg₁ hg₂

end NK.Reconstruct
