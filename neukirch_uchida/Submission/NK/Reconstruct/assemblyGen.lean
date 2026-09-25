import Submission.NK.Reconstruct.prop4f3
import Submission.NK.Reconstruct.lemma4f4_gen
import Submission.NK.Reconstruct.fourf5Gen
import Submission.NK.Reconstruct.thetaGammaTransport_gen
import Submission.NK.Reconstruct.exists_isomorphism_of_prop4f3_data

/-!
# Shimizu's Theorem 4.0 (the assembly) for arbitrary number fields

Shimizu, arXiv:2009.10431, §4: given

* finite number-field levels `K₁, K₂ ⊆ L` of a separable closure `Ω` of `ℚ`, with `L/ℚ` Galois,
* a **continuous** isomorphism `σ̄ : Γ_{K₁} ≅ Γ_{K₂}` of the torsion-free ℓ-adic abelianisations,
* a prime bijection `primeMap` preserving the rational prime (`hchar`) and matching the Frobenius
  elements (`hb`),
* a section `Θ : Gal(L/ℚ) → Ω ≃ₐ[ℚ] Ω` of the restriction map (`exists_ringEquiv_extends`),
* the Čebotarev input `hc`,
* the rank computation of Proposition 4f.5 (`Fourf5InputGen`, from the rank inputs of
  `NK.Reconstruct.fourf5Gen`) and a complex prime of `K₁.L`,

one has `K₁.L = θ⁻¹(K₂.L)` for some `θ = Θ τ`, whence `K₁.L ≃+* K₂.L`.

The two ingredients new in this file relative to `NK.Reconstruct.exists_isomorphism_of_prop4f3_data`
are

* the base fields `K₁, K₂` are `NumFieldIn ℚ Ω`, i.e. **arbitrary finite number-field levels** of
  `Ω/ℚ` (not necessarily Galois over `ℚ`) — this is what makes the theorem applicable to the level
  pairs `(L, levelMap ϕ L)` of the reconstruction step;
* the conclusion **exposes the field equality** `K₁.L = (Θ τ)⁻¹(K₂.L)`, which is what a caller needs
  in order to run the argument at several levels simultaneously (Shimizu's Theorem 4.0 uses the
  same `τ` for two different pairs and intersects the resulting fields).

The proof is the one of `exists_isomorphism_of_prop4f3_data`, with `lemma4f4_gen` (Lemma 4f.4 for
arbitrary base fields, `Submission/Work/Reconstruct/lemma4f4_gen.lean`) and
`thetaGammaTransport_gen` (the θ-transport for arbitrary base fields) in place of their
Galois-over-`ℚ` versions, and `Fourf5InputGen` (Proposition 4f.5 for arbitrary base fields) in place
of `Fourf5Input`.

## Contents

* **`NK.Reconstruct.exists_theta_of_prop4f3_data_gen`** — the assembly, with the field equality
  `K₁.L = (Θ τ)⁻¹(K₂.L)`;
* **`NK.Reconstruct.exists_isomorphism_of_prop4f3_data_gen`** — the assembly, with the conclusion
  `Nonempty (↥K₁.L ≃+* ↥K₂.L)`.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped NumberField Pointwise

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **Shimizu's Theorem 4.0 (assembly), with the field equality exposed.** -/
theorem exists_theta_of_prop4f3_data_gen
    (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (primeMap : NK.Chebotarev.PrimeIdeal ↥K₁.L ≃ NK.Chebotarev.PrimeIdeal ↥K₂.L)
    (hb : ∀ (𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L) (g₁ : Gal(Ω/↥K₁.L)) (g₂ : Gal(Ω/↥K₂.L)),
        IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ →
        σbar (galToGamma (K := ↥K₁.L) (K' := Ω) ℓ g₁) =
          galToGamma (K := ↥K₂.L) (K' := Ω) ℓ g₂)
    (hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L,
        Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal)
    (Θ : Gal(↥L.L/ℚ) → Ω ≃ₐ[ℚ] Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ L.L ↔ Θ τ x ∈ L.L)
    (hΘres : ∀ τ (x : ↥L.L), Θ τ (x : Ω) = (τ x : Ω))
    (hcomplex : ∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v)
    (hc : ChebotarevInput ℚ Ω) (h45 : Fourf5InputGen Ω ℓ) :
    ∃ τ : Gal(↥L.L/ℚ), K₁.L = K₂.L.map (Θ τ).symm.toAlgHom := by
  classical
  -- Step 1: the element `τ ∈ Gal(L/ℚ)` produced by Shimizu's Proposition 4f.3.
  obtain ⟨τ, hτ⟩ := prop4f3 K₁ K₂ L h₁ h₂ ℓ σbar hσbar primeMap hb hchar
    (fun τ' => (Θ τ' : Ω ≃+* Ω)) (fun τ' => hΘmem τ') (fun τ' x => hΘres τ' x) hc
  refine ⟨τ, ?_⟩
  -- Step 2: the `θ⁻¹`-image `M` of `K₂`, and the transport isomorphism `Ψ : Γ_M ≅ Γ_{K₂}`.
  set M : NumFieldIn ℚ Ω := K₂.map (Θ τ) with hMdef
  have hM : M.L = K₂.L.map (Θ τ).symm.toAlgHom := NumFieldIn.map_L K₂ (Θ τ)
  haveI : IsSepClosure ↥M.L Ω := hM ▸ isSepClosure_level (K₂.L.map (Θ τ).symm.toAlgHom)
  have hθL : ∀ x : Ω, x ∈ L.L ↔ (Θ τ) x ∈ L.L := hΘmem τ
  have hML : M.L ≤ L.L := by
    rw [hM]
    exact le_trans (IntermediateField.map_mono (Θ τ).symm.toAlgHom h₂)
      (map_symm_le_self L.L (Θ τ) hθL)
  obtain ⟨Ψ, hΨcont, hΨeq⟩ := thetaGammaTransport_gen K₂ (Θ τ) ℓ M hM L h₂ hML hθL
  -- Step 3: `σbar' := Ψ⁻¹ ∘ σbar`, and the reformulation of step 1.
  have hΨsymm_cont : Continuous ⇑(Ψ.symm : Gamma ↥K₂.L Ω ℓ →* Gamma ↥M.L Ω ℓ) :=
    continuous_symm_of_mulEquiv Ψ hΨcont
  let σbar' : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥M.L Ω ℓ := σbar.trans Ψ.symm
  have hσbar'cont : Continuous ⇑σbar' := hΨsymm_cont.comp hσbar
  have heq : ∀ γ : Gamma ↥L.L Ω ℓ,
      gammaHausMk (K := ↥M.L) (K' := Ω) ℓ (σbar' (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥M.L) (K' := Ω) ℓ (ambientPi M L hML ℓ γ) := by
    intro γ
    have hτγ := hτ γ
    have hΨeqγ : (ambientPi K₂ L h₂ ℓ) (tauStar L.L ℓ (Θ τ) hθL γ)
        = Ψ (ambientPi M L hML ℓ γ) := by
      have h1 := DFunLike.congr_fun hΨeq γ
      rwa [MonoidHom.comp_apply] at h1
    have hstep : gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
        (σbar (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ (Ψ (ambientPi M L hML ℓ γ)) := by
      rw [hτγ, hΨeqγ]
    have h3 := congrArg
      (gammaHausLift ℓ (Ψ.symm : Gamma ↥K₂.L Ω ℓ →* Gamma ↥M.L Ω ℓ) hΨsymm_cont) hstep
    rw [gammaHausLift_comp, gammaHausLift_comp] at h3
    simpa [σbar', MulEquiv.trans_apply] using h3
  -- Step 4: Lemma 4f.4 for the pair `(K₁, M)`, then join with `L`.
  have h4f4 := lemma4f4_gen K₁ M L h₁ hML ℓ σbar' hσbar'cont heq
  have hsup : (levelInfinityOf K₁ ℓ ⊔ L.L : IntermediateField ℚ Ω)
      = (L.L ⊔ levelInfinityOf M ℓ : IntermediateField ℚ Ω) := by
    calc (levelInfinityOf K₁ ℓ ⊔ L.L : IntermediateField ℚ Ω)
        = (levelInfinityOf K₁ ℓ ⊔ M.L) ⊔ L.L := by rw [sup_assoc, sup_eq_right.mpr hML]
      _ = (K₁.L ⊔ levelInfinityOf M ℓ) ⊔ L.L := by rw [h4f4]
      _ = L.L ⊔ levelInfinityOf M ℓ := by
          rw [sup_assoc, sup_comm (levelInfinityOf M ℓ) L.L, ← sup_assoc,
            sup_eq_right.mpr h₁]
  -- Step 5: Proposition 4f.5 identifies `M` with `K₁`.
  have hKM : K₁.L = M.L := h45 K₁ M L h₁ hML hsup hcomplex
  exact hKM.trans hM

/-- **Shimizu's Theorem 4.0 (assembly) for arbitrary number fields**: the two base fields are
isomorphic. -/
theorem exists_isomorphism_of_prop4f3_data_gen
    (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (primeMap : NK.Chebotarev.PrimeIdeal ↥K₁.L ≃ NK.Chebotarev.PrimeIdeal ↥K₂.L)
    (hb : ∀ (𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L) (g₁ : Gal(Ω/↥K₁.L)) (g₂ : Gal(Ω/↥K₂.L)),
        IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ →
        σbar (galToGamma (K := ↥K₁.L) (K' := Ω) ℓ g₁) =
          galToGamma (K := ↥K₂.L) (K' := Ω) ℓ g₂)
    (hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L,
        Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal)
    (Θ : Gal(↥L.L/ℚ) → Ω ≃ₐ[ℚ] Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ L.L ↔ Θ τ x ∈ L.L)
    (hΘres : ∀ τ (x : ↥L.L), Θ τ (x : Ω) = (τ x : Ω))
    (hcomplex : ∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v)
    (hc : ChebotarevInput ℚ Ω) (h45 : Fourf5InputGen Ω ℓ) :
    ∃ τ : Gal(↥L.L/ℚ), Nonempty (↥K₁.L ≃+* ↥K₂.L) := by
  obtain ⟨τ, hf⟩ := exists_theta_of_prop4f3_data_gen K₁ K₂ L h₁ h₂ ℓ σbar hσbar primeMap hb
    hchar Θ hΘmem hΘres hcomplex hc h45
  refine ⟨τ, ?_⟩
  -- Pin the `Algebra ℚ` structures on the two subtypes, so that the `AlgEquiv` produced by
  -- `IntermediateField.equivMap` matches the instances of its declaration.
  letI : Algebra ℚ ↥K₂.L := IntermediateField.algebra' K₂.L
  letI : Algebra ℚ ↥(K₂.L.map (Θ τ).symm.toAlgHom) :=
    IntermediateField.algebra' (K₂.L.map (Θ τ).symm.toAlgHom)
  rw [hf]
  exact ⟨(IntermediateField.equivMap K₂.L (Θ τ).symm.toAlgHom).symm.toRingEquiv⟩

end NK.Reconstruct
