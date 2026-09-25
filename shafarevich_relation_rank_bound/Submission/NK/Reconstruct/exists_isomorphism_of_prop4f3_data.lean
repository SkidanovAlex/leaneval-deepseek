import Mathlib
import Submission.NK.Reconstruct.prop4f3
import Submission.NK.Reconstruct.fourf5Input
import Submission.NK.Reconstruct.lemma4f4
import Submission.NK.Reconstruct.thetaGammaTransport
import Submission.NK.Reconstruct.exists_thetaLevel

namespace NK.Reconstruct

open scoped NumberField

set_option maxHeartbeats 1600000

/-- **Continuity of the inverse of a continuous multiplicative equivalence.**  A continuous
multiplicative equivalence from a compact group to a Hausdorff group is a closed map, and the
inverse of a bijective closed map is continuous. -/
theorem continuous_symm_of_mulEquiv {G H : Type*} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] [CompactSpace G] [T2Space H] (e : G ≃* H) (he : Continuous ⇑e) :
    Continuous ⇑e.symm := by
  rw [continuous_iff_isClosed]
  intro s hs
  have h := he.isClosedMap s hs
  rwa [show ⇑e.symm ⁻¹' s = e '' s from ?_]
  ext y
  simp only [Set.mem_preimage, Set.mem_image]
  exact ⟨fun h => ⟨e.symm y, h, e.apply_symm_apply y⟩,
    fun ⟨x, hx, hxy⟩ => by rw [← hxy, MulEquiv.symm_apply_apply]; exact hx⟩

/-- If a `ℚ`-algebra automorphism `θ` of `Ω` preserves a level `L` as a set, then the level `L`
is stable under `θ.symm`. -/
theorem map_symm_le_self {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    (L : IntermediateField ℚ Ω) (θ : Ω ≃ₐ[ℚ] Ω) (hθ : ∀ x : Ω, x ∈ L ↔ θ x ∈ L) :
    L.map θ.symm.toAlgHom ≤ L := by
  rw [IntermediateField.map_le_iff_le_comap]
  intro x hx
  show θ.symm x ∈ L
  exact (hθ (θ.symm x)).mpr (by rw [AlgEquiv.apply_symm_apply]; exact hx)

/-- **Shimizu's Theorem 4.0 (assembly), modulo Proposition 4f.5.**  Let `Ω/ℚ` be Galois and
separably closed, `K₁, K₂ ⊆ L` finite Galois levels of `Ω/ℚ`, `ℓ` prime, `σbar : Γ_{K₁} ≃* Γ_{K₂}`
continuous, `primeMap` a prime bijection preserving the rational prime (`hchar`), `hb` the
Frobenius correspondence, `Θ` a section of `Gal(L/ℚ) ← (Ω ≃ₐ[ℚ] Ω)`, `hc` the Čebotarev input,
`hcomplex` a complex prime of `K₁` (required by Shimizu's Proposition 4f.5), and `h45` that
proposition (`NK.Reconstruct.Fourf5Input`).  Then `K₁` and `K₂` are isomorphic fields.

Plan (the Shimizu §4 assembly, all of whose ingredients are on disk):
1. `NK.Reconstruct.prop4f3` gives `τ ∈ Gal(L/ℚ)` with
   `∀ γ, gammaHausMk (σbar (π_{L/K₁} γ)) = gammaHausMk (π_{L/K₂} (τ^*(Θ τ) γ))`
   (`Θ τ` coerced from `Ω ≃ₐ[ℚ] Ω` to `Ω ≃+* Ω`).
2. Put `θ := Θ τ`; let `M` be the `θ⁻¹`-image of `K₂` from
   `NK.Reconstruct.exists_thetaLevel`, so `M.L = K₂.L.map θ.symm.toAlgHom ≤ L.L`.
   `NK.Reconstruct.thetaGammaTransport` gives a **continuous** `Ψ : Γ_M ≅ Γ_{K₂}` with
   `π_{L/K₂} ∘ τ^*_θ = Ψ ∘ π_{L/M}`.
3. With `σbar' := Ψ⁻¹ ∘ σbar : Γ_{K₁} ≅ Γ_M` (continuous), step 1 becomes
   `∀ γ, gammaHausMk (σbar' (π_{L/K₁} γ)) = gammaHausMk (π_{L/M} γ)`.
4. `NK.Reconstruct.lemma4f4` applied to the pair `(K₁, M)` gives
   `levelInfinityOf (NumFieldIn.ofFrobLevel K₁) ℓ ⊔ M.L = K₁.L ⊔ levelInfinityOf (NumFieldIn.ofFrobLevel M) ℓ`; joining with `L.L`
   (using `K₁.L, M.L ≤ L.L`) gives `levelInfinityOf (NumFieldIn.ofFrobLevel K₁) ℓ ⊔ L.L = L.L ⊔ levelInfinityOf (NumFieldIn.ofFrobLevel M) ℓ`,
   which is `h45`'s hypothesis shape.
5. `h45` (with `hcomplex`) gives `K₁.L = M.L = K₂.L.map θ.symm.toAlgHom`; then `θ` exhibits
   `↥K₁.L ≃+* ↥K₂.L` (via the `RingEquiv`/`AlgEquiv` induced by `θ.symm` on the mapped subfield,
   using `IntermediateField.equivMap`). -/
theorem exists_isomorphism_of_prop4f3_data {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω]
    (K₁ K₂ L : NK.Reconstruct.FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : NK.Reconstruct.Gamma ↥K₁.L Ω ℓ ≃* NK.Reconstruct.Gamma ↥K₂.L Ω ℓ)
    (hσbar : Continuous ⇑σbar)
    (primeMap : NK.Chebotarev.PrimeIdeal ↥K₁.L ≃ NK.Chebotarev.PrimeIdeal ↥K₂.L)
    (hb : ∀ (𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L) (g₁ : Gal(Ω/↥K₁.L)) (g₂ : Gal(Ω/↥K₂.L)),
        NK.Reconstruct.IsFrobElementAt 𝔭 g₁ → NK.Reconstruct.IsFrobElementAt (primeMap 𝔭) g₂ →
        σbar (galToGamma (K := ↥K₁.L) (K' := Ω) ℓ g₁) =
          galToGamma (K := ↥K₂.L) (K' := Ω) ℓ g₂)
    (hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L,
        Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal)
    (Θ : Gal(↥L.L/ℚ) → Ω ≃ₐ[ℚ] Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ L.L ↔ Θ τ x ∈ L.L)
    (hΘres : ∀ τ (x : ↥L.L), Θ τ (x : Ω) = (τ x : Ω))
    (hcomplex : ∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v)
    (hc : NK.Reconstruct.ChebotarevInput ℚ Ω) (h45 : NK.Reconstruct.Fourf5Input Ω ℓ) :
    ∃ τ : Gal(↥L.L/ℚ), Nonempty (↥K₁.L ≃+* ↥K₂.L) := by
  classical
  -- Step 1: the element `τ ∈ Gal(L/ℚ)` produced by Shimizu's Proposition 4f.3.
  obtain ⟨τ, hτ⟩ := prop4f3 (NumFieldIn.ofFrobLevel K₁) (NumFieldIn.ofFrobLevel K₂) L h₁ h₂ ℓ σbar hσbar primeMap hb hchar
    (fun τ' => (Θ τ' : Ω ≃+* Ω)) (fun τ' => hΘmem τ') (fun τ' x => hΘres τ' x) hc
  refine ⟨τ, ?_⟩
  -- Step 2: the `θ⁻¹`-image `M` of `K₂`, and the transport isomorphism `Ψ : Γ_M ≅ Γ_{K₂}`.
  obtain ⟨M, hM, hMsep⟩ := exists_thetaLevel K₂ (Θ τ)
  haveI : IsSepClosure ↥M.L Ω := hMsep
  have hθL : ∀ x : Ω, x ∈ L.L ↔ (Θ τ) x ∈ L.L := hΘmem τ
  have hML : M.L ≤ L.L := by
    rw [hM]
    exact le_trans (IntermediateField.map_mono (Θ τ).symm.toAlgHom h₂)
      (map_symm_le_self L.L (Θ τ) hθL)
  obtain ⟨Ψ, hΨcont, hΨeq⟩ := thetaGammaTransport K₂ (Θ τ) ℓ M hM L h₂ hML hθL
  -- Step 3: `σbar' := Ψ⁻¹ ∘ σbar`, and the reformulation of step 1.
  have hΨsymm_cont : Continuous ⇑(Ψ.symm : Gamma ↥K₂.L Ω ℓ →* Gamma ↥M.L Ω ℓ) :=
    continuous_symm_of_mulEquiv Ψ hΨcont
  let σbar' : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥M.L Ω ℓ := σbar.trans Ψ.symm
  have hσbar'cont : Continuous ⇑σbar' := hΨsymm_cont.comp hσbar
  have heq : ∀ γ : Gamma ↥L.L Ω ℓ,
      gammaHausMk (K := ↥M.L) (K' := Ω) ℓ (σbar' (ambientPi (NumFieldIn.ofFrobLevel K₁) L h₁ ℓ γ))
        = gammaHausMk (K := ↥M.L) (K' := Ω) ℓ (ambientPi (NumFieldIn.ofFrobLevel M) L hML ℓ γ) := by
    intro γ
    -- the identity of Proposition 4f.3 at `γ`
    have hτγ := hτ γ
    -- the transport identity of `thetaGammaTransport` at `γ`
    have hΨeqγ : (ambientPi (NumFieldIn.ofFrobLevel K₂) L h₂ ℓ) (tauStar L.L ℓ (Θ τ) hθL γ)
        = Ψ (ambientPi (NumFieldIn.ofFrobLevel M) L hML ℓ γ) := by
      have h1 := DFunLike.congr_fun hΨeq γ
      rwa [MonoidHom.comp_apply] at h1
    have hstep : gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ (σbar (ambientPi (NumFieldIn.ofFrobLevel K₁) L h₁ ℓ γ))
        = gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ (Ψ (ambientPi (NumFieldIn.ofFrobLevel M) L hML ℓ γ)) := by
      rw [hτγ, hΨeqγ]
    -- descend along `Ψ.symm` to `Γ_M^{tf}`
    have h3 := congrArg
      (gammaHausLift ℓ (Ψ.symm : Gamma ↥K₂.L Ω ℓ →* Gamma ↥M.L Ω ℓ) hΨsymm_cont) hstep
    rw [gammaHausLift_comp, gammaHausLift_comp] at h3
    simpa [σbar', MulEquiv.trans_apply] using h3
  -- Step 4: Lemma 4f.4 for the pair `(K₁, M)`, then join with `L`.
  have hπ₁ : Continuous ⇑(ambientPi (NumFieldIn.ofFrobLevel K₁) L h₁ ℓ) :=
    gammaBaseChange_continuous (K := ↥K₁.L) (K' := Ω) ℓ (levelExtend K₁ L h₁)
  have hπM : Continuous ⇑(ambientPi (NumFieldIn.ofFrobLevel M) L hML ℓ) :=
    gammaBaseChange_continuous (K := ↥M.L) (K' := Ω) ℓ (levelExtend M L hML)
  have h4f4 := lemma4f4 K₁ M L h₁ hML ℓ σbar' hσbar'cont hπ₁ hπM heq
  have hsup : (levelInfinityOf (NumFieldIn.ofFrobLevel K₁) ℓ ⊔ L.L : IntermediateField ℚ Ω)
      = (L.L ⊔ levelInfinityOf (NumFieldIn.ofFrobLevel M) ℓ : IntermediateField ℚ Ω) := by
    calc (levelInfinityOf (NumFieldIn.ofFrobLevel K₁) ℓ ⊔ L.L : IntermediateField ℚ Ω)
        = (levelInfinityOf (NumFieldIn.ofFrobLevel K₁) ℓ ⊔ M.L) ⊔ L.L := by rw [sup_assoc, sup_eq_right.mpr hML]
      _ = (K₁.L ⊔ levelInfinityOf (NumFieldIn.ofFrobLevel M) ℓ) ⊔ L.L := by rw [h4f4]
      _ = L.L ⊔ levelInfinityOf (NumFieldIn.ofFrobLevel M) ℓ := by
          rw [sup_assoc, sup_comm (levelInfinityOf (NumFieldIn.ofFrobLevel M) ℓ) L.L, ← sup_assoc,
            sup_eq_right.mpr h₁]
  -- Step 5: Proposition 4f.5 identifies `M` with `K₁`; `θ` then exhibits the isomorphism.
  have hKM : K₁.L = M.L := h45 K₁ M L h₁ hML hsup hcomplex
  refine ⟨?_⟩
  have hf : K₁.L = K₂.L.map (Θ τ).symm.toAlgHom := hKM.trans hM
  -- Pin the `Algebra ℚ` structures on the two subtypes, so that the `AlgEquiv` produced by
  -- `IntermediateField.equivMap` matches the instances of its declaration.
  letI : Algebra ℚ ↥K₂.L := IntermediateField.algebra' K₂.L
  letI : Algebra ℚ ↥(K₂.L.map (Θ τ).symm.toAlgHom) :=
    IntermediateField.algebra' (K₂.L.map (Θ τ).symm.toAlgHom)
  rw [hf]
  exact (IntermediateField.equivMap K₂.L (Θ τ).symm.toAlgHom).symm.toRingEquiv

end NK.Reconstruct
