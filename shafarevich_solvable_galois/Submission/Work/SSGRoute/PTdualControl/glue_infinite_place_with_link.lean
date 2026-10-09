import Mathlib
import Submission.Work.SSGRoute.glue_infinite_place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTdualControl

/-- An automorphism of a finite Galois level `K` acting by complex conjugation with respect to the
infinite place `w.embedding` extends to an involution of the absolute Galois group `Gal(Ω/k)`,
*and* the extension is compatible with the completion map `φ := ComplexEmbedding.lift Ω w.embedding`
in the sense that `φ (σ x) = conj (φ x)`.

This is exactly the local seam exposed: `glue_infinite_place` builds `σ = σ₁.symm` from
`φ := ComplexEmbedding.lift Ω w.embedding` and `hσ : φ.comp (↑σ₁.symm) = conj φ`, and `hσ` is the
missing clause. -/
private theorem exists_involution_extension_omega_aux_link (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (w : NumberField.InfinitePlace ↥K) (σ₀ : ↥K ≃ₐ[k] ↥K)
    (hσ₀ : NumberField.ComplexEmbedding.IsConj (k := k) w.embedding σ₀) :
    ∃ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 ∧
      (NumberField.ComplexEmbedding.lift Ω w.embedding).comp (σ : Ω →+* Ω)
        = NumberField.ComplexEmbedding.conjugate
            (NumberField.ComplexEmbedding.lift Ω w.embedding) ∧
      SSGRoute.res k K σ = σ₀ := by
  have hcz : CharZero k := inferInstance
  have hgal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  let E := ↥K
  let φ : Ω →+* ℂ := NumberField.ComplexEmbedding.lift Ω w.embedding
  have hφc : ∀ y : E, φ (y : Ω) = w.embedding y := by
    intro y
    rw [← IntermediateField.algebraMap_apply K y]
    exact NumberField.ComplexEmbedding.lift_algebraMap_apply Ω w.embedding y
  -- `φ` restricts to a real-valued map on `k`, so complex conjugation preserves `φ(Ω)`.
  have hreal : NumberField.ComplexEmbedding.IsReal (φ.comp (algebraMap k Ω)) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    rw [← NumberField.ComplexEmbedding.conjugate_comp]
    ext a
    simp only [RingHom.comp_apply]
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have h1 : φ (algebraMap k Ω a) = w.embedding (algebraMap k E a) := by
      rw [IsScalarTower.algebraMap_apply k E Ω]
      exact hφc _
    rw [h1]
    have hc := hσ₀.eq (algebraMap k E a)
    rw [AlgEquiv.commutes] at hc
    exact hc.symm
  -- `φ⁻¹ ∘ conj ∘ φ` is an element of `Gal(Ω/k)` because `conj ∘ φ` and `φ` agree on `k`.
  obtain ⟨σ₁, hσ₁⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (K := Ω) (k := k)
    φ (NumberField.ComplexEmbedding.conjugate φ) (by
      rw [NumberField.ComplexEmbedding.conjugate_comp]
      exact hreal.symm)
  have hσ : φ.comp (↑(σ₁.symm) : Ω →+* Ω) = NumberField.ComplexEmbedding.conjugate φ := hσ₁
  have hIsConj : NumberField.ComplexEmbedding.IsConj (k := k) (K := Ω) φ σ₁.symm := hσ.symm
  refine ⟨σ₁.symm, ?_, hσ, ?_⟩
  · -- `conj` is an involution, so `σ₁.symm` is one too.
    rw [pow_two]
    ext x
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact NumberField.ComplexEmbedding.isConj_apply_apply hIsConj x
  · -- On `K ⊆ Ω` the involution `σ₁.symm` agrees with `σ₀`, since `φ` is injective.
    ext x
    apply φ.injective
    rw [AlgEquiv.restrictNormalHom_apply]
    have h1 : φ ((σ₁.symm) ((x : E) : Ω)) = starRingEnd ℂ (φ ((x : E) : Ω)) :=
      RingHom.congr_fun hσ ((x : E) : Ω)
    have h2 : φ (((σ₀ x : E)) : Ω) = starRingEnd ℂ (φ ((x : E) : Ω)) := by
      rw [hφc (σ₀ x), hφc x]
      exact hσ₀.eq x
    rw [h2]
    exact h1

/-- **The place glue at an infinite place, with the local seam exposed.**

`Work.SSGRoute.glue_infinite_place` produces, for a ramified infinite place `w`, an involution
`σ ∈ Gal(Ω/k)` with `D_w ≤ (⟨σ⟩).map (res k K)` — but *not* the data that ties `σ` to the place `w`.
That data is what the archimedean comparison square needs (it is the archimedean analogue of the
lying-over hypothesis `hAq` of the finite-place crux
`PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero`): the coefficient change `Ωˣ → K_wˣ` induced
by the completion/seam `φ = NumberField.ComplexEmbedding.lift Ω w.embedding` must be
`⟨σ⟩`-equivariant, i.e. `φ (σ x) = conj (φ x)`.

The disjunction below is that of `glue_infinite_place` with the extra conjunct `φ.comp σ = conj φ`.
It is *literally* the data already constructed inside the proof of `glue_infinite_place` (which
builds `σ = σ₁.symm` from `φ := ComplexEmbedding.lift Ω w.embedding` and
`hσ : φ.comp (↑σ₁.symm) = ComplexEmbedding.conjugate φ`), so it is expected to be proved by
adapting that proof (the auxiliary `exists_involution_extension_omega_aux` is `private` there and may
be re-stated/copied).  Consumers: the corrected archimedean crux (see
`PTdualControl/NOTE_s14_archimedeanCruxA_and_leaf5_frontier.md`) and any restatement of
`SSGStage.archimedeanLocalDictionary` / `SSGStage.e1aLandingInfLocal` carrying the seam clause. -/
theorem glue_infinite_place_with_link (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (w : NumberField.InfinitePlace ↥K) :
    MulAction.stabilizer (↥K ≃ₐ[k] ↥K) (NK.GlobalCFT.Place.ofInfinite w) = ⊥ ∨
      ∃ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 ∧
        (NumberField.ComplexEmbedding.lift Ω w.embedding).comp (σ : Ω →+* Ω)
          = NumberField.ComplexEmbedding.conjugate
              (NumberField.ComplexEmbedding.lift Ω w.embedding) ∧
        MulAction.stabilizer (↥K ≃ₐ[k] ↥K) (NK.GlobalCFT.Place.ofInfinite w) ≤
          (Subgroup.zpowers σ).map (SSGRoute.res k K) := by
  -- The stabiliser of `ofInfinite w` is the stabiliser of `w` itself.
  have hmem : ∀ γ : ↥K ≃ₐ[k] ↥K,
      γ ∈ MulAction.stabilizer (↥K ≃ₐ[k] ↥K) (NK.GlobalCFT.Place.ofInfinite w) ↔
        γ ∈ MulAction.stabilizer (↥K ≃ₐ[k] ↥K) w := by
    intro γ
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj]
  by_cases hunr : NumberField.InfinitePlace.IsUnramified k w
  · -- Unramified place: the decomposition group is trivial.
    left
    rw [Subgroup.eq_bot_iff_forall]
    intro γ hγ
    have h1 : γ ∈ MulAction.stabilizer (↥K ≃ₐ[k] ↥K) w := (hmem γ).mp hγ
    rw [NumberField.InfinitePlace.IsUnramified.stabilizer_eq_bot hunr] at h1
    simpa using h1
  · -- Ramified place: the decomposition group is the group of order two generated by the local
    -- complex conjugation, which extends to an involution of the absolute Galois group carrying
    -- the local seam.
    right
    have hram' : NumberField.InfinitePlace.IsRamified k
        (NumberField.InfinitePlace.mk w.embedding) := by
      rwa [NumberField.InfinitePlace.mk_embedding]
    obtain ⟨σ₀, hσ₀⟩ :=
      NumberField.InfinitePlace.exists_isConj_of_isRamified (k := k) (φ := w.embedding) hram'
    obtain ⟨σ, hσ2, hσlink, hσres⟩ := exists_involution_extension_omega_aux_link k Ω K w σ₀ hσ₀
    refine ⟨σ, hσ2, hσlink, ?_⟩
    have hmap : (Subgroup.zpowers σ).map (SSGRoute.res k K) = Subgroup.zpowers σ₀ := by
      rw [MonoidHom.map_zpowers, hσres]
    rw [hmap]
    have hstab : (MulAction.stabilizer (↥K ≃ₐ[k] ↥K) w : Set (↥K ≃ₐ[k] ↥K)) = {1, σ₀} := by
      rw [← NumberField.InfinitePlace.mk_embedding w]
      exact hσ₀.coe_stabilizer_mk
    intro γ hγ
    have h2 : γ ∈ (MulAction.stabilizer (↥K ≃ₐ[k] ↥K) w : Set (↥K ≃ₐ[k] ↥K)) :=
      (hmem γ).mp hγ
    rw [hstab] at h2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
    rcases h2 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers σ₀

end Work.SSGRoute.PTdualControl
