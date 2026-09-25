import Mathlib
import Submission.NK.LocalTame.Global

namespace NK.LocalTame.Global

/-! ## The inertia subgroup at corresponding places

`NK.LocalTame.Main` proves that an isomorphism `Φ : Gal(κ̄/κ) ≃* Gal(λ̄/λ)` of the absolute
Galois groups of two local fields maps the inertia subgroup `I_κ` onto the inertia subgroup
`I_λ` (`NK.LocalTame.mulEquiv_maps_inertia`).  Here we transport that statement to the global
setting: if the decomposition groups `D_A`, `D_B` of two places are identified with the local
absolute Galois groups by `eA`, `eB` and correspond to each other under `Φ`, then the image of
the inertia subgroup of `D_A` under the induced isomorphism `D_A ≃* D_B` is the inertia subgroup
of `D_B`.  This is the "inertia matches at corresponding places" half of the local/global
correspondence of CoNF (12.1.9), in the form in which the Neukirch–Uchida endgame consumes it.

The proof is purely formal: the composite isomorphism

`Φloc = eA.symm.trans (δ.trans eB) : Gal(κ̄/κ) ≃* Gal(λ̄/λ)`

makes the square with corners `D_A`, `D_B`, `Gal(κ̄/κ)`, `Gal(λ̄/λ)` commute, so mapping the
preimage of `I_κ` under `eA` along `δ` is the preimage under `eB` of `Φloc(I_κ) = I_λ`, which is
`mulEquiv_maps_inertia`. -/

/-- **Mapping a preimage along a commuting square.**  If `Φ : G₁ ≃* G₂` is the isomorphism induced
by `δ : D₁ ≃* D₂` through the identifications `eA : D₁ ≃* G₁`, `eB : D₂ ≃* G₂` (i.e.
`Φ (eA y) = eB (δ y)` for all `y`), then the image of `H.comap eA` under `δ` is `H.map Φ`
pulled back along `eB`, for every `H ≤ G₁`. -/
theorem map_comap_eq_comap_map {D₁ D₂ G₁ G₂ : Type*} [Group D₁] [Group D₂] [Group G₁]
    [Group G₂] (eA : D₁ ≃* G₁) (eB : D₂ ≃* G₂) (δ : D₁ ≃* D₂) (Φ : G₁ ≃* G₂)
    (hΦ : ∀ y : D₁, Φ (eA y) = eB (δ y)) (H : Subgroup G₁) :
    (H.comap (eA : D₁ →* G₁)).map (δ : D₁ →* D₂) =
      (H.map (Φ : G₁ →* G₂)).comap (eB : D₂ →* G₂) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨eA y, hy, hΦ y⟩
  · rintro ⟨z, hz, hz'⟩
    refine ⟨δ.symm x, ?_, by simp⟩
    rw [Subgroup.mem_comap]
    have h1 : Φ (eA (δ.symm x)) = Φ z := by
      rw [hΦ, MulEquiv.apply_symm_apply]
      exact hz'.symm
    have h2 : eA (δ.symm x) = z := Φ.injective h1
    rw [show (eA : D₁ →* G₁) (δ.symm x) = z from h2]
    exact hz

/-- **The inertia subgroups at corresponding places match.**  Let `A` be a place of `K₁'` over
`𝔭₁` and `B` a place of `K₂'` over `𝔭₂`, identified with the local absolute Galois groups of the
completions by `eA`, `eB`, and suppose the decomposition groups `D_A = D_B` correspond under the
isomorphism `Φ` of absolute Galois groups (`Φ(D_A) = D_B`, the local correspondence of CoNF
(12.1.9)).  Then the isomorphism `D_A ≃* D_B` induced by `Φ` carries the inertia subgroup of
`D_A` (relative to `eA`) onto the inertia subgroup of `D_B` (relative to `eB`). -/
theorem inertia_matching_at_corresponding_places {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔭₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭₁)
    (B : ValuationSubring K₂')
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔭₂)
    (Φ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        (Φ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B)
    {p₁ q₁ p₂ q₂ : ℕ}
    (hT : TameData p₁ q₁ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)))
    (hT₂ : TameData p₂ q₂ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)))
    (hp : p₁ = p₂)
    (eA : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁))
    (eB : Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)) :
    (NK.LocalTame.inertiaOfDecomposition p₁ eA).map (NK.LocalTame.mulEquivSubgroupCongr Φ hAB) =
      NK.LocalTame.inertiaOfDecomposition p₂ eB := by
  let δ := NK.LocalTame.mulEquivSubgroupCongr Φ hAB
  let Φloc : Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁) ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂) :=
    eA.symm.trans (δ.trans eB)
  have hΦ : ∀ y, Φloc (eA y) = eB (δ y) := by intro y; simp [Φloc]
  have hmap := NK.LocalTame.mulEquiv_maps_inertia hT hT₂ hp Φloc
  rw [NK.LocalTame.inertiaOfDecomposition, NK.LocalTame.inertiaOfDecomposition, ← hmap]
  exact map_comap_eq_comap_map eA eB δ Φloc hΦ _

end NK.LocalTame.Global
