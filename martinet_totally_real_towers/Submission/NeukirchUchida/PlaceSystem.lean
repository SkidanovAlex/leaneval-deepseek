import Submission.NeukirchUchida.Reduction
import Submission.Commons.NumberTheory.NumberField.Valuation.centralizer_stabilizer_valuationSubring_sepClosure
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top

/-!
# The place system of a separable closure and the local correspondence

This file develops the *bookkeeping* of the local correspondence of CoNF XII §12.2, starting from
the input `PreservesDecompositionGroups ϕ` of `Reduction.lean` (= the "if" direction of (12.1.9)
applied to `ϕ`):

* the decomposition group of a place of `K₁'` over a finite prime of `K₁` is non-trivial, and a
  place is determined by its decomposition group (rigidity, CoNF (12.1.4)/(12.1.9));
* `ϕ` therefore induces a *place map* `Φ` between the places of `K₁'` and those of `K₂'` over the
  finite primes, with `Φ(D_A) = ϕ(D_A)` in the sense of subgroups;
* `Φ` is a bijection, and it is `Gal`-equivariant: `Φ(g • A) = ϕ g • Φ(A)`.

This is the group-theoretic skeleton on which the reconstruction of the field isomorphism
(CoNF §12.2's use of Čebotarev) operates.
-/

namespace Submission.NeukirchUchida

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- The **places of `K'` over the finite primes of the number field `K`**, i.e. the valuation
subrings of `K'` whose trace on `K` is a proper valuation subring. -/
abbrev FinitePlace (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K'] [Algebra K K'] :=
  {A : ValuationSubring K' // A.comap (algebraMap K K') ≠ ⊤}

/-- **A decomposition group is non-trivial** (the local Galois groups are non-trivial). -/
theorem decompositionGroup_ne_bot {A : ValuationSubring K₁'}
    (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) :
    decompositionGroup (K₁ := K₁) (K₁' := K₁') A ≠ ⊥ := by
  intro hbot
  obtain ⟨σ, hσne, hσA⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top
      (K := K₁) (K' := K₁') A hA
  have hmem : σ ∈ decompositionGroup (K₁ := K₁) (K₁' := K₁') A :=
    (Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer
      (K := K₁) (K' := K₁') A σ).mp hσA
  rw [hbot] at hmem
  exact hσne (Subgroup.mem_bot.mp hmem)

/-- **A place is determined by its decomposition group** (rigidity of places, CoNF (12.1.4)): two
places over finite primes with the same decomposition group are equal. -/
theorem decompositionGroup_injective {A₁ A₂ : ValuationSubring K₁'}
    (h₁ : A₁.comap (algebraMap K₁ K₁') ≠ ⊤) (h₂ : A₂.comap (algebraMap K₁ K₁') ≠ ⊤)
    (h : decompositionGroup (K₁ := K₁) (K₁' := K₁') A₁ =
      decompositionGroup (K₁ := K₁) (K₁' := K₁') A₂) : A₁ = A₂ := by
  by_contra hne
  have hbot : decompositionGroup (K₁ := K₁) (K₁' := K₁') A₁ ⊓
      decompositionGroup (K₁ := K₁) (K₁' := K₁') A₂ = ⊥ :=
    Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne hne h₁ h₂
  have hmem : decompositionGroup (K₁ := K₁) (K₁' := K₁') A₁ = ⊥ := by
    rw [← hbot]
    exact le_antisymm (le_inf le_rfl h.le) inf_le_left
  exact decompositionGroup_ne_bot h₁ hmem

/-- The decomposition group of the translate of a place is the conjugate of the decomposition
group. -/
theorem decompositionGroup_smul (g : Gal(K₁'/K₁)) (A : ValuationSubring K₁') :
    decompositionGroup (K₁ := K₁) (K₁' := K₁') (g • A) =
      (decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g A

/-- The translates of a place over a finite prime again lie over a finite prime. -/
theorem smul_comap_ne_top (g : Gal(K₁'/K₁)) {A : ValuationSubring K₁'}
    (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) : (g • A).comap (algebraMap K₁ K₁') ≠ ⊤ := by
  rw [Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap]
  exact hA

/-- Conjugation commutes with a group isomorphism: `(gHg⁻¹)ϕ = ϕ(g)·ϕ(H)·ϕ(g)⁻¹`. -/
theorem map_mulAut_conj {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (H : Subgroup Gal(K₁'/K₁))
    (g : Gal(K₁'/K₁)) :
    (H.map (MulAut.conj g).toMonoidHom).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      (H.map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))).map (MulAut.conj (ϕ g)).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    refine ⟨ϕ z, ⟨z, hz, rfl⟩, ?_⟩
    rw [← hxy, ← hyz]
    simp
  · rintro ⟨w, ⟨z, hz, hzw⟩, hwx⟩
    refine ⟨g * z * g⁻¹, ⟨z, hz, ?_⟩, ?_⟩
    · simp
    · rw [← hwx, ← hzw]
      simp

/-- **The place map induced by `ϕ`** (the local correspondence), assuming that `ϕ` maps
decomposition groups to decomposition groups (input A of `Reduction.lean`). -/
noncomputable def placeMap (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : PreservesDecompositionGroups ϕ) : FinitePlace K₁ K₁' → FinitePlace K₂ K₂' :=
  fun A => ⟨(h.1 A.1 A.2).choose, (h.1 A.1 A.2).choose_spec.1⟩

/-- The defining property of the place map: `ϕ` maps the decomposition group of `A` onto that of
its image. -/
theorem placeMap_spec (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (h : PreservesDecompositionGroups ϕ)
    (A : FinitePlace K₁ K₁') :
    (decompositionGroup (K₁ := K₁) (K₁' := K₁') A.1).map
        (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      decompositionGroup (K₁ := K₂) (K₁' := K₂') (placeMap ϕ h A).1 :=
  (h.1 A.1 A.2).choose_spec.2

/-- The place map is injective: distinct places have distinct decomposition groups, and `ϕ` is
injective. -/
theorem placeMap_injective (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : PreservesDecompositionGroups ϕ) : Function.Injective (placeMap ϕ h) := by
  intro A₁ A₂ hA
  have h1 := placeMap_spec ϕ h A₁
  have h2 := placeMap_spec ϕ h A₂
  have hmap : decompositionGroup (K₁ := K₁) (K₁' := K₁') A₁.1 =
      decompositionGroup (K₁ := K₁) (K₁' := K₁') A₂.1 := by
    apply Subgroup.map_injective (f := (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))) ϕ.injective
    rw [h1, h2, hA]
  exact Subtype.ext (decompositionGroup_injective A₁.2 A₂.2 hmap)

/-- The place map is surjective, by the second half of the input. -/
theorem placeMap_surjective (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : PreservesDecompositionGroups ϕ) : Function.Surjective (placeMap ϕ h) := by
  intro B
  obtain ⟨A, hAne, hAB⟩ := h.2 B.1 B.2
  refine ⟨⟨A, hAne⟩, ?_⟩
  refine Subtype.ext ?_
  apply decompositionGroup_injective (K₁ := K₂) (K₁' := K₂')
    (placeMap ϕ h (⟨A, hAne⟩ : FinitePlace K₁ K₁')).2 B.2
  rw [decompositionGroup₂_eq] at hAB
  rw [← placeMap_spec ϕ h (⟨A, hAne⟩ : FinitePlace K₁ K₁'), ← hAB]

/-- The place map is a bijection. -/
theorem placeMap_bijective (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : PreservesDecompositionGroups ϕ) : Function.Bijective (placeMap ϕ h) :=
  ⟨placeMap_injective ϕ h, placeMap_surjective ϕ h⟩

/-- **The local correspondence is Galois-equivariant**: the image of a translate of a place is the
translate of its image by the corresponding element. -/
theorem placeMap_smul (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (h : PreservesDecompositionGroups ϕ)
    (g : Gal(K₁'/K₁)) (A : FinitePlace K₁ K₁') :
    placeMap ϕ h ⟨g • A.1, smul_comap_ne_top g A.2⟩ =
      ⟨ϕ g • (placeMap ϕ h A).1, smul_comap_ne_top (K₁ := K₂) (K₁' := K₂') (ϕ g)
        (placeMap ϕ h A).2⟩ := by
  refine Subtype.ext ?_
  apply decompositionGroup_injective (K₁ := K₂) (K₁' := K₂')
    (placeMap ϕ h ⟨g • A.1, smul_comap_ne_top g A.2⟩).2
    (smul_comap_ne_top (K₁ := K₂) (K₁' := K₂') (ϕ g) (placeMap ϕ h A).2)
  rw [← placeMap_spec ϕ h (⟨g • A.1, smul_comap_ne_top g A.2⟩ : FinitePlace K₁ K₁'),
    decompositionGroup_smul, map_mulAut_conj, placeMap_spec ϕ h A, decompositionGroup_smul]

end Submission.NeukirchUchida

namespace Submission.NeukirchUchida

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-! ## The "only if" half of CoNF (12.1.9): decomposition groups are self-normalising -/

/-- **A decomposition group is self-normalising** (CoNF XII (12.1.4) in normaliser form; the
"only if" half of the characterisation (12.1.9) of decomposition groups). -/
theorem normalizer_decompositionGroup
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (A : ValuationSubring K₁')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ p) :
    Subgroup.normalizer (decompositionGroup (K₁ := K₁) (K₁' := K₁') A) =
      decompositionGroup (K₁ := K₁) (K₁' := K₁') A := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  intro σ hσ
  have hconj : ∀ τ ∈ decompositionGroup (K₁ := K₁) (K₁' := K₁') A, σ * τ * σ⁻¹ ∈ decompositionGroup (K₁ := K₁) (K₁' := K₁') A :=
    fun τ hτ => ((Subgroup.mem_normalizer_iff (H := decompositionGroup (K₁ := K₁) (K₁' := K₁') A) (g := σ)).mp hσ τ).mp hτ
  have hgoal : A.comap (σ : K₁' →+* K₁') = A := by
    refine Commons.NumberTheory.NumberField.Valuation.normalizer_stabilizer_valuationSubring_sepClosure
      (K := K₁) (K' := K₁') p A hA σ ?_
    intro τ hτ
    have hτmem : τ ∈ decompositionGroup (K₁ := K₁) (K₁' := K₁') A :=
      (Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer (K := K₁) (K' := K₁') A τ).mp hτ
    exact (Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer (K := K₁) (K' := K₁') A (σ * τ * σ⁻¹)).mpr
      (hconj τ hτmem)
  unfold decompositionGroup
  exact (Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer (K := K₁) (K' := K₁') A σ).mp hgoal

end Submission.NeukirchUchida
