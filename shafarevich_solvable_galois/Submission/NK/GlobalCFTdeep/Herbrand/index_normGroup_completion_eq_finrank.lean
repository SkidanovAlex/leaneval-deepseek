import Mathlib
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom
import Submission.NK.LocalReciprocity.NormGroup
import Submission.NK.LocalCFT.Instance.normGroup_real_complex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The index of the norm group of a completion at an infinite place

For a finite Galois extension of number fields `L / K`, an infinite place `v` of `K` and an
infinite place `w` of `L` lying over `v`, the local extension `w.Completion / v.Completion` is
either `ℝ / ℝ`, `ℂ / ℝ` or `ℂ / ℂ`, and hence has degree one or two.  In all three cases the
index of the norm group of units equals the local degree:

  `[v.Completionˣ : N_{w.Completion/v.Completion} w.Completionˣ] = [w.Completion : v.Completion]`.

This is the archimedean case of the Herbrand-quotient computation: it says that the norm index
of a local field is the degree of the extension.

The two ingredients are

* a transport lemma `index_normGroup_eq_of_equiv_equiv` which shows that the index of the norm
  group is invariant under a pair of compatible ring isomorphisms of the base and the top field
  (this is the norm-group analogue of `Algebra.finrank_eq_of_equiv_equiv`), and
* the degenerate case `index_normGroup_eq_one_of_finrank_eq_one`: in a degree one extension the
  norm of `algebraMap x` is `x ^ 1 = x`, so the norm map on units is surjective.

The remaining case `ℂ / ℝ` is `normGroup_real_complex` (the norm group is the group of positive
reals, of index two) together with `Units.index_posSubgroup`.
-/

namespace NK.GlobalCFTdeep.Herbrand

open scoped NumberField.LiesOver

open NK.LocalReciprocity

/-- **Transport of the norm group along ring isomorphisms.**  If `e₁ : A₁ ≃+* A₂` and
`e₂ : B₁ ≃+* B₂` are compatible with the algebra structures, then the norm group of `B₁/A₁` is
the preimage under `e₁` of the norm group of `B₂/A₂`. -/
theorem normGroup_eq_comap_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [Field A₁] [Field B₁]
    [Field A₂] [Field B₂] [Algebra A₁ B₁] [Algebra A₂ B₂]
    (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : (algebraMap A₂ B₂).comp (e₁ : A₁ →+* A₂) = (e₂ : B₁ →+* B₂).comp (algebraMap A₁ B₁)) :
    normGroup A₁ B₁ = (normGroup A₂ B₂).comap (Units.map e₁.toMonoidHom) := by
  ext u
  rw [Subgroup.mem_comap, mem_normGroup_iff, mem_normGroup_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.map e₂.toMonoidHom y, ?_⟩
    have key : e₁ (Algebra.norm A₁ (y : B₁)) = Algebra.norm A₂ (e₂ (y : B₁)) := by
      rw [Algebra.norm_eq_of_equiv_equiv e₁ e₂ he, RingEquiv.apply_symm_apply]
    simp only [Units.coe_map]
    change Algebra.norm A₂ (e₂ (y : B₁)) = e₁ (u : A₁)
    rw [← hy, key]
  · rintro ⟨z, hz⟩
    refine ⟨Units.map e₂.symm.toMonoidHom z, ?_⟩
    have key : e₁ (Algebra.norm A₁ (e₂.symm (z : B₂))) =
        Algebra.norm A₂ (e₂ (e₂.symm (z : B₂))) := by
      rw [Algebra.norm_eq_of_equiv_equiv e₁ e₂ he, RingEquiv.apply_symm_apply]
    apply e₁.injective
    simp only [Units.coe_map]
    change e₁ (Algebra.norm A₁ (e₂.symm (z : B₂))) = e₁ (u : A₁)
    rw [key, RingEquiv.apply_symm_apply, hz]
    rfl

/-- The index of the norm group is invariant under compatible ring isomorphisms of the base and
the top field.  This is the norm-group analogue of `Algebra.finrank_eq_of_equiv_equiv`. -/
theorem index_normGroup_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [Field A₁] [Field B₁]
    [Field A₂] [Field B₂] [Algebra A₁ B₁] [Algebra A₂ B₂]
    (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : (algebraMap A₂ B₂).comp (e₁ : A₁ →+* A₂) = (e₂ : B₁ →+* B₂).comp (algebraMap A₁ B₁)) :
    (normGroup A₁ B₁).index = (normGroup A₂ B₂).index := by
  rw [normGroup_eq_comap_of_equiv_equiv e₁ e₂ he,
    Subgroup.index_comap_of_surjective _ (Units.map_bijective e₁.bijective).surjective]

/-- In a degree one algebra the norm group on units is everything, so its index is one.  Indeed
the norm of `algebraMap F E x` is `x ^ [E : F] = x`. -/
theorem index_normGroup_eq_one_of_finrank_eq_one {F E : Type*} [Field F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 1) : (normGroup F E).index = 1 := by
  rw [Subgroup.index_eq_one, normGroup_eq_range, MonoidHom.range_eq_top]
  intro u
  have := Module.Free.of_divisionRing F E
  refine ⟨Units.map (algebraMap F E).toMonoidHom u, ?_⟩
  apply Units.ext
  simp only [Units.coe_map]
  change Algebra.norm F (algebraMap F E ↑u) = ↑u
  rw [Algebra.norm_algebraMap, h, pow_one]

/-- The norm group of `ℂ / ℝ` is the group of positive reals, which has index two in `ℝˣ`. -/
theorem index_normGroup_real_complex : (normGroup ℝ ℂ).index = 2 := by
  rw [NK.LocalCFT.Instance.normGroup_real_complex]
  exact Units.index_posSubgroup ℝ

theorem index_normGroup_completion_eq_finrank {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [hw : w.LiesOver v] :
    (NK.LocalReciprocity.normGroup v.Completion w.Completion).index
      = Module.finrank v.Completion w.Completion := by
  rcases NumberField.InfinitePlace.isUnramified_or_isRamified K w with h | h
  · rw [h.finrank_eq_one v]
    exact index_normGroup_eq_one_of_finrank_eq_one (h.finrank_eq_one v)
  · obtain ⟨hwc, hvr⟩ : w.IsComplex ∧ v.IsReal := by
      have H := NumberField.InfinitePlace.isRamified_iff.mp h
      rwa [NumberField.InfinitePlace.LiesOver.comap_eq w v] at H
    have := NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hvr
    rw [h.finrank_eq_two v,
      index_normGroup_eq_of_equiv_equiv
        (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvr)
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc) (by ext; simp)]
    exact index_normGroup_real_complex

end NK.GlobalCFTdeep.Herbrand
