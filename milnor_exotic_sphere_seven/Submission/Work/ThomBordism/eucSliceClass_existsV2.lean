import Mathlib
import Submission.Work.ThomBordism.coorientationRef
import Submission.Work.ThomBordism.chartModelClassDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A preimage of the standard model generator on the sphere pair (V2 spelling)

`Work.ThomBordism.stdModelGen n` is the determinate generator of the relative cohomology
`H^n(ℝⁿ, ℝⁿ∖0; ℤ)` of the model pair.  This file produces a class `σ` on the **sphere pair**
`(S^n, S^n∖{0})` — with `S^n = OnePoint ℝⁿ` — whose pullback along the inclusion
`ℝⁿ ↪ Sⁿ` (spelled here as the raw map `⟨OnePoint.some, OnePoint.continuous_coe⟩`, and with the
membership proof written out in the statement) is `stdModelGen n`.

This is the same statement as `Work.ThomBordism.eucSliceClass_exists` with the inclusion
`Work.ThomBordism.eucToOnePoint` replaced by its unfolding; the two are definitionally equal, but
the proof here is *self-contained*: it does **not** import
`Submission.Work.ThomBordism.eucSliceClass_exists` (hence not
`Submission.Work.ThomBordism.collapseLocalisation_ambientV2` either), so it can be used inside the
development of that file without a circular import.

The mathematical content is that the inclusion of pairs

  `(ℝⁿ, ℝⁿ∖0) ⟶ (Sⁿ, Sⁿ∖{0})`

induces an **isomorphism** on relative cohomology: both sides are `ℤ` in degree `n` and the two
pairs differ only by the "point at infinity", which lies in the second member of the pair.  This is
excision: the two open sets `U = Sⁿ∖{∞}` and `A = Sⁿ∖{0}` cover `Sⁿ`, and the inclusion of the
open pair `(U, U∩A)` into `(Sⁿ, A)` is a cohomology isomorphism
(`Work.Cohomology.capRel_excision_isIso`); under the homeomorphism `Sⁿ∖{∞} ≅ ℝⁿ`
(`Work.Tubular.onePointRangeHomeo`) the pair `(U, U∩A)` is the model pair `(ℝⁿ, ℝⁿ∖0)`
(`Work.Cohomology.capRel_relComplexMap_iso_of_isIso_pairs`), and the composite of the two
isomorphisms is precisely the pullback along the inclusion `ℝⁿ ↪ Sⁿ`.  The two isomorphisms are
composed on the *chain/cochain* level by `Work.Cohomology.capRel_isIso_relComplexMap_comp`, which
avoids any coherence bookkeeping.  The final step is then a pure formality: an isomorphism is
surjective (`Work.Cohomology.surjective_of_isIso`).

## Implementation notes (`OnePoint` is a `def` for `Option`)

The workhorse is the *inclusion* `ℝⁿ → Sⁿ`; writing `(TopCat.ofHom f) x` (`f` a continuous map)
and `f x` produces terms that are equal but not syntactically identical, so the proofs below
(i) apply `TopCat.ofHom_apply` to expose the unbundled map and (ii) `change` before rewriting, so
that `rw` sees the coercion it must rewrite.  The sets `U`, `A`, `A₁` are `abbrev`s rather than
`let`-bound locals: with `let`-bound sets unification unfolds `TopCat.of`/`OnePoint` under the type
ascription of the local and becomes pathologically slow.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open CategoryTheory

noncomputable section

namespace Work.ThomBordism

/-- The inclusion `ℝⁿ ↪ Sⁿ = OnePoint ℝⁿ`, as the raw continuous map (the map appearing in the
statement of `eucSliceClass_existsV2`). -/
def eucInclV2 (n : ℕ) : C(Work.Tubular.Euc n, OnePoint (Work.Tubular.Euc n)) :=
  ⟨OnePoint.some, OnePoint.continuous_coe⟩

/-- The inclusion of pairs `(ℝⁿ, ℝⁿ∖0) → (Sⁿ, Sⁿ∖{0})`. -/
theorem eucInclV2_mem (n : ℕ) :
    ∀ v ∈ ({0}ᶜ : Set (Work.Tubular.Euc n)),
      eucInclV2 n v ∈ ({OnePoint.some (0 : Work.Tubular.Euc n)}ᶜ :
        Set (OnePoint (Work.Tubular.Euc n))) :=
  fun _ hv hcon => hv (OnePoint.coe_injective hcon)

/-- `Sⁿ = OnePoint ℝⁿ` as a `TopCat`. -/
abbrev eucSphV2 (n : ℕ) : TopCat := TopCat.of (OnePoint (Work.Tubular.Euc n))

/-- The punctured sphere `Sⁿ ∖ {0}`. -/
abbrev eucSphV2A (n : ℕ) : Set (OnePoint (Work.Tubular.Euc n)) :=
  ({OnePoint.some (0 : Work.Tubular.Euc n)}ᶜ : Set (OnePoint (Work.Tubular.Euc n)))

/-- The complement of `∞`, i.e. the image of `ℝⁿ`. -/
abbrev eucSphV2U (n : ℕ) : Set (OnePoint (Work.Tubular.Euc n)) :=
  ({OnePoint.infty}ᶜ : Set (OnePoint (Work.Tubular.Euc n)))

/-- `U ∩ A`: the punctured Euclidean space inside the complement of `∞`. -/
abbrev eucSphV2A₁ (n : ℕ) : Set ↥(eucSphV2U n) :=
  {y | (y : OnePoint (Work.Tubular.Euc n)) ∈ eucSphV2A n}

/-- The homeomorphism `ℝⁿ ≅ Sⁿ ∖ {∞}`, as a continuous map. -/
abbrev sliceHomeoV2 (n : ℕ) :
    C(Work.Tubular.Euc n, ↥(eucSphV2U n)) :=
  (Work.Tubular.onePointRangeHomeo (Work.Tubular.Euc n) : C(_, _))

/-- Its inverse, as a continuous map. -/
abbrev sliceHomeoInvV2 (n : ℕ) :
    C(↥(eucSphV2U n), Work.Tubular.Euc n) :=
  ((Work.Tubular.onePointRangeHomeo (Work.Tubular.Euc n)).symm : C(_, _))

theorem eucSphV2U_isOpen (n : ℕ) : IsOpen (eucSphV2U n) := by
  change IsOpen ({OnePoint.infty}ᶜ : Set (OnePoint (Work.Tubular.Euc n)))
  rw [OnePoint.compl_infty]
  exact OnePoint.isOpenEmbedding_coe.isOpen_range

theorem eucSphV2A_isOpen (n : ℕ) : IsOpen (eucSphV2A n) := by
  rw [show eucSphV2A n = (OnePoint.some '' ({0} : Set (Work.Tubular.Euc n)))ᶜ by
    simp [eucSphV2A]]
  exact (OnePoint.isClosed_image_coe.mpr ⟨isClosed_singleton, isCompact_singleton⟩).isOpen_compl

theorem eucSphV2U_union_eucSphV2A (n : ℕ) : eucSphV2U n ∪ eucSphV2A n = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x = OnePoint.infty
  · rw [hx]
    exact Or.inr (Set.mem_compl_singleton_iff.mpr
      (Ne.symm (OnePoint.coe_ne_infty (0 : Work.Tubular.Euc n))))
  · exact Or.inl (Set.mem_compl_singleton_iff.mpr hx)

/-- **Excision**: the inclusion of pairs `(ℝⁿ, ℝⁿ∖0) → (Sⁿ, Sⁿ∖{0})` is an isomorphism on
relative cohomology, obtained by composing the excision isomorphism for the open cover
`{Sⁿ∖{∞}, Sⁿ∖{0}}` with the homeomorphism `Sⁿ∖{∞} ≅ ℝⁿ` of pairs. -/
theorem isIso_relComplexMap_eucInclV2 (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap ℤ ({0}ᶜ : Set (Work.Tubular.Euc n))
        (eucSphV2A n) (TopCat.ofHom (eucInclV2 n)) (eucInclV2_mem n)) n) := by
  classical
  have hsub : ∀ x ∈ (eucSphV2A₁ n),
      (Work.Cohomology.subtypeIncl (eucSphV2 n) (eucSphV2U n)) x ∈ eucSphV2A n :=
    fun x hx => hx
  have hexc := Work.Cohomology.capRel_excision_isIso (eucSphV2 n) (eucSphV2U n) (eucSphV2A n)
    (eucSphV2U_isOpen n) (eucSphV2A_isOpen n) (eucSphV2U_union_eucSphV2A n) n hsub
  have he_mem : ∀ v ∈ ({0}ᶜ : Set (Work.Tubular.Euc n)),
      (TopCat.ofHom (sliceHomeoV2 n)) v ∈ eucSphV2A₁ n := by
    intro v hv
    rw [TopCat.ofHom_apply]
    have h1 : (↑(sliceHomeoV2 n v) : OnePoint (Work.Tubular.Euc n)) = OnePoint.some v :=
      Work.Tubular.onePointRangeHomeo_apply v
    change (↑(sliceHomeoV2 n v) : OnePoint (Work.Tubular.Euc n)) ∈
      ({OnePoint.some (0 : Work.Tubular.Euc n)}ᶜ : Set (OnePoint (Work.Tubular.Euc n)))
    rw [h1, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => hv (OnePoint.coe_injective h)
  have he_symm_mem : ∀ y ∈ (eucSphV2A₁ n),
      (TopCat.ofHom (sliceHomeoInvV2 n)) y ∈ ({0}ᶜ : Set (Work.Tubular.Euc n)) := by
    intro y hy
    have hy' : (↑y : OnePoint (Work.Tubular.Euc n)) ≠
        OnePoint.some (0 : Work.Tubular.Euc n) := hy
    rw [TopCat.ofHom_apply]
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h0
    apply hy'
    have h1 : (↑(sliceHomeoV2 n (sliceHomeoInvV2 n y)) : OnePoint (Work.Tubular.Euc n))
        = OnePoint.some (sliceHomeoInvV2 n y) :=
      Work.Tubular.onePointRangeHomeo_apply (sliceHomeoInvV2 n y)
    have h2 : (↑(sliceHomeoV2 n (sliceHomeoInvV2 n y)) : OnePoint (Work.Tubular.Euc n))
        = (↑y : OnePoint (Work.Tubular.Euc n)) :=
      congrArg Subtype.val
        ((Work.Tubular.onePointRangeHomeo (Work.Tubular.Euc n)).apply_symm_apply y)
    have h3 : sliceHomeoInvV2 n y = 0 := h0
    rw [← h2, h1, h3]
  have hfg : CategoryTheory.CategoryStruct.comp
      (TopCat.ofHom (sliceHomeoV2 n)) (TopCat.ofHom (sliceHomeoInvV2 n))
      = 𝟙 (TopCat.of (Work.Tubular.Euc n)) := by
    apply TopCat.ext
    intro v
    exact (Work.Tubular.onePointRangeHomeo (Work.Tubular.Euc n)).symm_apply_apply v
  have hgf : CategoryTheory.CategoryStruct.comp
      (TopCat.ofHom (sliceHomeoInvV2 n)) (TopCat.ofHom (sliceHomeoV2 n))
      = 𝟙 (TopCat.of ↥(eucSphV2U n)) := by
    apply TopCat.ext
    intro y
    exact (Work.Tubular.onePointRangeHomeo (Work.Tubular.Euc n)).apply_symm_apply y
  have hhom := Work.Cohomology.capRel_relComplexMap_iso_of_isIso_pairs
      (X₁ := TopCat.of (Work.Tubular.Euc n)) (X₂ := TopCat.of ↥(eucSphV2U n)) ℤ
      ({0}ᶜ : Set (Work.Tubular.Euc n)) (eucSphV2A₁ n)
      (TopCat.ofHom (sliceHomeoV2 n)) he_mem
      (TopCat.ofHom (sliceHomeoInvV2 n)) he_symm_mem hfg hgf n
  have hcomp := Work.Cohomology.capRel_isIso_relComplexMap_comp
      (X₀ := TopCat.of (Work.Tubular.Euc n)) (X₁ := TopCat.of ↥(eucSphV2U n)) (X₂ := eucSphV2 n)
      ℤ ({0}ᶜ : Set (Work.Tubular.Euc n))
      (eucSphV2A₁ n) (eucSphV2A n) (TopCat.ofHom (sliceHomeoV2 n))
      (Work.Cohomology.subtypeIncl (eucSphV2 n) (eucSphV2U n))
      he_mem hsub n (fun v hv => hsub _ (he_mem v hv)) hexc hhom
  have hmap : CategoryTheory.CategoryStruct.comp
      (TopCat.ofHom (sliceHomeoV2 n)) (Work.Cohomology.subtypeIncl (eucSphV2 n) (eucSphV2U n))
      = TopCat.ofHom (eucInclV2 n) := by
    apply TopCat.ext
    intro v
    show (Work.Cohomology.subtypeIncl (eucSphV2 n) (eucSphV2U n)) ((TopCat.ofHom (sliceHomeoV2 n)) v)
      = eucInclV2 n v
    rw [TopCat.ofHom_apply]
    exact Work.Tubular.onePointRangeHomeo_apply v
  have hEq := Work.Cohomology.capRel_relComplexMap_congr
      (X₁ := TopCat.of (Work.Tubular.Euc n)) (X₂ := eucSphV2 n)
      ℤ ({0}ᶜ : Set (Work.Tubular.Euc n)) (eucSphV2A n)
      hmap (fun v hv => hsub _ (he_mem v hv)) (eucInclV2_mem n)
  rw [← hEq]
  exact hcomp

theorem eucSliceClass_existsV2 (k : ℕ) :
    ∃ σ : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.Euc (8 + k)))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
          Set (OnePoint (Work.Tubular.Euc (8 + k)))),
      (Work.Thom.relCohMap
        (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
          C(Work.Tubular.Euc (8 + k), OnePoint (Work.Tubular.Euc (8 + k))))
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
          Set (OnePoint (Work.Tubular.Euc (8 + k))))
        (fun v hv => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv ⊢
          exact fun h => hv (OnePoint.coe_injective h))
        ℤ (8 + k)).hom σ = Work.ThomBordism.stdModelGen (8 + k) := by
  haveI hslice : CategoryTheory.IsIso
      (Work.Thom.relCohMap (eucInclV2 (8 + k))
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
          Set (OnePoint (Work.Tubular.Euc (8 + k))))
        (eucInclV2_mem (8 + k)) ℤ (8 + k)) := isIso_relComplexMap_eucInclV2 (8 + k)
  exact Work.Cohomology.surjective_of_isIso
    (Work.Thom.relCohMap (eucInclV2 (8 + k))
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k))))
      (eucInclV2_mem (8 + k)) ℤ (8 + k))
    (Work.ThomBordism.stdModelGen (8 + k))

end Work.ThomBordism
