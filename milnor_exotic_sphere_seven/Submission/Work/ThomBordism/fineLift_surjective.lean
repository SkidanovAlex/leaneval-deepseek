import Mathlib
import Submission.Work.ThomBordism.localisation_surjective_zeroSection
import Submission.Work.ThomBordism.somePullbackCompPullV2
import Submission.Work.ThomBordism.ambientBase

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The fine lift: the localisation at a zero-section point of the Thom space is onto

Let `ν = NormalTotal E` be the normal total space of an embedding `E : V ↪ ℝ^{8+k}` of a connected
closed oriented smooth `8`-manifold, `ν⁺ = OnePoint ν` its one-point compactification (the Thom
space), `x₀` the zero-section point over `x`, `A = onePointNonzero E = ν⁺ ∖ (zero section)` and
`B = ν⁺ ∖ {x₀}`.  This file proves that the cohomological localisation

  `H^{8+k}(ν⁺, B) ⟶ H^{8+k}(ν⁺, A)`

is **surjective**: every class relative to the complement of the zero section extends to a class
relative to the complement of the single point `x₀`.

## Proof

The subsets `A ⊆ B ⊆ ν⁺` form a triple; the long exact sequence of the triple identifies the image
of the first map with the kernel of the second, so it suffices that the third term `H^{8+k}(B, A)`
vanishes.  Two ingredients give this.

* `punctPair_relCoh_subsingleton` computes `H^{8+k}(B, A)` as the relative cohomology of the
  *punctured normal bundle* pair: excision of the point at infinity in the open cover
  `{ν⁺∖{∞}, A}` of `B` (`Work.Cohomology.capRel_excision_isIso`) identifies `H^{8+k}(B,A)` with
  `H^{8+k}(ν∖{0_x}, ν∖0)`, and the latter vanishes by
  `Work.ThomBordism.relCohomology_zeroSection_punct` (the local degree of the Thom class is a unit).
* the vanishing is turned into the surjectivity of the localisation by the triple long exact
  sequence (`Work.ThomBordism.surjective_of_triple_third_subsingleton`), and the inclusion of
  relative complexes is identified with the pullback along the identity
  (`Work.ThomBordism.Mine.relInclSet_eq_relCohMap`).

This module deliberately does **not** import `Submission.Work.ThomBordism.collapseLocalisation_ambientV2`
(which consumes `fineLift_surjective`); the little helper `zeroSectionPunctPt_notMem` below is the
low-level home of the fact that the zero-section point over `x` lies outside `A`.
-/

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

/-- The homeomorphism of pairs `(ν⁺∖{x₀}, A∖{x₀}) ≅ (ν∖{0_x}, ν∖0)`
(`Work.Tubular.TubeClass.homeomorph_punctPair`) is the identity on the underlying points, read
through `OnePoint.some`. -/
theorem some_homeomorph_punctPair {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    (y : {q : Work.Tubular.PunctCompl E x //
      (q : OnePoint (Work.Tubular.NormalTotal E)) ∈ ({OnePoint.infty}ᶜ :
        Set (OnePoint (Work.Tubular.NormalTotal E)))}) :
    OnePoint.some ((Work.Tubular.TubeClass.homeomorph_punctPair E x y :
      Work.Tubular.NormalTotal E)) = (y : OnePoint (Work.Tubular.NormalTotal E)) := by
  have happ : (Work.Tubular.TubeClass.homeomorph_punctPair E x y : Work.Tubular.NormalTotal E)
      = ((Work.Tubular.onePointRangeHomeo (Work.Tubular.NormalTotal E)).symm
          (⟨(y : OnePoint (Work.Tubular.NormalTotal E)), y.2⟩ :
            ↥({OnePoint.infty}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))) := rfl
  rw [happ]
  exact congrArg Subtype.val
    ((Work.Tubular.onePointRangeHomeo (Work.Tubular.NormalTotal E)).apply_symm_apply
      (⟨(y : OnePoint (Work.Tubular.NormalTotal E)), y.2⟩ :
        ↥({OnePoint.infty}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))))

/-- **The relative cohomology of the pair `(ν⁺∖{x₀}, A)` vanishes** in the top degree
`8 + k`, where `A = onePointNonzero E = ν⁺ ∖ (zero section)` is viewed inside `ν⁺∖{x₀}`.

Excision of the point at infinity reduces it to `H^{8+k}(ν∖{0_x}, ν∖0) = 0`
(`Work.ThomBordism.relCohomology_zeroSection_punct`). -/
theorem punctPair_relCoh_subsingleton {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Subsingleton (Work.Thom.RelCoh ℤ (8 + k)
      (↥({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))
      ((Subtype.val : ↥({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
          Set (OnePoint (Work.Tubular.NormalTotal E))) → OnePoint (Work.Tubular.NormalTotal E)) ⁻¹'
        Work.Tubular.onePointNonzero E)) := by
  classical
  set B : Set (OnePoint (Work.Tubular.NormalTotal E)) :=
    ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))) with hB
  set U : Set ↥B := {y : ↥B | (y : OnePoint (Work.Tubular.NormalTotal E)) ∈
    ({OnePoint.infty}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))} with hU
  set A : Set ↥B := {y : ↥B | (y : OnePoint (Work.Tubular.NormalTotal E)) ∈
    Work.Tubular.onePointNonzero E} with hA
  -- the open cover `{U, A}` of `B`
  have hUopen : IsOpen U := (OnePoint.isClosed_infty.isOpen_compl).preimage continuous_subtype_val
  have hAopen : IsOpen A := (Work.Tubular.isOpen_onePointNonzero E).preimage continuous_subtype_val
  have hcov : U ∪ A = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases h : (y : OnePoint (Work.Tubular.NormalTotal E)) = OnePoint.infty
    · right
      rw [hA]
      exact Work.Tubular.mem_onePointNonzero.mpr (Or.inl h)
    · left
      rw [hU]
      exact fun h' => h h'
  -- excision: `H^{8+k}(B, A) ≅ H^{8+k}(U, U ∩ A)`
  let f := HomologicalComplex.homologyMap
    (Work.Cohomology.relComplexMap ℤ {y : ↥U | ((y : ↥B) : OnePoint (Work.Tubular.NormalTotal E)) ∈
        Work.Tubular.onePointNonzero E} A
      (Work.Cohomology.subtypeIncl (TopCat.of ↥B) U) (fun y hy => hy)) (8 + k)
  have hiso : CategoryTheory.IsIso f :=
    Work.Cohomology.capRel_excision_isIso (TopCat.of ↥B) U A hUopen hAopen hcov (8 + k)
      (fun y hy => hy)
  haveI : CategoryTheory.IsIso f := hiso
  -- the homeomorphism of pairs `(U, U ∩ A) ≅ (ν∖{0_x}, ν∖0)`
  let H : ↥U ≃ₜ ↥({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) :=
    Work.Tubular.TubeClass.homeomorph_punctPair E x
  have hsome : ∀ y : ↥U,
      OnePoint.some ((H y) : Work.Tubular.NormalTotal E) =
        ((y : ↥B) : OnePoint (Work.Tubular.NormalTotal E)) := by
    intro y
    have hy : ((y : ↥B) : OnePoint (Work.Tubular.NormalTotal E)) ∈
        ({OnePoint.infty}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))) := y.2
    exact some_homeomorph_punctPair E x ⟨y.1, hy⟩
  have heH : ∀ y : ↥U, y ∈ {z : ↥U | ((z : ↥B) : OnePoint (Work.Tubular.NormalTotal E)) ∈
        Work.Tubular.onePointNonzero E}
      ↔ (H y).1 ∈ Work.Tubular.normalNonzero E := by
    intro y
    show ((y : ↥B) : OnePoint (Work.Tubular.NormalTotal E)) ∈ Work.Tubular.onePointNonzero E ↔
      (H y).1 ∈ Work.Tubular.normalNonzero E
    rw [Work.Tubular.mem_onePointNonzero, Work.Tubular.mem_normalNonzero]
    constructor
    · rintro (hinf | ⟨q, hq, hqeq⟩)
      · exact absurd hinf y.2
      · have hqH : q = (H y).1 := by
          apply OnePoint.coe_injective
          rw [hqeq, ← hsome y]
        rw [← hqH]; exact hq
    · intro hy
      exact Or.inr ⟨(H y).1, hy, hsome y⟩
  obtain ⟨ehom⟩ := Work.Cohomology.relCohomology_homeomorph_pairs
    (X := ↥U) (Y := ↥({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}))
    ({z : ↥U | ((z : ↥B) : OnePoint (Work.Tubular.NormalTotal E)) ∈ Work.Tubular.onePointNonzero E})
    ((Subtype.val : ↥({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) →
      Work.Tubular.NormalTotal E) ⁻¹' Work.Tubular.normalNonzero E) H heH (8 + k)
  have h0 := Work.ThomBordism.relCohomology_zeroSection_punct (V := V) hk E x
  have hUU : Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of ↥U)
      {z : ↥U | ((z : ↥B) : OnePoint (Work.Tubular.NormalTotal E)) ∈
        Work.Tubular.onePointNonzero E}).homology (8 + k)) :=
    Work.Cohomology.subsingleton_of_iso ehom.symm h0
  exact Work.Cohomology.subsingleton_of_iso (CategoryTheory.asIso f).symm hUU

theorem fineLift_surjective {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Function.Surjective (ModuleCat.Hom.hom (Work.Thom.relCohMap
      (ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E)))
      (Work.Tubular.onePointNonzero E)
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
      (fun y hy => fun hcon => Work.ThomBordism.zeroSectionPunctPt_notMem E x (hcon ▸ hy))
      ℤ (8 + k))) := by
  have hsub : Work.Tubular.onePointNonzero E ⊆
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))) :=
    fun y hy => fun hcon => Work.ThomBordism.zeroSectionPunctPt_notMem E x (hcon ▸ hy)
  have hzero : Subsingleton (Work.Cohomology.relCohomology ℤ
      (TopCat.of ↥({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
        Set (OnePoint (Work.Tubular.NormalTotal E))))
      (Work.Cohomology.Endgame.preA (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
        (Work.Tubular.onePointNonzero E)
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))
      (8 + k)) :=
    punctPair_relCoh_subsingleton hk E x
  have hs := Work.ThomBordism.surjective_of_triple_third_subsingleton
    (X := TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
    (A := Work.Tubular.onePointNonzero E)
    (A' := ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))
    hsub (fun y hy => by simp only [Work.Cohomology.subtypeIncl]; exact hy) (8 + k) hzero
  rw [Work.ThomBordism.Mine.relInclSet_eq_relCohMap
    (X := TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
    (Work.Tubular.onePointNonzero E)
    ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
    hsub (8 + k)] at hs
  exact hs

end

end Work.ThomBordism
