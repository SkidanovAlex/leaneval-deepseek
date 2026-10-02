import Mathlib
import Submission.Work.ThomBordism.relH_zeroSection_localisation_injective
import Submission.Work.Cohomology.localCohomology
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.Tubular.Defs
import Submission.Work.Tubular.ThomComparison
import Submission.Work.Tubular.relKronH_natural
import Submission.Work.Tubular.LocalDegree
import Submission.Work.Cohomology.Endgame.tripleLESSurj
import Submission.Work.Cohomology.pd_us_f
import Submission.Work.ThomBordism.relCohomology_zeroSection_punct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-!
# Surjectivity of the localisation at a point of the zero section

Let `ν = NormalTotal E` be the normal total space of an embedding of a closed oriented smooth
`8`-manifold `V` in `ℝ^{8+k}`, let `0_x` be a point of its zero section and put `n = 8 + k`,
`A = normalNonzero E = ν∖0` (the complement of the zero section) and `B = ν∖{0_x}`.  The
restriction

  `H^n(ν, B) ⟶ H^n(ν, A)`

(the *cohomological localisation* of a class concentrated at `0_x`) is **surjective**.

## Proof

The subsets `A ⊆ B ⊆ ν` form a triple, and `Work.Cohomology.Endgame.relCohTriple_shortExact`
gives the long exact sequence of the triple

  `H^n(ν,B) --φ--> H^n(ν,A) --ρ--> H^n(B, B∩A) --δ--> H^{n+1}(ν,B)`,

whose exactness identifies `im φ` with `ker ρ`.  The third term `H^n(B, B∩A)` vanishes
(`Work.ThomBordism.relCohomology_zeroSection_punct`), so `ρ = 0` and `φ` is surjective.
-/

/-! ## The inclusion of relative complexes is the pullback along the identity -/

/-- The inclusion of the smaller relative cochain complex `C^*(X,A') ⊆ C^*(X,A)` (for `A ⊆ A'`) is
the cochain map induced by the identity of `X` viewed as a map of pairs `(X,A) → (X,A')`. -/
theorem relInclSet_eq_relComplexMap_id {X : TopCat} (A A' : Set X) (h : A ⊆ A') :
    Work.Cohomology.Endgame.relInclSet X A A' h
      = Work.Cohomology.relComplexMap ℤ A A' (𝟙 X) (fun x hx => by simpa using h hx) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [Work.Cohomology.Endgame.relInclSet_f, Work.Cohomology.relComplexMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom]
  rw [Work.Cohomology.Endgame.relInclSetHom_val]
  exact (Work.Cohomology.pd_us_relComplexMap_id_coe (X := X) (A := A) (B := A')
    (fun x hx => by simpa using h hx) n x).symm

/-! ## Surjectivity of the first map of a triple whose third term vanishes -/

/-- **If the third term `H^n(A', A'∩A)` of the triple `A ⊆ A' ⊆ X` vanishes, then the first map
`H^n(X,A') ⟶ H^n(X,A)` is surjective.**

This is the exactness of the long exact sequence of the triple at `H^n(X,A)`: the image of the
first map is the kernel of the second, and the second is zero because its target vanishes. -/
theorem surjective_of_triple_third_subsingleton {X : TopCat} {A A' : Set X} (h : A ⊆ A')
    (hh : ∀ x ∈ Work.Cohomology.Endgame.preA X A A',
      (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) (n : ℕ)
    (hzero : Subsingleton (Work.Cohomology.relCohomology ℤ (TopCat.of ↥A')
      (Work.Cohomology.Endgame.preA X A A') n)) :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relInclSet X A A' h) n)) := by
  have hS : (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).ShortExact :=
    Work.Cohomology.Endgame.relCohTriple_shortExact X A A' h hh
  have hex := ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₂ n)
  haveI : Subsingleton ((Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).X₃.homology n) :=
    hzero
  have hg : ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).g n) = 0 :=
    LinearMap.ext (fun y => Subsingleton.elim _ _)
  rw [hg, LinearMap.ker_zero] at hex
  intro y
  exact LinearMap.range_eq_top.mp hex y

/-! ## The target -/

theorem localisation_surjective_zeroSection {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    {k : ℕ} (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Function.Surjective ((Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
      (fun p hp => by
        intro h
        refine (Work.Tubular.mem_normalNonzero (E := E)).mp hp ?_
        have h2 : p = Work.Tubular.zeroSectionNormal E x := by simpa using h
        rw [h2]; simp)
      ℤ (8 + k)).hom) := by
  -- the vanishing of the third term of the triple (key geometric input)
  have hzero : Subsingleton (Work.Cohomology.relCohomology ℤ
      (TopCat.of ↥({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}))
      ((Subtype.val : ↥({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) →
        Work.Tubular.NormalTotal E) ⁻¹' Work.Tubular.normalNonzero E)
      (8 + k)) :=
    Work.ThomBordism.relCohomology_zeroSection_punct hk E x
  -- the subset relation, in the exact form of the statement
  have hsub : Work.Tubular.normalNonzero E ⊆
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) :=
    fun p hp => by
      intro h
      refine (Work.Tubular.mem_normalNonzero (E := E)).mp hp ?_
      have h2 : p = Work.Tubular.zeroSectionNormal E x := by simpa using h
      rw [h2]; simp
  have hsurj := surjective_of_triple_third_subsingleton
    (X := TopCat.of (Work.Tubular.NormalTotal E))
    (A := Work.Tubular.normalNonzero E)
    (A' := {p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
    hsub (fun y hy => by simp only [Work.Cohomology.subtypeIncl]; exact hy) (8 + k) hzero
  have hbridge : (Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)
          ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub
          ℤ (8 + k))
      = (HomologicalComplex.homologyMap (Work.Cohomology.Endgame.relInclSet
        (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub)
        (8 + k)) := by
    rw [relInclSet_eq_relComplexMap_id]
    congr 1
  rw [hbridge]
  exact hsurj

end

end Work.ThomBordism
