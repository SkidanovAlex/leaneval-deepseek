import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.Thom.ModelThomA
import Submission.Work.Thom.CohMap_oneH
import Submission.Work.Cohomology.relComplex_empty_homology_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-!
# The model induction for the trivial bundle, with canonical choices

This file fixes the *data* of the model induction of `Submission/Work/Thom/ModelThomA.lean`
(`Work.Thom.CleanA.modelThom_base` / `modelThom_step`) as *definitions*, so that the naturality of
the resulting class in the base can be proved.  The propositional induction
`Work.Thom.CleanA.ModelThom` only produces an existential, hence a `Classical.choose` of a class that
depends on the type of the base; here instead

* `Work.Thom.stepDisc`, `Work.Thom.stepSph` are the transfer of the model class to the disc pair and
  then to the sphere-bundle pair (both by `Classical.choose` of the *characterising* preimage, which
  is unique, together with the explicit equation `Work.Thom.stepSph_spec` pinning it down);
* `Work.Thom.step` is the inductive step, `δ ∘ relToAbs` of the transferred class, written in the
  form that is functorial in the base (`CohMap` of the homeomorphism `prodSubsetHomeoA.symm`);
* `Work.Thom.Mn` is the resulting family, `Mn 0` being the rank-zero model class (the unit class in
  `H^0(B × ℝ⁰, B × S⁰)`, transported in from `(B × ℝ⁰, ∅)`).

The main consumers are `Work.Thom.step_natural` and `Work.Thom.step_isModel`.
-/

open Work.Thom
open CategoryTheory

noncomputable section

namespace Work.Thom

/-- The inclusion `↥W × ℝⁿ → B × ℝⁿ` of the base `W ⊆ B`, written as in the statement of
`Work.Thom.naturalModelClass`. -/
def baseIncl (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ) :
    C(↥W × EuclideanSpace ℝ (Fin n), B × EuclideanSpace ℝ (Fin n)) :=
  ⟨fun p => (((p.1 : ↥W) : B), p.2),
    continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd⟩

/-- The sphere bundle of rank `n` over `B`, as a subset of `B × ℝⁿ`. -/
abbrev Sph (B : Type) [TopologicalSpace B] (n : ℕ) : Set (B × EuclideanSpace ℝ (Fin n)) :=
  {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n}

/-- The part of the sphere bundle of rank `n+1` lying over the lower region `mLower n`. -/
abbrev SphB (B : Type) [TopologicalSpace B] (n : ℕ) : Set (B × MSph (n+1)) :=
  {p : B × MSph (n+1) | p.2.1 ∈ mLower n}

/-- The sphere of the ball bundle of rank `n`, as a subset of `B × MBall n`. -/
abbrev DiscB (B : Type) [TopologicalSpace B] (n : ℕ) : Set (B × MBall n) :=
  {q : B × MBall n | q.2.1 ∈ mSph n}

/-- Step A of the model induction: the transfer of the model class of rank `n` to the disc pair
`(B × Dⁿ, B × Sⁿ⁻¹)`. -/
noncomputable def stepDisc (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    RelCoh ℤ n (B × MBall n) (DiscB B n) :=
  (relCohMap (CleanA.discFullMap B n) (DiscB B n) (Sph B n) (CleanA.discFullMap_mem B n) ℤ n).hom τ

/-- Step B of the model induction: the transfer of the disc-pair class to the sphere-bundle pair
`(B × Sⁿ, B × lower n)` along the cap map, as the (unique) preimage under the cap map. -/
noncomputable def stepSph (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    RelCoh ℤ n (B × MSph (n+1)) (SphB B n) :=
  Classical.choose ((CleanA.capRelCohIso B n n).2 (stepDisc B n τ))

/-- The characterising equation of `Work.Thom.stepSph`. -/
theorem stepSph_spec (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    (relCohMap (capMapPairSph B n) (DiscB B n) (SphB B n)
      (CleanA.capMapPairSph_mem_mLower n) ℤ n).hom (stepSph B n τ) = stepDisc B n τ :=
  Classical.choose_spec ((CleanA.capRelCohIso B n n).2 (stepDisc B n τ))

/-- **The inductive step of the model induction.**  From a class of the pair `(B × ℝⁿ, B × Sⁿ⁻¹)`
we produce a class of `(B × ℝⁿ⁺¹, B × Sⁿ)`: the cap map identifies the sphere-bundle pair of rank
`n+1` with the disc pair of rank `n`, and the connecting homomorphism of the pair
`(B × ℝⁿ⁺¹, B × Sⁿ)` completes the suspension.  The class is written as
`δ ∘ relToAbs ∘ CohMap (prodSubsetHomeoA).symm`, which is functorial in the base. -/
noncomputable def step (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    RelCoh ℤ (n+1) (B × EuclideanSpace ℝ (Fin (n+1))) (Sph B (n+1)) :=
  (pairδC (Sph B (n+1)) n).hom
    ((CohMap (prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n+1))) (mSph (n+1))).symm ℤ n).hom
      ((relToAbs ℤ (SphB B n) n).hom (stepSph B n τ)))

/-- `Sph B 0` is the empty set. -/
theorem sph_zero_eq_empty (B : Type) [TopologicalSpace B] :
    Sph B 0 = (∅ : Set (B × EuclideanSpace ℝ (Fin 0))) := by
  ext p
  simp only [Sph, mSph, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  have h : p.2 = 0 := Subsingleton.elim _ _
  rw [h, norm_zero]
  norm_num

/-- The forgetful map `H^n(E,∅) → H^n(E)` is an isomorphism. -/
theorem bijective_relToAbs_empty {E : Type} [TopologicalSpace E] (n : ℕ) :
    Function.Bijective ((relToAbs ℤ (∅ : Set E) n).hom) := by
  haveI H : IsIso (relToAbs ℤ (∅ : Set E) n) :=
    Work.Cohomology.relComplex_empty_homology_iso (TopCat.of E) n
  exact ConcreteCategory.bijective_of_isIso _

/-- The forgetful map `H^0(B × ℝ⁰, B × S⁰) → H^0(B × ℝ⁰)` is an isomorphism. -/
theorem bijective_relToAbs_sphZero (B : Type) [TopologicalSpace B] :
    Function.Bijective ((relToAbs ℤ (Sph B 0) 0).hom) := by
  rw [sph_zero_eq_empty]
  exact bijective_relToAbs_empty 0

/-- The unit class of `H^0(B × ℝ⁰)`. -/
noncomputable def oneSphZero (B : Type) [TopologicalSpace B] :
    Coh ℤ 0 (B × EuclideanSpace ℝ (Fin 0)) :=
  Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (B × EuclideanSpace ℝ (Fin 0))))

/-- **The model class of the trivial bundle of rank `n` over `B`**, for every `n`, constructed by
the explicit induction: the rank-zero class is the unit class of `(B × ℝ⁰, B × S⁰)`, and each step
is `Work.Thom.step`. -/
noncomputable def Mn : (n : ℕ) → (B : Type) → [TopologicalSpace B] →
    RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)
  | 0, B, _ => Classical.choose ((bijective_relToAbs_sphZero B).2 (oneSphZero B))
  | n+1, B, _ => step B n (Mn n B)

/-- The characterising equation of the rank-zero model class. -/
theorem Mn_zero_spec (B : Type) [TopologicalSpace B] :
    (relToAbs ℤ (Sph B 0) 0).hom (Mn 0 B) = oneSphZero B :=
  Classical.choose_spec ((bijective_relToAbs_sphZero B).2 (oneSphZero B))

end Work.Thom
