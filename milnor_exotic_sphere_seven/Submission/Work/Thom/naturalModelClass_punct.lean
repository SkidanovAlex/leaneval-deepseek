import Mathlib
import Submission.Work.Thom.naturalModelClass
import Submission.Work.Thom.stepDefs
import Submission.Work.Thom.ATools

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-!
# The natural model class of the *punctured* trivial bundle

`Work.Thom.naturalModelClass` produces a family `Mn n` of model classes for the pair
`(B × ℝⁿ, B × Sⁿ⁻¹)` (the sphere-bundle pair), natural in the base `B`.  Here we transport it to the
pair `(B × ℝⁿ, B × (ℝⁿ∖0))` (the *punctured* pair): the inclusion of pairs
`(B × ℝⁿ, B × Sⁿ⁻¹) → (B × ℝⁿ, B × (ℝⁿ∖0))` is the identity on the total space, and it is a
homotopy equivalence of pairs (the sphere `Sⁿ⁻¹` is a deformation retract of `ℝⁿ ∖ 0` along the
radial retraction), so it induces an isomorphism `Work.Thom.bijective_relCohMap_spherePunctured` on
relative cohomology.

The class `Mpun n B` is defined as the unique preimage of `Mn n B` under this isomorphism.  The two
properties asked for in `Work.Thom.naturalModelClass_punct` are then

* the *model property*: since the mixed cup product is natural under maps of pairs
  (`Work.Thom.mixedCupC_pairNatural`), the cup map of the punctured pair is the cup map of the
  sphere pair conjugated by the isomorphism, hence bijective;
* *naturality in the base*: the isomorphism of pairs commutes with the base inclusion
  (`Work.Thom.relCohMap_compA`), and the preimage of a natural class under a natural bijection is
  natural.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- The punctured part `{p : B × ℝⁿ | p.2 ≠ 0}` of the total space of the trivial bundle of rank
`n` over `B`.  (This is the second member of the pair `(B × ℝⁿ, B × (ℝⁿ∖0))`.) -/
abbrev Punct (B : Type) [TopologicalSpace B] (n : ℕ) : Set (B × EuclideanSpace ℝ (Fin n)) :=
  {p | p.2 ≠ 0}

/-- The sphere part of the trivial bundle sits inside its punctured part. -/
theorem mem_Sph_punct (B : Type) [TopologicalSpace B] (n : ℕ) :
    ∀ p ∈ Sph B n, p ∈ Punct B n := by
  intro p hp
  simp only [Sph, mSph, Set.mem_ofPred_eq, Punct] at hp ⊢
  intro h0
  rw [h0, norm_zero] at hp
  exact zero_ne_one hp

/-- The base inclusion `↥W × ℝⁿ → B × ℝⁿ` carries the punctured part of `W` into that of `B`. -/
theorem mem_Punct_baseIncl (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ) :
    ∀ p ∈ Punct W n, baseIncl B W n p ∈ Punct B n := by
  intro p hp
  simp only [Punct] at hp ⊢
  exact hp

/-- The base inclusion `↥W × ℝⁿ → B × ℝⁿ` carries the sphere part of `W` into that of `B`. -/
theorem mem_Sph_baseIncl (B : Type) [TopologicalSpace B] (W : Set B) (n : ℕ) :
    ∀ p ∈ Sph W n, baseIncl B W n p ∈ Sph B n := by
  intro p hp
  simp only [Sph, mSph, Set.mem_ofPred_eq] at hp ⊢
  exact hp

/-- **The inclusion of the sphere-bundle pair into the punctured pair is an isomorphism on relative
cohomology**, in the normalised form with the canonical membership proofs used throughout this
file. -/
theorem bijective_jMap (B : Type) [TopologicalSpace B] (n m : ℕ) :
    Function.Bijective
      ((relCohMap (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n))) (Sph B n) (Punct B n)
        (mem_Sph_punct B n) ℤ m).hom) :=
  bijective_relCohMap_spherePunctured B n m

/-- **The model class of the punctured trivial bundle of rank `n` over `B`**: the preimage of the
sphere-bundle model class `Mn n B` under the isomorphism
`Work.Thom.bijective_jMap B n n` (equivalently, the image of `Mn n B` under the inverse
isomorphism). -/
noncomputable def Mpun (n : ℕ) (B : Type) [TopologicalSpace B] :
    RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n) :=
  Classical.choose ((bijective_jMap B n n).2 (Mn n B))

/-- The characterising equation of `Work.Thom.Mpun`. -/
theorem Mpun_spec (n : ℕ) (B : Type) [TopologicalSpace B] :
    (relCohMap (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n))) (Sph B n) (Punct B n)
      (mem_Sph_punct B n) ℤ n).hom (Mpun n B) = Mn n B :=
  Classical.choose_spec ((bijective_jMap B n n).2 (Mn n B))

/-- **Naturality of the pair inclusion `(B × ℝⁿ, B × Sⁿ⁻¹) → (B × ℝⁿ, B × (ℝⁿ∖0))`**: the
isomorphism on relative cohomology induced by it commutes with the restriction to a base `W ⊆ B`. -/
theorem pairIncl_natural (n : ℕ) (B : Type) [TopologicalSpace B] (W : Set B) (m : ℕ)
    (a : RelCoh ℤ m (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    (relCohMap (ContinuousMap.id (↥W × EuclideanSpace ℝ (Fin n))) (Sph W n) (Punct W n)
        (mem_Sph_punct W n) ℤ m).hom
      ((relCohMap (baseIncl B W n) (Punct W n) (Punct B n) (mem_Punct_baseIncl B W n) ℤ m).hom a)
    = (relCohMap (baseIncl B W n) (Sph W n) (Sph B n) (mem_Sph_baseIncl B W n) ℤ m).hom
        ((relCohMap (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n))) (Sph B n) (Punct B n)
          (mem_Sph_punct B n) ℤ m).hom a) := by
  rw [relCohMap_compA_apply (Sph W n) (Punct W n) (Punct B n)
        (ContinuousMap.id (↥W × EuclideanSpace ℝ (Fin n))) (baseIncl B W n)
        (mem_Sph_punct W n) (mem_Punct_baseIncl B W n)
        (fun x hx => mem_Punct_baseIncl B W n x (mem_Sph_punct W n x hx)) ℤ m a]
  rw [relCohMap_compA_apply (Sph W n) (Sph B n) (Punct B n)
        (baseIncl B W n) (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
        (mem_Sph_baseIncl B W n) (mem_Sph_punct B n)
        (fun x hx => mem_Sph_punct B n (baseIncl B W n x) (mem_Sph_baseIncl B W n x hx)) ℤ m a]
  simp only [ContinuousMap.comp_id, ContinuousMap.id_comp]

/-- **The punctured model class is natural in the base.** -/
theorem Mpun_natural (n : ℕ) (B : Type) [TopologicalSpace B] (W : Set B) :
    (relCohMap (baseIncl B W n)
      {p : ↥W × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
      (fun _ hp => hp) ℤ n).hom (Mpun n B) = Mpun n W := by
  have hprP : relCohMap (baseIncl B W n)
        {p : ↥W × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
        {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} (fun _ hp => hp) ℤ n
      = relCohMap (baseIncl B W n) (Punct W n) (Punct B n)
          (mem_Punct_baseIncl B W n) ℤ n :=
    relCohMap_hcongrA _ _ _ _ _ ℤ n
  have hprS : relCohMap (baseIncl B W n) (Sph W n) (Sph B n) (mem_Sph_baseIncl B W n) ℤ n
      = relCohMap (baseIncl B W n) (Sph W n) (Sph B n) (fun _ h => h) ℤ n :=
    relCohMap_hcongrA _ _ _ _ _ ℤ n
  rw [hprP]
  apply (bijective_jMap W n n).1
  rw [pairIncl_natural n B W n (Mpun n B), Mpun_spec n B, Mpun_spec n W]
  rw [hprS, Mn_natural n B W]

/-- **The punctured model class is a model class**: cupping with it is a bijection. -/
theorem Mpun_isModel (n : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ) :
    Function.Bijective (fun x : Coh ℤ k B =>
      (mixedCupC ℤ (Punct B n) k n) ((CohMap (projFstA B n) ℤ k).hom x) (Mpun n B)) := by
  have hkey : ∀ x : Coh ℤ k B,
      (relCohMap (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n))) (Sph B n) (Punct B n)
          (mem_Sph_punct B n) ℤ (k + n)).hom
        ((mixedCupC ℤ (Punct B n) k n) ((CohMap (projFstA B n) ℤ k).hom x) (Mpun n B))
      = (mixedCupC ℤ (Sph B n) k n) ((CohMap (projFstA B n) ℤ k).hom x) (Mn n B) := by
    intro x
    have h := mixedCupC_pairNatural (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
      (Sph B n) (Punct B n) (mem_Sph_punct B n) k n
      ((CohMap (projFstA B n) ℤ k).hom x) (Mpun n B)
    simpa only [CohMap_id, ModuleCat.hom_id, LinearMap.id_apply, Mpun_spec n B] using h
  have hbijS := Mn_isModel n B k
  constructor
  · intro x y hxy
    have hxy' : (mixedCupC ℤ (Punct B n) k n) ((CohMap (projFstA B n) ℤ k).hom x) (Mpun n B)
        = (mixedCupC ℤ (Punct B n) k n) ((CohMap (projFstA B n) ℤ k).hom y) (Mpun n B) := hxy
    have h2 : (mixedCupC ℤ (Sph B n) k n) ((CohMap (projFstA B n) ℤ k).hom x) (Mn n B)
        = (mixedCupC ℤ (Sph B n) k n) ((CohMap (projFstA B n) ℤ k).hom y) (Mn n B) := by
      rw [← hkey x, ← hkey y, hxy']
    exact hbijS.1 h2
  · intro z
    obtain ⟨x, hx⟩ := hbijS.2 ((relCohMap (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
      (Sph B n) (Punct B n) (mem_Sph_punct B n) ℤ (k + n)).hom z)
    refine ⟨x, ?_⟩
    apply (bijective_jMap B n (k + n)).1
    exact (hkey x).trans hx

end

theorem naturalModelClass_punct (n : ℕ) (hn : 1 ≤ n) :
    ∃ M : (B : Type) → [TopologicalSpace B] →
        RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0},
      (∀ (B : Type) [TopologicalSpace B], ∀ k, Function.Bijective (fun x : Coh ℤ k B =>
        (mixedCupC ℤ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} k n)
          ((CohMap (Work.Thom.projFstA B n) ℤ k).hom x) (M B))) ∧
      (∀ (B : Type) [TopologicalSpace B] (W : Set B),
        (relCohMap (Work.Thom.baseIncl B W n)
          {p : ↥W × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
          {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
          (fun _ hp => hp) ℤ n).hom (M B) = M W) := by
  have _hn : 1 ≤ n := hn
  exact ⟨fun B _ => Mpun n B, fun B _ k => Mpun_isModel n B k, fun B _ W => Mpun_natural n B W⟩

end Work.Thom
