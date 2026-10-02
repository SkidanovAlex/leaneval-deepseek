import Mathlib
import Submission.Work.Thom.step_natural
import Submission.Work.Thom.naturalModelClass_punct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Changing the base of the trivial bundle over an arbitrary continuous map

The model class `Work.Thom.Mn n B` of the pair `(B × ℝⁿ, B × Sⁿ⁻¹)` and its punctured companion
`Work.Thom.Mpun n B` are natural in the base.  The files `Submission/Work/Thom/step_natural.lean`
and `Submission/Work/Thom/naturalModelClass_punct.lean` prove the naturality only for the
*inclusions* `↥W × ℝⁿ → B × ℝⁿ` induced by a subset `W ⊆ B`.  The present file collects the
elementary ingredients needed to run the *same* induction for an arbitrary continuous map
`g : C(B', B)`, with the induced map

`prodMapA g F : B' × F → B × F`,  `(b, v) ↦ (g b, v)`

on the total spaces.

Concretely, this file provides

* `Work.Thom.prodMapA` — the map `(b, v) ↦ (g b, v)` (`g` on the base, the identity on the fibre);
* the three commutation identities saying that `prodMapA` commutes with all the structural maps of
  the model induction (`CleanA.discFullMap`, `capMapPairSph`, `prodSubsetHomeoA`), so that the
  proofs of `stepDisc_natural` / `stepSph_natural` / `step_natural` transpose verbatim;
* the two "squares" comparing the pullback of a *punctured* class along `prodMapA g` with the
  pullback of the corresponding *sphere-pair* class — the bridge between `Mn` and `Mpun`.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- **The base change of a product along `g`**: the map `B' × F → B × F`, `(b, v) ↦ (g b, v)`.
It is `g` on the base and the identity on the fibre. -/
abbrev prodMapA {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] (g : C(B', B))
    (F : Type) [TopologicalSpace F] : C(B' × F, B × F) :=
  ⟨fun p => (g p.1, p.2), g.continuous.comp continuous_fst |>.prodMk continuous_snd⟩

@[simp] theorem prodMapA_apply {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (F : Type) [TopologicalSpace F] (p : B' × F) :
    prodMapA g F p = (g p.1, p.2) := rfl

/-- `prodMapA` is the identity when the base map is. -/
@[simp] theorem prodMapA_id (B : Type) [TopologicalSpace B] (F : Type) [TopologicalSpace F] :
    prodMapA (ContinuousMap.id B) F = ContinuousMap.id (B × F) := by
  apply ContinuousMap.ext; intro p; rfl

/-- `prodMapA` is compatible with composition of the base maps. -/
theorem prodMapA_comp {B B' B'' : Type} [TopologicalSpace B] [TopologicalSpace B']
    [TopologicalSpace B''] (g : C(B', B)) (h : C(B'', B')) (F : Type) [TopologicalSpace F] :
    (prodMapA g F).comp (prodMapA h F) = prodMapA (g.comp h) F := by
  apply ContinuousMap.ext; intro p; rfl

/-! ## Commutation with the structural maps of the model induction -/

/-- The disc-transfer map `CleanA.discFullMap` commutes with the base change. -/
theorem discFullMap_comp_prodMapA {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ) :
    (CleanA.discFullMap B n).comp (prodMapA g (MBall n))
      = (prodMapA g (EuclideanSpace ℝ (Fin n))).comp (CleanA.discFullMap B' n) := by
  apply ContinuousMap.ext; intro p; rfl

/-- The cap map `capMapPairSph` commutes with the base change. -/
theorem capMapPairSph_comp_prodMapA {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ) :
    (capMapPairSph B n).comp (prodMapA g (MBall n))
      = (prodMapA g (MSph (n + 1))).comp (capMapPairSph B' n) := by
  apply ContinuousMap.ext; intro p; rfl

/-- The homeomorphism `prodSubsetHomeoA.symm` commutes with the base change. -/
theorem prodSubsetHomeoA_symm_comp_prodMapA {B B' : Type} [TopologicalSpace B]
    [TopologicalSpace B'] (g : C(B', B)) (n : ℕ) :
    (prodMapA g (MSph (n + 1))).comp
      ((prodSubsetHomeoA B' (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1))).symm :
        C(↥{p : B' × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)}, B' × MSph (n + 1)))
      = ((prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1))).symm :
        C(↥{p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)}, B × MSph (n + 1))).comp
        (restrictMap (prodMapA g (EuclideanSpace ℝ (Fin (n + 1))))
          (Sph B' (n + 1)) (Sph B (n + 1)) (fun _ h => h)) := by
  apply ContinuousMap.ext; intro p; rfl

/-- The restricted base change on the sphere pairs is the restriction of `prodMapA`. -/
theorem restrictMap_prodMapA_sph {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ) :
    restrictMap (prodMapA g (EuclideanSpace ℝ (Fin n))) (Sph B' n) (Sph B n) (fun _ h => h)
      = (⟨fun p : ↥(Sph B' n) => (⟨(g p.1.1, p.1.2), p.2⟩ : ↥(Sph B n)),
          Continuous.subtype_mk ((g.continuous.comp
            (continuous_fst.comp continuous_subtype_val)).prodMk
            (continuous_snd.comp continuous_subtype_val)) (fun p => p.2)⟩ :
        C(↥(Sph B' n), ↥(Sph B n))) := rfl

/-! ## The relation between the punctured and the sphere-bundle model classes -/

/-- **The pair inclusion commutes with the base change**: pulling a punctured class back along
`prodMapA g` and then applying the isomorphism
`(B × ℝⁿ, B × Sⁿ⁻¹) → (B × ℝⁿ, B × (ℝⁿ∖0))` gives the same as applying the isomorphism first (over
`B`) and then pulling back along `prodMapA g` as a map of sphere-bundle pairs. -/
theorem jMap_comp_prodMapA_punct {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ)
    (x : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    (relCohMap (ContinuousMap.id (B' × EuclideanSpace ℝ (Fin n))) (Sph B' n) (Punct B' n)
      (mem_Sph_punct B' n) ℤ n).hom
      ((relCohMap (prodMapA g (EuclideanSpace ℝ (Fin n))) (Punct B' n) (Punct B n)
        (fun _ hp => hp) ℤ n).hom x)
    = (relCohMap (prodMapA g (EuclideanSpace ℝ (Fin n))) (Sph B' n) (Punct B n)
        (fun y hy => mem_Sph_punct B' n y hy) ℤ n).hom x := by
  rw [relCohMap_compA_apply (Sph B' n) (Punct B' n) (Punct B n)
        (ContinuousMap.id (B' × EuclideanSpace ℝ (Fin n)))
        (prodMapA g (EuclideanSpace ℝ (Fin n)))
        (mem_Sph_punct B' n) (fun _ hp => hp) (fun y hy => mem_Sph_punct B' n y hy) ℤ n x]
  rw [relCohMap_congrA (Sph B' n) (Punct B n)
      (ContinuousMap.comp_id (prodMapA g (EuclideanSpace ℝ (Fin n))))
      (fun y hy => mem_Sph_punct B' n y hy) (fun y hy => mem_Sph_punct B' n y hy) ℤ n]

/-- **The other square**: pulling a punctured class back along `prodMapA g` (as a map of sphere
pairs into the punctured pair) equals pulling its image under the isomorphism back as a map of
sphere-bundle pairs. -/
theorem prodMapA_punct_eq_prodMapA_sph_comp_jMap {B B' : Type} [TopologicalSpace B]
    [TopologicalSpace B'] (g : C(B', B)) (n : ℕ)
    (x : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    (relCohMap (prodMapA g (EuclideanSpace ℝ (Fin n))) (Sph B' n) (Punct B n)
        (fun y hy => mem_Sph_punct B' n y hy) ℤ n).hom x
    = (relCohMap (prodMapA g (EuclideanSpace ℝ (Fin n))) (Sph B' n) (Sph B n)
        (fun _ h => h) ℤ n).hom
        ((relCohMap (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n))) (Sph B n) (Punct B n)
          (mem_Sph_punct B n) ℤ n).hom x) := by
  rw [relCohMap_compA_apply (Sph B' n) (Sph B n) (Punct B n)
        (prodMapA g (EuclideanSpace ℝ (Fin n)))
        (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
        (fun _ h => h) (mem_Sph_punct B n)
        (fun y hy => mem_Sph_punct B' n y hy) ℤ n x]
  rw [relCohMap_congrA (Sph B' n) (Punct B n)
      (ContinuousMap.id_comp (prodMapA g (EuclideanSpace ℝ (Fin n))))
      (fun y hy => mem_Sph_punct B' n y hy) (fun y hy => mem_Sph_punct B' n y hy) ℤ n]

end

end Work.Thom
