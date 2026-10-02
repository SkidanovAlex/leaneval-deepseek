import Mathlib
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.tautQuotientCore_comap
import Submission.Work.Thom.tautQuotientComap
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.exists_pieceMap
import Submission.Work.Thom.pieceMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The total-space map of a pullback, and the naturality of the Gysin descent

For a real bundle `Z` over `B` and `f : C(B', B)`, the pullback `bundleComap Z f` maps to `Z` by
`⟨x, v⟩ ↦ ⟨f x, v⟩`; `Work.Thom.totalMap` is that map on total spaces.  It carries the complement of
the zero section of the pullback into the complement of the zero section of `Z`, so it induces a map
of the Thom pairs.

The main result here is `Work.Thom.gysin_descent_square`: the Gysin descent
`π^* : H^k(B) → H^k(E∖0)` commutes with the pullback,

  `d_{f^*Z} ∘ f^* = (punctMap Z f)^* ∘ d_Z`,

which is `Work.Thom.descent_symm_general` in the inverse form used by the Chern recursion: the
*inverse* of the descent of the pullback is the pullback of the inverse of the descent.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']

/-- **The total-space map of a pullback**: `⟨x, v⟩ ↦ ⟨f x, v⟩`, as a continuous map of total
spaces. -/
def totalMap {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (f : C(B', B)) : C((bundleComap Z f).TotalSpace, Z.TotalSpace) :=
  ⟨fun p => ⟨f p.1, p.2⟩,
    continuous_totalSpaceMap (bundleComap Z f) Z f
      (fun i => bundleComap_baseSet Z f i)
      (fun x i => by simp only [bundleComap_indexAt, bundleComap_coordChange])⟩

/-- The defining formula of `Work.Thom.totalMap`. -/
theorem totalMap_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (f : C(B', B)) (p : (bundleComap Z f).TotalSpace) :
    (totalMap Z f p : Z.TotalSpace) = (⟨f p.1, p.2⟩ : Z.TotalSpace) := rfl

/-- The total-space map carries the complement of the zero section to the complement of the zero
section. -/
theorem totalMap_mem_zeroComplement {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (f : C(B', B)) :
    ∀ p ∈ zeroComplement (bundleComap Z f), totalMap Z f p ∈ zeroComplement Z :=
  fun _ hp => hp


/-- **The total-space map of the pullback of a complex bundle**, on the side of
`realification (bundleComap Z f)` (whose topology is the one carried by the Chern recursion). -/
def totalMapR {m : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    C((realification (bundleComap Z f)).TotalSpace, (realification Z).TotalSpace) :=
  ⟨fun p => ⟨f p.1, p.2⟩,
    continuous_totalSpaceMap (realification (bundleComap Z f)) (realification Z) f
      (fun i => by rw [realification_baseSet, bundleComap_baseSet, realification_baseSet])
      (fun x i => by
        apply ContinuousLinearMap.ext; intro v
        simp only [realification_coordChange, realification_indexAt, bundleComap_coordChange,
          bundleComap_indexAt])⟩

/-- The defining formula of `Work.Thom.totalMapR`. -/
theorem totalMapR_apply {m : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B))
    (p : (realification (bundleComap Z f)).TotalSpace) :
    (totalMapR Z f p : (realification Z).TotalSpace) =
      (⟨f p.1, p.2⟩ : (realification Z).TotalSpace) := rfl

/-- The total-space map carries the complement of the zero section to the complement of the zero
section. -/
theorem totalMapR_mem_zeroComplement {m : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    ∀ p ∈ zeroComplement (realification (bundleComap Z f)), totalMapR Z f p ∈ zeroComplement (realification Z) :=
  fun _ hp => hp



/-- The product-with-identity map `(x, v) ↦ (g x, v)` induced by a continuous base map. -/
def baseMap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] (g : C(B', B)) (n : ℕ) :
    C(B' × EuclideanSpace ℝ (Fin n), B × EuclideanSpace ℝ (Fin n)) :=
  ⟨fun p => (g p.1, p.2), g.continuous.comp continuous_fst |>.prodMk continuous_snd⟩

@[simp] theorem baseMap_apply {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ) (p : B' × EuclideanSpace ℝ (Fin n)) :
    baseMap g n p = (g p.1, p.2) := rfl

/-- **The map of the pieces over `W' ⊆ B'` and `W ⊆ B` on the realification side**: on underlying
points, `q ↦ (f q.1.1, q.1.2)`.  The bundle on the left is `realification (bundleComap Z f)` (the
one the Chern recursion sees), whose topology is that carried by `Work.Thom.totalMapR`. -/
def pieceMapR {m : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B))
    {W : Set B} {W' : Set B'} (hWf : ∀ x ∈ W', f x ∈ W) :
    C(↥((realification (bundleComap Z f)).proj ⁻¹' W'), ↥((realification Z).proj ⁻¹' W)) :=
  ⟨fun q => ⟨totalMapR Z f q.1, hWf q.1.1 q.2⟩,
    ((totalMapR Z f).continuous.comp continuous_subtype_val).subtype_mk
      (fun q => hWf q.1.1 q.2)⟩

/-- The defining formula of `Work.Thom.pieceMapR`. -/
theorem pieceMapR_apply {m : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B))
    {W : Set B} {W' : Set B'} (hWf : ∀ x ∈ W', f x ∈ W)
    (q : ↥((realification (bundleComap Z f)).proj ⁻¹' W')) :
    (pieceMapR Z f hWf q : (realification Z).TotalSpace) =
      (⟨f q.1.1, q.1.2⟩ : (realification Z).TotalSpace) := rfl

/-- The memberships of the pieces: `pieceMapR` carries `pieceZero` to `pieceZero`. -/
theorem pieceMapR_mem {m : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B))
    {W : Set B} {W' : Set B'} (hWf : ∀ x ∈ W', f x ∈ W) :
    ∀ q ∈ pieceZero (realification (bundleComap Z f)) W',
      pieceMapR Z f hWf q ∈ pieceZero (realification Z) W := by
  intro q hq
  show (show EuclideanSpace ℂ (Fin m) from
      ((pieceMapR Z f hWf q : (realification Z).TotalSpace)).2) ≠ 0
  have h1 : (show EuclideanSpace ℂ (Fin m) from
      ((pieceMapR Z f hWf q : (realification Z).TotalSpace)).2)
      = (show EuclideanSpace ℂ (Fin m) from q.1.2) := rfl
  rw [h1]
  exact hq

/-- The two composites of the pullback diagram of total spaces over `f` and the map of punctured
total spaces agree. -/
theorem comp_totalMap_punctMap {m : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (f : C(B', B)) :
    f.comp ((bundleProj (realification (bundleComap Z f))).comp
        (subtypeMap (zeroComplement (realification (bundleComap Z f)))))
      = ((bundleProj (realification Z)).comp
        (subtypeMap (zeroComplement (realification Z)))).comp (punctMap Z f) := by
  apply ContinuousMap.ext
  intro p
  simp only [ContinuousMap.comp_apply, bundleProj_apply, subtypeMap, ContinuousMap.coe_mk]
  rw [punctMap_apply]

/-- **The Gysin descent commutes with the pullback.**  For `x ∈ H^{2j}(B;ℤ)`,

  `(π_{f^*Z})^*(f^*(x)) = (punctMap Z f)^*((π_Z)^*(x))`,

i.e. pulling back `π_Z^*(x)` to the punctured total space of the pullback is the same as restricting
`π_{f^*Z}^*(f^*x)`.  Both sides are `(f ∘ π_{f^*Z})^*(x) = (π_Z ∘ punctMap)^*(x)`. -/
theorem gysin_descent_square {m j : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (f : C(B', B))
    (x : Coh ℤ (2 * j) B) :
    (CohMap ((bundleProj (realification (bundleComap Z f))).comp
        (subtypeMap (zeroComplement (realification (bundleComap Z f))))) ℤ (2 * j)).hom
      ((CohMap f ℤ (2 * j)).hom x)
    = (CohMap (punctMap Z f) ℤ (2 * j)).hom
      ((CohMap ((bundleProj (realification Z)).comp
        (subtypeMap (zeroComplement (realification Z)))) ℤ (2 * j)).hom x) := by
  rw [CohMap_comp_apply ((bundleProj (realification (bundleComap Z f))).comp
        (subtypeMap (zeroComplement (realification (bundleComap Z f))))) f ℤ (2*j) x,
      CohMap_comp_apply (punctMap Z f) ((bundleProj (realification Z)).comp
        (subtypeMap (zeroComplement (realification Z)))) ℤ (2*j) x,
      comp_totalMap_punctMap Z f]

/-- **The inverse Gysin descent commutes with the pullback** (the form used by the Chern
recursion): if `eX`, `eZ` are the descent isomorphisms of the pullback and of `Z` (as linear
equivalences whose underlying maps are `(π_{f^*Z})^*` and `(π_Z)^*`), then

  `eX⁻¹ ((punctMap Z f)^* y) = f^*(eZ⁻¹ y)`.

The identification of the underlying maps of `eX`, `eZ` with the pullbacks is the hypothesis
(they hold by `rfl` for `LinearEquiv.ofBijective`). -/
theorem descent_symm_general {m j : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (f : C(B', B))
    (eX : Coh ℤ (2*j) B' ≃ₗ[ℤ] Coh ℤ (2*j)
      ↥(zeroComplement (realification (bundleComap Z f))))
    (eZ : Coh ℤ (2*j) B ≃ₗ[ℤ] Coh ℤ (2*j) ↥(zeroComplement (realification Z)))
    (hX : ⇑eX = ⇑((CohMap ((bundleProj (realification (bundleComap Z f))).comp
        (subtypeMap (zeroComplement (realification (bundleComap Z f))))) ℤ (2*j)).hom))
    (hZ : ⇑eZ = ⇑((CohMap ((bundleProj (realification Z)).comp
        (subtypeMap (zeroComplement (realification Z)))) ℤ (2*j)).hom))
    (y : Coh ℤ (2*j) ↥(zeroComplement (realification Z))) :
    eX.symm ((CohMap (punctMap Z f) ℤ (2*j)).hom y)
      = (CohMap f ℤ (2*j)).hom (eZ.symm y) := by
  have key : eX ((CohMap f ℤ (2*j)).hom (eZ.symm y))
      = (CohMap (punctMap Z f) ℤ (2*j)).hom y := by
    rw [show eX ((CohMap f ℤ (2*j)).hom (eZ.symm y))
        = (CohMap ((bundleProj (realification (bundleComap Z f))).comp
            (subtypeMap (zeroComplement (realification (bundleComap Z f))))) ℤ (2*j)).hom
            ((CohMap f ℤ (2*j)).hom (eZ.symm y)) from by rw [← hX]]
    rw [CohMap_comp_apply ((bundleProj (realification (bundleComap Z f))).comp
        (subtypeMap (zeroComplement (realification (bundleComap Z f))))) f ℤ (2*j) (eZ.symm y),
      comp_totalMap_punctMap Z f,
      ← CohMap_comp_apply (punctMap Z f) ((bundleProj (realification Z)).comp
        (subtypeMap (zeroComplement (realification Z)))) ℤ (2*j) (eZ.symm y)]
    rw [show (CohMap ((bundleProj (realification Z)).comp
        (subtypeMap (zeroComplement (realification Z)))) ℤ (2*j)).hom (eZ.symm y)
        = eZ (eZ.symm y) from by rw [hZ]]
    rw [LinearEquiv.apply_symm_apply]
  rw [← key, LinearEquiv.symm_apply_apply]

end

end Work.Thom
