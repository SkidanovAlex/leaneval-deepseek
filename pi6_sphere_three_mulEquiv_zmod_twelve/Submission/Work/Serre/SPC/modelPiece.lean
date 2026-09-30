import Mathlib
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.Serre.CellStep.Model
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.CellStep.ModelReduction
import Submission.Work.Serre.SPC.radial
import Submission.Work.Serre.SPC.discStrong
import Submission.Work.Cohomology.relChainsMapOf_comp

set_option synthInstance.maxHeartbeats 400000


/-!
# The model per-cell map in "whole pullback" form

For a Serre fibration `p : E → B` and a map `τ : D^{n+2} → B` from the model cell, `pmMap n p τ W`
is the map of pairs `(τ^*E, τ^*E|_W) → (D^{n+2}, W)` induced by the projection, with the *whole*
pullback as the total space of the domain (so that the ambient space is fixed and the disc
statement applies directly).

The strong statement `pmMap_strong` is the chain of relative-part compressions
`csSh → csS → csQ → S^{n+1}`, each a `relCokerMap` (a quasi-isomorphism by the radial compression
facts of `SPC/radial.lean`), followed by `discPairStrong`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC

noncomputable section

open Work.RatHurewicz

/-- **The model per-cell map in "whole pullback" form.** -/
noncomputable def pmMap (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(cellDisk n, B)) (W : Set (cellDisk n)) :
    Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.discPre n p τ W) ⟶
      Work.Cohomology.relChains (TopCat.of (cellDisk n)) W :=
  Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback p τ))
    (TopCat.of (cellDisk n)) (Work.Serre.discPre n p τ W) W
    (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
    (TopCat.ofHom ⟨fun x => ⟨Work.StemsB.pullbackSnd p τ x.1, x.2⟩, by
      exact Continuous.subtype_mk
        ((Work.StemsB.pullbackSnd p τ).continuous.comp continuous_subtype_val) (fun x => x.2)⟩)
    (by ext x; rfl)

/-- At the boundary sphere, `pmMap` is `discPairMap`. -/
theorem pmMap_cellSphereSet (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(cellDisk n, B)) :
    pmMap n p τ (Work.Serre.cellSphereSet n) = Work.Serre.discPairMap n p τ := rfl

/-- **The `relCokerMap` square of the model maps**: shrinking the relative part commutes with the
pair maps. -/
theorem pmMap_square (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(cellDisk n, B)) {W₀ W₁ : Set (cellDisk n)} (h : W₀ ⊆ W₁) :
    Work.Cohomology.relCokerMap (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.discPre n p τ W₀) (Work.Serre.discPre n p τ W₁) (fun x hx => h hx)
      ≫ pmMap n p τ W₁
    = pmMap n p τ W₀
      ≫ Work.Cohomology.relCokerMap (TopCat.of (cellDisk n)) W₀ W₁ h := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains
    (TopCat.of (Work.StemsB.Pullback p τ)) (Work.Serre.discPre n p τ W₀)))).mp
  show cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.discPre n p τ W₀))
      ≫ (Work.Cohomology.relCokerMap (TopCat.of (Work.StemsB.Pullback p τ))
          (Work.Serre.discPre n p τ W₀) (Work.Serre.discPre n p τ W₁) (fun x hx => h hx)
        ≫ pmMap n p τ W₁)
    = cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.discPre n p τ W₀))
      ≫ (pmMap n p τ W₀ ≫ Work.Cohomology.relCokerMap (TopCat.of (cellDisk n)) W₀ W₁ h)
  have hpm (W : Set (cellDisk n)) :
      cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p τ))
          (Work.Serre.discPre n p τ W)) ≫ pmMap n p τ W
        = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p τ))
            (TopCat.of (cellDisk n)) (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (cellDisk n)) W) := by
    unfold pmMap Work.Cohomology.relChainsMapOf
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  rw [← Category.assoc, Work.Cohomology.relCokerMap_comp_π]
  calc cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.discPre n p τ W₁)) ≫ pmMap n p τ W₁
      = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p τ))
          (TopCat.of (cellDisk n)) (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (cellDisk n)) W₁) := hpm W₁
    _ = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p τ))
          (TopCat.of (cellDisk n)) (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
        ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of (cellDisk n)) W₀)
          ≫ Work.Cohomology.relCokerMap (TopCat.of (cellDisk n)) W₀ W₁ h) := by
        rw [Work.Cohomology.relCokerMap_comp_π]
    _ = (Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p τ))
          (TopCat.of (cellDisk n)) (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (cellDisk n)) W₀))
          ≫ Work.Cohomology.relCokerMap (TopCat.of (cellDisk n)) W₀ W₁ h := by
        rw [Category.assoc]
    _ = (cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p τ))
          (Work.Serre.discPre n p τ W₀)) ≫ pmMap n p τ W₀)
          ≫ Work.Cohomology.relCokerMap (TopCat.of (cellDisk n)) W₀ W₁ h := by rw [hpm W₀]
    _ = cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p τ))
          (Work.Serre.discPre n p τ W₀))
        ≫ (pmMap n p τ W₀
          ≫ Work.Cohomology.relCokerMap (TopCat.of (cellDisk n)) W₀ W₁ h) := by
        rw [Category.assoc]

/-- The set `csQ` of the model is the closed shell `{7/8 ≤ ‖x‖}`. -/
theorem csQ_eq_cellClosedShell (n : ℕ) :
    Work.Serre.csQ (n := n) = cellClosedShell n (7/8) := by
  ext x
  rw [Work.Serre.csQ, cellClosedShell, Set.mem_setOf_eq, Set.mem_setOf_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, norm_coe_le_one x⟩⟩

/-- The set `csS` of the model is the sphere of radius `7/8`. -/
theorem csS_eq (n : ℕ) :
    Work.Serre.csS (n := n) = {x : cellDisk n | ‖(x : CellVec n)‖ = 7/8} := rfl

/-- The boundary sphere of the model cell is contained in the closed shell. -/
theorem cellSphereSet_subset_closedShell (n : ℕ) :
    Work.Serre.cellSphereSet n ⊆ cellClosedShell n (7/8) := by
  intro x hx
  rw [Work.Serre.mem_cellSphereSet] at hx
  show (7:ℝ)/8 ≤ ‖((x : cellDisk n) : CellVec n)‖
  rw [hx]
  norm_num

/-- The sphere of radius `7/8` is contained in the closed shell. -/
theorem csS_subset_closedShell (n : ℕ) :
    Work.Serre.csS (n := n) ⊆ cellClosedShell n (7/8) := by
  intro x hx
  rw [Work.Serre.csS] at hx
  show (7:ℝ)/8 ≤ ‖((x : cellDisk n) : CellVec n)‖
  rw [hx]

/-- **Strong form of the model per-cell statement, in "whole pullback" form.** -/
theorem pmMap_strong (n : ℕ) :
    ∀ (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B] (p : C(E, B))
      (hp : Work.StemsB.IsSerreFibration p) (τ : C(cellDisk n, B)) (φ : ℕ),
      (∀ y : cellDisk n, ∀ j : ℕ, 0 < j → j < φ →
        IsZero ((Work.Cohomology.singularChains ℤ
          (TopCat.of (Work.StemsB.fibre p (τ y)))).homology j)) →
      (∀ y : cellDisk n,
        IsIso (TopCat.singularHomology₀ε
          (TopCat.of (Work.StemsB.fibre p (τ y))) (ModuleCat.of ℤ ℤ))) →
      (∀ i : ℕ, i < (n + 2) + φ →
        IsIso (HomologicalComplex.homologyMap (pmMap n p τ (Work.Serre.csSh (n := n))) i)) ∧
      Function.Surjective
        (HomologicalComplex.homologyMap (pmMap n p τ (Work.Serre.csSh (n := n)))
          ((n + 2) + φ)).hom := by
  intro E _ B _ p hp τ φ hfib h0
  have hq : Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd p τ) :=
    fun m => Work.StemsB.hasHLP_pullback p τ (hp m)
  -- the disc statement
  have hDisc := discPairStrong n E B p hp τ φ hfib h0
  rw [← pmMap_cellSphereSet] at hDisc
  -- the three relative-part steps, transferred through `pmMap_square`
  have hcsQ : Work.Serre.csQ (n := n) = cellClosedShell n (7/8) := csQ_eq_cellClosedShell n
  -- step data: for `W₀ ⊆ W₁`, the two `relCokerMap`s are quasi-isomorphisms
  have key (W₀ W₁ : Set (cellDisk n)) (h : W₀ ⊆ W₁)
      (hc : ∀ d, CompressRel ↥W₁ {x : ↥W₁ | (x : cellDisk n) ∈ W₀} d) (k : ℕ)
      (hZ : ∀ j, IsZero ((Work.Cohomology.relChains (TopCat.of ↥W₁)
        {x : ↥W₁ | (x : cellDisk n) ∈ W₀}).homology j)) :
      IsIso (HomologicalComplex.homologyMap (pmMap n p τ W₀) k) ↔
        IsIso (HomologicalComplex.homologyMap (pmMap n p τ W₁) k) := by
    haveI htot : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap (TopCat.of (Work.StemsB.Pullback p τ))
          (Work.Serre.discPre n p τ W₀) (Work.Serre.discPre n p τ W₁) (fun x hx => h hx)) k) :=
      Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of (Work.StemsB.Pullback p τ))
        (fun x hx => h hx)
        (fun j => Work.Serre.isZero_relChains_preimage_of_compress (Work.StemsB.pullbackSnd p τ)
          hq h hc j) k
    haveI hbase : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap (TopCat.of (cellDisk n)) W₀ W₁ h) k) :=
      Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of (cellDisk n)) h hZ k
    have hsq := congrArg (fun ψ => HomologicalComplex.homologyMap ψ k) (pmMap_square n p τ h)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    exact (isIso_iff_of_comm_square
      (h := HomologicalComplex.homologyMap (pmMap n p τ W₁) k)
      (f := HomologicalComplex.homologyMap (pmMap n p τ W₀) k)
      (u := HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
        (TopCat.of (Work.StemsB.Pullback p τ)) (Work.Serre.discPre n p τ W₀)
        (Work.Serre.discPre n p τ W₁) (fun x hx => h hx)) k)
      (v := HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
        (TopCat.of (cellDisk n)) W₀ W₁ h) k) hsq).symm
  have keysurj (W₀ W₁ : Set (cellDisk n)) (h : W₀ ⊆ W₁)
      (hc : ∀ d, CompressRel ↥W₁ {x : ↥W₁ | (x : cellDisk n) ∈ W₀} d) (k : ℕ)
      (hZ : ∀ j, IsZero ((Work.Cohomology.relChains (TopCat.of ↥W₁)
        {x : ↥W₁ | (x : cellDisk n) ∈ W₀}).homology j)) :
      Function.Surjective (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (pmMap n p τ W₀) k)) ↔
      Function.Surjective (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (pmMap n p τ W₁) k)) := by
    haveI htot : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap (TopCat.of (Work.StemsB.Pullback p τ))
          (Work.Serre.discPre n p τ W₀) (Work.Serre.discPre n p τ W₁) (fun x hx => h hx)) k) :=
      Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of (Work.StemsB.Pullback p τ))
        (fun x hx => h hx)
        (fun j => Work.Serre.isZero_relChains_preimage_of_compress (Work.StemsB.pullbackSnd p τ)
          hq h hc j) k
    haveI hbase : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap (TopCat.of (cellDisk n)) W₀ W₁ h) k) :=
      Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of (cellDisk n)) h hZ k
    have hsq := congrArg (fun ψ => HomologicalComplex.homologyMap ψ k) (pmMap_square n p τ h)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    exact (surjective_iff_of_comm_square
      (h := HomologicalComplex.homologyMap (pmMap n p τ W₁) k)
      (f := HomologicalComplex.homologyMap (pmMap n p τ W₀) k)
      (u := HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
        (TopCat.of (Work.StemsB.Pullback p τ)) (Work.Serre.discPre n p τ W₀)
        (Work.Serre.discPre n p τ W₁) (fun x hx => h hx)) k)
      (v := HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
        (TopCat.of (cellDisk n)) W₀ W₁ h) k) hsq).symm
  constructor
  · intro i hi
    have h1 : IsIso (HomologicalComplex.homologyMap
        (pmMap n p τ (cellClosedShell n (7/8))) i) :=
      (key (Work.Serre.cellSphereSet n) (cellClosedShell n (7/8))
        (cellSphereSet_subset_closedShell n)
        (fun d => compressRel_csQ_cellSphere n d) i
        (fun j => Work.Serre.isZero_relChains_of_compress (compressRel_csQ_cellSphere n) j)).mp
        (hDisc.1 i hi)
    have h2 : IsIso (HomologicalComplex.homologyMap (pmMap n p τ (Work.Serre.csS (n := n))) i) :=
      (key (Work.Serre.csS (n := n)) (cellClosedShell n (7/8)) (csS_subset_closedShell n)
        (fun d => compressRel_csQ_csS n d) i
        (fun j => Work.Serre.isZero_relChains_of_compress (compressRel_csQ_csS n) j)).mpr h1
    exact (key (Work.Serre.csS (n := n)) (Work.Serre.csSh (n := n))
      (fun x hx => Work.Serre.csS_subset_csSh hx)
      (fun d => compressRel_csSh_csS n d) i
      (fun j => Work.Serre.isZero_relChains_of_compress (compressRel_csSh_csS n) j)).mp h2
  · have h1 : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (pmMap n p τ (cellClosedShell n (7/8))) ((n + 2) + φ))) :=
      (keysurj (Work.Serre.cellSphereSet n) (cellClosedShell n (7/8))
        (cellSphereSet_subset_closedShell n) (fun d => compressRel_csQ_cellSphere n d)
        ((n + 2) + φ)
        (fun j => Work.Serre.isZero_relChains_of_compress (compressRel_csQ_cellSphere n) j)).mp
        hDisc.2
    have h2 : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (pmMap n p τ (Work.Serre.csS (n := n))) ((n + 2) + φ))) :=
      (keysurj (Work.Serre.csS (n := n)) (cellClosedShell n (7/8)) (csS_subset_closedShell n)
        (fun d => compressRel_csQ_csS n d) ((n + 2) + φ)
        (fun j => Work.Serre.isZero_relChains_of_compress (compressRel_csQ_csS n) j)).mpr h1
    exact (keysurj (Work.Serre.csS (n := n)) (Work.Serre.csSh (n := n))
      (fun x hx => Work.Serre.csS_subset_csSh hx)
      (fun d => compressRel_csSh_csS n d) ((n + 2) + φ)
      (fun j => Work.Serre.isZero_relChains_of_compress (compressRel_csSh_csS n) j)).mp h2

end

end Work.Serre.SPC
