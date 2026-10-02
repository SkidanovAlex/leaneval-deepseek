import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.StemsB.CylMapGen
import Submission.Work.StemsB.PairDeltaNaturalR
import Submission.Work.Serre.relCoh_concentrated_of_ratAcyclic
import Submission.Work.Serre.E2dFibre
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.Basic
import Submission.Work.Thom.relCohMap_comp
import Submission.Work.Thom.relCohMap_id
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Thom.Pair
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.StemsB.ThomRatShim

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-! ## Auxiliary: the map induced on the `A`-parts of a map of pairs -/

/-- The restriction of a continuous map `φ : F → F'` sending `A` into `A'`, as a continuous map
`A → A'`. -/
def apart {F F' : Type} [TopologicalSpace F] [TopologicalSpace F'] (φ : C(F, F'))
    (A : Set F) (A' : Set F') (h : ∀ x ∈ A, φ x ∈ A') : C(A, A') :=
  ⟨fun a => ⟨φ ↑a, h ↑a a.2⟩,
    Continuous.subtype_mk (φ.continuous.comp continuous_subtype_val) (fun a => h ↑a a.2)⟩

@[simp] theorem apart_apply {F F' : Type} [TopologicalSpace F] [TopologicalSpace F']
    (φ : C(F, F')) (A : Set F) (A' : Set F') (h : ∀ x ∈ A, φ x ∈ A') (a : A) :
    (apart φ A A' h a : F') = φ ↑a := rfl

/-- **The pullback along a homeomorphism is an isomorphism on cohomology** (with `ℚ`
coefficients, in every degree). -/
theorem isIso_cohMap_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) :
    CategoryTheory.IsIso (Work.Thom.CohMap (e : C(X, Y)) ℚ n) := by
  refine IsIso.mk ⟨Work.Thom.CohMap (e.symm : C(Y, X)) ℚ n, ?_, ?_⟩
  · rw [← Work.Thom.CohMap_comp]
    rw [show (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y from
      ContinuousMap.ext fun y => e.apply_symm_apply y]
    exact Work.Thom.CohMap_id (B := Y) ℚ n
  · rw [← Work.Thom.CohMap_comp]
    rw [show (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X from
      ContinuousMap.ext fun x => e.symm_apply_apply x]
    exact Work.Thom.CohMap_id (B := X) ℚ n

/-! ## The `δ`-argument: a map of pairs is an isomorphism on relative cohomology as soon as it is
one on the `A`-parts and both total spaces have vanishing cohomology in the relevant degrees. -/

/-- **A map of pairs `(F,A) → (F',A')` whose `A`-part is an isomorphism on `H^m` is an isomorphism
on `H^{m+1}(–,–)`** when `H^m` and `H^{m+1}` of both total spaces vanish.  The proof identifies the
two connecting maps `δ` (both are isomorphisms by `Work.Serre.pairδ_isIso_rat`) and uses the
naturality of `δ` (`Work.StemsB.pairDeltaNaturalR`). -/
theorem isIso_relCohMap_of_pairDelta {F F' : Type} [TopologicalSpace F] [TopologicalSpace F']
    (A : Set F) (A' : Set F') (φ : C(F, F')) (hφ : ∀ x ∈ A, φ x ∈ A') (m : ℕ)
    (h1 : CategoryTheory.Limits.IsZero (Work.Thom.Coh ℚ m F))
    (h2 : CategoryTheory.Limits.IsZero (Work.Thom.Coh ℚ (m + 1) F))
    (h1' : CategoryTheory.Limits.IsZero (Work.Thom.Coh ℚ m F'))
    (h2' : CategoryTheory.Limits.IsZero (Work.Thom.Coh ℚ (m + 1) F'))
    (hA : CategoryTheory.IsIso (Work.Thom.CohMap (apart φ A A' hφ) ℚ m)) :
    CategoryTheory.IsIso (Work.Thom.relCohMap φ A A' hφ ℚ (m + 1)) := by
  have hδ : CategoryTheory.IsIso (Work.Cohomology.pairδ ℚ (TopCat.of F) A m) :=
    Work.Serre.pairδ_isIso_rat (TopCat.of F) A m h2 h1
  have hδ' : CategoryTheory.IsIso (Work.Cohomology.pairδ ℚ (TopCat.of F') A' m) :=
    Work.Serre.pairδ_isIso_rat (TopCat.of F') A' m h2' h1'
  have hδbij : Function.Bijective (Work.Cohomology.pairδ ℚ (TopCat.of F) A m).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hδ
  have hδ'bij : Function.Bijective (Work.Cohomology.pairδ ℚ (TopCat.of F') A' m).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hδ'
  have hψbij : Function.Bijective (Work.Thom.CohMap (apart φ A A' hφ) ℚ m).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hA
  have hnat : ∀ y : Work.Thom.Coh ℚ m A',
      (Work.Thom.relCohMap φ A A' hφ ℚ (m + 1)).hom
          ((Work.Cohomology.pairδ ℚ (TopCat.of F') A' m).hom y) =
        (Work.Cohomology.pairδ ℚ (TopCat.of F) A m).hom
          ((Work.Thom.CohMap (apart φ A A' hφ) ℚ m).hom y) :=
    fun y => Work.StemsB.pairDeltaNaturalR ℚ φ A A' hφ m y
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨u, rfl⟩ := hδ'bij.2 x
    obtain ⟨v, rfl⟩ := hδ'bij.2 y
    rw [hnat u, hnat v] at hxy
    have huv : u = v := hψbij.1 (hδbij.1 hxy)
    rw [huv]
  · intro z
    obtain ⟨u, hu⟩ := hδbij.2 z
    obtain ⟨v, hv⟩ := hψbij.2 u
    exact ⟨(Work.Cohomology.pairδ ℚ (TopCat.of F') A' m).hom v, by rw [hnat v, hv, hu]⟩

/-! ## The map of mapping cylinders induced by the pullback along a path, and its fibres -/

variable {X B : Type} [TopologicalSpace X] [TopologicalSpace B]

/-- The canonical map of mapping cylinders induced by the pullback square of `q` along a path `γ`
(over the interval, with `γ` as the map of targets). -/
def cylPullMap (q : C(X, B)) (γ : C(unitInterval, B)) :
    C(Work.Serre.cyl (Work.StemsB.pullbackSnd q γ), Work.Serre.cyl q) :=
  Work.StemsB.cylMapGen (Work.StemsB.pullbackSnd q γ) q (Work.StemsB.pullbackFst q γ) γ
    (fun u => (u.2).symm)

/-- `cylPullMap` is compatible with the two retractions. -/
theorem cylPullMap_retract (q : C(X, B)) (γ : C(unitInterval, B))
    (y : Work.Serre.cyl (Work.StemsB.pullbackSnd q γ)) :
    Work.Serre.cylRetract q (cylPullMap q γ y) =
      γ (Work.Serre.cylRetract (Work.StemsB.pullbackSnd q γ) y) :=
  congrFun (congrArg DFunLike.coe (Work.StemsB.cylRetract_comp_cylMapGen
    (Work.StemsB.pullbackSnd q γ) q (Work.StemsB.pullbackFst q γ) γ (fun u => (u.2).symm))) y

/-- `cylPullMap` is compatible with the two bottom copies. -/
theorem cylPullMap_cylIncl (q : C(X, B)) (γ : C(unitInterval, B))
    (u : Work.StemsB.Pullback q γ) :
    cylPullMap q γ (Work.Serre.cylIncl (Work.StemsB.pullbackSnd q γ) u) =
      Work.Serre.cylIncl q (Work.StemsB.pullbackFst q γ u) :=
  congrFun (congrArg DFunLike.coe (Work.StemsB.cylIncl_comp_cylMapGen
    (Work.StemsB.pullbackSnd q γ) q (Work.StemsB.pullbackFst q γ) γ (fun u => (u.2).symm))) u

/-- The fibre of the cylinder retraction over `z₀`, as a set. -/
abbrev cylFibreSet (q : C(X, B)) (z₀ : B) : Set (Work.Serre.cyl q) :=
  (Work.Serre.cylRetract q) ⁻¹' {z₀}

/-- The bottom part of the fibre of the cylinder retraction over `z₀`. -/
abbrev cylFibreBotSet (q : C(X, B)) (z₀ : B) : Set ↥(cylFibreSet q z₀) :=
  {y | (y : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}

/-- The membership description of `cylFibreSet`. -/
@[simp] theorem mem_cylFibreSet {q : C(X, B)} {z₀ : B} {y : Work.Serre.cyl q} :
    y ∈ cylFibreSet q z₀ ↔ Work.Serre.cylRetract q y = z₀ := Iff.rfl

/-- `cylPullMap` carries the fibre over `b` into the fibre over `γ b`. -/
theorem cylPullMap_mem_cylFibreSet (q : C(X, B)) (γ : C(unitInterval, B)) (b : unitInterval)
    (y : Work.Serre.cyl (Work.StemsB.pullbackSnd q γ))
    (hy : y ∈ cylFibreSet (Work.StemsB.pullbackSnd q γ) b) :
    cylPullMap q γ y ∈ cylFibreSet q (γ b) := by
  show Work.Serre.cylRetract q (cylPullMap q γ y) = γ b
  rw [cylPullMap_retract q γ y]
  show γ (Work.Serre.cylRetract (Work.StemsB.pullbackSnd q γ) y) = γ b
  rw [show Work.Serre.cylRetract (Work.StemsB.pullbackSnd q γ) y = b from hy]

/-- The map induced by `cylPullMap` on the fibres of the two cylinder retractions. -/
def cylPullFibreMap (q : C(X, B)) (γ : C(unitInterval, B)) (b : unitInterval) :
    C(↥(cylFibreSet (Work.StemsB.pullbackSnd q γ) b),
      ↥(cylFibreSet q (γ b))) where
  toFun y := ⟨cylPullMap q γ (y : Work.Serre.cyl (Work.StemsB.pullbackSnd q γ)),
    cylPullMap_mem_cylFibreSet q γ b _ y.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((cylPullMap q γ).continuous.comp continuous_subtype_val)
    (fun y => cylPullMap_mem_cylFibreSet q γ b _ y.2)

theorem cylPullFibreMap_apply (q : C(X, B)) (γ : C(unitInterval, B)) (b : unitInterval)
    (y : ↥(cylFibreSet (Work.StemsB.pullbackSnd q γ) b)) :
    ((cylPullFibreMap q γ b y : ↥(cylFibreSet q (γ b))) : Work.Serre.cyl q) =
      cylPullMap q γ (y : Work.Serre.cyl (Work.StemsB.pullbackSnd q γ)) := rfl

/-- `cylPullMap` carries the bottom part of the fibre over `b` into the bottom part of the fibre
over `γ b`. -/
theorem cylPullMap_mem_cylFibreBotSet (q : C(X, B)) (γ : C(unitInterval, B)) (b : unitInterval)
    (y : ↥(cylFibreSet (Work.StemsB.pullbackSnd q γ) b))
    (hy : y ∈ cylFibreBotSet (Work.StemsB.pullbackSnd q γ) b) :
    cylPullFibreMap q γ b y ∈ cylFibreBotSet q (γ b) := by
  obtain ⟨u, hu⟩ := hy
  refine ⟨Work.StemsB.pullbackFst q γ u, ?_⟩
  rw [cylPullFibreMap_apply]
  rw [← hu, cylPullMap_cylIncl q γ u]

/-- The map induced by `cylPullMap` on the bottom parts of the two fibres. -/
def cylPullBotMap (q : C(X, B)) (γ : C(unitInterval, B)) (b : unitInterval) :
    C(↥(cylFibreBotSet (Work.StemsB.pullbackSnd q γ) b), ↥(cylFibreBotSet q (γ b))) where
  toFun y := ⟨cylPullFibreMap q γ b (y : ↥(cylFibreSet (Work.StemsB.pullbackSnd q γ) b)),
    cylPullMap_mem_cylFibreBotSet q γ b _ y.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((cylPullFibreMap q γ b).continuous.comp continuous_subtype_val)
    (fun y => cylPullMap_mem_cylFibreBotSet q γ b _ y.2)

theorem cylPullBotMap_apply (q : C(X, B)) (γ : C(unitInterval, B)) (b : unitInterval)
    (y : ↥(cylFibreBotSet (Work.StemsB.pullbackSnd q γ) b)) :
    ((cylPullBotMap q γ b y : ↥(cylFibreBotSet q (γ b))) : Work.Serre.cyl q) =
      cylPullMap q γ (y : Work.Serre.cyl (Work.StemsB.pullbackSnd q γ)) := rfl


/-! ## The bottom part of the fibre is homeomorphic to the fibre -/

/-- The two descriptions of the bottom part of the fibre (inside the bottom copy, and inside the
fibre) are the same space. -/
def botSwap (q : C(X, B)) (z₀ : B) :
    ↥{y : ↥(Set.range (Work.Serre.cylIncl q)) |
        Work.Serre.cylRetract q (y : Work.Serre.cyl q) = z₀} ≃ₜ
      ↥(cylFibreBotSet q z₀) where
  toFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv y := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2))
    (fun y => y.1.2)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2))
    (fun y => y.1.2)

/-- `cylRetract q ∘ cylIncl q = q` on elements. -/
theorem cylRetract_cylIncl_apply (q : C(X, B)) (x : X) :
    Work.Serre.cylRetract q (Work.Serre.cylIncl q x) = q x :=
  congrFun (congrArg DFunLike.coe (Work.Serre.cylRetract_cylIncl q)) x

end

end Work.RatHurewicz
