import Mathlib
import Submission.Work.Serre.SPC.Defs
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.CWModel.Maps
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Serre.Assembly.pullbackFst_serre
import Submission.Work.Serre.E2dFibre
import Submission.Work.Cohomology.relChains_vanishing_of_compact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The tower comparison: setup

Vocabulary for the inductive proof of `Work.Serre.SPC.towerComparison`:

* `Good p b f s` — the invariant of the tower induction: the comparison map of the pullback of `p`
  along the structure map of the stage `s` is an isomorphism in degrees `< b + f` and surjective in
  degree `b + f`;
* the definitional identifications saying that the comparison map
  `Work.Serre.CWModel.stagePairMap g p γ₀` of a map `g` is `Work.StemsB.relPairMap` of the first
  projection of the pullback;
* the definitional identifications of the data of the generator and killing steps of the model
  tower (`Work.Serre.CWModel.genStep`, `Work.Serre.CWModel.killStep`): their underlying space is an
  attachment of cells, the base point is the image of the old base point, and the structure map
  restricts to the old structure map on the old part.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.SPC

noncomputable section

/-- **The invariant of the tower induction.**  For a Serre fibration `p : E → B` and natural
numbers `b`, `f`, the stage `s` of the model tower is *good* if the comparison map
`(Pullback s.g p, fibre over s.y₀) → (s.Y, {s.y₀})` is an isomorphism on homology in degrees
`< b + f` and surjective in degree `b + f`. -/
def Good {B : Type} [TopologicalSpace B] {b₀ : B} {E : Type} [TopologicalSpace E]
    (p : C(E, B)) (b f : ℕ) {n : ℕ} (s : Work.Serre.CWModel.StA B b₀ n) : Prop :=
  (∀ i : ℕ, i < b + f → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.CWModel.stagePairMap s.g p s.y₀) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.CWModel.stagePairMap s.g p s.y₀) (b + f)).hom

/-- The comparison map of a stage is `relPairMap` of the first projection of the pullback
(definitionally). -/
theorem stagePairMap_eq_relPairMap {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) :
    Work.Serre.CWModel.stagePairMap g p γ₀
      = Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀ := rfl

/-! ## The data of the generator step -/

theorem genStep_Y {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ} (s : Work.Serre.CWModel.StA B b₀ n) :
    (Work.Serre.CWModel.genStep s).Y = Work.RatHurewicz.attachCells n s.Y
      (HomotopyGroup (Fin (n + 2)) B (s.g s.y₀))
      (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere n) s.y₀) := rfl

theorem genStep_y₀ {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ} (s : Work.Serre.CWModel.StA B b₀ n) :
    (Work.Serre.CWModel.genStep s).y₀ = Work.RatHurewicz.attachIncl n s.Y
      (HomotopyGroup (Fin (n + 2)) B (s.g s.y₀))
      (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere n) s.y₀) s.y₀ := rfl

theorem genStep_apply_incl {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ} (s : Work.Serre.CWModel.StA B b₀ n)
    (x : s.Y) :
    (Work.Serre.CWModel.genStep s).g (Work.RatHurewicz.attachIncl n s.Y
      (HomotopyGroup (Fin (n + 2)) B (s.g s.y₀))
      (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere n) s.y₀) x) = s.g x := rfl

/-! ## The data of the killing step -/

theorem killStep_Y {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ} (s : Work.Serre.CWModel.StG B b₀ n) :
    (Work.Serre.CWModel.killStep s).Y = Work.RatHurewicz.attachCells (n + 1) s.Y
      {α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀ // piMapN s.g (n + 2) s.y₀ α = 1}
      (fun k => Work.RatHurewicz.killFamily (n + 1) s.Y s.y₀ k.1) := rfl

theorem killStep_y₀ {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ} (s : Work.Serre.CWModel.StG B b₀ n) :
    (Work.Serre.CWModel.killStep s).y₀ = Work.RatHurewicz.attachIncl (n + 1) s.Y
      {α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀ // piMapN s.g (n + 2) s.y₀ α = 1}
      (fun k => Work.RatHurewicz.killFamily (n + 1) s.Y s.y₀ k.1) s.y₀ := rfl

theorem killStep_apply_incl {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ} (s : Work.Serre.CWModel.StG B b₀ n)
    (x : s.Y) :
    (Work.Serre.CWModel.killStep s).g (Work.RatHurewicz.attachIncl (n + 1) s.Y
      {α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀ // piMapN s.g (n + 2) s.y₀ α = 1}
      (fun k => Work.RatHurewicz.killFamily (n + 1) s.Y s.y₀ k.1) x) = s.g x := rfl


/-! ## The base of the tower -/

/-- **The base of the tower is good.**  For the base state (`Y = PUnit`, `g = const b₀`) the
comparison map is a map between the relative complexes of the pairs `(X, X)` (the relative part is
all of the space), whose homology vanishes; a map between zero objects is an isomorphism and a map
into a zero object is surjective. -/
theorem baseGood {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b₀ : B) (b f : ℕ) (hb : 2 ≤ b)
    (hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀)) :
    Good p b f (Work.Serre.CWModel.baseState B b₀ b hb hconn) := by
  classical
  have hsrc : ((Work.StemsB.pullbackFst (ContinuousMap.const PUnit b₀) p) ⁻¹'
      ({⟨⟩} : Set PUnit)) = Set.univ := by
    ext x; simp
  have htgt : ({⟨⟩} : Set PUnit) = (Set.univ : Set PUnit) := by
    ext x; simp
  have hX : ∀ i : ℕ, IsZero ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback
      (ContinuousMap.const PUnit b₀) p))
      ((Work.StemsB.pullbackFst (ContinuousMap.const PUnit b₀) p) ⁻¹'
        ({⟨⟩} : Set PUnit))).homology i) := by
    intro i
    rw [hsrc]
    exact Work.Cohomology.isZero_relChains_univ _ i
  have hY : ∀ i : ℕ, IsZero ((Work.Cohomology.relChains (TopCat.of PUnit)
      ({⟨⟩} : Set PUnit)).homology i) := by
    intro i
    rw [htgt]
    exact Work.Cohomology.isZero_relChains_univ _ i
  constructor
  · intro i _
    change IsIso (HomologicalComplex.homologyMap
      (Work.Serre.CWModel.stagePairMap (ContinuousMap.const PUnit b₀) p ⟨⟩) i)
    have he := IsZero.eq_of_src (hX i)
      (HomologicalComplex.homologyMap
        (Work.Serre.CWModel.stagePairMap (ContinuousMap.const PUnit b₀) p ⟨⟩) i)
      (IsZero.iso (hX i) (hY i)).hom
    rw [he]
    infer_instance
  · change Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.CWModel.stagePairMap (ContinuousMap.const PUnit b₀) p ⟨⟩) (b + f)).hom
    haveI : Subsingleton (↥(HomologicalComplex.homology
        (Work.Cohomology.relChains (TopCat.of PUnit) ({⟨⟩} : Set PUnit)) (b + f))) :=
      ModuleCat.subsingleton_of_isZero (hY (b + f))
    intro y
    exact ⟨0, Subsingleton.elim _ y⟩

end

end Work.Serre.SPC
