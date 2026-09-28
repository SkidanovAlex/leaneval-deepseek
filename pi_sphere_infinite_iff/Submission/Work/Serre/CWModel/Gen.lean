import Mathlib
import Submission.Work.Serre.CWModel.Defs
import Submission.Work.Serre.CWModel.Descent

set_option synthInstance.maxHeartbeats 400000

/-!
# The generator step of the model tower

Attaching, for every element `α` of `π_{n+2}(B)` at the base point of the model, one `(n+2)`-cell
along the *constant* map at the base point, and extending the structure map `g` over that cell by a
representative of `α`, makes `π_{n+2}(g)` surjective while leaving `π_{j+1}(g)` for `j ≤ n` alone.
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.RatHurewicz

namespace Work.Serre.CWModel

noncomputable section

/-- The explicit extension of a map over a cell attachment: on the old space it is `g`, on the
`i`-th cell it is `G i`.  It is defined by the quotient construction (rather than being extracted
from the existential universal property `Work.RatHurewicz.attachCells_extension`) so that its
values on the old space and on the cells are *definitional*: this is what makes the base-point
bookkeeping of the tower work. -/
def attachG {B : Type} [TopologicalSpace B] (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (g : C(Y, B)) (G : ι → C(cellDisk n, B))
    (hG : ∀ (j : ι) (z : cellSphere n), G j (cellSphereToDisk n z) = g (f j z)) :
    C(attachCells n Y ι f, B) :=
  ⟨Quotient.lift (attachCellsGlue n Y ι f g G) (attachCellsGlue_rel n Y ι f g G hG),
    (continuous_attachCellsGlue n Y ι f g G).quotient_lift
      (attachCellsGlue_rel n Y ι f g G hG)⟩

@[simp] theorem attachG_incl {B : Type} [TopologicalSpace B] (n : ℕ) (Y : Type)
    [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y)) (g : C(Y, B))
    (G : ι → C(cellDisk n, B))
    (hG : ∀ (j : ι) (z : cellSphere n), G j (cellSphereToDisk n z) = g (f j z)) (y : Y) :
    attachG n Y ι f g G hG (attachIncl n Y ι f y) = g y := rfl

@[simp] theorem attachG_cell {B : Type} [TopologicalSpace B] (n : ℕ) (Y : Type)
    [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y)) (g : C(Y, B))
    (G : ι → C(cellDisk n, B))
    (hG : ∀ (j : ι) (z : cellSphere n), G j (cellSphereToDisk n z) = g (f j z))
    (j : ι) (z : cellDisk n) :
    attachG n Y ι f g G hG (cellMap n Y ι f j z) = G j z := rfl

/-- **Surjectivity cancels on the right for bijectivity**: if `f ∘ s` is bijective and `s` is
surjective then `f` is bijective. -/
theorem bijective_of_comp_of_surjective {α β γ : Type*} {f : β → γ} {s : α → β}
    (h : Function.Bijective fun a => f (s a)) (hs : Function.Surjective s) :
    Function.Bijective f := by
  refine ⟨?_, h.2.of_comp⟩
  intro a b hab
  obtain ⟨a', rfl⟩ := hs a
  obtain ⟨b', rfl⟩ := hs b
  exact congrArg s (h.1 hab)

/-- **The generator step.** -/
def genStep {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ} (s : StA B b₀ n) : StG B b₀ n := by
  classical
  let e : Work.Stems.Cubical.IC (n + 2) ≃ₜ cellDisk n := Classical.choose (cubeDiskHomeo (n + 2))
  have he : ∀ x : Work.Stems.Cubical.IC (n + 2),
      x ∈ Cube.boundary (Fin (n + 2)) ↔
        (e x : EuclideanSpace ℝ (Fin (n + 2))) ∈ Metric.sphere 0 1 :=
    Classical.choose_spec (cubeDiskHomeo (n + 2))
  let eCont : C(Work.Stems.Cubical.IC (n + 2), cellDisk n) := ⟨⇑e, e.continuous_toFun⟩
  let esym : C(cellDisk n, Work.Stems.Cubical.IC (n + 2)) := ⟨⇑e.symm, e.continuous_invFun⟩
  let ι := HomotopyGroup (Fin (n + 2)) B (s.g s.y₀)
  let f : ι → C(cellSphere n, s.Y) := fun _ => ContinuousMap.const _ s.y₀
  let G : ι → C(cellDisk n, B) := fun j => (Quotient.out j).1.comp esym
  have hG : ∀ (j : ι) (z : cellSphere n), G j (cellSphereToDisk n z) = s.g (f j z) := by
    intro j z
    have hzb : e.symm (cellSphereToDisk n z) ∈ Cube.boundary (Fin (n + 2)) := by
      refine (he _).mpr ?_
      show (e (e.symm (cellSphereToDisk n z)) : EuclideanSpace ℝ (Fin (n + 2))) ∈ Metric.sphere 0 1
      rw [Homeomorph.apply_symm_apply]
      exact z.2
    have hconst : (Quotient.out j).1 (e.symm (cellSphereToDisk n z)) = s.g s.y₀ :=
      (Quotient.out j).2 _ hzb
    show (Quotient.out j).1 (e.symm (cellSphereToDisk n z))
      = s.g (ContinuousMap.const (cellSphere n) s.y₀ z)
    rw [hconst]
    rfl
  let g' : C(attachCells n s.Y ι f, B) := attachG n s.Y ι f s.g G hG
  have hgl : ∀ y, g' (attachIncl n s.Y ι f y) = s.g y := fun y => rfl
  have hgc : ∀ (j : ι) (z : cellDisk n), g' (cellMap n s.Y ι f j z) = G j z := fun j z => rfl
  haveI hconn : PathConnectedSpace s.Y := s.conn
  refine { Y := attachCells n s.Y ι f
           inst := inferInstance
           y₀ := attachIncl n s.Y ι f s.y₀
           g := g'
           gbase := (hgl s.y₀).trans s.gbase
           conn := pathConnectedSpace_attachCells n s.Y ι f
           bij := ?_
           surj := ?_ }
  · -- preservation of the lower homotopy groups
    intro j hj
    have hcomp : ∀ a, piMapN s.g (j + 1) s.y₀ a
        = piMapN g' (j + 1) (attachIncl n s.Y ι f s.y₀)
            (piMapN (attachIncl n s.Y ι f) (j + 1) s.y₀ a) := by
      intro a
      exact piMapN_comp (attachIncl n s.Y ι f) g' (j + 1) s.y₀ a
    have hbij : Function.Bijective (piMapN s.g (j + 1) s.y₀) := s.bij j hj
    have key : piMapN s.g (j + 1) s.y₀ = fun a =>
        piMapN g' (j + 1) (attachIncl n s.Y ι f s.y₀)
          (piMapN (attachIncl n s.Y ι f) (j + 1) s.y₀ a) := funext hcomp
    have hbij' : Function.Bijective (fun a =>
        piMapN g' (j + 1) (attachIncl n s.Y ι f s.y₀)
          (piMapN (attachIncl n s.Y ι f) (j + 1) s.y₀ a)) := key ▸ hbij
    have hsurj : Function.Surjective (piMapN (attachIncl n s.Y ι f) (j + 1) s.y₀) := by
      by_cases hjn : j + 1 ≤ n
      · exact (attachIncl_piMap_bijective_of_compress n s.Y ι f s.y₀ (j + 1) (by omega) hjn).2
      · have hje : j = n := by omega
        rw [hje]
        exact surjective_πmap_attachIncl n s.Y ι f s.y₀
    exact bijective_of_comp_of_surjective hbij' hsurj
  · -- surjectivity at the new degree
    intro α
    have hb₁ : ∀ x ∈ Cube.boundary (Fin (n + 2)),
        ((cellMap n s.Y ι f α).comp eCont) x = attachIncl n s.Y ι f s.y₀ := by
      intro x hx
      have hxb : (e x : EuclideanSpace ℝ (Fin (n + 2))) ∈ Metric.sphere 0 1 := (he x).mp hx
      have hcell : (cellMap n s.Y ι f α) (e x)
          = attachIncl n s.Y ι f (f α ⟨e x, hxb⟩) :=
        (attachIncl_attachRel n s.Y ι f α ⟨e x, hxb⟩).symm
      show (cellMap n s.Y ι f α) (e x) = attachIncl n s.Y ι f s.y₀
      rw [hcell]
      rfl
    refine ⟨Quotient.mk _ (⟨(cellMap n s.Y ι f α).comp eCont, hb₁⟩ :
      Ω^ (Fin (n + 2)) (attachCells n s.Y ι f) (attachIncl n s.Y ι f s.y₀)), ?_⟩
    rw [piMapN_apply_mk]
    have hcube : Work.StemsB.genLoopMap g' (n + 2)
        (⟨(cellMap n s.Y ι f α).comp eCont, hb₁⟩ :
          Ω^ (Fin (n + 2)) (attachCells n s.Y ι f) (attachIncl n s.Y ι f s.y₀))
        = Quotient.out α := by
      apply GenLoop.ext
      intro x
      show g' ((cellMap n s.Y ι f α) (e x)) = (Quotient.out α).1 x
      rw [hgc α (e x)]
      show (Quotient.out α).1 (e.symm (e x)) = (Quotient.out α).1 x
      rw [Homeomorph.symm_apply_apply]
    rw [hcube]
    exact Quotient.out_eq α

end

end Work.Serre.CWModel
