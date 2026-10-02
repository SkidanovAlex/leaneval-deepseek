import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.AttachKill
import Submission.Work.RatHurewicz.attachCells_extension
import Submission.Work.RatHurewicz.attachCells_kill
import Submission.Work.RatHurewicz.killFamily_subsingleton
import Submission.Work.Stems.subsingleton_of_contractible
import Submission.Work.Serre.Models
import Submission.Work.Serre.cubeDiskHomeo
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.Serre.attachIncl_pi0_bijective
import Submission.Work.Serre.exists_joined_attachIncl
import Submission.Work.Serre.serreAttachKillPi
import Submission.Work.ThomBordism.Grassmann.Clamp.LpcCriterion

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# K1: the CW model of a space in a homotopy range

For a space `B`, a base point `b₀` and an integer `b ≥ 2` such that `B` is `(b-1)`-connected, we
build a cell complex `Γ` with a map `g : Γ → B` which is a bijection on `π_i` for all `i ≤ N`, with
`N` as large as one likes, and whose cells all have dimension `≥ b`.  This is the "CW approximation
in a range" that the cellular induction (K5) of the Serre exactness proof runs over.

The construction is in the "two substeps per degree" form.  A state at *level* `n` carries a space
`Y`, a based map `g : Y → B` (the base point of `B` being the image of the base point of `Y`) and
the property that `π_{j+1}(g)` is bijective for every `j ≤ n` (in this area's indexing
`Work.StemsB.πmap g j y` is the map on `π_{j+1}`; equivalently `π_i(g)` is bijective for
`i ≤ n+1`).

* the **generator step** (level `n`): attach one `(n+2)`-cell per element of `π_{n+2}(B)` along the
  *constant* map at the base point, extending `g` by the representative of the element.  This makes
  `π_{n+2}(g)` *surjective* and leaves `π_{j+1}(g)` for `j ≤ n` alone.
* the **killing step** (level `n`): attach one `(n+3)`-cell per element of the kernel of
  `π_{n+2}(g)`, along the representing sphere map (`Work.RatHurewicz.killFamily`), extending `g` by
  a null-homotopy of `g` composed with the attaching map (which exists precisely because the class
  lies in the kernel).  This makes `π_{n+2}(g)` *injective*, and leaves `π_{j+1}(g)` for `j ≤ n`
  alone.

Both steps attach cells of dimension `≥ b` once `n ≥ b - 2`, so the resulting filtration of `Γ` by
skeleta is by cells of dimension `≥ b` — exactly what K5 needs.
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.RatHurewicz

namespace Work.Serre.CWModel

noncomputable section

/-! ## Path connectedness of a cell attachment -/

/-- **A cell attachment of a path connected space along maps into it is path connected.** -/
theorem pathConnectedSpace_attachCells (n : ℕ) (Y : Type) [TopologicalSpace Y]
    [PathConnectedSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y)) :
    PathConnectedSpace (attachCells n Y ι f) := by
  have hjoin : ∀ p : attachCells n Y ι f, Joined p (attachIncl n Y ι f (Classical.arbitrary Y)) := by
    intro p
    obtain ⟨y, hy⟩ := exists_joined_attachIncl n Y ι f p
    exact hy.trans ((PathConnectedSpace.joined y (Classical.arbitrary Y)).map
      (attachIncl n Y ι f).continuous)
  refine pathConnectedSpace_iff_zerothHomotopy.mpr
    ⟨⟨ZerothHomotopy.mk (attachIncl n Y ι f (Classical.arbitrary Y))⟩, ⟨fun a b => ?_⟩⟩
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective a
  obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective b
  obtain ⟨γ⟩ := (hjoin x).trans (hjoin y).symm
  exact ZerothHomotopy.sound γ

/-! ## The states of the tower -/

/-- A stage of the model at level `n`: a space `Y` with a map `g : Y → B` sending the base point
`y₀` to `b₀`, path connected, and inducing a bijection on `π_{j+1}` for every `j ≤ n`. -/
structure StA (B : Type) [TopologicalSpace B] (b₀ : B) (n : ℕ) where
  Y : Type
  inst : TopologicalSpace Y
  y₀ : Y
  g : @ContinuousMap Y B inst _
  gbase : g y₀ = b₀
  conn : PathConnectedSpace Y
  bij : ∀ j : ℕ, j ≤ n → Function.Bijective (@piMapN Y B inst _ g (j + 1) y₀)

attribute [instance] StA.inst

/-- A stage of the model just before the killing step: as `StA n`, and additionally the induced map
on `π_{n+2}` is surjective. -/
structure StG (B : Type) [TopologicalSpace B] (b₀ : B) (n : ℕ) where
  Y : Type
  inst : TopologicalSpace Y
  y₀ : Y
  g : @ContinuousMap Y B inst _
  gbase : g y₀ = b₀
  conn : PathConnectedSpace Y
  bij : ∀ j : ℕ, j ≤ n → Function.Bijective (@piMapN Y B inst _ g (j + 1) y₀)
  surj : Function.Surjective (@piMapN Y B inst _ g (n + 2) y₀)

attribute [instance] StG.inst

/-- Forget the surjectivity of a stage. -/
def StG.toA {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ} (s : StG B b₀ n) : StA B b₀ n where
  Y := s.Y
  inst := s.inst
  y₀ := s.y₀
  g := s.g
  gbase := s.gbase
  conn := s.conn
  bij := s.bij

/-! ## The base of the tower -/

/-- **The base of the tower**: a point, mapping to `b₀`.  Here `π_{j+1}(g)` is a bijection for
`j ≤ b-2` because both sides are trivial: the homotopy groups of a point are trivial, and those of
`B` vanish below `b` by hypothesis. -/
def baseState (B : Type) [TopologicalSpace B] (b₀ : B) (b : ℕ) (hb : 2 ≤ b)
    (hB : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B b₀)) : StA B b₀ (b - 2) where
  Y := PUnit
  inst := inferInstance
  y₀ := ⟨⟩
  g := ContinuousMap.const PUnit b₀
  gbase := rfl
  conn := inferInstance
  bij := by
    intro j hj
    have hj' : j + 1 < b := by omega
    have h1 : Subsingleton (HomotopyGroup (Fin (j + 1)) PUnit (⟨⟩ : PUnit)) :=
      Work.Stems.subsingleton_of_contractible (⟨⟩ : PUnit)
    have h2 : Subsingleton (HomotopyGroup (Fin (j + 1)) B b₀) := hB (j + 1) hj'
    refine ⟨fun a b _ => h1.elim a b, fun y => ⟨default, h2.elim _ _⟩⟩

end

end Work.Serre.CWModel
