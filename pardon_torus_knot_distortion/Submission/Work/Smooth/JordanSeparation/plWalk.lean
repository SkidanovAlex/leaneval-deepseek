import Mathlib
import Submission.Work.Smooth.JordanSeparation.GridWalkDefs
import Submission.Work.Smooth.JordanSeparation.gridWalk_approx

/-!
# Polygonal loops in the plane, and the joins of restrictions of a path to a partition

A `PLWalk` is a closed sequence of points of `ℂ`; its realization is the corresponding polygonal
loop.  `homotopic_of_convex_set` says that two paths in `ℂ` with the same endpoints and values in a
convex set are homotopic.  `joinRestr` is the recursive join of the restrictions of a path to the
consecutive intervals of a partition of the unit interval, and `homotopic_restr_joinRestr` relates
a path to it.  These are the tools for the polygonal approximation of an arbitrary loop.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- A closed polygonal path in `ℂ`: a closed sequence of vertices. -/
structure PLWalk where
  /-- number of edges -/
  n : ℕ
  /-- at least one edge -/
  pos : 0 < n
  /-- the vertices -/
  v : Fin (n + 1) → ℂ
  /-- the walk is closed -/
  closed : v 0 = v (Fin.last n)

namespace PLWalk

variable (W : PLWalk)

/-- The realization of a polygonal walk as a path in `ℂ`. -/
def path : Path (W.v 0) (W.v (Fin.last W.n)) :=
  Path.concat W.v (fun i => segPath (W.v i.castSucc) (W.v i.succ))

/-- The realization of a polygonal walk, as a loop. -/
def loop : Path (W.v 0) (W.v 0) := W.path.cast rfl W.closed

end PLWalk

/-! ### Paths in a convex set are homotopic -/

/-- Two paths in `ℂ` with the same endpoints and values in a convex set are homotopic (in `ℂ`). -/
theorem homotopic_of_convex_set {S : Set ℂ} (hS : Convex ℝ S) (hSne : S.Nonempty)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) {p q : Path a b}
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) : Path.Homotopic p q := by
  haveI : ContractibleSpace ↥S := Convex.contractibleSpace hS hSne
  haveI : SimplyConnectedSpace ↥S := inferInstance
  have hp' : Set.range p ⊆ S := fun y hy => by rcases hy with ⟨t, rfl⟩; exact hp t
  have hq' : Set.range q ⊆ S := fun y hy => by rcases hy with ⟨t, rfl⟩; exact hq t
  have h := SimplyConnectedSpace.paths_homotopic
    (Path.toSubtype ha hb p hp') (Path.toSubtype ha hb q hq')
  have hmap := Path.Homotopic.map h
    (⟨fun z : ↥S => (z : ℂ), continuous_subtype_val⟩ : C(↥S, ℂ))
  have e1 : (Path.toSubtype ha hb p hp').map (f := fun z : ↥S => (z : ℂ))
      continuous_subtype_val = p := by
    ext t; rfl
  have e2 : (Path.toSubtype ha hb q hq').map (f := fun z : ↥S => (z : ℂ))
      continuous_subtype_val = q := by
    ext t; rfl
  rw [e1, e2] at hmap
  exact hmap

/-! ### The recursive join of the restrictions of a path to a partition -/

/-- The recursive join of the restrictions of a path to the consecutive intervals of the
partition `t`. -/
def joinRestr {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t : ℕ → unitInterval) :
    ∀ j : ℕ, Path (γ (t 0)) (γ (t j))
  | 0 => Path.refl _
  | j + 1 => (joinRestr γ t j).trans (γ.restr (t j) (t (j + 1)))

/-- **A path is homotopic to the recursive join of its restrictions to a partition.** -/
theorem homotopic_restr_joinRestr {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (t : ℕ → unitInterval) (j : ℕ) :
    Path.Homotopic (γ.restr (t 0) (t j)) (joinRestr γ t j) := by
  induction j with
  | zero => rw [Path.restr_same]; exact Path.Homotopic.refl _
  | succ k ih =>
    refine (Path.homotopic_restr_trans γ (t 0) (t k) (t (k + 1))).trans ?_
    rw [show joinRestr γ t (k + 1) = (joinRestr γ t k).trans (γ.restr (t k) (t (k+1))) from rfl]
    exact Path.Homotopic.hcomp ih (Path.Homotopic.refl _)


/-! ### `Path.concat` versus the recursive join -/

/-- The recursive (right-associated) join of a family of paths indexed by a `Fin`. -/
def joinFam {X : Type*} [TopologicalSpace X] :
    ∀ (n : ℕ) (p : Fin (n + 1) → X) (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)),
      Path (p 0) (p (Fin.last n))
  | 0, p, _ => Path.refl _
  | n + 1, p, F => (joinFam n (fun i => p i.castSucc) (fun k => F k.castSucc)).trans
      (F (Fin.last n))

/-- **`Path.concat` is homotopic to the recursive join of the same family.** -/
theorem concat_homotopic_joinFam {X : Type*} [TopologicalSpace X] :
    ∀ (n : ℕ) (p : Fin (n + 1) → X) (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)),
      Path.Homotopic (Path.concat p F) (joinFam n p F)
  | 0, p, F => by
    rw [Path.concat_zero]
    exact Path.Homotopic.refl _
  | n + 1, p, F => by
    rw [Path.concat_succ]
    rw [show joinFam (n + 1) p F =
        (joinFam n (fun i => p i.castSucc) (fun k => F k.castSucc)).trans (F (Fin.last n))
      from rfl]
    exact Path.Homotopic.hcomp
      (concat_homotopic_joinFam n (fun i => p i.castSucc) (fun k => F k.castSucc))
      (Path.Homotopic.refl _)
