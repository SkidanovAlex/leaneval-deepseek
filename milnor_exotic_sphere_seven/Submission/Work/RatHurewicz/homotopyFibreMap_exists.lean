import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The canonical map of homotopy fibres induced by a map of pairs

For `i : C(A,X)`, `a₀ : A`, the homotopy fibre `homotopyFibre i a₀` is the space of pairs
`(a, γ)` with `γ` a path in `X` from `i a₀` to `i a` (`Work.RatHurewicz`, built on
`Work.StemsB.bundlePullback`).  A commutative square `f ∘ i = i' ∘ g` of continuous maps induces a
continuous map of homotopy fibres

`homotopyFibreMap : homotopyFibre i a₀ → homotopyFibre i' (g a₀)`,  `(a, γ) ↦ (g a, f ∘ γ)`,

which sends base point to base point.  This file constructs that map, records its two components
(`homotopyFibreMap_fst`, `homotopyFibreMap_snd`) and its effect on the base point
(`homotopyFibreMap_basepoint`), and assembles the packaged existence statement
`homotopyFibreMap_exists` required by the rational Hurewicz chapter.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

noncomputable section

open Work.StemsB

variable {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y]
  {A : Type} [TopologicalSpace A] {B : Type} [TopologicalSpace B]

/-- **The canonical map of homotopy fibres induced by a commutative square** `f ∘ i = i' ∘ g`: a
point `(a, γ)` of the homotopy fibre of `i` over `a₀` (so `γ 0 = i a₀` and `γ 1 = i a`) is sent to
`(g a, f ∘ γ)`, which is a point of the homotopy fibre of `i'` over `g a₀` because
`f (i a₀) = i' (g a₀)` and `f (i a) = i' (g a)`. -/
def homotopyFibreMap (i : C(A, X)) (i' : C(B, Y)) (f : C(X, Y)) (g : C(A, B))
    (hsq : f.comp i = i'.comp g) (a₀ : A) :
    C(homotopyFibre i a₀, homotopyFibre i' (g a₀)) where
  toFun p :=
    ⟨(g p.1.1, ⟨f.comp p.1.2.1, by
        show (f.comp p.1.2.1) 0 = i' (g a₀)
        rw [ContinuousMap.comp_apply, p.1.2.2]
        simpa using congrArg (fun k : C(A, Y) => k a₀) hsq⟩),
      by
        have h : p.1.2.1 1 = i p.1.1 := p.2
        show (f.comp p.1.2.1) 1 = i' (g p.1.1)
        rw [ContinuousMap.comp_apply, h]
        simpa using congrArg (fun k : C(A, Y) => k p.1.1) hsq⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact g.continuous.comp (continuous_fst.comp continuous_subtype_val)
    · refine Continuous.subtype_mk ?_ _
      exact f.continuous_postcomp.comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))

/-- The first component of `homotopyFibreMap`: it is `g` on the underlying points. -/
@[simp]
theorem homotopyFibreMap_fst (i : C(A, X)) (i' : C(B, Y)) (f : C(X, Y)) (g : C(A, B))
    (hsq : f.comp i = i'.comp g) (a₀ : A) (p : homotopyFibre i a₀) :
    (homotopyFibreMap i i' f g hsq a₀ p).1.1 = g p.1.1 := rfl

/-- The second component of `homotopyFibreMap`: it is composition with `f` on the underlying
paths. -/
@[simp]
theorem homotopyFibreMap_snd (i : C(A, X)) (i' : C(B, Y)) (f : C(X, Y)) (g : C(A, B))
    (hsq : f.comp i = i'.comp g) (a₀ : A) (p : homotopyFibre i a₀) :
    (homotopyFibreMap i i' f g hsq a₀ p).1.2.1 = f.comp p.1.2.1 := rfl

/-- `homotopyFibreMap` preserves the base point. -/
theorem homotopyFibreMap_basepoint (i : C(A, X)) (i' : C(B, Y)) (f : C(X, Y)) (g : C(A, B))
    (hsq : f.comp i = i'.comp g) (a₀ : A) :
    homotopyFibreMap i i' f g hsq a₀ (homotopyFibreBasepoint i a₀)
      = homotopyFibreBasepoint i' (g a₀) := by
  have hpoint : f (i a₀) = i' (g a₀) := congrArg (fun k : C(A, Y) => k a₀) hsq;
  refine Subtype.ext ?_;
  refine Prod.ext rfl ?_;
  refine Subtype.ext ?_;
  ext t;
  exact hpoint

/-- **The canonical map of homotopy fibres induced by a map of "pairs".**  Given a commutative
square `f ∘ i = i' ∘ g` of continuous maps, the homotopy fibre of `i : A → X` over `a₀` maps
canonically to the homotopy fibre of `i' : B → Y` over `g a₀`, by `(a, γ) ↦ (g a, f ∘ γ)`.  The
statement records the map, its effect on the base points, and its formula on the two components. -/
theorem homotopyFibreMap_exists {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y]
    {A : Type} [TopologicalSpace A] {B : Type} [TopologicalSpace B] (i : C(A, X)) (i' : C(B, Y))
    (f : C(X, Y)) (g : C(A, B)) (hsq : f.comp i = i'.comp g) (a₀ : A) :
    ∃ (F : C(Work.RatHurewicz.homotopyFibre i a₀, Work.RatHurewicz.homotopyFibre i' (g a₀)))
      (_F0 : F (Work.RatHurewicz.homotopyFibreBasepoint i a₀)
        = Work.RatHurewicz.homotopyFibreBasepoint i' (g a₀)),
      (∀ p : Work.RatHurewicz.homotopyFibre i a₀,
        (F p).1.1 = g p.1.1 ∧ (F p).1.2.1 = f.comp p.1.2.1) :=
  ⟨homotopyFibreMap i i' f g hsq a₀, homotopyFibreMap_basepoint i i' f g hsq a₀,
    fun _ => ⟨rfl, rfl⟩⟩

end

end Work.RatHurewicz
