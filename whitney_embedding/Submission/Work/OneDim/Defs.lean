import Mathlib

/-!
# Parametrised arcs in a 1-manifold

Auxiliary definitions for the study of arcs in one-dimensional smooth manifolds: an *arc
parametrisation* at a point `p` of a `1`-manifold `C` is an injective local diffeomorphism
`γ : ℝ → C` on an open set `s ∋ 0` with `γ 0 = p`; `arcGraph` is its graph and `arcGraphDom` the
projection of a set in `ℝ × C` to `ℝ`.

NOTE: this file was accidentally overwritten and has been reconstructed from the compiled
`olean`; if you were working on it, please restore your own version.
-/

open scoped Manifold ContDiff
open Topology Set Function

namespace Work.OneDim

noncomputable section

/-- The model space of a `1`-manifold. -/
abbrev E1 : Type := EuclideanSpace ℝ (Fin 1)

/-- The model with corners of a `1`-manifold. -/
abbrev I1 : ModelWithCorners ℝ E1 E1 := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))

/-- The smoothness index `C^∞`. -/
abbrev sm : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- A parametrisation of an arc through `p`: a local diffeomorphism `γ` which is injective on an
open set `s ∋ 0` with `γ 0 = p`. -/
def IsArcParam {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C]
    (p : C) (s : Set ℝ) (γ : ℝ → C) : Prop :=
  IsOpen s ∧ 0 ∈ s ∧ γ 0 = p ∧ Set.InjOn γ s ∧
    IsLocalDiffeomorphOn (modelWithCornersSelf ℝ ℝ) I1 sm γ s

variable {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C] [IsManifold I1 sm C]

theorem IsArcParam.zero_mem {p : C} {s : Set ℝ} {γ : ℝ → C} (h : IsArcParam p s γ) : 0 ∈ s :=
  h.2.1

theorem IsArcParam.apply_zero {p : C} {s : Set ℝ} {γ : ℝ → C} (h : IsArcParam p s γ) :
    γ 0 = p := h.2.2.1

theorem IsArcParam.injOn {p : C} {s : Set ℝ} {γ : ℝ → C} (h : IsArcParam p s γ) :
    Set.InjOn γ s := h.2.2.2.1

theorem IsArcParam.isOpen {p : C} {s : Set ℝ} {γ : ℝ → C} (h : IsArcParam p s γ) :
    IsOpen s := h.1

theorem IsArcParam.isLocalDiffeomorphOn {p : C} {s : Set ℝ} {γ : ℝ → C} (h : IsArcParam p s γ) :
    IsLocalDiffeomorphOn (modelWithCornersSelf ℝ ℝ) I1 sm γ s := h.2.2.2.2

/-- The graph of a parametrised curve in `ℝ × C`. -/
def arcGraph {C : Type*} (s : Set ℝ) (γ : ℝ → C) : Set (ℝ × C) := {q | q.1 ∈ s ∧ q.2 = γ q.1}

/-- The projection of a set in `ℝ × C` to `ℝ`. -/
def arcGraphDom {C : Type*} (G : Set (ℝ × C)) : Set ℝ := {t | ∃ x, (t, x) ∈ G}

/-- The set of graphs of arc parametrisations through `p`. -/
def arcGraphs {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C] (p : C) : Set (Set (ℝ × C)) :=
  {G | ∃ s γ, IsArcParam p s γ ∧ G = arcGraph s γ}

@[simp] theorem arcGraphDom_arcGraph {s : Set ℝ} {γ : ℝ → C} :
    arcGraphDom (arcGraph s γ) = s := by
  ext t
  simp only [arcGraphDom, arcGraph, mem_setOf_eq, exists_eq_right]

@[simp] theorem mem_arcGraph {s : Set ℝ} {γ : ℝ → C} {t : ℝ} :
    (t, γ t) ∈ arcGraph s γ ↔ t ∈ s := by
  simp [arcGraph]

theorem mem_arcGraphDom {G : Set (ℝ × C)} {t : ℝ} :
    t ∈ arcGraphDom G ↔ ∃ x, (t, x) ∈ G := Iff.rfl

end

end Work.OneDim
