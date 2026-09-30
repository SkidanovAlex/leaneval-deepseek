/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.OrderComplex
import Submission.Work.Subdivision.CellChain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cone recursion defining the subdivision chain map

For a `PolyCW` `P`, the subdivision chain of a cell `e` is defined by the cone
recursion on the dimension:

`subdivCell e = (-1)^(dim e) • cone_e (∑_{f ⋖ e} inc(e,f) • subdivCell f)`

with base case `subdivCell e = {e}` for a vertex `e` (the cone on the empty
boundary).  Here `cone_e : Λ_k → Λ_{k+1}` appends the new vertex `e` to every
simplex all of whose vertices are `< e`, and sends every other simplex to `0`.

The two facts that make this work are

* `PolyCW.subdivCell_support` — the support invariant: `subdivCell e` is supported
  on simplices all of whose vertices are `≤ e` (at the next stage, a facet
  `f ⋖ g` then gives the strict bound `≤ f < g` needed by `coneLM`), and
* `D_subdivCell` — the cone recursion respects boundaries:
  `∂(subdivCell e) = ∑_{f ⋖ e} inc(e,f) • subdivCell f`, i.e. `subdivCell` is
  compatible with the differential of the cellular chain complex.
-/

namespace Work.Subdivision

universe u

namespace Simplex

/-- The `0`-simplex at an element. -/
def vertex {α : Type u} [Preorder α] (a : α) : Simplex α 0 where
  toFun := fun _ => a
  strictMono := fun i j h => by
    simp only [Fin.lt_def] at h
    omega

@[simp] theorem vertex_apply {α : Type u} [Preorder α] (a : α) (i : Fin 1) :
    vertex a i = a := rfl

end Simplex

namespace PolyCW

variable (P : PolyCW.{u})

/-! ### The cone with a new apex -/

/-- The cone with apex `e`: append `e` at the end of every simplex all of whose
vertices are `< e`, and `0` elsewhere. -/
noncomputable def coneLM (e : P.Cell) (k : ℕ) :
    chainMod P.Cell k →ₗ[ℤ] chainMod P.Cell (k + 1) :=
  Finsupp.linearCombination ℤ fun σ : Simplex P.Cell k =>
    if h : ∀ i, σ i < e then Finsupp.single (Simplex.snoc σ e h) 1 else 0

theorem coneLM_single (e : P.Cell) (k : ℕ) (σ : Simplex P.Cell k) (h : ∀ i, σ i < e) :
    coneLM P e k (Finsupp.single σ 1) = Finsupp.single (Simplex.snoc σ e h) 1 := by
  simp [coneLM, h]

/-- The submodule of chains supported on simplices all of whose vertices are `< e`. -/
noncomputable def belowSub (e : P.Cell) (k : ℕ) : Submodule ℤ (chainMod P.Cell k) :=
  Submodule.span ℤ {x : chainMod P.Cell k |
    ∃ σ : Simplex P.Cell k, (∀ i, σ i < e) ∧ x = Finsupp.single σ 1}

theorem single_mem_belowSub {e : P.Cell} {k : ℕ} {σ : Simplex P.Cell k}
    (h : ∀ i, σ i < e) : Finsupp.single σ 1 ∈ belowSub P e k :=
  Submodule.subset_span ⟨σ, h, rfl⟩

/-- The coefficient sum (augmentation) of a 0-chain. -/
noncomputable def coeffSum {α : Type u} [Preorder α] : chainMod α 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun _ : Simplex α 0 => (1 : ℤ)

@[simp] theorem coeffSum_single {α : Type u} [Preorder α] (σ : Simplex α 0) :
    coeffSum (Finsupp.single σ 1) = 1 := by
  simp [coeffSum]

/-- A chain supported below `e` as a member of `belowSub`. -/
theorem mem_belowSub_of_support {e : P.Cell} {k : ℕ} {x : chainMod P.Cell k}
    (h : ∀ σ ∈ x.support, ∀ i, σ i < e) : x ∈ belowSub P e k := by
  rw [belowSub, ← Finsupp.sum_single x]
  refine Submodule.sum_mem _ fun σ hσ => ?_
  have : Finsupp.single σ (x σ) = x σ • Finsupp.single σ (1 : ℤ) := by simp
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, h σ hσ, rfl⟩)

theorem belowSub_le_iff {e : P.Cell} {k : ℕ} {p : Submodule ℤ (chainMod P.Cell k)} :
    belowSub P e k ≤ p ↔ ∀ σ : Simplex P.Cell k, (∀ i, σ i < e) → Finsupp.single σ 1 ∈ p := by
  rw [belowSub, Submodule.span_le]
  exact ⟨fun h σ hσ => h ⟨σ, hσ, rfl⟩, fun h x hx => by
    obtain ⟨σ, hσ, rfl⟩ := hx; exact h σ hσ⟩

theorem belowSub_mono {e e' : P.Cell} (h : e ≤ e') (k : ℕ) : belowSub P e k ≤ belowSub P e' k := by
  rw [belowSub_le_iff]
  exact fun σ hσ => single_mem_belowSub (P := P) fun i => lt_of_lt_of_le (hσ i) h

/-- The differential of a chain supported below `e` is again supported below `e`. -/
theorem D_mem_belowSub_le (e : P.Cell) (k : ℕ) :
    belowSub P e (k + 1) ≤ Submodule.comap (D (α := P.Cell) k) (belowSub P e k) := by
  rw [belowSub_le_iff]
  intro σ hσ
  rw [Submodule.mem_comap, D_single]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact single_mem_belowSub (P := P) fun j => hσ (i.succAbove j)

theorem D_mem_belowSub {e : P.Cell} {k : ℕ} {x : chainMod P.Cell (k + 1)}
    (hx : x ∈ belowSub P e (k + 1)) : D (α := P.Cell) k x ∈ belowSub P e k :=
  D_mem_belowSub_le P e k hx

/-! ### The subdivision chain of a cell -/

/-- The subdivision chain of a cell, by cone recursion on the dimension. -/
noncomputable def subdivCell (n : ℕ) (e : {e : P.Cell // P.dim e = n}) :
    chainMod P.Cell n :=
  Nat.rec (motive := fun n => (e : {e : P.Cell // P.dim e = n}) → chainMod P.Cell n)
    (fun e => Finsupp.single (Simplex.vertex e.1) 1)
    (fun n ih e => (-1 : ℤ) ^ (n + 1) • coneLM P e.1 n
      (∑ x ∈ (P.facets e.1).attach, P.inc e.1 x.1 • ih ⟨x.1, by
        have h := (P.mem_facets e.1 x.1).1 x.2
        have he := e.2
        omega⟩))
    n e

@[simp] theorem subdivCell_zero (e : {e : P.Cell // P.dim e = 0}) :
    subdivCell P 0 e = Finsupp.single (Simplex.vertex e.1) 1 := rfl

theorem subdivCell_succ (n : ℕ) (e : {e : P.Cell // P.dim e = n + 1}) :
    subdivCell P (n + 1) e = (-1 : ℤ) ^ (n + 1) • coneLM P e.1 n
      (∑ x ∈ (P.facets e.1).attach, P.inc e.1 x.1 • subdivCell P n ⟨x.1, by
        have h := (P.mem_facets e.1 x.1).1 x.2
        have he := e.2
        omega⟩) := rfl

/-- The chain-level subdivision map on cells. -/
noncomputable def subdivLM (k : ℕ) : cellMod P k →ₗ[ℤ] chainMod P.Cell k :=
  Finsupp.linearCombination ℤ fun e : {e : P.Cell // P.dim e = k} => subdivCell P k e

@[simp] theorem subdivLM_single (k : ℕ) (e : {e : P.Cell // P.dim e = k}) :
    subdivLM P k (Finsupp.single e 1) = subdivCell P k e := by
  simp [subdivLM]

end PolyCW

end Work.Subdivision
