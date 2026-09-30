/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.Subdivision.Subdiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The support invariant of the subdivision chain of a cell

The subdivision chain `subdivCell e` of a cell `e` of dimension `n` is a chain in
the order complex of the poset of cells, i.e. a formal `ℤ`-linear combination of
strictly increasing `(n+1)`-tuples of cells.  The geometric content of the cone
recursion defining it is that *every* vertex of *every* simplex occurring in
`subdivCell e` is a face of `e`:

`∀ σ ∈ (subdivCell e).support, ∀ i, σ i ≤ e`.

This is the "admissible" invariant that makes the cone recursion well typed: the
recursion computes `subdivCell e` as the cone with apex `e` on the boundary chain
`∑_{f ⋖ e} inc(e,f) • subdivCell f`, and the cone `coneLM e` appends the apex `e`
to a simplex only when all its vertices are `< e`.  The statement proved here
supplies exactly that: for `f ⋖ e` and `σ ∈ subdivCell f` the induction
hypothesis gives `σ i ≤ f < e`.

## Implementation

The only technical wrinkle is that the recursion `PolyCW.subdivCell` recurses into
`subdivCell n ⟨f, hf⟩` where the proof `hf` that `P.dim f = n` is the internal
proof term of the definition, which cannot be named in a client file.  We
therefore isolate a variant of the recursion step, `subdivCell_succ_eq`, in which
the recursive calls are indexed by the *named* function `facetIndex`; it is
proved from the definitional unfolding by `congr 1` (congruence reasoning
identifies the two proof terms, which are proofs of a proposition).
-/

namespace Work.Subdivision

namespace PolyCW

variable {P : PolyCW}

/-- Two subtype presentations of the same cell (i.e. with the same underlying
cell and dimension proofs) have the same subdivision chain. -/
theorem subdivCell_heq_subtype {n : ℕ} {a b : {e : P.Cell // P.dim e = n}} (h : a.1 = b.1) :
    subdivCell P n a = subdivCell P n b :=
  congrArg (subdivCell P n) (Subtype.ext h)

/-- The `n`-cell underlying a facet `x` of an `(n+1)`-cell `e`, as an element of
the type of `n`-cells. -/
noncomputable def facetIndex (n : ℕ) (e : P.Cell) (he : P.dim e = n + 1)
    (x : {x : P.Cell // x ∈ P.facets e}) : {f : P.Cell // P.dim f = n} :=
  ⟨x.1, by have h := (P.mem_facets e x.1).1 x.2; omega⟩

/-- **Support of the cone.** If a simplex occurs in the support of the cone with
apex `e` on a chain `y`, then it is the cone `snoc τ e` of a simplex `τ` occurring
in `y`, and in particular all vertices of `τ` are `< e`. -/
theorem coneLM_mem_support {e : P.Cell} {k : ℕ} {y : chainMod P.Cell k}
    {σ : Simplex P.Cell (k + 1)} (hσ : σ ∈ (coneLM P e k y).support) :
    ∃ τ ∈ y.support, ∃ h : ∀ i, τ i < e, σ = Simplex.snoc τ e h := by
  rw [coneLM, Finsupp.linearCombination_apply] at hσ
  obtain ⟨τ, hτ, hτ'⟩ := Finsupp.mem_support_finsetSum σ hσ
  have hτ'' : σ ∈ ((if h : ∀ i, τ i < e then Finsupp.single (Simplex.snoc τ e h) 1 else 0 :
      Simplex P.Cell (k+1) →₀ ℤ)).support := Finsupp.support_smul hτ'
  by_cases h : ∀ i, τ i < e
  · have : σ ∈ ({Simplex.snoc τ e h} : Finset _) := by
      simpa [h, Finsupp.support_single _ (one_ne_zero)] using hτ''
    exact ⟨τ, hτ, h, Finset.mem_singleton.mp this⟩
  · simp [h] at hτ''

/-- The recursion step for the subdivision chain, with the recursive calls
indexed by the named function `facetIndex` rather than by the internal proof term
of the definition. -/
theorem subdivCell_succ_eq (n : ℕ) (e : {e : P.Cell // P.dim e = n + 1}) :
    subdivCell P (n + 1) e = (-1 : ℤ) ^ (n + 1) • coneLM P e.1 n
      (∑ x ∈ (P.facets e.1).attach,
        P.inc e.1 x.1 • subdivCell P n (facetIndex (P := P) n e.1 e.2 x)) := by
  rw [subdivCell_succ]
  congr 1

end PolyCW

/-- **Support invariant of the subdivision chain.** Every vertex of every simplex
in the support of `subdivCell e` is a face of `e`. -/
theorem subdivCell_support (P : PolyCW) (n : ℕ) (e : {e : P.Cell // P.dim e = n}) :
    ∀ σ ∈ (PolyCW.subdivCell P n e).support, ∀ i, σ i ≤ e.1 := by
  induction n with
  | zero =>
    intro σ hσ i
    rw [PolyCW.subdivCell_zero] at hσ
    have h : σ = Simplex.vertex e.1 := by
      rw [Finsupp.support_single _ (one_ne_zero : (1 : ℤ) ≠ 0)] at hσ
      exact Finset.mem_singleton.mp hσ
    rw [h]
    simp
  | succ n ih =>
    intro σ hσ i
    rw [PolyCW.subdivCell_succ_eq] at hσ
    have hσ₁ := Finsupp.support_smul hσ
    obtain ⟨τ, hτ, hτe, hσeq⟩ := PolyCW.coneLM_mem_support hσ₁
    obtain ⟨x, _hx, hxτ⟩ := Finsupp.mem_support_finsetSum τ hτ
    have hxτ' := Finsupp.support_smul hxτ
    have hxlt : x.1 < e.1 := ((P.mem_facets e.1 x.1).1 x.2).1
    have hτle : ∀ j, τ j ≤ x.1 := ih (PolyCW.facetIndex (P := P) n e.1 e.2 x) τ hxτ'
    rw [hσeq]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [Simplex.snoc_apply_castSucc]
      exact le_trans (hτle j) (le_of_lt hxlt)
    · rw [Simplex.snoc_apply_last]

end Work.Subdivision
