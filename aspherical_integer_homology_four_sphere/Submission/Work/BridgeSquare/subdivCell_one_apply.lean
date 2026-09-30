import Mathlib
import Submission.Work.Subdivision.API

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The subdivision chain of a `1`-cell, evaluated at a `1`-simplex

For a `PolyCW` `P` and a `1`-cell `R`, the subdivision chain of `R` is

`subdivCell R = - cone_R (∑_{f ⋖ R} inc(R,f) • [f]) = - ∑_{f ⋖ R} inc(R,f) • [f, R]`,

so it is supported on precisely the `1`-simplices `[f, R]` (an edge of the
barycentric subdivision of `R`), with coefficient `-inc(R,f)`.  Reading this as a
statement about an arbitrary `1`-simplex `s` gives the coefficient formula

`(subdivCell R) s = if s (last 1) = R then -(inc R (s 0)) else 0`,

which is the statement of `subdivCell_one_apply` below: if the top vertex of `s`
is `R` then `s` is the edge from `s 0` to `R` (so `s 0` is the facet of `R` that
`inc R (s 0)` refers to), and otherwise `s` does not occur at all.

The three steps are the natural ones:

* `subdivCellTopMemSupport` — every simplex in the support of `subdivCell e` has
  `e` as its last vertex (induction on the dimension, using that the support of a
  cone consists of the cones `snoc τ e`);
* `snocVertexZero` — the bottom vertex of the cone `[f, e]` is `f`;
* `subdivCellOneSnoc` — the coefficient recursion in dimension `1`: the facets of
  a `1`-cell are `0`-cells, hence `subdivCell 1 R` is the sum of the `-inc R f`
  over the facets `f`, and only one summand hits a given simplex `[s 0, R]`.

The names of the helpers are chosen so as not to collide with the (differently
proved) lemmas `snoc_vertex_zero` / `subdivCell_one_snoc` of the same namespace in
`Submission.Work.BridgeSquare.PsiM_edgeCell_expand`.
-/

namespace Work.BridgeSquare

open Work.Subdivision

/-- The `0`-simplex at a vertex, evaluated at the first of the two indices of
`Fin 2`. -/
theorem snocVertexZero {α : Type*} [Preorder α] (a e : α)
    (h : ∀ i, (Simplex.vertex a : Simplex α 0) i < e) :
    (Simplex.snoc (Simplex.vertex a) e h) (0 : Fin 2) = a := by
  simpa using Simplex.snoc_apply_castSucc (Simplex.vertex a) e h (0 : Fin 1)

/-- **Every simplex in the support of `subdivCell e` has `e` as its last vertex.**
Induction on the dimension: in dimension `0` the chain is the single vertex `e`,
and the recursion step is a cone with apex `e`, whose simplices are the `snoc τ e`
for `τ` in the support of the subdivided boundary of `e`. -/
theorem subdivCellTopMemSupport (P : PolyCW) (n : ℕ) (e : {e : P.Cell // P.dim e = n}) :
    ∀ σ ∈ (PolyCW.subdivCell P n e).support, σ (Fin.last n) = e.1 := by
  induction n with
  | zero =>
    intro σ hσ
    rw [PolyCW.subdivCell_zero] at hσ
    rw [Finsupp.support_single _ (one_ne_zero : (1 : ℤ) ≠ 0)] at hσ
    rw [Finset.mem_singleton] at hσ
    rw [hσ]
    simp
  | succ n ih =>
    intro σ hσ
    rw [PolyCW.subdivCell_succ_eq] at hσ
    have hσ₁ := Finsupp.support_smul hσ
    obtain ⟨τ, hτ, hτe, hσeq⟩ := PolyCW.coneLM_mem_support hσ₁
    rw [hσeq, Simplex.snoc_apply_last]

/-- **The coefficient of `subdivCell R` at the cone of a facet.**  For a `1`-cell
`R` and a facet `f ⋖ R` (a vertex), the coefficient of the `1`-simplex `[f, R]`
in `subdivCell R` is `-inc R f`. -/
theorem subdivCellOneSnoc {P : PolyCW} (e : P.Cell) (hd : P.dim e = 1)
    (f : P.Cell) (hf : f ∈ P.facets e)
    (h : ∀ i, (Simplex.vertex f : Simplex P.Cell 0) i < e) :
    (PolyCW.subdivCell P 1 ⟨e, hd⟩) (Simplex.snoc (Simplex.vertex f) e h) = - P.inc e f := by
  rw [PolyCW.subdivCell_succ_eq (P := P) 0 ⟨e, hd⟩]
  simp only [zero_add, pow_one, PolyCW.subdivCell_zero, PolyCW.facetIndex]
  rw [map_sum]
  simp only [map_smul]
  have hcongr : (∑ x ∈ (P.facets e).attach,
        P.inc e ↑x • (P.coneLM e 0) (fun₀ | Simplex.vertex ↑x => 1))
      = (∑ x ∈ (P.facets e).attach,
        P.inc e ↑x • (Finsupp.single (Simplex.snoc (Simplex.vertex ↑x) e
          (fun i => by rw [Simplex.vertex_apply]; exact P.facet_lt x.2)) (1 : ℤ))) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [PolyCW.coneLM_single]
  rw [hcongr]
  rw [Finsupp.smul_apply, smul_eq_mul, neg_one_mul, neg_inj]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single (⟨f, hf⟩ : {x // x ∈ P.facets e})]
  · rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_eq_same, mul_one]
  · intro b _ hb
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_eq_of_ne]
    · ring
    · intro hcon
      apply hb
      apply Subtype.ext
      have hf0 := snocVertexZero f e h
      have hb0 := snocVertexZero b.1 e
        (fun i => by rw [Simplex.vertex_apply]; exact P.facet_lt b.2)
      rw [← hcon, hf0] at hb0
      exact hb0.symm
  · intro habs; exact absurd (Finset.mem_attach _ _) habs

/-- **The subdivision chain of a `1`-cell, evaluated at a `1`-simplex.**  The only
simplices carrying a nonzero coefficient are the edges `[f, R]` from a facet `f`
to the top vertex `R`, where the coefficient is `-inc R f`. -/
theorem subdivCell_one_apply {P : Work.Subdivision.PolyCW} (R : P.Cell) (hR : P.dim R = 1)
    (s : Work.Subdivision.Simplex P.Cell 1) :
    Work.Subdivision.PolyCW.subdivCell P 1 ⟨R, hR⟩ s
      = if s (Fin.last 1) = R then -(P.inc R (s 0)) else 0 := by
  by_cases htop : s (Fin.last 1) = R
  · rw [ite_eq_left htop]
    have hlt : s 0 < R := by rw [← htop]; exact s.strictMono (by decide)
    have hdim : P.dim (s 0) = 0 := by
      have h := P.dim_lt' hlt
      rw [hR] at h
      omega
    have hfacet : s 0 ∈ P.facets R := by
      rw [P.mem_facets]
      exact ⟨hlt, by rw [hR, hdim]⟩
    have hne : ∀ i, (Simplex.vertex (s 0) : Simplex P.Cell 0) i < R :=
      fun i => by rw [Simplex.vertex_apply]; exact hlt
    have hs_eq : s = Simplex.snoc (Simplex.vertex (s 0)) R hne := by
      apply Simplex.ext
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
        rw [hj, Simplex.snoc_toFun, Simplex.snocFun_castSucc, Simplex.vertex_apply]
        congr 1
      · rw [Simplex.snoc_toFun, Simplex.snocFun_last]
        exact htop
    have h1 : (PolyCW.subdivCell P 1 ⟨R, hR⟩) s
        = (PolyCW.subdivCell P 1 ⟨R, hR⟩) (Simplex.snoc (Simplex.vertex (s 0)) R hne) :=
      congrArg (fun t : Simplex P.Cell 1 => (PolyCW.subdivCell P 1 ⟨R, hR⟩) t) hs_eq
    rw [h1, subdivCellOneSnoc R hR (s 0) hfacet hne]
  · rw [ite_eq_right htop]
    rw [← Finsupp.notMem_support_iff]
    intro hmem
    exact htop (subdivCellTopMemSupport P 1 ⟨R, hR⟩ s hmem)

end Work.BridgeSquare
