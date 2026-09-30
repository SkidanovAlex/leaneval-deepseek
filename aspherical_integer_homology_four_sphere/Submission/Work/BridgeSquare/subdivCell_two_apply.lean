import Mathlib
import Submission.Work.BridgeSquare.subdivCell_one_apply
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range
import Submission.Work.Subdivision.subdivCell_support

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
-- `QbarCW.Cell` is definitionally `QbarCell`, but the projections of `QbarCW` are elaborated with
-- argument type `QbarCW.Cell`; the legacy transparency behaviour lets `rfl` identify them.
set_option backward.isDefEq.respectTransparency false

/-!
# The subdivision chain of a `2`-cell, evaluated at a `2`-simplex

This is the `n = 2` companion of `BridgeSquare.subdivCell_one_apply`.  For a
`PolyCW` `P` and a `2`-cell `R`, the subdivision chain of `R` is

`subdivCell R = (+1) • cone_R (∑_{f ⋖ R} inc(R,f) • subdivCell f)`

(with `(-1) ^ 2 = 1`), and for each facet `f` the chain `subdivCell f` is
supported on the edges `[u, f]` (`u ⋖ f`) with coefficient `-inc(f,u)`.  Coning
these up at `R` gives the `2`-simplices `[u, f, R]`, so the coefficient of an
arbitrary `2`-simplex `s` is

`(subdivCell R) s = if s (last 2) = R then -(inc R (s 1)) * (inc (s 1) (s 0)) else 0`,

which is `sd2_subdivCell_two_apply` below (a statement about an arbitrary `PolyCW`,
of which the requested theorem is the specialisation to the atlas of `M̄`).

The proof has three steps, mirroring the dimension-one argument:

* `sd2_coneLM_apply_last` / `sd2_coneLM_apply_ne` — the cone with apex `e`
  evaluated at a simplex `s` is the value of the coned chain at the last face of
  `s` when `s (last) = e`, and `0` otherwise (the only simplex of the cone whose
  last vertex is `e` and which can equal `s` is `snoc (s.face last) e`);
* the coned chain is `∑_{f ⋖ R} inc(R,f) • subdivCell f`, whose value at
  `t = s.face (last 2)` is computed termwise by `subdivCell_one_apply`;
* among the facets `f ⋖ R` only `f = s 1` can contribute, because the indicator
  in the dimension-one formula is `t (last 1) = f`, i.e. `s 1 = f`.

The final theorem `subdivCell_two_apply` is the specialisation to the cell atlas
of `M̄` (`QbarCW`, `mbarAtlasOf`, `rootCx`), where the incidence numbers are the
`Q̄`-incidence numbers `qInc` of the indices.
-/

namespace Work.BridgeSquare

open Work.Subdivision

/-- The last face of a cone at `e` is the original simplex. -/
theorem sd2_face_last_snoc {α : Type*} [Preorder α] {k : ℕ} (σ : Simplex α k) (e : α)
    (h : ∀ i, σ i < e) :
    (Simplex.snoc σ e h).face (Fin.last (k + 1)) = σ := by
  ext j
  rw [Simplex.face_apply, Fin.succAbove_last_apply, Simplex.snoc_apply_castSucc]

/-- The cone on the last face of `s` at `e = s (last)` is `s`. -/
theorem sd2_snoc_face_last {α : Type*} [Preorder α] {k : ℕ} (s : Simplex α (k + 1)) (e : α)
    (hse : s (Fin.last (k + 1)) = e) (h : ∀ i, (s.face (Fin.last (k + 1))) i < e) :
    Simplex.snoc (s.face (Fin.last (k + 1))) e h = s := by
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Simplex.snoc_apply_castSucc, Simplex.face_apply, Fin.succAbove_last_apply]
  · rw [Simplex.snoc_apply_last, hse]

/-- **The cone with apex `e`, evaluated at a simplex with top vertex `e`.** -/
theorem sd2_coneLM_apply_last {P : PolyCW} (e : P.Cell) {k : ℕ} (y : chainMod P.Cell k)
    (s : Simplex P.Cell (k + 1)) (h : s (Fin.last (k + 1)) = e) :
    PolyCW.coneLM P e k y s = y (s.face (Fin.last (k + 1))) := by
  have hc0 : ∀ i, (s.face (Fin.last (k + 1))) i < e := by
    intro i
    rw [Simplex.face_apply, Fin.succAbove_last_apply, ← h]
    exact s.strictMono (Fin.castSucc_lt_last i)
  rw [PolyCW.coneLM, Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum]
  refine (Finset.sum_eq_single (s.face (Fin.last (k + 1))) ?_ ?_).trans ?_
  · intro b _ hne
    rw [Finsupp.smul_apply, smul_eq_mul]
    by_cases hc : ∀ i, b i < e
    · rw [dite_eq_left hc]
      have hne' : s ≠ Simplex.snoc b e hc := by
        intro hcon
        exact hne (by rw [hcon, sd2_face_last_snoc b e hc])
      rw [Finsupp.single_eq_of_ne hne', mul_zero]
    · rw [dite_eq_right hc]
      simp
  · intro hnot
    rw [Finsupp.smul_apply, Finsupp.notMem_support_iff.mp hnot, zero_smul]
  · rw [Finsupp.smul_apply, smul_eq_mul, dite_eq_left hc0, sd2_snoc_face_last s e h hc0,
      Finsupp.single_eq_same, mul_one]

/-- **The cone with apex `e`, evaluated at a simplex whose top vertex is not `e`.** -/
theorem sd2_coneLM_apply_ne {P : PolyCW} (e : P.Cell) {k : ℕ} (y : chainMod P.Cell k)
    (s : Simplex P.Cell (k + 1)) (h : s (Fin.last (k + 1)) ≠ e) :
    PolyCW.coneLM P e k y s = 0 := by
  rw [PolyCW.coneLM, Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  by_cases hc : ∀ i, b i < e
  · rw [dite_eq_left hc]
    have hne' : s ≠ Simplex.snoc b e hc := by
      intro hcon
      exact h (by rw [hcon, Simplex.snoc_apply_last])
    rw [Finsupp.single_eq_of_ne hne', mul_zero]
  · rw [dite_eq_right hc]
    simp

/-- Evaluation of the last face of a `2`-simplex at `0`. -/
theorem sd2_face_last_two_zero {P : PolyCW} (s : Simplex P.Cell 2) :
    (s.face (Fin.last 2)) 0 = s 0 := by
  rw [Simplex.face_apply, Fin.succAbove_last_apply]
  rfl

/-- Evaluation of the last face of a `2`-simplex at `1`. -/
theorem sd2_face_last_two_one {P : PolyCW} (s : Simplex P.Cell 2) :
    (s.face (Fin.last 2)) (Fin.last 1) = s 1 := by
  rw [Simplex.face_apply, Fin.succAbove_last_apply]
  rfl

/-- **The subdivision chain of a `2`-cell, evaluated at a `2`-simplex.**  The only
simplices carrying a nonzero coefficient are the triangles `[u, f, R]` with
`u ⋖ f ⋖ R`, where the coefficient is `-inc(R,f) * inc(f,u)`. -/
theorem sd2_subdivCell_two_apply {P : PolyCW} (R : P.Cell) (hR : P.dim R = 2)
    (s : Simplex P.Cell 2) :
    PolyCW.subdivCell P 2 ⟨R, hR⟩ s
      = if s (Fin.last 2) = R then -(P.inc R (s 1)) * (P.inc (s 1) (s 0)) else 0 := by
  rw [PolyCW.subdivCell_succ_eq (P := P) 1 ⟨R, hR⟩,
    show ((-1 : ℤ)) ^ (1 + 1) = 1 by norm_num, one_smul]
  by_cases htop : s (Fin.last 2) = R
  · rw [ite_eq_left htop]
    have hcone : PolyCW.coneLM P R 1
        (∑ x ∈ (P.facets R).attach, P.inc R x.1 • PolyCW.subdivCell P 1
          (PolyCW.facetIndex 1 R hR x)) s
        = (∑ x ∈ (P.facets R).attach, P.inc R x.1 • PolyCW.subdivCell P 1
            (PolyCW.facetIndex 1 R hR x)) (s.face (Fin.last 2)) :=
      sd2_coneLM_apply_last (P := P) R _ s htop
    rw [hcone, Finsupp.finsetSum_apply]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    have hsub : ∀ x : {x : P.Cell // x ∈ P.facets R},
        PolyCW.subdivCell P 1 (PolyCW.facetIndex 1 R hR x) (s.face (Fin.last 2))
          = if s 1 = x.1 then -(P.inc x.1 (s 0)) else 0 := by
      intro x
      have hx : P.dim x.1 = 1 := by
        have h := (P.mem_facets R x.1).1 x.2
        omega
      rw [PolyCW.subdivCell_heq_subtype (P := P) (n := 1)
        (a := PolyCW.facetIndex 1 R hR x) (b := ⟨x.1, hx⟩) rfl]
      rw [subdivCell_one_apply (P := P) x.1 hx (s.face (Fin.last 2)),
        sd2_face_last_two_one, sd2_face_last_two_zero]
    rw [Finset.sum_congr rfl (fun x _ => by rw [hsub x])]
    have hs1 : s 1 ∈ P.facets R := by
      rw [P.mem_facets]
      have hlt : s 1 < R := by
        have h := s.strictMono (show (1 : Fin 3) < Fin.last 2 by decide)
        rwa [htop] at h
      refine ⟨hlt, ?_⟩
      have hd0 : P.dim (s 0) < P.dim (s 1) :=
        P.dim_lt' (s.strictMono (show (0 : Fin 3) < 1 by decide))
      have hd1 : P.dim (s 1) < P.dim R := P.dim_lt' hlt
      omega
    rw [Finset.sum_eq_single (⟨s 1, hs1⟩ : {x : P.Cell // x ∈ P.facets R})]
    · rw [ite_eq_left rfl]
      ring
    · intro b _ hne
      rw [ite_eq_right (fun hh => hne (Subtype.ext hh.symm)), mul_zero]
    · intro habs
      exact absurd (Finset.mem_attach _ _) habs
  · rw [ite_eq_right htop]
    exact sd2_coneLM_apply_ne (P := P) R _ s htop

/-- **The subdivision chain of the root face of a `2`-cell of the atlas of `M̄`,
evaluated at a `2`-simplex.** -/
theorem subdivCell_two_apply (e : Fin (Work.HomologyIso.Gen.mbarDim 2))
    (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell 2) :
    Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf 2 e s
      = if h : s (Fin.last 2) = Work.MbarHomology.Mbar.rootCx 2 e then
          - (Work.MbarHomology.qInc (Work.MbarHomology.Mbar.rootCx 2 e).idx (s 1).idx)
            * (Work.MbarHomology.qInc (s 1).idx (s 0).idx)
        else 0 := by
  have hroot : Work.MbarHomology.CellAtlas.rootCoeff Work.MbarHomology.Mbar.mbarAtlasOf 2 e s
      = Work.Subdivision.PolyCW.subdivCell Work.MbarHomology.QbarCW 2
          ⟨Work.MbarHomology.Mbar.rootCx 2 e,
            Work.MbarHomology.Mbar.rootCx_dim 2 e⟩ s := rfl
  rw [hroot]
  by_cases h : s (Fin.last 2) = Work.MbarHomology.Mbar.rootCx 2 e
  · rw [dite_eq_left h,
      sd2_subdivCell_two_apply (P := Work.MbarHomology.QbarCW)
        (Work.MbarHomology.Mbar.rootCx 2 e)
        (Work.MbarHomology.Mbar.rootCx_dim 2 e) s,
      ite_eq_left h]
    simp only [Work.MbarHomology.QbarCW_inc]
  · rw [dite_eq_right h,
      sd2_subdivCell_two_apply (P := Work.MbarHomology.QbarCW)
        (Work.MbarHomology.Mbar.rootCx 2 e)
        (Work.MbarHomology.Mbar.rootCx_dim 2 e) s,
      ite_eq_right h]

end Work.BridgeSquare
