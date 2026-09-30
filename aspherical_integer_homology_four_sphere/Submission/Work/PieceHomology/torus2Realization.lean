/-
# The `Δ`-realization of the minimal `Δ`-structure of the `2`-torus

An explicit `Work.DeltaHomology.DeltaRealization` of `Work.PieceHomology.torus2DeltaCx`
(one vertex, three edges `a, b, c` and two triangles `T₀ = [b,c,a]`, `T₁ = [a,c,b]`) in
`T² = (ℝ/ℤ)² = TopCat.of (Fin 2 → AddCircle 1)`.

The characteristic maps, the coordinates `[0,1)` on the circle, the cells and the open simplex
`cellOf x` containing a point live in `Submission/Work/PieceHomology/Torus2Chi.lean`.
-/
import Mathlib
import Submission.Work.PieceHomology.Torus2Chi
import Submission.Work.PieceHomology.torus2Chi_face_compat
import Submission.Work.PieceHomology.torus2CellReal
import Submission.Work.PieceHomology.torus2CellWeights
import Submission.Work.PieceHomology.torus2_weakTopology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits
open Convexity
open scoped Topology

open Work.DeltaHomology

namespace Work.PieceHomology

noncomputable section

/-! ## §3  The `Δ`-simplex map -/

/-- The characteristic maps of `torus2DeltaCx` as singular simplices of the torus. -/
def torus2SimplexMap : DeltaSimplexMap torus2DeltaCx Torus2Space where
  χ := torus2Chi
  face_compat := fun {k} σ i => torus2Chi_face_compat σ i

/-! ### The two triangles cover the torus -/

theorem chiT0_ptT0 (x : Fin 2 → AddCircle (1 : ℝ)) (h : uy x ≤ ux x) :
    chiT0 (ptT0 x h) = x := by
  trans tpt ((ux x : ℝ) : AddCircle (1 : ℝ)) ((uy x : ℝ) : AddCircle (1 : ℝ))
  · simp only [chiT0, ContinuousMap.coe_mk, ptT0_weights_one, ptT0_weights_two, tpt,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [show ux x - uy x + uy x = ux x from by ring]
  · exact tpt_ux_uy x

theorem chiT1_ptT1 (x : Fin 2 → AddCircle (1 : ℝ)) (h : ux x ≤ uy x) :
    chiT1 (ptT1 x h) = x := by
  trans tpt ((ux x : ℝ) : AddCircle (1 : ℝ)) ((uy x : ℝ) : AddCircle (1 : ℝ))
  · simp only [chiT1, ContinuousMap.coe_mk, ptT1_weights_one, ptT1_weights_two, tpt,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [show uy x - ux x + ux x = uy x from by ring]
  · exact tpt_ux_uy x

/-- Every point of the torus lies in one of the two closed triangles. -/
theorem torus2_cover (x : Fin 2 → AddCircle (1 : ℝ)) :
    ∃ σ : Fin 2, ∃ w : StdSimplex ℝ (Fin 3), chiT σ w = x := by
  rcases le_total (uy x) (ux x) with h | h
  · exact ⟨0, ptT0 x h, by rw [chiT_zero]; exact chiT0_ptT0 x h⟩
  · exact ⟨1, ptT1 x h, by rw [chiT_one]; exact chiT1_ptT1 x h⟩

/-! ### The characteristic maps of the simplex map -/

/-- The characteristic map `cls` of `torus2SimplexMap` is `torus2ChiCls`, up to the
definitional identification of `torus2DeltaCx.card k` with `torus2Card k`. -/
theorem cls_eq_chiCls (k : ℕ) (σ : Fin (torus2DeltaCx.card k)) :
    DeltaSimplexMap.cls torus2SimplexMap k σ
      = torus2ChiCls k (Fin.cast (torus2DeltaCx_card k) σ) := by
  simp only [DeltaSimplexMap.cls, torus2SimplexMap]
  rw [toSSetObjEquiv_torus2Chi]
  exact (congrArg (torus2ChiCls k) (Fin.ext rfl)).symm

theorem cls_preimage (k : ℕ) (σ : Fin (torus2DeltaCx.card k))
    (s : Set (Fin 2 → AddCircle (1 : ℝ))) :
    ((DeltaSimplexMap.cls torus2SimplexMap k σ) ⁻¹' s)
      = ((torus2ChiCls k (Fin.cast (torus2DeltaCx_card k) σ)) ⁻¹' s) :=
  congrArg (fun f : C(StdSimplex ℝ (Fin (k + 1)), Fin 2 → AddCircle (1 : ℝ)) => f ⁻¹' s)
    (cls_eq_chiCls k σ)

/-- The `torus2ChiCls`-preimages are open whenever the `cls`-preimages are. -/
theorem isOpen_chiCls_preimage (s : Set (Fin 2 → AddCircle (1 : ℝ)))
    (h : ∀ (k : ℕ) (σ : Fin (torus2DeltaCx.card k)),
      IsOpen ((DeltaSimplexMap.cls torus2SimplexMap k σ) ⁻¹' s))
    (k : ℕ) (σ : Fin (torus2Card k)) : IsOpen ((torus2ChiCls k σ) ⁻¹' s) := by
  have hcast : (Fin.cast (torus2DeltaCx_card k) (Fin.cast (torus2DeltaCx_card k).symm σ)
      : Fin (torus2Card k)) = σ := Fin.ext rfl
  rw [← hcast, ← cls_preimage k (Fin.cast (torus2DeltaCx_card k).symm σ) s]
  exact h k _

/-! ## §4  The realization -/

/-- The interior point of every open cell maps onto the cell's points. -/
theorem real_cellOf (x : Fin 2 → AddCircle (1 : ℝ)) :
    DeltaSimplexMap.real torus2SimplexMap (cellOf x) = x := by
  unfold cellOf
  split_ifs with h1 h2 h3 h4 h5
  · simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap,
      toSSetObjEquiv_torus2Chi]
    exact torus2CellReal.2.2.2.2.2 x h1.1 h1.2
  · simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap,
      toSSetObjEquiv_torus2Chi]
    exact torus2CellReal.2.2.1 x h2 (lt_of_le_of_ne (ux_mem x).1 (fun h => h1 ⟨h.symm, h2⟩))
  · simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap,
      toSSetObjEquiv_torus2Chi]
    exact torus2CellReal.2.2.2.1 x h3 (lt_of_le_of_ne (uy_mem x).1 (fun h => h1 ⟨h3, h.symm⟩))
  · simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap,
      toSSetObjEquiv_torus2Chi]
    exact torus2CellReal.2.2.2.2.1 x (lt_of_le_of_ne (ux_mem x).1 (fun h => h3 h.symm)) h4
  · simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap,
      toSSetObjEquiv_torus2Chi]
    exact torus2CellReal.1 x (lt_of_le_of_ne (uy_mem x).1 (fun h => h2 h.symm)) h5
  · simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap,
      toSSetObjEquiv_torus2Chi]
    exact torus2CellReal.2.1 x (lt_of_le_of_ne (ux_mem x).1 (fun h => h3 h.symm))
      (lt_of_le_of_ne (le_of_not_gt h5) h4)

/-- Two open simplices with the same dimension, simplex and interior point are equal. -/
theorem openSimplex_eq {d : ℕ} {σ τ : Fin (torus2DeltaCx.card d)}
    {w w' : StdSimplex ℝ (Fin (d + 1))} {a : IsOpenSimplexPoint d w} {b : IsOpenSimplexPoint d w'}
    (hσ : σ = τ) (hw : w = w') :
    (⟨d, σ, w, a⟩ : OpenSimplex torus2DeltaCx) = ⟨d, τ, w', b⟩ := by
  subst hσ
  subst hw
  exact congrArg (fun (r : IsOpenSimplexPoint d w) =>
    (⟨d, σ, w, r⟩ : OpenSimplex torus2DeltaCx)) (Subsingleton.elim _ _)

/-- All elements of the vertex index type are equal. -/
theorem eq_idxV {σ : Fin (torus2DeltaCx.card 0)} : σ = idxV := by
  have hc : torus2DeltaCx.card 0 = 1 := rfl
  apply Fin.ext
  have h := σ.isLt
  have h0 : idxV.val = 0 := rfl
  omega

/-- The points of the standard `0`-simplex are all equal. -/
theorem eq_ptV {w : StdSimplex ℝ (Fin (torus2DeltaCx.card 0))} : w = ptV := by
  haveI : Subsingleton (Fin (torus2DeltaCx.card 0)) :=
    ⟨fun a b => (eq_idxV (σ := a)).trans (eq_idxV (σ := b)).symm⟩
  exact Subsingleton.elim w ptV

/-! ### The branches of `cellOf` -/

theorem cellOf_eq_v {x : Fin 2 → AddCircle (1 : ℝ)} (h1 : ux x = 0) (h2 : uy x = 0) :
    cellOf x = (⟨0, idxV, ptV, ptV_pos⟩ : OpenSimplex torus2DeltaCx) := by
  unfold cellOf
  rw [dite_eq_left (show ux x = 0 ∧ uy x = 0 from ⟨h1, h2⟩)]

theorem cellOf_eq_a {x : Fin 2 → AddCircle (1 : ℝ)}
    (h1 : ¬(ux x = 0 ∧ uy x = 0)) (h2 : uy x = 0) :
    cellOf x = (⟨1, idxA, ptA x,
      ptA_pos x (lt_of_le_of_ne (ux_mem x).1 (fun h => h1 ⟨h.symm, h2⟩))⟩ :
        OpenSimplex torus2DeltaCx) := by
  unfold cellOf
  rw [dite_eq_right h1, dite_eq_left h2]

theorem cellOf_eq_b {x : Fin 2 → AddCircle (1 : ℝ)}
    (h1 : ¬(ux x = 0 ∧ uy x = 0)) (h2 : ¬(uy x = 0)) (h3 : ux x = 0) :
    cellOf x = (⟨1, idxB, ptB x,
      ptB_pos x (lt_of_le_of_ne (uy_mem x).1 (fun h => h1 ⟨h3, h.symm⟩))⟩ :
        OpenSimplex torus2DeltaCx) := by
  unfold cellOf
  rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]

theorem cellOf_eq_c {x : Fin 2 → AddCircle (1 : ℝ)}
    (h1 : ¬(ux x = 0 ∧ uy x = 0)) (h2 : ¬(uy x = 0)) (h3 : ¬(ux x = 0)) (h4 : ux x = uy x) :
    cellOf x = (⟨1, idxC, ptC x,
      ptA_pos x (lt_of_le_of_ne (ux_mem x).1 (fun h => h3 h.symm))⟩ :
        OpenSimplex torus2DeltaCx) := by
  unfold cellOf
  rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3, dite_eq_left h4]

theorem cellOf_eq_t0 {x : Fin 2 → AddCircle (1 : ℝ)}
    (h1 : ¬(ux x = 0 ∧ uy x = 0)) (h2 : ¬(uy x = 0)) (h3 : ¬(ux x = 0))
    (h4 : ¬(ux x = uy x)) (h5 : uy x < ux x) :
    cellOf x = (⟨2, idxT0, ptT0 x h5.le,
      ptT0_pos x (lt_of_le_of_ne (uy_mem x).1 (fun h => h2 h.symm)) h5⟩ :
        OpenSimplex torus2DeltaCx) := by
  unfold cellOf
  rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3, dite_eq_right h4, dite_eq_left h5]

theorem cellOf_eq_t1 {x : Fin 2 → AddCircle (1 : ℝ)}
    (h1 : ¬(ux x = 0 ∧ uy x = 0)) (h2 : ¬(uy x = 0)) (h3 : ¬(ux x = 0))
    (h4 : ¬(ux x = uy x)) (h5 : ¬(uy x < ux x)) :
    cellOf x = (⟨2, idxT1, ptT1 x (le_of_not_gt h5),
      ptT1_pos x (lt_of_le_of_ne (ux_mem x).1 (fun h => h3 h.symm))
        (lt_of_le_of_ne (le_of_not_gt h5) h4)⟩ :
        OpenSimplex torus2DeltaCx) := by
  unfold cellOf
  rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3, dite_eq_right h4, dite_eq_right h5]

/-- The two elements of `Fin 2`. -/
theorem fin_two_eq (j : Fin 2) : j = 0 ∨ j = 1 := by
  have h : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- The three elements of `Fin 3`. -/
theorem fin_three_eq (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  have h : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by have := j.isLt; omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-! ### The comparison of `real` with the characteristic maps -/

theorem real_vertex {x : Fin 2 → AddCircle (1 : ℝ)} {w : StdSimplex ℝ (Fin 1)}
    {hw : IsOpenSimplexPoint 0 w} {σ : Fin (torus2DeltaCx.card 0)}
    (hp : DeltaSimplexMap.real torus2SimplexMap
      (⟨0, σ, w, hw⟩ : OpenSimplex torus2DeltaCx) = x) : chiV w = x := by
  have h := hp
  simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap] at h
  rw [toSSetObjEquiv_torus2Chi] at h
  rw [show σ = idxV from eq_idxV] at h
  rwa [show torus2ChiCls 0 idxV = chiV from rfl] at h

theorem real_edge_a {x : Fin 2 → AddCircle (1 : ℝ)} {w : StdSimplex ℝ (Fin 2)}
    {hw : IsOpenSimplexPoint 1 w} {σ : Fin (torus2DeltaCx.card 1)} (hσ : σ = idxA)
    (hp : DeltaSimplexMap.real torus2SimplexMap
      (⟨1, σ, w, hw⟩ : OpenSimplex torus2DeltaCx) = x) : chiA w = x := by
  have h := hp
  simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap] at h
  rw [toSSetObjEquiv_torus2Chi] at h
  rw [hσ] at h
  rwa [show torus2ChiCls 1 idxA = chiA from rfl] at h

theorem real_edge_b {x : Fin 2 → AddCircle (1 : ℝ)} {w : StdSimplex ℝ (Fin 2)}
    {hw : IsOpenSimplexPoint 1 w} {σ : Fin (torus2DeltaCx.card 1)} (hσ : σ = idxB)
    (hp : DeltaSimplexMap.real torus2SimplexMap
      (⟨1, σ, w, hw⟩ : OpenSimplex torus2DeltaCx) = x) : chiB w = x := by
  have h := hp
  simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap] at h
  rw [toSSetObjEquiv_torus2Chi] at h
  rw [hσ] at h
  rwa [show torus2ChiCls 1 idxB = chiB from rfl] at h

theorem real_edge_c {x : Fin 2 → AddCircle (1 : ℝ)} {w : StdSimplex ℝ (Fin 2)}
    {hw : IsOpenSimplexPoint 1 w} {σ : Fin (torus2DeltaCx.card 1)} (hσ : σ = idxC)
    (hp : DeltaSimplexMap.real torus2SimplexMap
      (⟨1, σ, w, hw⟩ : OpenSimplex torus2DeltaCx) = x) : chiC w = x := by
  have h := hp
  simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap] at h
  rw [toSSetObjEquiv_torus2Chi] at h
  rw [hσ] at h
  rwa [show torus2ChiCls 1 idxC = chiC from rfl] at h

theorem real_tri0 {x : Fin 2 → AddCircle (1 : ℝ)} {w : StdSimplex ℝ (Fin 3)}
    {hw : IsOpenSimplexPoint 2 w} {σ : Fin (torus2DeltaCx.card 2)} (hσ : σ = idxT0)
    (hp : DeltaSimplexMap.real torus2SimplexMap
      (⟨2, σ, w, hw⟩ : OpenSimplex torus2DeltaCx) = x) : chiT0 w = x := by
  have h := hp
  simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap] at h
  rw [toSSetObjEquiv_torus2Chi] at h
  rw [hσ] at h
  rwa [show torus2ChiCls 2 idxT0 = chiT0 from rfl] at h

theorem real_tri1 {x : Fin 2 → AddCircle (1 : ℝ)} {w : StdSimplex ℝ (Fin 3)}
    {hw : IsOpenSimplexPoint 2 w} {σ : Fin (torus2DeltaCx.card 2)} (hσ : σ = idxT1)
    (hp : DeltaSimplexMap.real torus2SimplexMap
      (⟨2, σ, w, hw⟩ : OpenSimplex torus2DeltaCx) = x) : chiT1 w = x := by
  have h := hp
  simp only [DeltaSimplexMap.real, DeltaSimplexMap.cls, torus2SimplexMap] at h
  rw [toSSetObjEquiv_torus2Chi] at h
  rw [hσ] at h
  rwa [show torus2ChiCls 2 idxT1 = chiT1 from rfl] at h

/-- The open simplex containing a point is unique: any open simplex whose characteristic map
passes through `x` is `cellOf x`. -/
theorem eq_cellOf {x : Fin 2 → AddCircle (1 : ℝ)} {p : OpenSimplex torus2DeltaCx}
    (hp : DeltaSimplexMap.real torus2SimplexMap p = x) : p = cellOf x := by
  obtain ⟨d, σ, w, hw⟩ := p
  rcases d with _ | _ | _ | k
  · -- dimension `0`: the vertex
    have hV : ux x = 0 ∧ uy x = 0 :=
      torus2CellWeights.2.2.2.2.2 x w (real_vertex hp)
    rw [cellOf_eq_v hV.1 hV.2]
    apply openSimplex_eq
    · exact eq_idxV
    · exact eq_ptV
  · -- dimension `1`: the three edges
    obtain ⟨v, hv⟩ := σ
    have hv3 : v < 3 := by simpa [torus2DeltaCx_card_one] using hv
    have hv' : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    rcases hv' with rfl | rfl | rfl
    · -- the edge `a`
      have h0 : w.weights 0 = 1 - ux x := by
        have hA := torus2CellWeights.2.2.1 x w hw (real_edge_a (Fin.ext rfl) hp)
        have := w.total_fin_two
        linarith [hA.1]
      have hA : ux x = w.weights 1 ∧ uy x = 0 :=
        torus2CellWeights.2.2.1 x w hw (real_edge_a (Fin.ext rfl) hp)
      have hpos1 : 0 < ux x := by rw [hA.1]; exact hw 1
      rw [cellOf_eq_a (fun hh => absurd hh.1 (ne_of_gt hpos1)) hA.2]
      apply openSimplex_eq
      · exact Fin.ext rfl
      · apply StdSimplex.ext
        apply Finsupp.ext
        intro j
        have h : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
        rcases h with h | h
        · rw [show j = 0 from Fin.ext h, ptA_weights_zero]; exact h0
        · rw [show j = 1 from Fin.ext h, ptA_weights_one]; exact hA.1.symm
    · -- the edge `b`
      have hB : uy x = w.weights 1 ∧ ux x = 0 :=
        torus2CellWeights.2.2.2.1 x w hw (real_edge_b (Fin.ext rfl) hp)
      have hpos1 : 0 < uy x := by rw [hB.1]; exact hw 1
      have h0 : w.weights 0 = 1 - uy x := by
        have := w.total_fin_two; linarith [hB.1]
      rw [cellOf_eq_b (fun hh => absurd hh.2 (ne_of_gt hpos1)) (ne_of_gt hpos1) hB.2]
      apply openSimplex_eq
      · exact Fin.ext rfl
      · apply StdSimplex.ext
        apply Finsupp.ext
        intro j
        have h : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
        rcases h with h | h
        · rw [show j = 0 from Fin.ext h, ptB_weights_zero]; exact h0
        · rw [show j = 1 from Fin.ext h, ptB_weights_one]; exact hB.1.symm
    · -- the edge `c`
      have hC : ux x = w.weights 1 ∧ uy x = w.weights 1 :=
        torus2CellWeights.2.2.2.2.1 x w hw (real_edge_c (Fin.ext rfl) hp)
      have hpos1 : 0 < ux x := by rw [hC.1]; exact hw 1
      have h0 : w.weights 0 = 1 - ux x := by
        have := w.total_fin_two; linarith [hC.1]
      have huy : uy x ≠ 0 := by rw [hC.2, ← hC.1]; exact ne_of_gt hpos1
      rw [cellOf_eq_c (fun hh => absurd hh.1 (ne_of_gt hpos1)) huy
        (ne_of_gt hpos1) (hC.1.trans hC.2.symm)]
      apply openSimplex_eq
      · exact Fin.ext rfl
      · apply StdSimplex.ext
        apply Finsupp.ext
        intro j
        have h : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
        rcases h with h | h
        · rw [show j = 0 from Fin.ext h]; rw [show (ptC x) = ptA x from rfl, ptA_weights_zero]
          exact h0
        · rw [show j = 1 from Fin.ext h]; rw [show (ptC x) = ptA x from rfl, ptA_weights_one]
          exact hC.1.symm
  · -- dimension `2`: the two triangles
    obtain ⟨v, hv⟩ := σ
    have hv2 : v < 2 := by simpa [torus2DeltaCx_card_two] using hv
    have hv' : v = 0 ∨ v = 1 := by omega
    rcases hv' with rfl | rfl
    · -- the triangle `T₀`
      have hT : uy x = w.weights 2 ∧ ux x = w.weights 1 + w.weights 2 :=
        torus2CellWeights.1 x w hw (real_tri0 (Fin.ext rfl) hp)
      have hpos1 : 0 < uy x := by rw [hT.1]; exact hw 2
      have hlt : uy x < ux x := by rw [hT.1, hT.2]; linarith [hw 1]
      have hpos0 : 0 < ux x := lt_trans hpos1 hlt
      have hsum : w.weights 0 + w.weights 1 + w.weights 2 = 1 := by
        have h := w.total_of_fintype
        rw [Fin.sum_univ_three] at h
        exact h
      rw [cellOf_eq_t0 (fun hh => absurd hh.1 (ne_of_gt hpos0)) (ne_of_gt hpos1)
        (ne_of_gt hpos0) (fun hh => absurd hh.symm (ne_of_lt hlt)) hlt]
      apply openSimplex_eq
      · exact Fin.ext rfl
      · apply StdSimplex.ext
        apply Finsupp.ext
        intro j
        have h : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by have := j.isLt; omega
        rcases h with h | h | h
        · rw [show j = 0 from Fin.ext h, ptT0_weights_zero]; linarith
        · rw [show j = 1 from Fin.ext h, ptT0_weights_one]; linarith
        · rw [show j = 2 from Fin.ext h, ptT0_weights_two]; exact hT.1.symm
    · -- the triangle `T₁`
      have hT : ux x = w.weights 2 ∧ uy x = w.weights 1 + w.weights 2 :=
        torus2CellWeights.2.1 x w hw (real_tri1 (Fin.ext rfl) hp)
      have hpos1 : 0 < ux x := by rw [hT.1]; exact hw 2
      have hlt : ux x < uy x := by rw [hT.1, hT.2]; linarith [hw 1]
      have hpos0 : 0 < uy x := lt_trans hpos1 hlt
      have hsum : w.weights 0 + w.weights 1 + w.weights 2 = 1 := by
        have h := w.total_of_fintype
        rw [Fin.sum_univ_three] at h
        exact h
      rw [cellOf_eq_t1 (fun hh => absurd hh.1 (ne_of_gt hpos1)) (ne_of_gt hpos0)
        (ne_of_gt hpos1) (ne_of_lt hlt) (not_lt.mpr hlt.le)]
      apply openSimplex_eq
      · exact Fin.ext rfl
      · apply StdSimplex.ext
        apply Finsupp.ext
        intro j
        have h : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by have := j.isLt; omega
        rcases h with h | h | h
        · rw [show j = 0 from Fin.ext h, ptT1_weights_zero]; linarith
        · rw [show j = 1 from Fin.ext h, ptT1_weights_one]; linarith
        · rw [show j = 2 from Fin.ext h, ptT1_weights_two]; exact hT.1.symm
  · -- no simplices above dimension `2`
    exact Fin.elim0 σ

/-- **The realization of the `Δ`-structure of the torus.** -/
def torus2RealizationData : DeltaRealization torus2DeltaCx Torus2Space where
  toDeltaSimplexMap := torus2SimplexMap
  compact := inferInstance
  t2 := inferInstance
  bij := fun x => ⟨cellOf x, real_cellOf x, fun q hq => eq_cellOf hq⟩
  weak := fun s => ⟨fun hs k σ => by
      simp only [DeltaSimplexMap.cls, torus2SimplexMap]
      exact (TopCat.toSSetObjEquiv Torus2Space (Opposite.op (SimplexCategory.mk k))
        (torus2Chi k σ)).continuous.isOpen_preimage s hs,
    fun h => torus2_weakTopology s (fun k σ => isOpen_chiCls_preimage s h k σ) torus2_cover⟩

/-- **The `Δ`-structure of the torus is realized in the torus.** -/
theorem torus2Realization :
    Nonempty (Work.DeltaHomology.DeltaRealization Work.PieceHomology.torus2DeltaCx
      (TopCat.of (Fin 2 → AddCircle (1 : ℝ)))) :=
  ⟨torus2RealizationData⟩

end

end Work.PieceHomology
