/-
# The characteristic maps of the `Δ`-structure of the `2`-torus

Definitions shared by the construction of the `Δ`-realization of
`Work.PieceHomology.torus2DeltaCx` in `T² = (ℝ/ℤ)²` (`Submission/Work/PieceHomology/torus2Realization.lean`).

The geometry is the standard "square with opposite sides identified, cut along the diagonal":

* the vertex is `(0,0)`;
* the edges are the loops `a : t ↦ (t,0)`, `b : t ↦ (0,t)`, `c : t ↦ (t,t)`;
* the triangles are
  `T₀ : (w₀,w₁,w₂) ↦ (w₁+w₂, w₂)` (the lower triangle `0 < y < x < 1`),
  `T₁ : (w₀,w₁,w₂) ↦ (w₂, w₁+w₂)` (the upper triangle `0 < x < y < 1`).

The characteristic maps are continuous maps `Δ^k → T²`; `torus2ChiCls k σ` is the one of the
`σ`-th `k`-simplex, `torus2Chi k σ` the corresponding singular simplex of `T²` (under the
identification `(TopCat.toSSet.obj X).obj (op [k]) ≃ C(Δ^k, X)`).
-/
import Mathlib
import Submission.Work.PieceHomology.Torus2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open Convexity
open scoped Topology

open Work.DeltaHomology

namespace Work.PieceHomology

noncomputable section

/-! ## §1  The characteristic maps -/

/-- The point `(u,v)` of the torus `T² = (ℝ/ℤ)²`. -/
def tpt (u v : AddCircle (1 : ℝ)) : Fin 2 → AddCircle (1 : ℝ) := ![u, v]

@[simp] theorem tpt_apply_zero (u v : AddCircle (1 : ℝ)) : tpt u v 0 = u := rfl

@[simp] theorem tpt_apply_one (u v : AddCircle (1 : ℝ)) : tpt u v 1 = v := rfl

@[simp] theorem tpt_zero_zero : tpt 0 0 = (fun _ : Fin 2 => (0 : AddCircle (1 : ℝ))) := by
  funext i
  fin_cases i <;> rfl

/-- The characteristic map of the unique vertex: a point, mapped to `(0,0)`. -/
def chiV : C(StdSimplex ℝ (Fin 1), Fin 2 → AddCircle (1 : ℝ)) :=
  ContinuousMap.const _ (tpt 0 0)

/-- The characteristic map of the edge `a = (t,0)`. -/
def chiA : C(StdSimplex ℝ (Fin 2), Fin 2 → AddCircle (1 : ℝ)) :=
  ⟨fun z => tpt (((z.weights 1 : ℝ)) : AddCircle (1 : ℝ)) 0, by unfold tpt; fun_prop⟩

/-- The characteristic map of the edge `b = (0,t)`. -/
def chiB : C(StdSimplex ℝ (Fin 2), Fin 2 → AddCircle (1 : ℝ)) :=
  ⟨fun z => tpt 0 (((z.weights 1 : ℝ)) : AddCircle (1 : ℝ)), by unfold tpt; fun_prop⟩

/-- The characteristic map of the edge `c = (t,t)`. -/
def chiC : C(StdSimplex ℝ (Fin 2), Fin 2 → AddCircle (1 : ℝ)) :=
  ⟨fun z => tpt (((z.weights 1 : ℝ)) : AddCircle (1 : ℝ))
      (((z.weights 1 : ℝ)) : AddCircle (1 : ℝ)), by unfold tpt; fun_prop⟩

/-- The characteristic map of the triangle `T₀ = (w₀,w₁,w₂) ↦ (w₁+w₂, w₂)`. -/
def chiT0 : C(StdSimplex ℝ (Fin 3), Fin 2 → AddCircle (1 : ℝ)) :=
  ⟨fun w => tpt (((w.weights 1 + w.weights 2 : ℝ)) : AddCircle (1 : ℝ))
      (((w.weights 2 : ℝ)) : AddCircle (1 : ℝ)), by unfold tpt; fun_prop⟩

/-- The characteristic map of the triangle `T₁ = (w₀,w₁,w₂) ↦ (w₂, w₁+w₂)`. -/
def chiT1 : C(StdSimplex ℝ (Fin 3), Fin 2 → AddCircle (1 : ℝ)) :=
  ⟨fun w => tpt (((w.weights 2 : ℝ)) : AddCircle (1 : ℝ))
      (((w.weights 1 + w.weights 2 : ℝ)) : AddCircle (1 : ℝ)), by unfold tpt; fun_prop⟩

/-- The characteristic maps of the three edges, indexed as in `torus2DeltaCx`. -/
def chiE : Fin 3 → C(StdSimplex ℝ (Fin 2), Fin 2 → AddCircle (1 : ℝ)) :=
  ![chiA, chiB, chiC]

/-- The characteristic maps of the two triangles, indexed as in `torus2DeltaCx`. -/
def chiT : Fin 2 → C(StdSimplex ℝ (Fin 3), Fin 2 → AddCircle (1 : ℝ)) :=
  ![chiT0, chiT1]

@[simp] theorem chiE_zero : chiE 0 = chiA := rfl

@[simp] theorem chiE_one : chiE 1 = chiB := rfl

@[simp] theorem chiE_two : chiE 2 = chiC := rfl

@[simp] theorem chiT_zero : chiT 0 = chiT0 := rfl

@[simp] theorem chiT_one : chiT 1 = chiT1 := rfl

/-- The characteristic map of the `σ`-th `k`-simplex of `torus2DeltaCx`, as a continuous map
`Δ^k → T²`. -/
def torus2ChiCls : (k : ℕ) → Fin (torus2Card k) →
    C(StdSimplex ℝ (Fin (k + 1)), Fin 2 → AddCircle (1 : ℝ))
  | 0, _ => chiV
  | 1, i => chiE i
  | 2, σ => chiT σ
  | (_ + 3), i => Fin.elim0 i

theorem torus2ChiCls_zero : torus2ChiCls 0 = fun _ => chiV := rfl

@[simp] theorem torus2ChiCls_one (i : Fin 3) : torus2ChiCls 1 i = chiE i := rfl

@[simp] theorem torus2ChiCls_two (σ : Fin 2) : torus2ChiCls 2 σ = chiT σ := rfl

/-- The characteristic maps as singular simplices of the torus. -/
def torus2Chi (k : ℕ) (σ : Fin (torus2DeltaCx.card k)) :
    (TopCat.toSSet.obj Torus2Space).obj (Opposite.op (SimplexCategory.mk k)) :=
  (TopCat.toSSetObjEquiv Torus2Space (Opposite.op (SimplexCategory.mk k))).symm
    (torus2ChiCls k σ)

/-- The characteristic map attached to a singular simplex is recovered by `toSSetObjEquiv`. -/
@[simp] theorem toSSetObjEquiv_torus2Chi (k : ℕ) (σ : Fin (torus2DeltaCx.card k)) :
    TopCat.toSSetObjEquiv Torus2Space (Opposite.op (SimplexCategory.mk k)) (torus2Chi k σ)
      = torus2ChiCls k σ :=
  Equiv.apply_symm_apply _ _

/-! ## §2  The coordinates `[0,1)` on `ℝ/ℤ` -/

/-- The canonical representative in `[0,1)` of a point of `ℝ/ℤ`. -/
def coord (u : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 u).1

theorem coord_mem (u : AddCircle (1 : ℝ)) : coord u ∈ Set.Ico (0 : ℝ) 1 := by
  simpa [coord] using (AddCircle.equivIco (1 : ℝ) 0 u).2

@[simp] theorem coe_coord (u : AddCircle (1 : ℝ)) : ((coord u : ℝ) : AddCircle (1 : ℝ)) = u :=
  AddCircle.coe_equivIco

theorem coord_coe {a : ℝ} (ha : a ∈ Set.Ico (0 : ℝ) 1) :
    coord ((a : AddCircle (1 : ℝ))) = a := by
  have h : a ∈ Set.Ico (0 : ℝ) (0 + 1) := by simpa using ha
  rw [coord, AddCircle.equivIco_coe_eq h]

/-- Two reals in `[0,1)` with the same class in `ℝ/ℤ` are equal. -/
theorem coe_eq_coe_iff_Ico {a b : ℝ} (ha : a ∈ Set.Ico (0 : ℝ) 1) (hb : b ∈ Set.Ico (0 : ℝ) 1) :
    ((a : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ))) ↔ a = b := by
  have ha' : a ∈ Set.Ico (0 : ℝ) (0 + 1) := by simpa using ha
  have hb' : b ∈ Set.Ico (0 : ℝ) (0 + 1) := by simpa using hb
  exact AddCircle.coe_eq_coe_iff_of_mem_Ico ha' hb'

/-! ## §3  The cells of the `Δ`-structure -/

/-- The first coordinate (in `[0,1)`) of a point of the torus. -/
def ux (x : Fin 2 → AddCircle (1 : ℝ)) : ℝ := coord (x 0)

/-- The second coordinate (in `[0,1)`) of a point of the torus. -/
def uy (x : Fin 2 → AddCircle (1 : ℝ)) : ℝ := coord (x 1)

theorem ux_mem (x : Fin 2 → AddCircle (1 : ℝ)) : ux x ∈ Set.Ico (0 : ℝ) 1 := coord_mem _

theorem uy_mem (x : Fin 2 → AddCircle (1 : ℝ)) : uy x ∈ Set.Ico (0 : ℝ) 1 := coord_mem _

theorem coe_ux (x : Fin 2 → AddCircle (1 : ℝ)) : ((ux x : ℝ) : AddCircle (1 : ℝ)) = x 0 :=
  coe_coord _

theorem coe_uy (x : Fin 2 → AddCircle (1 : ℝ)) : ((uy x : ℝ) : AddCircle (1 : ℝ)) = x 1 :=
  coe_coord _

/-- Every point of the torus is `(ux, uy)` in the coordinates `[0,1)`. -/
theorem tpt_ux_uy (x : Fin 2 → AddCircle (1 : ℝ)) :
    tpt ((ux x : ℝ) : AddCircle (1 : ℝ)) ((uy x : ℝ) : AddCircle (1 : ℝ)) = x := by
  funext i
  fin_cases i
  · simp [tpt, ux, coe_coord]
  · simp [tpt, uy, coe_coord]

/-- The six open cells of the `Δ`-structure of the torus, in the order in which they occur. -/
inductive Torus2Cell : Type
  | v : Torus2Cell
  | a : Torus2Cell
  | b : Torus2Cell
  | c : Torus2Cell
  | t0 : Torus2Cell
  | t1 : Torus2Cell
  deriving DecidableEq

/-- The locus of each open cell, in the coordinates `[0,1)`. -/
def Torus2Cell.cond : Torus2Cell → (Fin 2 → AddCircle (1 : ℝ)) → Prop
  | v, x => ux x = 0 ∧ uy x = 0
  | a, x => uy x = 0 ∧ 0 < ux x
  | b, x => ux x = 0 ∧ 0 < uy x
  | c, x => 0 < ux x ∧ ux x = uy x
  | t0, x => 0 < uy x ∧ uy x < ux x
  | t1, x => 0 < ux x ∧ ux x < uy x

/-- The standard `2`-simplex point with barycentric weights `a, b, c`. -/
def stdSimplex3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1) :
    StdSimplex ℝ (Fin 3) where
  weights := Finsupp.equivFunOnFinite.symm ![a, b, c]
  nonneg := by
    rw [Finsupp.le_def]
    intro i
    fin_cases i
    · simpa [Finsupp.equivFunOnFinite_symm_apply_apply] using ha
    · simpa [Finsupp.equivFunOnFinite_symm_apply_apply] using hb
    · simpa [Finsupp.equivFunOnFinite_symm_apply_apply] using hc
  total := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp [Finsupp.equivFunOnFinite_symm_apply_apply, Fin.sum_univ_three, h]

@[simp] theorem stdSimplex3_weights_zero
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1) :
    (stdSimplex3 a b c ha hb hc h).weights 0 = a := by
  simp [stdSimplex3, Finsupp.equivFunOnFinite_symm_apply_apply]

@[simp] theorem stdSimplex3_weights_one
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1) :
    (stdSimplex3 a b c ha hb hc h).weights 1 = b := by
  simp [stdSimplex3, Finsupp.equivFunOnFinite_symm_apply_apply]

@[simp] theorem stdSimplex3_weights_two
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1) :
    (stdSimplex3 a b c ha hb hc h).weights 2 = c := by
  simp [stdSimplex3, Finsupp.equivFunOnFinite_symm_apply_apply]

/-! ### The interior points of the six open cells -/

/-- The (unique) point of `Δ⁰`. -/
def ptV : StdSimplex ℝ (Fin 1) := StdSimplex.single 0

theorem ptV_pos : IsOpenSimplexPoint 0 ptV := by
  intro i
  fin_cases i
  simp [ptV]

/-- The point of `Δ¹` with barycentric weights `(1 - s, s)`. -/
def pt2 (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) : StdSimplex ℝ (Fin 2) :=
  StdSimplex.duple (0 : Fin 2) 1 (s := 1 - s) (t := s) (by linarith) hs (by ring)

@[simp] theorem pt2_weights_zero (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (pt2 s hs hs1).weights 0 = 1 - s := by
  simp [pt2, StdSimplex.weights_duple]

@[simp] theorem pt2_weights_one (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (pt2 s hs hs1).weights 1 = s := by
  simp [pt2, StdSimplex.weights_duple]

theorem pt2_pos (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    IsOpenSimplexPoint 1 (pt2 s hs.le hs1.le) := by
  intro i
  fin_cases i
  · simpa using (show (0 : ℝ) < 1 - s by linarith)
  · simpa using hs

/-- The point of `Δ¹` associated with the open edge `a` (resp. `c`): weights `(1 - ux, ux)`. -/
def ptA (x : Fin 2 → AddCircle (1 : ℝ)) : StdSimplex ℝ (Fin 2) :=
  pt2 (ux x) (ux_mem x).1 (ux_mem x).2.le

/-- The point of `Δ¹` associated with the open edge `b`: weights `(1 - uy, uy)`. -/
def ptB (x : Fin 2 → AddCircle (1 : ℝ)) : StdSimplex ℝ (Fin 2) :=
  pt2 (uy x) (uy_mem x).1 (uy_mem x).2.le

/-- The point of `Δ¹` associated with the open edge `c`: weights `(1 - ux, ux)`. -/
def ptC (x : Fin 2 → AddCircle (1 : ℝ)) : StdSimplex ℝ (Fin 2) := ptA x

@[simp] theorem ptA_weights_zero (x) : (ptA x).weights 0 = 1 - ux x := by
  simp [ptA]

@[simp] theorem ptA_weights_one (x) : (ptA x).weights 1 = ux x := by
  simp [ptA]

@[simp] theorem ptB_weights_zero (x) : (ptB x).weights 0 = 1 - uy x := by
  simp [ptB]

@[simp] theorem ptB_weights_one (x) : (ptB x).weights 1 = uy x := by
  simp [ptB]

theorem ptA_pos (x) (h : 0 < ux x) : IsOpenSimplexPoint 1 (ptA x) :=
  pt2_pos (ux x) h (ux_mem x).2

theorem ptB_pos (x) (h : 0 < uy x) : IsOpenSimplexPoint 1 (ptB x) :=
  pt2_pos (uy x) h (uy_mem x).2

/-- The point of `Δ²` associated with the open triangle `T₀`: weights `(1-ux, ux-uy, uy)`. -/
def ptT0 (x : Fin 2 → AddCircle (1 : ℝ)) (h : uy x ≤ ux x) : StdSimplex ℝ (Fin 3) :=
  stdSimplex3 (1 - ux x) (ux x - uy x) (uy x)
    (by linarith [(ux_mem x).2]) (by linarith) (by linarith [(uy_mem x).1]) (by ring)

/-- The point of `Δ²` associated with the open triangle `T₁`: weights `(1-uy, uy-ux, ux)`. -/
def ptT1 (x : Fin 2 → AddCircle (1 : ℝ)) (h : ux x ≤ uy x) : StdSimplex ℝ (Fin 3) :=
  stdSimplex3 (1 - uy x) (uy x - ux x) (ux x)
    (by linarith [(uy_mem x).2]) (by linarith) (by linarith [(ux_mem x).1]) (by ring)

@[simp] theorem ptT0_weights_zero (x) (h : uy x ≤ ux x) : (ptT0 x h).weights 0 = 1 - ux x := by
  simp [ptT0]

@[simp] theorem ptT0_weights_one (x) (h : uy x ≤ ux x) : (ptT0 x h).weights 1 = ux x - uy x := by
  simp [ptT0]

@[simp] theorem ptT0_weights_two (x) (h : uy x ≤ ux x) : (ptT0 x h).weights 2 = uy x := by
  simp [ptT0]

@[simp] theorem ptT1_weights_zero (x) (h : ux x ≤ uy x) : (ptT1 x h).weights 0 = 1 - uy x := by
  simp [ptT1]

@[simp] theorem ptT1_weights_one (x) (h : ux x ≤ uy x) : (ptT1 x h).weights 1 = uy x - ux x := by
  simp [ptT1]

@[simp] theorem ptT1_weights_two (x) (h : ux x ≤ uy x) : (ptT1 x h).weights 2 = ux x := by
  simp [ptT1]

theorem ptT0_pos (x) (h1 : 0 < uy x) (h2 : uy x < ux x) : IsOpenSimplexPoint 2 (ptT0 x h2.le) := by
  intro i
  fin_cases i
  · simpa using (show (0 : ℝ) < 1 - ux x by linarith [(ux_mem x).2])
  · simpa using (show (0 : ℝ) < ux x - uy x by linarith)
  · simpa using h1

theorem ptT1_pos (x) (h1 : 0 < ux x) (h2 : ux x < uy x) : IsOpenSimplexPoint 2 (ptT1 x h2.le) := by
  intro i
  fin_cases i
  · simpa using (show (0 : ℝ) < 1 - uy x by linarith [(uy_mem x).2])
  · simpa using (show (0 : ℝ) < uy x - ux x by linarith)
  · simpa using h1

/-! ### The open simplex containing a point -/

@[simp] theorem torus2DeltaCx_card_zero : torus2DeltaCx.card 0 = 1 := rfl

@[simp] theorem torus2DeltaCx_card_one : torus2DeltaCx.card 1 = 3 := rfl

@[simp] theorem torus2DeltaCx_card_two : torus2DeltaCx.card 2 = 2 := rfl

/-- The index of the unique vertex of `torus2DeltaCx`. -/
def idxV : Fin (torus2DeltaCx.card 0) := ⟨0, by simp [torus2DeltaCx_card]⟩

/-- The index of the edge `a`. -/
def idxA : Fin (torus2DeltaCx.card 1) := ⟨0, by simp [torus2DeltaCx_card]⟩

/-- The index of the edge `b`. -/
def idxB : Fin (torus2DeltaCx.card 1) := ⟨1, by simp [torus2DeltaCx_card]⟩

/-- The index of the edge `c`. -/
def idxC : Fin (torus2DeltaCx.card 1) := ⟨2, by simp [torus2DeltaCx_card]⟩

/-- The index of the triangle `T₀`. -/
def idxT0 : Fin (torus2DeltaCx.card 2) := ⟨0, by simp [torus2DeltaCx_card]⟩

/-- The index of the triangle `T₁`. -/
def idxT1 : Fin (torus2DeltaCx.card 2) := ⟨1, by simp [torus2DeltaCx_card]⟩

/-- The cell of the `Δ`-structure containing a point of the torus, decided by its coordinates. -/
def cellIndex (x : Fin 2 → AddCircle (1 : ℝ)) : Torus2Cell :=
  if ux x = 0 ∧ uy x = 0 then Torus2Cell.v
  else if uy x = 0 then Torus2Cell.a
  else if ux x = 0 then Torus2Cell.b
  else if ux x = uy x then Torus2Cell.c
  else if uy x < ux x then Torus2Cell.t0
  else Torus2Cell.t1

/-- The interior of a cell, as an open simplex of `torus2DeltaCx`. -/
def cellSimplex (i : Torus2Cell) (x : Fin 2 → AddCircle (1 : ℝ)) (h : i.cond x) :
    OpenSimplex torus2DeltaCx :=
  match i, h with
  | .v, _ => ⟨0, idxV, ptV, ptV_pos⟩
  | .a, h => ⟨1, idxA, ptA x, ptA_pos x h.2⟩
  | .b, h => ⟨1, idxB, ptB x, ptB_pos x h.2⟩
  | .c, h => ⟨1, idxC, ptC x, ptA_pos x h.1⟩
  | .t0, h => ⟨2, idxT0, ptT0 x h.2.le, ptT0_pos x h.1 h.2⟩
  | .t1, h => ⟨2, idxT1, ptT1 x h.2.le, ptT1_pos x h.1 h.2⟩

theorem cellIndex_cond (x : Fin 2 → AddCircle (1 : ℝ)) : (cellIndex x).cond x := by
  unfold cellIndex
  by_cases h1 : ux x = 0 ∧ uy x = 0
  · rw [ite_eq_left h1]; exact ⟨h1.1, h1.2⟩
  · rw [ite_eq_right h1]
    by_cases h2 : uy x = 0
    · rw [ite_eq_left h2]
      exact ⟨h2, lt_of_le_of_ne (ux_mem x).1 (fun h => h1 ⟨h.symm, h2⟩)⟩
    · rw [ite_eq_right h2]
      by_cases h3 : ux x = 0
      · rw [ite_eq_left h3]
        exact ⟨h3, lt_of_le_of_ne (uy_mem x).1 (fun h => h1 ⟨h3, h.symm⟩)⟩
      · rw [ite_eq_right h3]
        by_cases h4 : ux x = uy x
        · rw [ite_eq_left h4]
          exact ⟨lt_of_le_of_ne (ux_mem x).1 (fun h => h3 h.symm), h4⟩
        · rw [ite_eq_right h4]
          by_cases h5 : uy x < ux x
          · rw [ite_eq_left h5]
            exact ⟨lt_of_le_of_ne (uy_mem x).1 (fun h => h2 h.symm), h5⟩
          · rw [ite_eq_right h5]
            exact ⟨lt_of_le_of_ne (ux_mem x).1 (fun h => h3 h.symm),
              lt_of_le_of_ne (le_of_not_gt h5) (fun h => h4 h)⟩

/-- The open simplex containing a point of the torus.

The branches are the six cells of `Torus2Cell.cond`, in the same order as `cellIndex`; each branch
carries the explicit interior point of the cell (with the positivity of the weights derived from
the branch conditions). -/
def cellOf (x : Fin 2 → AddCircle (1 : ℝ)) : OpenSimplex torus2DeltaCx :=
  if h1 : ux x = 0 ∧ uy x = 0 then ⟨0, idxV, ptV, ptV_pos⟩
  else if h2 : uy x = 0 then
    ⟨1, idxA, ptA x, ptA_pos x (lt_of_le_of_ne (ux_mem x).1 (fun h => h1 ⟨h.symm, h2⟩))⟩
  else if h3 : ux x = 0 then
    ⟨1, idxB, ptB x, ptB_pos x (lt_of_le_of_ne (uy_mem x).1 (fun h => h1 ⟨h3, h.symm⟩))⟩
  else if h4 : ux x = uy x then
    ⟨1, idxC, ptC x, ptA_pos x (lt_of_le_of_ne (ux_mem x).1 (fun h => h3 h.symm))⟩
  else if h5 : uy x < ux x then
    ⟨2, idxT0, ptT0 x h5.le,
      ptT0_pos x (lt_of_le_of_ne (uy_mem x).1 (fun h => h2 h.symm)) h5⟩
  else
    ⟨2, idxT1, ptT1 x (le_of_not_gt h5),
      ptT1_pos x (lt_of_le_of_ne (ux_mem x).1 (fun h => h3 h.symm))
        (lt_of_le_of_ne (le_of_not_gt h5) h4)⟩

end

end Work.PieceHomology
