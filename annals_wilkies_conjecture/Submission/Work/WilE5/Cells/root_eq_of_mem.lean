import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE5.Cells

open WilkiesDesign WilkiesDesign.E
open Work.WilE5

variable {p q : ℕ}

/-- Membership in the set of a state, unfolded: the ambient set `X`, the accumulated vanishing
conditions (`B` and `Ξ`) and the accumulated strict positivity conditions (`ν`). -/
theorem mem_stSemiPf_iff {X : SemiPf (p + q)} (σ : St p q X.r) (z : Fin (p + q) → ℝ) :
    z ∈ (stSemiPf X σ).set ↔
      z ∈ X.set ∧ (∀ f ∈ σ.B.map Prod.fst ++ σ.Ξ, eaEval X.c f z = 0) ∧
        (∀ g ∈ σ.ν, 0 < eaEval X.c g z) := by
  simp [stSemiPf, semiPfAnd_set, stCond, Basic.holds]

/-- The equations of `initSt` with the pivots dropped. -/
theorem initSt_B_map {X : SemiPf (p + q)} (A : Basic (p + q) X.r) (Fy : Finset (Fin q))
    (ε : {l // l ∈ Fy} → Bool) :
    (initSt X A Fy ε).B.map Prod.fst =
      Fy.attach.toList.map (fun l => facePoly (p := p) (q := q) (r := X.r) l.1
        (if ε l then 1 else -1)) := by
  simp [initSt, List.map_map]

/-- At a point of the state's set, every face equation of the initial state holds: the fibre
coordinate `y l` is `±1`, as prescribed by the face pattern `ε`. -/
theorem face_eq_of_mem {X : SemiPf (p + q)} (A : Basic (p + q) X.r) (Fy : Finset (Fin q))
    (ε : {l // l ∈ Fy} → Bool) {z : Fin (p + q) → ℝ}
    (hz : z ∈ (stSemiPf X (initSt X A Fy ε)).set) (l : {l // l ∈ Fy}) :
    z (yDir p l.1) = (if ε l then (1 : ℝ) else -1) := by
  have heqs := ((mem_stSemiPf_iff (initSt X A Fy ε) z).mp hz).2.1
  have hmem : facePoly (p := p) (q := q) (r := X.r) l.1 (if ε l then (1 : ℝ) else -1) ∈
      (initSt X A Fy ε).B.map Prod.fst ++ (initSt X A Fy ε).Ξ := by
    refine List.mem_append_left _ ?_
    rw [initSt_B_map (p := p) (q := q) (X := X) A Fy ε]
    exact List.mem_map.mpr ⟨l, Finset.mem_toList.mpr (Finset.mem_attach Fy l), rfl⟩
  have h0 := heqs _ hmem
  simp only [facePoly] at h0
  rw [eaEval_facePoly] at h0
  linarith

/-- At a point of the state's set, every interior inequality of the initial state holds: the fibre
coordinate `y l` lies strictly inside `(-1,1)` for the directions `l` not carrying a face. -/
theorem int_pos_of_mem {X : SemiPf (p + q)} (A : Basic (p + q) X.r) (Fy : Finset (Fin q))
    (ε : {l // l ∈ Fy} → Bool) {z : Fin (p + q) → ℝ}
    (hz : z ∈ (stSemiPf X (initSt X A Fy ε)).set) {l : Fin q} (hl : l ∉ Fy) :
    1 - (z (yDir p l)) ^ 2 > 0 := by
  have hpos := ((mem_stSemiPf_iff (initSt X A Fy ε) z).mp hz).2.2
  have hmem : intPoly (p := p) (q := q) (r := X.r) l ∈ (initSt X A Fy ε).ν := by
    show intPoly l ∈ A.pos ++ Fyᶜ.attach.toList.map
      (fun l => intPoly (p := p) (q := q) (r := X.r) l.1)
    refine List.mem_append_right _ ?_
    exact List.mem_map.mpr
      ⟨⟨l, Finset.mem_compl.mpr hl⟩, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩
  have h0 := hpos _ hmem
  simp only [intPoly] at h0
  rw [eaEval_intPoly] at h0
  exact h0

/-- The `Bool`-indexed `if` with values `±1` is injective: equal values force equal conditions.
(The point is that `(1 : ℝ) ≠ -1`.) -/
private theorem bool_eq_of_ite_eq {a b : Bool}
    (h : (if a then (1 : ℝ) else -1) = (if b then (1 : ℝ) else -1)) : a = b := by
  cases a <;> cases b <;>
    first
      | rfl
      | (exfalso; exact absurd (show (1 : ℝ) = -1 from h) (by norm_num))
      | (exfalso; exact absurd (show (-1 : ℝ) = 1 from h) (by norm_num))

theorem root_eq_of_mem {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q))
    (A : WilkiesDesign.E.Basic (p + q) X.r)
    (Fy Fy' : Finset (Fin q)) (ε : {l // l ∈ Fy} → Bool) (ε' : {l // l ∈ Fy'} → Bool)
    {z : Fin (p + q) → ℝ}
    (hz : z ∈ (Work.WilE5.stSemiPf X (Work.WilE5.initSt X A Fy ε)).set)
    (hz' : z ∈ (Work.WilE5.stSemiPf X (Work.WilE5.initSt X A Fy' ε')).set) :
    Work.WilE5.initSt X A Fy ε = Work.WilE5.initSt X A Fy' ε' := by
  have hFy : Fy = Fy' := by
    refine Finset.ext fun l => ⟨fun hl => ?_, fun hl => ?_⟩
    · by_contra hl'
      have h1 := face_eq_of_mem (p := p) (q := q) (X := X) A Fy ε hz ⟨l, hl⟩
      have h2 := int_pos_of_mem (p := p) (q := q) (X := X) A Fy' ε' hz' hl'
      have hsq : (z (yDir p l)) ^ 2 = 1 := by
        rw [h1]
        by_cases hb : ε ⟨l, hl⟩ = true <;> simp [hb]
      nlinarith
    · by_contra hl'
      have h1 := face_eq_of_mem (p := p) (q := q) (X := X) A Fy' ε' hz' ⟨l, hl⟩
      have h2 := int_pos_of_mem (p := p) (q := q) (X := X) A Fy ε hz hl'
      have hsq : (z (yDir p l)) ^ 2 = 1 := by
        rw [h1]
        by_cases hb : ε' ⟨l, hl⟩ = true <;> simp [hb]
      nlinarith
  subst hFy
  have hε : ε = ε' := by
    funext l
    exact bool_eq_of_ite_eq
      ((face_eq_of_mem (p := p) (q := q) (X := X) A Fy ε hz l).symm.trans
        (face_eq_of_mem (p := p) (q := q) (X := X) A Fy ε' hz' l))
  subst hε
  rfl

end Work.WilE5.Cells
