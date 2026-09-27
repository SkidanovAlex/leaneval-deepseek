import Submission.Work.Whitney.PathTools.GridGeom

/-!
# Snapping a continuous path to a grid chain
-/

open Set Metric Work.Whitney.PathTools.Grid

namespace Work.Whitney.PathTools

noncomputable section

@[simp] theorem pfst_mk_int (a b : ℤ) : ((a, b) : ℤ × ℤ).1 = a := rfl
@[simp] theorem psnd_mk_int (a b : ℤ) : ((a, b) : ℤ × ℤ).2 = b := rfl


lemma norm_le_coords (v : Pt) : ‖v‖ ≤ |v 0| + |v 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  nlinarith [sq_abs (v 0), sq_abs (v 1), abs_nonneg (v 0), abs_nonneg (v 1)]

lemma floor_half (y : ℝ) : |y - (⌊y + 1/2⌋ : ℝ)| ≤ 1/2 := by
  rw [abs_le]
  constructor
  · have := Int.floor_le (a := y + 1/2); linarith
  · have := Int.lt_floor_add_one (a := y + 1/2); linarith

/-- The grid vertex of the mesh-`h` grid nearest to `z`. -/
def gNear (h : ℝ) (z : Pt) : ℤ × ℤ := (⌊z 0 / h + 1/2⌋, ⌊z 1 / h + 1/2⌋)

/-- Coordinate accessor for `gNear`. -/
def gNF (h : ℝ) (z : Pt) (i : Fin 2) : ℤ := if i = 0 then (gNear h z).1 else (gNear h z).2

lemma gptH_gNear (h : ℝ) (z : Pt) (i : Fin 2) :
    (gptH h (gNear h z)) i = h * ((gNF h z i : ℤ) : ℝ) := by
  fin_cases i <;> simp [gNF, gptH]

lemma gNear_coord0 (h : ℝ) (hh : 0 < h) (z : Pt) :
    |z 0 - h * ((gNear h z).1 : ℝ)| ≤ h / 2 := by
  have hne : h ≠ 0 := ne_of_gt hh
  have key : z 0 - h * ((gNear h z).1 : ℝ) = h * (z 0 / h - ((gNear h z).1 : ℝ)) := by
    rw [mul_sub, mul_comm h (z 0 / h), div_mul_cancel₀ (z 0) hne]
  rw [key, abs_mul, abs_of_pos hh]
  have hfl : ((gNear h z).1 : ℝ) = (⌊z 0 / h + 1 / 2⌋ : ℝ) := by
    rw [show (gNear h z).1 = ⌊z 0 / h + 1 / 2⌋ from rfl]
  rw [hfl]
  calc h * |z 0 / h - (⌊z 0 / h + 1 / 2⌋ : ℝ)| ≤ h * (1/2) :=
        mul_le_mul_of_nonneg_left (floor_half (z 0 / h)) (le_of_lt hh)
    _ = h / 2 := by ring

lemma gNear_coord1 (h : ℝ) (hh : 0 < h) (z : Pt) :
    |z 1 - h * ((gNear h z).2 : ℝ)| ≤ h / 2 := by
  have hne : h ≠ 0 := ne_of_gt hh
  have key : z 1 - h * ((gNear h z).2 : ℝ) = h * (z 1 / h - ((gNear h z).2 : ℝ)) := by
    rw [mul_sub, mul_comm h (z 1 / h), div_mul_cancel₀ (z 1) hne]
  rw [key, abs_mul, abs_of_pos hh]
  have hfl : ((gNear h z).2 : ℝ) = (⌊z 1 / h + 1 / 2⌋ : ℝ) := by
    rw [show (gNear h z).2 = ⌊z 1 / h + 1 / 2⌋ from rfl]
  rw [hfl]
  calc h * |z 1 / h - (⌊z 1 / h + 1 / 2⌋ : ℝ)| ≤ h * (1/2) :=
        mul_le_mul_of_nonneg_left (floor_half (z 1 / h)) (le_of_lt hh)
    _ = h / 2 := by ring

lemma gNF_coord (h : ℝ) (hh : 0 < h) (z : Pt) (i : Fin 2) :
    |z i - h * ((gNF h z i : ℤ) : ℝ)| ≤ h / 2 := by
  fin_cases i
  · exact gNear_coord0 h hh z
  · exact gNear_coord1 h hh z

lemma gNF_dist (h : ℝ) (hh : 0 < h) (z : Pt) : dist (gptH h (gNear h z)) z ≤ 2 * h := by
  rw [dist_eq_norm]
  calc ‖gptH h (gNear h z) - z‖
      ≤ |(gptH h (gNear h z) - z) 0| + |(gptH h (gNear h z) - z) 1| := norm_le_coords _
    _ = |h * ((gNF h z 0 : ℤ) : ℝ) - z 0| + |h * ((gNF h z 1 : ℤ) : ℝ) - z 1| := by
        simp only [PiLp.sub_apply, gptH_gNear]
    _ ≤ h / 2 + h / 2 := by
        have h0 : |h * ((gNF h z 0 : ℤ) : ℝ) - z 0| ≤ h / 2 := by
          rw [abs_sub_comm]; exact gNF_coord h hh z 0
        have h1 : |h * ((gNF h z 1 : ℤ) : ℝ) - z 1| ≤ h / 2 := by
          rw [abs_sub_comm]; exact gNF_coord h hh z 1
        linarith
    _ ≤ 2 * h := by linarith

lemma coord_le_dist (z z' : Pt) (i : Fin 2) : |z i - z' i| ≤ dist z z' := by
  have h : |(z - z') i| ≤ ‖z - z'‖ := by
    have := PiLp.norm_apply_le (z - z') i
    simpa using this
  have h2 : (z - z') i = z i - z' i := by simp
  rw [h2] at h
  rw [dist_eq_norm]
  exact h

lemma gNF_step (h : ℝ) (hh : 0 < h) {z z' : Pt} (hzz : dist z z' ≤ h / 8) (i : Fin 2) :
    |gNF h z i - gNF h z' i| ≤ 1 := by
  have hcoord : |z i - z' i| ≤ h / 8 := (coord_le_dist z z' i).trans hzz
  have c0 : |h * ((gNF h z i : ℤ) : ℝ) - z i| ≤ h / 2 := by
    rw [abs_sub_comm]; exact gNF_coord h hh z i
  have c1 : |z' i - h * ((gNF h z' i : ℤ) : ℝ)| ≤ h / 2 := gNF_coord h hh z' i
  have hcast : ((gNF h z i : ℤ) : ℝ) - ((gNF h z' i : ℤ) : ℝ)
      = ((gNF h z i - gNF h z' i : ℤ) : ℝ) := by push_cast; ring
  have hexp : h * (((gNF h z i : ℤ) : ℝ) - ((gNF h z' i : ℤ) : ℝ))
      = (h * ((gNF h z i : ℤ) : ℝ) - z i) + (z' i - h * ((gNF h z' i : ℤ) : ℝ)) + (z i - z' i) := by
    ring
  have hbound : |h * (((gNF h z i : ℤ) : ℝ) - ((gNF h z' i : ℤ) : ℝ))| ≤ h * (9/8) := by
    rw [hexp]
    calc |_| ≤ |h * ((gNF h z i : ℤ) : ℝ) - z i| + |z' i - h * ((gNF h z' i : ℤ) : ℝ)|
              + |z i - z' i| := abs_add_three _ _ _
      _ ≤ h / 2 + h / 2 + h / 8 := by linarith
      _ = h * (9/8) := by ring
  rw [abs_mul, abs_of_pos hh] at hbound
  rw [hcast, ← Int.cast_abs] at hbound
  have hdiv : (((|gNF h z i - gNF h z' i| : ℤ)) : ℝ) ≤ 9/8 := by nlinarith [hbound, hh]
  have hlt2 : (|gNF h z i - gNF h z' i| : ℤ) < 2 := by
    rw [← Int.cast_lt (R := ℝ)]
    push_cast
    push_cast at hdiv
    linarith
  have hnn := abs_nonneg (gNF h z i - gNF h z' i)
  omega

/-- The mod-two delta function at a grid vertex. -/
def dirac (a : ℤ × ℤ) : ℤ × ℤ → ZMod 2 := fun w => if w = a then 1 else 0

lemma bdry1_edge (e : Edge) :
    bdry1 ((eChain e : Chain1) : Edge → ZMod 2) = dirac (eTail e) + dirac (eHead e) := by
  funext w
  rw [bdry1_eChain, Pi.add_apply]
  rfl

lemma char2_hex1 (a m b : ℤ × ℤ → ZMod 2) : a + m + (m + b) = a + b := by
  rw [show a + m + (m + b) = a + b + (m + m) from by abel, CharTwo.add_self_eq_zero, add_zero]

lemma char2_hex2 (a m b : ℤ × ℤ → ZMod 2) : a + m + (b + m) = a + b := by
  rw [show a + m + (b + m) = a + b + (m + m) from by abel, CharTwo.add_self_eq_zero, add_zero]

lemma char2_hex3 (a m b : ℤ × ℤ → ZMod 2) : m + a + (m + b) = a + b := by
  rw [show m + a + (m + b) = a + b + (m + m) from by abel, CharTwo.add_self_eq_zero, add_zero]

lemma char2_hex4 (a m b : ℤ × ℤ → ZMod 2) : m + a + (b + m) = a + b := by
  rw [show m + a + (b + m) = a + b + (m + m) from by abel, CharTwo.add_self_eq_zero, add_zero]

/-- The staircase chain from `u` to `v`, for grid vertices differing by at most one unit in each
coordinate. -/
def stair (u v : ℤ × ℤ) : Chain1 :=
  if u = v then 0
  else if u.2 = v.2 then
    (if u.1 < v.1 then eChain (true, u.1, u.2) else eChain (true, v.1, u.2))
  else if u.1 = v.1 then
    (if u.2 < v.2 then eChain (false, u.1, u.2) else eChain (false, u.1, v.2))
  else
    (if u.1 < v.1 then eChain (true, u.1, u.2) else eChain (true, v.1, u.2)) +
    (if u.2 < v.2 then eChain (false, v.1, u.2) else eChain (false, v.1, v.2))

lemma dirac_pair_of {a b c d : ℤ × ℤ}
    (h : (a = c ∧ b = d) ∨ (a = d ∧ b = c)) : dirac a + dirac b = dirac c + dirac d := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [add_comm]

lemma bdry1_stair {u v : ℤ × ℤ} (h1 : |u.1 - v.1| ≤ 1) (h2 : |u.2 - v.2| ≤ 1) :
    bdry1 ((stair u v : Chain1) : Edge → ZMod 2) = dirac u + dirac v := by
  have H1 := abs_le.mp h1
  have H2 := abs_le.mp h2
  by_cases huv : u = v
  · subst huv
    rw [stair, if_pos rfl, Finsupp.coe_zero]
    have hz : bdry1 (0 : Edge → ZMod 2) = 0 := by funext w; simp [bdry1]
    rw [hz]
    exact (CharTwo.add_self_eq_zero (dirac u)).symm
  · rw [stair, if_neg huv]
    by_cases hrow : u.2 = v.2
    · rw [if_pos hrow]
      have hlt_or : u.1 < v.1 ∨ v.1 < u.1 := by
        rcases lt_trichotomy u.1 v.1 with h | h | h
        · exact Or.inl h
        · exact absurd (Prod.ext h hrow) huv
        · exact Or.inr h
      rcases hlt_or with hlt | hgt
      · rw [if_pos hlt, bdry1_edge]
        simp only [eTail_true, eHead_true]
        refine dirac_pair_of (Or.inl ⟨Prod.ext rfl rfl, ?_⟩)
        exact Prod.ext (by omega) hrow
      · rw [if_neg (not_lt.mpr (le_of_lt hgt)), bdry1_edge]
        simp only [eTail_true, eHead_true]
        refine dirac_pair_of (Or.inr ⟨?_, ?_⟩)
        · exact Prod.ext rfl hrow
        · exact Prod.ext (by omega) rfl
    · rw [if_neg hrow]
      by_cases hcol : u.1 = v.1
      · rw [if_pos hcol]
        have hlt_or : u.2 < v.2 ∨ v.2 < u.2 := by
          rcases lt_trichotomy u.2 v.2 with h | h | h
          · exact Or.inl h
          · exact absurd (Prod.ext hcol h) huv
          · exact Or.inr h
        rcases hlt_or with hlt | hgt
        · rw [if_pos hlt, bdry1_edge]
          simp only [eTail_false, eHead_false]
          refine dirac_pair_of (Or.inl ⟨Prod.ext rfl rfl, ?_⟩)
          exact Prod.ext hcol (by omega)
        · rw [if_neg (not_lt.mpr (le_of_lt hgt)), bdry1_edge]
          simp only [eTail_false, eHead_false]
          refine dirac_pair_of (Or.inr ⟨?_, ?_⟩)
          · exact Prod.ext hcol rfl
          · exact Prod.ext rfl (by omega)
      · rw [if_neg hcol]
        have hlt1_or : u.1 < v.1 ∨ v.1 < u.1 := by
          rcases lt_trichotomy u.1 v.1 with h | h | h
          · exact Or.inl h
          · exact absurd h hcol
          · exact Or.inr h
        have hlt2_or : u.2 < v.2 ∨ v.2 < u.2 := by
          rcases lt_trichotomy u.2 v.2 with h | h | h
          · exact Or.inl h
          · exact absurd h hrow
          · exact Or.inr h
        rcases hlt1_or with hlt1 | hgt1
        · rw [if_pos hlt1]
          have hv1 : v.1 = u.1 + 1 := by omega
          rcases hlt2_or with hlt2 | hgt2
          · rw [if_pos hlt2]
            have hv2 : v.2 = u.2 + 1 := by omega
            rw [Finsupp.coe_add, bdry1_add, bdry1_edge, bdry1_edge]
            simp only [eTail_true, eHead_true, eTail_false, eHead_false]
            rw [show ((u.1, u.2) : ℤ × ℤ) = u from Prod.mk.eta,
              show ((u.1 + 1, u.2) : ℤ × ℤ) = (v.1, u.2) from by rw [hv1],
              show ((v.1, u.2 + 1) : ℤ × ℤ) = v from Prod.ext rfl (by omega)]
            exact char2_hex1 _ _ _
          · rw [if_neg (not_lt.mpr (le_of_lt hgt2))]
            have hv2 : u.2 = v.2 + 1 := by omega
            rw [Finsupp.coe_add, bdry1_add, bdry1_edge, bdry1_edge]
            simp only [eTail_true, eHead_true, eTail_false, eHead_false]
            rw [show ((u.1, u.2) : ℤ × ℤ) = u from Prod.mk.eta,
              show ((u.1 + 1, u.2) : ℤ × ℤ) = (v.1, u.2) from by rw [hv1],
              show ((v.1, v.2) : ℤ × ℤ) = v from Prod.mk.eta,
              show ((v.1, v.2 + 1) : ℤ × ℤ) = (v.1, u.2) from by rw [hv2]]
            exact char2_hex2 _ _ _
        · rw [if_neg (not_lt.mpr (le_of_lt hgt1))]
          have hv1 : u.1 = v.1 + 1 := by omega
          rcases hlt2_or with hlt2 | hgt2
          · rw [if_pos hlt2]
            have hv2 : v.2 = u.2 + 1 := by omega
            rw [Finsupp.coe_add, bdry1_add, bdry1_edge, bdry1_edge]
            simp only [eTail_true, eHead_true, eTail_false, eHead_false]
            rw [show ((v.1 + 1, u.2) : ℤ × ℤ) = u from Prod.ext (by omega) rfl,
              show ((v.1, u.2 + 1) : ℤ × ℤ) = v from Prod.ext rfl (by omega)]
            exact char2_hex3 _ _ _
          · rw [if_neg (not_lt.mpr (le_of_lt hgt2))]
            have hv2 : u.2 = v.2 + 1 := by omega
            rw [Finsupp.coe_add, bdry1_add, bdry1_edge, bdry1_edge]
            simp only [eTail_true, eHead_true, eTail_false, eHead_false]
            rw [show ((v.1 + 1, u.2) : ℤ × ℤ) = u from Prod.ext (by omega) rfl,
              show ((v.1, v.2) : ℤ × ℤ) = v from Prod.mk.eta,
              show ((v.1, v.2 + 1) : ℤ × ℤ) = (v.1, u.2) from by rw [hv2]]
            exact char2_hex4 _ _ _
lemma bdry1_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Edge → ZMod 2) :
    bdry1 (∑ i ∈ s, f i) = ∑ i ∈ s, bdry1 (f i) := by
  classical
  induction s using Finset.induction with
  | empty => funext w; simp [bdry1]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bdry1_add, ih]

lemma eChain_support_eq {e e₀ : Edge} (h : ((eChain e₀ : Chain1) : Edge → ZMod 2) e ≠ 0) :
    e = e₀ := by
  rw [eChain_apply] at h
  by_cases h2 : e = e₀
  · exact h2
  · rw [if_neg h2] at h
    exact absurd rfl h

lemma eChain_add_support {e e₁ e₂ : Edge}
    (h : (((eChain e₁ + eChain e₂) : Chain1) : Edge → ZMod 2) e ≠ 0) : e = e₁ ∨ e = e₂ := by
  rw [Finsupp.coe_add, Pi.add_apply, eChain_apply, eChain_apply] at h
  by_cases h1 : e = e₁
  · exact Or.inl h1
  · by_cases h2 : e = e₂
    · exact Or.inr h2
    · rw [if_neg h1, if_neg h2, add_zero] at h
      exact absurd rfl h

lemma gptH_dist_le (h : ℝ) (hh : 0 < h) {a b : ℤ × ℤ}
    (h1 : |a.1 - b.1| ≤ 1) (h2 : |a.2 - b.2| ≤ 1) :
    dist (gptH h a) (gptH h b) ≤ 2 * h := by
  rw [dist_eq_norm]
  calc ‖gptH h a - gptH h b‖
      ≤ |(gptH h a - gptH h b) 0| + |(gptH h a - gptH h b) 1| := norm_le_coords _
    _ = h * |((a.1 : ℤ) : ℝ) - ((b.1 : ℤ) : ℝ)| + h * |((a.2 : ℤ) : ℝ) - ((b.2 : ℤ) : ℝ)| := by
        simp only [PiLp.sub_apply, gptH_apply_zero, gptH_apply_one]
        rw [show h * ((a.1 : ℤ) : ℝ) - h * ((b.1 : ℤ) : ℝ) = h * (((a.1 : ℤ) : ℝ) - ((b.1 : ℤ) : ℝ)) from by ring,
            show h * ((a.2 : ℤ) : ℝ) - h * ((b.2 : ℤ) : ℝ) = h * (((a.2 : ℤ) : ℝ) - ((b.2 : ℤ) : ℝ)) from by ring]
        simp only [abs_mul, abs_of_pos hh]
    _ ≤ h * 1 + h * 1 := by
        have e1 : |((a.1 : ℤ) : ℝ) - ((b.1 : ℤ) : ℝ)| ≤ 1 := by
          have := h1; rw [abs_le] at this ⊢
          exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
        have e2 : |((a.2 : ℤ) : ℝ) - ((b.2 : ℤ) : ℝ)| ≤ 1 := by
          have := h2; rw [abs_le] at this ⊢
          exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
        nlinarith
    _ = 2 * h := by ring

lemma cellEdges_endpoints (h : ℝ) (hh : 0 ≤ h) {c : Cell} {e : Edge} (hce : e ∈ cellEdges c) :
    gptH h (eTail e) ∈ gsq h c ∧ gptH h (eHead e) ∈ gsq h c := by
  simp only [cellEdges, Finset.mem_insert, Finset.mem_singleton] at hce
  rcases hce with rfl | rfl | rfl | rfl <;>
    · refine ⟨?_, ?_⟩ <;>
      · simp only [eTail_false, eTail_true, eHead_false, eHead_true, gsq, Set.mem_setOf_eq,
          gptH_apply_zero, gptH_apply_one]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> nlinarith [hh]

lemma gsq_dist_le (h : ℝ) (hh : 0 ≤ h) {c : Cell} {x y : Pt}
    (hx : x ∈ gsq h c) (hy : y ∈ gsq h c) : dist x y ≤ 2 * h := by
  rw [dist_eq_norm]
  have hb := norm_le_coords (x - y)
  have e0 : |(x - y) 0| ≤ h := by
    rw [show (x - y) 0 = x 0 - y 0 from by simp, abs_le]
    exact ⟨by linarith [hx.1, hy.2.1], by linarith [hx.2.1, hy.1]⟩
  have e1 : |(x - y) 1| ≤ h := by
    rw [show (x - y) 1 = x 1 - y 1 from by simp, abs_le]
    exact ⟨by linarith [hx.2.2.1, hy.2.2.2], by linarith [hx.2.2.2, hy.2.2.1]⟩
  linarith

lemma stair_edges_close {u v : ℤ × ℤ} (h1 : |u.1 - v.1| ≤ 1) (h2 : |u.2 - v.2| ≤ 1) :
    ∀ e ∈ (stair u v).support,
      |(eTail e).1 - u.1| ≤ 1 ∧ |(eTail e).2 - u.2| ≤ 1 ∧
      |(eHead e).1 - u.1| ≤ 1 ∧ |(eHead e).2 - u.2| ≤ 1 := by
  have H1 := abs_le.mp h1
  have H2 := abs_le.mp h2
  intro e he
  have hne : ((stair u v : Chain1) : Edge → ZMod 2) e ≠ 0 := Finsupp.mem_support_iff.mp he
  rw [stair] at hne
  by_cases huv : u = v
  · rw [if_pos huv] at hne; exact absurd rfl hne
  · rw [if_neg huv] at hne
    by_cases hrow : u.2 = v.2
    · rw [if_pos hrow] at hne
      by_cases hlt : u.1 < v.1
      · rw [if_pos hlt] at hne
        have heq := eChain_support_eq hne
        subst heq
        simp only [eTail_true, eHead_true]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)
      · rw [if_neg hlt] at hne
        have heq := eChain_support_eq hne
        subst heq
        simp only [eTail_true, eHead_true]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)
    · rw [if_neg hrow] at hne
      by_cases hcol : u.1 = v.1
      · rw [if_pos hcol] at hne
        by_cases hlt : u.2 < v.2
        · rw [if_pos hlt] at hne
          have heq := eChain_support_eq hne
          subst heq
          simp only [eTail_false, eHead_false]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)
        · rw [if_neg hlt] at hne
          have heq := eChain_support_eq hne
          subst heq
          simp only [eTail_false, eHead_false]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)
      · rw [if_neg hcol, Finsupp.coe_add, Pi.add_apply] at hne
        by_cases hlt1 : u.1 < v.1
        · rw [if_pos hlt1] at hne
          by_cases hlt2 : u.2 < v.2
          · rw [if_pos hlt2] at hne
            rcases eChain_add_support hne with heq | heq
            · subst heq
              simp only [eTail_true, eHead_true]
              refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)
            · subst heq
              simp only [eTail_false, eHead_false]
              refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)
          · rw [if_neg hlt2] at hne
            rcases eChain_add_support hne with heq | heq
            · subst heq
              simp only [eTail_true, eHead_true]
              refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)
            · subst heq
              simp only [eTail_false, eHead_false]
              refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)
        · rw [if_neg hlt1] at hne
          by_cases hlt2 : u.2 < v.2
          · rw [if_pos hlt2] at hne
            rcases eChain_add_support hne with heq | heq
            · subst heq
              simp only [eTail_true, eHead_true]
              refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)
            · subst heq
              simp only [eTail_false, eHead_false]
              refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)
          · rw [if_neg hlt2] at hne
            rcases eChain_add_support hne with heq | heq
            · subst heq
              simp only [eTail_true, eHead_true]
              refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)
            · subst heq
              simp only [eTail_false, eHead_false]
              refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [abs_le]; omega)

lemma stair_seg (h : ℝ) (hh : 0 < h) {u v : ℤ × ℤ}
    (h1 : |u.1 - v.1| ≤ 1) (h2 : |u.2 - v.2| ≤ 1) :
    ∀ e ∈ (stair u v).support, gseg h e ⊆ closedBall (gptH h u) (2 * h) := by
  intro e he
  obtain ⟨hx1, hx2, hy1, hy2⟩ := stair_edges_close h1 h2 e he
  have hx : gptH h (eTail e) ∈ closedBall (gptH h u) (2 * h) := by
    rw [Metric.mem_closedBall]
    exact gptH_dist_le h hh hx1 hx2
  have hy : gptH h (eHead e) ∈ closedBall (gptH h u) (2 * h) := by
    rw [Metric.mem_closedBall]
    exact gptH_dist_le h hh hy1 hy2
  exact (convex_closedBall (gptH h u) (2 * h)).segment_subset hx hy

lemma gsq_gseg_dist_le {c : Cell} {e : Edge} (hce : e ∈ cellEdges c)
    (h : ℝ) (hh : 0 ≤ h) {k : Pt} (hk : k ∈ gsq h c) {z : Pt} (hz : z ∈ gseg h e) :
    dist z k ≤ 2 * h := by
  obtain ⟨hx, hy⟩ := cellEdges_endpoints h hh hce
  have hxk : gptH h (eTail e) ∈ closedBall k (2 * h) := by
    rw [Metric.mem_closedBall]; exact gsq_dist_le (c := c) (x := gptH h (eTail e)) (y := k) h hh hx hk
  have hyk : gptH h (eHead e) ∈ closedBall k (2 * h) := by
    rw [Metric.mem_closedBall]; exact gsq_dist_le (c := c) (x := gptH h (eHead e)) (y := k) h hh hy hk
  exact (convex_closedBall k (2 * h)).segment_subset hxk hyk hz

theorem exists_chain_of_path {h : ℝ} (hh : 0 < h) {α : ℝ → Pt}
    (hα : ContinuousOn α (Set.Icc (0:ℝ) 1)) {K : Set Pt} (hK : IsCompact K)
    (hroom : ∀ t ∈ Set.Icc (0:ℝ) 1, 100 * h ≤ Metric.infDist (α t) K) :
    ∃ (l : Chain1),
      (∀ v : ℤ × ℤ, bdry1 ((l : Chain1) : Edge → ZMod 2) v
        = (if v = gNear h (α 0) then 1 else 0) + (if v = gNear h (α 1) then 1 else 0)) ∧
      ∀ e ∈ l.support, e ∉ edgeSet (cellSet h K) := by
  have huc : UniformContinuousOn α (Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hα
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc (h / 8) (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity : (0 : ℝ) < 1 / δ) hm
  have hmpos : 0 < m := by exact_mod_cast hm0
  have hmδ : 1 / (m : ℝ) < δ := by
    rw [div_lt_iff₀ hm0]
    have h1 := (div_lt_iff₀ hδpos).mp hm
    linarith
  set t : ℕ → ℝ := fun i => (i : ℝ) / m with ht
  have htmem : ∀ i, i ≤ m → t i ∈ Set.Icc (0:ℝ) 1 := by
    intro i hi
    constructor
    · rw [ht]; simp only; positivity
    · rw [ht, div_le_one hm0]
      exact_mod_cast hi
  set u : ℕ → ℤ × ℤ := fun i => gNear h (α (t i)) with hu
  have hstep : ∀ i, i < m → dist (α (t i)) (α (t (i + 1))) ≤ h / 8 := by
    intro i hi
    refine le_of_lt (hδ (t i) (htmem i (le_of_lt hi)) (t (i + 1)) (htmem (i + 1) (by omega)) ?_)
    have hsub : t i - t (i + 1) = -(1 / (m : ℝ)) := by
      rw [ht]; simp only; field_simp; push_cast; ring
    rw [Real.dist_eq, hsub, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (m : ℝ))]
    exact hmδ
  have hcoord : ∀ i, i < m →
      |(u i).1 - (u (i + 1)).1| ≤ 1 ∧ |(u i).2 - (u (i + 1)).2| ≤ 1 := by
    intro i hi
    have h0 := gNF_step h hh (hstep i hi) 0
    have h1 := gNF_step h hh (hstep i hi) 1
    exact ⟨h0, h1⟩
  have h0 : u 0 = gNear h (α 0) := by
    rw [hu]; congr 1; rw [ht]; simp
  have hm : u m = gNear h (α 1) := by
    rw [hu]; congr 1; rw [ht]; field_simp
  refine ⟨∑ i ∈ Finset.range m, stair (u i) (u (i + 1)), ?_, ?_⟩
  · have h1 : bdry1 (((∑ i ∈ Finset.range m, stair (u i) (u (i + 1))) : Chain1) : Edge → ZMod 2)
        = ∑ i ∈ Finset.range m,
            bdry1 ((stair (u i) (u (i + 1)) : Chain1) : Edge → ZMod 2) := by
      rw [Finsupp.coe_finset_sum]
      exact bdry1_finset_sum _ _
    have h2 : ∑ i ∈ Finset.range m,
          bdry1 ((stair (u i) (u (i + 1)) : Chain1) : Edge → ZMod 2)
        = ∑ i ∈ Finset.range m, (dirac (u i) + dirac (u (i + 1))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact bdry1_stair (hcoord i (Finset.mem_range.mp hi)).1 (hcoord i (Finset.mem_range.mp hi)).2
    have h3 : ∑ i ∈ Finset.range m, (dirac (u i) + dirac (u (i + 1)))
        = dirac (u 0) + dirac (u m) := by
      have hsub : ∑ i ∈ Finset.range m, (dirac (u i) + dirac (u (i + 1)))
          = ∑ i ∈ Finset.range m, (dirac (u i) - dirac (u (i + 1))) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [sub_eq_add_neg, CharTwo.neg_eq]
      rw [hsub, Finset.sum_range_sub', sub_eq_add_neg, CharTwo.neg_eq]
    have hbd : bdry1 (((∑ i ∈ Finset.range m, stair (u i) (u (i + 1))) : Chain1) : Edge → ZMod 2)
        = dirac (u 0) + dirac (u m) := by rw [h1, h2, h3]
    intro v
    rw [hbd, h0, hm]
    simp only [Pi.add_apply, dirac]
  · intro e he heS
    have hsub := Finsupp.support_finset_sum (s := Finset.range m)
      (f := fun i => stair (u i) (u (i + 1)))
    obtain ⟨i, hi, hie⟩ := Finset.mem_biUnion.mp (hsub he)
    have hki : i < m := Finset.mem_range.mp hi
    obtain ⟨c, hc, hce⟩ := heS
    obtain ⟨k, hkc, hkK⟩ := hc
    have hz : gptH h (eTail e) ∈ gseg h e := gseg_self h e
    have hzk : dist (gptH h (eTail e)) k ≤ 2 * h :=
      gsq_gseg_dist_le hce h (le_of_lt hh) hkc hz
    have hzball : dist (gptH h (eTail e)) (gptH h (u i)) ≤ 2 * h := by
      have := stair_seg h hh (hcoord i hki).1 (hcoord i hki).2 e hie hz
      rwa [Metric.mem_closedBall] at this
    have hzα : dist (gptH h (eTail e)) (α (t i)) ≤ 4 * h := by
      calc dist (gptH h (eTail e)) (α (t i))
          ≤ dist (gptH h (eTail e)) (gptH h (u i)) + dist (gptH h (u i)) (α (t i)) :=
            dist_triangle _ _ _
        _ ≤ 2 * h + 2 * h := add_le_add hzball (gNF_dist h hh (α (t i)))
        _ = 4 * h := by ring
    have hkα : dist (α (t i)) k ≤ 6 * h := by
      calc dist (α (t i)) k
          ≤ dist (α (t i)) (gptH h (eTail e)) + dist (gptH h (eTail e)) k := dist_triangle _ _ _
        _ ≤ 4 * h + 2 * h := add_le_add (by rw [dist_comm]; exact hzα) hzk
        _ = 6 * h := by ring
    have h100 := hroom (t i) (htmem i (le_of_lt hki))
    have := le_trans h100 (le_trans (Metric.infDist_le_dist_of_mem hkK) hkα)
    linarith


end

end Work.Whitney.PathTools
