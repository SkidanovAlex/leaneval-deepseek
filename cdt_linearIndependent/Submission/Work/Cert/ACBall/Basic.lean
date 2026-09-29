import Mathlib
import Submission.Work.Cert.Spec

/-! # Ball semantics for the Theorem-A arc certificate (`Work.Cert.Bl`)

`Bl = ⟨x, y, r⟩` denotes the closed disc of centre `(x + y i)/S` and radius `r/S`.

This file fixes the *semantics* `BallMem`, the elementary soundness lemmas for the structurally
trivial ball operations (`bK`, `badd`, `bsub`), and the integer rounding primitives (`md`, `mu`,
`dvu`, `fdiv`, `chalf`) used by the certificate checkers in `Submission/Work/Cert/Defs.lean`.

The non-trivial operations (`bmul`, `binv`, `bsqrt`) are proved in the sibling modules
`ACBall.bmul_sound`, `ACBall.binv_sound`, `ACBall.bsqrt_sound`. -/

namespace Work.Cert.ACBall
open Work.Cert Complex

/-! ## The scale -/

lemma S_pos : (0 : ℤ) < S := by norm_num [S]
lemma S_posR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast S_pos
lemma S_ne : (S : ℤ) ≠ 0 := ne_of_gt S_pos

/-! ## Semantics -/

/-- `w` lies in the ball `a = ⟨x, y, r⟩`, i.e. `‖w − (x + y i)/S‖ ≤ r/S`. -/
def BallMem (a : Bl) (w : ℂ) : Prop := ‖w - cx a.x a.y‖ ≤ (a.r : ℝ) / (S : ℝ)

theorem ballMem_iff (a : Bl) (w : ℂ) :
    BallMem a w ↔ ‖w - cx a.x a.y‖ ≤ (a.r : ℝ) / (S : ℝ) := Iff.rfl

/-- A nonempty ball has nonnegative radius. -/
lemma nonneg_radius {a : Bl} {w : ℂ} (h : BallMem a w) : 0 ≤ a.r := by
  by_contra hneg
  rw [not_le] at hneg
  have h1 : ((a.r : ℤ) : ℝ) / (S : ℝ) < 0 :=
    div_neg_of_neg_of_pos (by exact_mod_cast hneg) S_posR
  have h2 : (0 : ℝ) ≤ ‖w - cx a.x a.y‖ := norm_nonneg _
  rw [BallMem] at h
  linarith

/-! ## `cx` facts -/

lemma cx_re (x y : ℤ) : (cx x y).re = (x : ℝ) / (S : ℝ) := by simp [cx]
lemma cx_im (x y : ℤ) : (cx x y).im = (y : ℝ) / (S : ℝ) := by simp [cx]

lemma cx_add (x y x' y' : ℤ) : cx (x + x') (y + y') = cx x y + cx x' y' := by
  simp only [cx]; push_cast; ring

lemma cx_sub (x y x' y' : ℤ) : cx x y - cx x' y' = cx (x - x') (y - y') := by
  simp only [cx]; push_cast; ring

lemma cx_zero_y (x : ℤ) : cx x 0 = Complex.ofReal ((x : ℝ) / (S : ℝ)) := by
  simp only [cx]
  rw [Complex.ofReal_div]
  simp

lemma cx_zero : cx 0 0 = 0 := by
  rw [cx_zero_y]; simp

lemma norm_cx_sq (x y : ℤ) :
    ‖cx x y‖ ^ 2 = ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) / (S : ℝ) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [cx_re, cx_im]
  ring

lemma norm_cx_le_abs (x y : ℤ) : ‖cx x y‖ ≤ (|(x : ℝ)| + |(y : ℝ)|) / (S : ℝ) := by
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) (le_of_eq ?_)
  rw [cx_re, cx_im, abs_div, abs_div, abs_of_pos S_posR]
  ring

lemma iabs_abs (a : ℤ) : ((iabs a : ℤ) : ℝ) = |(a : ℝ)| := by
  rw [iabs]
  by_cases h : a < 0
  · rw [if_pos h]; push_cast; exact_mod_cast (abs_of_neg h).symm
  · rw [if_neg h]; push_cast; exact_mod_cast (abs_of_nonneg (not_lt.mp h)).symm

lemma iabs_nonneg (a : ℤ) : 0 ≤ iabs a := by
  rw [iabs]; split <;> omega

/-- `bmod a` dominates `S·‖centre a‖`. -/
lemma le_bmod (a : Bl) : (S : ℝ) * ‖cx a.x a.y‖ ≤ (bmod a : ℝ) := by
  have h := norm_cx_le_abs a.x a.y
  have hb : (bmod a : ℝ) = |(a.x : ℝ)| + |(a.y : ℝ)| := by
    rw [bmod]; push_cast; rw [iabs_abs, iabs_abs]
  rw [hb, mul_comm]
  exact (le_div_iff₀ S_posR).mp h

lemma bmod_nonneg (a : Bl) : 0 ≤ bmod a := by
  rw [bmod]
  have h1 := iabs_nonneg a.x
  have h2 := iabs_nonneg a.y
  omega

lemma norm_cx_le_of_sq_le (x y m : ℤ) (hm : 0 ≤ m) (h : x * x + y * y ≤ m * m) :
    ‖cx x y‖ ≤ (m : ℝ) / (S : ℝ) := by
  have hcast : ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) ≤ (m : ℝ) ^ 2 := by
    have h' : ((x * x + y * y : ℤ) : ℝ) ≤ ((m * m : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    simpa [sq] using h'
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : ‖cx x y‖ ^ 2 ≤ ((m : ℝ) / (S : ℝ)) ^ 2 := by
    rw [norm_cx_sq, div_pow]
    exact div_le_div_of_nonneg_right hcast (sq_nonneg _)
  calc ‖cx x y‖ = Real.sqrt (‖cx x y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (((m : ℝ) / (S : ℝ)) ^ 2) := Real.sqrt_le_sqrt h2
    _ = (m : ℝ) / (S : ℝ) := Real.sqrt_sq (div_nonneg hmR S_posR.le)

/-! ## The trivial ball operations -/

lemma ballMem_bK (k : ℤ) : BallMem (bK k) (Complex.ofReal ((k : ℝ) / (S : ℝ))) := by
  rw [BallMem]
  show ‖Complex.ofReal ((k : ℝ) / (S : ℝ)) - cx k 0‖ ≤ ((0 : ℤ) : ℝ) / (S : ℝ)
  rw [cx_zero_y]
  simp only [sub_self, norm_zero, Int.cast_zero, zero_div]
  exact le_refl 0

lemma ballMem_badd {a b : Bl} {u v : ℂ} (ha : BallMem a u) (hb : BallMem b v) :
    BallMem (badd a b) (u + v) := by
  have ha' : ‖u - cx a.x a.y‖ ≤ (a.r : ℝ) / (S : ℝ) := ha
  have hb' : ‖v - cx b.x b.y‖ ≤ (b.r : ℝ) / (S : ℝ) := hb
  show ‖(u + v) - cx (a.x + b.x) (a.y + b.y)‖ ≤ ((a.r + b.r : ℤ) : ℝ) / (S : ℝ)
  rw [cx_add]
  calc ‖(u + v) - (cx a.x a.y + cx b.x b.y)‖
      = ‖(u - cx a.x a.y) + (v - cx b.x b.y)‖ := by
        congr 1; ring
    _ ≤ ‖u - cx a.x a.y‖ + ‖v - cx b.x b.y‖ := norm_add_le _ _
    _ ≤ (a.r : ℝ) / (S : ℝ) + (b.r : ℝ) / (S : ℝ) := add_le_add ha' hb'
    _ = ((a.r + b.r : ℤ) : ℝ) / (S : ℝ) := by push_cast; ring

lemma ballMem_bsub {a b : Bl} {u v : ℂ} (ha : BallMem a u) (hb : BallMem b v) :
    BallMem (bsub a b) (u - v) := by
  have ha' : ‖u - cx a.x a.y‖ ≤ (a.r : ℝ) / (S : ℝ) := ha
  have hb' : ‖v - cx b.x b.y‖ ≤ (b.r : ℝ) / (S : ℝ) := hb
  show ‖(u - v) - cx (a.x - b.x) (a.y - b.y)‖ ≤ ((a.r + b.r : ℤ) : ℝ) / (S : ℝ)
  rw [← cx_sub]
  calc ‖(u - v) - (cx a.x a.y - cx b.x b.y)‖
      = ‖(u - cx a.x a.y) - (v - cx b.x b.y)‖ := by
        congr 1; ring
    _ ≤ ‖u - cx a.x a.y‖ + ‖v - cx b.x b.y‖ := by
        rw [sub_eq_add_neg]
        exact le_trans (norm_add_le _ _) (le_of_eq (by rw [norm_neg]))
    _ ≤ (a.r : ℝ) / (S : ℝ) + (b.r : ℝ) / (S : ℝ) := add_le_add ha' hb'
    _ = ((a.r + b.r : ℤ) : ℝ) / (S : ℝ) := by push_cast; ring

/-! ## Integer rounding primitives -/

/-- `md a b = ⌊ab/S⌋ ≤ ab/S`. -/
lemma md_le (a b : ℤ) : ((md a b : ℤ) : ℝ) ≤ (a : ℝ) * (b : ℝ) / (S : ℝ) := by
  have h : Int.ediv (a * b) S * S ≤ a * b := Int.ediv_mul_le _ (ne_of_gt S_pos)
  have h2 : ((Int.ediv (a * b) S : ℤ) : ℝ) * (S : ℝ) ≤ (a : ℝ) * (b : ℝ) := by
    exact_mod_cast h
  rw [md, fdiv, le_div_iff₀ S_posR]
  linarith

/-- `md a b = ⌊ab/S⌋ > ab/S - 1`. -/
lemma md_gt (a b : ℤ) : (a : ℝ) * (b : ℝ) / (S : ℝ) - 1 < ((md a b : ℤ) : ℝ) := by
  have h : a * b < (Int.ediv (a * b) S + 1) * S := Int.lt_ediv_add_one_mul_self _ S_pos
  have h2 : (a : ℝ) * (b : ℝ) < (((Int.ediv (a * b) S : ℤ) : ℝ) + 1) * (S : ℝ) := by
    exact_mod_cast h
  rw [md, fdiv, sub_lt_iff_lt_add, div_lt_iff₀ S_posR]
  linarith

/-- `mu a b = ⌈ab/S⌉ ≥ ab/S`. -/
lemma mu_ge (a b : ℤ) : (a : ℝ) * (b : ℝ) / (S : ℝ) ≤ ((mu a b : ℤ) : ℝ) := by
  have h : Int.ediv (-(a * b)) S * S ≤ -(a * b) := Int.ediv_mul_le _ (ne_of_gt S_pos)
  have h2 : ((Int.ediv (-(a * b)) S : ℤ) : ℝ) * (S : ℝ) ≤ -((a : ℝ) * (b : ℝ)) := by
    exact_mod_cast h
  have h3 : ((mu a b : ℤ) : ℝ) = -((Int.ediv (-(a * b)) S : ℤ) : ℝ) := by
    rw [mu, fdiv]; push_cast; ring
  rw [h3, div_le_iff₀ S_posR]
  linarith

/-- `mu a b = ⌈ab/S⌉ < ab/S + 1`. -/
lemma mu_lt (a b : ℤ) : ((mu a b : ℤ) : ℝ) < (a : ℝ) * (b : ℝ) / (S : ℝ) + 1 := by
  have h : -(a * b) < (Int.ediv (-(a * b)) S + 1) * S := Int.lt_ediv_add_one_mul_self _ S_pos
  have h2 : -((a : ℝ) * (b : ℝ)) < (((Int.ediv (-(a * b)) S : ℤ) : ℝ) + 1) * (S : ℝ) := by
    exact_mod_cast h
  have h3 : ((mu a b : ℤ) : ℝ) = -((Int.ediv (-(a * b)) S : ℤ) : ℝ) := by
    rw [mu, fdiv]; push_cast; ring
  rw [h3, ← sub_lt_iff_lt_add, lt_div_iff₀ S_posR]
  linarith

/-- `dvu a b = ⌈aS/b⌉ ≥ aS/b` for `0 < b`. -/
lemma dvu_ge {a b : ℤ} (hb : 0 < b) : (a : ℝ) * (S : ℝ) / (b : ℝ) ≤ ((dvu a b : ℤ) : ℝ) := by
  have h : Int.ediv (-(a * S)) b * b ≤ -(a * S) := Int.ediv_mul_le _ (ne_of_gt hb)
  have h2 : ((Int.ediv (-(a * S)) b : ℤ) : ℝ) * (b : ℝ) ≤ -((a : ℝ) * (S : ℝ)) := by
    exact_mod_cast h
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h3 : ((dvu a b : ℤ) : ℝ) = -((Int.ediv (-(a * S)) b : ℤ) : ℝ) := by
    rw [dvu, fdiv]; push_cast; ring
  rw [h3, div_le_iff₀ hbR]
  linarith

/-- `dvu a b = ⌈aS/b⌉ < aS/b + 1` for `0 < b`. -/
lemma dvu_lt {a b : ℤ} (hb : 0 < b) : ((dvu a b : ℤ) : ℝ) < (a : ℝ) * (S : ℝ) / (b : ℝ) + 1 := by
  have h : -(a * S) < (Int.ediv (-(a * S)) b + 1) * b := Int.lt_ediv_add_one_mul_self _ hb
  have h2 : -((a : ℝ) * (S : ℝ)) < (((Int.ediv (-(a * S)) b : ℤ) : ℝ) + 1) * (b : ℝ) := by
    exact_mod_cast h
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h3 : ((dvu a b : ℤ) : ℝ) = -((Int.ediv (-(a * S)) b : ℤ) : ℝ) := by
    rw [dvu, fdiv]; push_cast; ring
  rw [h3, ← sub_lt_iff_lt_add, lt_div_iff₀ hbR]
  linarith

/-- `fdiv a b = ⌊a/b⌋ ≤ a/b` for `0 < b`. -/
lemma fdiv_le {a b : ℤ} (hb : 0 < b) : ((fdiv a b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have h : Int.ediv a b * b ≤ a := Int.ediv_mul_le _ (ne_of_gt hb)
  have h2 : ((Int.ediv a b : ℤ) : ℝ) * (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [fdiv, le_div_iff₀ hbR]
  linarith

/-- `fdiv a b = ⌊a/b⌋ > a/b - 1` for `0 < b`. -/
lemma fdiv_gt {a b : ℤ} (hb : 0 < b) : (a : ℝ) / (b : ℝ) - 1 < ((fdiv a b : ℤ) : ℝ) := by
  have h : a < (Int.ediv a b + 1) * b := Int.lt_ediv_add_one_mul_self _ hb
  have h2 : (a : ℝ) < (((Int.ediv a b : ℤ) : ℝ) + 1) * (b : ℝ) := by exact_mod_cast h
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [fdiv, sub_lt_iff_lt_add, div_lt_iff₀ hbR]
  linarith

/-- `chalf x = ⌈x/2⌉ ≥ x/2`. -/
lemma chalf_ge (x : ℤ) : (x : ℝ) / 2 ≤ ((chalf x : ℤ) : ℝ) := by
  have h : Int.ediv (-x) 2 * 2 ≤ -x := Int.ediv_mul_le _ (by norm_num : (2 : ℤ) ≠ 0)
  have h2 : ((Int.ediv (-x) 2 : ℤ) : ℝ) * 2 ≤ -(x : ℝ) := by exact_mod_cast h
  have h3 : ((chalf x : ℤ) : ℝ) = -((Int.ediv (-x) 2 : ℤ) : ℝ) := by
    rw [chalf, fdiv]; push_cast; ring
  rw [h3]; linarith

/-- `chalf x = ⌈x/2⌉ < x/2 + 1`. -/
lemma chalf_lt (x : ℤ) : ((chalf x : ℤ) : ℝ) < (x : ℝ) / 2 + 1 := by
  have h : -x < (Int.ediv (-x) 2 + 1) * 2 :=
    Int.lt_ediv_add_one_mul_self _ (by norm_num : (0 : ℤ) < 2)
  have h2 : -(x : ℝ) < (((Int.ediv (-x) 2 : ℤ) : ℝ) + 1) * 2 := by exact_mod_cast h
  have h3 : ((chalf x : ℤ) : ℝ) = -((Int.ediv (-x) 2 : ℤ) : ℝ) := by
    rw [chalf, fdiv]; push_cast; ring
  rw [h3]; linarith

/-- `x/S ≤ y/S ↔ x ≤ y`. -/
lemma m2r_le_iff {x y : ℤ} : ((x : ℝ) / (S : ℝ)) ≤ ((y : ℝ) / (S : ℝ)) ↔ x ≤ y := by
  rw [div_le_div_iff_of_pos_right S_posR, Int.cast_le]

end Work.Cert.ACBall
