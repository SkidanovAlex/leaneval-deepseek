import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.prop_11_1
import Submission.Work.FIArea4.polya_vinogradov
import Submission.Work.FIArea4.jacobi_congruence_count
import Submission.Work.FIArea4.Evar_le_trivial
import Submission.Work.FIArea4.Assembly
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.pair_sum_le_Evar
import Submission.Work.FIArea4.Vflip.Vvar_le_of_mul_lt_D
import Submission.Work.FIArea4.P13_sharp_evar
import Submission.Work.FIArea4.Vflip.Vvar_flip_mid
import Submission.Work.FIArea4.prop_13_1

namespace Work.FIArea4

open scoped BigOperators

noncomputable section

/-!
# Friedlander–Iwaniec Proposition 14.1 (the Jacobi-twisted variance, consolidated)

This file proves `Work.FIArea4.prop_14_1`, the bound

`V(D) ≤ C·[D + D^{-1/2}RS + D^{1/3}(RS)^{2/3}(log 2RS + 1)^4 + (R+S)^{1/12}(RS)^{11/12+ε}]·Σ τ(r)|α_{rs}|²`

for `V(D) = Work.FIPlan.Vvar R S D α`, i.e. the paper's Proposition 14.1 ("the
Jacobi-twisted sums: conclusion", FI (14.1)/(14.2)).

The proof is the paper's: the result follows from three estimates, applied according to the
size of `D` — Proposition 11.1 for `D ≤ D₁ = (R+S)^{1/12}(RS)^{5/12}` (small moduli, the
large-sieve argument), Proposition 13.1 for `D₁ < D < D₂ = (R+S)^{-1/8}(RS)^{5/8}` (enlarging
moduli) and Proposition 12.1 for `D ≥ D₂` (flipping moduli).  Those three estimates are *input*
to this file (as the `p14Prop111`, `p14Prop121`, `p14Prop131` hypotheses of `p14asm_assembly`, and as the
imported results `prop_11_1`, `prop_12_1`, `prop_13_1` in the final theorem); what is proved
*here* is the assembly: the case distinction and all the numerical bookkeeping (the four
elementary real-variable inequalities `p14asm_ey_xy`, `p14asm_ey_yx`, `p14asm_ey_T` and the threshold estimates
`p14asm_eyA`, `p14asm_eyE`, `p14asm_eyF`, `p14asm_eyG`), together with the passage from the `‖α‖²`-normalisation of
Propositions 11.1/13.1 to the `Σ τ(r)|α_{rs}|²`-normalisation of Proposition 14.1.
-/

/-! ## Elementary real-variable estimates -/

lemma p14asm_Rpos {R : ℕ} (hR : 1 ≤ R) : (0:ℝ) < (R:ℝ) := by exact_mod_cast hR

lemma p14asm_Tpos {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) : (0:ℝ) < (R:ℝ) + (S:ℝ) := by
  have := p14asm_Rpos hR; have := p14asm_Rpos hS; linarith

lemma p14asm_Ppos {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) : (0:ℝ) < (R:ℝ) * (S:ℝ) :=
  mul_pos (p14asm_Rpos hR) (p14asm_Rpos hS)

/-- `R·S^{3/4} ≤ (R+S)^{1/12}(RS)^{11/12}`. -/
lemma p14asm_ey_xy (R S : ℕ) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (R:ℝ) * (S:ℝ) ^ ((3:ℝ)/4) ≤ ((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/12) * ((R:ℝ)*(S:ℝ)) ^ ((11:ℝ)/12) := by
  set X : ℝ := (R:ℝ) with hXdef
  set Y : ℝ := (S:ℝ) with hYdef
  have hX1 : 1 ≤ X := by rw [hXdef]; exact_mod_cast hR
  have hY1 : 1 ≤ Y := by rw [hYdef]; exact_mod_cast hS
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hY2 : (1:ℝ) ≤ Y ^ (2:ℝ) := by
    simpa [Real.rpow_natCast] using Real.one_le_rpow hY1 (by norm_num : (0:ℝ) ≤ 2)
  have hbase : X ^ (12:ℝ) * Y ^ (9:ℝ) ≤ (X + Y) * (X * Y) ^ (11:ℝ) := by
    have hstep : X ≤ (X + Y) * Y ^ (2:ℝ) := by
      have h1 : X * (1:ℝ) ≤ X * Y ^ (2:ℝ) := mul_le_mul_of_nonneg_left hY2 hX0.le
      have h2 : X * Y ^ (2:ℝ) ≤ (X + Y) * Y ^ (2:ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [hY0.le]) (Real.rpow_nonneg hY0.le _)
      simpa using le_trans h1 h2
    have hfac : (0:ℝ) ≤ X ^ (11:ℝ) * Y ^ (9:ℝ) := by positivity
    have hX12 : X ^ (12:ℝ) = X ^ (11:ℝ) * X := by
      rw [show (12:ℝ) = 11 + 1 by norm_num, Real.rpow_add hX0, Real.rpow_one]
    have hY11 : Y ^ (11:ℝ) = Y ^ (9:ℝ) * Y ^ (2:ℝ) := by
      rw [show (11:ℝ) = 9 + 2 by norm_num, Real.rpow_add hY0]
    have e1 : X ^ (12:ℝ) * Y ^ (9:ℝ) = (X ^ (11:ℝ) * Y ^ (9:ℝ)) * X := by rw [hX12]; ring
    have e2 : (X + Y) * (X * Y) ^ (11:ℝ) = (X ^ (11:ℝ) * Y ^ (9:ℝ)) * ((X + Y) * Y ^ (2:ℝ)) := by
      rw [Real.mul_rpow hX0.le hY0.le, hY11]; ring
    calc X ^ (12:ℝ) * Y ^ (9:ℝ) = (X ^ (11:ℝ) * Y ^ (9:ℝ)) * X := e1
      _ ≤ (X ^ (11:ℝ) * Y ^ (9:ℝ)) * ((X + Y) * Y ^ (2:ℝ)) :=
          mul_le_mul_of_nonneg_left hstep hfac
      _ = (X + Y) * (X * Y) ^ (11:ℝ) := e2.symm
  have hL : X * Y ^ ((3:ℝ)/4) = (X ^ (12:ℝ) * Y ^ (9:ℝ)) ^ ((1:ℝ)/12) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hX0.le _) (Real.rpow_nonneg hY0.le _)]
    rw [← Real.rpow_mul hX0.le, ← Real.rpow_mul hY0.le]
    have h1 : (12:ℝ) * ((1:ℝ)/12) = 1 := by norm_num
    have h2 : (9:ℝ) * ((1:ℝ)/12) = 3/4 := by norm_num
    rw [h1, h2, Real.rpow_one]
  have hR' : (X + Y) ^ ((1:ℝ)/12) * (X * Y) ^ ((11:ℝ)/12) = ((X + Y) * (X * Y) ^ (11:ℝ)) ^ ((1:ℝ)/12) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ X*Y) _)]
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ X*Y)]
    have h2 : (11:ℝ) * ((1:ℝ)/12) = 11/12 := by norm_num
    rw [h2]
  rw [hL, hR', Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0:ℝ) < 1/12)]
  exact hbase

/-- `S·R^{3/4} ≤ (R+S)^{1/12}(RS)^{11/12}` (the symmetric form of `p14asm_ey_xy`). -/
lemma p14asm_ey_yx (R S : ℕ) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (S:ℝ) * (R:ℝ) ^ ((3:ℝ)/4) ≤ ((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/12) * ((R:ℝ)*(S:ℝ)) ^ ((11:ℝ)/12) := by
  simpa only [add_comm, mul_comm] using p14asm_ey_xy S R hS hR

/-- `(R+S)^{1/8}(RS)^{7/8} ≤ 2^{1/24}(R+S)^{1/12}(RS)^{11/12}` (from `R+S ≤ 2RS`). -/
lemma p14asm_ey_T (R S : ℕ) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    ((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/8) * ((R:ℝ)*(S:ℝ)) ^ ((7:ℝ)/8) ≤
      2 ^ ((1:ℝ)/24) * (((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/12) * ((R:ℝ)*(S:ℝ)) ^ ((11:ℝ)/12)) := by
  set X : ℝ := (R:ℝ) with hXdef
  set Y : ℝ := (S:ℝ) with hYdef
  have hX1 : 1 ≤ X := by rw [hXdef]; exact_mod_cast hR
  have hY1 : 1 ≤ Y := by rw [hYdef]; exact_mod_cast hS
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hT0 : 0 < X + Y := by linarith
  have hP0 : 0 < X * Y := mul_pos hX0 hY0
  have hTY : X + Y ≤ 2 * (X * Y) := by nlinarith [hX0.le, hY0.le, hY1, hX1]
  have hbase : (X+Y) ^ (3:ℝ) * (X*Y) ^ (21:ℝ) ≤ 2 * (X+Y) ^ (2:ℝ) * (X*Y) ^ (22:ℝ) := by
    have h3 : (X+Y) ^ (3:ℝ) = (X+Y) ^ (2:ℝ) * (X+Y) := by
      rw [show (3:ℝ) = 2 + 1 by norm_num, Real.rpow_add hT0, Real.rpow_one]
    have h22 : (X*Y) ^ (22:ℝ) = (X*Y) ^ (21:ℝ) * (X*Y) := by
      rw [show (22:ℝ) = 21 + 1 by norm_num, Real.rpow_add hP0, Real.rpow_one]
    rw [h3, h22]
    have hfac : (0:ℝ) < (X+Y) ^ (2:ℝ) * (X*Y) ^ (21:ℝ) := by positivity
    nlinarith [hTY, hfac, mul_pos hX0 hY0]
  have hL : (X+Y) ^ ((1:ℝ)/8) * (X*Y) ^ ((7:ℝ)/8) = ((X+Y) ^ (3:ℝ) * (X*Y) ^ (21:ℝ)) ^ ((1:ℝ)/24) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg hP0.le _)]
    rw [← Real.rpow_mul hT0.le, ← Real.rpow_mul hP0.le]
    have h1 : (3:ℝ) * ((1:ℝ)/24) = 1/8 := by norm_num
    have h2 : (21:ℝ) * ((1:ℝ)/24) = 7/8 := by norm_num
    rw [h1, h2]
  have hR' : 2 ^ ((1:ℝ)/24) * ((X+Y) ^ ((1:ℝ)/12) * (X*Y) ^ ((11:ℝ)/12)) =
      (2 * (X+Y) ^ (2:ℝ) * (X*Y) ^ (22:ℝ)) ^ ((1:ℝ)/24) := by
    rw [show (2:ℝ) * (X+Y) ^ (2:ℝ) * (X*Y) ^ (22:ℝ)
          = 2 * ((X+Y) ^ (2:ℝ) * (X*Y) ^ (22:ℝ)) by ring]
    rw [Real.mul_rpow (by norm_num) (by positivity : (0:ℝ) ≤ (X+Y) ^ (2:ℝ) * (X*Y) ^ (22:ℝ))]
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ (X+Y) ^ (2:ℝ)) (Real.rpow_nonneg hP0.le _)]
    rw [← Real.rpow_mul hT0.le, ← Real.rpow_mul hP0.le]
    have h1 : (2:ℝ) * ((1:ℝ)/24) = 1/12 := by norm_num
    have h2 : (22:ℝ) * ((1:ℝ)/24) = 11/12 := by norm_num
    rw [h1, h2]
  rw [hL, hR', Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0:ℝ) < 1/24)]
  exact hbase

/-- `(R+S)^{1/8}(RS)^{7/8+ε} ≤ 2^{1/24}(R+S)^{1/12}(RS)^{11/12+ε}`. -/
lemma p14asm_18_eps (R S : ℕ) (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    ((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/8) * ((R:ℝ)*(S:ℝ)) ^ ((7:ℝ)/8 + ε) ≤
      2 ^ ((1:ℝ)/24) * p14Last R S ε := by
  have hP : (0:ℝ) < (R:ℝ)*(S:ℝ) := p14asm_Ppos hR hS
  rw [p14Last]
  calc ((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/8) * ((R:ℝ)*(S:ℝ)) ^ ((7:ℝ)/8 + ε)
      = (((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/8) * ((R:ℝ)*(S:ℝ)) ^ ((7:ℝ)/8)) * (((R:ℝ)*(S:ℝ)) ^ ε) := by
        rw [Real.rpow_add hP]; ring
    _ ≤ (2 ^ ((1:ℝ)/24) * (((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/12) * ((R:ℝ)*(S:ℝ)) ^ ((11:ℝ)/12)))
          * (((R:ℝ)*(S:ℝ)) ^ ε) :=
        mul_le_mul_of_nonneg_right (p14asm_ey_T R S hR hS) (Real.rpow_nonneg hP.le ε)
    _ = 2 ^ ((1:ℝ)/24) * (((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/12) * ((R:ℝ)*(S:ℝ)) ^ ((11:ℝ)/12 + ε)) := by
        rw [mul_assoc, mul_assoc, Real.rpow_add hP]

/-- `R·S^{3/4}·(RS)^ε ≤ p14Last R S ε`. -/
lemma p14asm_Y34_eps (R S : ℕ) (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (R:ℝ) * (S:ℝ) ^ ((3:ℝ)/4) * (((R:ℝ)*(S:ℝ)) ^ ε) ≤ p14Last R S ε := by
  have hP : (0:ℝ) < (R:ℝ)*(S:ℝ) := p14asm_Ppos hR hS
  rw [p14Last]
  calc (R:ℝ) * (S:ℝ) ^ ((3:ℝ)/4) * (((R:ℝ)*(S:ℝ)) ^ ε)
      ≤ (((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/12) * ((R:ℝ)*(S:ℝ)) ^ ((11:ℝ)/12)) * (((R:ℝ)*(S:ℝ)) ^ ε) :=
        mul_le_mul_of_nonneg_right (p14asm_ey_xy R S hR hS) (Real.rpow_nonneg hP.le ε)
    _ = ((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/12) * ((R:ℝ)*(S:ℝ)) ^ ((11:ℝ)/12 + ε) := by
        rw [mul_assoc, ← Real.rpow_add hP]

/-- `S·R^{3/4}·(RS)^ε ≤ p14Last R S ε`. -/
lemma p14asm_X34_eps (R S : ℕ) (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (S:ℝ) * (R:ℝ) ^ ((3:ℝ)/4) * (((R:ℝ)*(S:ℝ)) ^ ε) ≤ p14Last R S ε := by
  have hP : (0:ℝ) < (R:ℝ)*(S:ℝ) := p14asm_Ppos hR hS
  rw [p14Last]
  calc (S:ℝ) * (R:ℝ) ^ ((3:ℝ)/4) * (((R:ℝ)*(S:ℝ)) ^ ε)
      ≤ (((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/12) * ((R:ℝ)*(S:ℝ)) ^ ((11:ℝ)/12)) * (((R:ℝ)*(S:ℝ)) ^ ε) :=
        mul_le_mul_of_nonneg_right (p14asm_ey_yx R S hR hS) (Real.rpow_nonneg hP.le ε)
    _ = ((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/12) * ((R:ℝ)*(S:ℝ)) ^ ((11:ℝ)/12 + ε) := by
        rw [mul_assoc, ← Real.rpow_add hP]

/-! ## The three threshold estimates

Each converts the "exceptional" term of one of the three input brackets into (a multiple of)
`p14Last`, using the definition of `D₁` resp. `D₂` and the elementary `R+S ≤ 2RS`. -/

/-- If `D ≤ D₁` then `D·√(RS)·(RS)^ε ≤ p14Last`. -/
lemma p14asm_eyA (D R S : ℕ) (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) (hD : 1 ≤ D)
    (hcase : (D:ℝ) ≤ p14D1 R S) :
    (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * (((R:ℝ)*(S:ℝ))^ε) ≤ p14Last R S ε := by
  have hD0 : 0 < (D:ℝ) := by exact_mod_cast hD
  have hP := p14asm_Ppos hR hS
  have hT := p14asm_Tpos hR hS
  simp only [p14Last, p14D1] at hcase ⊢
  set T : ℝ := (R:ℝ)+(S:ℝ) with hTdef
  set P : ℝ := (R:ℝ)*(S:ℝ) with hPdef
  have hT0 : 0 < T := by rw [hTdef]; exact hT
  have hP0 : 0 < P := by rw [hPdef]; exact hP
  rw [Real.sqrt_eq_rpow]
  rw [show (D:ℝ) * P^((1:ℝ)/2) * P^ε = (D:ℝ) * (P^((1:ℝ)/2) * P^ε) by ring]
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  conv_lhs => rw [Real.log_mul (ne_of_gt hD0) (ne_of_gt (by positivity)),
      Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow hP0, Real.log_rpow hP0]
  conv_rhs => rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow hT0, Real.log_rpow hP0]
  have hcase' : Real.log (D:ℝ) ≤ Real.log (T ^ ((1:ℝ)/12) * P ^ ((5:ℝ)/12)) :=
    Real.log_le_log hD0 hcase
  rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow hT0, Real.log_rpow hP0] at hcase'
  linarith [hcase']

/-- If `D ≥ D₂` then `D⁻¹(RS)^{3/2}(RS)^ε ≤ 2^{1/24}·p14Last`. -/
lemma p14asm_eyE (D R S : ℕ) (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) (hD : 1 ≤ D)
    (hcase : p14D2 R S ≤ (D:ℝ)) :
    (D:ℝ)⁻¹ * (((R:ℝ)*(S:ℝ))^((3:ℝ)/2)) * (((R:ℝ)*(S:ℝ))^ε)
      ≤ 2 ^ ((1:ℝ)/24) * p14Last R S ε := by
  have hD0 : 0 < (D:ℝ) := by exact_mod_cast hD
  have hP := p14asm_Ppos hR hS
  have hT := p14asm_Tpos hR hS
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  simp only [p14Last, p14D2] at hcase ⊢
  set T : ℝ := (R:ℝ)+(S:ℝ) with hTdef
  set P : ℝ := (R:ℝ)*(S:ℝ) with hPdef
  have hT0 : 0 < T := by rw [hTdef]; exact hT
  have hP0 : 0 < P := by rw [hPdef]; exact hP
  have hTP : T ≤ 2 * P := by rw [hTdef, hPdef]; nlinarith [hR1, hS1]
  have hlogTP : Real.log T ≤ Real.log 2 + Real.log P := by
    calc Real.log T ≤ Real.log (2 * P) := Real.log_le_log hT0 hTP
      _ = Real.log 2 + Real.log P := Real.log_mul (by norm_num) (ne_of_gt hP0)
  rw [show (D:ℝ)⁻¹ * P^((3:ℝ)/2) * P^ε = (D:ℝ)⁻¹ * (P^((3:ℝ)/2) * P^ε) by ring]
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  conv_lhs => rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_inv, Real.log_rpow hP0, Real.log_rpow hP0]
  conv_rhs => rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow (by norm_num : (0:ℝ) < 2),
      Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow hT0, Real.log_rpow hP0]
  have hcase' : Real.log (T ^ (-((1:ℝ)/8)) * P ^ ((5:ℝ)/8)) ≤ Real.log (D:ℝ) :=
    Real.log_le_log (by positivity) hcase
  rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow hT0, Real.log_rpow hP0] at hcase'
  linarith [hcase', hlogTP]

/-- If `D ≤ D₂` then `D(R+S)^{1/4}(RS)^{1/4}(RS)^ε ≤ 2^{1/24}·p14Last`. -/
lemma p14asm_eyF (D R S : ℕ) (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) (hD : 1 ≤ D)
    (hcase : (D:ℝ) ≤ p14D2 R S) :
    (D:ℝ) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) * (((R:ℝ)*(S:ℝ))^((1:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε)
      ≤ 2 ^ ((1:ℝ)/24) * p14Last R S ε := by
  have hD0 : 0 < (D:ℝ) := by exact_mod_cast hD
  have hP := p14asm_Ppos hR hS
  have hT := p14asm_Tpos hR hS
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  simp only [p14Last, p14D2] at hcase ⊢
  set T : ℝ := (R:ℝ)+(S:ℝ) with hTdef
  set P : ℝ := (R:ℝ)*(S:ℝ) with hPdef
  have hT0 : 0 < T := by rw [hTdef]; exact hT
  have hP0 : 0 < P := by rw [hPdef]; exact hP
  have hTP : T ≤ 2 * P := by rw [hTdef, hPdef]; nlinarith [hR1, hS1]
  have hlogTP : Real.log T ≤ Real.log 2 + Real.log P := by
    calc Real.log T ≤ Real.log (2 * P) := Real.log_le_log hT0 hTP
      _ = Real.log 2 + Real.log P := Real.log_mul (by norm_num) (ne_of_gt hP0)
  rw [show (D:ℝ) * T^((1:ℝ)/4) * P^((1:ℝ)/4) * P^ε
      = (D:ℝ) * (T^((1:ℝ)/4) * (P^((1:ℝ)/4) * P^ε)) by ring]
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  conv_lhs => rw [Real.log_mul (ne_of_gt hD0) (ne_of_gt (by positivity)),
      Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow hT0, Real.log_rpow hP0, Real.log_rpow hP0]
  conv_rhs => rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow (by norm_num : (0:ℝ) < 2),
      Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow hT0, Real.log_rpow hP0]
  have hcase' : Real.log (D:ℝ) ≤ Real.log (T ^ (-((1:ℝ)/8)) * P ^ ((5:ℝ)/8)) :=
    Real.log_le_log hD0 hcase
  rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow hT0, Real.log_rpow hP0] at hcase'
  linarith [hcase', hlogTP]

/-- If `D ≥ D₁` then `D^{-1/2}(R+S)^{1/8}(RS)^{9/8}(RS)^ε ≤ p14Last`. -/
lemma p14asm_eyG (D R S : ℕ) (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) (hD : 1 ≤ D)
    (hcase : p14D1 R S ≤ (D:ℝ)) :
    (D:ℝ)^(-(1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8) * (((R:ℝ)*(S:ℝ))^((9:ℝ)/8)) * (((R:ℝ)*(S:ℝ))^ε)
      ≤ p14Last R S ε := by
  have hD0 : 0 < (D:ℝ) := by exact_mod_cast hD
  have hP := p14asm_Ppos hR hS
  have hT := p14asm_Tpos hR hS
  simp only [p14Last, p14D1] at hcase ⊢
  set T : ℝ := (R:ℝ)+(S:ℝ) with hTdef
  set P : ℝ := (R:ℝ)*(S:ℝ) with hPdef
  have hT0 : 0 < T := by rw [hTdef]; exact hT
  have hP0 : 0 < P := by rw [hPdef]; exact hP
  rw [show (D:ℝ)^(-(1:ℝ)/2) * T^((1:ℝ)/8) * P^((9:ℝ)/8) * P^ε
      = (D:ℝ)^(-(1:ℝ)/2) * (T^((1:ℝ)/8) * (P^((9:ℝ)/8) * P^ε)) by ring]
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  conv_lhs => rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow hD0, Real.log_rpow hT0, Real.log_rpow hP0, Real.log_rpow hP0]
  conv_rhs => rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow hT0, Real.log_rpow hP0]
  have hcase' : Real.log (T ^ ((1:ℝ)/12) * P ^ ((5:ℝ)/12)) ≤ Real.log (D:ℝ) :=
    Real.log_le_log (by positivity) hcase
  rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
      Real.log_rpow hT0, Real.log_rpow hP0] at hcase'
  linarith [hcase']

/-! ## Comparisons with the bracket of Proposition 14.1 -/

lemma p14asm_e_Bracket_last (D R S : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    p14Last R S ε ≤ p14Bracket D R S ε := by
  rw [p14Bracket]
  have h1 : 0 ≤ (D:ℝ) := by positivity
  have h2 : 0 ≤ (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ)*(S:ℝ) := by positivity
  have h3 : 0 ≤ (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3)
      * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^(4:ℕ) := by positivity
  linarith

lemma p14asm_e_Bracket_D (D R S : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (D:ℝ) ≤ p14Bracket D R S ε := by
  rw [p14Bracket]
  have h2 : 0 ≤ (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ)*(S:ℝ) := by positivity
  have h3 : 0 ≤ (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3)
      * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^(4:ℕ) := by positivity
  have h4 : 0 ≤ p14Last R S ε := by rw [p14Last]; positivity
  linarith

lemma p14asm_e_Bracket_inv (D R S : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S:ℝ) ≤ p14Bracket D R S ε := by
  rw [p14Bracket]
  have h1 : 0 ≤ (D:ℝ) := by positivity
  have h3 : 0 ≤ (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3)
      * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^(4:ℕ) := by positivity
  have h4 : 0 ≤ p14Last R S ε := by rw [p14Last]; positivity
  linarith

lemma p14asm_e_Bracket_mid (D R S : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3) * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^(4:ℕ)
      ≤ p14Bracket D R S ε := by
  rw [p14Bracket]
  have h1 : 0 ≤ (D:ℝ) := by positivity
  have h2 : 0 ≤ (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ)*(S:ℝ) := by positivity
  have h4 : 0 ≤ p14Last R S ε := by rw [p14Last]; positivity
  linarith

/-- A term bounded by `p14Last` is bounded by the bracket. -/
lemma p14asm_e_Bracket_of_le_last (D R S : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S)
    {a : ℝ} (ha : a ≤ p14Last R S ε) : a ≤ p14Bracket D R S ε :=
  le_trans ha (p14asm_e_Bracket_last D R S ε hD hR hS)

/-- A term bounded by `K·p14Last` with `K ≤ 8` is bounded by `8·` the bracket. -/
lemma p14asm_ul8_le_TBracket_last (D R S : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S)
    {a K : ℝ} (ha : a ≤ K * p14Last R S ε) (_hK : 0 ≤ K) (hK8 : K ≤ 8) :
    a ≤ 8 * p14Bracket D R S ε := by
  have hlast := p14asm_e_Bracket_last D R S ε hD hR hS
  have hlt : 0 ≤ p14Last R S ε := by rw [p14Last]; positivity
  calc a ≤ K * p14Last R S ε := ha
    _ ≤ 8 * p14Last R S ε := mul_le_mul_of_nonneg_right hK8 hlt
    _ ≤ 8 * p14Bracket D R S ε := mul_le_mul_of_nonneg_left hlast (by norm_num)

/-- `2^{1/24} ≤ 8`. -/
lemma p14asm_wo_pow_le_eight : (2:ℝ) ^ ((1:ℝ)/24) ≤ 8 := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    (by norm_num : ((1:ℝ)/24) ≤ (3:ℝ))
  have h3 : (2:ℝ) ^ (3:ℝ) = 8 := by norm_num [Real.rpow_natCast]
  rw [h3] at h
  exact h

/-! ## The three case estimates -/

/-- Proposition 11.1's bracket is dominated by `8·` the bracket of Proposition 14.1 when
`D ≤ D₁`. -/
lemma p14asm_ase111 (D R S : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hcase : (D:ℝ) ≤ p14D1 R S) : p14T11 D R S ε ≤ 16 * p14Bracket D R S ε := by
  have hexp : p14T11 D R S ε
      = (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S:ℝ)
        + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * (((R:ℝ)*(S:ℝ))^ε)
        + ((R:ℝ) * (S:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε)
        + ((S:ℝ) * (R:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε) := by
    rw [p14T11]; ring
  rw [hexp]
  have h1 := p14asm_e_Bracket_inv D R S ε hD hR hS
  have h2 : (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * (((R:ℝ)*(S:ℝ))^ε) ≤ p14Bracket D R S ε :=
    p14asm_e_Bracket_of_le_last D R S ε hD hR hS (p14asm_eyA D R S ε hR hS hD hcase)
  have h3 : ((R:ℝ) * (S:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε) ≤ p14Bracket D R S ε :=
    p14asm_e_Bracket_of_le_last D R S ε hD hR hS (p14asm_Y34_eps R S ε hR hS)
  have h4 : ((S:ℝ) * (R:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε) ≤ p14Bracket D R S ε :=
    p14asm_e_Bracket_of_le_last D R S ε hD hR hS (p14asm_X34_eps R S ε hR hS)
  have hTB : 0 ≤ p14Bracket D R S ε := by
    have := p14asm_e_Bracket_last D R S ε hD hR hS
    have : 0 ≤ p14Last R S ε := by rw [p14Last]; positivity
    linarith
  linarith

/-- Proposition 12.1's bracket is dominated by `8·` the bracket of Proposition 14.1. -/
lemma p14asm_ase121 (D R S : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hcase : p14D2 R S ≤ (D:ℝ)) : p14T12 D R S ε ≤ 16 * p14Bracket D R S ε := by
  have hexp : p14T12 D R S ε
      = (D:ℝ)
        + (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3)
            * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^(4:ℕ)
        + ((D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2)) * (((R:ℝ)*(S:ℝ))^ε)
        + ((R:ℝ) * (S:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε)
        + ((S:ℝ) * (R:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε) := by
    rw [p14T12]; ring
  rw [hexp]
  have h1 := p14asm_e_Bracket_D D R S ε hD hR hS
  have h2 := p14asm_e_Bracket_mid D R S ε hD hR hS
  have h3 : ((D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2)) * (((R:ℝ)*(S:ℝ))^ε)
      ≤ 8 * p14Bracket D R S ε :=
    p14asm_ul8_le_TBracket_last D R S ε hD hR hS (p14asm_eyE D R S ε hR hS hD hcase) (by positivity)
      p14asm_wo_pow_le_eight
  have h4 : ((R:ℝ) * (S:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε) ≤ p14Bracket D R S ε :=
    p14asm_e_Bracket_of_le_last D R S ε hD hR hS (p14asm_Y34_eps R S ε hR hS)
  have h5 : ((S:ℝ) * (R:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε) ≤ p14Bracket D R S ε :=
    p14asm_e_Bracket_of_le_last D R S ε hD hR hS (p14asm_X34_eps R S ε hR hS)
  have hTB : 0 ≤ p14Bracket D R S ε := by
    have := p14asm_e_Bracket_last D R S ε hD hR hS
    have : 0 ≤ p14Last R S ε := by rw [p14Last]; positivity
    linarith
  linarith

/-- Proposition 13.1's bracket is dominated by `8·` the bracket of Proposition 14.1 when
`D₁ < D < D₂`. -/
lemma p14asm_ase131 (D R S : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hcase1 : p14D1 R S < (D:ℝ)) (hcase2 : (D:ℝ) < p14D2 R S) :
    p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε) ≤ 16 * p14Bracket D R S ε := by
  have hP : (0:ℝ) < (R:ℝ)*(S:ℝ) := p14asm_Ppos hR hS
  have hexp : p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε)
      = (D:ℝ) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((1:ℝ)/4)
          * (((R:ℝ)*(S:ℝ))^ε)
        + (D:ℝ)^(-(1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8) * ((R:ℝ)*(S:ℝ))^((9:ℝ)/8)
          * (((R:ℝ)*(S:ℝ))^ε) := by
    rw [p14T13]; ring
  rw [hexp]
  have h1 : (D:ℝ) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((1:ℝ)/4)
      * (((R:ℝ)*(S:ℝ))^ε) ≤ 8 * p14Bracket D R S ε :=
    p14asm_ul8_le_TBracket_last D R S ε hD hR hS
      (p14asm_eyF D R S ε hR hS hD (le_of_lt hcase2)) (by positivity) p14asm_wo_pow_le_eight
  have h2 : (D:ℝ)^(-(1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8) * ((R:ℝ)*(S:ℝ))^((9:ℝ)/8)
      * (((R:ℝ)*(S:ℝ))^ε) ≤ p14Bracket D R S ε :=
    p14asm_e_Bracket_of_le_last D R S ε hD hR hS (p14asm_eyG D R S ε hR hS hD (le_of_lt hcase1))
  have hTB : 0 ≤ p14Bracket D R S ε := by
    have := p14asm_e_Bracket_last D R S ε hD hR hS
    have : 0 ≤ p14Last R S ε := by rw [p14Last]; positivity
    linarith
  linarith

/-! ## The energy comparison -/

lemma p14asm_ne_le_card_divisors {r : ℕ} (hr : 1 ≤ r) : (1:ℝ) ≤ ((r.divisors.card : ℕ) : ℝ) := by
  have h : 1 ≤ r.divisors.card := by
    apply Finset.card_pos.mpr
    refine ⟨1, ?_⟩
    rw [Nat.mem_divisors]
    exact ⟨one_dvd r, by omega⟩
  exact_mod_cast h

/-- `Σ‖α‖² ≤ Σ τ(r)‖α‖²` on the box. -/
lemma p14asm_2_le_Ener (R S : ℕ) (α : ℕ → ℕ → ℂ) : p14L2 R S α ≤ p14Ener R S α := by
  rw [p14L2, p14Ener]
  refine Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun s _ => ?_))
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have h := p14asm_ne_le_card_divisors hr1
  have hnn : 0 ≤ Complex.normSq (α r s) := Complex.normSq_nonneg _
  calc Complex.normSq (α r s) = 1 * Complex.normSq (α r s) := (one_mul _).symm
    _ ≤ ((r.divisors.card : ℕ) : ℝ) * Complex.normSq (α r s) :=
        mul_le_mul_of_nonneg_right h hnn

/-! ## The three input estimates of §§11–13 and the assembly -/

/-- **FI Proposition 14.1**, assembled from the estimates of Propositions 11.1, 12.1 and 13.1.
The bracket is written out in full so that the statement is definitionally the target. -/
theorem p14asm_assembly (ε : ℝ) (_hε : 0 < ε)
    (h1 : p14Prop111 ε) (h2 : p14Prop121 ε) (h3 : p14Prop131 ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        Work.FIPlan.Vvar R S D α ≤ C * p14Bracket D R S ε * p14Ener R S α := by
  obtain ⟨C1, hC1, hB1⟩ := h1
  obtain ⟨C2, hC2, hB2⟩ := h2
  obtain ⟨C3, hC3, hB3⟩ := h3
  refine ⟨16 * (C1 + C2 + C3) + 1, by positivity, ?_⟩
  intro D R S α hD hR hS hsupp
  have hTM : 0 ≤ p14Bracket D R S ε := by
    have := p14asm_e_Bracket_last D R S ε hD hR hS
    have : 0 ≤ p14Last R S ε := by rw [p14Last]; positivity
    linarith
  have hE : 0 ≤ p14Ener R S α := by
    rw [p14Ener]
    refine Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => ?_))
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  have hL2 : 0 ≤ p14L2 R S α := by
    rw [p14L2]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
  have hL2E := p14asm_2_le_Ener R S α
  have hC1' : 0 < C1 := hC1
  have hfin : ∀ {Cx : ℝ} {T : ℝ}, 0 < Cx → 0 ≤ T →
      Cx * T * p14Ener R S α ≤ (16 * (C1 + C2 + C3) + 1) * p14Bracket D R S ε * p14Ener R S α → True := by
    intro Cx T _ _ _
    trivial
  by_cases hcase : (D:ℝ) ≤ p14D1 R S
  · have hV := hB1 D R S α hD hR hS
    have hk := p14asm_ase111 D R S ε hD hR hS hcase
    have hTnn : 0 ≤ p14T11 D R S ε := by rw [p14T11]; positivity
    have hstep : p14T11 D R S ε * p14L2 R S α ≤ (16 * p14Bracket D R S ε) * p14Ener R S α :=
      calc p14T11 D R S ε * p14L2 R S α ≤ p14T11 D R S ε * p14Ener R S α :=
            mul_le_mul_of_nonneg_left hL2E hTnn
        _ ≤ (16 * p14Bracket D R S ε) * p14Ener R S α := mul_le_mul_of_nonneg_right hk hE
    calc Work.FIPlan.Vvar R S D α ≤ C1 * p14T11 D R S ε * p14L2 R S α := hV
      _ = C1 * (p14T11 D R S ε * p14L2 R S α) := by ring
      _ ≤ C1 * ((16 * p14Bracket D R S ε) * p14Ener R S α) :=
          mul_le_mul_of_nonneg_left hstep hC1.le
      _ ≤ (16 * (C1 + C2 + C3) + 1) * p14Bracket D R S ε * p14Ener R S α := by
          have h0 : 0 ≤ (16 * C2 + 16 * C3 + 1) * (p14Bracket D R S ε * p14Ener R S α) :=
            mul_nonneg (by linarith [hC2, hC3]) (mul_nonneg hTM hE)
          nlinarith [h0]
  · by_cases hcase2 : p14D2 R S ≤ (D:ℝ)
    · have hV := hB2 D R S α hD hR hS hsupp
      have hk := p14asm_ase121 D R S ε hD hR hS hcase2
      calc Work.FIPlan.Vvar R S D α ≤ C2 * p14T12 D R S ε * p14Ener R S α := hV
        _ = C2 * (p14T12 D R S ε * p14Ener R S α) := by ring
        _ ≤ C2 * ((16 * p14Bracket D R S ε) * p14Ener R S α) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk hE) hC2.le
        _ ≤ (16 * (C1 + C2 + C3) + 1) * p14Bracket D R S ε * p14Ener R S α := by
            have h0 : 0 ≤ (16 * C1 + 16 * C3 + 1) * (p14Bracket D R S ε * p14Ener R S α) :=
              mul_nonneg (by linarith [hC1, hC3]) (mul_nonneg hTM hE)
            nlinarith [h0]
    · have hV := hB3 D R S α hD hR hS hsupp
      have hk := p14asm_ase131 D R S ε hD hR hS (not_le.mp hcase) (not_le.mp hcase2)
      have hL2nn : 0 ≤ p14L2 R S α := hL2
      calc Work.FIPlan.Vvar R S D α
            ≤ C3 * p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε) * p14L2 R S α := hV
        _ = C3 * ((p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε)) * p14L2 R S α) := by ring
        _ ≤ C3 * ((16 * p14Bracket D R S ε) * p14Ener R S α) := by
            refine mul_le_mul_of_nonneg_left ?_ hC3.le
            calc (p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε)) * p14L2 R S α
                ≤ (16 * p14Bracket D R S ε) * p14L2 R S α :=
                  mul_le_mul_of_nonneg_right hk hL2nn
              _ ≤ (16 * p14Bracket D R S ε) * p14Ener R S α :=
                  mul_le_mul_of_nonneg_left hL2E (mul_nonneg (by norm_num) hTM)
        _ ≤ (16 * (C1 + C2 + C3) + 1) * p14Bracket D R S ε * p14Ener R S α := by
            have h0 : 0 ≤ (16 * C1 + 16 * C2 + 1) * (p14Bracket D R S ε * p14Ener R S α) :=
              mul_nonneg (by linarith [hC1, hC2]) (mul_nonneg hTM hE)
            nlinarith [h0]

end

end Work.FIArea4
