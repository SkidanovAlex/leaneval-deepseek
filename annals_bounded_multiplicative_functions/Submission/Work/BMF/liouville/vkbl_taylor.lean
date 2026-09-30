import Mathlib
import Submission.Work.BMF.liouville.vkbl_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Taylor comparison of `Trel` with `TrelP`
-/

open Finset

namespace Work.BMF.liouville

noncomputable section

/-- `‖eC z - 1‖ ≤ 2π|z|`. -/
lemma norm_eC_sub_one_le (z : ℝ) : ‖Work.BMF.eC z - 1‖ ≤ 2 * Real.pi * |z| := by
  have h : Work.BMF.eC z = Complex.exp (Complex.I * (((2 * Real.pi * z : ℝ)) : ℂ)) := by
    unfold Work.BMF.eC
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ))
        = Complex.I * (((2 * Real.pi * z : ℝ)) : ℂ) by push_cast; ring]
  rw [h]
  calc ‖Complex.exp (Complex.I * (((2 * Real.pi * z : ℝ)) : ℂ)) - 1‖
      ≤ ‖(2 * Real.pi * z : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |z| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]

/-- `‖eC a - eC b‖ ≤ 2π|a - b|`. -/
lemma norm_eC_sub_le (a b : ℝ) : ‖Work.BMF.eC a - Work.BMF.eC b‖ ≤ 2 * Real.pi * |a - b| := by
  have h : Work.BMF.eC a - Work.BMF.eC b = Work.BMF.eC b * (Work.BMF.eC (a - b) - 1) := by
    rw [mul_sub, mul_one, ← Work.BMF.zpt.eC_add, show b + (a - b) = a by ring]
  rw [h, norm_mul, Work.BMF.zpt.eC_norm, one_mul]
  exact norm_eC_sub_one_le (a - b)

/-- The Taylor phase in the `range` (= alternating-series) form. -/
lemma tayPhase_eq_sum_range (k : ℕ) (t u : ℝ) (n m : ℕ) :
    Work.BMF.zpt.tayPhase k t (n : ℝ) u m
      = (t / (2 * Real.pi)) *
          ∑ i ∈ Finset.range k,
            (-1 : ℝ) ^ (i + 1) * ((m : ℝ) / ((n : ℝ) + u)) ^ (i + 1) / ((i : ℝ) + 1) := by
  unfold Work.BMF.zpt.tayPhase Work.BMF.zpt.gam
  rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) from by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_pow]
  simp only [Nat.add_comm 1 i]
  push_cast
  first | (field_simp; ring) | field_simp

/-- The log remainder: the degree-`k` Taylor polynomial of `-(t/2π)log(1+y)` differs from it by
at most `(t/2π) y^{k+1}/(1-y)`, for `y ≥ 0`, `y < 1`, `t ≥ 0`. -/
lemma abs_phase_sub_tayPhase_le (k : ℕ) (t u : ℝ) (n m : ℕ) (ht : 0 ≤ t) (hn : 1 ≤ n) (hu : 0 < u)
    (hy : (m : ℝ) / ((n : ℝ) + u) < 1) :
    |-(t / (2 * Real.pi)) * Real.log (1 + (m : ℝ) / ((n : ℝ) + u))
        - Work.BMF.zpt.tayPhase k t (n : ℝ) u m|
      ≤ (t / (2 * Real.pi)) * ((m : ℝ) / ((n : ℝ) + u)) ^ (k + 1)
          / (1 - (m : ℝ) / ((n : ℝ) + u)) := by
  set y : ℝ := (m : ℝ) / ((n : ℝ) + u) with hydef
  have hy0 : 0 ≤ y := by rw [hydef]; positivity
  have hylt : |y| < 1 := by rw [abs_of_nonneg hy0]; exact hy
  have hlog := Real.abs_log_sub_add_sum_range_le (x := -y) (by rwa [abs_neg]) k
  simp only [sub_neg_eq_add] at hlog
  rw [abs_neg, abs_of_nonneg hy0] at hlog
  have hsum : ∑ i ∈ Finset.range k, (-y) ^ (i + 1) / ((i : ℝ) + 1)
      = ∑ i ∈ Finset.range k, (-1 : ℝ) ^ (i + 1) * y ^ (i + 1) / ((i : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_pow]
  rw [hsum] at hlog
  have hphase := tayPhase_eq_sum_range k t u n m
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have ht0 : 0 ≤ t / (2 * Real.pi) := div_nonneg ht h2pi.le
  rw [hphase]
  have hsplit : -(t / (2 * Real.pi)) * Real.log (1 + y)
        - (t / (2 * Real.pi)) * (∑ i ∈ Finset.range k, (-1 : ℝ) ^ (i + 1) * y ^ (i + 1) / ((i : ℝ) + 1))
      = -(t / (2 * Real.pi)) * (Real.log (1 + y)
          + ∑ i ∈ Finset.range k, (-1 : ℝ) ^ (i + 1) * y ^ (i + 1) / ((i : ℝ) + 1)) := by ring
  rw [hsplit, abs_mul, abs_neg, abs_of_nonneg ht0]
  rw [add_comm] at hlog
  calc (t / (2 * Real.pi))
        * |Real.log (1 + y) + ∑ i ∈ Finset.range k, (-1 : ℝ) ^ (i + 1) * y ^ (i + 1) / ((i : ℝ) + 1)|
      ≤ (t / (2 * Real.pi)) * (y ^ (k + 1) / (1 - y)) := mul_le_mul_of_nonneg_left hlog ht0
    _ = (t / (2 * Real.pi)) * y ^ (k + 1) / (1 - y) := by ring

/-- Per-term Taylor comparison. -/
lemma norm_relT_sub_tayRel_le (k : ℕ) (u t : ℝ) (n m : ℕ) (hn : 1 ≤ n) (hu : 0 < u)
    (ht : 0 ≤ t) (hy : (m : ℝ) / ((n : ℝ) + u) < 1) :
    ‖relT u t n m - tayRel k u t n m‖ ≤
      t * ((m : ℝ) / ((n : ℝ) + u)) ^ (k + 1) / (1 - (m : ℝ) / ((n : ℝ) + u)) := by
  have h := abs_phase_sub_tayPhase_le k t u n m ht hn hu hy
  have hrepr : relT u t n m - tayRel k u t n m
      = Work.BMF.eC (-(t / (2 * Real.pi)) * Real.log (1 + (m : ℝ) / ((n : ℝ) + u)))
        - Work.BMF.eC (Work.BMF.zpt.tayPhase k t (n : ℝ) u m) := rfl
  rw [hrepr]
  refine le_trans (norm_eC_sub_le _ _) ?_
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  calc 2 * Real.pi * |-(t / (2 * Real.pi)) * Real.log (1 + (m : ℝ) / ((n : ℝ) + u))
          - Work.BMF.zpt.tayPhase k t (n : ℝ) u m|
      ≤ 2 * Real.pi * ((t / (2 * Real.pi)) * ((m : ℝ) / ((n : ℝ) + u)) ^ (k + 1)
          / (1 - (m : ℝ) / ((n : ℝ) + u))) := mul_le_mul_of_nonneg_left h h2pi.le
    _ = t * ((m : ℝ) / ((n : ℝ) + u)) ^ (k + 1) / (1 - (m : ℝ) / ((n : ℝ) + u)) := by
        field_simp

theorem Trel_sub_TrelP (k M : ℕ) (n : ℕ) (u t : ℝ) (hn : 1 ≤ n) (hu : 0 < u) (ht : 0 ≤ t)
    (hM : (M : ℝ) ≤ ((n : ℝ) + u) / 2) :
    ‖Trel M n u t - TrelP k M n u t‖ ≤
      (M : ℝ) * (t * ((M : ℝ) / ((n : ℝ) + u)) ^ (k + 1) / (1 - (M : ℝ) / ((n : ℝ) + u))) := by
  have hDpos : 0 < (n : ℝ) + u := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hR1 : (M : ℝ) / ((n : ℝ) + u) ≤ 1 / 2 := by
    rw [div_le_iff₀ hDpos]; linarith
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      ‖relT u t n m - tayRel k u t n m‖ ≤
        t * ((M : ℝ) / ((n : ℝ) + u)) ^ (k + 1) / (1 - (M : ℝ) / ((n : ℝ) + u)) := by
    intro m hm
    have hmM : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hx0 : 0 ≤ (m : ℝ) / ((n : ℝ) + u) := by positivity
    have hxle : (m : ℝ) / ((n : ℝ) + u) ≤ (M : ℝ) / ((n : ℝ) + u) :=
      div_le_div_of_nonneg_right hmM hDpos.le
    have hxlt : (m : ℝ) / ((n : ℝ) + u) < 1 := lt_of_le_of_lt (le_trans hxle hR1) (by norm_num)
    refine le_trans (norm_relT_sub_tayRel_le k u t n m hn hu ht hxlt) ?_
    have h1 : ((m : ℝ) / ((n : ℝ) + u)) ^ (k + 1) ≤ ((M : ℝ) / ((n : ℝ) + u)) ^ (k + 1) :=
      pow_le_pow_left₀ hx0 hxle (k + 1)
    have h2 : 1 - (M : ℝ) / ((n : ℝ) + u) ≤ 1 - (m : ℝ) / ((n : ℝ) + u) := by linarith
    have h3 : ((m : ℝ) / ((n : ℝ) + u)) ^ (k + 1) / (1 - (m : ℝ) / ((n : ℝ) + u))
        ≤ ((M : ℝ) / ((n : ℝ) + u)) ^ (k + 1) / (1 - (M : ℝ) / ((n : ℝ) + u)) :=
      div_le_div₀ (pow_nonneg (by positivity : (0:ℝ) ≤ (M : ℝ) / ((n : ℝ) + u)) _) h1
        (by linarith) h2
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left h3 ht
  calc ‖Trel M n u t - TrelP k M n u t‖
      = ‖∑ m ∈ Finset.Icc 1 M, (relT u t n m - tayRel k u t n m)‖ := by
        simp only [Trel, TrelP, Finset.sum_sub_distrib]
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ‖relT u t n m - tayRel k u t n m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 M,
          (t * ((M : ℝ) / ((n : ℝ) + u)) ^ (k + 1) / (1 - (M : ℝ) / ((n : ℝ) + u))) :=
        Finset.sum_le_sum hterm
    _ = (M : ℝ) * (t * ((M : ℝ) / ((n : ℝ) + u)) ^ (k + 1)
          / (1 - (M : ℝ) / ((n : ℝ) + u))) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel]; simp

end

end Work.BMF.liouville
