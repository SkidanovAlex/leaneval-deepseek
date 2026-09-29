import Mathlib
import Submission.Work.TMC16Core.NrFinal.sepBdefs
import Submission.Work.Basic.UniNonres.Defs

/-!
# `cls_add_le_sepB`

`cls c δ m` is the single-cluster bound for `∑ -log (sin (π v))` over `m` points
`v ∈ [c,1/2]` that are pairwise `δ`-separated (`cls c δ 0 = 0`,
`cls c δ (m+1) = log (1/(2c)) + m log (1/(2δ)) - log (m!)`), while `sepB c δ M` is
the two-cluster bound `2 log (1/(2 min c δ)) + (M-2) log (1/(2δ)) - 2 log (⌊(M-2)/2⌋!)`.

The two-cluster bound is obtained from two single-cluster bounds of sizes `m₁`, `m₂` by
combining them with the factorial inequality `a! b! ≥ (⌊(a+b)/2⌋!)²` (`factorial_central_sq`)
and the elementary `min c δ ≤ c`, `min c δ ≤ δ`.

This file proves `cls c δ m₁ + cls c δ m₂ ≤ sepB c δ (m₁ + m₂)` from scratch (including the
factorial inequality), independent of `factorial_central` / `cls_add_le_of`.
-/

namespace Work.TMC16Core.NrFinal

/-! ## Elementary helpers -/

/-- `2 log x = log (x^2)`. -/
private theorem two_mul_log (x : ℝ) : 2 * Real.log x = Real.log (x^2) := by
  rw [Real.log_pow]; ring

/-! ## The central factorial inequality `(⌊(a+b)/2⌋)!² ≤ a! b!` -/

/-- Auxiliary form of `factorial_central_sq` for `(a, a+d)`. -/
private theorem fac_aux (d : ℕ) : ∀ a : ℕ,
    ((a + (a+d))/2).factorial^2 ≤ a.factorial * (a+d).factorial := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a
    match d with
    | 0 =>
      have h : (a + (a+0))/2 = a := by omega
      rw [h]; simp [pow_two]
    | 1 =>
      have h : (a + (a+1))/2 = a := by omega
      rw [h]
      have : a.factorial ≤ (a+1).factorial := Nat.factorial_le (by omega)
      calc a.factorial^2 = a.factorial * a.factorial := by rw [pow_two]
        _ ≤ a.factorial * (a+1).factorial := Nat.mul_le_mul_left _ this
    | (k+2) =>
      have hidx : (a + (a+(k+2)))/2 = ((a+1) + ((a+1)+k))/2 := by omega
      rw [hidx]
      have hIH := ih k (by omega) (a+1)
      calc (((a+1) + ((a+1)+k))/2).factorial^2
          ≤ (a+1).factorial * ((a+1)+k).factorial := hIH
        _ ≤ a.factorial * (a+(k+2)).factorial := by
            rw [Nat.factorial_succ a]
            rw [show a + (k+2) = ((a+1)+k)+1 by omega, Nat.factorial_succ]
            have hle : (a+1) ≤ ((a+1)+k)+1 := by omega
            calc (a+1) * a.factorial * ((a+1)+k).factorial
                = (a+1) * (a.factorial * ((a+1)+k).factorial) := by ring
              _ ≤ (((a+1)+k)+1) * (a.factorial * ((a+1)+k).factorial) :=
                    Nat.mul_le_mul_right _ hle
              _ = a.factorial * ((((a+1)+k)+1) * ((a+1)+k).factorial) := by ring

/-- `(⌊(a+b)/2⌋)!² ≤ a! b!` ("the product of factorials is minimised when balanced"). -/
private theorem factorial_central_sq (a b : ℕ) :
    ((a + b)/2).factorial^2 ≤ a.factorial * b.factorial := by
  rcases le_total a b with h | h
  · have hb : b = a + (b - a) := by omega
    conv_lhs => rw [hb]
    conv_rhs => rw [hb]
    exact fac_aux (b - a) a
  · have ha : a = b + (a - b) := by omega
    have key := fac_aux (a - b) b
    conv_lhs => rw [ha]
    conv_rhs => rw [ha]
    rw [show (b + (a - b)) + b = b + (b + (a - b)) by omega]
    rw [Nat.mul_comm]
    exact key

/-- If `2k ≤ n` then `k!² ≤ n!`. -/
private theorem fac_sq_le_of_two_mul_le (k n : ℕ) (h : 2*k ≤ n) :
    k.factorial^2 ≤ n.factorial := by
  have h1 : k.factorial ≤ (k+1)^k := by
    calc k.factorial ≤ k^k := Nat.factorial_le_pow k
      _ ≤ (k+1)^k := by apply pow_le_pow_left₀ (by omega) (by omega)
  have h2 : k.factorial * (k+1)^k ≤ (k+k).factorial := by
    simpa using Nat.factorial_mul_pow_le_factorial (m:=k) (n:=k)
  have h3 : k.factorial^2 ≤ (k+k).factorial := by
    calc k.factorial^2 = k.factorial * k.factorial := by rw [pow_two]
      _ ≤ k.factorial * (k+1)^k := Nat.mul_le_mul_left _ h1
      _ ≤ (k+k).factorial := h2
  exact le_trans h3 (Nat.factorial_le (by omega))

/-! ## Factorial inequalities in logarithmic form -/

private theorem log_two_log_le (a b : ℕ) (h : a.factorial^2 ≤ b.factorial) :
    2 * Real.log ((a.factorial : ℕ) : ℝ) ≤ Real.log ((b.factorial : ℕ) : ℝ) := by
  rw [two_mul_log]
  apply Real.log_le_log (by positivity)
  exact_mod_cast h

private theorem log_two_fac_le (k₁ k₂ : ℕ)
    (h : (((k₁+k₂)/2).factorial)^2 ≤ k₁.factorial * k₂.factorial) :
    2 * Real.log ((((k₁+k₂)/2).factorial : ℕ) : ℝ)
      ≤ Real.log ((k₁.factorial:ℕ):ℝ) + Real.log ((k₂.factorial:ℕ):ℝ) := by
  rw [two_mul_log, ← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  exact_mod_cast h

/-! ## Elementary inequalities for `min c δ` -/

private theorem log_c_le_log_min {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    Real.log (1/(2*c)) ≤ Real.log (1/(2*min c δ)) := by
  apply Real.log_le_log (by positivity)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [min_le_left c δ, min_le_right c δ, lt_min hc hδ]

private theorem log_pair_le {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    Real.log (1/(2*c)) + Real.log (1/(2*δ)) ≤ 2 * Real.log (1/(2*min c δ)) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  rw [two_mul_log]
  apply Real.log_le_log (by positivity)
  rw [div_mul_div_comm, div_pow]
  simp only [one_mul, one_pow]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [min_le_left c δ, min_le_right c δ, lt_min hc hδ]

/-! ## The single-cluster bound against `sepB` -/

private theorem cls_le_sepB_ge2 {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) {m : ℕ} (hm : 2 ≤ m) :
    cls c δ m ≤ Work.Basic.UniNonres.sepB c δ m := by
  have hcls : cls c δ m
      = Real.log (1/(2*c)) + ((m-1:ℕ):ℝ) * Real.log (1/(2*δ))
        - Real.log (((m-1).factorial:ℕ):ℝ) := by
    conv_lhs => rw [show m = (m-1)+1 by omega]
    rw [cls_succ]
  have hsep : Work.Basic.UniNonres.sepB c δ m
      = 2 * Real.log (1/(2*min c δ)) + ((m:ℝ) - 2) * Real.log (1/(2*δ))
        - 2 * Real.log ((((m-2)/2).factorial:ℕ):ℝ) := by
    rw [Work.Basic.UniNonres.sepB, if_neg (by omega : ¬ (m ≤ 1))]
  rw [hcls, hsep]
  have hA := log_pair_le hc hδ
  have hF : 2 * Real.log ((((m-2)/2).factorial:ℕ):ℝ) ≤ Real.log (((m-1).factorial:ℕ):ℝ) :=
    log_two_log_le ((m-2)/2) (m-1) (fac_sq_le_of_two_mul_le _ _ (by omega))
  have hm1 : ((m - 1 : ℕ) : ℝ) * Real.log (1/(2*δ))
      = ((m:ℝ) - 2) * Real.log (1/(2*δ)) + Real.log (1/(2*δ)) := by
    have hsub : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := Nat.cast_sub hm
    have h1 : ((m-1:ℕ):ℝ) = ((m-2:ℕ):ℝ) + 1 := by
      have : m - 1 = (m - 2) + 1 := by omega
      rw [this]; push_cast; ring
    rw [h1, ← hsub]; ring
  rw [hm1]
  linarith [hA, hF]

private theorem cls_le_sepB {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (m : ℕ) :
    cls c δ m ≤ Work.Basic.UniNonres.sepB c δ m := by
  rcases m with _ | _ | k
  · simp [Work.Basic.UniNonres.sepB]
  · simp [Work.Basic.UniNonres.sepB, cls_succ]
  · exact cls_le_sepB_ge2 hc hδ (by omega : 2 ≤ k + 2)

/-! ## The two-cluster bound -/

private theorem cls_add_pos {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    cls c δ a + cls c δ b ≤ Work.Basic.UniNonres.sepB c δ (a + b) := by
  have hcla : cls c δ a
      = Real.log (1/(2*c)) + ((a-1:ℕ):ℝ) * Real.log (1/(2*δ))
        - Real.log (((a-1).factorial:ℕ):ℝ) := by
    conv_lhs => rw [show a = (a-1)+1 by omega]
    rw [cls_succ]
  have hclb : cls c δ b
      = Real.log (1/(2*c)) + ((b-1:ℕ):ℝ) * Real.log (1/(2*δ))
        - Real.log (((b-1).factorial:ℕ):ℝ) := by
    conv_lhs => rw [show b = (b-1)+1 by omega]
    rw [cls_succ]
  have hsep : Work.Basic.UniNonres.sepB c δ (a+b)
      = 2 * Real.log (1/(2*min c δ)) + (((a+b:ℕ):ℝ) - 2) * Real.log (1/(2*δ))
        - 2 * Real.log (((((a+b)-2)/2).factorial:ℕ):ℝ) := by
    rw [Work.Basic.UniNonres.sepB, if_neg (by omega : ¬ (a+b ≤ 1))]
  rw [hcla, hclb, hsep]
  have hcoef : ((a-1:ℕ):ℝ) + ((b-1:ℕ):ℝ) = ((a+b:ℕ):ℝ) - 2 := by
    rw [← Nat.cast_add, show a - 1 + (b - 1) = a + b - 2 by omega,
      Nat.cast_sub (by omega : 2 ≤ a+b)]
    norm_num
  have hL2 : ((a-1:ℕ):ℝ) * Real.log (1/(2*δ)) + ((b-1:ℕ):ℝ) * Real.log (1/(2*δ))
      = (((a+b:ℕ):ℝ) - 2) * Real.log (1/(2*δ)) := by rw [← add_mul, hcoef]
  have hAB : 2 * Real.log (1/(2*c)) ≤ 2 * Real.log (1/(2*min c δ)) := by
    have := log_c_le_log_min hc hδ; linarith
  have hFF : 2 * Real.log (((((a+b)-2)/2).factorial:ℕ):ℝ)
      ≤ Real.log (((a-1).factorial:ℕ):ℝ) + Real.log (((b-1).factorial:ℕ):ℝ) := by
    have hidx : ((a-1) + (b-1))/2 = ((a+b)-2)/2 := by omega
    have hfac := factorial_central_sq (a-1) (b-1)
    have h := log_two_fac_le (a-1) (b-1) hfac
    rwa [hidx] at h
  linarith [hAB, hFF, hL2]

theorem cls_add_le_sepB {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (m₁ m₂ : ℕ) :
    Work.TMC16Core.NrFinal.cls c δ m₁ + Work.TMC16Core.NrFinal.cls c δ m₂
      ≤ Work.Basic.UniNonres.sepB c δ (m₁ + m₂) := by
  rcases Nat.eq_zero_or_pos m₁ with h1 | h1
  · subst h1
    simpa using cls_le_sepB hc hδ m₂
  rcases Nat.eq_zero_or_pos m₂ with h2 | h2
  · subst h2
    simpa using cls_le_sepB hc hδ m₁
  · exact cls_add_pos hc hδ h1 h2

end Work.TMC16Core.NrFinal
