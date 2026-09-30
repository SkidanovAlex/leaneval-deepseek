import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The purely arithmetic core of the `κ'·κ ≤ C(n,d)` estimate: dropping the
`min`/`max` pair `≤ 1`, the two constants combine to
`(9/4)(n+1) r^{r+1} (64d)^{r+2} log(2rd) (64nd)^{n-r} n!/2^{n-1}`, which equals
`18 (n+1) n! n^{n-r} (32d)^{n+2} · (r^{r+1} log(2rd))` and is dominated by
`C(n,d) = 18 (n+1)! n^{n+1} (32d)^{n+2} log(2nd)` because `r ≤ n`. -/
private lemma bw_arith_core (n d r : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (hr1 : 1 ≤ r) (hr2 : r ≤ n) :
    (9 / 4 : ℝ) * ((n : ℝ) + 1) * (r : ℝ) ^ (r + 1) * (64 * (d : ℝ)) ^ (r + 2) *
        Real.log (2 * (r : ℝ) * (d : ℝ)) *
      ((64 * (n : ℝ) * (d : ℝ)) ^ (n - r) * ((n.factorial : ℝ) / 2 ^ (n - 1)))
    ≤ 18 * ((n + 1).factorial : ℝ) * (n : ℝ) ^ (n + 1) * (32 * (d : ℝ)) ^ (n + 2) *
        Real.log (2 * (n : ℝ) * (d : ℝ)) := by
  -- Combine the two power towers: `(64d)^{r+2} (64nd)^{n-r} = 2^{n+2} (32d)^{n+2} n^{n-r}`.
  have hprod : (64 * (d:ℝ))^(r+2) * (64 * (n:ℝ) * (d:ℝ))^(n-r)
      = (2:ℝ)^(n+2) * (32 * (d:ℝ))^(n+2) * (n:ℝ)^(n-r) := by
    have h1 : (64 * (d:ℝ))^(r+2) = (64:ℝ)^(r+2) * (d:ℝ)^(r+2) := by rw [mul_pow]
    have h2 : (64 * (n:ℝ) * (d:ℝ))^(n-r) = (64:ℝ)^(n-r) * (n:ℝ)^(n-r) * (d:ℝ)^(n-r) := by
      rw [mul_pow, mul_pow]
    have h3 : (32 * (d:ℝ))^(n+2) = (32:ℝ)^(n+2) * (d:ℝ)^(n+2) := by rw [mul_pow]
    have h64' : (64:ℝ)^(n+2) = (2:ℝ)^(n+2) * (32:ℝ)^(n+2) := by
      rw [show (64:ℝ) = 2*32 by norm_num, mul_pow]
    have h64 : (64:ℝ)^(r+2) * (64:ℝ)^(n-r) = (64:ℝ)^(n+2) := by
      rw [← pow_add]; congr 1; omega
    have hd : (d:ℝ)^(r+2) * (d:ℝ)^(n-r) = (d:ℝ)^(n+2) := by
      rw [← pow_add]; congr 1; omega
    rw [h1, h2, h3]
    have hrearr : (64:ℝ)^(r+2) * (d:ℝ)^(r+2) * ((64:ℝ)^(n-r) * (n:ℝ)^(n-r) * (d:ℝ)^(n-r))
        = ((64:ℝ)^(r+2) * (64:ℝ)^(n-r)) * ((d:ℝ)^(r+2)*(d:ℝ)^(n-r)) * (n:ℝ)^(n-r) := by ring
    rw [hrearr, h64, hd, h64']
    ring
  -- Merge the `2`-powers.
  have hcancel : (2:ℝ)^(n+2) * ((n.factorial:ℝ)/2^(n-1)) = 8 * (n.factorial:ℝ) := by
    rw [show (2:ℝ)^(n+2) = 2^(n-1) * 2^3 by
          rw [show n + 2 = (n-1) + 3 by omega, pow_add]]
    have hne : (2:ℝ)^(n-1) ≠ 0 := by positivity
    field_simp
    ring
  have hfac : ((n+1).factorial : ℝ) = ((n:ℝ)+1) * (n.factorial:ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hN : (n:ℝ)^(n+1) = (n:ℝ)^(n-r) * (n:ℝ)^(r+1) := by rw [← pow_add]; congr 1; omega
  -- The monotone core: `r^{r+1} log(2rd) ≤ n^{r+1} log(2nd)`.
  have hlogmono : Real.log (2*(r:ℝ)*(d:ℝ)) ≤ Real.log (2*(n:ℝ)*(d:ℝ)) := by
    apply Real.log_le_log
    · have hr1' : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
      have hd1' : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      nlinarith
    · have hr2' : (r:ℝ) ≤ (n:ℝ) := by exact_mod_cast hr2
      have hdnn : (0:ℝ) ≤ (d:ℝ) := by positivity
      nlinarith
  have hlogpos : 0 ≤ Real.log (2*(r:ℝ)*(d:ℝ)) := by
    apply Real.log_nonneg
    have hr1' : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
    have hd1' : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    nlinarith
  have hRN : (r:ℝ)^(r+1) ≤ (n:ℝ)^(r+1) :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hr2) (r+1)
  have hcore : (r:ℝ)^(r+1) * Real.log (2*(r:ℝ)*(d:ℝ)) ≤
      (n:ℝ)^(r+1) * Real.log (2*(n:ℝ)*(d:ℝ)) :=
    mul_le_mul hRN hlogmono hlogpos (by positivity)
  -- Rewrite the left-hand side into the shape `18 (n+1) n! n^{n-r} (32d)^{n+2} · r^{r+1}log(2rd)`.
  have hL1 : (9 / 4 : ℝ) * ((n : ℝ) + 1) * (r : ℝ) ^ (r + 1) * (64 * (d : ℝ)) ^ (r + 2) *
        Real.log (2 * (r : ℝ) * (d : ℝ)) *
      ((64 * (n : ℝ) * (d : ℝ)) ^ (n - r) * ((n.factorial : ℝ) / 2 ^ (n - 1)))
      = (9/4) * ((n:ℝ)+1) * (r:ℝ)^(r+1) * Real.log (2*(r:ℝ)*(d:ℝ))
          * ((64*(d:ℝ))^(r+2) * (64*(n:ℝ)*(d:ℝ))^(n-r)) * ((n.factorial:ℝ)/2^(n-1)) := by ring
  rw [hL1, hprod]
  have hL2 : (9/4) * ((n:ℝ)+1) * (r:ℝ)^(r+1) * Real.log (2*(r:ℝ)*(d:ℝ))
          * ((2:ℝ)^(n+2) * (32*(d:ℝ))^(n+2) * (n:ℝ)^(n-r)) * ((n.factorial:ℝ)/2^(n-1))
        = (9/4) * ((n:ℝ)+1) * ((r:ℝ)^(r+1) * Real.log (2*(r:ℝ)*(d:ℝ)))
          * (32*(d:ℝ))^(n+2) * (n:ℝ)^(n-r) * ((2:ℝ)^(n+2) * ((n.factorial:ℝ)/2^(n-1))) := by ring
  rw [hL2, hcancel]
  have hfin : (9/4) * ((n:ℝ)+1) * ((r:ℝ)^(r+1) * Real.log (2*(r:ℝ)*(d:ℝ)))
          * (32*(d:ℝ))^(n+2) * (n:ℝ)^(n-r) * (8*(n.factorial:ℝ))
      ≤ 18 * ((n+1).factorial : ℝ) * (n:ℝ)^(n+1) * (32*(d:ℝ))^(n+2) * Real.log (2*(n:ℝ)*(d:ℝ)) := by
    rw [hfac, hN]
    have hK : 0 ≤ 18*((n:ℝ)+1)*(n.factorial:ℝ)*(32*(d:ℝ))^(n+2)*(n:ℝ)^(n-r) := by positivity
    have hthis := mul_le_mul_of_nonneg_left hcore hK
    convert hthis using 1 <;> ring
  exact hfin

/-- `κ'(r) · κ(r) ≤ C(n,d)`: the two §7/§11 constants fit under the §5 Baker–Wüstholz
constant. -/
theorem bw_arith_kappa (n d r v : ℕ) (c : ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d) (hr1 : 1 ≤ r)
    (hr2 : r ≤ n) (hc : 0 < c) :
    kappa' n d r v c * kappa n d r v c ≤ BakerWustholz.C n d := by
  -- The `min(c/2^v,1) · max(2^v/c,1)` pair is at most `1`.
  have hminmax : max (2^v/c) 1 * min (c/2^v) 1 ≤ 1 := by
    have hkey : (2:ℝ)^v / c = (c/2^v)⁻¹ := by rw [inv_div]
    rw [hkey]
    set a : ℝ := c/2^v with ha'
    have hapos : 0 < a := by rw [ha']; positivity
    have hane : a ≠ 0 := ne_of_gt hapos
    rcases le_or_gt a 1 with h | h
    · have h1 : min a 1 = a := min_eq_left h
      have h2 : max a⁻¹ 1 = a⁻¹ := max_eq_left ((one_le_inv₀ hapos).mpr h)
      rw [h1, h2]; exact le_of_eq (inv_mul_cancel₀ hane)
    · have h1 : min a 1 = 1 := min_eq_right h.le
      have h2 : max a⁻¹ 1 = 1 := max_eq_right ((inv_le_one₀ hapos).mpr h.le)
      rw [h1, h2]; norm_num
  rw [kappa', kappa, BakerWustholz.C]
  set A : ℝ := 9/4 * ((n:ℝ)+1) * (r:ℝ)^(r+1) * (64*(d:ℝ))^(r+2) * Real.log (2*(r:ℝ)*(d:ℝ)) with hAdef
  set B : ℝ := (64*(n:ℝ)*(d:ℝ))^(n-r) * ((n.factorial:ℝ)/2^(n-1)) with hBdef
  have hlogpos : 0 ≤ Real.log (2*(r:ℝ)*(d:ℝ)) := by
    apply Real.log_nonneg
    have hr1' : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
    have hd1' : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    nlinarith
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (by positivity)) (by positivity)) hlogpos
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hstep : A * max (2^v/c) 1 * (B * min (c/2^v) 1) ≤ A * B := by
    have hr : A * max (2^v/c) 1 * (B * min (c/2^v) 1)
        = (A*B) * (max (2^v/c) 1 * min (c/2^v) 1) := by ring
    rw [hr]
    calc (A*B) * (max (2^v/c) 1 * min (c/2^v) 1) ≤ (A*B) * 1 :=
          mul_le_mul_of_nonneg_left hminmax (mul_nonneg hA hB)
      _ = A*B := mul_one _
  exact le_trans hstep (bw_arith_core n d r hn hd hr1 hr2)

end Work.BW
