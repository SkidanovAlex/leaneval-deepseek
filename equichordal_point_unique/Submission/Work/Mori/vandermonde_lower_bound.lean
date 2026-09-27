import Mathlib
import Submission.Work.Mori.Defs

namespace Work.Mori

noncomputable section

/-!
# The Fekete / Vandermonde lower bound

This file proves `Work.Mori.vandermonde_lower_bound`: for `n ≥ 2` the geometric mean of the
pairwise differences `j - i` (`i < j < n`) is at least `n exp (-3)`.

The route is the one described in the statement.

* `prod_Ioi_sub_eq_factorial`: for a fixed `i : Fin n`, the differences `j - i` over `j > i` are
  exactly `1, …, n-1-i`, so their product is `(n-1-i)!`.
* `vandermonde_prod_eq`: consequently `∏_{i<j} (j-i) = ∏_{d<n} d!`.
* `log_factorial_lower`: `k log k - k ≤ log k!` (Stirling).
* `hF_step_real` / `sum_mul_log_lower`: telescoping `t ↦ t²/2 log t - t²/4` bounds
  `Σ_{d=1}^{m} d log d` from below by `m²/2 log m - m²/4 + 1/4`.
* `fekete_numeric_final`: the resulting explicit lower bound is `≥ (n(n-1)/2)(log n - 3)`.
-/

/-- **Stirling lower bound in logarithmic form**, valid for every `k : ℕ`: `k log k - k ≤ log k!`
(both sides vanish for `k = 0`). -/
lemma log_factorial_lower (k : ℕ) :
    (k : ℝ) * Real.log k - (k : ℝ) ≤ Real.log (((k.factorial : ℕ) : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have h := Stirling.le_log_factorial_stirling (n := k) (by omega)
    have h1 : (0 : ℝ) ≤ Real.log (k : ℝ) / 2 :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hk)) (by norm_num)
    have h2 : (0 : ℝ) ≤ Real.log (2 * Real.pi) / 2 :=
      div_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three])) (by norm_num)
    linarith

/-- `∏_{k < m} (k + 1) = m!`, over the reals. -/
lemma prod_range_add_one_cast (m : ℕ) :
    (∏ k ∈ Finset.range m, (((k : ℕ) : ℝ) + 1)) = (((m.factorial : ℕ) : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring

/-- For a fixed `i : Fin n`, the product of the differences `j - i` over `j > i` is
`(n - 1 - i)!`: these differences run over `1, …, n-1-i`. -/
lemma prod_Ioi_sub_eq_factorial (n : ℕ) (i : Fin n) :
    (∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
      = (((n - 1 - (i : ℕ)).factorial : ℕ) : ℝ) := by
  rw [← show (∏ k : Fin (n - 1 - (i : ℕ)), ((k : ℝ) + 1))
      = ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) from by
    refine Finset.prod_bij
      (fun (k : Fin (n - 1 - (i : ℕ))) (_ : k ∈ Finset.univ) =>
        (⟨(i : ℕ) + (k : ℕ) + 1, by have hk := k.isLt; omega⟩ : Fin n)) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Ioi]; exact Fin.lt_def.mpr (by simp)
    · intro k₁ hk₁ k₂ hk₂ heq
      have : (k₁ : ℕ) = (k₂ : ℕ) := by
        have h := congrArg Fin.val heq; simp at h; omega
      exact Fin.ext this
    · intro j hj
      simp only [Finset.mem_Ioi] at hj
      refine ⟨⟨(j : ℕ) - (i : ℕ) - 1, by have h := j.isLt; have hi := i.isLt; omega⟩,
        Finset.mem_univ _, ?_⟩
      ext; simp; omega
    · intro k hk; push_cast; ring]
  exact (Fin.prod_univ_eq_prod_range (fun j : ℕ => ((j : ℝ) + 1)) (n - 1 - (i:ℕ))).trans
    (prod_range_add_one_cast _)

/-- **The Vandermonde product**: `∏_{i<j<n} (j - i) = ∏_{d<n} d!`. -/
lemma vandermonde_prod_eq (n : ℕ) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
      = ∏ d ∈ Finset.range n, (((d.factorial : ℕ) : ℝ)) := by
  have h2 : (∏ i : Fin n, (((n - 1 - (i:ℕ)).factorial : ℕ) : ℝ))
        = ∏ d ∈ Finset.range n, (((d.factorial : ℕ) : ℝ)) := by
    rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => (((n - 1 - k).factorial : ℕ) : ℝ)) n]
    exact Finset.prod_range_reflect (fun k : ℕ => (((k.factorial : ℕ) : ℝ))) n
  calc ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))
      = ∏ i : Fin n, (((n - 1 - (i:ℕ)).factorial : ℕ) : ℝ) := by
        apply Finset.prod_congr rfl
        intro i _
        exact prod_Ioi_sub_eq_factorial n i
    _ = _ := h2

/-- The increments of `t ↦ t²/2 log t - t²/4` are dominated by `x log x` (for `x ≥ 2`). -/
lemma hF_step_real (x : ℝ) (hx : 2 ≤ x) :
    x^2/2 * Real.log x - x^2/4 - ((x-1)^2/2 * Real.log (x-1) - (x-1)^2/4) ≤
      x * Real.log x := by
  have hx1 : (0:ℝ) < x - 1 := by linarith
  have hsplit : Real.log x = Real.log (x-1) + Real.log (x/(x-1)) := by
    rw [← Real.log_mul (ne_of_gt hx1) (by positivity)]
    congr 1
    field_simp
  have hlogle : Real.log (x/(x-1)) ≤ 1/(x-1) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < x/(x-1) by positivity)
    have h2 : x/(x-1) - 1 = 1/(x-1) := by field_simp; ring
    linarith
  have hcoef : (0:ℝ) ≤ x*(x-2) := by nlinarith
  have key : x*(x-2)*Real.log (x/(x-1)) ≤ x*(x-2)*(1/(x-1)) :=
    mul_le_mul_of_nonneg_left hlogle hcoef
  have hlog1 : (0:ℝ) ≤ Real.log (x-1) := Real.log_nonneg (by linarith)
  have hdiv : x*(x-2)*(1/(x-1)) ≤ x - 1 := by
    have h1 : x*(x-2)*(1/(x-1)) = (x*(x-2))/(x-1) := by ring
    rw [h1, div_le_iff₀ hx1]
    nlinarith
  have hmain : x*(x-2)*Real.log x - (x-1)^2*Real.log (x-1) ≤ (2*x-1)/2 := by
    rw [hsplit]
    nlinarith [key, hlog1, hdiv]
  nlinarith [hmain]

/-- `Σ_{d=1}^{m} d log d ≥ m²/2 log m - m²/4 + 1/4` (discrete Euler–Maclaurin). -/
lemma sum_mul_log_lower (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ 2 / 2 * Real.log m - (m : ℝ) ^ 2 / 4 + 1 / 4
      ≤ ∑ d ∈ Finset.Ico 1 (m + 1), (d : ℝ) * Real.log d := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [Finset.sum_Ico_succ_top (le_refl 1), Finset.Ico_self, Finset.sum_empty, zero_add]
    norm_num
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1)]
    push_cast
    have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have h := hF_step_real ((m:ℝ)+1) (by linarith)
    rw [show ((m:ℝ)+1) - 1 = (m:ℝ) from by ring] at h
    linarith [ih, h]

/-- The final numerical estimate: with `m = n - 1 ≥ 1` and `N = n m / 2`,
`(m²/2) log m - m²/4 + 1/4 - N ≥ N (log n - 3)`. -/
lemma fekete_numeric_final (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ 2 / 2 * Real.log m - (m : ℝ) ^ 2 / 4 + 1 / 4 - ((m : ℝ) * ((m : ℝ) + 1) / 2)
      ≥ ((m : ℝ) * ((m : ℝ) + 1) / 2) * (Real.log ((m : ℝ) + 1) - 3) := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hx : (0:ℝ) < (m:ℝ) := by linarith
  have hlog1 : Real.log ((m:ℝ)+1) ≤ Real.log (m:ℝ) + 1/(m:ℝ) := by
    have hsplit : Real.log ((m:ℝ)+1) = Real.log (m:ℝ) + Real.log (((m:ℝ)+1)/(m:ℝ)) := by
      rw [← Real.log_mul (ne_of_gt hx) (by positivity)]
      congr 1
      field_simp
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((m:ℝ)+1)/(m:ℝ) by positivity)
    have h2 : ((m:ℝ)+1)/(m:ℝ) - 1 = 1/(m:ℝ) := by field_simp; ring
    linarith
  have hlogm : Real.log (m:ℝ) ≤ (m:ℝ) - 1 := Real.log_le_sub_one_of_pos hx
  have ha : (0:ℝ) ≤ (m:ℝ)*((m:ℝ)+1)/2 := by positivity
  have hkey : (m:ℝ)*((m:ℝ)+1)/2 * Real.log ((m:ℝ)+1) ≤
      (m:ℝ)*((m:ℝ)+1)/2 * Real.log (m:ℝ) + ((m:ℝ)+1)/2 := by
    have hk1 := mul_le_mul_of_nonneg_left hlog1 ha
    have hk2 : (m:ℝ)*((m:ℝ)+1)/2 * (1/(m:ℝ)) = ((m:ℝ)+1)/2 := by field_simp
    nlinarith [hk1, hk2]
  have hlogm2 : (m:ℝ)/2 * Real.log (m:ℝ) ≤ (m:ℝ)/2 * ((m:ℝ) - 1) := by
    have := mul_le_mul_of_nonneg_left hlogm (show (0:ℝ) ≤ (m:ℝ)/2 by positivity)
    linarith
  nlinarith [hkey, hlogm2]

/-- **Fekete / Vandermonde lower bound.** For `n ≥ 2`, the geometric mean over pairs `i < j` of the
integer distances `j - i` is at least `n * exp (-3)`; equivalently
`(∏_{i<j} (j - i))^{2/(n(n-1))} ≥ n e^{-3}`.

Route: the product of the pairwise differences is `∏_{d = 1}^{n-1} d!` (there are `n - d` pairs at
distance `d`), so its logarithm is `Σ_{d=1}^{n-1}(n-d) log d`; combine
`log d! ≥ d log d - d` (a separate lemma, `Work.Mori.factorial_log_lower_bound`) with the bound
`Σ_{d=1}^{n-1} d log d ≥ ∫_1^{n-1} t log t dt` (or a telescoping version of it) to get
`log V ≥ ((n-1)/n) log (n-1) - (n-1)/(2n) - 1 ≥ log n - 3`.  Any explicit positive lower bound
would do; the constant `exp (-3)` is what the rest of the chapter uses, and it holds with a factor
`> 4` of slack at every `n`. -/
theorem vandermonde_lower_bound {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) * Real.exp (-3) ≤
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  -- the number of pairs
  have hpred : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
    rw [Nat.cast_sub hn1]; norm_num
  have hN : ((n * (n - 1) / 2 : ℕ) : ℝ) = (n:ℝ)*((n:ℝ)-1)/2 := by
    rw [Nat.cast_div (even_iff_two_dvd.mp (Nat.even_mul_pred_self n)) (by norm_num : (2:ℝ) ≠ 0)]
    push_cast
    rw [hpred]
  have hNpos : (0:ℝ) < ((n * (n - 1) / 2 : ℕ) : ℝ) := by rw [hN]; nlinarith
  set V : ℝ := ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) with hVdef
  have hVeq : V = ∏ d ∈ Finset.range n, (((d.factorial : ℕ) : ℝ)) := vandermonde_prod_eq n
  have hVpos : (0:ℝ) < V := by
    rw [hVeq]
    exact Finset.prod_pos (fun d _ => by exact_mod_cast Nat.factorial_pos d)
  have hlogV : Real.log V = ∑ d ∈ Finset.range n, Real.log (((d.factorial : ℕ) : ℝ)) := by
    rw [hVeq, Real.log_prod]
    intro d _
    exact ne_of_gt (by exact_mod_cast Nat.factorial_pos d)
  -- Stirling
  have hb1 : ∑ d ∈ Finset.range n, ((d:ℝ) * Real.log (d:ℝ) - (d:ℝ))
      ≤ ∑ d ∈ Finset.range n, Real.log (((d.factorial : ℕ) : ℝ)) :=
    Finset.sum_le_sum (fun d _ => log_factorial_lower d)
  have hsum_id : ∑ d ∈ Finset.range n, (d : ℝ) = ((n * (n - 1) / 2 : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, Finset.sum_range_id]
  have hsum_log : ∑ d ∈ Finset.range n, ((d:ℝ) * Real.log (d:ℝ))
      = ∑ k ∈ Finset.range (n - 1), (((k:ℝ)+1) * Real.log ((k:ℝ)+1)) := by
    have hn' : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn']
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, Real.log_zero, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  have hsum_eq : ∑ d ∈ Finset.range n, ((d:ℝ) * Real.log (d:ℝ) - (d:ℝ))
      = (∑ k ∈ Finset.range (n - 1), (((k:ℝ)+1) * Real.log ((k:ℝ)+1)))
        - ((n * (n - 1) / 2 : ℕ) : ℝ) := by
    rw [Finset.sum_sub_distrib, hsum_log, hsum_id]
  -- the telescoping bound
  have hb2 : ((n - 1 : ℕ) : ℝ)^2/2 * Real.log (((n-1:ℕ):ℝ)) - ((n-1:ℕ):ℝ)^2/4 + 1/4
      ≤ ∑ k ∈ Finset.range (n - 1), (((k:ℝ)+1) * Real.log ((k:ℝ)+1)) := by
    have h := sum_mul_log_lower (n - 1) (by omega)
    have hIco : (n - 1) + 1 = n := by omega
    rw [hIco] at h
    have hconv : (∑ d ∈ Finset.Ico 1 n, ((d:ℝ) * Real.log (d:ℝ)))
        = ∑ k ∈ Finset.range (n - 1), (((k:ℝ)+1) * Real.log ((k:ℝ)+1)) := by
      rw [Finset.sum_Ico_eq_sum_range (fun d : ℕ => ((d:ℝ) * Real.log (d:ℝ))) 1 n]
      apply Finset.sum_congr rfl
      intro k _
      have h1k : ((1 + k : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
      rw [h1k]
    rw [hconv] at h
    exact h
  -- the final numerical estimate
  have hnum := fekete_numeric_final (n - 1) (by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n:ℝ) := by
    rw [Nat.cast_sub hn1]; norm_num
  have hN2 : ((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) + 1) / 2
      = ((n * (n - 1) / 2 : ℕ) : ℝ) := by
    rw [hpred, hN]; ring
  rw [hN2, hcast] at hnum
  have hlog_lower : Real.log V ≥ ((n * (n - 1) / 2 : ℕ) : ℝ) * (Real.log n - 3) := by
    rw [hlogV]
    linarith [hb1, hsum_eq, hb2, hnum]
  have hstep2 : (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) * Real.log V ≥ Real.log n - 3 := by
    have h := mul_le_mul_of_nonneg_left hlog_lower (show (0:ℝ) ≤ 1 / ((n * (n-1)/2 : ℕ):ℝ) by positivity)
    have hNN : (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) * (((n * (n - 1) / 2 : ℕ) : ℝ) * (Real.log n - 3))
        = Real.log n - 3 := by
      field_simp
    linarith [h, hNN]
  rw [Real.rpow_def_of_pos hVpos]
  have hexp : (n:ℝ) * Real.exp (-3) = Real.exp (Real.log n - 3) := by
    rw [show Real.log n - 3 = Real.log n + (-3) from by ring, Real.exp_add, Real.exp_log hnpos]
  rw [hexp]
  apply Real.exp_le_exp.mpr
  linarith [hstep2]

end

end Work.Mori
