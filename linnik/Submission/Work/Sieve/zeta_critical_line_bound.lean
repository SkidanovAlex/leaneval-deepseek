import Mathlib.NumberTheory.LSeries.RiemannZeta
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le
import Submission.Work.Sieve.sum_Icc_rpow_neg_half_le
import Submission.Work.Sieve.pole_term_norm_le_half
import Submission.Work.Sieve.half_norm_tail_arith

/-!
# The classical `t^(1/2)` bound for `ζ` on the critical line

We prove: there is an absolute constant `C > 0` with
`‖ζ(1/2 + i t)‖ ≤ C (1 + |t|)^(1/2)` for every real `t`.

The proof uses the Euler–Maclaurin decomposition of `ζ` on the half-plane `re s > 0`
(`Commons.NumberTheory.Zeta.zeta_eq_emN`), applied at `N = ⌊|t|⌋₊ + 1`:

`ζ(s) = ∑_{n ≤ N} n^{-s} + N^{1-s}/(s-1) + ∑'_m emTerm_m(s)`,

together with `Commons.NumberTheory.Zeta.emTerm_tsum_le`, which bounds the norm of the
tail series by `(‖s‖ / re s) · N^{-re s}`. On the critical line `re s = 1/2` this gives

* head:  `‖∑_{n ≤ N} n^{-1/2-it}‖ ≤ 2√(N+1) ≤ 4(1+|t|)^{1/2}`,
* pole:  `‖N^{1/2-it}/(s-1)‖ ≤ 2√N ≤ 2(1+|t|)^{1/2}`,
* tail:  `≤ 2‖s‖N^{-1/2} ≤ 3(1+|t|)^{1/2}`,

using `|t| ≤ N ≤ |t| + 1`, and the three contributions sum to at most `9(1+|t|)^{1/2}`.
-/

namespace Work.Sieve

/-- The critical-line bound with the explicit constant `9`. -/
lemma zeta_critical_line_aux (t : ℝ) :
    ‖riemannZeta ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 9 * (1 + |t|) ^ (1/2 : ℝ) := by
  set s : ℂ := (1/2 : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = 1/2 := by simp [hs]
  have hs0 : 0 < s.re := by rw [hsre]; norm_num
  have hsne : s ≠ 1 := by
    intro h
    have h1 : s.re = 1 := by rw [h]; simp
    rw [hsre] at h1
    norm_num at h1
  set N : ℕ := Nat.floor |t| + 1 with hNdef
  have hN1 : 1 ≤ N := by simp [hNdef]
  have hNt : |t| ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one |t|
    simp only [hNdef]
    push_cast
    linarith
  have hNle : (N : ℝ) ≤ |t| + 1 := by
    have h := Nat.floor_le (abs_nonneg t)
    simp only [hNdef]
    push_cast
    linarith
  obtain ⟨hsum, hbound⟩ := Commons.NumberTheory.Zeta.emTerm_tsum_le N hN1 s hs0 hsne
  set TT : ℂ := ∑' m : ℕ,
      ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
        (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))) with hTdef
  set H : ℂ := ∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)) with hHdef
  set M : ℂ := ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) with hMdef
  have hid : riemannZeta s = H + M + TT := by
    have h := Commons.NumberTheory.Zeta.zeta_eq_emN (s := s) hs0 hsne N hN1
    rw [h]
  have hhead : ‖H‖ ≤ 4 * (1 + |t|) ^ (1/2 : ℝ) := by
    have h1 : ‖H‖ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1/2 : ℝ)) := by
      rw [hHdef]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hbase : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := (Complex.ofReal_natCast n).symm
      have heq : ‖(((n : ℕ) : ℂ) ^ (-s))‖ = (n : ℝ) ^ (-(1/2 : ℝ)) := by
        rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
        rw [show (-s).re = -s.re from Complex.neg_re s, hsre]
      exact le_of_eq heq
    have h2 : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1/2 : ℝ))) ≤ 2 * (((N : ℝ) + 1) ^ (1/2 : ℝ)) :=
      sum_Icc_rpow_neg_half_le N hN1
    have h3 : 2 * (((N : ℝ) + 1) ^ (1/2 : ℝ)) ≤ 4 * (1 + |t|) ^ (1/2 : ℝ) := by
      have hN1pos : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      have hle : (N : ℝ) + 1 ≤ 4 * (1 + |t|) := by
        have habs : (0:ℝ) ≤ |t| := abs_nonneg t
        linarith [hNle]
      have hmono : ((N : ℝ) + 1) ^ (1/2 : ℝ) ≤ (4 * (1 + |t|)) ^ (1/2 : ℝ) :=
        Real.rpow_le_rpow hN1pos hle (by norm_num)
      have h4 : (4:ℝ) ^ (1/2 : ℝ) = 2 := by norm_num
      have hsplit : (4 * (1 + |t|)) ^ (1/2 : ℝ) = 2 * (1 + |t|) ^ (1/2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity : (0:ℝ) ≤ 1 + |t|), h4]
      have hmono' : ((N : ℝ) + 1) ^ (1/2 : ℝ) ≤ 2 * (1 + |t|) ^ (1/2 : ℝ) := by
        rw [← hsplit]; exact hmono
      linarith
    linarith
  have hpole : ‖M‖ ≤ 2 * (1 + |t|) ^ (1/2 : ℝ) := by
    have h1 : ‖M‖ ≤ 2 * ((N : ℝ) ^ (1/2 : ℝ)) := by
      rw [hMdef]
      exact pole_term_norm_le_half hN1 hsre
    have h2 : 2 * ((N : ℝ) ^ (1/2 : ℝ)) ≤ 2 * (1 + |t|) ^ (1/2 : ℝ) := by
      have hNle' : (N : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t, hNle]
      have hm := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (N:ℝ)) hNle' (by norm_num : (0:ℝ) ≤ 1/2)
      linarith
    linarith
  have htail : ‖TT‖ ≤ 3 * (1 + |t|) ^ (1/2 : ℝ) := by
    have h1 : ‖TT‖ ≤ ∑' m : ℕ, ‖(((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
        (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))‖ := by
      rw [hTdef]
      exact norm_tsum_le_tsum_norm hsum.norm
    have h3 : (‖s‖ / s.re) * ((N : ℝ) ^ (-s.re)) ≤ 3 * (1 + |t|) ^ (1/2 : ℝ) := by
      rw [hsre]
      rw [show ‖s‖ = ‖((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ by rw [hs]]
      exact half_norm_tail_arith hN1 hNt
    exact le_trans h1 (le_trans hbound h3)
  rw [hid]
  have htri : ‖H + M + TT‖ ≤ ‖H‖ + ‖M‖ + ‖TT‖ := by
    calc ‖H + M + TT‖ ≤ ‖H + M‖ + ‖TT‖ := norm_add_le _ _
      _ ≤ (‖H‖ + ‖M‖) + ‖TT‖ := by linarith [norm_add_le H M]
  calc ‖H + M + TT‖ ≤ ‖H‖ + ‖M‖ + ‖TT‖ := htri
    _ ≤ 4 * (1 + |t|) ^ (1/2 : ℝ) + 2 * (1 + |t|) ^ (1/2 : ℝ) + 3 * (1 + |t|) ^ (1/2 : ℝ) := by
        linarith [hhead, hpole, htail]
    _ = 9 * (1 + |t|) ^ (1/2 : ℝ) := by ring

theorem zeta_critical_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖riemannZeta ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ (1/2 : ℝ) := by
  refine ⟨10, by norm_num, fun t => ?_⟩
  refine le_trans (zeta_critical_line_aux t) ?_
  have hpos : (0 : ℝ) ≤ (1 + |t|) ^ (1/2 : ℝ) := Real.rpow_nonneg (by positivity) _
  linarith

end Work.Sieve
