import Mathlib

/-!
# Two elementary lemmas from the Introduction of Calegari–Dimitrov–Tang

* **Lemma `simple`** (with the sharper hypothesis `q_n·|β - p_n/q_n| → 0` noted by the authors): if
  `β ∈ ℝ` admits rational approximations `p_n/q_n ≠ β` with `q_n > 0` and
  `q_n·|β - p_n/q_n| → 0`, then `β` is irrational.

* **Lemma `simpletwo`**: a power series `∑ f_n z^n` with *integer* coefficients that converges on a
  disc of radius `> 1` is a polynomial.  We prove the sharper statement that convergence at a
  *single* point `z` with `‖z‖ > 1` already forces `f_n = 0` for all large `n` (because then
  `‖f_n‖·‖z‖^n → 0`, so `‖f_n‖ < 1` for large `n`, and `f_n ∈ ℤ`).

These are the two elementary inputs of the paper's motivational discussion of the Apéry/Beukers
irrationality proofs (§"Comparisons to the work of Apéry").
-/

namespace Submission.CDT.BorelSimple

open Filter
open scoped Topology

/-- **Lemma `simple` of the Introduction.**  Let `β : ℝ` and let `p n / q n` (`q n > 0`) be rational
approximations of `β`, all distinct from `β`, with `q n · |β - p n / q n| → 0`.  Then `β` is
irrational. -/
theorem irrational_of_mul_abs_sub_tendsto_zero {β : ℝ} {p q : ℕ → ℤ}
    (hq : ∀ n, 0 < q n) (hne : ∀ n, (p n : ℝ) / (q n : ℝ) ≠ β)
    (h : Tendsto (fun n => (q n : ℝ) * |β - (p n : ℝ) / (q n : ℝ)|) atTop (nhds 0)) :
    Irrational β := by
  intro hβ
  obtain ⟨r, hr⟩ := hβ
  rw [← hr] at h hne
  have hden : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hcast : ∀ n, (r : ℝ) - (p n : ℝ) / (q n : ℝ)
      = ((r.num * q n - p n * (r.den : ℤ) : ℤ) : ℝ) / ((r.den : ℝ) * (q n : ℝ)) := by
    intro n
    have hqne : (q n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hq n)
    have hdne' : ((r.den : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hlow : ∀ n, 1 / (r.den : ℝ) ≤ (q n : ℝ) * |(r : ℝ) - (p n : ℝ) / (q n : ℝ)| := by
    intro n
    have hqpos : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hq n
    have hqne : (q n : ℝ) ≠ 0 := ne_of_gt hqpos
    have hdne : ((r.den : ℕ) : ℝ) ≠ 0 := ne_of_gt hden
    have hnum : r.num * q n - p n * (r.den : ℤ) ≠ 0 := by
      intro h0
      apply hne n
      have hqne' : (q n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hq n)
      have hdne'' : ((r.den : ℕ) : ℝ) ≠ 0 := by positivity
      have hz : (r : ℝ) - (p n : ℝ) / (q n : ℝ) = 0 := by
        rw [hcast n, show ((r.num * q n - p n * (r.den : ℤ) : ℤ) : ℝ) = 0 from by
          rw [h0]; norm_num]
        simp
      have hEq : (r : ℝ) = (p n : ℝ) / (q n : ℝ) := by linarith
      exact hEq.symm
    have hge1 : (1 : ℝ) ≤ |((r.num * q n - p n * (r.den : ℤ) : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hnum
    have hkey : (q n : ℝ) * |(r : ℝ) - (p n : ℝ) / (q n : ℝ)|
        = |((r.num * q n - p n * (r.den : ℤ) : ℤ) : ℝ)| / (r.den : ℝ) := by
      rw [hcast n, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (r.den : ℝ) * (q n : ℝ))]
      field_simp
    rw [hkey]
    gcongr
  have hnot : ¬ Tendsto (fun n => (q n : ℝ) * |(r : ℝ) - (p n : ℝ) / (q n : ℝ)|) atTop
      (nhds 0) := by
    intro hc
    have hev1 : ∀ᶠ n in atTop,
        1 / (r.den : ℝ) ≤ (q n : ℝ) * |(r : ℝ) - (p n : ℝ) / (q n : ℝ)| :=
      Eventually.of_forall hlow
    have hev2 : ∀ᶠ n in atTop,
        (q n : ℝ) * |(r : ℝ) - (p n : ℝ) / (q n : ℝ)| < (1 / (r.den : ℝ)) / 2 :=
      hc.eventually (eventually_lt_nhds (by positivity))
    have hpos : (0 : ℝ) < 1 / (r.den : ℝ) := by positivity
    obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
    linarith
  exact hnot h

/-- **Lemma `simpletwo` of the Introduction.**  If a power series with integer coefficients
converges at a point `z` with `‖z‖ > 1`, then it is a polynomial (all coefficients vanish
eventually); in particular an integer power series defining a holomorphic function on a disc of
radius `> 1` is a polynomial. -/
theorem int_coeff_eventually_zero_of_summable {f : ℕ → ℤ} {z : ℂ} (hz : 1 < ‖z‖)
    (h : Summable fun n => (f n : ℂ) * z ^ n) : ∃ N, ∀ n ≥ N, f n = 0 := by
  have htend : Tendsto (fun n => ‖(f n : ℂ) * z ^ n‖) atTop (nhds 0) := by
    have h0 := h.tendsto_atTop_zero
    simpa using h0.norm
  have hev : ∀ᶠ n in atTop, ‖(f n : ℂ) * z ^ n‖ < 1 :=
    (tendsto_order.1 htend).2 1 zero_lt_one
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  have h1 : |(f n : ℝ)| * ‖z‖ ^ n < 1 := by
    have h0 : ‖(f n : ℂ) * z ^ n‖ < 1 := hN n hn
    simpa only [norm_mul, norm_pow, Complex.norm_intCast, Real.norm_eq_abs] using h0
  by_contra hf
  have hzn : (1 : ℝ) ≤ ‖z‖ ^ n := one_le_pow₀ hz.le
  have habs : (1 : ℝ) ≤ |((f n : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hf
  have hnn : (0 : ℝ) ≤ |(f n : ℝ)| := abs_nonneg _
  nlinarith [h1, hzn, habs, hnn]

end Submission.CDT.BorelSimple
