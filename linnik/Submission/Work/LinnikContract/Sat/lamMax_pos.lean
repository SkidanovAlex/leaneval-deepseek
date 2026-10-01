import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.Sat

/-- For every real `x ≥ 16` we have `log (log (log x)) > 0`, because
`log 16 = 4 log 2 > e = exp 1` forces `log (log x) > 1`. -/
private lemma log_log_log_pos {x : ℝ} (hx : 16 ≤ x) : 0 < Real.log (Real.log (Real.log x)) := by
  have h16pos : (0 : ℝ) < 16 := by norm_num
  have hxpos : 0 < x := lt_of_lt_of_le h16pos hx
  have hlog16 : Real.exp 1 < Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9, Real.exp_one_lt_d9]
  have hlogx : Real.exp 1 < Real.log x :=
    lt_of_lt_of_le hlog16 ((Real.log_le_log_iff h16pos hxpos).mpr hx)
  have hlogxpos : 0 < Real.log x := lt_trans (Real.exp_pos 1) hlogx
  have h1 : 1 < Real.log (Real.log x) := (Real.lt_log_iff_exp_lt hlogxpos).mpr hlogx
  exact Real.log_pos h1

/-- Non-degeneracy of the working region of AREA 4 (D1): there is a threshold `q₀` such that for
all `q ≥ q₀` the density parameter `lamMax q = (1/3) log log log q` is strictly positive, so the
region `λ(ρ) ≤ lamMax q` is a genuine non-trivial range for all large `q` (this matches the
threshold shape of `DensityCert`, which quantifies over `q ≥ q₀`).

Prover notes: `q₀ = 16` works: `0 < Real.log (Real.log (Real.log q))` follows from
`1 < Real.log (Real.log q)` from `Real.exp_pos`-style bounds, e.g.
`Real.exp 1 < 3`/`Real.exp_one_lt_d9` and `Real.log 16 = 4 log 2 ≥ 4 * 0.693 > 2.7 > e`; then
`Real.log_pos` twice.  No `native_decide`. -/
theorem lamMax_pos : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → 0 < Work.LinnikContract.lamMax q := by
  refine ⟨16, fun q hq => ?_⟩
  have hx : (16 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  unfold Work.LinnikContract.lamMax
  exact div_pos (log_log_log_pos hx) (by norm_num)

end Work.LinnikContract.Sat
