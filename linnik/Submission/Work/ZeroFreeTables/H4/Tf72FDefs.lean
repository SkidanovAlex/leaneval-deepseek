/-
# ZeroFreeTables — `tf72f (3/4)` on its support, as an explicit polynomial

HB Lemma 7.2's test function at `λ = 3/4` is supported on `[0, 8/3]`, where it equals
the quintic

  `hP t = (λ/30)(2-λt)³(4+6λt+λ²t²) = 4/5 - (9/16)t² + (27/128)t³ - (243/40960)t⁵`.

`hM j` is the closed form of the `j`-th moment `∫_0^{8/3} t^j hP t`.  These are the
vocabulary of the numerical upper bound `F(-λ₁) ≤ 1147/1000` for `λ₁ ∈ [0, 87/250]`
(`Work.ZeroFreeTables.H4.Tf72FNegLamLe`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

open MeasureTheory intervalIntegral Finset
noncomputable section

namespace Work.ZeroFreeTables.H4

/-- On `[0, 8/3]`, HB Lemma 7.2's test function with `λ = 3/4` equals this quintic:
the expansion of `(λ/30)(2-λt)³(4+6λt+λ²t²)` at `λ = 3/4`. -/
def hP (t : ℝ) : ℝ := 4/5 - (9/16)*t^2 + (27/128)*t^3 - (243/40960)*t^5

/-- The `j`-th moment `∫_0^{8/3} t^j · hP t`, in closed form. -/
def hM (j : ℕ) : ℝ :=
  (4/5)*(8/3)^(j+1)/(j+1) - (9/16)*(8/3)^(j+3)/(j+3)
    + (27/128)*(8/3)^(j+4)/(j+4) - (243/40960)*(8/3)^(j+6)/(j+6)

/-- `hP` in the factored form of HB Lemma 7.2 (`λ = 3/4`). -/
lemma hP_factored (t : ℝ) :
    hP t = (3/4/30)*(2-(3/4)*t)^3*(4+6*(3/4)*t+(3/4)^2*t^2) := by
  unfold hP; ring

/-- `hP` is non-negative on the support `[0, 8/3]`. -/
lemma hP_nonneg (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 8/3) : 0 ≤ hP t := by
  rw [hP_factored]
  have h2 : 0 ≤ 2 - (3/4)*t := by linarith
  have h3 : 0 ≤ 4 + 6*(3/4)*t + (3/4)^2*t^2 := by nlinarith [h0, sq_nonneg ((3/4)*t)]
  exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h2 3)) h3

/-- On its support, `tf72f (3/4)` is the polynomial `hP`. -/
lemma tf72f34_eq (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (8/3)) :
    Work.ZeroFreeTables.tf72f (3/4) t = hP t := by
  rw [hP_factored]
  exact Work.ZeroFreeTables.tf72f_eq_poly (3/4) (by norm_num) t (by
    have h : (2:ℝ)/(3/4) = 8/3 := by norm_num
    simpa [h] using ht)

end Work.ZeroFreeTables.H4
