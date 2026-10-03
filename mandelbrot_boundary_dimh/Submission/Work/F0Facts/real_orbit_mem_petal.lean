import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Main
import Submission.Work.F0Facts.Petal

namespace Work.F0Facts

open Filter Set Metric Topology
open scoped Topology

noncomputable section

/-! ## The real orbit of `f₀(z) = z + z²`

For `t ∈ [-1/2, 0)` the orbit of `t` stays in `[-1/2, 0)` and, written in the chart
`w = -1/z`, satisfies `w_{n+1} ≥ w_n + 1`; hence `w_N > M` for large `N`, i.e.
`u_N = -1/w_N ∈ (-1/M, 0)`.  The petal `Petal r M` contains the interval `(-1/M, 0)`
when `0 < r` and `1/r < M`, giving the result. -/

/-- The real orbit of `t` under `x ↦ x + x²`. -/
def rOrbit (t : ℝ) : ℕ → ℝ
  | 0 => t
  | n + 1 => rOrbit t n + rOrbit t n ^ 2

lemma rOrbit_zero (t : ℝ) : rOrbit t 0 = t := rfl

lemma rOrbit_succ (t : ℝ) (n : ℕ) : rOrbit t (n + 1) = rOrbit t n + rOrbit t n ^ 2 := rfl

lemma f0_unfold (z : ℂ) : MandelDim.f0 z = z + z ^ 2 := rfl

/-- The complex orbit of a real point is the complexification of the real orbit. -/
lemma ofReal_rOrbit {t : ℝ} : ∀ n : ℕ,
    (MandelDim.f0^[n] ((t : ℝ) : ℂ)) = ((rOrbit t n : ℝ) : ℂ) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, rOrbit_succ, f0_unfold]
    push_cast
    ring

/-- For `t ∈ [-1/2, 0)` the whole real orbit stays in `[-1/2, 0)`. -/
lemma rOrbit_bounds {t : ℝ} (ht1 : -(1 / 2) ≤ t) (ht2 : t < 0) :
    ∀ n : ℕ, -(1 / 2) ≤ rOrbit t n ∧ rOrbit t n < 0 := by
  intro n
  induction n with
  | zero => exact ⟨ht1, ht2⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [rOrbit_succ]
    refine ⟨by nlinarith [sq_nonneg (rOrbit t n)], ?_⟩
    have h3 : 0 < 1 + rOrbit t n := by linarith
    have h4 : rOrbit t n + rOrbit t n ^ 2 = rOrbit t n * (1 + rOrbit t n) := by ring
    rw [h4]
    exact mul_neg_of_neg_of_pos h2 h3

/-- In the chart `w = -1/u`, one step of the real orbit reads
`w_{n+1} = w_n + 1/(1 + u_n)`. -/
lemma inv_rOrbit_succ {t : ℝ} (ht1 : -(1 / 2) ≤ t) (ht2 : t < 0) (n : ℕ) :
    -1 / rOrbit t (n + 1) = -1 / rOrbit t n + 1 / (1 + rOrbit t n) := by
  have h1 := (rOrbit_bounds ht1 ht2 n).1
  have h2 := (rOrbit_bounds ht1 ht2 n).2
  have hne : rOrbit t n ≠ 0 := by linarith
  have hp : 1 + rOrbit t n ≠ 0 := by linarith
  rw [rOrbit_succ]
  field_simp
  ring

/-- The chart coordinates of the real orbit increase by at least `1` at every step. -/
lemma inv_rOrbit_ge {t : ℝ} (ht1 : -(1 / 2) ≤ t) (ht2 : t < 0) (n : ℕ) :
    -1 / rOrbit t n + 1 ≤ -1 / rOrbit t (n + 1) := by
  rw [inv_rOrbit_succ ht1 ht2 n]
  have h1 := (rOrbit_bounds ht1 ht2 n).1
  have h2 := (rOrbit_bounds ht1 ht2 n).2
  have h3 : 0 < 1 + rOrbit t n := by linarith
  have h4 : 1 ≤ 1 / (1 + rOrbit t n) := one_le_one_div h3 (by linarith)
  linarith

lemma le_inv_rOrbit {t : ℝ} (ht1 : -(1 / 2) ≤ t) (ht2 : t < 0) :
    ∀ n : ℕ, -1 / rOrbit t 0 + n ≤ -1 / rOrbit t n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := inv_rOrbit_ge ht1 ht2 n
    push_cast
    linarith

/-- The orbit of a real point `t ∈ [-1/2, 0)` under `f₀(z) = z + z²` is real, increasing and
converges to `0`, and never hits `0`; in particular it eventually enters the petal `Petal r M`
for `0 < r` and `1/r < M`. -/
theorem real_orbit_mem_petal {r M : ℝ} (hr : 0 < r) (hM : 1 / r < M) {t : ℝ}
    (ht1 : -(1 / 2) ≤ t) (ht2 : t < 0) :
    ∃ N : ℕ, MandelDim.f0^[N] (t : ℂ) ∈ Work.FatouCoord.Petal r M := by
  have hMpos : 0 < M := lt_trans (one_div_pos.mpr hr) hM
  have hrM : 1 / M < r := by
    rw [div_lt_iff₀ hMpos]
    have h := (div_lt_iff₀ hr).mp hM
    linarith
  have hbound := rOrbit_bounds ht1 ht2
  obtain ⟨N, hN⟩ := exists_nat_gt (M - (-1 / rOrbit t 0))
  have hNM : M < -1 / rOrbit t 0 + N := by linarith
  have hwN : M < -1 / rOrbit t N := lt_of_lt_of_le hNM (le_inv_rOrbit ht1 ht2 N)
  have hne : rOrbit t N ≠ 0 := by have := (hbound N).2; linarith
  have hww : (1 : ℝ) / (-1 / rOrbit t N) < 1 / M := one_div_lt_one_div_of_lt hMpos hwN
  have hthis : -rOrbit t N = (1 : ℝ) / (-1 / rOrbit t N) := by field_simp
  have hgt : -(1 / M) < rOrbit t N := by
    have : -rOrbit t N < 1 / M := by rw [hthis]; exact hww
    linarith
  refine ⟨N, ?_⟩
  rw [ofReal_rOrbit]
  exact ofReal_mem_petal (r := r) (M := M) (t := rOrbit t N) hMpos hrM hgt (hbound N).2

end

end Work.F0Facts
