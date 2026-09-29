import Mathlib
import Submission.Work.Haupt.defs

/-! # Holomorphy of the theta series `T3`, `T4`, `T2` on the unit disc

The three series of `Submission.Work.Haupt.defs`

* `T3 x = ∑' n : ℤ, x ^ (n^2)`,
* `T4 x = ∑' n : ℤ, (-1)^n * x ^ (n^2)`,
* `T2 x = ∑' n : ℤ, x ^ (n(n+1))`

are lacunary power series with unit radius of convergence.  We prove that they are
complex differentiable on `Metric.ball 0 1`.

The argument is entirely standard.  All exponents are non-negative, so writing
`x ^ (n^2) = x ^ (n^2).toNat` turns the `ℤ`-indexed series into a series of polynomials;
for `0 ≤ r < 1` the exponent sequences grow at least like `|n|` (resp. like `|n| - 1`), so
the series converges locally uniformly on `ball 0 r` by comparison with the geometric
series `∑ r ^ n.natAbs`.  Weierstrass' theorem
(`Complex.differentiableOn_tsum_of_summable_norm`) then gives differentiability on each
`ball 0 r`, hence on `ball 0 1`.
-/

namespace Work.Haupt

open Complex

noncomputable section

/-! ## Summability of the exponent sequences -/

/-- The two-sided geometric series `∑_{n∈ℤ} r^{|n|}` converges for `0 ≤ r < 1`. -/
lemma cdt_summable_int_natAbs (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => r ^ n.natAbs) := by
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using summable_geometric_of_lt_one hr0 hr1
  · simpa using summable_geometric_of_lt_one hr0 hr1

/-- `|n| ≤ n²` for integers, transported to the `toNat` normalisation of the exponent. -/
lemma cdt_int_natAbs_le_sq (n : ℤ) : n.natAbs ≤ (n ^ 2).toNat := by
  have h : (n.natAbs : ℤ) ≤ ((n ^ 2).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (sq_nonneg n)]
    exact Int.natAbs_le_self_sq n
  exact_mod_cast h

/-- `∑_{n∈ℤ} r^{n²}` converges for `0 ≤ r < 1`. -/
lemma cdt_summable_int_sq (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => r ^ (n ^ 2).toNat) := by
  refine Summable.of_nonneg_of_le (fun n => pow_nonneg hr0 _) (fun n => ?_)
    (cdt_summable_int_natAbs r hr0 hr1)
  exact pow_le_pow_of_le_one hr0 hr1.le (cdt_int_natAbs_le_sq n)

/-- The shifted two-sided geometric series `∑_{n∈ℤ} r^{|n|-1}` converges for `0 ≤ r < 1`. -/
lemma cdt_summable_int_natAbs_sub_one (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => r ^ (n.natAbs - 1)) := by
  have hshift : Summable (fun n : ℕ => r ^ (n - 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => r ^ (n - 1)) 1).mp
      (by simpa using summable_geometric_of_lt_one hr0 hr1)
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using hshift
  · simpa using hshift

/-- `|n| - 1 ≤ n(n+1)` for every integer `n`, in the `toNat` normalisation of the exponent. -/
lemma cdt_int_natAbs_sub_one_le_mul_add_one (n : ℤ) :
    n.natAbs - 1 ≤ (n * (n + 1)).toNat := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n
  · subst hm
    simp only [Int.natAbs_natCast]
    rw [show ((↑m : ℤ) * (↑m + 1)).toNat = m * (m + 1) by
      rw [show ((↑m : ℤ) * (↑m + 1)) = ((m * (m + 1) : ℕ) : ℤ) by push_cast; ring]
      rw [Int.toNat_natCast]]
    exact (Nat.sub_le m 1).trans (Nat.le_mul_of_pos_right m (Nat.succ_pos m))
  · subst hm
    rcases m with _ | k
    · simp
    · rw [show (-((k + 1 : ℕ) : ℤ)) * (-((k + 1 : ℕ) : ℤ) + 1) = ((k + 1) * k : ℕ) by
        push_cast; ring]
      rw [Int.toNat_natCast]
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      rw [Nat.add_sub_cancel]
      exact Nat.le_mul_of_pos_left k (Nat.succ_pos k)

/-- `∑_{n∈ℤ} r^{n(n+1)}` converges for `0 ≤ r < 1`. -/
lemma cdt_summable_int_mul_add_one (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => r ^ (n * (n + 1)).toNat) := by
  refine Summable.of_nonneg_of_le (fun n => pow_nonneg hr0 _) (fun n => ?_)
    (cdt_summable_int_natAbs_sub_one r hr0 hr1)
  exact pow_le_pow_of_le_one hr0 hr1.le (cdt_int_natAbs_sub_one_le_mul_add_one n)

/-! ## A Weierstrass-type differentiability criterion -/

/-- If `‖c n‖ ≤ 1` and the exponent sequence `k` is dominated by geometric bounds, then
`w ↦ ∑' n : ℤ, c n * w ^ k n` is complex differentiable on the unit disc.

The bound `‖c n * w ^ k n‖ ≤ ρ ^ k n` is uniform on the smaller disc `ball 0 ρ`,
`‖x‖ < ρ < 1`, where `∑ ρ ^ k n` converges by hypothesis; Weierstrass' theorem
(`Complex.differentiableOn_tsum_of_summable_norm`) applies there, and differentiability at
`x` follows. -/
lemma cdt_differentiableAt_tsum_int (c : ℤ → ℂ) (k : ℤ → ℕ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hk : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable (fun n : ℤ => r ^ k n))
    (x : ℂ) (hx : ‖x‖ < 1) :
    DifferentiableAt ℂ (fun w : ℂ => ∑' n : ℤ, c n * w ^ k n) x := by
  obtain ⟨ρ, hxρ, hρ1, hρ0⟩ : ∃ ρ : ℝ, ‖x‖ < ρ ∧ ρ < 1 ∧ 0 ≤ ρ :=
    ⟨(‖x‖ + 1) / 2, by linarith, by linarith, by linarith [norm_nonneg x]⟩
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have hmem : x ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hxρ
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℤ, c n * w ^ k n)
      (Metric.ball (0 : ℂ) ρ) :=
    Complex.differentiableOn_tsum_of_summable_norm (u := fun n : ℤ => ρ ^ k n)
      (hk ρ hρ0 hρ1)
      (fun n => (differentiableOn_const (c := c n)).mul (differentiableOn_id.pow (k n)))
      Metric.isOpen_ball
      (fun n w hw => by
        have hwρ : ‖w‖ ≤ ρ := by
          have h := Metric.mem_ball.mp hw
          rw [dist_eq_norm, sub_zero] at h
          exact h.le
        rw [norm_mul, norm_pow]
        calc ‖c n‖ * ‖w‖ ^ k n ≤ 1 * ρ ^ k n :=
              mul_le_mul (hc n) (pow_le_pow_left₀ (norm_nonneg w) hwρ (k n))
                (pow_nonneg (norm_nonneg w) _) (by norm_num)
          _ = ρ ^ k n := one_mul _)
  exact hdiff.differentiableAt (hU.mem_nhds hmem)

/-! ## The three theta series -/

/-- The exponent rewriting `x ^ (n^2) = x ^ (n^2).toNat`, using `n^2 ≥ 0`. -/
lemma cdt_pow_sq_eq (w : ℂ) (n : ℤ) : w ^ (n ^ 2) = w ^ (n ^ 2).toNat := by
  have h1 : ((n ^ 2).toNat : ℤ) = n ^ 2 := Int.toNat_of_nonneg (sq_nonneg n)
  conv_lhs => rw [← h1]
  rw [zpow_natCast]

/-- The exponent rewriting `x ^ (n(n+1)) = x ^ (n(n+1)).toNat`. -/
lemma cdt_pow_mul_add_one_eq (w : ℂ) (n : ℤ) :
    w ^ (n * (n + 1)) = w ^ (n * (n + 1)).toNat := by
  have hn : 0 ≤ n * (n + 1) := by
    rcases lt_or_ge n 0 with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg h (by omega)
  have h1 : ((n * (n + 1)).toNat : ℤ) = n * (n + 1) := Int.toNat_of_nonneg hn
  conv_lhs => rw [← h1]
  rw [zpow_natCast]

theorem differentiableOn_T3 : DifferentiableOn ℂ T3 (Metric.ball 0 1) := by
  have hEq : T3 = fun w : ℂ => ∑' n : ℤ, (1 : ℂ) * w ^ (n ^ 2).toNat := by
    funext w
    rw [T3]
    exact tsum_congr fun n => by rw [one_mul, cdt_pow_sq_eq]
  rw [hEq]
  intro x hx
  have hx' : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  exact (cdt_differentiableAt_tsum_int (fun _ => 1) (fun n : ℤ => (n ^ 2).toNat)
    (fun n => by simp) cdt_summable_int_sq x hx').differentiableWithinAt

theorem differentiableOn_T4 : DifferentiableOn ℂ T4 (Metric.ball 0 1) := by
  have hEq : T4 = fun w : ℂ => ∑' n : ℤ, (-1 : ℂ) ^ n * w ^ (n ^ 2).toNat := by
    funext w
    rw [T4]
    exact tsum_congr fun n => by rw [cdt_pow_sq_eq]
  rw [hEq]
  intro x hx
  have hx' : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  exact (cdt_differentiableAt_tsum_int (fun n : ℤ => (-1 : ℂ) ^ n) (fun n : ℤ => (n ^ 2).toNat)
    (fun n => by simp) cdt_summable_int_sq x hx').differentiableWithinAt

theorem differentiableOn_T2 : DifferentiableOn ℂ T2 (Metric.ball 0 1) := by
  have hEq : T2 = fun w : ℂ => ∑' n : ℤ, (1 : ℂ) * w ^ (n * (n + 1)).toNat := by
    funext w
    rw [T2]
    exact tsum_congr fun n => by rw [one_mul, cdt_pow_mul_add_one_eq]
  rw [hEq]
  intro x hx
  have hx' : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  exact (cdt_differentiableAt_tsum_int (fun _ => 1) (fun n : ℤ => (n * (n + 1)).toNat)
    (fun n => by simp) cdt_summable_int_mul_add_one x hx').differentiableWithinAt

theorem theta_differentiable :
    DifferentiableOn ℂ T3 (Metric.ball 0 1) ∧ DifferentiableOn ℂ T4 (Metric.ball 0 1) ∧
    DifferentiableOn ℂ T2 (Metric.ball 0 1) :=
  ⟨differentiableOn_T3, differentiableOn_T4, differentiableOn_T2⟩

end

end Work.Haupt
