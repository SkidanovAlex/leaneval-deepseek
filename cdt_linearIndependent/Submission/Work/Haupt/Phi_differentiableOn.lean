import Mathlib
import Submission.Work.Haupt.theta_aux
import Submission.Work.Haupt.phi_defs

/-!
# Holomorphy of `Φ x = ∑' n : ℤ, x^{n²} z^n` on `ℂ \ {0}`

For `‖x‖ < 1` the two-sided theta series
`Phi x z = jtpTheta x z = ∑' n : ℤ, x ^ (n^2) * z^n`
converges absolutely for every `z ≠ 0` and is holomorphic on `ℂ \ {0}`.

The proof splits the summand as `x^(n^2) z^n = (x^(n^2)) * z^n` and applies Weierstrass'
theorem (`Complex.differentiableOn_tsum_of_summable_norm`) on a small ball
`Metric.ball z r` around a point `z ≠ 0`, where the sum is dominated by
`u n = ‖x‖^(n^2) * R^(n.natAbs)` with `R ≥ max (‖z‖ + r) (‖z‖ - r)⁻¹`.
The domination `‖w‖ ^ n ≤ R ^ n.natAbs` holds for all `n : ℤ` on that ball, and `u` is summable
by the lacunary estimate `summable_int_pow_sq_mul_natAbs`.
-/

namespace Work.Haupt

open Filter
open scoped Topology BigOperators

noncomputable section

/-! ### Lacunary summability estimates -/

/-- `∑_n a^(n²) R^n` converges for `0 ≤ a < 1` and `0 ≤ R`. -/
lemma summable_nat_pow_sq_mul_pow (a R : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) :
    Summable (fun n : ℕ => a ^ (n ^ 2) * R ^ n) := by
  have htend : Tendsto (fun N : ℕ => a ^ N * R) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => a ^ N * R) atTop (𝓝 (0 * R)) :=
      Filter.Tendsto.mul_const R (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1)
    simpa using h
  have hev : ∀ᶠ N : ℕ in atTop, a ^ N * R < 1 :=
    (tendsto_order.1 htend).2 1 zero_lt_one
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have key : ∀ m : ℕ, N + 1 ≤ m → a ^ (m ^ 2) * R ^ m ≤ a ^ m := by
    intro m hm
    have hNm : N ≤ m := by omega
    have hNR : a ^ N * R ≤ 1 := (hN N le_rfl).le
    have haNR0 : 0 ≤ a ^ N * R := mul_nonneg (pow_nonneg ha0 N) hR
    have hle : N * m ≤ m ^ 2 := by
      calc N * m ≤ m * m := Nat.mul_le_mul_right m hNm
        _ = m ^ 2 := by ring
    have hstep1 : a ^ (m ^ 2) * R ^ m = (a ^ N * R) ^ m * a ^ (m ^ 2 - N * m) := by
      have h2 : (a ^ N * R) ^ m * a ^ (m ^ 2 - N * m)
          = a ^ (N * m + (m ^ 2 - N * m)) * R ^ m := by
        rw [mul_pow, ← pow_mul, pow_add]
        ring
      rw [h2, Nat.add_sub_of_le hle]
    have hsub : m ≤ m ^ 2 - N * m := by
      have h1 : m ^ 2 - N * m = m * (m - N) := by
        rw [Nat.mul_sub_left_distrib, pow_two, mul_comm N m]
      rw [h1]
      calc m = m * 1 := (mul_one m).symm
        _ ≤ m * (m - N) := Nat.mul_le_mul_left m (by omega)
    calc a ^ (m ^ 2) * R ^ m
        = (a ^ N * R) ^ m * a ^ (m ^ 2 - N * m) := hstep1
      _ ≤ 1 ^ m * a ^ m := by
          refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · rw [one_pow]; exact pow_le_one₀ haNR0 hNR
          · exact pow_le_pow_of_le_one ha0 ha1.le hsub
      _ = a ^ m := by rw [one_pow, one_mul]
  refine Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one ha0 ha1) ?_
  rw [Nat.cofinite_eq_atTop]
  refine Filter.eventually_atTop.2 ⟨N + 1, fun m hm => ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  exact key m hm

/-- `∑_{n : ℤ} a^(n²) R^|n|` converges for `0 ≤ a < 1` and `0 ≤ R`. -/
lemma summable_int_pow_sq_mul_natAbs (a R : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) :
    Summable (fun n : ℤ => a ^ (n ^ 2) * R ^ n.natAbs) := by
  have hnat := summable_nat_pow_sq_mul_pow a R ha0 ha1 hR
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine hnat.congr (fun n => ?_)
    show a ^ (n ^ 2) * R ^ n = a ^ (((n : ℤ)) ^ 2) * R ^ ((n : ℤ)).natAbs
    rw [Int.natAbs_natCast,
      show ((n : ℤ)) ^ 2 = ((n ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  · have hshift : Summable (fun k : ℕ => a ^ ((k + 1) ^ 2) * R ^ (k + 1)) :=
      (summable_nat_add_iff 1).2 hnat
    refine hshift.congr (fun k => ?_)
    have hm : (-(↑k + 1) : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]
    show a ^ ((k + 1) ^ 2) * R ^ (k + 1)
        = a ^ (((-(↑k + 1)) : ℤ) ^ 2) * R ^ ((-(↑k + 1) : ℤ)).natAbs
    rw [hm, Int.natAbs_negSucc,
      show (Int.negSucc k) ^ 2 = (((k + 1) ^ 2 : ℕ) : ℤ) by
        rw [Int.negSucc_eq]; push_cast; ring,
      zpow_natCast]

/-! ### Elementary `z`-bounds on a ball -/

/-- On `Metric.ball t₀ r`, `‖w‖` is squeezed between `‖t₀‖ - r` and `‖t₀‖ + r`. -/
lemma norm_bounds_of_mem_ball {t₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.ball t₀ r) :
    ‖t₀‖ - r ≤ ‖w‖ ∧ ‖w‖ ≤ ‖t₀‖ + r := by
  have h : ‖w - t₀‖ < r := by
    have h := Metric.mem_ball.mp hw
    rwa [dist_eq_norm] at h
  constructor
  · have h1 := norm_add_le (t₀ - w) w
    have h2 : (t₀ - w) + w = t₀ := by ring
    rw [h2, norm_sub_rev] at h1
    linarith
  · have h1 := norm_add_le t₀ (w - t₀)
    have h2 : t₀ + (w - t₀) = w := by ring
    rw [h2] at h1
    linarith

/-- `‖w‖ ^ n ≤ R ^ n.natAbs` for every `n : ℤ`, provided `‖w‖ ≤ R` and `‖w‖⁻¹ ≤ R`. -/
lemma zpow_le_pow_natAbs {w : ℂ} {R : ℝ} (h1 : ‖w‖ ≤ R) (h2 : ‖w‖⁻¹ ≤ R)
    (n : ℤ) : ‖w‖ ^ n ≤ R ^ n.natAbs := by
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  rcases le_or_gt 0 n with hn | hn
  · have h1' : ‖w‖ ^ n = ‖w‖ ^ n.toNat := by
      conv_lhs => rw [← Int.toNat_of_nonneg hn]
      exact zpow_natCast ‖w‖ n.toNat
    have h2' : n.natAbs = n.toNat := by
      rw [← Int.natAbs_natCast n.toNat, Int.toNat_of_nonneg hn]
    rw [h1', h2']
    exact pow_le_pow_left₀ hw0 h1 n.toNat
  · have hneg : n = -(((n.natAbs : ℕ)) : ℤ) := by
      have h : (((n.natAbs : ℕ)) : ℤ) = -n := by
        rw [← Int.natAbs_neg n]
        exact Int.natAbs_of_nonneg (by omega)
      omega
    have h1' : ‖w‖ ^ n = (‖w‖⁻¹) ^ n.natAbs := by
      conv_lhs => rw [hneg]
      rw [zpow_neg, zpow_natCast, ← inv_pow]
    rw [h1']
    exact pow_le_pow_left₀ (inv_nonneg.mpr hw0) h2 n.natAbs

/-! ### The main statement -/

theorem Phi_differentiableOn (x : ℂ) (hx : ‖x‖ < 1) :
    DifferentiableOn ℂ (Phi x) {t : ℂ | t ≠ 0} := by
  rw [Phi]
  show DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℤ, x ^ (n ^ 2) * w ^ n) {t : ℂ | t ≠ 0}
  intro t₀ ht₀
  have ht₀pos : 0 < ‖t₀‖ := norm_pos_iff.mpr ht₀
  obtain ⟨r, hr0, hrt⟩ : ∃ r : ℝ, 0 < r ∧ r < ‖t₀‖ :=
    ⟨‖t₀‖ / 2, by positivity, by linarith⟩
  set R : ℝ := max (‖t₀‖ + r) (‖t₀‖ - r)⁻¹ with hRdef
  have hR0 : 0 ≤ R := le_trans (by positivity) (le_max_left _ _)
  have hRM : ‖t₀‖ + r ≤ R := le_max_left _ _
  have hRm : (‖t₀‖ - r)⁻¹ ≤ R := le_max_right _ _
  have hmpos : 0 < ‖t₀‖ - r := by linarith
  have hu : Summable (fun n : ℤ => ‖x‖ ^ (n ^ 2) * R ^ n.natAbs) :=
    summable_int_pow_sq_mul_natAbs ‖x‖ R (norm_nonneg x) hx hR0
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℤ, x ^ (n ^ 2) * w ^ n)
      (Metric.ball t₀ r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (F := fun n : ℤ => fun w : ℂ => x ^ (n ^ 2) * w ^ n) hu ?_ Metric.isOpen_ball ?_
    · intro n
      have hne : ∀ w ∈ Metric.ball t₀ r, w ≠ 0 := by
        intro w hw
        obtain ⟨hw1, _⟩ := norm_bounds_of_mem_ball hw
        exact norm_pos_iff.mp (by linarith)
      have h1 : DifferentiableOn ℂ (fun w : ℂ => w ^ n) (Metric.ball t₀ r) :=
        (differentiableOn_id (𝕜 := ℂ) (s := Metric.ball t₀ r)).zpow (Or.inl hne)
      simpa using h1.const_mul (x ^ (n ^ 2))
    · intro n w hw
      obtain ⟨hw1, hw2⟩ := norm_bounds_of_mem_ball hw
      have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hmpos hw1
      have hwR : ‖w‖ ≤ R := le_trans hw2 hRM
      have hwR' : ‖w‖⁻¹ ≤ R := le_trans (inv_le_inv₀ hwpos hmpos |>.2 hw1) hRm
      have hb : ‖w ^ n‖ ≤ R ^ n.natAbs := by
        rw [norm_zpow]
        exact zpow_le_pow_natAbs hwR hwR' n
      calc ‖x ^ (n ^ 2) * w ^ n‖ = ‖x ^ (n ^ 2)‖ * ‖w ^ n‖ := norm_mul _ _
        _ ≤ ‖x ^ (n ^ 2)‖ * R ^ n.natAbs :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = ‖x‖ ^ (n ^ 2) * R ^ n.natAbs := by rw [norm_zpow]
  exact (hdiff.differentiableAt (Metric.ball_mem_nhds t₀ hr0)).differentiableWithinAt

end

end Work.Haupt
