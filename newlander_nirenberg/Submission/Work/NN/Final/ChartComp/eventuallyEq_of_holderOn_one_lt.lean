import Mathlib

namespace Work.NN.Final.ChartComp

open Filter

/-- **Hölder continuity with exponent `> 1` forces constancy on each convex piece.**

If `f : X → ℂ` satisfies `‖f a - f b‖ ≤ M * ‖a - b‖ ^ α` for all `a, b` in a convex
set `s`, with `1 < α`, then `f` is constant on `s`. This is the classical fact that a
map subdividing the segment `[a, b]` into `n` equal parts gains a factor `n ^ (1 - α)`,
which tends to `0`. It does not require completeness of `X`. -/
lemma eq_of_convex_holder {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s : Set X} (hs : Convex ℝ s) {f : X → ℂ} {M α : ℝ} (hα : 1 < α)
    (h : ∀ a ∈ s, ∀ b ∈ s, ‖f a - f b‖ ≤ M * ‖a - b‖ ^ α) :
    ∀ a ∈ s, ∀ b ∈ s, f a = f b := by
  intro a ha b hb
  set D := ‖b - a‖ with hDdef
  -- Subdivide the segment from `a` to `b` into `n` equal pieces.
  have key : ∀ n : ℕ, 1 ≤ n → ‖f b - f a‖ ≤ M * (n : ℝ) * (D / (n : ℝ)) ^ α := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    set p : ℕ → X := fun k => a + ((k : ℝ) / (n : ℝ)) • (b - a) with hpdef
    have hp0 : p 0 = a := by simp [p]
    have hpn : p n = b := by
      simp only [p]
      rw [div_self (ne_of_gt hnpos), one_smul, add_sub_cancel]
    have hmem : ∀ k : ℕ, k ≤ n → p k ∈ s := by
      intro k hk
      have ht0 : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := div_nonneg (Nat.cast_nonneg _) hnpos.le
      have ht1 : (k : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hnpos).mpr (by exact_mod_cast hk)
      exact (hs ha).add_smul_sub_mem hb ht0 ht1
    have hpk : ∀ k : ℕ, p (k + 1) - p k = (1 / (n : ℝ)) • (b - a) := by
      intro k
      have hcoef : ((k : ℝ) + 1) / (n : ℝ) - (k : ℝ) / (n : ℝ) = 1 / (n : ℝ) := by
        field_simp
        ring
      simp only [p, Nat.cast_add, Nat.cast_one]
      rw [add_sub_add_left_eq_sub, ← sub_smul, hcoef]
    have hnorm : ∀ k : ℕ, ‖p (k + 1) - p k‖ = D / (n : ℝ) := by
      intro k
      rw [hpk k, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg zero_le_one hnpos.le), hDdef]
      ring
    have htel : f b - f a = ∑ k ∈ Finset.range n, (f (p (k + 1)) - f (p k)) := by
      rw [Finset.sum_range_sub (fun k => f (p k)), hpn, hp0]
    calc ‖f b - f a‖
        = ‖∑ k ∈ Finset.range n, (f (p (k + 1)) - f (p k))‖ := by rw [htel]
      _ ≤ ∑ k ∈ Finset.range n, ‖f (p (k + 1)) - f (p k)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range n, M * (D / (n : ℝ)) ^ α := by
            apply Finset.sum_le_sum
            intro k hk
            have hk' : k < n := Finset.mem_range.mp hk
            rw [← hnorm k]
            exact h (p (k + 1)) (hmem (k + 1) (by omega)) (p k) (hmem k hk'.le)
      _ = M * (n : ℝ) * (D / (n : ℝ)) ^ α := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
  -- Rewrite the right-hand side in the form `M * D ^ α * n ^ (1 - α)`, which tends to `0`.
  have hconv : ∀ n : ℕ, 1 ≤ n →
      M * (n : ℝ) * (D / (n : ℝ)) ^ α = M * D ^ α * (n : ℝ) ^ (1 - α) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hDnonneg : 0 ≤ D := by rw [hDdef]; exact norm_nonneg _
    rw [Real.div_rpow hDnonneg hnpos.le, Real.rpow_sub hnpos, Real.rpow_one]
    ring
  have hbound : ∀ᶠ n : ℕ in atTop, ‖f b - f a‖ ≤ M * D ^ α * (n : ℝ) ^ (1 - α) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [← hconv n hn]
    exact key n hn
  have htend : Tendsto (fun n : ℕ => M * D ^ α * (n : ℝ) ^ (1 - α)) atTop (nhds 0) := by
    have h1 : (0 : ℝ) < α - 1 := by linarith
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - α)) atTop (nhds 0) := by
      have h3 : Tendsto (fun x : ℝ => x ^ (-(α - 1))) atTop (nhds 0) := tendsto_rpow_neg_atTop h1
      have heq : (fun x : ℝ => x ^ (-(α - 1))) = fun x : ℝ => x ^ (1 - α) := by
        funext x; congr 1; ring
      rw [heq] at h3
      exact h3.comp tendsto_natCast_atTop_atTop
    simpa using h2.const_mul (M * D ^ α)
  have hle0 : ‖f b - f a‖ ≤ 0 := ge_of_tendsto htend hbound
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp hle0)).symm

/-- **Hölder continuity with exponent `> 1` implies local constancy.**

`u` satisfies a Hölder estimate of order `α > 1` on an open set `t`; then `u` is
locally constant on `t`. The set `t` being open, it contains a ball around each of its
points, and the ball is convex, so `eq_of_convex_holder` applies. -/
theorem eventuallyEq_of_holderOn_one_lt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {t : Set X} (ht : IsOpen t) {u : X → ℂ} {M α : ℝ} (hα : 1 < α) (hM : 0 ≤ M)
    (h : ∀ x ∈ t, ∀ y ∈ t, ‖u x - u y‖ ≤ M * ‖x - y‖ ^ α) :
    ∀ x ∈ t, ∀ᶠ y in nhds x, u y = u x := by
  have _ := hM
  intro x hx
  rcases (Metric.isOpen_iff.mp ht) x hx with ⟨r, hr, hsub⟩
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  exact eq_of_convex_holder (convex_ball x r) hα
    (fun a ha b hb => h a (hsub ha) b (hsub hb)) y hy x (Metric.mem_ball_self hr)

end Work.NN.Final.ChartComp
