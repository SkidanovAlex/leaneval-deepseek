import Mathlib
import Submission.Work.Analysis.InverseTheory.Basic

set_option autoImplicit false

namespace Work.Analysis.InverseTheory

/-! ## Auxiliary lemmas for the Riemann-sum comparison `riemann_shift`

The proof of `riemann_shift` is purely discrete; the three ingredients are

* `tsum_le_of_forall_range_sum_le` — a partial-sum criterion for `tsum` bounds (for real
  sequences it is not enough to bound the partial sums "up to summability", because Mathlib's
  `tsum` is `0` on non-summable families; the two-case proof handles this);
* `inv_pow_succ_le_two` — the telescoping inequality `x^{-(n+1)} ≤ 2(x^{-n} - (x+1)^{-n})`
  for `x ≥ 1`;
* `sum_range_inv_pow_le` — the resulting bound `∑_{i<m} (K+i)^{-(n+1)} ≤ 2K^{-n}` on partial
  sums, for `K ≥ 1`, `n ≥ 1`.
-/

/-- Monotonicity of the Japanese bracket on the nonnegative half-line. -/
theorem jb_le_jb_of_nonneg {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) : jb s ≤ jb u := by
  rw [jb_le_jb_iff, abs_of_nonneg hs, abs_of_nonneg (hs.trans hsu)]
  exact hsu

/-- **Partial-sum criterion for `tsum` bounds.** If every finite initial sum of `f` is at most
`B`, then so is `∑' i, f i`. -/
theorem tsum_le_of_forall_range_sum_le {f : ℕ → ℝ} {B : ℝ}
    (h : ∀ m : ℕ, ∑ i ∈ Finset.range m, f i ≤ B) : ∑' i, f i ≤ B := by
  by_cases hf : Summable f
  · exact le_of_tendsto' hf.hasSum.tendsto_sum_nat h
  · rw [tsum_eq_zero_of_not_summable hf]
    simpa using h 0

/-- The telescoping inequality `x^{-(n+1)} ≤ 2 (x^{-n} - (x+1)^{-n})` for `x ≥ 1` and `n ≥ 1`.
Writing `a = x⁻¹`, `b = (x+1)⁻¹` (so that `0 ≤ b ≤ a ≤ 1`, `a - b = ab` and `2b ≥ a`), the
content is `a^{n+1} = a·a^n ≤ 2b·a^n ≤ a^n - b^n`. -/
theorem inv_pow_succ_le_two (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 1 ≤ x) :
    (x⁻¹) ^ (n + 1) ≤ 2 * ((x⁻¹) ^ n - ((x + 1)⁻¹) ^ n) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx1 : 0 < x + 1 := by linarith
  set a := x⁻¹ with ha
  set b := (x + 1)⁻¹ with hb
  have ha0 : 0 ≤ a := le_of_lt (inv_pos.mpr hx0)
  have hb0 : 0 ≤ b := le_of_lt (inv_pos.mpr hx1)
  have hab : b ≤ a := by
    rw [ha, hb, inv_le_inv₀ hx1 hx0]
    linarith
  have hkey : a ^ n * b ≤ a ^ n - b ^ n := by
    have hbpow : b ^ n ≤ a ^ (n - 1) * b := by
      have h1 : b ^ (n - 1) ≤ a ^ (n - 1) := pow_le_pow_left₀ hb0 hab (n - 1)
      calc b ^ n = b ^ (n - 1) * b := by
            rw [← pow_succ, Nat.sub_add_cancel hn]
        _ ≤ a ^ (n - 1) * b := mul_le_mul_of_nonneg_right h1 hb0
    have hab_eq : a - b = a * b := by
      rw [ha, hb]
      field_simp
      ring
    have h2 : a ^ n - a ^ (n - 1) * b = a ^ n * b := by
      have hna : a ^ n = a ^ (n - 1) * a := by rw [← pow_succ, Nat.sub_add_cancel hn]
      rw [hna, ← mul_sub, hab_eq]
      ring
    linarith [hbpow]
  have ha2b : a ≤ 2 * b := by
    rw [ha, hb]
    field_simp
    linarith
  calc a ^ (n + 1) = a ^ n * a := pow_succ a n
    _ ≤ a ^ n * (2 * b) := mul_le_mul_of_nonneg_left ha2b (pow_nonneg ha0 n)
    _ = 2 * (a ^ n * b) := by ring
    _ ≤ 2 * (a ^ n - b ^ n) := by linarith

/-- The tail partial sums of the `(n+1)`-st powers of the reciprocals of the integers starting at
`K ≥ 1` are at most `2 K^{-n}`. -/
theorem sum_range_inv_pow_le (n K m : ℕ) (hK : 1 ≤ K) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range m, (((K + i : ℕ) : ℝ)⁻¹) ^ (n + 1)
      ≤ 2 * (((K : ℕ) : ℝ)⁻¹) ^ n := by
  have htel : ∑ i ∈ Finset.range m,
        ((((K + i : ℕ) : ℝ)⁻¹) ^ n - ((((K + i : ℕ) : ℝ) + 1)⁻¹) ^ n)
      = (((K : ℕ) : ℝ)⁻¹) ^ n - ((((K + m : ℕ) : ℝ))⁻¹) ^ n := by
    have h := Finset.sum_range_sub' (fun i : ℕ => (((K + i : ℕ) : ℝ)⁻¹) ^ n) m
    simpa [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using h
  calc ∑ i ∈ Finset.range m, (((K + i : ℕ) : ℝ)⁻¹) ^ (n + 1)
      ≤ ∑ i ∈ Finset.range m,
          2 * ((((K + i : ℕ) : ℝ)⁻¹) ^ n - ((((K + i : ℕ) : ℝ) + 1)⁻¹) ^ n) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hx : (1 : ℝ) ≤ ((K + i : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ K + i by omega)
        have := inv_pow_succ_le_two n hn hx
        simpa [Nat.cast_add, Nat.cast_one, Nat.add_assoc] using this
    _ = 2 * ∑ i ∈ Finset.range m,
          ((((K + i : ℕ) : ℝ)⁻¹) ^ n - ((((K + i : ℕ) : ℝ) + 1)⁻¹) ^ n) := by
        rw [← Finset.mul_sum]
    _ = 2 * ((((K : ℕ) : ℝ)⁻¹) ^ n - ((((K + m : ℕ) : ℝ))⁻¹) ^ n) := by rw [htel]
    _ ≤ 2 * (((K : ℕ) : ℝ)⁻¹) ^ n := by
        have h0 : 0 ≤ ((((K + m : ℕ) : ℝ))⁻¹) ^ n := by positivity
        linarith

/-- Riemann-sum comparison for the Japanese bracket: for `1 ≤ n`, `0 < ε ≤ 1` and `0 ≤ t`,
`ε ∑_{k≥0} ⟨t + εk⟩^{-(n+1)} ≤ 2 ^ 60 · ⟨t⟩^{-n}`.  This is the analytic input that turns the
Poisson-summation approximation of an interval indicator into the `⟨ε(x-a)⟩^{-10}` error terms of
Lemma `calc`.  Route: `⟨·⟩^{-(n+1)}` is decreasing on `[0,∞)`, so the `k ≥ 1` part is at most
`∫_t^∞ ⟨u⟩^{-(n+1)} du ≤ ⟨t⟩^{-n}`, and the `k = 0` term is at most `⟨t⟩^{-n}` since `ε ≤ 1`. -/
theorem riemann_shift (n : ℕ) (hn : 1 ≤ n) {ε t : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    ∑' k : ℕ, ε * jbDecay (n + 1) (t + ε * (k : ℝ)) ≤ (2 : ℝ) ^ 60 * jbDecay n t := by
  set L : ℝ := jb t with hLdef
  have hL1 : 1 ≤ L := one_le_jb t
  have hL0 : 0 < L := jb_pos t
  have htL : t ≤ L := (le_abs_self t).trans (abs_le_jb t)
  set K₀ : ℕ := Nat.ceil (L / ε) with hKdef
  have hKpos : 0 < K₀ := by
    rw [hKdef]
    exact Nat.ceil_pos.mpr (div_pos hL0 hε0)
  have hK1 : 1 ≤ K₀ := hKpos
  have hKlow : L / ε ≤ (K₀ : ℝ) := by
    rw [hKdef]
    exact Nat.le_ceil _
  have hKhigh : (K₀ : ℝ) < L / ε + 1 := by
    rw [hKdef]
    exact Nat.ceil_lt_add_one (div_nonneg hL0.le hε0.le)
  -- `ε K₀ ≤ 2L`, the counting bound for the "small `k`" range
  have hKe : ε * (K₀ : ℝ) ≤ 2 * L := by
    have h1 : ε * (L / ε) = L := by
      field_simp
    have h2 : ε * (K₀ : ℝ) < ε * (L / ε + 1) := mul_lt_mul_of_pos_left hKhigh hε0
    rw [mul_add, mul_one, h1] at h2
    linarith
  -- `L * L^{-(n+1)} = L^{-n}`
  have hLmul : L * (L⁻¹) ^ (n + 1) = (L⁻¹) ^ n := by
    calc L * (L⁻¹) ^ (n + 1) = L * ((L⁻¹) ^ n * L⁻¹) := by rw [pow_succ]
      _ = (L * L⁻¹) * (L⁻¹) ^ n := by ring
      _ = (L⁻¹) ^ n := by rw [mul_inv_cancel₀ hL0.ne', one_mul]
  -- the "small `k`" range: each term is at most `ε L^{-(n+1)}`
  have hA : ∑ k ∈ Finset.range K₀, ε * jbDecay (n + 1) (t + ε * (k : ℝ)) ≤ 2 * jbDecay n t := by
    have hterm : ∀ k : ℕ,
        ε * jbDecay (n + 1) (t + ε * (k : ℝ)) ≤ ε * jbDecay (n + 1) t := by
      intro k
      refine mul_le_mul_of_nonneg_left ?_ hε0.le
      rw [jbDecay, jbDecay]
      refine pow_le_pow_left₀ (jb_inv_nonneg (t + ε * (k : ℝ))) ?_ (n + 1)
      rw [inv_le_inv₀ (jb_pos _) (jb_pos t)]
      exact jb_le_jb_of_nonneg ht (le_add_of_nonneg_right (mul_nonneg hε0.le (Nat.cast_nonneg k)))
    calc ∑ k ∈ Finset.range K₀, ε * jbDecay (n + 1) (t + ε * (k : ℝ))
        ≤ ∑ k ∈ Finset.range K₀, ε * jbDecay (n + 1) t :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = (K₀ : ℝ) * (ε * jbDecay (n + 1) t) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (ε * (K₀ : ℝ)) * jbDecay (n + 1) t := by ring
      _ ≤ (2 * L) * jbDecay (n + 1) t :=
          mul_le_mul_of_nonneg_right hKe (jbDecay_nonneg _ _)
      _ = 2 * jbDecay n t := by
          rw [jbDecay, jbDecay, ← hLdef, mul_assoc, hLmul]
  -- the "large `k`" range: first reduce to the pure power tail `∑ (K₀+i)^{-(n+1)}`
  have hB : ∀ j : ℕ,
      ∑ i ∈ Finset.range j, ε * jbDecay (n + 1) (t + ε * ((K₀ + i : ℕ) : ℝ))
        ≤ 2 * jbDecay n t := by
    intro j
    have hpoint : ∀ i : ℕ,
        ε * jbDecay (n + 1) (t + ε * ((K₀ + i : ℕ) : ℝ))
          ≤ (ε⁻¹) ^ n * ((((K₀ + i : ℕ) : ℝ)⁻¹) ^ (n + 1)) := by
      intro i
      set x : ℝ := ((K₀ + i : ℕ) : ℝ) with hxdef
      have hx1 : 1 ≤ x := by
        rw [hxdef]
        exact_mod_cast (show 1 ≤ K₀ + i by omega)
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      have hu0 : 0 < t + ε * x := by
        have := mul_pos hε0 hx0
        linarith
      have heps : ε * (ε⁻¹) ^ (n + 1) = (ε⁻¹) ^ n := by
        calc ε * (ε⁻¹) ^ (n + 1) = (ε * ε⁻¹) * (ε⁻¹) ^ n := by rw [pow_succ']; ring
          _ = (ε⁻¹) ^ n := by rw [mul_inv_cancel₀ hε0.ne', one_mul]
      have hstep1 : ((jb (t + ε * x))⁻¹) ^ (n + 1) ≤ ((t + ε * x)⁻¹) ^ (n + 1) := by
        refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ (n + 1)
        rw [inv_le_inv₀ (jb_pos _) hu0]
        exact (le_abs_self _).trans (abs_le_jb _)
      have hstep2 : ((t + ε * x)⁻¹) ^ (n + 1) ≤ ((ε * x)⁻¹) ^ (n + 1) := by
        have hle : (t + ε * x)⁻¹ ≤ (ε * x)⁻¹ := by
          rw [inv_le_inv₀ hu0 (mul_pos hε0 hx0)]
          linarith
        exact pow_le_pow_left₀ (by positivity) hle (n + 1)
      calc ε * jbDecay (n + 1) (t + ε * x)
          = ε * ((jb (t + ε * x))⁻¹) ^ (n + 1) := by rw [jbDecay]
        _ ≤ ε * ((ε * x)⁻¹) ^ (n + 1) :=
              mul_le_mul_of_nonneg_left (hstep1.trans hstep2) hε0.le
        _ = ε * ((ε⁻¹) ^ (n + 1) * (x⁻¹) ^ (n + 1)) := by rw [mul_inv, mul_pow]
        _ = (ε⁻¹) ^ n * (x⁻¹) ^ (n + 1) := by rw [← mul_assoc, heps]
    calc ∑ i ∈ Finset.range j, ε * jbDecay (n + 1) (t + ε * ((K₀ + i : ℕ) : ℝ))
        ≤ ∑ i ∈ Finset.range j, (ε⁻¹) ^ n * ((((K₀ + i : ℕ) : ℝ)⁻¹) ^ (n + 1)) :=
          Finset.sum_le_sum fun i _ => hpoint i
      _ = (ε⁻¹) ^ n * ∑ i ∈ Finset.range j, ((((K₀ + i : ℕ) : ℝ)⁻¹) ^ (n + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ (ε⁻¹) ^ n * (2 * (((K₀ : ℕ) : ℝ)⁻¹) ^ n) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_pow_le n K₀ j hK1 hn)
            (pow_nonneg (inv_nonneg.mpr hε0.le) n)
      _ = 2 * ((ε * (K₀ : ℝ))⁻¹) ^ n := by
          rw [mul_inv, mul_pow]
          ring
      _ ≤ 2 * (L⁻¹) ^ n := by
          have hEL : L ≤ ε * (K₀ : ℝ) := by
            have h := mul_le_mul_of_nonneg_left hKlow hε0.le
            rwa [mul_div_cancel₀ L hε0.ne'] at h
          have hinv : (ε * (K₀ : ℝ))⁻¹ ≤ L⁻¹ := by
            rw [inv_le_inv₀ (mul_pos hε0 (by exact_mod_cast hKpos)) hL0]
            exact hEL
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hinv n) (by norm_num)
      _ = 2 * jbDecay n t := by rw [jbDecay, ← hLdef]
  -- assemble
  refine tsum_le_of_forall_range_sum_le (f := fun k : ℕ =>
    ε * jbDecay (n + 1) (t + ε * (k : ℝ))) (B := (2 : ℝ) ^ 60 * jbDecay n t) fun m => ?_
  have hnn : ∀ k : ℕ, 0 ≤ ε * jbDecay (n + 1) (t + ε * (k : ℝ)) :=
    fun k => mul_nonneg hε0.le (jbDecay_nonneg _ _)
  rcases le_or_gt m K₀ with hm | hm
  · calc ∑ k ∈ Finset.range m, ε * jbDecay (n + 1) (t + ε * (k : ℝ))
        ≤ ∑ k ∈ Finset.range K₀, ε * jbDecay (n + 1) (t + ε * (k : ℝ)) :=
          Finset.sum_mono_set_of_nonneg hnn (Finset.range_subset_range.mpr hm)
      _ ≤ 2 * jbDecay n t := hA
      _ ≤ (2 : ℝ) ^ 60 * jbDecay n t := by
          have h4 : (2 : ℝ) ≤ (2 : ℝ) ^ 60 := by norm_num
          exact mul_le_mul_of_nonneg_right h4 (jbDecay_nonneg n t)
  · have hm' : m = K₀ + (m - K₀) := by omega
    rw [hm', Finset.sum_range_add]
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ 60 := by norm_num
    have h4j : (4 : ℝ) * jbDecay n t ≤ (2 : ℝ) ^ 60 * jbDecay n t :=
      mul_le_mul_of_nonneg_right h4 (jbDecay_nonneg n t)
    linarith [hA, hB (m - K₀)]

end Work.Analysis.InverseTheory
