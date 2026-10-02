import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

/-- Auxiliary inequality (weighted AM–GM): for `0 < s ≤ 1` and `0 < q ≤ 1`,
`q * (1 - s) ≤ s ^ (-q) - 1`. -/
private lemma rpowSumBound_key (s q : ℝ) (hs0 : 0 < s) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    q * (1 - s) ≤ s ^ (-q) - 1 := by
  -- Weighted AM–GM with weights `q` and `1 - q` gives `s ^ q ≤ q * s + (1 - q)`,
  -- i.e. `1 - s ^ q ≥ q * (1 - s)`.
  have hamgm : s ^ q ≤ q * s + (1 - q) := by
    have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := q) (w₂ := 1 - q) (p₁ := s) (p₂ := 1)
      (le_of_lt hq0) (by linarith) (le_of_lt hs0) (by norm_num) (by ring)
    simpa using h
  -- And for `t = s ^ q ∈ (0,1]` one has `1 - t ≤ 1/t - 1`, i.e. `1 - s ^ q ≤ s ^ (-q) - 1`.
  have ht0 : 0 < s ^ q := Real.rpow_pos_of_pos hs0 q
  have h2 : 1 - s ^ q ≤ s ^ (-q) - 1 := by
    rw [Real.rpow_neg hs0.le, inv_eq_one_div]
    have : 2 - s ^ q ≤ 1 / s ^ q := by
      rw [le_div_iff₀ ht0]
      nlinarith [sq_nonneg (1 - s ^ q)]
    linarith
  linarith

/-- One telescoping step: for `0 < A < B`, `0 < q ≤ 1`,
`B ^ (-(q+1)) ≤ (A ^ (-q) - B ^ (-q)) / (q * (B - A))`. -/
private lemma rpowSumBound_step (A B q : ℝ) (hA : 0 < A) (hAB : A < B) (hq0 : 0 < q)
    (hq1 : q ≤ 1) :
    B ^ (-(q + 1)) ≤ (A ^ (-q) - B ^ (-q)) / (q * (B - A)) := by
  have hB : 0 < B := lt_trans hA hAB
  have hBA : 0 < B - A := sub_pos.mpr hAB
  have hs0 : 0 < A / B := div_pos hA hB
  have hs1 : A / B ≤ 1 := (div_le_one hB).mpr hAB.le
  have key := rpowSumBound_key (A / B) q hs0 hq0 hq1
  have key' : q * (1 - A / B) ≤ (A / B) ^ (-q) - 1 := by
    rw [show 1 - A / B = 1 - A / B by rfl] at key
    exact key
  have hBq : 0 < B ^ (-q) := Real.rpow_pos_of_pos hB (-q)
  rw [le_div_iff₀ (mul_pos hq0 hBA)]
  have lhs_eq : B ^ (-(q + 1)) * (q * (B - A)) = B ^ (-q) * (q * (1 - A / B)) := by
    have h1 : B ^ (-(q + 1)) = B ^ (-q) * B⁻¹ := by
      rw [show -(q + 1) = -q + -1 by ring, Real.rpow_add hB, Real.rpow_neg_one]
    rw [h1]
    have h2 : B⁻¹ * (B - A) = 1 - A / B := by field_simp
    calc B ^ (-q) * B⁻¹ * (q * (B - A)) = B ^ (-q) * q * (B⁻¹ * (B - A)) := by ring
      _ = B ^ (-q) * (q * (1 - A / B)) := by rw [h2]; ring
  have rhs_eq : A ^ (-q) - B ^ (-q) = B ^ (-q) * ((A / B) ^ (-q) - 1) := by
    rw [Real.div_rpow hA.le hB.le]
    field_simp
  rw [lhs_eq, rhs_eq]
  exact mul_le_mul_of_nonneg_left key' hBq.le

/-- **Telescoping bound for a shifted inverse-power series.**

For `a > 0`, `c > 0` and `0 < q ≤ 1` the series `∑_k (a + c*k)^{-(q+1)}` converges and is bounded
by `a^{-(q+1)} + a^{-q}/(q*c)`.

Proof idea: `u_k = (a + c*k)^{-q}` satisfies, for `k ≥ 1` and with `s = (a+c(k-1))/(a+ck) ∈ (0,1]`,
`(a+ck)^{-(q+1)} ≤ (u_{k-1} - u_k)/(q*c)`, because this is equivalent to `s^{-q} - 1 ≥ q*(1-s)`,
which follows from `s^q ≥ s` (as `q ≤ 1`) and `q ≤ 1`: `(1-s^q)/(1-s) ≥ 1 ≥ q ≥ q*s^q`. Summing
telescopes. -/
theorem rpowSumBound (a c q : ℝ) (ha : 0 < a) (hc : 0 < c) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    Summable (fun k : ℕ => (a + c * k) ^ (-(q + 1))) ∧
    (∑' k : ℕ, (a + c * k) ^ (-(q + 1))) ≤ a ^ (-(q + 1)) + a ^ (-q) / (q * c) := by
  let f : ℕ → ℝ := fun k => (a + c * (k:ℝ)) ^ (-(q+1))
  let g : ℕ → ℝ := fun k => (a + c * (k:ℝ)) ^ (-q)
  set B : ℝ := a ^ (-(q+1)) + a ^ (-q) / (q*c) with hBdef
  have hqcs : 0 < q * c := mul_pos hq0 hc
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hfnn : ∀ k, 0 ≤ f k := by
    intro k; simp only [f]; exact Real.rpow_nonneg (by positivity) _
  -- one telescoping step, in the notation of `f` and `g`
  have hstep : ∀ k : ℕ, f (k+1) ≤ (g k - g (k+1)) / (q*c) := by
    intro k
    have hA : 0 < a + c * (k:ℝ) := by positivity
    have hAB : a + c * (k:ℝ) < a + c * ((k:ℝ) + 1) := by nlinarith
    have hd : a + c * ((k:ℝ)+1) - (a + c * (k:ℝ)) = c := by ring
    have h := rpowSumBound_step (a + c*(k:ℝ)) (a + c*((k:ℝ)+1)) q hA hAB hq0 hq1
    rw [hd] at h
    simpa only [f, g, Nat.cast_add, Nat.cast_one] using h
  -- partial sums are bounded
  have hlev : ∀ N : ℕ, ∑ i ∈ Finset.range (N+1), f i ≤ B := by
    intro N
    have htel : ∑ i ∈ Finset.range N, (g i - g (i+1)) = g 0 - g N := Finset.sum_range_sub' g N
    have hsum1 : ∑ i ∈ Finset.range (N+1), f i = f 0 + ∑ i ∈ Finset.range N, f (i+1) := by
      rw [Finset.sum_range_succ']; ring
    have h2 : ∑ i ∈ Finset.range N, f (i+1) ≤ ∑ i ∈ Finset.range N, (g i - g (i+1))/(q*c) :=
      Finset.sum_le_sum (fun i _ => hstep i)
    have h3 : ∑ i ∈ Finset.range N, (g i - g (i+1))/(q*c) = (g 0 - g N)/(q*c) := by
      rw [← Finset.sum_div, htel]
    have hgN : 0 ≤ g N := by simp only [g]; exact Real.rpow_nonneg (by positivity) _
    have h4 : (g 0 - g N)/(q*c) ≤ g 0/(q*c) :=
      div_le_div_of_nonneg_right (by linarith) hqcs.le
    have hfg : f 0 = a ^ (-(q+1)) ∧ g 0 = a ^ (-q) := by
      constructor <;> simp [f, g]
    rw [hsum1]
    calc f 0 + ∑ i ∈ Finset.range N, f (i+1) ≤ f 0 + (g 0 - g N)/(q*c) := by linarith
      _ ≤ f 0 + g 0/(q*c) := by linarith
      _ = B := by rw [hBdef, hfg.1, hfg.2]
  have hle : ∀ n : ℕ, ∑ i ∈ Finset.range n, f i ≤ B := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simpa using hBnn
    · obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
      exact hlev N
  have hsum : Summable f := summable_of_sum_range_le hfnn hle
  constructor
  · simpa only [f] using hsum
  · have := le_of_tendsto_of_tendsto' (HasSum.tendsto_sum_nat hsum.hasSum) tendsto_const_nhds hle
    rw [hBdef] at this
    simpa only [f] using this

end Work.FatouDeg.Petal
