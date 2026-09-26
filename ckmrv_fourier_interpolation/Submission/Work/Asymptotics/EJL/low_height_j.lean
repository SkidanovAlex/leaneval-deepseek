import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Asymptotics.E4Fun_upper_half
import Submission.Work.Asymptotics.EJL.e4_cusp_second_order

/-!
# The second-order cusp expansion of `j` on `Im τ ≥ 1`

`Work.Asymptotics.EJL.low_height_j` states

`‖j τ - q⁻¹ - 744‖ ≤ 10⁷ ‖q‖`  for `1 ≤ τ.im`,

where `q = e^{2πiτ}` and `j = E₄³/Δ` is the modular `j`-invariant.

The proof combines the two explicit cusp expansions

* `E₄ τ = 1 + 240 q + O(q²)`, with constant `2·10⁴` (`e4_cusp_second_order`),
* `Δ τ = q - 24 q² + O(q³)`, with constant `500` (`delta_third_order_bound`),

with the elementary numerator estimate `num_small_estimate`: the numerator
`N = E₄³ - Δ(q⁻¹ + 744)` of `j - q⁻¹ - 744 = N/Δ` is `O(q²)` with constant `4·10⁵`,
while `‖Δ‖ ≥ ‖q‖/2`.  Hence
`‖j - q⁻¹ - 744‖ ≤ ‖N‖/‖Δ‖ ≤ 4·10⁵ ‖q‖² / (‖q‖/2) = 8·10⁵ ‖q‖ ≤ 10⁷ ‖q‖`.
-/

namespace Work.Asymptotics.EJL

open Filter

/-! ## Elementary estimates -/

/-- For a finite set `t` of vectors whose norms have small total, the product
`∏ (1 + a n)` is within `2 ∑ ‖a n‖` of `1`. -/
private lemma norm_prod_one_add_sub_one_le_two {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (a : ι → ℂ) (h : (∑ n ∈ t, ‖a n‖) ≤ 1 / 2) :
    ‖∏ n ∈ t, (1 + a n) - 1‖ ≤ 2 * ∑ n ∈ t, ‖a n‖ := by
  revert h
  refine Finset.induction_on t ?_ ?_
  · intro h; simp
  · intro x s hx ih h
    rw [Finset.sum_insert hx] at h
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    have hs : ∑ n ∈ s, ‖a n‖ ≤ 1 / 2 := by
      have h0 : (0 : ℝ) ≤ ‖a x‖ := norm_nonneg _
      linarith
    have ih' := ih hs
    have hx0 : (0 : ℝ) ≤ ‖a x‖ := norm_nonneg _
    have hs0 : (0 : ℝ) ≤ ∑ n ∈ s, ‖a n‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    have hsplit : (1 + a x) * ∏ n ∈ s, (1 + a n) - 1
        = (1 + a x) * (∏ n ∈ s, (1 + a n) - 1) + a x := by ring
    rw [hsplit]
    have hle1 : ‖1 + a x‖ ≤ 1 + ‖a x‖ := by simpa using norm_add_le (1 : ℂ) (a x)
    have h2 : ‖(1 + a x) * (∏ n ∈ s, (1 + a n) - 1)‖
        ≤ (1 + ‖a x‖) * (2 * ∑ n ∈ s, ‖a n‖) := by
      calc ‖(1 + a x) * (∏ n ∈ s, (1 + a n) - 1)‖
          ≤ ‖1 + a x‖ * ‖∏ n ∈ s, (1 + a n) - 1‖ := norm_mul_le _ _
        _ ≤ (1 + ‖a x‖) * (2 * ∑ n ∈ s, ‖a n‖) :=
            mul_le_mul hle1 ih' (norm_nonneg _) (by positivity)
    calc ‖(1 + a x) * (∏ n ∈ s, (1 + a n) - 1) + a x‖
        ≤ ‖(1 + a x) * (∏ n ∈ s, (1 + a n) - 1)‖ + ‖a x‖ := norm_add_le _ _
      _ ≤ (1 + ‖a x‖) * (2 * ∑ n ∈ s, ‖a n‖) + ‖a x‖ := by linarith
      _ ≤ 2 * (‖a x‖ + ∑ n ∈ s, ‖a n‖) := by
          have hs1 : 2 * ∑ n ∈ s, ‖a n‖ ≤ 1 := by linarith
          nlinarith [hs0, hx0, hs1]

/-- Geometric tail of ratio `r ≤ 1/2`, shifted by two. -/
private lemma geom_range_shift_le (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (M : ℕ) :
    ∑ n ∈ Finset.range M, r ^ (n + 2) ≤ 2 * r ^ 2 := by
  have hr1 : r < 1 := by linarith
  have hsumm : Summable (fun n : ℕ => r ^ (n + 2)) := by
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left (r ^ 2)
    refine h.congr fun n => ?_
    rw [pow_add]; ring
  calc ∑ n ∈ Finset.range M, r ^ (n + 2) ≤ ∑' n : ℕ, r ^ (n + 2) :=
        hsumm.sum_le_tsum _ (fun i _ => by positivity)
    _ = r ^ 2 / (1 - r) := by
        rw [show (fun n : ℕ => r ^ (n + 2)) = (fun n => r ^ 2 * r ^ n) by
              funext n; rw [pow_add]; ring]
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
        ring
    _ ≤ 2 * r ^ 2 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - r)]
        nlinarith [hr0, hr]

/-- `(1 - q)^24 = 1 - 24 q + O(q²)`, with constant `290`. -/
private lemma one_sub_pow24_sub_linear (q : ℂ) (r : ℝ) (hr : r = ‖q‖) (hr512 : r ≤ 1 / 512) :
    ‖(1 - q) ^ 24 - 1 + 24 * q‖ ≤ 290 * r ^ 2 := by
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hnq : ‖1 - q‖ ≤ 1 + r := by
    calc ‖1 - q‖ ≤ ‖(1 : ℂ)‖ + ‖q‖ := norm_sub_le 1 q
      _ = 1 + r := by rw [norm_one, ← hr]
  have hid : (1 - q) ^ 24 - 1 + 24 * q
      = -q * ∑ k ∈ Finset.range 24, ((1 - q) ^ k - 1) := by
    have h := geom_sum_mul (1 - q) 24
    have h2 : (1 - q : ℂ) - 1 = -q := by ring
    rw [h2] at h
    have h3 : ∑ k ∈ Finset.range 24, ((1 - q) ^ k - 1)
        = (∑ k ∈ Finset.range 24, (1 - q) ^ k) - 24 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      norm_num
    rw [h3]
    calc (1 - q) ^ 24 - 1 + 24 * q
        = (∑ k ∈ Finset.range 24, (1 - q) ^ k) * (-q) + 24 * q := by rw [h]
      _ = -q * ((∑ k ∈ Finset.range 24, (1 - q) ^ k) - 24) := by ring
  rw [hid, norm_mul, norm_neg, ← hr]
  have hsum_bound : ‖∑ k ∈ Finset.range 24, ((1 - q) ^ k - 1)‖ ≤ 276 * r * (1 + r) ^ 22 := by
    have hterm : ∀ k ∈ Finset.range 24, ‖(1 - q) ^ k - 1‖ ≤ r * ((k : ℝ) * (1 + r) ^ 22) := by
      intro k hk
      have hk23 : k ≤ 23 := by have h := Finset.mem_range.mp hk; omega
      have hx1 : (1 : ℝ) ≤ 1 + r := by linarith
      by_cases hk0 : k = 0
      · subst hk0
        simp
      · have hg : (1 - q) ^ k - 1 = -q * ∑ j ∈ Finset.range k, (1 - q) ^ j := by
          have h := geom_sum_mul (1 - q) k
          have h2 : (1 - q : ℂ) - 1 = -q := by ring
          rw [h2, mul_comm] at h
          exact h.symm
        rw [hg, norm_mul, norm_neg, ← hr]
        have h1 : ‖∑ j ∈ Finset.range k, (1 - q) ^ j‖ ≤ (k : ℝ) * (1 + r) ^ 22 := by
          calc ‖∑ j ∈ Finset.range k, (1 - q) ^ j‖
              ≤ ∑ j ∈ Finset.range k, ‖(1 - q) ^ j‖ := norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range k, (1 + r) ^ 22 := by
                apply Finset.sum_le_sum
                intro j hj
                have hj22 : j ≤ 22 := by have h := Finset.mem_range.mp hj; omega
                calc ‖(1 - q) ^ j‖ = ‖1 - q‖ ^ j := by rw [norm_pow]
                  _ ≤ (1 + r) ^ j := pow_le_pow_left₀ (norm_nonneg _) hnq j
                  _ ≤ (1 + r) ^ 22 := pow_le_pow_right₀ hx1 hj22
            _ = (k : ℝ) * (1 + r) ^ 22 := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_left h1 hr0
    calc ‖∑ k ∈ Finset.range 24, ((1 - q) ^ k - 1)‖
        ≤ ∑ k ∈ Finset.range 24, ‖(1 - q) ^ k - 1‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range 24, r * ((k : ℝ) * (1 + r) ^ 22) := Finset.sum_le_sum hterm
      _ = 276 * r * (1 + r) ^ 22 := by
          rw [← Finset.mul_sum]
          rw [show (∑ i ∈ Finset.range 24, (i : ℝ) * (1 + r) ^ 22) = 276 * (1 + r) ^ 22 by
                rw [← Finset.sum_mul]; norm_num]
          ring
  have hX : (1 + r) ^ 22 ≤ 1.046 := by
    have h1 : 1 + r ≤ 1 + (1 / 512 : ℝ) := by linarith
    calc (1 + r) ^ 22 ≤ (1 + 1 / 512) ^ 22 := pow_le_pow_left₀ (by positivity) h1 22
      _ ≤ 1.046 := by norm_num
  calc r * ‖∑ k ∈ Finset.range 24, ((1 - q) ^ k - 1)‖ ≤ r * (276 * r * (1 + r) ^ 22) :=
        mul_le_mul_of_nonneg_left hsum_bound hr0
    _ ≤ 290 * r ^ 2 := by nlinarith [hX, hr0, sq_nonneg r]

/-- The infinite product `P = ∏'ₙ (1 - ηₙ)` (with `ηₙ = q^{n+1}`) satisfies
`‖P - (1 - q)‖ ≤ 5 ‖q‖²`. -/
private lemma tprod_eta_close (τ : UpperHalfPlane) (q : ℂ) (r : ℝ)
    (hqper : Function.Periodic.qParam 1 (τ : ℂ) = q) (hr : r = ‖q‖) (hr512 : r ≤ 1 / 512) :
    ‖(∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) - (1 - q)‖ ≤ 5 * r ^ 2 := by
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 / 2 := by linarith
  have hq_lt : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by rw [hqper]; linarith
  have hmul : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ)) :=
    ModularForm.multipliable_one_sub_pow hq_lt
  have heta : ∀ n : ℕ, ModularForm.eta_q n (τ : ℂ) = q ^ (n + 1) := by
    intro n
    rw [ModularForm.eta_q, hqper]
  have hnq : ‖1 - q‖ ≤ 1 + r := by
    calc ‖1 - q‖ ≤ ‖(1 : ℂ)‖ + ‖q‖ := norm_sub_le 1 q
      _ = 1 + r := by rw [norm_one, hr]
  have hbd : ∀ N : ℕ, 1 ≤ N →
      ‖∏ k ∈ Finset.range N, (1 - ModularForm.eta_q k (τ : ℂ)) - (1 - q)‖ ≤ 5 * r ^ 2 := by
    intro N hN
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [Finset.prod_range_succ']
    have hfac : ∏ k ∈ Finset.range M, (1 - ModularForm.eta_q (k + 1) (τ : ℂ))
        = ∏ k ∈ Finset.range M, (1 + -(q ^ (k + 2))) := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [heta (k + 1)]
      have : k + 1 + 1 = k + 2 := by omega
      rw [this]
      ring
    have h0 : ModularForm.eta_q 0 (τ : ℂ) = q := by rw [heta 0]; simp
    rw [hfac, h0]
    have hsum1 : ∑ k ∈ Finset.range M, ‖(-(q ^ (k + 2)) : ℂ)‖
        = ∑ k ∈ Finset.range M, r ^ (k + 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_neg, norm_pow, hr]
    have hgs : ∑ k ∈ Finset.range M, ‖(-(q ^ (k + 2)) : ℂ)‖ ≤ 2 * r ^ 2 := by
      rw [hsum1]; exact geom_range_shift_le r hr0 hr1 M
    have htermsum : ∑ k ∈ Finset.range M, ‖(-(q ^ (k + 2)) : ℂ)‖ ≤ 1 / 2 := by
      have h3 : (2 : ℝ) * r ^ 2 ≤ 1 / 2 := by nlinarith [hr0, hr512]
      linarith
    have hL1 := norm_prod_one_add_sub_one_le_two (Finset.range M) (fun k => -(q ^ (k + 2)))
      htermsum
    have hnew : ‖∏ k ∈ Finset.range M, (1 + -(q ^ (k + 2))) - 1‖ ≤ 4 * r ^ 2 := by linarith
    have hid : (∏ k ∈ Finset.range M, (1 + -(q ^ (k + 2)))) * (1 - q) - (1 - q)
        = (1 - q) * (∏ k ∈ Finset.range M, (1 + -(q ^ (k + 2))) - 1) := by ring
    rw [hid, norm_mul]
    calc ‖1 - q‖ * ‖∏ k ∈ Finset.range M, (1 + -(q ^ (k + 2))) - 1‖
        ≤ (1 + r) * (4 * r ^ 2) :=
          mul_le_mul hnq hnew (norm_nonneg _) (by linarith)
      _ ≤ 5 * r ^ 2 := by nlinarith [hr0, hr1]
  have hlim := hmul.tendsto_prod_tprod_nat
  have hlim2 : Tendsto
      (fun N : ℕ => ‖∏ k ∈ Finset.range N, (1 - ModularForm.eta_q k (τ : ℂ)) - (1 - q)‖)
      atTop (nhds ‖(∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) - (1 - q)‖) :=
    (hlim.sub tendsto_const_nhds).norm
  exact le_of_tendsto hlim2 (eventually_atTop.mpr ⟨1, fun N hN => hbd N hN⟩)

/-- **Third-order cusp expansion of `Δ`.**  On `Im τ ≥ 1`,
`Δ τ = q - 24 q² + O(q³)` with explicit constant `500`, where `q = e^{2πiτ}`. -/
private theorem delta_third_order_bound (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ
        + 24 * (Work.Kernels.qParamFun τ) ^ 2‖
      ≤ 500 * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  set q : ℂ := Work.Kernels.qParamFun τ with hqdef
  set r : ℝ := ‖q‖ with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr512 : r ≤ 1 / 512 := by
    rw [hrdef, hqdef]
    exact Work.Asymptotics.norm_qParamFun_le_inv512 hτ
  have hr1 : r ≤ 1 / 2 := by linarith
  have hqper : Function.Periodic.qParam 1 (τ : ℂ) = q := by
    rw [hqdef]
    simp [Work.Kernels.qParamFun, Function.Periodic.qParam]
  have hq_lt : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by rw [hqper]; linarith
  have hmul : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ)) :=
    ModularForm.multipliable_one_sub_pow hq_lt
  set P : ℂ := ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) with hPdef
  have hΔ : Work.Kernels.DeltaFun τ = q * P ^ 24 := by
    rw [hPdef]
    rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant,
      ModularForm.discriminant_eq_q_prod]
    rw [hqper, hmul.tprod_pow]
  have hP1 : ‖P - (1 - q)‖ ≤ 5 * r ^ 2 := by
    rw [hPdef]
    exact tprod_eta_close τ q r hqper hrdef hr512
  have hnq : ‖1 - q‖ ≤ 1 + r := by
    calc ‖1 - q‖ ≤ ‖(1 : ℂ)‖ + ‖q‖ := norm_sub_le 1 q
      _ = 1 + r := by rw [norm_one, ← hrdef]
  have hPnorm : ‖P‖ ≤ 1002 / 1000 := by
    have h1 : ‖P‖ ≤ ‖P - (1 - q)‖ + ‖1 - q‖ := by
      have h := norm_add_le (P - (1 - q)) (1 - q)
      rwa [sub_add_cancel] at h
    have h2 : ‖P - (1 - q)‖ + ‖1 - q‖ ≤ 5 * r ^ 2 + (1 + r) := by linarith
    have h3 : 5 * r ^ 2 + (1 + r) ≤ 1002 / 1000 := by nlinarith [hr0, hr512, sq_nonneg r]
    linarith
  have hnq2 : ‖1 - q‖ ≤ 1002 / 1000 := by
    have h3 : 1 + r ≤ 1002 / 1000 := by nlinarith [hr512]
    linarith
  have hcoef : ‖∑ i ∈ Finset.range 24, P ^ i * (1 - q) ^ (24 - 1 - i)‖ ≤ 26 := by
    calc ‖∑ i ∈ Finset.range 24, P ^ i * (1 - q) ^ (24 - 1 - i)‖
        ≤ ∑ i ∈ Finset.range 24, ‖P ^ i * (1 - q) ^ (24 - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range 24, (1002 / 1000 : ℝ) ^ 23 := by
          apply Finset.sum_le_sum
          intro i hi
          have hi23 : i ≤ 23 := by have h := Finset.mem_range.mp hi; omega
          rw [norm_mul, norm_pow, norm_pow]
          calc ‖P‖ ^ i * ‖1 - q‖ ^ (24 - 1 - i)
              ≤ (1002 / 1000) ^ i * (1002 / 1000) ^ (24 - 1 - i) := by
                apply mul_le_mul
                · exact pow_le_pow_left₀ (norm_nonneg _) hPnorm i
                · exact pow_le_pow_left₀ (norm_nonneg _) hnq2 (24 - 1 - i)
                · positivity
                · positivity
            _ = (1002 / 1000) ^ (i + (24 - 1 - i)) := by rw [← pow_add]
            _ = (1002 / 1000) ^ 23 := by
                congr 1
                omega
      _ = 24 * (1002 / 1000 : ℝ) ^ 23 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
      _ ≤ 26 := by norm_num
  have hP24 : ‖P ^ 24 - (1 - q) ^ 24‖ ≤ 130 * r ^ 2 := by
    have hfac : P ^ 24 - (1 - q) ^ 24
        = (∑ i ∈ Finset.range 24, P ^ i * (1 - q) ^ (24 - 1 - i)) * (P - (1 - q)) := by
      have h := geom_sum₂_mul_add (P - (1 - q)) (1 - q) 24
      simp only [sub_add_cancel] at h
      rw [← h]
      ring
    rw [hfac, norm_mul]
    calc ‖∑ i ∈ Finset.range 24, P ^ i * (1 - q) ^ (24 - 1 - i)‖ * ‖P - (1 - q)‖
        ≤ 26 * (5 * r ^ 2) := mul_le_mul hcoef hP1 (norm_nonneg _) (by norm_num)
      _ = 130 * r ^ 2 := by ring
  have hP3b : ‖(1 - q) ^ 24 - 1 + 24 * q‖ ≤ 290 * r ^ 2 :=
    one_sub_pow24_sub_linear q r hrdef hr512
  have hP3 : ‖P ^ 24 - 1 + 24 * q‖ ≤ 500 * r ^ 2 := by
    have hsplit : P ^ 24 - 1 + 24 * q = (P ^ 24 - (1 - q) ^ 24) + ((1 - q) ^ 24 - 1 + 24 * q) := by
      ring
    rw [hsplit]
    calc ‖(P ^ 24 - (1 - q) ^ 24) + ((1 - q) ^ 24 - 1 + 24 * q)‖
        ≤ ‖P ^ 24 - (1 - q) ^ 24‖ + ‖(1 - q) ^ 24 - 1 + 24 * q‖ := norm_add_le _ _
      _ ≤ 130 * r ^ 2 + 290 * r ^ 2 := add_le_add hP24 hP3b
      _ ≤ 500 * r ^ 2 := by nlinarith [sq_nonneg r]
  have hmain : Work.Kernels.DeltaFun τ - q + 24 * q ^ 2 = q * (P ^ 24 - 1 + 24 * q) := by
    rw [hΔ]; ring
  rw [hmain, norm_mul]
  rw [show ‖q‖ = r from hrdef.symm]
  calc r * ‖P ^ 24 - 1 + 24 * q‖ ≤ r * (500 * r ^ 2) := mul_le_mul_of_nonneg_left hP3 hr0
    _ = 500 * r ^ 3 := by ring

/-- **Numerator estimate.**  Given the two explicit cusp expansions of `E` and `Δ`
(constants `20000` and `500`), the numerator `E³ - Δ(q⁻¹ + 744)` of `j - q⁻¹ - 744` is
`O(q²)` with constant `4·10⁵` on `‖q‖ ≤ 1/512`. -/
private lemma num_small_estimate (E D q : ℂ) (r : ℝ) (hq0 : q ≠ 0)
    (hr : r = ‖q‖) (hr512 : r ≤ 1 / 512)
    (he : ‖E - 1 - 240 * q‖ ≤ 20000 * r ^ 2)
    (hd : ‖D - q + 24 * q ^ 2‖ ≤ 500 * r ^ 3) :
    ‖E ^ 3 - D * (q⁻¹ + 744)‖ ≤ 400000 * r ^ 2 := by
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hrne : r ≠ 0 := by rw [hr]; exact norm_ne_zero_iff.mpr hq0
  have hpow : r ^ 3 * r⁻¹ = r ^ 2 := by
    rw [show r ^ 3 = r ^ 2 * r by ring, mul_assoc, mul_inv_cancel₀ hrne, mul_one]
  have hid : E ^ 3 - D * (q⁻¹ + 744)
      = 3 * (E - 1 - 240 * q) + 3 * (E - 1) ^ 2 + (E - 1) ^ 3
        - (D - q + 24 * q ^ 2) * q⁻¹ - 744 * (D - q + 24 * q ^ 2) + 17856 * q ^ 2 := by
    field_simp
    ring
  have ha : ‖E - 1‖ ≤ 280 * r := by
    have h1 : E - 1 = 240 * q + (E - 1 - 240 * q) := by ring
    rw [h1]
    have h2 : ‖240 * q + (E - 1 - 240 * q)‖ ≤ ‖(240 : ℂ) * q‖ + ‖E - 1 - 240 * q‖ :=
      norm_add_le _ _
    have h3 : ‖(240 : ℂ) * q‖ = 240 * r := by rw [norm_mul, Complex.norm_ofNat, ← hr]
    have h4 : (20000 : ℝ) * r ^ 2 ≤ 40 * r := by nlinarith [hr0, hr512]
    calc ‖240 * q + (E - 1 - 240 * q)‖
        ≤ ‖(240 : ℂ) * q‖ + ‖E - 1 - 240 * q‖ := h2
      _ = 240 * r + ‖E - 1 - 240 * q‖ := by rw [h3]
      _ ≤ 240 * r + 20000 * r ^ 2 := by linarith [he]
      _ ≤ 280 * r := by linarith [h4]
  have ha2 : ‖E - 1‖ ^ 2 ≤ (280 * r) ^ 2 := by
    nlinarith [ha, norm_nonneg (E - 1), hr0]
  have hb1 : ‖3 * (E - 1 - 240 * q)‖ ≤ 60000 * r ^ 2 := by
    rw [norm_mul, show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num]
    nlinarith [he]
  have hb2 : ‖3 * (E - 1) ^ 2‖ ≤ 235200 * r ^ 2 := by
    rw [norm_mul, show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num, norm_pow]
    nlinarith [ha2, sq_nonneg r, hr0]
  have hb3 : ‖(E - 1) ^ 3‖ ≤ 42875 * r ^ 2 := by
    rw [norm_pow]
    have hsplit : ‖E - 1‖ ^ 3 = ‖E - 1‖ ^ 2 * ‖E - 1‖ := by ring
    rw [hsplit]
    have h1 : ‖E - 1‖ ^ 2 * ‖E - 1‖ ≤ (280 * r) ^ 2 * (280 * r) :=
      mul_le_mul ha2 ha (norm_nonneg _) (by positivity)
    have h2 : (280 * r) ^ 2 * (280 * r) ≤ 42875 * r ^ 2 := by
      nlinarith [hr0, hr512, sq_nonneg r]
    linarith
  have hb4 : ‖(D - q + 24 * q ^ 2) * q⁻¹‖ ≤ 500 * r ^ 2 := by
    rw [norm_mul, norm_inv, ← hr]
    calc ‖D - q + 24 * q ^ 2‖ * r⁻¹
        ≤ (500 * r ^ 3) * r⁻¹ := mul_le_mul_of_nonneg_right hd (inv_nonneg.mpr hr0)
      _ = 500 * r ^ 2 := by rw [mul_assoc, hpow]
  have hb5 : ‖744 * (D - q + 24 * q ^ 2)‖ ≤ 727 * r ^ 2 := by
    rw [norm_mul, show ‖(744 : ℂ)‖ = (744 : ℝ) by norm_num]
    nlinarith [hd, hr0, hr512, sq_nonneg r]
  have hb6 : ‖17856 * q ^ 2‖ ≤ 17856 * r ^ 2 := by
    rw [norm_mul, show ‖(17856 : ℂ)‖ = (17856 : ℝ) by norm_num, norm_pow, ← hr]
  have hterms : ‖3 * (E - 1 - 240 * q) + 3 * (E - 1) ^ 2 + (E - 1) ^ 3
        - (D - q + 24 * q ^ 2) * q⁻¹ - 744 * (D - q + 24 * q ^ 2) + 17856 * q ^ 2‖
      ≤ ‖3 * (E - 1 - 240 * q)‖ + ‖3 * (E - 1) ^ 2‖ + ‖(E - 1) ^ 3‖
        + ‖(D - q + 24 * q ^ 2) * q⁻¹‖ + ‖744 * (D - q + 24 * q ^ 2)‖ + ‖17856 * q ^ 2‖ := by
    have h1 := norm_add_le (3 * (E - 1 - 240 * q) + 3 * (E - 1) ^ 2 + (E - 1) ^ 3
        - (D - q + 24 * q ^ 2) * q⁻¹ - 744 * (D - q + 24 * q ^ 2)) (17856 * q ^ 2)
    have h2 := norm_sub_le (3 * (E - 1 - 240 * q) + 3 * (E - 1) ^ 2 + (E - 1) ^ 3
        - (D - q + 24 * q ^ 2) * q⁻¹) (744 * (D - q + 24 * q ^ 2))
    have h3 := norm_sub_le (3 * (E - 1 - 240 * q) + 3 * (E - 1) ^ 2 + (E - 1) ^ 3)
        ((D - q + 24 * q ^ 2) * q⁻¹)
    have h4 := norm_add_le (3 * (E - 1 - 240 * q) + 3 * (E - 1) ^ 2) ((E - 1) ^ 3)
    have h5 := norm_add_le (3 * (E - 1 - 240 * q)) (3 * (E - 1) ^ 2)
    linarith
  rw [hid]
  calc ‖3 * (E - 1 - 240 * q) + 3 * (E - 1) ^ 2 + (E - 1) ^ 3
        - (D - q + 24 * q ^ 2) * q⁻¹ - 744 * (D - q + 24 * q ^ 2) + 17856 * q ^ 2‖
      ≤ ‖3 * (E - 1 - 240 * q)‖ + ‖3 * (E - 1) ^ 2‖ + ‖(E - 1) ^ 3‖
        + ‖(D - q + 24 * q ^ 2) * q⁻¹‖ + ‖744 * (D - q + 24 * q ^ 2)‖ + ‖17856 * q ^ 2‖ := hterms
    _ ≤ 60000 * r ^ 2 + 235200 * r ^ 2 + 42875 * r ^ 2 + 500 * r ^ 2 + 727 * r ^ 2
          + 17856 * r ^ 2 := by linarith [hb1, hb2, hb3, hb4, hb5, hb6]
    _ = 357158 * r ^ 2 := by ring
    _ ≤ 400000 * r ^ 2 := by nlinarith [sq_nonneg r]

/-! ## The main pointwise bound -/

theorem low_height_j :
    ∀ u : UpperHalfPlane, 1 ≤ u.im →
      ‖Work.Kernels.jInvariantFun u - (Work.Kernels.qParamFun u)⁻¹ - 744‖
        ≤ 10 ^ 7 * ‖Work.Kernels.qParamFun u‖ := by
  intro u hu
  set q : ℂ := Work.Kernels.qParamFun u with hqdef
  set r : ℝ := ‖q‖ with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr512 : r ≤ 1 / 512 := by
    rw [hrdef, hqdef]
    exact Work.Asymptotics.norm_qParamFun_le_inv512 hu
  have hq0 : q ≠ 0 := by rw [hqdef]; exact Complex.exp_ne_zero _
  have hrne : r ≠ 0 := by rw [hrdef]; exact norm_ne_zero_iff.mpr hq0
  have hε : ‖Work.Kernels.E4Fun u - 1 - 240 * q‖ ≤ 20000 * r ^ 2 := by
    have h := e4_cusp_second_order u hu
    rw [← hqdef, ← hrdef] at h
    exact h
  have hδ : ‖Work.Kernels.DeltaFun u - q + 24 * q ^ 2‖ ≤ 500 * r ^ 3 := by
    have h := delta_third_order_bound u hu
    rw [← hqdef, ← hrdef] at h
    exact h
  have hN : ‖Work.Kernels.E4Fun u ^ 3 - Work.Kernels.DeltaFun u * (q⁻¹ + 744)‖
      ≤ 400000 * r ^ 2 :=
    num_small_estimate (Work.Kernels.E4Fun u) (Work.Kernels.DeltaFun u) q r hq0 hrdef hr512 hε hδ
  have hΔne : Work.Kernels.DeltaFun u ≠ 0 := by
    have h : Work.Kernels.DeltaFun u = ModularForm.discriminant u := by
      rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
    rw [h]
    exact ModularForm.discriminant_ne_zero u
  have hDlow : r / 2 ≤ ‖Work.Kernels.DeltaFun u‖ := by
    have hsub : ‖Work.Kernels.DeltaFun u - q‖ ≤ 24 * r ^ 2 + 500 * r ^ 3 := by
      have h1 : Work.Kernels.DeltaFun u - q
          = (Work.Kernels.DeltaFun u - q + 24 * q ^ 2) - 24 * q ^ 2 := by ring
      rw [h1]
      have h2 : ‖(24 : ℂ) * q ^ 2‖ = 24 * r ^ 2 := by rw [norm_mul, norm_pow, hrdef]; norm_num
      calc ‖(Work.Kernels.DeltaFun u - q + 24 * q ^ 2) - 24 * q ^ 2‖
          ≤ ‖Work.Kernels.DeltaFun u - q + 24 * q ^ 2‖ + ‖(24 : ℂ) * q ^ 2‖ := norm_sub_le _ _
        _ ≤ 500 * r ^ 3 + 24 * r ^ 2 := by rw [h2]; linarith
        _ = 24 * r ^ 2 + 500 * r ^ 3 := by ring
    have h3 : r - ‖Work.Kernels.DeltaFun u - q‖ ≤ ‖Work.Kernels.DeltaFun u‖ := by
      have h := abs_norm_sub_norm_le q (Work.Kernels.DeltaFun u)
      rw [abs_le] at h
      have h4 : ‖q - Work.Kernels.DeltaFun u‖ = ‖Work.Kernels.DeltaFun u - q‖ := norm_sub_rev _ _
      rw [h4, ← hrdef] at h
      linarith [h.1]
    have h5 : 24 * r ^ 2 + 500 * r ^ 3 ≤ r / 2 := by
      nlinarith [hr0, hr512, sq_nonneg r]
    linarith
  have hdiv : Work.Kernels.jInvariantFun u - q⁻¹ - 744
      = (Work.Kernels.E4Fun u ^ 3 - Work.Kernels.DeltaFun u * (q⁻¹ + 744))
          / Work.Kernels.DeltaFun u := by
    rw [show Work.Kernels.jInvariantFun u
        = Work.Kernels.E4Fun u ^ 3 / Work.Kernels.DeltaFun u from rfl]
    field_simp
    ring
  rw [hdiv, norm_div]
  have hstep : ‖Work.Kernels.E4Fun u ^ 3 - Work.Kernels.DeltaFun u * (q⁻¹ + 744)‖
        / ‖Work.Kernels.DeltaFun u‖ ≤ (400000 * r ^ 2) / (r / 2) :=
    div_le_div₀ (by positivity) hN (by
      have : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
      linarith) hDlow
  calc ‖Work.Kernels.E4Fun u ^ 3 - Work.Kernels.DeltaFun u * (q⁻¹ + 744)‖
        / ‖Work.Kernels.DeltaFun u‖ ≤ (400000 * r ^ 2) / (r / 2) := hstep
    _ = 800000 * r := by field_simp; ring
    _ ≤ 10 ^ 7 * r := by nlinarith [hr0]

end Work.Asymptotics.EJL
