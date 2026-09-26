import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.DeltaFun_upper_sharp

/-!
# First-order (linear) bound for `Δ` at the cusp: `‖Δ - q‖ ≤ (1/20)‖q‖` on `{Im ≥ 1}`

`Δ = q ∏'ₙ (1 - η_q n)^24` (`ModularForm.discriminant_eq_q_prod`), where `q = qParamFun z =
e^{2πiz}`.  Hence `Δ z - q z = q z · (P z - 1)` with `P z = ∏'ₙ (1 - η_q n)^24`, so the theorem
is exactly the statement

  `‖P z - 1‖ ≤ 1/20`      for `Im z ≥ 1`.

The size of `P z - 1` is controlled by the elementary telescoping estimate

  `‖∏_{n<N} (1 + c n) - 1‖ ≤ ∏_{n<N} (1 + ‖c n‖) - 1`,

applied with `c n = (1 - η_q n)^24 - 1`.  On `{Im z ≥ 1}` the nome satisfies `‖q‖ ≤ 1/512`
(`e^{-2π} < 1/512`), and `‖η_q n‖ = ‖q‖^{n+1}`, so `‖c n‖ ≤ (1+‖q‖^{n+1})^24 - 1`; passing to
the limit along `atTop` gives `‖P z - 1‖ ≤ ∏'ₙ (1+‖q‖^{n+1})^24 - 1`.  Finally
`∏'ₙ (1 + r^{n+1}) ≤ exp (r/(1-r)) ≤ 511/510` for `r ≤ 1/512`, whence
`∏'ₙ (1+r^{n+1})^24 ≤ (511/510)^24 ≤ 21/20`, i.e. `‖P z - 1‖ ≤ 1/20`.
-/

open scoped Topology
open Filter
open UpperHalfPlane

namespace Work.CKFinal.LineDecay

noncomputable section

/-! ## Numerical input: `‖q‖ ≤ 1/512` on `{1 ≤ Im τ}` -/

private lemma exp_neg_two_pi_le_inv512 : Real.exp (-(2 * Real.pi)) ≤ 1 / 512 := by
  have h1 : Real.exp (-(2 * Real.pi)) ≤ Real.exp (-6.28 : ℝ) := by
    rw [Real.exp_le_exp]; linarith [Real.pi_gt_d20]
  have h5 : Real.exp (-6.28 : ℝ) ≤ 1 / 512 := by
    rw [Real.exp_neg, show (1:ℝ)/512 = (512:ℝ)⁻¹ by norm_num]
    rw [inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
    have he6 : (403 : ℝ) ≤ Real.exp 6 := by
      have h := Real.sum_le_exp_of_nonneg (x := (6:ℝ)) (by norm_num) 16
      norm_num [Finset.sum_range_succ] at h ⊢
      linarith
    have he028 : (1.28 : ℝ) ≤ Real.exp (0.28 : ℝ) := by
      have h := Real.add_one_le_exp (0.28 : ℝ)
      linarith
    have h6 : (512 : ℝ) ≤ Real.exp 6 * Real.exp (0.28 : ℝ) := by nlinarith
    have h7 : Real.exp 6 * Real.exp (0.28 : ℝ) = Real.exp (6.28 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    linarith
  exact le_trans h1 h5

/-- The nome is at most `1/512` on `{1 ≤ Im τ}`. -/
private lemma nome_le_inv512 (z : UpperHalfPlane) (hz : 1 ≤ z.im) :
    ‖Work.Kernels.qParamFun z‖ ≤ 1 / 512 := by
  rw [Work.Asymptotics.norm_qParamFun]
  have h2 : Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (-(2 * Real.pi)) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hz]
  linarith [exp_neg_two_pi_le_inv512, h2]

/-! ## Elementary norm estimates -/

/-- `‖η_q n‖` is the `(n+1)`-st power of the nome. -/
private lemma norm_eta_q_eq_pow (n : ℕ) (z : UpperHalfPlane) :
    ‖ModularForm.eta_q n (z : ℂ)‖ = ‖Work.Kernels.qParamFun z‖ ^ (n + 1) := by
  rw [Work.Asymptotics.norm_eta_q, Work.Asymptotics.norm_qParamFun, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `‖(1+x)^k - 1‖ ≤ (1+r)^k - 1` whenever `‖x‖ ≤ r`. -/
private lemma norm_one_add_pow_sub_one_le (x : ℂ) (k : ℕ) (r : ℝ) (hx : ‖x‖ ≤ r) :
    ‖(1 + x) ^ k - 1‖ ≤ (1 + r) ^ k - 1 := by
  have hr : 0 ≤ r := le_trans (norm_nonneg x) hx
  have h1 : (1 + x) ^ k - 1 = (∑ j ∈ Finset.range k, (1 + x) ^ j) * x := by
    have := geom_sum_mul (1 + x) k
    rw [show (1 + x) - 1 = x by ring] at this
    exact this.symm
  rw [h1, norm_mul]
  have h2 : ‖∑ j ∈ Finset.range k, (1 + x) ^ j‖ ≤ ∑ j ∈ Finset.range k, (1 + r) ^ j := by
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ j
    have h := norm_add_le (1:ℂ) x
    rw [norm_one] at h
    linarith
  calc ‖∑ j ∈ Finset.range k, (1 + x) ^ j‖ * ‖x‖
      ≤ (∑ j ∈ Finset.range k, (1 + r) ^ j) * r := by
        refine mul_le_mul h2 hx (norm_nonneg x) ?_
        exact Finset.sum_nonneg (fun j _ => pow_nonneg (by linarith) j)
    _ = (1 + r) ^ k - 1 := by
        have hg := geom_sum_mul (1 + r) k
        rw [show (1 + r) - 1 = r by ring] at hg
        exact hg

/-- **Telescoping product estimate.**  `‖∏_{n<N}(1+c n) - 1‖ ≤ ∏_{n<N}(1+u n) - 1`
whenever `‖c n‖ ≤ u n`. -/
private lemma norm_prod_range_one_add_sub_one_le (N : ℕ) (c : ℕ → ℂ) (u : ℕ → ℝ)
    (hc : ∀ n < N, ‖c n‖ ≤ u n) :
    ‖(∏ n ∈ Finset.range N, (1 + c n)) - 1‖ ≤ (∏ n ∈ Finset.range N, (1 + u n)) - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hcN : ∀ n < N, ‖c n‖ ≤ u n := fun n hn => hc n (Nat.lt_succ_of_lt hn)
    have ih' : ‖(∏ n ∈ Finset.range N, (1 + c n)) - 1‖
        ≤ (∏ n ∈ Finset.range N, (1 + u n)) - 1 := ih hcN
    have hN := hc N (Nat.lt_succ_self N)
    have hQ0 : 0 ≤ ∏ n ∈ Finset.range N, (1 + u n) :=
      Finset.prod_nonneg (fun i hi => by
        have := hcN i (Finset.mem_range.mp hi)
        linarith [norm_nonneg (c i)])
    have hPnorm : ‖∏ n ∈ Finset.range N, (1 + c n)‖ ≤ ∏ n ∈ Finset.range N, (1 + u n) := by
      refine le_trans (Finset.norm_prod_le _ _) ?_
      refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => ?_)
      have hci := hcN i (Finset.mem_range.mp hi)
      have h1 := norm_add_le (1:ℂ) (c i)
      rw [norm_one] at h1
      linarith
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have hkey : (∏ n ∈ Finset.range N, (1 + c n)) * (1 + c N) - 1
        = ((∏ n ∈ Finset.range N, (1 + c n)) - 1)
          + (∏ n ∈ Finset.range N, (1 + c n)) * c N := by ring
    rw [hkey]
    calc ‖((∏ n ∈ Finset.range N, (1 + c n)) - 1)
            + (∏ n ∈ Finset.range N, (1 + c n)) * c N‖
        ≤ ‖(∏ n ∈ Finset.range N, (1 + c n)) - 1‖
            + ‖(∏ n ∈ Finset.range N, (1 + c n)) * c N‖ := norm_add_le _ _
      _ ≤ ((∏ n ∈ Finset.range N, (1 + u n)) - 1) + (∏ n ∈ Finset.range N, (1 + u n)) * u N := by
          rw [norm_mul]
          have h2 := mul_le_mul hPnorm hN (norm_nonneg _) hQ0
          linarith
      _ = (∏ n ∈ Finset.range N, (1 + u n)) * (1 + u N) - 1 := by ring

/-! ## The geometric infinite product -/

/-- For `0 ≤ r ≤ 1/512` one has `∏'ₙ (1 + r^{n+1})^24 ≤ 21/20`. -/
private lemma tprod_geom_pow_le (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 512) :
    ∏' n : ℕ, (1 + r ^ (n + 1)) ^ 24 ≤ 21 / 20 := by
  have hr1 : r < 1 := by linarith
  have hsum : Summable (fun n : ℕ => r ^ (n + 1)) := by
    have h0 : Summable (fun n : ℕ => r * r ^ n) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left r
    refine h0.congr (fun n => ?_)
    rw [pow_succ]; ring
  have htsum : ∑' n : ℕ, r ^ (n + 1) = r / (1 - r) :=
    Work.Asymptotics.tsum_pow_succ_eq r hr0 hr1
  have hmul : Multipliable (fun n : ℕ => (1 + r ^ (n + 1)) ^ 24) :=
    (Real.multipliable_one_add_of_summable hsum).pow 24
  refine hmul.tprod_le_of_prod_le (fun s => ?_)
  have h1 : ∏ i ∈ s, (1 + r ^ (i + 1)) ^ 24 = (∏ i ∈ s, (1 + r ^ (i + 1))) ^ 24 :=
    Finset.prod_pow s 24 _
  rw [h1]
  have h2 : ∏ i ∈ s, (1 + r ^ (i + 1)) ≤ Real.exp (r / (1 - r)) := by
    refine le_trans (Work.Asymptotics.prod_one_add_le_exp_sum s _
      (fun i _ => pow_nonneg hr0 _)) ?_
    refine Real.exp_le_exp.mpr ?_
    rw [← htsum]
    exact hsum.sum_le_tsum s (fun i _ => pow_nonneg hr0 (i+1))
  have hr511 : r / (1 - r) ≤ 1 / 511 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - r)]
    linarith
  calc (∏ i ∈ s, (1 + r ^ (i + 1))) ^ 24
      ≤ (Real.exp (r / (1 - r))) ^ 24 :=
        pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => by positivity)) h2 24
    _ = Real.exp (24 * (r / (1 - r))) := by
        rw [← Real.exp_nat_mul]; push_cast; ring
    _ ≤ Real.exp (24 / 511) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [mul_le_mul_of_nonneg_left hr511 (by norm_num : (0:ℝ) ≤ 24)]
    _ ≤ 511 / 487 := by
        have h4 := Work.Asymptotics.exp_le_inv_one_sub (x := (24/511 : ℝ)) (by norm_num)
        have h5 : ((1 : ℝ) - 24/511)⁻¹ = 511/487 := by norm_num
        linarith [h5 ▸ h4]
    _ ≤ 21 / 20 := by norm_num

/-! ## The theorem -/

theorem Delta_first_order_lin :
    ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.DeltaFun z - Work.Kernels.qParamFun z‖
        ≤ (1 / 20) * ‖Work.Kernels.qParamFun z‖ := by
  intro z hz
  set q : ℂ := Work.Kernels.qParamFun z with hq
  set r : ℝ := ‖q‖ with hr
  set η : ℕ → ℂ := fun n => ModularForm.eta_q n (z : ℂ) with hη
  set A : ℕ → ℂ := fun n => (1 - η n) ^ 24 with hA
  set B : ℕ → ℝ := fun n => (1 + r ^ (n + 1)) ^ 24 with hB
  have hr0 : 0 ≤ r := norm_nonneg q
  have hr512 : r ≤ 1 / 512 := by rw [hr]; exact nome_le_inv512 z hz
  have hηnorm : ∀ n, ‖η n‖ = r ^ (n + 1) := by
    intro n; rw [hη, hr, hq]; exact norm_eta_q_eq_pow n z
  have hmulη : Multipliable (fun n : ℕ => 1 - η n) := by
    have h := ModularForm.multipliableLocallyUniformlyOn_eta.multipliable z.2
    simpa [hη] using h
  have hmulA : Multipliable A := hmulη.pow 24
  have hsumB : Summable (fun n : ℕ => r ^ (n + 1)) := by
    have h0 : Summable (fun n : ℕ => r * r ^ n) :=
      (summable_geometric_of_lt_one hr0 (by linarith)).mul_left r
    refine h0.congr (fun n => ?_); rw [pow_succ]; ring
  have hmulB : Multipliable B := (Real.multipliable_one_add_of_summable hsumB).pow 24
  have hfin : ∀ N, ‖(∏ n ∈ Finset.range N, A n) - 1‖ ≤ (∏ n ∈ Finset.range N, B n) - 1 := by
    intro N
    have h := norm_prod_range_one_add_sub_one_le N (fun n => A n - 1) (fun n => B n - 1)
      (fun n _ => by
        have h1 : A n - 1 = (1 + (-η n)) ^ 24 - 1 := by rw [hA]; ring
        rw [h1]
        show ‖(1 + -η n) ^ 24 - 1‖ ≤ (1 + r ^ (n + 1)) ^ 24 - 1
        exact norm_one_add_pow_sub_one_le (-η n) 24 (r ^ (n+1))
          (by rw [norm_neg]; exact le_of_eq (hηnorm n)))
    simpa using h
  have h1lim : Filter.Tendsto (fun N => ‖(∏ n ∈ Finset.range N, A n) - 1‖) Filter.atTop
      (𝓝 (‖(∏' n, A n) - 1‖)) :=
    ((hmulA.hasProd.tendsto_prod_nat.sub tendsto_const_nhds).norm)
  have h2lim : Filter.Tendsto (fun N => (∏ n ∈ Finset.range N, B n) - 1) Filter.atTop
      (𝓝 ((∏' n, B n) - 1)) :=
    (hmulB.hasProd.tendsto_prod_nat.sub tendsto_const_nhds)
  have hP : ‖(∏' n, A n) - 1‖ ≤ (∏' n, B n) - 1 :=
    le_of_tendsto_of_tendsto' h1lim h2lim hfin
  have hB21 : (∏' n, B n) ≤ 21 / 20 := by
    have h := tprod_geom_pow_le r hr0 hr512
    simpa [hB] using h
  have hP20 : ‖(∏' n, A n) - 1‖ ≤ 1 / 20 := by linarith
  have hΔ : Work.Kernels.DeltaFun z = q * ∏' n, A n := by
    have h1 : Work.Kernels.DeltaFun z = ModularForm.discriminant z := by
      rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
    rw [h1, ModularForm.discriminant_eq_q_prod, hq, Work.Asymptotics.qParamFun_eq_qParam z]
  rw [hΔ]
  have hfac : q * (∏' n, A n) - q = q * ((∏' n, A n) - 1) := by ring
  rw [hfac, norm_mul]
  calc ‖q‖ * ‖(∏' n, A n) - 1‖ ≤ ‖q‖ * (1 / 20) := mul_le_mul_of_nonneg_left hP20 (norm_nonneg q)
    _ = (1 / 20) * r := by rw [hr]; ring

end

end Work.CKFinal.LineDecay
