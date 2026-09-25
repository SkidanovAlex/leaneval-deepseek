import Mathlib

namespace Work.BourgainPlan.IonescuWainger

open Finset Filter

/-- For `t ≥ 0`, the `rpow` expression `(1+t)^{-2}` is the reciprocal of the square. -/
private lemma rpow_neg_two_eq_inv_sq (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ (-(2 : ℝ)) = 1 / (1 + t) ^ 2 := by
  have h : (0 : ℝ) < 1 + t := by linarith
  rw [Real.rpow_neg (le_of_lt h), Real.rpow_two, inv_eq_one_div]

/-- Splitting a sum over `ℤ` into its nonnegative and negative parts. -/
private lemma int_tsum_split (g : ℤ → ℝ)
    (h1 : Summable fun n : ℕ => g n) (h2 : Summable fun n : ℕ => g (Int.negSucc n)) :
    ∑' l : ℤ, g l = (∑' n : ℕ, g n) + ∑' n : ℕ, g (Int.negSucc n) := by
  have h := Equiv.tsum_eq (Equiv.intEquivNatSumNat.symm) g
  rw [← h]
  have e1 : Summable fun n : ℕ => g (Equiv.intEquivNatSumNat.symm (Sum.inl n)) :=
    h1.congr (fun n => rfl)
  have e2 : Summable fun n : ℕ => g (Equiv.intEquivNatSumNat.symm (Sum.inr n)) :=
    h2.congr (fun n => rfl)
  have h2' : (∑' i : ℕ, g (Equiv.intEquivNatSumNat.symm (Sum.inl i))) = ∑' n : ℕ, g n :=
    tsum_congr (fun n => rfl)
  have h3' : (∑' i : ℕ, g (Equiv.intEquivNatSumNat.symm (Sum.inr i)))
      = ∑' n : ℕ, g (Int.negSucc n) := tsum_congr (fun n => rfl)
  rw [Summable.tsum_sum (f := fun c : ℕ ⊕ ℕ => g (Equiv.intEquivNatSumNat.symm c)) e1 e2,
    h2', h3']

/-- Riemann-comparison bound for the `ℤ`-sum of the majorant: for `0 < a ≤ 1`,
`a · ∑_{l ∈ ℤ} (1 + |a l|)^{-2} ≤ 3`.

Proof route: rewrite the `ℤ`-sum as `∑_{n ∈ ℕ} (1 + a n)^{-2} + ∑_{n ∈ ℕ} (1 + a(n+1))^{-2}` via
`Equiv.intEquivNatSumNat` and `Summable.tsum_sum`; then use the integral test
`AntitoneOn.tsum_add_one_le_integral` / `AntitoneOn.tsum_le_integral` for `f t = a (1 + a t)^{-2}`
(antitone, nonnegative, `∫_{(0,∞)} f = 1`), giving `a · ∑_l (1+|al|)^{-2} ≤ a + 2 ≤ 3`. -/
theorem int_tsum_rpow_inv_two_mul_le (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    a * ∑' (l : ℤ), (1 + |a * (l : ℝ)|) ^ (-(2 : ℝ)) ≤ 3 := by
  let F : ℕ → ℝ := fun n => (1 + a * (n:ℝ)) ^ (-(2:ℝ))
  let u : ℕ → ℝ := fun n => 1 / (1 + a * (n:ℝ))
  let T : ℕ → ℝ := fun n => a⁻¹ * (u n - u (n+1))
  have hF_nonneg : ∀ n : ℕ, 0 ≤ F n := by
    intro n
    simp only [F]
    rw [rpow_neg_two_eq_inv_sq _ (by positivity)]
    positivity
  have hF_le_T : ∀ n : ℕ, F (n+1) ≤ T n := by
    intro n
    simp only [F, T, u, Nat.cast_add, Nat.cast_one]
    have hD : (0:ℝ) < (1 + a*(n:ℝ)) * (1 + a*((n:ℝ)+1)) := by positivity
    have hsub : (1/(1+a*(n:ℝ))) - (1/(1+a*((n:ℝ)+1)))
        = a / ((1 + a*(n:ℝ)) * (1 + a*((n:ℝ)+1))) := by
      field_simp
      ring
    rw [rpow_neg_two_eq_inv_sq _ (by positivity), hsub]
    have hDle : (1 + a*(n:ℝ)) * (1 + a*((n:ℝ)+1)) ≤ (1 + a*((n:ℝ)+1))^2 := by
      have hle1 : 1 + a*(n:ℝ) ≤ 1 + a*((n:ℝ)+1) := by linarith
      have hpos2 : 0 ≤ 1 + a*((n:ℝ)+1) := by positivity
      calc (1 + a*(n:ℝ)) * (1 + a*((n:ℝ)+1))
          ≤ (1 + a*((n:ℝ)+1)) * (1 + a*((n:ℝ)+1)) :=
            mul_le_mul_of_nonneg_right hle1 hpos2
        _ = (1 + a*((n:ℝ)+1))^2 := by ring
    have h1 : 1 / (1 + a*((n:ℝ)+1))^2 ≤ 1 / ((1 + a*(n:ℝ)) * (1 + a*((n:ℝ)+1))) :=
      one_div_le_one_div_of_le hD hDle
    refine le_trans h1 (le_of_eq ?_)
    field_simp
  have hT_nonneg : ∀ n : ℕ, 0 ≤ T n := by
    intro n
    simp only [T, u, Nat.cast_add, Nat.cast_one]
    have hle : 1 / (1 + a * ((n:ℝ)+1)) ≤ 1 / (1 + a * (n:ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have := inv_pos.2 ha
    nlinarith
  have hu_tendsto : Tendsto u atTop (nhds 0) := by
    have hg : Tendsto (fun n : ℕ => 1 + a * (n:ℝ)) atTop atTop := by
      have h : Tendsto (fun n : ℕ => a * (n:ℝ) + 1) atTop atTop :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop ha).atTop_add tendsto_const_nhds
      simpa only [add_comm] using h
    have hconst : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds (1:ℝ)) := tendsto_const_nhds
    have hdiv := hconst.div_atTop hg
    simpa only [u] using hdiv
  have hpartial : ∀ N, ∑ i ∈ Finset.range N, T i = a⁻¹ * (u 0 - u N) := by
    intro N
    have htel : ∑ i ∈ Finset.range N, (u i - u (i+1)) = u 0 - u N := by
      have h := Finset.sum_range_sub u N
      have h' : ∑ i ∈ Finset.range N, (u i - u (i+1))
          = - ∑ i ∈ Finset.range N, (u (i+1) - u i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [h', h]
      ring
    simp only [T]
    rw [← Finset.mul_sum, htel]
  have hT_sum : HasSum T a⁻¹ := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hT_nonneg a⁻¹]
    simp_rw [hpartial]
    have hc : Tendsto (fun _ : ℕ => u 0) atTop (nhds (u 0)) := tendsto_const_nhds
    have hlim : Tendsto (fun N : ℕ => a⁻¹ * (u 0 - u N)) atTop (nhds a⁻¹) := by
      have h := (hc.sub hu_tendsto).const_mul a⁻¹
      simpa [u] using h
    exact hlim
  have hTs : Summable T := hT_sum.summable
  have hF1s : Summable (fun n => F (n+1)) :=
    Summable.of_nonneg_of_le (f := T) (fun n => hF_nonneg (n+1)) (fun n => hF_le_T n) hTs
  have hF1_le : ∑' n, F (n+1) ≤ a⁻¹ := by
    have h := Summable.tsum_le_tsum (fun n => hF_le_T n) hF1s hTs
    rwa [hT_sum.tsum_eq] at h
  have hFs : Summable F := (summable_nat_add_iff 1).mp hF1s
  have hF_le : ∑' n, F n ≤ 1 + a⁻¹ := by
    rw [hFs.tsum_eq_zero_add]
    have h0 : F 0 = 1 := by simp [F]
    rw [h0]
    linarith
  have hg_nat : ∀ n : ℕ, (1 + |a * ((n:ℤ):ℝ)|)^(-(2:ℝ)) = F n := by
    intro n
    simp only [F]
    have h : |a * ((n:ℤ):ℝ)| = a * (n:ℝ) := by
      rw [Int.cast_natCast, abs_of_nonneg (by positivity)]
    rw [h]
  have hg_neg : ∀ n : ℕ, (1 + |a * ((Int.negSucc n : ℤ):ℝ)|)^(-(2:ℝ)) = F (n+1) := by
    intro n
    simp only [F, Nat.cast_add, Nat.cast_one]
    have hcast : ((Int.negSucc n : ℤ) : ℝ) = -((n:ℝ)+1) := by
      rw [Int.cast_negSucc]; push_cast; ring
    have hle0 : a * -((n:ℝ)+1) ≤ 0 := by
      rw [mul_neg, neg_nonpos]
      positivity
    rw [hcast, abs_of_nonpos hle0]
    ring_nf
  have hGs : Summable (fun n : ℕ => (1 + |a * ((n:ℤ):ℝ)|)^(-(2:ℝ))) := by
    rw [show (fun n : ℕ => (1 + |a * ((n:ℤ):ℝ)|)^(-(2:ℝ))) = F from funext hg_nat]
    exact hFs
  have hGn : Summable (fun n : ℕ => (1 + |a * ((Int.negSucc n : ℤ):ℝ)|)^(-(2:ℝ))) := by
    rw [show (fun n : ℕ => (1 + |a * ((Int.negSucc n : ℤ):ℝ)|)^(-(2:ℝ)))
        = (fun n => F (n+1)) from funext hg_neg]
    exact hF1s
  have hsplit := int_tsum_split (fun l : ℤ => (1 + |a * (l:ℝ)|)^(-(2:ℝ))) hGs hGn
  have htotal : ∑' l : ℤ, (1 + |a * (l:ℝ)|)^(-(2:ℝ)) = (∑' n, F n) + ∑' n, F (n+1) := by
    rw [hsplit]
    congr 1
    · exact tsum_congr hg_nat
    · exact tsum_congr hg_neg
  rw [htotal]
  have h1 : ∑' n, F n + ∑' n, F (n+1) ≤ (1 + a⁻¹) + a⁻¹ := add_le_add hF_le hF1_le
  calc a * (∑' n, F n + ∑' n, F (n+1))
      ≤ a * ((1 + a⁻¹) + a⁻¹) := mul_le_mul_of_nonneg_left h1 (le_of_lt ha)
    _ = a + 2 := by field_simp; ring
    _ ≤ 3 := by linarith

end Work.BourgainPlan.IonescuWainger
