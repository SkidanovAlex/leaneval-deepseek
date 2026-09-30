import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The head sum bound for the VK chain

`Work.BMF.VKChain.head_rpow_sum_bound`: for `0 < σ ≤ 2`, `κ ≥ 0` with `(1-σ)κ ≤ 1`
and `K₀ ≤ exp κ + 2`,

`∑_{m=1}^{K₀} m^{-σ} ≤ 5 e⁴ (2 + κ)`.

The proof splits on whether `σ ≤ 1`.

* For `σ ≥ 1` we have `m^{-σ} ≤ 1/m`, hence the sum is at most the `K₀`-th harmonic
  number, which is `≤ 1 + log K₀`, and `log K₀ ≤ log(3 exp κ) = log 3 + κ`.
* For `σ ≤ 1`, `m^{-σ} = m^{1-σ}/m` and, since `m ≤ K₀ ≤ exp κ + 2 ≤ 3 exp κ`,
  `m^{1-σ} ≤ 3^{1-σ} e^{(1-σ)κ} ≤ 3 e`, so the sum is at most `3 e (1 + log K₀)`.

In both cases the arithmetic is closed by elementary numerical bounds
(`e ≤ 3`, `e^4 ≥ 16`, `log 3 ≤ 2`).
-/

namespace Work.BMF.VKChain

/-- Harmonic-sum bound: `∑_{m=1}^{K} 1/m ≤ 1 + log K` (Mathlib's `harmonic_le_one_add_log`). -/
private lemma sum_Icc_inv_le (K : ℕ) :
    (∑ m ∈ Finset.Icc 1 K, ((m : ℝ))⁻¹) ≤ 1 + Real.log (K : ℝ) := by
  have h := harmonic_le_one_add_log K
  have h2 : (harmonic K : ℝ) = ∑ m ∈ Finset.Icc 1 K, ((m : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rwa [h2] at h

/-- Logarithmic comparison: if `K₀ ≤ exp κ + 2` with `κ ≥ 0` then `log K₀ ≤ log 3 + κ`. -/
private lemma log_le_log_three_add (κ : ℝ) (hκ0 : 0 ≤ κ) (K₀ : ℕ)
    (hK₀ : (K₀ : ℝ) ≤ Real.exp κ + 2) :
    Real.log (K₀ : ℝ) ≤ Real.log 3 + κ := by
  rcases Nat.eq_zero_or_pos K₀ with h | h
  · subst h
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)]
  · have hKpos : (0 : ℝ) < (K₀ : ℝ) := by exact_mod_cast h
    have hexpκ : (1 : ℝ) ≤ Real.exp κ := Real.one_le_exp hκ0
    have h3 : (K₀ : ℝ) ≤ 3 * Real.exp κ := by linarith
    calc Real.log (K₀ : ℝ) ≤ Real.log (3 * Real.exp κ) := Real.log_le_log hKpos h3
      _ = Real.log 3 + Real.log (Real.exp κ) :=
            Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos κ))
      _ = Real.log 3 + κ := by rw [Real.log_exp]

/-- Pointwise bound for `σ ≥ 1`: `m^{-σ} ≤ 1/m`. -/
private lemma rpow_neg_le_inv {m : ℕ} {σ : ℝ} (hm : 1 ≤ m) (hσ : 1 ≤ σ) :
    (m : ℝ) ^ (-σ) ≤ ((m : ℝ))⁻¹ := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h : (m : ℝ) ^ (-σ) ≤ (m : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  rwa [Real.rpow_neg_one] at h

/-- Pointwise bound for `σ ≤ 1`: `m^{-σ} ≤ 3 e / m` whenever `m ≤ 3 exp κ`
and `(1-σ) κ ≤ 1`. -/
private lemma rpow_caseB {m : ℕ} {σ κ : ℝ} (hm : 1 ≤ m) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσκ : (1 - σ) * κ ≤ 1) (hmb : (m : ℝ) ≤ 3 * Real.exp κ) :
    (m : ℝ) ^ (-σ) ≤ 3 * Real.exp 1 * ((m : ℝ))⁻¹ := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have h1σ_nn : 0 ≤ 1 - σ := by linarith
  have h1 : (m : ℝ) ^ (1 - σ) ≤ (3 * Real.exp κ) ^ (1 - σ) :=
    Real.rpow_le_rpow (le_of_lt hmpos) hmb h1σ_nn
  have h2 : (3 * Real.exp κ) ^ (1 - σ) = (3:ℝ) ^ (1 - σ) * (Real.exp κ) ^ (1 - σ) :=
    Real.mul_rpow (by norm_num) (le_of_lt (Real.exp_pos κ))
  have h3 : (3:ℝ) ^ (1 - σ) ≤ (3:ℝ) ^ (1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (3:ℝ) by norm_num) (by linarith)
  rw [Real.rpow_one] at h3
  have h4 : (Real.exp κ) ^ (1 - σ) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos (Real.exp_pos κ), Real.log_exp]
    exact Real.exp_le_exp.mpr (by nlinarith [hσκ])
  have h5 : (m : ℝ) ^ (1 - σ) ≤ 3 * Real.exp 1 := by
    calc (m : ℝ) ^ (1 - σ) ≤ (3:ℝ) ^ (1 - σ) * (Real.exp κ) ^ (1 - σ) := by
          rw [← h2]; exact h1
      _ ≤ 3 * Real.exp 1 :=
          mul_le_mul h3 h4 (Real.rpow_nonneg (le_of_lt (Real.exp_pos κ)) _) (by norm_num)
  have e : (-σ : ℝ) = (1 - σ) + (-1) := by ring
  have hinv_nn : 0 ≤ ((m : ℝ))⁻¹ := by positivity
  rw [e, Real.rpow_add hmpos, Real.rpow_neg_one]
  calc (m : ℝ) ^ (1 - σ) * (m : ℝ)⁻¹ ≤ (3 * Real.exp 1) * (m : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right h5 hinv_nn
    _ = 3 * Real.exp 1 * ((m : ℝ))⁻¹ := by ring

/-- Elementary numerical bound: `16 ≤ e⁴`. -/
private lemma exp4_ge_sixteen : (16:ℝ) ≤ Real.exp 4 := by
  have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h4 : (2:ℝ)^4 ≤ (Real.exp 1)^4 := by gcongr
  have he : Real.exp 4 = (Real.exp 1)^4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  linarith [h4, he.symm.le, he.le]

theorem head_rpow_sum_bound {K₀ : ℕ} {σ κ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 2)
    (hκ0 : 0 ≤ κ) (hσκ : (1 - σ) * κ ≤ 1) (hK₀ : (K₀ : ℝ) ≤ Real.exp κ + 2) :
    (∑ m ∈ Finset.Icc 1 K₀, (m : ℝ) ^ (-σ)) ≤ 5 * Real.exp 4 * (2 + κ) := by
  have _hσ2' : σ ≤ 2 := hσ2
  have hlog := log_le_log_three_add κ hκ0 K₀ hK₀
  have hharm := sum_Icc_inv_le K₀
  have hexp4 := exp4_ge_sixteen
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
  have hnum1 : 1 + (Real.log 3 + κ) ≤ 5 * Real.exp 4 * (2 + κ) := by
    nlinarith [Real.exp_pos 4]
  have hnum2 : 3 * Real.exp 1 * (1 + (Real.log 3 + κ)) ≤ 5 * Real.exp 4 * (2 + κ) := by
    have hlog3nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hexp1 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    nlinarith [Real.exp_pos 4, Real.exp_pos 1, Real.log_pos (show (1:ℝ) < 3 by norm_num)]
  rcases lt_or_ge σ 1 with hσ | hσ
  · have hσge0 : (0:ℝ) ≤ σ := le_of_lt hσ0
    have hterm : ∀ m ∈ Finset.Icc 1 K₀, (m:ℝ)^(-σ) ≤ 3 * Real.exp 1 * ((m:ℝ))⁻¹ := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmle : (m:ℝ) ≤ 3 * Real.exp κ := by
        have hmK : (m:ℝ) ≤ (K₀:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).2
        have hexpκ : (1:ℝ) ≤ Real.exp κ := Real.one_le_exp hκ0
        linarith [hK₀, hmK]
      exact rpow_caseB hm1 hσge0 (le_of_lt hσ) hσκ hmle
    calc ∑ m ∈ Finset.Icc 1 K₀, (m:ℝ)^(-σ)
        ≤ ∑ m ∈ Finset.Icc 1 K₀, 3 * Real.exp 1 * ((m:ℝ))⁻¹ := Finset.sum_le_sum hterm
      _ = 3 * Real.exp 1 * ∑ m ∈ Finset.Icc 1 K₀, ((m:ℝ))⁻¹ := by
            rw [Finset.mul_sum]
      _ ≤ 3 * Real.exp 1 * (1 + Real.log (K₀:ℝ)) :=
            mul_le_mul_of_nonneg_left hharm (by positivity)
      _ ≤ 3 * Real.exp 1 * (1 + (Real.log 3 + κ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 5 * Real.exp 4 * (2 + κ) := hnum2
  · calc ∑ m ∈ Finset.Icc 1 K₀, (m:ℝ)^(-σ)
      ≤ ∑ m ∈ Finset.Icc 1 K₀, ((m:ℝ))⁻¹ :=
          Finset.sum_le_sum (fun m hm => rpow_neg_le_inv (Finset.mem_Icc.mp hm).1 hσ)
      _ ≤ 1 + Real.log (K₀:ℝ) := hharm
      _ ≤ 1 + (Real.log 3 + κ) := by linarith
      _ ≤ 5 * Real.exp 4 * (2 + κ) := hnum1

end Work.BMF.VKChain
