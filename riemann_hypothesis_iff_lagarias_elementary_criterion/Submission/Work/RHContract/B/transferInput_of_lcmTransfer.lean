import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# `Work.RHContract.B.transferInput_of_lcmTransfer`

This module proves the glue step of AREA B2: the (elementary, unconditional) transfer
inequality at `n = lcm(1..⌊x⌋)`, taken here as a hypothesis `hT` in the exact form in which
`Work.RHContract.B.lcm_transfer` states it, yields `Work.RHContract.TransferInput`, i.e.

  `PsiTailOscillation → SigmaOscillation`.

## The argument

Let `J = psiTail`, `n_x = Nat.lcmUpto ⌊x⌋`.  The transfer inequality reads

  `γ + log log log n_x − J(x) − 5/√x ≤ log (σ(n_x)/n_x)`     (`x ≥ 100`).

If `PsiTailOscillation` holds with exponent `β ∈ (0, 1/2)`, then for arbitrarily large `x` one
has `J(x) ≤ −2 x^{−β}`; for such `x` (and `x` large enough that `5/√x ≤ x^{−β}`)

  `log (σ(n_x)/n_x) ≥ γ + log log log n_x + x^{−β}`,

hence, exponentiating (`exp (log log log n) = log log n`),

  `σ(n_x)/n_x ≥ e^γ · log log n_x · exp (x^{−β}) ≥ e^γ · log log n_x · (1 + x^{−β})`.

Finally `log n_x = ψ(⌊x⌋) ≥ θ(⌊x⌋) ≥ (9/10)⌊x⌋ ≥ x/3`, so `x ≤ 3 log n_x` and therefore
`x^{−β} ≥ 3^{−β} (log n_x)^{−β} ≥ (1/3)(log n_x)^{−β}`.  Multiplying by `n_x > 0` gives

  `σ(n_x) ≥ e^γ n_x log log n_x + (e^γ/3) n_x log log n_x / (log n_x)^β`,

i.e. `SigmaOscillation` with `β` and `C = e^γ/3`; and since `x` can be taken arbitrarily large,
`n_x = lcm(1..⌊x⌋)` runs through arbitrarily large integers.

All numerics are deliberately slack (the constant is `e^γ/3` rather than the sharp `0.9 e^γ`).
-/

namespace Work.RHContract.B

noncomputable section

/-! ## Elementary auxiliary facts -/

/-- `lcm(1..m) ≥ m` for `m ≥ 1`. -/
private lemma le_lcmUpto (m : ℕ) (hm : 1 ≤ m) : m ≤ Nat.lcmUpto m := by
  have hdvd : id m ∣ (Finset.Icc 1 m).lcm id :=
    Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hm, le_refl m⟩)
  exact Nat.le_of_dvd (Nat.lcmUpto_pos m) (by simpa [Nat.lcmUpto] using hdvd)

/-- `log (lcm(1..⌊x⌋)) ≥ x/3` for `x ≥ 1530`.  Uses `log (lcm(1..m)) = ψ m` and the proved
Chebyshev bound `θ x ≥ 9x/10` (`x ≥ 1530`). -/
private lemma log_lcmUpto_ge_third (x : ℝ) (hx : 1530 ≤ x) :
    x / 3 ≤ Real.log (Nat.lcmUpto ⌊x⌋₊) := by
  have hfloor : 1530 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have h1 : (9 / 10 : ℝ) * (⌊x⌋₊ : ℝ) ≤ Chebyshev.theta (⌊x⌋₊ : ℝ) :=
    Commons.NumberTheory.Chebyshev.theta_lower_ninetenths _ (by exact_mod_cast hfloor)
  have h2 : Chebyshev.theta (⌊x⌋₊ : ℝ) ≤ Chebyshev.psi (⌊x⌋₊ : ℝ) :=
    Chebyshev.theta_le_psi _
  have h3 : Chebyshev.psi (⌊x⌋₊ : ℝ) = Real.log (Nat.lcmUpto ⌊x⌋₊) :=
    Chebyshev.psi_eq_log_lcmUpto ⌊x⌋₊
  have h4 : x - 1 ≤ (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  rw [← h3]
  linarith

/-- For `0 < β < 1/2` and `x ≥ 5^{1/(1/2-β)}` one has `5/√x ≤ x^{−β}`. -/
private lemma five_div_sqrt_le_rpow_neg (β x : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1 / 2)
    (hx : (5 : ℝ) ^ (1 / (1 / 2 - β)) ≤ x) : 5 / Real.sqrt x ≤ x ^ (-β) := by
  have hδ : 0 < 1 / 2 - β := by linarith [hβ0]
  have hxpos : 0 < x := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hx
  have hpow5 : (5 : ℝ) ≤ x ^ (1 / 2 - β) := by
    have h5 : ((5 : ℝ) ^ (1 / (1 / 2 - β))) ^ (1 / 2 - β) = 5 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5),
        show 1 / (1 / 2 - β) * (1 / 2 - β) = 1 by
          rw [one_div]; exact inv_mul_cancel₀ (ne_of_gt hδ),
        Real.rpow_one]
    rw [← h5]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hx (le_of_lt hδ)
  calc 5 / Real.sqrt x = 5 * x ^ (-(1 / 2)) := by
        rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hxpos) (1 / 2)]
    _ ≤ x ^ (1 / 2 - β) * x ^ (-(1 / 2)) :=
        mul_le_mul_of_nonneg_right hpow5 (Real.rpow_nonneg (le_of_lt hxpos) _)
    _ = x ^ ((1 / 2 - β) + -(1 / 2)) := (Real.rpow_add hxpos _ _).symm
    _ = x ^ (-β) := by rw [show (1 / 2 - β) + -(1 / 2) = -β by ring]

/-- For `0 < β < 1/2`, `0 < x`, `0 < L` and `x ≤ 3L` one has `(1/3) L^{−β} ≤ x^{−β}`. -/
private lemma third_mul_rpow_neg_le (β x L : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1 / 2)
    (hx0 : 0 < x) (hL0 : 0 < L) (hxL : x ≤ 3 * L) :
    (1 / 3) * L ^ (-β) ≤ x ^ (-β) := by
  have h3L : 0 < 3 * L := by linarith
  have h1 : x ^ β ≤ (3 * L) ^ β := Real.rpow_le_rpow (le_of_lt hx0) hxL (le_of_lt hβ0)
  have h2 : (3 * L) ^ (-β) ≤ x ^ (-β) := by
    rw [Real.rpow_neg (le_of_lt h3L), Real.rpow_neg (le_of_lt hx0)]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos h3L β) (Real.rpow_pos_of_pos hx0 β)).mpr h1
  have h3 : (1 / 3 : ℝ) ≤ 3 ^ (-β) := by
    have h3b : (3 : ℝ) ^ β ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (le_of_lt (by linarith : β < 1))
      rwa [Real.rpow_one] at h
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    simpa using (inv_le_inv₀ (by norm_num : (0 : ℝ) < 3)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) β)).mpr h3b
  calc (1 / 3) * L ^ (-β) ≤ 3 ^ (-β) * L ^ (-β) :=
        mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (le_of_lt hL0) _)
    _ = (3 * L) ^ (-β) := (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (le_of_lt hL0)).symm
    _ ≤ x ^ (-β) := h2

/-- Exponentiate the log-expansion: `exp(γ + log log log n + w) = e^γ · log log n · exp w`
for `n ≥ 100`. -/
private lemma exp_euler_add_logloglog_add (n : ℕ) (w : ℝ) (hn : 100 ≤ n) :
    Real.exp (Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (n : ℝ))) + w)
      = Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) * Real.exp w := by
  have hnR : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog100 : (1 : ℝ) < Real.log 100 := by
    have hlt : Real.exp 1 < 100 := by
      have h3 := Real.exp_one_lt_three
      linarith
    have h := Real.log_lt_log (Real.exp_pos 1) hlt
    rwa [Real.log_exp] at h
  have hlog1 : (1 : ℝ) < Real.log (n : ℝ) :=
    lt_of_lt_of_le hlog100 (Real.log_le_log (by norm_num) hnR)
  have hlog2 : (0 : ℝ) < Real.log (Real.log (n : ℝ)) := Real.log_pos hlog1
  rw [Real.exp_add, Real.exp_add, Real.exp_log hlog2]

/-! ## The core inequality at a single `x` -/

/-- If, for `x ≥ 100` and `0 < β < 1/2`, the log-expansion
`γ + log log log n + x^{−β} ≤ log(σ(n)/n)` holds at `n = lcm(1..⌊x⌋)`, and
`x/3 ≤ log n`, then `σ(n) ≥ e^γ n log log n + (e^γ/3) n log log n/(log n)^β`. -/
private lemma sigma_ge_of_log_expansion {β x : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1 / 2)
    (hx : 100 ≤ x)
    (hL : x / 3 ≤ Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ))
    (hlog : Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (Nat.lcmUpto ⌊x⌋₊)))
        + x ^ (-β) ≤ Real.log (((ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℕ) : ℝ) /
            (Nat.lcmUpto ⌊x⌋₊ : ℝ))) :
    Real.exp Real.eulerMascheroniConstant * (Nat.lcmUpto ⌊x⌋₊ : ℝ) *
        Real.log (Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ))
      + (Real.exp Real.eulerMascheroniConstant / 3) * (Nat.lcmUpto ⌊x⌋₊ : ℝ) *
        Real.log (Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ)) / (Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ)) ^ β
      ≤ ((ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℕ) : ℝ) := by
  set n : ℕ := Nat.lcmUpto ⌊x⌋₊ with hn
  have hn100 : 100 ≤ n := by
    have h1 : (100 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (show (100 : ℝ) ≤ x by linarith)
    rw [hn]
    exact le_trans h1 (le_lcmUpto _ (le_trans (by norm_num : 1 ≤ 100) h1))
  have hNpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)

  have hLpos : 0 < Real.log (n : ℝ) := by
    have h : (100 : ℝ) / 3 ≤ Real.log (n : ℝ) := le_trans (by linarith) hL
    linarith
  have hL1 : 1 < Real.log (n : ℝ) := by
    have h : (100 : ℝ) / 3 ≤ Real.log (n : ℝ) := le_trans (by linarith) hL
    linarith
  have hLLpos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hL1
  have hsigpos : 0 < (((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ)) :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n (by omega)) hNpos
  -- exponentiate the log-expansion
  have hexp := Real.exp_le_exp.mpr hlog
  rw [exp_euler_add_logloglog_add n (x ^ (-β)) hn100, Real.exp_log hsigpos] at hexp
  -- `e^γ log log n · exp(x^{−β}) ≤ σ(n)/n`
  have hone : 1 + x ^ (-β) ≤ Real.exp (x ^ (-β)) := by
    have := Real.add_one_le_exp (x ^ (-β))
    linarith
  have hstep : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) *
      (1 + x ^ (-β)) ≤ ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hone (by positivity)) hexp
  -- convert `x^{−β}` into `(log n)^{−β}`
  have hxL : x ≤ 3 * Real.log (n : ℝ) := by linarith
  have h3 : (1 / 3) * (Real.log (n : ℝ)) ^ (-β) ≤ x ^ (-β) :=
    third_mul_rpow_neg_le β x (Real.log (n : ℝ)) hβ0 hβ1 (by linarith) hLpos hxL
  have h3' : (1 / 3) * (Real.log (n : ℝ)) ^ (-β)
      = (1 / 3) / (Real.log (n : ℝ)) ^ β := by
    rw [Real.rpow_neg (le_of_lt hLpos), one_div]
    ring
  have h4 : 1 + (1 / 3) / (Real.log (n : ℝ)) ^ β ≤ 1 + x ^ (-β) := by linarith
  have h5 : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) *
      (1 + (1 / 3) / (Real.log (n : ℝ)) ^ β) ≤
        ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left h4 (by positivity)) hstep
  -- multiply by `n`
  have h6 : (n : ℝ) * (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) *
      (1 + (1 / 3) / (Real.log (n : ℝ)) ^ β)) ≤ ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left h5 (le_of_lt hNpos)
    rwa [mul_div_cancel₀ _ (ne_of_gt hNpos)] at this
  have h7 : (n : ℝ) * (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) *
      (1 + (1 / 3) / (Real.log (n : ℝ)) ^ β))
      = Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))
        + (Real.exp Real.eulerMascheroniConstant / 3) * (n : ℝ) *
          Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β := by
    ring
  linarith [h6, h7.symm.le, h7.le]

/-! ## The glue: `lcm_transfer`-shaped hypothesis implies `TransferInput` -/

/-- **AREA B2.**  The `lcm`-transfer inequality `hT` — the exact form in which
`Work.RHContract.B.lcm_transfer` states the elementary transfer at `n = lcm(1..⌊x⌋)` — implies
`TransferInput`: the oscillation `psiTail x ≤ −2x^{−β}` of `J` forces Robin's inequality to fail
infinitely often by a relative margin `C (log n)^{−β}`, namely `SigmaOscillation` with the same
exponent `β` and `C = e^γ/3`.

Only the case `x ≥ 1530` of `hT` is used, and only the one-sided information
`psiTail x ≤ −2x^{−β}` from `PsiTailOscillation`. -/
theorem transferInput_of_lcmTransfer
    (hT : ∀ x : ℝ, 100 ≤ x →
      Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (Nat.lcmUpto ⌊x⌋₊)))
          - Work.RHContract.psiTail x - 5 / Real.sqrt x
        ≤ Real.log (((ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℕ) : ℝ) /
            (Nat.lcmUpto ⌊x⌋₊ : ℝ))) :
    Work.RHContract.TransferInput := by
  intro hosc
  obtain ⟨β, hβ0, hβ1, hosc⟩ := hosc
  refine ⟨β, hβ0, hβ1, Real.exp Real.eulerMascheroniConstant / 3, by positivity, ?_⟩
  rw [Filter.frequently_atTop]
  intro N₀
  set x₀ : ℝ := max (max 100 ((N₀ : ℝ) + 1)) (max ((5 : ℝ) ^ (1 / (1 / 2 - β))) 1530) with hx₀
  obtain ⟨x, hxge, hpsi⟩ := hosc x₀
  have hA1 : (100 : ℝ) ≤ x₀ := by rw [hx₀]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hA2 : ((N₀ : ℝ) + 1) ≤ x₀ := by
    rw [hx₀]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hA3 : (5 : ℝ) ^ (1 / (1 / 2 - β)) ≤ x₀ := by
    rw [hx₀]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hA4 : (1530 : ℝ) ≤ x₀ := by rw [hx₀]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hx100 : 100 ≤ x := le_trans hA1 hxge
  have hx1530 : 1530 ≤ x := le_trans hA4 hxge
  have hx5 : (5 : ℝ) ^ (1 / (1 / 2 - β)) ≤ x := le_trans hA3 hxge
  have hN0le : (N₀ : ℝ) + 1 ≤ x := le_trans hA2 hxge
  have hT_x := hT x hx100
  have hw1 : 5 / Real.sqrt x ≤ x ^ (-β) := five_div_sqrt_le_rpow_neg β x hβ0 hβ1 hx5
  have hlog : Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (Nat.lcmUpto ⌊x⌋₊)))
      + x ^ (-β) ≤ Real.log (((ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℕ) : ℝ) /
          (Nat.lcmUpto ⌊x⌋₊ : ℝ)) := by linarith
  have hL : x / 3 ≤ Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ) := log_lcmUpto_ge_third x hx1530
  set n : ℕ := Nat.lcmUpto ⌊x⌋₊ with hn
  have hgoals := sigma_ge_of_log_expansion hβ0 hβ1 hx100 hL hlog
  refine ⟨n, ?_, hgoals⟩
  have h1 : (N₀ : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (show (N₀ : ℝ) ≤ x by linarith)
  have h100 : (100 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (show (100 : ℝ) ≤ x by linarith)
  have hpos : (1 : ℕ) ≤ ⌊x⌋₊ := le_trans (by norm_num : (1 : ℕ) ≤ 100) h100
  rw [hn]
  exact le_trans h1 (le_lcmUpto ⌊x⌋₊ hpos)

end

end Work.RHContract.B
