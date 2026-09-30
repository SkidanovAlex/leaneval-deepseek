import Mathlib
import Submission.Work.BW.mahlerDefs
import Submission.Work.BW.mahler_num_exp
import Submission.Work.BW.mahler_num_key

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-!
# The explicit numerics behind the Blanksby–Montgomery averaging argument

This file verifies, for the parameters `A = 48/5`, `B = 54/5`, `ρ' = 1 - 1/(12N)`,
`K = ⌊B N log (12N)⌋`, `c₀ = log (1/(1-exp(-1/A)))` and `ℓ' = log (1+ρ')`, the four explicit
inequalities used in §3 of Blanksby–Montgomery (and in Baker–Wüstholz, Lemma 5).

The proof is by crude but effective roundings.  The only analytic inputs are

* `Real.log_two_lt_d9` (`log 2 < 0.6931471808`, used to dominate `ℓ'` by a rational number),
* `exp (-(5/24)) ≥ 4/5` and `exp (-(5/48)) ≤ 23/24` (from the Taylor expansion of `exp`).

All the remaining work is the floor estimate `(⌊x⌋₊ : ℝ) ≤ x` and `x - 1 < (⌊x⌋₊ : ℝ)` for
`x = (54/5) N log (12N)`, together with the elementary comparison of slopes

`(54/5)·(1/5 - 5·0.6931471808/48) ≈ 1.38021 > 1.34658 ≈ log 2 / 2 + 1`.

Note the (harmless) direction of the `c₀` term: it occurs with a minus sign on the right hand
side, so only `c₀ ≥ 0` is needed.
-/

/-- **Numerics of Blanksby–Montgomery's §3.** With `A = 48/5`, `B = 54/5`, `ρ' = 1 - 1/(12N)`
(so `R = 1/(1-ρ') = 12N`), `K = ⌊B N log(12N)⌋`, `c₀ = log (1/(1-exp(-1/A)))` and
`ℓ' = log (1+ρ')`, the following explicit inequalities hold for every `N ≥ 2`:
* `1 ≤ K`;
* `A·K ≤ 52·(2N)·log(6·(2N))` (this is `K·log M(P) ≤ 1/A` for `M(P) ≤ 1 + 1/(52 n log 6n)`,
  `n = 2N` — note `52·(2N)·log(12N) = 104 N log(12N)`);
* `exp(-1/A) ≤ ρ'`;
* `K·(exp(-2/A)/4 - ℓ'/A) > N·(ℓ'·log(12N)/2 + log(12N)) - c₀/A - exp(-2/A)/4`
  (this is the comparison of the two Fejér moments, via `ε_j ∈ [exp(-1/A), ρ']`,
  `log(1/(1-ε_j)) ≥ c₀`, `log(1+ε_j) ≤ ℓ'`, `∑ ε_j² ≥ N exp(-2/A)`, `∑ ε_j ≤ N ρ'`). -/
theorem mahler_numeric {N : ℕ} (hN : 2 ≤ N) :
    1 ≤ KK N
    ∧ A0 * (KK N : ℝ) ≤ 52 * (2*(N:ℝ)) * Real.log (6 * (2*(N:ℝ)))
    ∧ Real.exp (-(1/A0)) ≤ rhoP N
    ∧ (KK N : ℝ) * (Real.exp (-(2/A0))/4 - ellP N/A0)
        > (N:ℝ) * (ellP N * Real.log (12*(N:ℝ))/2 + Real.log (12*(N:ℝ)))
          - c0/A0 - Real.exp (-(2/A0))/4 := by
  -- the two exponential bounds and the key comparison of slopes
  have hexp24 : (4:ℝ)/5 ≤ Real.exp (-(5/24)) := mahler_num_exp.1
  have hexp48 : Real.exp (-(5/48)) ≤ (23:ℝ)/24 := mahler_num_exp.2
  -- basic facts about the parameters
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hLpos : 0 < Real.log (12*(N:ℝ)) := Real.log_pos (by linarith)
  have hlog2lt : Real.log 2 < (0.6931471808:ℝ) := Real.log_two_lt_d9
  have hlog2gt : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have hLge : (2:ℝ) * Real.log 2 ≤ Real.log (12*(N:ℝ)) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 4) (by linarith : (4:ℝ) ≤ 12*(N:ℝ))
    rw [hlog4] at h; exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `1 ≤ K = ⌊(54/5) N log (12N)⌋₊`
    show 1 ≤ ⌊(54/5) * (N:ℝ) * Real.log (12*(N:ℝ))⌋₊
    rw [Nat.one_le_floor_iff]
    have hLb : (1.386:ℝ) ≤ Real.log (12*(N:ℝ)) := by linarith
    have hNL : (11:ℝ)/4 ≤ (N:ℝ) * Real.log (12*(N:ℝ)) := by
      have h := mul_le_mul hN2 hLb (by norm_num) hNpos.le
      linarith
    linarith
  · -- `A · K ≤ 52 · (2N) · log (12N)`: since `A · B = 103.68 ≤ 104`
    rw [show 6 * (2*(N:ℝ)) = 12*(N:ℝ) by ring]
    rw [show A0 * (KK N : ℝ) = (48/5) * (⌊(54/5) * (N:ℝ) * Real.log (12*(N:ℝ))⌋₊ : ℝ)
        from rfl]
    have hx0 : (0:ℝ) ≤ (54/5) * (N:ℝ) * Real.log (12*(N:ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num) hNpos.le) hLpos.le
    have hfl := Nat.floor_le hx0
    have hNL : (0:ℝ) ≤ (N:ℝ) * Real.log (12*(N:ℝ)) := mul_nonneg hNpos.le hLpos.le
    have h2 := mul_le_mul_of_nonneg_left hfl (by norm_num : (0:ℝ) ≤ 48/5)
    nlinarith [h2, hNL]
  · -- `exp (-5/48) ≤ 23/24 ≤ 1 - 1/(12N)`
    rw [show -(1/A0) = -(5/48) by unfold A0; norm_num]
    rw [rhoP]
    have h24 : (23:ℝ)/24 ≤ 1 - 1/(12*(N:ℝ)) := by
      have hd : (1:ℝ)/(12*(N:ℝ)) ≤ 1/24 := by
        apply one_div_le_one_div_of_le (by norm_num)
        linarith
      linarith
    linarith
  · -- the comparison of the two Fejér moments
    rw [show (KK N : ℝ) = (⌊(54/5) * (N:ℝ) * Real.log (12*(N:ℝ))⌋₊ : ℝ) from rfl]
    rw [show -(2/A0) = -(5/24) by unfold A0; norm_num]
    rw [show ellP N / A0 = (5:ℝ)/48 * ellP N by unfold A0; ring]
    rw [show c0 / A0 = (5:ℝ)/48 * c0 by unfold A0; ring]
    -- floor estimates for `x = (54/5) N log (12N)`
    have hfl := Nat.sub_one_lt_floor ((54/5) * (N:ℝ) * Real.log (12*(N:ℝ)))
    have hK0 : (0:ℝ) ≤ (⌊(54/5) * (N:ℝ) * Real.log (12*(N:ℝ))⌋₊ : ℝ) := Nat.cast_nonneg _
    -- `ℓ' ≤ log 2`
    have hellP : ellP N ≤ Real.log 2 := by
      have hposN : (0:ℝ) < 1/(12*(N:ℝ)) := by positivity
      have hlt1 : (1:ℝ)/(12*(N:ℝ)) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      unfold ellP rhoP
      apply Real.log_le_log
      · linarith
      · linarith
    have hellPg : ellP N ≤ (0.6931471808:ℝ) := le_trans hellP hlog2lt.le
    -- `0 ≤ c₀`
    have hc0 : (0:ℝ) ≤ c0 := by
      have h1 : (0:ℝ) < 1 - Real.exp (-(1/A0)) := by
        have he := Real.exp_lt_one_iff.mpr (show -(1/A0) < 0 by unfold A0; norm_num)
        linarith
      have h2 : (1:ℝ) ≤ 1/(1 - Real.exp (-(1/A0))) := by
        rw [le_div_iff₀ h1]
        have := Real.exp_pos (-(1/A0))
        linarith
      exact Real.log_nonneg h2
    -- the bracket on the left is at least the slope `a = 1/5 - 5·0.6931471808/48 > 0`
    have hf : (1:ℝ)/5 - 5*(0.6931471808:ℝ)/48
        ≤ Real.exp (-(5/24))/4 - (5:ℝ)/48 * ellP N := by
      have h5 : (5:ℝ)/48 * ellP N ≤ 5*(0.6931471808:ℝ)/48 := by linarith [hellPg]
      linarith
    -- lower bound for the left hand side
    have hLHS : ((54/5)*(N:ℝ)*Real.log (12*(N:ℝ)) - 1) * ((1:ℝ)/5 - 5*(0.6931471808:ℝ)/48)
        ≤ (⌊(54/5)*(N:ℝ)*Real.log (12*(N:ℝ))⌋₊ : ℝ)
            * (Real.exp (-(5/24))/4 - (5:ℝ)/48 * ellP N) := by
      have h1 : ((54/5)*(N:ℝ)*Real.log (12*(N:ℝ)) - 1) * ((1:ℝ)/5 - 5*(0.6931471808:ℝ)/48)
          ≤ (⌊(54/5)*(N:ℝ)*Real.log (12*(N:ℝ))⌋₊ : ℝ)
              * ((1:ℝ)/5 - 5*(0.6931471808:ℝ)/48) :=
        mul_le_mul_of_nonneg_right hfl.le (by norm_num)
      have h2 : (⌊(54/5)*(N:ℝ)*Real.log (12*(N:ℝ))⌋₊ : ℝ) * ((1:ℝ)/5 - 5*(0.6931471808:ℝ)/48)
          ≤ (⌊(54/5)*(N:ℝ)*Real.log (12*(N:ℝ))⌋₊ : ℝ)
              * (Real.exp (-(5/24))/4 - (5:ℝ)/48 * ellP N) :=
        mul_le_mul_of_nonneg_left hf hK0
      linarith
    -- upper bound for the right hand side
    have hRHS : (N:ℝ) * (ellP N * Real.log (12*(N:ℝ))/2 + Real.log (12*(N:ℝ)))
          - (5:ℝ)/48 * c0 - Real.exp (-(5/24))/4
        ≤ (Real.log 2 / 2 + 1) * (N:ℝ) * Real.log (12*(N:ℝ)) - (1:ℝ)/5 := by
      have h1 : ellP N * Real.log (12*(N:ℝ))/2 ≤ Real.log 2 * Real.log (12*(N:ℝ))/2 := by
        have := mul_le_mul_of_nonneg_right hellP hLpos.le
        linarith
      have h1' : (N:ℝ) * (ellP N * Real.log (12*(N:ℝ))/2 + Real.log (12*(N:ℝ)))
          ≤ (N:ℝ) * (Real.log 2 * Real.log (12*(N:ℝ))/2 + Real.log (12*(N:ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hNpos.le
      have h4 : (0:ℝ) ≤ (5:ℝ)/48 * c0 := by linarith [hc0]
      have h3 : (1:ℝ)/5 ≤ Real.exp (-(5/24))/4 := by linarith
      linarith
    -- the comparison of slopes
    have hk : (Real.log 2 / 2 + 1) * (N:ℝ) * Real.log (12*(N:ℝ)) - 1/5
        < ((54/5) * (N:ℝ) * Real.log (12*(N:ℝ)) - 1) * (1/5 - 5 * 0.6931471808 / 48) :=
      mahler_num_key hNpos hLpos
    linarith

end Work.BW
