import Mathlib
import Submission.Work.BMF.pcsw.tendsto_id_sub_rpow
import Submission.Work.BMF.pcsw.tendsto_mul_exp_sub_rpow
import Submission.Work.BMF.pcsw.tendsto_exp_neg_rpow_div

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

/-- **Sub-polynomial absorption.** For `c > 0` and `K ≥ 0` there is `P₀ ≥ 8` such that for
`P ≥ P₀` the constant term, the `√P log P` term, and the two exponentially decaying terms
`P e^{-c (log P)^{1/12}} / log P` and `P e^{-c (log P)^{1/12}} / (log P)^2` are dominated by
`(K+1) P e^{-(c/2)(log P)^{1/12}}`.

Route: elementary, put `L = Real.log P` and `r = L^(1/12)`, both positive for `P ≥ 8`.
The right-hand side is `(K+1)·exp(L − (c/2) r)`, which tends to `+∞`; all four left-hand terms
have ratio to it tending to `0`:
- `1 / (P e^{-(c/2) r}) = exp(-L + (c/2) r) ≤ exp(-L/2)` once `(c/2) r ≤ L/2`;
- `√P log P / (P e^{-(c/2)r}) = exp(-L/2 + log log P + (c/2) r) ≤ exp(-L/4)` once
  `log log P ≤ L/4` and `(c/2) r ≤ L/4`;
- the two last terms give `exp(-(c/2) r) / L` resp. `/L²` times `K/(K+1)`, and
  `exp(-(c/2)r)/L ≤ exp(-(c/4) r)` once `(c/4) r ≥ log L`.
Each of the conditions `(c/4)(log P)^{1/12} ≥ log L`, `log log P ≤ L/4`,
`(c/2)(log P)^{1/12} ≤ L/2` holds for all large `P` because `log P / (log P)^{1/12} → ∞` and
`log log P / log P → 0`; extract an explicit `P₀` with
`Filter.eventually_ge_atTop`/`Filter.Tendsto.eventually` (or `Real.tendsto_log_atTop`,
`Real.tendsto_log_div_rpow_atTop`-type limits) and take the max with `8`; the `K`-factors are
absorbed by the `(K+1)` prefactor. -/
theorem absorb_terms (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ P₀ : ℝ, 8 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      1 + K * (Real.sqrt P * Real.log P)
          + K * (P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ)) / Real.log P)
          + K * (P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ)) / (Real.log P) ^ 2)
        ≤ (K + 1) * P * Real.exp (-(c / 2) * Real.log P ^ (1 / 12 : ℝ)) := by
  have hc2 : 0 < c / 2 := by linarith
  have hm1 : (0 : ℝ) < 1 / 4 := by norm_num
  -- The four "eventually" facts, phrased for the variable `t = log P`.
  have e1 := (tendsto_id_sub_rpow (c / 2) hc2).eventually
    (Filter.eventually_ge_atTop (Real.log 4))
  have e2 := (tendsto_mul_exp_sub_rpow (c / 2) hc2).eventually (eventually_le_nhds hm1)
  have e3 := (tendsto_exp_neg_rpow_div (c / 2) hc2).eventually (eventually_le_nhds hm1)
  have hE : ∀ᶠ t in Filter.atTop,
      Real.log 4 ≤ t - (c / 2) * t ^ (1 / 12 : ℝ) ∧
      t * Real.exp (-t / 2 + (c / 2) * t ^ (1 / 12 : ℝ)) ≤ 1 / 4 ∧
      Real.exp (-(c / 2) * t ^ (1 / 12 : ℝ)) / t ≤ 1 / 4 := by
    filter_upwards [e1, e2, e3] with t ht1 ht2 ht3
    exact ⟨ht1, ht2, ht3⟩
  have hE' := Real.tendsto_log_atTop.eventually hE
  obtain ⟨P₁, hP₁⟩ := Filter.eventually_atTop.mp hE'
  refine ⟨max P₁ 8, le_max_right _ _, ?_⟩
  intro P hP
  have hPP₁ : P₁ ≤ P := le_trans (le_max_left _ _) hP
  have hP8 : (8 : ℝ) ≤ P := le_trans (le_max_right _ _) hP
  obtain ⟨hlog4, hmul, hdiv1⟩ := hP₁ P hPP₁
  have hPpos : 0 < P := by linarith
  set L := Real.log P with hL
  set r := L ^ (1 / 12 : ℝ) with hr
  have hexpL : Real.exp L = P := by rw [hL, Real.exp_log hPpos]
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hL1 : 1 ≤ L := by
    rw [hL]
    have h8 : Real.log 8 ≤ Real.log P := Real.log_le_log (by norm_num) hP8
    have h1 : (1 : ℝ) ≤ Real.log 8 :=
      (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 8)).mpr
        (by linarith [Real.exp_one_lt_three])
    linarith
  have hsqrt : Real.sqrt P = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hPpos]
    congr 1
    rw [← hL]; ring
  -- The fourth eventual fact: `L ≥ 1` so `1/L² ≤ 1/L`.
  have hdiv2 : Real.exp (-(c / 2) * r) / L ^ 2 ≤ 1 / 4 := by
    have hL2 : L ≤ L ^ 2 := by nlinarith [hL1, hLpos]
    have hstep : Real.exp (-(c / 2) * r) / L ^ 2 ≤ Real.exp (-(c / 2) * r) / L :=
      div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) hLpos hL2
    linarith [hstep, hdiv1]
  set A := (K + 1) * P * Real.exp (-(c / 2) * r) with hA
  have hK1pos : (0 : ℝ) < K + 1 := by linarith
  have hApos : 0 < A := by
    rw [hA]
    exact mul_pos (mul_pos hK1pos hPpos) (Real.exp_pos _)
  have hAnonneg : 0 ≤ A := le_of_lt hApos
  -- Exponential identities.
  have hexpPe : Real.exp (L - (c / 2) * r) = P * Real.exp (-(c / 2) * r) := by
    rw [Real.exp_sub, hexpL, div_eq_mul_inv, ← Real.exp_neg]
    have harg : -((c / 2) * r) = -(c / 2) * r := by ring
    rw [harg]
  have hexp2 : Real.exp (L / 2) =
      Real.exp L * Real.exp (-(c / 2) * r) * Real.exp (-L / 2 + (c / 2) * r) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexp_cr : Real.exp (-c * r) =
      Real.exp (-(c / 2) * r) * Real.exp (-(c / 2) * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  -- (1) the constant term
  have hb1 : 1 ≤ A / 4 := by
    have hPe4 : 4 ≤ P * Real.exp (-(c / 2) * r) := by
      have h1 : Real.exp (Real.log 4) ≤ Real.exp (L - (c / 2) * r) :=
        Real.exp_le_exp.mpr hlog4
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at h1
      rwa [hexpPe] at h1
    have hK1 : (1 : ℝ) ≤ K + 1 := by linarith
    rw [hA]
    nlinarith [hPe4, hK1]
  -- (2) the `√P log P` term
  have hb2 : K * (Real.sqrt P * L) ≤ A / 4 := by
    have hs : (0 : ℝ) ≤ Real.sqrt P * L := by positivity
    have hKL : K * (Real.sqrt P * L) ≤ (K + 1) * (Real.sqrt P * L) :=
      mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) hs
    have hkey : (K + 1) * (Real.sqrt P * L) =
        A * (L * Real.exp (-L / 2 + (c / 2) * r)) := by
      rw [hsqrt, hA, ← hexpL, hexp2]
      ring
    calc K * (Real.sqrt P * L)
        ≤ (K + 1) * (Real.sqrt P * L) := hKL
      _ = A * (L * Real.exp (-L / 2 + (c / 2) * r)) := hkey
      _ ≤ A * (1 / 4) := mul_le_mul_of_nonneg_left hmul hAnonneg
      _ = A / 4 := by ring
  -- (3) the `P e^{-c r}/L` term
  have hb3 : K * (P * Real.exp (-c * r) / L) ≤ A / 4 := by
    have hn : (0 : ℝ) ≤ P * Real.exp (-c * r) / L := by positivity
    calc K * (P * Real.exp (-c * r) / L)
        ≤ (K + 1) * (P * Real.exp (-c * r) / L) :=
          mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) hn
      _ = A * (Real.exp (-(c / 2) * r) / L) := by
            rw [hA, hexp_cr]; ring_nf
      _ ≤ A * (1 / 4) := mul_le_mul_of_nonneg_left hdiv1 hAnonneg
      _ = A / 4 := by ring
  -- (4) the `P e^{-c r}/L²` term
  have hb4 : K * (P * Real.exp (-c * r) / L ^ 2) ≤ A / 4 := by
    have hn : (0 : ℝ) ≤ P * Real.exp (-c * r) / L ^ 2 := by positivity
    calc K * (P * Real.exp (-c * r) / L ^ 2)
        ≤ (K + 1) * (P * Real.exp (-c * r) / L ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) hn
      _ = A * (Real.exp (-(c / 2) * r) / L ^ 2) := by
            rw [hA, hexp_cr]; ring_nf
      _ ≤ A * (1 / 4) := mul_le_mul_of_nonneg_left hdiv2 hAnonneg
      _ = A / 4 := by ring
  linarith [hb1, hb2, hb3, hb4]

end Work.BMF.pcsw
