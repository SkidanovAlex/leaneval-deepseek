import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Work.RHContract.A.RegionIII.caRegionIIIDefs
import Submission.Work.RHContract.A.RegionIII.regionIII_basic_bounds
import Submission.Work.RHContract.A.RegionIII.regionIII_rpow_bounds
import Submission.Work.RHContract.A.RegionIII.regionIII_corr_le
import Submission.Work.RHContract.A.RegionIII.caC1_finset_reduction
import Submission.Work.RHContract.A.RegionIII.regionIII_main_bounds
import Submission.Work.RHContract.A.RegionIII.sum_prime_inv_sq_lower_A2

set_option maxRecDepth 100000
namespace Work.RHContract.A.RegionIII

/-- **`Margin.caC1 ε ≥ (44/100) · u(ξ)` in the region `ξ = caXi ε ≥ 10^8`**,
`u ξ = 1/(√ξ log ξ)` (no `RiemannHypothesis` needed: the envelope hypothesis `hA2` on
`[√ξ, ∞)` suffices).

`Margin.caC1 ε = ∑_{ξ₂ < p ≤ ξ} (1/(2p²) − 1/(3p³))` with `ξ₂ = Margin.caXi2 ε`, and
`ξ₂ ≤ √(2.5ξ) + 1` (`Work.RHContract.A.caXi2_le_sqrt`), so with `n := ⌊√(2.5ξ)⌋₊ + 1` and
`m := Work.RHPlan.caXi ε`,

`caC1 ε ≥ ∑_{n < p ≤ m} 1/(2p²) − (1/3)·∑_{n < p ≤ m} 1/p³ ≥ (1/2)·S2 − (1/3)/n²`

(primes `p` with `n < p ≤ m` satisfy `ξ₂ < p ≤ ξ`; and `∑_{p > n} 1/p³ ≤ 1/n²` because
`∑_{j ≥ n} 1/j³ ≤ 1/n³ + ∫_n^∞ dt/t³ = 1/n³ + 1/(2n²) ≤ 1/n²` for `n ≥ 2`), where
`S2 := ∑_{n < p ≤ m, p prime} 1/p²` is bounded below by
`Work.RHContract.A.RegionIII.sum_prime_inv_sq_lower_A2` (note `n ≥ ⌊√(2.5·10^8)⌋₊ + 1 = 15812 ≥ 15000`).
Take `Θ := n` when `n ≤ 10^5` (then `θ n ≤ n` by
`Commons.NumberTheory.Chebyshev.theta_bracket_finite_range`, valid on `[59,10^5]`), and
`Θ := n + (0.45 n^{3/4} + 2)` otherwise (from `hA2` at `t = n ≥ √ξ`, plus `θ ≤ ψ`).

With `L = log ξ` the numeric chain is (all powers of `ξ` are `Real.rpow`; `√ξ ≥ 10^4`,
`L ≥ 18.42`, `n ≥ √(2.5ξ) ≥ 1.58113·√ξ`, `1/log n ≤ 2/(L + 0.916)`):

* `√ξ·L/(n log n) ≥ 2L/(√2.5·(L+0.916)) ≥ 1.20498` and
  `1 − n/m − 1/log n ≥ 1 − (√(2.5ξ)+1)/ξ − 2/(L+0.916) ≥ 0.896406`,
  hence `I_low·√ξL ≥ 1.080158`, where `I_low` is the main term of the Abel estimate;
* the Abel-estimate corrections (from `sum_prime_inv_sq_lower_A2`) satisfy
  `[(0.45 m^{3/4} + 2 + 3√m)/(m² log m) + (Θ−n)/(n²log n) + 0.76/(n^{5/4}log n) + 2/(n²log n)
    + 4.25/(n^{3/2}log n)]·√ξL ≤ 0.171366`
  (each term is handled as in the sibling file `A/R3/caC1_ge`: `ξ^{-1/8} ≤ 10^{-1}`,
  `ξ^{-1/4} ≤ 10^{-2}`, `L/(L+0.916) ≤ 0.9527`; the first and third terms use
  `n ≥ 1.58113 √ξ` and the fourth uses `m = ξ`);

therefore `S2·√ξL ≥ 0.908792`, so
`caC1 ε ≥ (1/2)·0.908792/(√ξ L) = 0.454396·u(ξ) ≥ (44/100)·u(ξ)`. -/
theorem caC1_lower_regionIII (ε : ℝ) (hε : 0 < ε)
    (hξ : (10 : ℝ) ^ 8 ≤ (Work.RHPlan.caXi ε : ℝ))
    (hA2 : ∀ t : ℝ, Real.sqrt (Work.RHPlan.caXi ε : ℝ) ≤ t →
      |Chebyshev.psi t - t| ≤ 0.45 * t ^ (3 / 4 : ℝ) + 2) :
    (44 / 100) * (1 / (Real.sqrt (Work.RHPlan.caXi ε : ℝ)
        * Real.log (Work.RHPlan.caXi ε : ℝ))) ≤ Work.RHContract.Margin.caC1 ε := by
  -- ===== 0. notation and elementary consequences of `ξ ≥ 10^8` =====
  have hξ' : (10 : ℝ) ^ 8 ≤ caXiR ε := hξ
  obtain ⟨hL18, hlogn_lo, hlogn_hi, hn_lo, hn_hi, hn15000, hn_le_m, hm_le_n2⟩ :=
    regionIII_basic_bounds ε hξ'
  obtain ⟨hL8, hxi14, hxi38, hxi34, hn14, hn54, hn32⟩ := regionIII_rpow_bounds ε hξ'
  have hξpos : 0 < caXiR ε := by linarith
  have hLpos : 0 < caL ε := by linarith
  have hspos : 0 < Real.sqrt (caXiR ε) := Real.sqrt_pos_of_pos hξpos
  have hsLpos : 0 < Real.sqrt (caXiR ε) * caL ε := mul_pos hspos hLpos
  have hfloor : Real.sqrt (2.5 * caXiR ε) ≤ (caN ε : ℝ) := by
    have hcast : (caN ε : ℝ) = ((Nat.floor (Real.sqrt (2.5 * caXiR ε)) : ℕ) : ℝ) + 1 := by
      rw [caN]; push_cast; ring
    have h := Nat.lt_floor_add_one (Real.sqrt (2.5 * caXiR ε))
    rw [hcast]
    exact le_of_lt h
  have hnpos : 0 < (caN ε : ℝ) := by
    rcases Nat.eq_zero_or_pos (caN ε) with h | h
    · rw [h] at hlogn_lo ⊢
      linarith
    · exact_mod_cast h
  -- ===== 1. the envelope hypothesis, at the integer `caN ε ≥ √ξ` =====
  have hA2' : ∀ t : ℝ, (caN ε : ℝ) ≤ t →
      |Chebyshev.psi t - t| ≤ 0.45 * t ^ (3 / 4 : ℝ) + 2 := by
    intro t ht
    apply hA2 t
    change Real.sqrt (caXiR ε) ≤ t
    have h1 : Real.sqrt (caXiR ε) ≤ Real.sqrt (2.5 * caXiR ε) :=
      Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (2.5 * caXiR ε) ≤ (caN ε : ℝ) := hfloor
    linarith
  set Θ : ℝ := (caN ε : ℝ) + (0.45 * (caN ε : ℝ) ^ (3 / 4 : ℝ) + 2) with hΘdef
  have hΘ : Chebyshev.theta (caN ε : ℝ) ≤ Θ := by
    have hψ := (abs_le.mp (hA2' (caN ε : ℝ) le_rfl)).2
    have hθψ := Chebyshev.theta_le_psi (caN ε : ℝ)
    rw [hΘdef]
    linarith
  -- ===== 2. the Abel lower bound for `S2 = ∑_{n<p≤m} 1/p²` =====
  have hS2raw := sum_prime_inv_sq_lower_A2 (n := caN ε) (m := Work.RHPlan.caXi ε) (Θ := Θ)
    hn15000 hn_le_m hΘ hA2'
  have hmin : min (Work.RHPlan.caXi ε : ℝ) ((caN ε : ℝ) ^ 2) = caXiR ε :=
    min_eq_left hm_le_n2
  rw [hmin] at hS2raw
  -- ===== 3. abbreviations for the assembly =====
  set S2 : ℝ := ∑ p ∈ Finset.Ioc (caN ε) (Work.RHPlan.caXi ε),
      (if p.Prime then (1 : ℝ) / ((p : ℝ) ^ 2) else 0) with hS2def
  set M0 : ℝ := (1 / ((caN ε : ℝ) * Real.log (caN ε)))
      * (1 - (caN ε : ℝ) / caXiR ε - 1 / Real.log (caN ε)) with hM0def
  set CC : ℝ := (0.45 * caXiR ε ^ (3 / 4 : ℝ) + 2 + 3 * Real.sqrt (caXiR ε))
        / (caXiR ε ^ 2 * caL ε)
      + (Θ - (caN ε : ℝ)) / ((caN ε : ℝ) ^ 2 * Real.log (caN ε))
      + 0.76 / ((caN ε : ℝ) ^ (5 / 4 : ℝ) * Real.log (caN ε))
      + 2 / ((caN ε : ℝ) ^ 2 * Real.log (caN ε))
      + 4.25 / ((caN ε : ℝ) ^ (3 / 2 : ℝ) * Real.log (caN ε)) with hCCdef
  set sL : ℝ := Real.sqrt (caXiR ε) * caL ε with hsLdef
  set ninv : ℝ := 1 / ((caN ε : ℝ) ^ 2) with hninvdef
  have hsLpos' : 0 < sL := by rw [hsLdef]; exact hsLpos
  have hS2' : S2 ≥ M0 - CC := by
    rw [hS2def, hM0def, hCCdef]
    exact hS2raw
  have hmain' : (1.075 : ℝ) ≤ M0 * sL := by
    rw [hM0def, hsLdef]
    exact main_term_aux (ξ := caXiR ε) (L := caL ε) (n := caN ε) hξ' hL18 hlogn_lo hlogn_hi hn_hi
  have hcorr' : CC * sL ≤ 0.181 := by
    rw [hCCdef, hsLdef]
    exact regionIII_corr_le ε hξ' Θ (le_of_eq hΘdef)
  have hn2 : 2.5 * caXiR ε ≤ (caN ε : ℝ) ^ 2 := by
    have hA0 : 0 ≤ 2.5 * caXiR ε := by linarith
    have h1 : Real.sqrt (2.5 * caXiR ε) ≤ (caN ε : ℝ) := hfloor
    have h3 : Real.sqrt (2.5 * caXiR ε) ^ 2 ≤ ((caN ε : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt hA0] at h3
  have hthird' : (1 / 3) * ninv * sL ≤ 0.0011 := by
    rw [hninvdef, hsLdef]
    exact third_term_aux (ξ := caXiR ε) (L := caL ε) (n := caN ε) hξ' (le_of_lt hLpos)
      hnpos hn2 hL8 hxi38
  have hD1' : (1 / 2) * S2 - (1 / 3) * ninv ≤ Work.RHContract.Margin.caC1 ε := by
    rw [hS2def, hninvdef]
    exact caC1_finset_reduction ε hε hξ'
  -- ===== 4. the numeric assembly =====
  have hS2T : (0.894 : ℝ) ≤ S2 * sL := by
    have h1 := mul_le_mul_of_nonneg_right hS2' (le_of_lt hsLpos')
    rw [sub_mul] at h1
    linarith [h1, hmain', hcorr']
  have hthird'' : (1 / 3) * (ninv * sL) ≤ 0.0011 := by
    have heq : (1 / 3) * ninv * sL = (1 / 3) * (ninv * sL) := by ring
    rw [← heq]
    exact hthird'
  have hcaC1 : (0.44 : ℝ) ≤ Work.RHContract.Margin.caC1 ε * sL := by
    have h1 := mul_le_mul_of_nonneg_right hD1' (le_of_lt hsLpos')
    have heq : ((1 / 2) * S2 - (1 / 3) * ninv) * sL
        = (1 / 2) * (S2 * sL) - (1 / 3) * (ninv * sL) := by ring
    rw [heq] at h1
    have h3 : (0.44 : ℝ) ≤ (1 / 2) * (S2 * sL) - (1 / 3) * (ninv * sL) := by
      linarith [hS2T, hthird'']
    linarith [h1, h3]
  have hfin : (0.44 : ℝ) / sL ≤ Work.RHContract.Margin.caC1 ε := by
    rw [div_le_iff₀ hsLpos']
    linarith [hcaC1]
  have hsLeq : sL = Real.sqrt (Work.RHPlan.caXi ε : ℝ)
      * Real.log (Work.RHPlan.caXi ε : ℝ) := by
    rw [hsLdef]
    rfl
  have h44100 : (44 : ℝ) / 100 = 0.44 := by norm_num
  have hgoal : (44 / 100) * (1 / (Real.sqrt (Work.RHPlan.caXi ε : ℝ)
        * Real.log (Work.RHPlan.caXi ε : ℝ))) = 0.44 / sL := by
    rw [hsLeq, mul_one_div, h44100]
  rw [hgoal]
  exact hfin

end Work.RHContract.A.RegionIII
