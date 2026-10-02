/-
# The Böttcher coordinate commutes with the holomorphic second iterate

`p_c = T_c ∘ T_c` is the monic quartic `p_c(z) = (z² + conj c)² + c`, and the Böttcher
coordinate of a monic degree-`4` map satisfies `φ ∘ p_c = φ^4`.  Since `bottcher c` is
*defined* here by the product formula

`φ_c(z) = z · exp (Σ_n 4^{-(n+1)} log (p_c^n z / (p_c^n z)^4))`,

the functional equation is proved by comparing the defining series: the terms of the series
of `p_c z` are `4` times the shifted terms of the series of `z`, so

`bottcherSeries c (p_c z) = 4 · bottcherSeries c z - log (p_c z / z^4)`,

and then `φ_c(p_c z) = p_c z · exp (… ) = (p_c z / (p_c z / z^4)) · exp (… )^4 = φ_c(z)^4`.

The summability of the defining series is proved for an escaping orbit, using that the
normalising factor `p_c w / w^4 = 1 + O(1/w²)` tends to `1`, so its logarithm is bounded
along the orbit while the coefficients `4^{-(n+1)}` decay geometrically.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Bottcher.Core.tendsto_normFactor_pMap_iterate
import Submission.Work.Bottcher.Series.summable_quarterPow_log

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology

namespace Work.Bottcher.Core

/-! ## Arithmetic of the coefficients `4^{-(n+1)}` -/

/-- `4^{-(n+1)} = 4 · 4^{-(n+2)}`: shifting the index of the Böttcher series by one multiplies
the coefficient by `4`. -/
lemma quarter_pow_succ (n : ℕ) :
    (↑(1 / 4 : ℝ) : ℂ) ^ (n + 1) = 4 * (↑(1 / 4 : ℝ) : ℂ) ^ (n + 1 + 1) := by
  have h : (↑(1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by norm_num
  rw [h, pow_succ]
  ring

/-- The `n`-th Böttcher term of `p_c z` is `4` times the `(n+1)`-st Böttcher term of `z`. -/
lemma bottcherTerm_pMap_eq (c z : ℂ) (n : ℕ) :
    Work.Bottcher.bottcherTerm c n (Work.Bottcher.pMap c z)
      = 4 * Work.Bottcher.bottcherTerm c (n + 1) z := by
  have hiter : (Work.Bottcher.pMap c)^[n+1] z = (Work.Bottcher.pMap c)^[n] (Work.Bottcher.pMap c z) :=
    Function.iterate_succ_apply _ _ _
  simp only [Work.Bottcher.bottcherTerm]
  rw [hiter]
  rw [quarter_pow_succ n]
  ring

/-- The `0`-th Böttcher term recovers `log` of the normalisation factor. -/
lemma four_mul_bottcherTerm_zero (c z : ℂ) :
    4 * Work.Bottcher.bottcherTerm c 0 z = Complex.log (Work.Bottcher.normFactor c z) := by
  simp [Work.Bottcher.bottcherTerm]

/-! ## The Böttcher series of `p_c z` -/

/-- **Shift of the Böttcher series.**  If the Böttcher series of `z` converges, then the series
of `p_c z` is `4 ×` the series of `z` shifted by one, i.e.
`Σ_n 4^{-(n+1)} log (p_c^{n+1} z / (p_c^{n+1} z)^4) = 4 · (Σ_n … - 4^{-1} log (p_c z / z^4))`. -/
lemma bottcherSeries_pMap (c z : ℂ)
    (hsum : Summable (fun n : ℕ => Work.Bottcher.bottcherTerm c n z)) :
    Work.Bottcher.bottcherSeries c (Work.Bottcher.pMap c z)
      = 4 * Work.Bottcher.bottcherSeries c z - Complex.log (Work.Bottcher.normFactor c z) := by
  have hshift : ∑' n : ℕ, Work.Bottcher.bottcherTerm c (n + 1) z
      = (∑' n : ℕ, Work.Bottcher.bottcherTerm c n z) - Work.Bottcher.bottcherTerm c 0 z := by
    have h := Summable.sum_add_tsum_nat_add (f := fun n : ℕ => Work.Bottcher.bottcherTerm c n z)
      1 hsum
    simp only [Finset.sum_range_one] at h
    rw [← h]
    abel
  calc Work.Bottcher.bottcherSeries c (Work.Bottcher.pMap c z)
      = ∑' n : ℕ, Work.Bottcher.bottcherTerm c n (Work.Bottcher.pMap c z) := rfl
    _ = ∑' n : ℕ, 4 * Work.Bottcher.bottcherTerm c (n + 1) z :=
          tsum_congr fun n => bottcherTerm_pMap_eq c z n
    _ = 4 * ∑' n : ℕ, Work.Bottcher.bottcherTerm c (n + 1) z := tsum_mul_left
    _ = 4 * ((∑' n : ℕ, Work.Bottcher.bottcherTerm c n z) - Work.Bottcher.bottcherTerm c 0 z) := by
          rw [hshift]
    _ = 4 * (∑' n : ℕ, Work.Bottcher.bottcherTerm c n z) - Complex.log (Work.Bottcher.normFactor c z) := by
          rw [mul_sub, four_mul_bottcherTerm_zero]
    _ = 4 * Work.Bottcher.bottcherSeries c z - Complex.log (Work.Bottcher.normFactor c z) := rfl

/-! ## The functional equation -/

theorem bottcher_comm_pMap (c z : ℂ)
    (h : Filter.Tendsto (fun n : ℕ => ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖) Filter.atTop Filter.atTop)
    (hz : ∀ n : ℕ, (Work.Bottcher.pMap c)^[n] z ≠ 0) :
    Work.Bottcher.bottcher c (Work.Bottcher.pMap c z) = (Work.Bottcher.bottcher c z) ^ 4 := by
  have hsum : Summable (fun n : ℕ => Work.Bottcher.bottcherTerm c n z) := by
    have hnf : Filter.Tendsto
        (fun n : ℕ => Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z))
        Filter.atTop (nhds 1) :=
      tendsto_normFactor_pMap_iterate c z h
    have hB := Work.Bottcher.Series.summable_quarterPow_log
      (fun n : ℕ => Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z)) hnf
    simpa only [Work.Bottcher.bottcherTerm, Complex.ofReal_pow] using hB
  have hz0 : z ≠ 0 := by simpa using hz 0
  have hpz : Work.Bottcher.pMap c z ≠ 0 := by simpa using hz 1
  have hnf : Work.Bottcher.normFactor c z ≠ 0 := by
    rw [Work.Bottcher.normFactor]
    exact div_ne_zero hpz (pow_ne_zero 4 hz0)
  have hdiv : Work.Bottcher.pMap c z / Work.Bottcher.normFactor c z = z^4 := by
    rw [Work.Bottcher.normFactor, div_div_eq_mul_div, mul_comm (Work.Bottcher.pMap c z) (z^4),
      mul_div_assoc, div_self hpz, mul_one]
  have hexp : Complex.exp (4 * Work.Bottcher.bottcherSeries c z)
      = Complex.exp (Work.Bottcher.bottcherSeries c z)^4 := by
    rw [show (4:ℂ) = ((4:ℕ):ℂ) by norm_num, Complex.exp_nat_mul]
  rw [Work.Bottcher.bottcher, Work.Bottcher.bottcher, bottcherSeries_pMap c z hsum,
    Complex.exp_sub, Complex.exp_log hnf, hexp, mul_pow]
  calc Work.Bottcher.pMap c z * (Complex.exp (Work.Bottcher.bottcherSeries c z) ^ 4
          / Work.Bottcher.normFactor c z)
      = (Work.Bottcher.pMap c z / Work.Bottcher.normFactor c z)
          * Complex.exp (Work.Bottcher.bottcherSeries c z) ^ 4 := by ring
    _ = z^4 * Complex.exp (Work.Bottcher.bottcherSeries c z) ^ 4 := by rw [hdiv]

end Work.Bottcher.Core
