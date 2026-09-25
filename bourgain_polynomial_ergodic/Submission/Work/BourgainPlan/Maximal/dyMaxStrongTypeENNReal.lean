import Mathlib
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

namespace Work.BourgainPlan.Maximal

open MeasureTheory

/-- **Strong `(q,q)` type (`q > 1`) of the dyadic maximal function, `ENNReal` form.**

For every `q > 1` there is `C > 0` with
`∫⁻ x, (dyMax ψ x)^q ≤ ofReal (C^q) * ∫⁻ x, (ψ x)^q`
for every measurable `ψ : ℝ → ENNReal` taking only finite values.

The proof is the composition of the elementary domination `dyMax ≤ hlMax` with the `L^q` bound
`Commons.Analysis.Maximal.lintegral_rpow_hlMax_le` for the centred Hardy--Littlewood maximal
function (constant `8 q 2^{q-1}/(q-1)`, raised to the power `1/q`). When `∫⁻ ψ^q = ⊤` the
inequality is vacuous, since the right side is then `⊤`. -/
theorem dyMaxStrongTypeENNReal {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ENNReal), Measurable ψ → (∀ x, ψ x ≠ ⊤) →
      ∫⁻ x, (Work.BourgainPlan.Maximal.dyMax ψ x) ^ q ≤ ENNReal.ofReal (C ^ q) * ∫⁻ x, ψ x ^ q := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hq1 : 0 < q - 1 := by linarith
  have h2pos : (0 : ℝ) < 2 ^ (q - 1) := Real.rpow_pos_of_pos (by norm_num) _
  set K : ℝ := 8 * q * 2 ^ (q - 1) / (q - 1) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  refine ⟨K ^ (1 / q), Real.rpow_pos_of_pos hKpos _, fun ψ hψmeas hψfin => ?_⟩
  have hCq : (K ^ (1 / q)) ^ q = K := by
    rw [← Real.rpow_mul hKpos.le, one_div, inv_mul_cancel₀ hq0.ne', Real.rpow_one]
  by_cases htop : ∫⁻ x, ψ x ^ q = ⊤
  · rw [htop, ENNReal.mul_top]
    · exact le_top
    · rw [hCq]
      exact (ENNReal.ofReal_pos.mpr hKpos).ne'
  · have hH : ∫⁻ x, ENNReal.rpow (ψ x) q < ⊤ := lt_top_iff_ne_top.mpr htop
    have h1 : ∫⁻ x, (dyMax ψ x) ^ q ≤ ∫⁻ x, (Commons.Analysis.Maximal.hlMax ψ x) ^ q :=
      lintegral_mono fun x => ENNReal.rpow_le_rpow (dyMax_le_hlMax ψ x) hq0.le
    have h2 := Commons.Analysis.Maximal.lintegral_rpow_hlMax_le hψmeas hψfin hq hH
    calc ∫⁻ x, (dyMax ψ x) ^ q
        ≤ ∫⁻ x, (Commons.Analysis.Maximal.hlMax ψ x) ^ q := h1
      _ ≤ ENNReal.ofReal (8 * q * 2 ^ (q - 1) / (q - 1)) * ∫⁻ x, ENNReal.rpow (ψ x) q := h2
      _ = ENNReal.ofReal ((K ^ (1 / q)) ^ q) * ∫⁻ x, ENNReal.rpow (ψ x) q := by
            rw [hCq, hK]

end Work.BourgainPlan.Maximal
