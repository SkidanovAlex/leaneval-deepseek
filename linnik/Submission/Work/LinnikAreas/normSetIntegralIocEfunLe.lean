import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

/-- `‖x^{-β}‖ = x^{-β}` for the complex power, and hence the crude bound on `Efun` integrates:
for `1 ≤ x` and `1/2 < β < 1`,
`‖∫_1^x E(t) t^{-β} dt‖ ≤ K (x^{3/2-β} - 1)/(3/2 - β)`
whenever `‖E(t)‖ ≤ K √t` for `t ≥ 1`. -/
theorem normSetIntegralIocEfunLe {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {K β : ℝ} (hK : 0 ≤ K)
    (hE : ∀ t : ℝ, 1 ≤ t → ‖Work.LinnikAreas.Efun χ t‖ ≤ K * Real.sqrt t)
    (hβ : 1/2 < β) (hβ1 : β < 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖∫ t in Set.Ioc (1:ℝ) x, Work.LinnikAreas.Efun χ t * (t : ℂ) ^ (-(β : ℂ))‖
      ≤ K * (x ^ (3/2 - β) - 1) / (3/2 - β) := by
  -- Exponent facts.
  have hc : -1 < (1/2 : ℝ) - β := by linarith
  have hcx : (1/2 : ℝ) - β + 1 = 3/2 - β := by ring
  -- Pointwise bound on `(1, x]`: `‖E(t) t^{-β}‖ ≤ K t^{1/2-β}`.
  have hpt : ∀ t ∈ Set.Ioc (1:ℝ) x,
      ‖Efun χ t * (t : ℂ) ^ (-(β : ℂ))‖ ≤ K * t ^ (1/2 - β) := by
    intro t ht
    rw [Set.mem_Ioc] at ht
    obtain ⟨ht1, _⟩ := ht
    have ht1' : (1:ℝ) ≤ t := le_of_lt ht1
    have htpos : (0:ℝ) < t := by linarith
    have hcpow : ‖(t : ℂ) ^ (-(β : ℂ))‖ = t ^ (-β) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos]
      simp
    rw [norm_mul, hcpow]
    calc ‖Efun χ t‖ * t ^ (-β)
        ≤ (K * Real.sqrt t) * t ^ (-β) :=
          mul_le_mul_of_nonneg_right (hE t ht1') (Real.rpow_nonneg htpos.le (-β))
      _ = K * t ^ (1/2 - β) := by
          rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add htpos (1/2) (-β)]
          rw [show (1:ℝ)/2 + -β = 1/2 - β by ring]
  rw [← intervalIntegral.integral_of_le hx]
  have hbound : IntervalIntegrable (fun t : ℝ => K * t ^ (1/2 - β)) MeasureTheory.volume (1:ℝ) x :=
    (intervalIntegral.intervalIntegrable_rpow' hc).const_mul K
  calc ‖∫ t in (1:ℝ)..x, Efun χ t * (t : ℂ) ^ (-(β : ℂ))‖
      ≤ ∫ t in (1:ℝ)..x, K * t ^ (1/2 - β) :=
        intervalIntegral.norm_integral_le_of_norm_le hx
          (Filter.Eventually.of_forall fun t ht => hpt t ht) hbound
    _ = K * ∫ t in (1:ℝ)..x, t ^ (1/2 - β) := by
        rw [intervalIntegral.integral_const_mul]
    _ = K * (x ^ (3/2 - β) - 1) / (3/2 - β) := by
        rw [integral_rpow (Or.inl hc), Real.one_rpow, hcx]
        ring

end Work.LinnikAreas
