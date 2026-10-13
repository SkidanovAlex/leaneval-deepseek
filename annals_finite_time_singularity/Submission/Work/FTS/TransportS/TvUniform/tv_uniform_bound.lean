import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.TransportS.TvUniform.csc_sqrt_specialise
import Submission.Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le
import Submission.Work.FTS.TransportS.TvUniform.exists_min_le_average

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.TvUniform

open MeasureTheory

/-- `sin (2θ) ≥ 0` on the interval `[0, π/2]`. -/
theorem sin_two_nonneg_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- For `0 ≤ a ≤ b ≤ π/2`, the interval integral over `[a,b]` of a nonnegative function is at
most its set integral over `Icc 0 (π/2)`. -/
theorem intervalIntegral_le_setIntegral {p : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2)
    (hpnn : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), 0 ≤ p θ)
    (hpint : IntegrableOn p (Set.Icc 0 (Real.pi / 2))) :
    ∫ θ in a..b, p θ ≤ ∫ θ in Set.Icc 0 (Real.pi / 2), p θ := by
  rw [intervalIntegral.integral_of_le hab]
  refine MeasureTheory.setIntegral_mono_set hpint ?_ ?_
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpnn
  · exact Filter.Eventually.of_forall fun x hx =>
      ⟨le_trans ha hx.1.le, le_trans hx.2 hb⟩

/-- **The total-variation bound, integrated form.**  If on the open interval `(a,b) ⊆ (0,π/2)` a
function `F` coincides with `2·(√p)·(√q)`, then its interval integral is at most
`2√(∫_{Icc 0 (π/2)} p · ∫_{Icc 0 (π/2)} q)`.  This is Cauchy–Schwarz for the two factors. -/
theorem integral_tv_le {F p q : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2)
    (hFpq : Set.EqOn F (fun θ => 2 * (Real.sqrt (p θ) * Real.sqrt (q θ))) (Set.Ioo a b))
    (hpnn : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), 0 ≤ p θ)
    (hqnn : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), 0 ≤ q θ)
    (hpint : IntegrableOn p (Set.Icc 0 (Real.pi / 2)))
    (hqint : IntegrableOn q (Set.Icc 0 (Real.pi / 2))) :
    ∫ θ in a..b, F θ
      ≤ 2 * Real.sqrt ((∫ θ in Set.Icc 0 (Real.pi / 2), p θ)
          * (∫ θ in Set.Icc 0 (Real.pi / 2), q θ)) := by
  have hsub : Set.Ioc a b ⊆ Set.Icc 0 (Real.pi / 2) := fun x hx =>
    ⟨le_trans ha hx.1.le, le_trans hx.2 hb⟩
  have hpI : IntegrableOn p (Set.Ioc a b) := hpint.mono_set hsub
  have hqI : IntegrableOn q (Set.Ioc a b) := hqint.mono_set hsub
  have hpn' : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] p :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hpnn x (hsub hx)
  have hqn' : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] q :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hqnn x (hsub hx)
  -- Cauchy–Schwarz on the interval
  have hCS := integral_sqrt_mul_sqrt_le (volume.restrict (Set.Ioc a b)) hpn' hqn' hpI hqI
  have hCS' : ∫ θ in Set.Ioc a b, Real.sqrt (p θ) * Real.sqrt (q θ)
      ≤ Real.sqrt (∫ θ in Set.Ioc a b, p θ) * Real.sqrt (∫ θ in Set.Ioc a b, q θ) := hCS
  -- comparison of the integrals with the integrals over `Icc 0 (π/2)`
  have hIp : ∫ θ in a..b, p θ ≤ ∫ θ in Set.Icc 0 (Real.pi / 2), p θ :=
    intervalIntegral_le_setIntegral ha hab hb hpnn hpint
  have hIq : ∫ θ in a..b, q θ ≤ ∫ θ in Set.Icc 0 (Real.pi / 2), q θ :=
    intervalIntegral_le_setIntegral ha hab hb hqnn hqint
  have hIp' : ∫ θ in Set.Ioc a b, p θ ≤ ∫ θ in Set.Icc 0 (Real.pi / 2), p θ := by
    rw [← intervalIntegral.integral_of_le hab]; exact hIp
  have hIq' : ∫ θ in Set.Ioc a b, q θ ≤ ∫ θ in Set.Icc 0 (Real.pi / 2), q θ := by
    rw [← intervalIntegral.integral_of_le hab]; exact hIq
  have hp0 : 0 ≤ ∫ θ in Set.Ioc a b, p θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun x hx => hpnn x (hsub hx)
  have hq0 : 0 ≤ ∫ θ in Set.Ioc a b, q θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun x hx => hqnn x (hsub hx)
  have hA0 : 0 ≤ ∫ θ in Set.Icc 0 (Real.pi / 2), p θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc hpnn
  have hstep : ∫ θ in Set.Ioc a b, Real.sqrt (p θ) * Real.sqrt (q θ)
      ≤ Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2), p θ)
        * Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2), q θ) :=
    le_trans hCS' (mul_le_mul (Real.sqrt_le_sqrt hIp') (Real.sqrt_le_sqrt hIq')
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hcongr : ∫ θ in a..b, F θ
      = ∫ θ in a..b, 2 * (Real.sqrt (p θ) * Real.sqrt (q θ)) :=
    intervalIntegral.integral_congr_Ioo_of_le hab hFpq
  rw [hcongr, intervalIntegral.integral_const_mul]
  calc 2 * ∫ θ in a..b, Real.sqrt (p θ) * Real.sqrt (q θ)
      = 2 * ∫ θ in Set.Ioc a b, Real.sqrt (p θ) * Real.sqrt (q θ) := by
        rw [intervalIntegral.integral_of_le hab]
    _ ≤ 2 * (Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2), p θ)
          * Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2), q θ)) := by
        exact mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 2 * Real.sqrt ((∫ θ in Set.Icc 0 (Real.pi / 2), p θ)
          * (∫ θ in Set.Icc 0 (Real.pi / 2), q θ)) := by rw [Real.sqrt_mul hA0]

theorem tv_uniform_bound {Ξ Ξ₁ : ℝ → ℝ} {c : ℝ}
    (hcont : ContinuousOn Ξ (Set.Icc 0 (Real.pi / 2)))
    (hΞnn : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), 0 ≤ Ξ θ)
    (hΞ₁nn : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), 0 ≤ Ξ₁ θ)
    (hTV : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      |Ξ b - Ξ a| ≤ ∫ θ in a..b, 2 * (Real.sin (2 * θ))⁻¹ * Real.sqrt (Ξ θ * Ξ₁ θ))
    (hintΞ : MeasureTheory.IntegrableOn Ξ (Set.Icc 0 (Real.pi / 2)))
    (hintA : MeasureTheory.IntegrableOn
      (fun θ => Ξ θ * (Real.sin (2 * θ)) ^ (-c)) (Set.Icc 0 (Real.pi / 2)))
    (hintB : MeasureTheory.IntegrableOn
      (fun θ => Ξ₁ θ * (Real.sin (2 * θ)) ^ (c - 2)) (Set.Icc 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      Ξ θ ≤ (2 / Real.pi) * (∫ θ in Set.Icc 0 (Real.pi / 2), Ξ θ)
        + 2 * Real.sqrt
            ((∫ θ in Set.Icc 0 (Real.pi / 2), Ξ θ * (Real.sin (2 * θ)) ^ (-c))
              * (∫ θ in Set.Icc 0 (Real.pi / 2), Ξ₁ θ * (Real.sin (2 * θ)) ^ (c - 2))) := by
  intro θ hθI
  obtain ⟨θ₀, hθ₀I, hθ₀le⟩ := exists_min_le_average hcont hintΞ
  -- nonnegativity of the two weighted profiles
  have hpnn : ∀ σ ∈ Set.Icc 0 (Real.pi / 2),
      0 ≤ Ξ σ * (Real.sin (2 * σ)) ^ (-c) := fun σ hσ =>
    mul_nonneg (hΞnn σ hσ) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Icc hσ) _)
  have hqnn : ∀ σ ∈ Set.Icc 0 (Real.pi / 2),
      0 ≤ Ξ₁ σ * (Real.sin (2 * σ)) ^ (c - 2) := fun σ hσ =>
    mul_nonneg (hΞ₁nn σ hσ) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Icc hσ) _)
  -- the pointwise identification of the two forms of the total-variation integrand
  have hFpq : ∀ {a b : ℝ}, 0 ≤ a → b ≤ Real.pi / 2 →
      Set.EqOn (fun σ => 2 * (Real.sin (2 * σ))⁻¹ * Real.sqrt (Ξ σ * Ξ₁ σ))
        (fun σ => 2 * (Real.sqrt (Ξ σ * (Real.sin (2 * σ)) ^ (-c))
          * Real.sqrt (Ξ₁ σ * (Real.sin (2 * σ)) ^ (c - 2)))) (Set.Ioo a b) := by
    intro a b ha hb σ hσ
    have hσ0 : 0 < σ := lt_of_le_of_lt ha hσ.1
    have hσ1 : σ < Real.pi / 2 := lt_of_lt_of_le hσ.2 hb
    have h := csc_sqrt_specialise (c := c) ⟨hσ0, hσ1⟩
      (hΞnn σ ⟨le_of_lt hσ0, le_of_lt hσ1⟩) (hΞ₁nn σ ⟨le_of_lt hσ0, le_of_lt hσ1⟩)
    simpa only [mul_assoc] using h
  -- the uniform bound for the total variation
  have hbound : |Ξ θ - Ξ θ₀| ≤ 2 * Real.sqrt
      ((∫ σ in Set.Icc 0 (Real.pi / 2), Ξ σ * (Real.sin (2 * σ)) ^ (-c))
        * (∫ σ in Set.Icc 0 (Real.pi / 2), Ξ₁ σ * (Real.sin (2 * σ)) ^ (c - 2))) := by
    rcases le_total θ θ₀ with hle | hle
    · have h1 := hTV θ θ₀ hθI.1 hle hθ₀I.2
      have h2 := integral_tv_le (F := fun σ => 2 * (Real.sin (2 * σ))⁻¹ * Real.sqrt (Ξ σ * Ξ₁ σ))
        hθI.1 hle hθ₀I.2 (hFpq hθI.1 hθ₀I.2) hpnn hqnn hintA hintB
      rw [abs_sub_comm]
      exact le_trans h1 h2
    · have h1 := hTV θ₀ θ hθ₀I.1 hle hθI.2
      have h2 := integral_tv_le (F := fun σ => 2 * (Real.sin (2 * σ))⁻¹ * Real.sqrt (Ξ σ * Ξ₁ σ))
        hθ₀I.1 hle hθI.2 (hFpq hθ₀I.1 hθI.2) hpnn hqnn hintA hintB
      exact le_trans h1 h2
  calc Ξ θ = Ξ θ₀ + (Ξ θ - Ξ θ₀) := by ring
    _ ≤ Ξ θ₀ + |Ξ θ - Ξ θ₀| := by linarith [le_abs_self (Ξ θ - Ξ θ₀)]
    _ ≤ (2 / Real.pi) * (∫ σ in Set.Icc 0 (Real.pi / 2), Ξ σ)
        + 2 * Real.sqrt
            ((∫ σ in Set.Icc 0 (Real.pi / 2), Ξ σ * (Real.sin (2 * σ)) ^ (-c))
              * (∫ σ in Set.Icc 0 (Real.pi / 2), Ξ₁ σ * (Real.sin (2 * σ)) ^ (c - 2))) :=
        add_le_add hθ₀le hbound

end Work.FTS.TransportS.TvUniform
