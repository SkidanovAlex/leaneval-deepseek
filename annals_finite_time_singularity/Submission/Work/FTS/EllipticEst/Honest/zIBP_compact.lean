import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.remov.ibpZZ
import Submission.Work.FTS.EllipticEst.Blocks.AgmonIBP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory Set Filter
open scoped Topology

theorem zIBP_compact (α : ℝ) (ω Φ : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hω : ∀ z, z ∉ Set.Icc a b → ω z = 0)
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0)) (hΦd : ContDiffOn ℝ 2 Φ (Set.Ioi 0)) :
    (∫ z in Set.Ioi (0 : ℝ), ω z * (α ^ 2 * z ^ 2 * deriv (deriv Φ) z
        + (α * (5 + α) * z) * deriv Φ z) * Φ z)
      = -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), ω z * (z * deriv Φ z) ^ 2)
        + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun z => z ^ 2 * ω z)) z * (Φ z) ^ 2)
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ), deriv (fun z => z * ω z) z * (Φ z) ^ 2) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  -- ## 0. Vanishing off the support `[a,b]`
  have hω_off : ∀ z, z ∉ Set.Icc a b → ω =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    intro z hz
    have hz' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz
    rcases hz' with hlt | hgt
    · filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
      exact hω w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)
    · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
      exact hω w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)
  have hW_off : ∀ z, z ∉ Set.Icc a b → deriv (fun y : ℝ => y ^ 2 * ω y) z = 0 := by
    intro z hz
    have hev : (fun y : ℝ => y ^ 2 * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hω_off z hz] with y hy
      rw [hy]; ring
    rw [hev.deriv_eq]; simp
  have hddW_off : ∀ z, z ∉ Set.Icc a b →
      deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z = 0 := by
    intro z hz
    have hz' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz
    have hev : deriv (fun y : ℝ => y ^ 2 * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
      rcases hz' with hlt | hgt
      · filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
        exact hW_off w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)
      · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        exact hW_off w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)
    rw [hev.deriv_eq]; simp
  have hzω_off : ∀ z, z ∉ Set.Icc a b → deriv (fun y : ℝ => y * ω y) z = 0 := by
    intro z hz
    have hev : (fun y : ℝ => y * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hω_off z hz] with y hy
      rw [hy]; ring
    rw [hev.deriv_eq]; simp
  -- ## 1. Smoothness bookkeeping
  have hW2ω : ContDiffOn ℝ 2 (fun y : ℝ => y ^ 2 * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hW2ω₁ : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y ^ 2 * ω y)) (Set.Ioi 0) :=
    hW2ω.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hW1ω : ContDiffOn ℝ 2 (fun y : ℝ => y * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hΦ₁ : ContDiffOn ℝ 1 (deriv Φ) (Set.Ioi 0) :=
    hΦd.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hcontω : ContinuousOn ω (Set.Icc a b) := hωd.continuousOn.mono hsub
  have hcontΦ : ContinuousOn Φ (Set.Icc a b) := hΦd.continuousOn.mono hsub
  have hcontdΦ : ContinuousOn (deriv Φ) (Set.Icc a b) :=
    (hΦd.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hcontddΦ : ContinuousOn (deriv (deriv Φ)) (Set.Icc a b) :=
    (hΦ₁.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hcontdW : ContinuousOn (deriv (fun y : ℝ => y ^ 2 * ω y)) (Set.Icc a b) :=
    (hW2ω.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hcontddW : ContinuousOn (deriv (deriv (fun y : ℝ => y ^ 2 * ω y))) (Set.Icc a b) :=
    (hW2ω₁.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hcontdzω : ContinuousOn (deriv (fun y : ℝ => y * ω y)) (Set.Icc a b) :=
    (hW1ω.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  -- ## 2. Integrability (every integrand is continuous on `[a,b]` and zero off it)
  have hi1 : IntegrableOn (fun z : ℝ => z ^ 2 * ω z * Φ z * deriv (deriv Φ) z)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      ((((continuousOn_id.pow 2).mul hcontω).mul hcontΦ).mul hcontddΦ)
      (fun z hz => by rw [hω z hz]; ring)
  have hi2 : IntegrableOn
      (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * ω y) z * Φ z * deriv Φ z) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      ((hcontdW.mul hcontΦ).mul hcontdΦ)
      (fun z hz => by rw [hW_off z hz]; ring)
  have hi3 : IntegrableOn (fun z : ℝ => ω z * (z * deriv Φ z) ^ 2) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      (hcontω.mul ((continuousOn_id.mul hcontdΦ).pow 2))
      (fun z hz => by rw [hω z hz]; ring)
  have hi4 : IntegrableOn
      (fun z : ℝ => deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * (Φ z) ^ 2) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      (hcontddW.mul (hcontΦ.pow 2))
      (fun z hz => by rw [hddW_off z hz]; ring)
  have hi1' : IntegrableOn (fun z : ℝ => ω z * z ^ 2 * deriv (deriv Φ) z * Φ z) (Set.Ioi 0) :=
    hi1.congr_fun (fun z _ => by ring) measurableSet_Ioi
  have hIntB0 : IntegrableOn (fun z : ℝ => ω z * z * deriv Φ z * Φ z) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      (((hcontω.mul continuousOn_id).mul hcontdΦ).mul hcontΦ)
      (fun z hz => by rw [hω z hz]; ring)
  have hIntB1 : IntegrableOn (fun z : ℝ => (z * ω z) * (2 * Φ z * deriv Φ z)) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      ((continuousOn_id.mul hcontω).mul (((continuous_const.continuousOn).mul hcontΦ).mul hcontdΦ))
      (fun z hz => by rw [hω z hz]; ring)
  have hIntB2 : IntegrableOn (fun z : ℝ => deriv (fun y : ℝ => y * ω y) z * (Φ z) ^ 2)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      (hcontdzω.mul (hcontΦ.pow 2))
      (fun z hz => by rw [hzω_off z hz]; ring)
  -- ## 3. Boundary terms
  have hb1 : Tendsto (fun z : ℝ => z ^ 2 * ω z * Φ z * deriv Φ z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => z ^ 2 * ω z * Φ z * deriv Φ z) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hω z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb2 : Tendsto (fun z : ℝ => z ^ 2 * ω z * Φ z * deriv Φ z) atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop]
        (fun z : ℝ => z ^ 2 * ω z * Φ z * deriv Φ z) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hω z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb3 : Tendsto (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * ω y) z * (Φ z) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * ω y) z * (Φ z) ^ 2) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hW_off z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb4 : Tendsto (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * ω y) z * (Φ z) ^ 2)
      atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop]
        (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * ω y) z * (Φ z) ^ 2) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hW_off z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb5 : Tendsto (fun z : ℝ => (z * ω z) * (Φ z) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => (z * ω z) * (Φ z) ^ 2) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hω z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb6 : Tendsto (fun z : ℝ => (z * ω z) * (Φ z) ^ 2) atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop] (fun z : ℝ => (z * ω z) * (Φ z) ^ 2) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hω z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  -- ## 4. The two integrations by parts
  -- `∫ ω z² Φ'' Φ = (1/2)∫ (z²ω)'' Φ² - ∫ ω (zΦ')²`
  have key1 : (∫ z in Set.Ioi (0 : ℝ), ω z * z ^ 2 * deriv (deriv Φ) z * Φ z)
      = (1 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun z : ℝ => z ^ 2 * ω z)) z * (Φ z) ^ 2)
        - (∫ z in Set.Ioi (0 : ℝ), ω z * (z * deriv Φ z) ^ 2) :=
    Work.FTS.EllipticEst.remov.ibpZZ ω Φ hωd hΦd hi1 hi2 hi3 hi4 hb1 hb2 hb3 hb4
  -- `∫ z ω Φ' Φ = -(1/2)∫ (zω)' Φ²`
  have hzv : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => y * ω y) (deriv (fun y : ℝ => y * ω y) z) z := by
    intro z hz
    exact (hW1ω.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hΦ2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => (Φ y) ^ 2) (2 * Φ z * deriv Φ z) z := by
    intro z hz
    have hΦz : HasDerivAt Φ (deriv Φ z) z :=
      (hΦd.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
    convert hΦz.pow 2 using 1
    simp [pow_one, mul_assoc]
  have hIBP2 := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := fun y : ℝ => y * ω y) (u' := fun y : ℝ => deriv (fun y : ℝ => y * ω y) y)
    (v := fun y : ℝ => (Φ y) ^ 2) (v' := fun y : ℝ => 2 * Φ y * deriv Φ y)
    hzv hΦ2 hIntB1 hIntB2 hb5 hb6
  have hIBP2' : (∫ z in Set.Ioi (0 : ℝ), (z * ω z) * (2 * Φ z * deriv Φ z))
      = -(∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * ω y) z * (Φ z) ^ 2) := by
    simpa using hIBP2
  have key2 : (∫ z in Set.Ioi (0 : ℝ), ω z * z * deriv Φ z * Φ z)
      = -(1 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun y : ℝ => y * ω y) z * (Φ z) ^ 2) := by
    have hcongr : (∫ z in Set.Ioi (0 : ℝ), (z * ω z) * (2 * Φ z * deriv Φ z))
        = 2 * (∫ z in Set.Ioi (0 : ℝ), ω z * z * deriv Φ z * Φ z) := by
      rw [show (∫ z in Set.Ioi (0 : ℝ), (z * ω z) * (2 * Φ z * deriv Φ z))
            = ∫ z in Set.Ioi (0 : ℝ), 2 * (ω z * z * deriv Φ z * Φ z) from
          setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
      rw [integral_const_mul]
    rw [hcongr] at hIBP2'
    linarith
  -- ## 5. Assembly
  rw [show (∫ z in Set.Ioi (0 : ℝ), ω z * (α ^ 2 * z ^ 2 * deriv (deriv Φ) z
          + (α * (5 + α) * z) * deriv Φ z) * Φ z)
        = ∫ z in Set.Ioi (0 : ℝ), α ^ 2 * (ω z * z ^ 2 * deriv (deriv Φ) z * Φ z)
            + (α * (5 + α)) * (ω z * z * deriv Φ z * Φ z) from
      setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
  rw [integral_add (hi1'.const_mul (α ^ 2)) (hIntB0.const_mul (α * (5 + α))),
    integral_const_mul, integral_const_mul, key1, key2]
  ring

end Work.FTS.EllipticEst.Honest
