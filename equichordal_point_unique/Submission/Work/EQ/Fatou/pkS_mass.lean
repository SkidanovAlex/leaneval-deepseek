import Mathlib
import Submission.Work.EQ.FatouDefs
import Submission.Work.EQ.Fatou.integral_pk_eq

/-! # The first moment of the angular Poisson-kernel derivative

`pkS r s = -(d/ds) pk r s`, so integrating `pkS r s * 2s` over `[0, π]` by parts and using
that the Poisson kernel has mass `π` on a half period gives
`∫₀^π pkS r s · 2s ds = 2π - 2π · pk r π`. -/

namespace Work.EQ.Fatou

open MeasureTheory Set

/-- `s ↦ pk r s` has derivative `-pkS r s` (for `0 ≤ r < 1`, where the denominator
`1 - 2 r cos s + r² ≥ (1-r)² > 0` never vanishes). -/
lemma hasDerivAt_pk (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasDerivAt (fun s : ℝ => Work.EQ.pk r s) (-(Work.EQ.pkS r x)) x := by
  have hc : Real.cos x ≤ 1 := Real.cos_le_one x
  have hmul : r * Real.cos x ≤ r := by nlinarith [hc, hr, sub_nonneg.mpr hc]
  have hDne : (1 - 2 * r * Real.cos x + r ^ 2) ≠ 0 := by nlinarith [sq_nonneg (1 - r)]
  have hD : HasDerivAt (fun s : ℝ => 1 - 2 * r * Real.cos s + r ^ 2)
      (2 * r * Real.sin x) x := by
    have h := ((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      ((hasDerivAt_const (x := x) (c := (2 * r))).mul (Real.hasDerivAt_cos x))).add
      (hasDerivAt_const (x := x) (c := r ^ 2))
    convert h using 1
    ring
  have h2 : HasDerivAt (fun s : ℝ => (1 - r ^ 2) / (1 - 2 * r * Real.cos s + r ^ 2))
      ((0 * (1 - 2 * r * Real.cos x + r ^ 2) - (1 - r ^ 2) * (2 * r * Real.sin x))
        / (1 - 2 * r * Real.cos x + r ^ 2) ^ 2) x :=
    (hasDerivAt_const (x := x) (c := (1 - r ^ 2))).div hD hDne
  unfold Work.EQ.pk Work.EQ.pkS
  convert h2 using 1
  field_simp
  ring

/-- `s ↦ pkS r s` is continuous for `0 ≤ r < 1`. -/
lemma continuous_pkS (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous fun s : ℝ => Work.EQ.pkS r s := by
  unfold Work.EQ.pkS
  apply Continuous.div <;> try fun_prop
  intro s
  have hc : Real.cos s ≤ 1 := Real.cos_le_one s
  have hpos : 0 < 1 - 2 * r * Real.cos s + r ^ 2 := by nlinarith [sq_nonneg (1 - r)]
  exact pow_ne_zero 2 (ne_of_gt hpos)

/-- The angular Poisson kernel has half-period mass `π`. -/
lemma integral_pk_zero_pi (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ∫ s in (0 : ℝ)..Real.pi, Work.EQ.pk r s = Real.pi := by
  have hfull := Work.EQ.Fatou.integral_pk_eq r hr hr1
  have hcont : Continuous fun s : ℝ => Work.EQ.pk r s := by
    unfold Work.EQ.pk
    apply Continuous.div <;> try fun_prop
    intro s
    have hc : Real.cos s ≤ 1 := Real.cos_le_one s
    nlinarith [sq_nonneg (1 - r)]
  have hInt1 : IntervalIntegrable (fun s : ℝ => Work.EQ.pk r s) volume (-Real.pi) 0 :=
    hcont.intervalIntegrable _ _
  have hInt2 : IntervalIntegrable (fun s : ℝ => Work.EQ.pk r s) volume (0 : ℝ) Real.pi :=
    hcont.intervalIntegrable _ _
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2
  have hneg : ∫ s in (-Real.pi)..(0 : ℝ), Work.EQ.pk r s
      = ∫ s in (0 : ℝ)..Real.pi, Work.EQ.pk r s := by
    have h1 : ∫ s in (-Real.pi)..(0 : ℝ), Work.EQ.pk r s
        = ∫ s in (-Real.pi)..(0 : ℝ), Work.EQ.pk r (-s) := by
      apply intervalIntegral.integral_congr
      intro s _
      simp [Work.EQ.pk, Real.cos_neg]
    rw [h1, intervalIntegral.integral_comp_neg]
    simp
  linarith

theorem pkS_mass (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ∫ s in (0 : ℝ)..Real.pi, Work.EQ.pkS r s * (2 * s)
      = 2 * Real.pi - 2 * Real.pi * Work.EQ.pk r Real.pi := by
  have hIntS : IntervalIntegrable (fun s : ℝ => Work.EQ.pkS r s) volume (0 : ℝ) Real.pi :=
    (continuous_pkS r hr hr1).intervalIntegrable _ _
  have hInt1 : IntervalIntegrable (fun _ : ℝ => (2 : ℝ)) volume (0 : ℝ) Real.pi :=
    intervalIntegrable_const
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi, HasDerivAt (fun s : ℝ => 2 * s) (2 : ℝ) x := by
    intro x _
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun s : ℝ => Work.EQ.pk r s) (-(Work.EQ.pkS r x)) x := by
    intro x _
    exact hasDerivAt_pk r hr hr1 x
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ => 2 * s) (v := fun s : ℝ => Work.EQ.pk r s)
    (u' := fun _ : ℝ => (2 : ℝ)) (v' := fun s : ℝ => -(Work.EQ.pkS r s))
    hu hv hInt1 hIntS.neg
  have hneg : ∫ x in (0 : ℝ)..Real.pi, (2 * x) * (-(Work.EQ.pkS r x))
      = -∫ x in (0 : ℝ)..Real.pi, Work.EQ.pkS r x * (2 * x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hneg] at hIBP
  have hpkin : ∫ x in (0 : ℝ)..Real.pi, (2 : ℝ) * Work.EQ.pk r x = 2 * Real.pi := by
    rw [intervalIntegral.integral_const_mul, integral_pk_zero_pi r hr hr1]
  rw [hpkin] at hIBP
  simp only [mul_zero, zero_mul, sub_zero] at hIBP
  linarith

end Work.EQ.Fatou
