import Mathlib
import Submission.Work.EQ.FatouDefs
import Submission.Work.EQ.Fatou.pkS_mass

/-!
# The Poisson-kernel / angular-derivative mixture identity

For `0 ≤ r < 1` and an interval-integrable `f`,

`∫_{-π}^{π} pk r ψ · f ψ = ∫_0^{π} pkS r s · (∫_{-s}^{s} f) + pk r π · ∫_{-π}^{π} f`,

where `pkS r = -(d/dψ) pk r ψ`.  The proof rewrites `∫_{-s}^{s} f = ∫_0^{s} (f ψ + f (-ψ))`,
applies Fubini on the triangle `0 ≤ ψ ≤ s ≤ π`, and uses the fundamental theorem of calculus
`∫_ψ^{π} pkS r = pk r ψ - pk r π` together with the symmetry `pk r (-ψ) = pk r ψ`.
-/

namespace Work.EQ.Fatou

open MeasureTheory Set intervalIntegral

/-- `ψ ↦ pk r ψ` is continuous for `0 ≤ r < 1`. -/
lemma continuous_pk (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous fun ψ : ℝ => Work.EQ.pk r ψ := by
  unfold Work.EQ.pk
  apply Continuous.div <;> try fun_prop
  intro s
  have hc : Real.cos s ≤ 1 := Real.cos_le_one s
  nlinarith [sq_nonneg (1 - r)]

/-- `pk r` is even. -/
lemma pk_even (r ψ : ℝ) : Work.EQ.pk r (-ψ) = Work.EQ.pk r ψ := by
  simp [Work.EQ.pk, Real.cos_neg]

/-- **Fubini on the triangle** `0 ≤ ψ ≤ s ≤ π`. -/
theorem triangle_swap (g h : ℝ → ℝ) (hg : Continuous g)
    (hh : IntervalIntegrable h volume (0:ℝ) Real.pi) :
    ∫ s in (0:ℝ)..Real.pi, g s * (∫ ψ in (0:ℝ)..s, h ψ)
      = ∫ ψ in (0:ℝ)..Real.pi, h ψ * (∫ s in ψ..Real.pi, g s) := by
  let G : ℝ → ℝ := fun x => ∫ v in (0:ℝ)..x, g v
  let H : ℝ → ℝ := fun x => ∫ v in (0:ℝ)..x, h v
  have hGac : AbsolutelyContinuousOnInterval G 0 Real.pi :=
    (hg.intervalIntegrable 0 Real.pi).absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hHac : AbsolutelyContinuousOnInterval H 0 Real.pi :=
    hh.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hIBP := hHac.integral_mul_deriv_eq_deriv_mul hGac
  have hderivG : ∀ x : ℝ, deriv G x = g x := by
    intro x
    exact (hg.integral_hasStrictDerivAt 0 x).hasDerivAt.deriv
  have hderivH_ae : ∀ᵐ x : ℝ, x ∈ uIoc (0:ℝ) Real.pi → deriv H x = h x := by
    filter_upwards [hh.ae_hasDerivAt_integral] with x hx hxu
    exact (hx (uIoc_subset_uIcc hxu) 0 (by simp)).deriv
  have h1 : ∫ x in (0:ℝ)..Real.pi, H x * deriv G x = ∫ x in (0:ℝ)..Real.pi, H x * g x := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hderivG x]
  have h2 : ∫ x in (0:ℝ)..Real.pi, deriv H x * G x = ∫ x in (0:ℝ)..Real.pi, h x * G x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderivH_ae] with x hx hxu
    simp only [hx hxu]
  have hH0 : H 0 = 0 := by simp [H]
  have hG0 : G 0 = 0 := by simp [G]
  have hGcont : Continuous G :=
    continuous_iff_continuousAt.mpr fun x => (hg.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt
  have hgs : ∀ ψ : ℝ, ∫ s in ψ..Real.pi, g s = G Real.pi - G ψ := by
    intro ψ
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hg.integral_hasStrictDerivAt 0 x).hasDerivAt) (hg.intervalIntegrable _ _)]
  have hL : ∫ s in (0:ℝ)..Real.pi, g s * (∫ ψ in (0:ℝ)..s, h ψ)
      = G Real.pi * H Real.pi - ∫ ψ in (0:ℝ)..Real.pi, h ψ * G ψ := by
    change ∫ s in (0:ℝ)..Real.pi, g s * H s = _
    have h := hIBP
    rw [h1, h2, hH0, hG0] at h
    simp only [mul_zero, sub_zero] at h
    rw [show (∫ s in (0:ℝ)..Real.pi, g s * H s)
          = ∫ s in (0:ℝ)..Real.pi, H s * g s from by
        apply intervalIntegral.integral_congr; intro s _; ring]
    rw [h]; ring
  have hR : ∫ ψ in (0:ℝ)..Real.pi, h ψ * (∫ s in ψ..Real.pi, g s)
      = G Real.pi * H Real.pi - ∫ ψ in (0:ℝ)..Real.pi, h ψ * G ψ := by
    rw [show (∫ ψ in (0:ℝ)..Real.pi, h ψ * (∫ s in ψ..Real.pi, g s))
        = ∫ ψ in (0:ℝ)..Real.pi, h ψ * (G Real.pi - G ψ) from by
        apply intervalIntegral.integral_congr; intro ψ _; simp only [hgs]]
    have hcongr : ∫ ψ in (0:ℝ)..Real.pi, h ψ * (G Real.pi - G ψ)
        = ∫ ψ in (0:ℝ)..Real.pi, (h ψ * G Real.pi - h ψ * G ψ) := by
      apply intervalIntegral.integral_congr; intro ψ _; ring
    rw [hcongr, intervalIntegral.integral_sub (hh.mul_const (G Real.pi))
          (hh.mul_continuousOn hGcont.continuousOn), intervalIntegral.integral_mul_const]
    ring
  rw [hL, hR]

/-- **Symmetrization**: the integral of `F ψ + F (-ψ)` over a half period is the integral of `F`
over a full period. -/
theorem half_sum_eq (F : ℝ → ℝ) (hF : IntervalIntegrable F volume (-Real.pi) Real.pi) :
    ∫ ψ in (0:ℝ)..Real.pi, (F ψ + F (-ψ)) = ∫ ψ in (-Real.pi)..Real.pi, F ψ := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hF1 : IntervalIntegrable F volume (-Real.pi) 0 :=
    hF.mono_set (by
      rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc (by linarith) (by linarith))
  have hF2 : IntervalIntegrable F volume (0:ℝ) Real.pi :=
    hF.mono_set (by
      rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc (by linarith) le_rfl)
  have hFneg : IntervalIntegrable (fun ψ : ℝ => F (-ψ)) volume (0:ℝ) Real.pi := by
    have h := (IntervalIntegrable.iff_comp_neg (a := -Real.pi) (b := 0)).mp hF1
    simpa using h.symm
  rw [intervalIntegral.integral_add hF2 hFneg]
  have hcomp : ∫ ψ in (0:ℝ)..Real.pi, F (-ψ) = ∫ ψ in (-Real.pi)..0, F ψ := by
    have h := intervalIntegral.integral_comp_neg (f := F) (a := (0:ℝ)) (b := Real.pi)
    simpa using h
  rw [hcomp, add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals hF1 hF2

/-- **Fundamental theorem of calculus for `pkS`**: `pkS r` is `-(d/ds) pk r s`. -/
theorem integral_pkS_sub (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (a b : ℝ) :
    ∫ s in a..b, Work.EQ.pkS r s = Work.EQ.pk r a - Work.EQ.pk r b := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun s : ℝ => Work.EQ.pk r s) (-(Work.EQ.pkS r x)) x :=
    fun x _ => hasDerivAt_pk r hr hr1 x
  have hint : IntervalIntegrable (fun s : ℝ => -(Work.EQ.pkS r s)) volume a b :=
    (continuous_pkS r hr hr1).neg.intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem pk_mixture (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (-Real.pi) Real.pi) :
    (∫ ψ in (-Real.pi)..Real.pi, Work.EQ.pk r ψ * f ψ)
      = (∫ s in (0:ℝ)..Real.pi, Work.EQ.pkS r s * (∫ ψ in (-s)..s, f ψ))
        + Work.EQ.pk r Real.pi * (∫ ψ in (-Real.pi)..Real.pi, f ψ) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hf0 : IntervalIntegrable f volume (-Real.pi) 0 :=
    hf.mono_set (by
      rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc le_rfl (by linarith))
  have hf1 : IntervalIntegrable f volume (0:ℝ) Real.pi :=
    hf.mono_set (by
      rw [uIcc_of_le (le_of_lt hpi), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc (by linarith) le_rfl)
  have hfneg : IntervalIntegrable (fun ψ : ℝ => f (-ψ)) volume (0:ℝ) Real.pi := by
    have h' := (IntervalIntegrable.iff_comp_neg (a := -Real.pi) (b := 0)).mp hf0
    simpa using h'.symm
  have hh : IntervalIntegrable (fun ψ : ℝ => f ψ + f (-ψ)) volume (0:ℝ) Real.pi :=
    hf1.add hfneg
  have hsub : ∀ s ∈ uIcc (0:ℝ) Real.pi,
      ∫ ψ in (-s)..s, f ψ = ∫ ψ in (0:ℝ)..s, (f ψ + f (-ψ)) := by
    intro s hs
    rw [uIcc_of_le (le_of_lt hpi)] at hs
    obtain ⟨hs0, hspi⟩ := hs
    have hI1 : IntervalIntegrable f volume (-s) 0 :=
      hf.mono_set (by
        rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
        exact Icc_subset_Icc (by linarith) (by linarith))
    have hI2 : IntervalIntegrable f volume (0:ℝ) s :=
      hf.mono_set (by
        rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
        exact Icc_subset_Icc (by linarith) (by linarith))
    have hI2' : IntervalIntegrable (fun ψ : ℝ => f (-ψ)) volume (0:ℝ) s := by
      have h' := (IntervalIntegrable.iff_comp_neg (a := -s) (b := 0)).mp hI1
      simpa using h'.symm
    have hcomp : ∫ ψ in (-s)..0, f ψ = ∫ ψ in (0:ℝ)..s, f (-ψ) := by
      have h' := intervalIntegral.integral_comp_neg (f := f) (a := (0:ℝ)) (b := s)
      simpa using h'.symm
    have hadd : ∫ ψ in (0:ℝ)..s, (f ψ + f (-ψ))
        = (∫ ψ in (0:ℝ)..s, f ψ) + (∫ ψ in (0:ℝ)..s, f (-ψ)) :=
      intervalIntegral.integral_add hI2 hI2'
    rw [hadd, ← hcomp]
    exact (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm.trans
      (add_comm (∫ ψ in (-s)..0, f ψ) (∫ ψ in (0:ℝ)..s, f ψ))
  have hpk : Continuous fun ψ : ℝ => Work.EQ.pk r ψ := continuous_pk r hr hr1
  have hpkS : Continuous fun s : ℝ => Work.EQ.pkS r s := continuous_pkS r hr hr1
  have hFint : IntervalIntegrable (fun ψ : ℝ => Work.EQ.pk r ψ * f ψ) volume (-Real.pi) Real.pi := by
    simpa only [mul_comm] using hf.mul_continuousOn hpk.continuousOn
  have hA : ∫ s in (0:ℝ)..Real.pi, Work.EQ.pkS r s * (∫ ψ in (-s)..s, f ψ)
      = ∫ s in (0:ℝ)..Real.pi, Work.EQ.pkS r s * (∫ ψ in (0:ℝ)..s, (f ψ + f (-ψ))) := by
    apply intervalIntegral.integral_congr
    intro s hs
    show Work.EQ.pkS r s * (∫ ψ in (-s)..s, f ψ)
        = Work.EQ.pkS r s * (∫ ψ in (0:ℝ)..s, (f ψ + f (-ψ)))
    rw [hsub s hs]
  have hB : ∫ s in (0:ℝ)..Real.pi, Work.EQ.pkS r s * (∫ ψ in (0:ℝ)..s, (f ψ + f (-ψ)))
      = ∫ ψ in (0:ℝ)..Real.pi, (f ψ + f (-ψ)) * (∫ s in ψ..Real.pi, Work.EQ.pkS r s) :=
    triangle_swap (fun s : ℝ => Work.EQ.pkS r s) (fun ψ : ℝ => f ψ + f (-ψ)) hpkS hh
  have hC : ∫ ψ in (0:ℝ)..Real.pi, (f ψ + f (-ψ)) * (∫ s in ψ..Real.pi, Work.EQ.pkS r s)
      = ∫ ψ in (0:ℝ)..Real.pi, (f ψ + f (-ψ)) * (Work.EQ.pk r ψ - Work.EQ.pk r Real.pi) := by
    apply intervalIntegral.integral_congr
    intro ψ _
    show (f ψ + f (-ψ)) * (∫ s in ψ..Real.pi, Work.EQ.pkS r s)
        = (f ψ + f (-ψ)) * (Work.EQ.pk r ψ - Work.EQ.pk r Real.pi)
    rw [integral_pkS_sub r hr hr1 ψ Real.pi]
  have hI1 : IntervalIntegrable (fun ψ : ℝ => (f ψ + f (-ψ)) * Work.EQ.pk r ψ)
      volume (0:ℝ) Real.pi :=
    hh.mul_continuousOn hpk.continuousOn
  have hI2 : IntervalIntegrable (fun ψ : ℝ => (f ψ + f (-ψ)) * Work.EQ.pk r Real.pi)
      volume (0:ℝ) Real.pi :=
    hh.mul_const _
  have hD : ∫ ψ in (0:ℝ)..Real.pi, (f ψ + f (-ψ)) * (Work.EQ.pk r ψ - Work.EQ.pk r Real.pi)
      = (∫ ψ in (0:ℝ)..Real.pi, (f ψ + f (-ψ)) * Work.EQ.pk r ψ)
        - Work.EQ.pk r Real.pi * (∫ ψ in (0:ℝ)..Real.pi, (f ψ + f (-ψ))) := by
    rw [show (∫ ψ in (0:ℝ)..Real.pi, (f ψ + f (-ψ)) * (Work.EQ.pk r ψ - Work.EQ.pk r Real.pi))
        = ∫ ψ in (0:ℝ)..Real.pi,
            ((f ψ + f (-ψ)) * Work.EQ.pk r ψ - (f ψ + f (-ψ)) * Work.EQ.pk r Real.pi) from by
        apply intervalIntegral.integral_congr
        intro ψ _
        show (f ψ + f (-ψ)) * (Work.EQ.pk r ψ - Work.EQ.pk r Real.pi)
            = (f ψ + f (-ψ)) * Work.EQ.pk r ψ - (f ψ + f (-ψ)) * Work.EQ.pk r Real.pi
        ring]
    rw [intervalIntegral.integral_sub hI1 hI2, intervalIntegral.integral_mul_const]
    ring
  have hE1 : ∫ ψ in (0:ℝ)..Real.pi, (f ψ + f (-ψ)) * Work.EQ.pk r ψ
      = ∫ ψ in (-Real.pi)..Real.pi, Work.EQ.pk r ψ * f ψ := by
    have hsum : ∫ ψ in (0:ℝ)..Real.pi,
          (Work.EQ.pk r ψ * f ψ + Work.EQ.pk r (-ψ) * f (-ψ))
        = ∫ ψ in (-Real.pi)..Real.pi, Work.EQ.pk r ψ * f ψ :=
      half_sum_eq (fun ψ : ℝ => Work.EQ.pk r ψ * f ψ) hFint
    rw [← hsum]
    apply intervalIntegral.integral_congr
    intro ψ _
    show (f ψ + f (-ψ)) * Work.EQ.pk r ψ
        = Work.EQ.pk r ψ * f ψ + Work.EQ.pk r (-ψ) * f (-ψ)
    rw [pk_even r ψ]
    ring
  have hE2 : ∫ ψ in (0:ℝ)..Real.pi, (f ψ + f (-ψ)) = ∫ ψ in (-Real.pi)..Real.pi, f ψ :=
    half_sum_eq f hf
  rw [← hE1, hA, hB, hC, hD, ← hE2]
  ring

end Work.EQ.Fatou
