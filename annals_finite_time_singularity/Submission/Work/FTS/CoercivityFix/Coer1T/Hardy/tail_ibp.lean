import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T.Hardy

/-- Integration by parts for the tail integral `F z = ∫ s in Ioi z, G s`.

With `F z = ∫ s in Ioi z, G s`, `P z = ∫ s in 1..z, G s`, `c = ∫ s in Ioi 1, G s` and the
primitive `H z = z * F z ^ 2` (absolutely continuous on `[1,R]`, with a.e. derivative
`F z ^ 2 - 2 * (z * F z) * G z`), the fundamental theorem of calculus gives the stated identity. -/
theorem tail_ibp (G : ℝ → ℝ) (hG : MeasureTheory.IntegrableOn G (Set.Ioi 1)) (R : ℝ) (hR : 1 < R) :
    (∫ z in (1:ℝ)..R, (∫ s in Set.Ioi z, G s) ^ 2)
      = R * (∫ s in Set.Ioi R, G s) ^ 2 - (∫ s in Set.Ioi 1, G s) ^ 2
        + 2 * (∫ z in (1:ℝ)..R, (z * (∫ s in Set.Ioi z, G s)) * G z) := by
  let F : ℝ → ℝ := fun z => ∫ s in Set.Ioi z, G s
  let c : ℝ := ∫ s in Set.Ioi 1, G s
  let P : ℝ → ℝ := fun z => ∫ t in (1:ℝ)..z, G t
  let H : ℝ → ℝ := fun z => z * (F z * F z)
  change (∫ z in (1:ℝ)..R, F z ^ 2)
      = R * F R ^ 2 - F 1 ^ 2 + 2 * (∫ z in (1:ℝ)..R, (z * F z) * G z)
  have hGint : IntervalIntegrable G (MeasureTheory.volume) (1:ℝ) R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr (hG.mono_set Set.Ioc_subset_Ioi_self)
  have huIcc : Set.uIcc (1:ℝ) R = Set.Icc (1:ℝ) R := Set.uIcc_of_le hR.le
  have h1mem : (1:ℝ) ∈ Set.uIcc (1:ℝ) R := by
    rw [huIcc]; exact ⟨le_rfl, hR.le⟩
  -- The tail integral is a primitive: `F y = c - P y` for all `y ≥ 1`.
  have hFP : ∀ y, 1 ≤ y → F y = c - P y := by
    intro y hy
    have hy1 : MeasureTheory.IntegrableOn G (Set.Ioi y) := hG.mono_set (Set.Ioi_subset_Ioi hy)
    have h := intervalIntegral.integral_interval_add_Ioi (μ := MeasureTheory.volume) hG hy1
    change (∫ s in Set.Ioi y, G s) = (∫ s in Set.Ioi 1, G s) - ∫ t in (1:ℝ)..y, G t
    linarith
  have hconst_AC : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) (1:ℝ) R :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  have hid_AC : AbsolutelyContinuousOnInterval (fun z : ℝ => z) (1:ℝ) R :=
    LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
  have hP_AC : AbsolutelyContinuousOnInterval P (1:ℝ) R :=
    hGint.absolutelyContinuousOnInterval_intervalIntegral (c := (1:ℝ)) h1mem
  have hF_AC : AbsolutelyContinuousOnInterval F (1:ℝ) R := by
    refine (hconst_AC.sub hP_AC).congr ?_
    intro z hz
    rw [huIcc] at hz
    exact (hFP z hz.1).symm
  have hH_AC : AbsolutelyContinuousOnInterval H (1:ℝ) R :=
    hid_AC.mul (hF_AC.mul hF_AC)
  have hne : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), x ≠ (1:ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp
  -- a.e. derivative of the tail integral.
  have hae_F : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      x ∈ Set.uIcc (1:ℝ) R → HasDerivAt F (-(G x)) x := by
    filter_upwards [hGint.ae_hasDerivAt_integral, hne] with x hpx hxne hxmem
    have hx1 : 1 ≤ x := by
      have h2 := hxmem; rw [huIcc] at h2; exact h2.1
    have hxgt : 1 < x := lt_of_le_of_ne hx1 (Ne.symm hxne)
    have hPx : HasDerivAt P (G x) x := hpx hxmem 1 h1mem
    have hE : F =ᶠ[nhds x] (fun y => c - P y) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨Set.Ioi (1:ℝ), isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hxgt), fun y hy => hFP y hy.le⟩
    have hsub : HasDerivAt (fun y => c - P y) (-(G x)) x := by
      have h0 : HasDerivAt (fun y => c - P y) (0 - G x) x :=
        (hasDerivAt_const (x := x) c).sub hPx
      simpa only [zero_sub] using h0
    exact hsub.congr_of_eventuallyEq hE
  -- a.e. derivative of `H z = z * F z ^ 2`.
  have hae_H : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      x ∈ Set.uIcc (1:ℝ) R → deriv H x = F x ^ 2 - 2 * ((x * F x) * G x) := by
    filter_upwards [hae_F] with x hFx hxmem
    have hF2 : HasDerivAt (fun y => F y * F y) ((-(G x)) * F x + F x * (-(G x))) x :=
      (hFx hxmem).mul (hFx hxmem)
    have hHd : HasDerivAt (fun y => y * (F y * F y))
        (1 * (F x * F x) + x * ((-(G x)) * F x + F x * (-(G x)))) x :=
      (hasDerivAt_id x).mul hF2
    have key : deriv (fun y => y * (F y * F y)) x = F x ^ 2 - 2 * ((x * F x) * G x) := by
      rw [hHd.deriv]; ring
    exact key
  have hFTC : ∫ x in (1:ℝ)..R, deriv H x = H R - H 1 := hH_AC.integral_deriv_eq_sub
  have hcongr : ∫ x in (1:ℝ)..R, deriv H x
      = ∫ x in (1:ℝ)..R, (F x ^ 2 - 2 * ((x * F x) * G x)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae_H] with x hx hxmem
    exact hx (Set.uIoc_subset_uIcc hxmem)
  have hcontA : ContinuousOn (fun x : ℝ => x * F x) (Set.uIcc (1:ℝ) R) :=
    continuousOn_id.mul hF_AC.continuousOn
  have hcontSq : ContinuousOn (fun x : ℝ => F x ^ 2) (Set.uIcc (1:ℝ) R) :=
    hF_AC.continuousOn.pow 2
  have hintA : IntervalIntegrable (fun x : ℝ => F x ^ 2) MeasureTheory.volume (1:ℝ) R :=
    hcontSq.intervalIntegrable
  have hintB : IntervalIntegrable (fun x : ℝ => (x * F x) * G x) MeasureTheory.volume (1:ℝ) R :=
    hGint.continuousOn_mul hcontA
  have hintC : IntervalIntegrable (fun x : ℝ => 2 * ((x * F x) * G x)) MeasureTheory.volume (1:ℝ) R :=
    hintB.const_mul 2
  have hsplit : ∫ x in (1:ℝ)..R, (F x ^ 2 - 2 * ((x * F x) * G x))
      = (∫ x in (1:ℝ)..R, F x ^ 2) - 2 * ∫ x in (1:ℝ)..R, (x * F x) * G x := by
    rw [intervalIntegral.integral_sub hintA hintC, intervalIntegral.integral_const_mul]
  have hHR : H R - H 1 = R * F R ^ 2 - F 1 ^ 2 := by
    change R * (F R * F R) - 1 * (F 1 * F 1) = R * F R ^ 2 - F 1 ^ 2
    ring
  linarith [hFTC, hcongr, hsplit, hHR]

end Work.FTS.CoercivityFix.Coer1T.Hardy
