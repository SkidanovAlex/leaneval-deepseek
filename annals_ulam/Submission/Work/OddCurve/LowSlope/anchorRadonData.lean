import Mathlib
import Submission.Work.OddCurve.LowSlope.radon_data_eq_inertiaIntegral_weak
import Submission.Work.OddCurve.LowSlope.Defs
import Submission.Work.OddRadon.Core

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

theorem anchorRadonData (n : ℕ) (hn : 1 ≤ n) {f ρ : ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hf_c : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hf_sm : ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1))
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u))
    (hbound : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * u ∈ Set.Ioo (-1 : ℝ) 1)
    (hrootR : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      f t = s * t → t = ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹)
    (hrootL : ∀ t ∈ Set.Ioo (-1 : ℝ) 0,
      f t = -(s * t) → t = -(ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (Real.sqrt (1 + s ^ 2))⁻¹))
    (hrad : ∀ t ∈ Set.Ioo
      (-(ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (Real.sqrt (1 + s ^ 2))⁻¹))
      (ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹),
      0 < Work.OddCurve.LowSlope.rad0 f s t)
    (hint1 : IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
      Work.OddCurve.LowSlope.rad0 f s t ^ (n - 1) / Real.sqrt (Work.OddCurve.LowSlope.rad0 f s t))
      volume (-(ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (Real.sqrt (1 + s ^ 2))⁻¹))
      (ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹))
    (hint2 : IntervalIntegrable (fun t : ℝ => t ^ 2 * Work.OddCurve.LowSlope.rad0 f s t ^ (n - 1) *
      Real.sqrt (Work.OddCurve.LowSlope.rad0 f s t)) volume
      (-(ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (Real.sqrt (1 + s ^ 2))⁻¹))
      (ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹)) :
    Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2))
        ((Real.sqrt (1 + s ^ 2))⁻¹) =
      (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) *
        Work.OddCurve.LowSlope.inertiaIntegral n f
          (fun _ : ℝ => ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (Real.sqrt (1 + s ^ 2))⁻¹)
          (fun _ : ℝ => ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹) s := by
  set c : ℝ := (Real.sqrt (1 + s ^ 2))⁻¹ with hc_def
  have hsq_pos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg s])
  have hcpos : 0 < c := by
    rw [hc_def]; exact inv_pos.mpr hsq_pos
  have hc_lt_one : c < 1 := by
    rw [hc_def]
    exact inv_lt_one_of_one_lt₀
      ((Real.lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num)).mpr (by nlinarith [sq_nonneg s]))
  have hmem_c : c ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hc_lt_one⟩
  have hmem_nc : -c ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  -- the derivative of `u ↦ ρ u * u` is nonnegative on `(-c, c)`
  have hderivn : ∀ u ∈ Set.Ioo (-c) c, 0 ≤ ρ u + u * deriv ρ u := by
    intro u hu
    have hu1 : u ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [hu.1, hc_lt_one], by linarith [hu.2, hc_lt_one]⟩
    have hmono' : MonotoneOn (fun v : ℝ => ρ v * v) (Set.Ioo (-c) c) :=
      hρmono.monotoneOn.mono
        (fun v hv => ⟨by linarith [hv.1, hc_lt_one], by linarith [hv.2, hc_lt_one]⟩)
    have h1 : 0 ≤ derivWithin (fun v : ℝ => ρ v * v) (Set.Ioo (-c) c) u :=
      hmono'.derivWithin_nonneg
    rw [derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hu)] at h1
    have hρd : DifferentiableAt ℝ ρ u :=
      (hρsm.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hu1)
    have hder : deriv (fun v : ℝ => ρ v * v) u = deriv ρ u * u + ρ u := by
      change deriv (fun v : ℝ => ρ v * id v) u = deriv ρ u * u + ρ u
      rw [deriv_fun_mul hρd differentiableAt_id]
      simp
    rw [hder] at h1
    linarith
  -- the value of `√(1 - c²)`
  have hsqrt_val : Real.sqrt (1 - c ^ 2) = s * c := by
    have hc2 : c ^ 2 = (1 + s ^ 2)⁻¹ := by
      rw [hc_def, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + s ^ 2)]
    rw [hc2]
    have hkey : 1 - (1 + s ^ 2)⁻¹ = s ^ 2 * (1 + s ^ 2)⁻¹ := by
      have hne : (1 + s ^ 2) ≠ 0 := by positivity
      field_simp
      ring
    rw [hkey, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq (le_of_lt hs), Real.sqrt_inv]
  have hend_y : ρ c * c = (fun _ : ℝ => ρ c * c) s := rfl
  have hend_x : ρ (-c) * (-c) = -((fun _ : ℝ => ρ (-c) * c) s) := by
    change ρ (-c) * (-c) = -(ρ (-c) * c)
    ring
  have hmem : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
      ρ (c * ν) * (c * ν) ∈ Set.Ioo (-((fun _ : ℝ => ρ (-c) * c) s))
        ((fun _ : ℝ => ρ c * c) s) := by
    intro ν hν
    change ρ (c * ν) * (c * ν) ∈ Set.Ioo (-(ρ (-c) * c)) (ρ c * c)
    have hνmem : c * ν ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨by nlinarith [hcpos, hc_lt_one, hν.1], by nlinarith [hcpos, hc_lt_one, hν.2]⟩
    have hlt1 : -c < c * ν := by nlinarith [hcpos, hν.1]
    have hlt2 : c * ν < c := by nlinarith [hcpos, hν.2]
    have h1 : ρ (-c) * (-c) < ρ (c * ν) * (c * ν) := hρmono hmem_nc hνmem hlt1
    have h2 : ρ (c * ν) * (c * ν) < ρ c * c := hρmono hνmem hmem_c hlt2
    have heq : ρ (-c) * (-c) = -(ρ (-c) * c) := by ring
    exact ⟨by linarith, h2⟩
  have hxI : -((fun _ : ℝ => ρ (-c) * c) s) ∈ Set.Ioo (-1 : ℝ) 1 := by
    change -(ρ (-c) * c) ∈ Set.Ioo (-1 : ℝ) 1
    have hb := hbound (-c) hmem_nc
    have heq : ρ (-c) * (-c) = -(ρ (-c) * c) := by ring
    rwa [heq] at hb
  have hyI : (fun _ : ℝ => ρ c * c) s ∈ Set.Ioo (-1 : ℝ) 1 := by
    change ρ c * c ∈ Set.Ioo (-1 : ℝ) 1
    exact hbound c hmem_c
  have hfy : f ((fun _ : ℝ => ρ c * c) s) = s * ((fun _ : ℝ => ρ c * c) s) := by
    change f (ρ c * c) = s * (ρ c * c)
    have hg := hgraph c hmem_c
    rw [hsqrt_val] at hg
    rw [← hg]
    ring
  have hfx : f (-((fun _ : ℝ => ρ (-c) * c) s)) = s * ((fun _ : ℝ => ρ (-c) * c) s) := by
    change f (-(ρ (-c) * c)) = s * (ρ (-c) * c)
    have hg := hgraph (-c) hmem_nc
    have hsq_neg : (1 : ℝ) - (-c) ^ 2 = 1 - c ^ 2 := by ring
    rw [hsq_neg, hsqrt_val] at hg
    have hneg : -(ρ (-c) * c) = ρ (-c) * (-c) := by ring
    rw [hneg, ← hg]
    ring
  have huniqy : ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = s * t → t = (fun _ : ℝ => ρ c * c) s := by
    intro t ht h
    exact hrootR t ht h
  have huniqx : ∀ t ∈ Set.Ioo (-1 : ℝ) 0, f t = -(s * t) →
      t = -((fun _ : ℝ => ρ (-c) * c) s) := by
    intro t ht h
    exact hrootL t ht h
  have hxy : -((fun _ : ℝ => ρ (-c) * c) s) < (fun _ : ℝ => ρ c * c) s := by
    change -(ρ (-c) * c) < ρ c * c
    have hlt : -c < c := by linarith [hcpos]
    have hh : ρ (-c) * (-c) < ρ c * c := hρmono hmem_nc hmem_c hlt
    have heq : ρ (-c) * (-c) = -(ρ (-c) * c) := by ring
    linarith
  have hmain := radon_data_eq_inertiaIntegral_weak n hn f ρ
    (fun _ : ℝ => ρ (-c) * c) (fun _ : ℝ => ρ c * c) s hs hf_c hf_sm hρpos hρsm hρmono
    hgraph hderivn hend_y hend_x hmem hxI hyI hfy hfx huniqy huniqx hxy hrad hint1 hint2
  rw [radonProfile_eq_natpow n hn (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) hcpos]
  exact hmain

end

end Work.OddCurve.LowSlope
