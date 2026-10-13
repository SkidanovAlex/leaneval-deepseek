import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real

namespace Work.FTS.PhiStar.Honesty.CSTools

/-- If the quadratic `s ↦ A + 2sB + s²C` is nonnegative for every real `s` and `C ≥ 0`, then
`B² ≤ A·C`: for `C > 0` evaluate at `s = -B/C`, and for `C = 0` the quadratic can only stay
nonnegative on both half-lines when `B = 0`. -/
theorem sq_le_mul_of_quadratic_nonneg {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s : ℝ, 0 ≤ A + 2 * s * B + s ^ 2 * C) : B ^ 2 ≤ A * C := by
  rcases lt_or_eq_of_le hC with hCpos | hCzero
  · have hCne : C ≠ 0 := ne_of_gt hCpos
    have hkey : A + 2 * (-(B / C)) * B + (-(B / C)) ^ 2 * C = A - B ^ 2 / C := by
      field_simp
      ring
    have h1 := h (-(B / C))
    rw [hkey] at h1
    have h2 : B ^ 2 / C ≤ A := by linarith
    exact (div_le_iff₀ hCpos).mp h2
  · have hC0 : C = 0 := hCzero.symm
    have hB0 : B = 0 := by
      by_contra hne
      have hBne : B ≠ 0 := hne
      have hkey : A + 2 * (-(A + 1) / (2 * B)) * B + (-(A + 1) / (2 * B)) ^ 2 * C = -1 := by
        rw [hC0]
        field_simp
        ring
      have h1 := h (-(A + 1) / (2 * B))
      rw [hkey] at h1
      linarith
    rw [hB0, hC0]
    norm_num

/-- Cauchy–Schwarz for the Bochner integral of real functions, in the `L²` form used by
`sq_interval_le_tail`. The proof is the discriminant argument applied to the nonnegative
quadratic `s ↦ ∫ t, (f t + s·g t)²`; note that no measurability of `f` or `g` themselves is
required. -/
theorem sq_integral_mul_le {μ : MeasureTheory.Measure ℝ} {f g : ℝ → ℝ}
    (hf : Integrable (fun t => (f t) ^ 2) μ) (hg : Integrable (fun t => (g t) ^ 2) μ)
    (hfg : Integrable (fun t => f t * g t) μ) :
    (∫ t, f t * g t ∂μ) ^ 2 ≤ (∫ t, (f t) ^ 2 ∂μ) * (∫ t, (g t) ^ 2 ∂μ) := by
  have hquad : ∀ s : ℝ, 0 ≤ (∫ t, (f t) ^ 2 ∂μ) + 2 * s * (∫ t, f t * g t ∂μ)
      + s ^ 2 * (∫ t, (g t) ^ 2 ∂μ) := by
    intro s
    have h1 : Integrable (fun t => 2 * s * (f t * g t)) μ := hfg.const_mul _
    have h2 : Integrable (fun t => s ^ 2 * (g t) ^ 2) μ := hg.const_mul _
    have e1 : ∫ t, (f t + s * g t) ^ 2 ∂μ
        = ∫ t, (f t) ^ 2 + 2 * s * (f t * g t) + s ^ 2 * (g t) ^ 2 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
    have e2 : ∫ t, (f t) ^ 2 + 2 * s * (f t * g t) + s ^ 2 * (g t) ^ 2 ∂μ
        = (∫ t, (f t) ^ 2 + 2 * s * (f t * g t) ∂μ) + (∫ t, s ^ 2 * (g t) ^ 2 ∂μ) :=
      integral_add (f := fun t : ℝ => (f t) ^ 2 + 2 * s * (f t * g t))
        (g := fun t : ℝ => s ^ 2 * (g t) ^ 2) (hf.add h1) h2
    have e3 : ∫ t, (f t) ^ 2 + 2 * s * (f t * g t) ∂μ
        = (∫ t, (f t) ^ 2 ∂μ) + (∫ t, 2 * s * (f t * g t) ∂μ) :=
      integral_add (f := fun t : ℝ => (f t) ^ 2) (g := fun t : ℝ => 2 * s * (f t * g t)) hf h1
    have e4 : (∫ t, 2 * s * (f t * g t) ∂μ) = 2 * s * (∫ t, f t * g t ∂μ) :=
      integral_const_mul (2 * s) (fun t : ℝ => f t * g t)
    have e5 : (∫ t, s ^ 2 * (g t) ^ 2 ∂μ) = s ^ 2 * (∫ t, (g t) ^ 2 ∂μ) :=
      integral_const_mul (s ^ 2) (fun t : ℝ => (g t) ^ 2)
    have hcalc : ∫ t, (f t + s * g t) ^ 2 ∂μ
        = (∫ t, (f t) ^ 2 ∂μ) + 2 * s * (∫ t, f t * g t ∂μ)
          + s ^ 2 * (∫ t, (g t) ^ 2 ∂μ) := by
      linarith [e1, e2, e3, e4, e5]
    have h0 : 0 ≤ ∫ t, (f t + s * g t) ^ 2 ∂μ :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun t => sq_nonneg _)
    rw [hcalc] at h0
    exact h0
  exact sq_le_mul_of_quadratic_nonneg
    (integral_nonneg_of_ae (Filter.Eventually.of_forall fun t => sq_nonneg _)) hquad

/-- For `0 ≤ r` and `1 ≤ w ≤ z`, the weighted power integral satisfies
`∫_{(w,z]} (t^r)² ≤ z^{2r+1}`. -/
theorem setIntegral_Ioc_rpow_sq_le {r w z : ℝ} (hr : 0 ≤ r) (hw : 1 ≤ w) (hwz : w ≤ z) :
    (∫ t in Set.Ioc w z, (t ^ r) ^ 2) ≤ z ^ (2 * r + 1) := by
  have hz1 : (1 : ℝ) ≤ z := le_trans hw hwz
  have hzpos : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
  have hgr : IntegrableOn (fun t : ℝ => (t ^ r) ^ 2) (Set.Ioc w z) := by
    have hcont : Continuous fun t : ℝ => (t ^ r) ^ 2 := (Real.continuous_rpow_const hr).pow 2
    have h2 : IntervalIntegrable (fun t : ℝ => (t ^ r) ^ 2) volume w z :=
      hcont.continuousOn.intervalIntegrable
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hwz] at h2
  have hconst : IntegrableOn (fun _ : ℝ => z ^ (2 * r)) (Set.Ioc w z) :=
    integrableOn_const (C := z ^ (2 * r)) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hmono : ∀ t ∈ Set.Ioc w z, (t ^ r) ^ 2 ≤ z ^ (2 * r) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := by linarith [hw, ht.1]
    have htr : t ^ r ≤ z ^ r := Real.rpow_le_rpow ht0 ht.2 hr
    have hsq : (t ^ r) ^ 2 ≤ (z ^ r) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg ht0 r) htr 2
    have hzr : (z ^ r) ^ 2 = z ^ (2 * r) := by
      rw [← Real.rpow_two (z ^ r), ← Real.rpow_mul (le_of_lt hzpos) r 2, mul_comm r 2]
    rwa [hzr] at hsq
  have hval : (∫ t in Set.Ioc w z, z ^ (2 * r)) = (z - w) * z ^ (2 * r) := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hwz, smul_eq_mul]
  have hfin : (z - w) * z ^ (2 * r) ≤ z ^ (2 * r + 1) := by
    have h1 : z - w ≤ z := by linarith
    have h2 : 0 ≤ z ^ (2 * r) := Real.rpow_nonneg (le_of_lt hzpos) _
    have h3 : (z - w) * z ^ (2 * r) ≤ z * z ^ (2 * r) := mul_le_mul_of_nonneg_right h1 h2
    have h4 : z * z ^ (2 * r) = z ^ (2 * r + 1) := by
      rw [Real.rpow_add hzpos (2 * r) 1, Real.rpow_one, mul_comm]
    rw [h4] at h3
    exact h3
  calc (∫ t in Set.Ioc w z, (t ^ r) ^ 2) ≤ ∫ t in Set.Ioc w z, z ^ (2 * r) :=
        setIntegral_mono_on hgr hconst measurableSet_Ioc hmono
    _ = (z - w) * z ^ (2 * r) := hval
    _ ≤ z ^ (2 * r + 1) := hfin

theorem sq_interval_le_tail {c : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r) {w z : ℝ} (hw : 1 ≤ w)
    (hwz : w ≤ z) (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    (∫ t in w..z, c t * t ^ r) ^ 2 ≤ (∫ t in Set.Ioi w, (c t) ^ 2) * z ^ (2 * r + 1) := by
  have hz1 : (1 : ℝ) ≤ z := le_trans hw hwz
  have hzpos : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
  have hfar_Ioc : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioc w z) :=
    hfar.mono_set (fun t ht => lt_of_le_of_lt hw ht.1)
  have hfar_Ioi : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi w) :=
    hfar.mono_set (fun t ht => lt_of_le_of_lt hw ht)
  have hg_int : IntegrableOn (fun t : ℝ => (t ^ r) ^ 2) (Set.Ioc w z) := by
    have hcont : Continuous fun t : ℝ => (t ^ r) ^ 2 := (Real.continuous_rpow_const hr).pow 2
    have h2 : IntervalIntegrable (fun t : ℝ => (t ^ r) ^ 2) volume w z :=
      hcont.continuousOn.intervalIntegrable
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hwz] at h2
  by_cases hBint : IntegrableOn (fun t : ℝ => c t * t ^ r) (Set.Ioc w z)
  · -- the integrand on the interval is integrable: Cauchy–Schwarz against the power weight
    have hCS := sq_integral_mul_le (μ := volume.restrict (Set.Ioc w z)) (f := c)
      (g := fun t : ℝ => t ^ r) hfar_Ioc hg_int hBint
    have hmid : (∫ t in Set.Ioc w z, (c t) ^ 2) ≤ ∫ t in Set.Ioi w, (c t) ^ 2 :=
      setIntegral_mono_set hfar_Ioi (Filter.Eventually.of_forall fun t => sq_nonneg _)
        (Filter.Eventually.of_forall fun t ht => ht.1)
    have hright : (∫ t in Set.Ioc w z, (t ^ r) ^ 2) ≤ z ^ (2 * r + 1) :=
      setIntegral_Ioc_rpow_sq_le hr hw hwz
    have hnn1 : 0 ≤ ∫ t in Set.Ioc w z, (t ^ r) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc (fun t _ => sq_nonneg _)
    have hnn2 : 0 ≤ ∫ t in Set.Ioi w, (c t) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
    calc (∫ t in w..z, c t * t ^ r) ^ 2
        = (∫ t, c t * t ^ r ∂(volume.restrict (Set.Ioc w z))) ^ 2 := by
          rw [intervalIntegral.integral_of_le hwz]
      _ ≤ (∫ t, (c t) ^ 2 ∂(volume.restrict (Set.Ioc w z)))
            * (∫ t, (t ^ r) ^ 2 ∂(volume.restrict (Set.Ioc w z))) := hCS
      _ = (∫ t in Set.Ioc w z, (c t) ^ 2) * (∫ t in Set.Ioc w z, (t ^ r) ^ 2) := rfl
      _ ≤ (∫ t in Set.Ioi w, (c t) ^ 2) * z ^ (2 * r + 1) :=
          mul_le_mul hmid hright hnn1 hnn2
  · -- otherwise the interval integral is `0` by the junk-value convention
    have hzero : (∫ t in w..z, c t * t ^ r) = 0 := by
      rw [intervalIntegral.integral_of_le hwz]
      exact integral_undef hBint
    rw [hzero]
    have hnn : 0 ≤ ∫ t in Set.Ioi w, (c t) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
    have hz0 : 0 ≤ z ^ (2 * r + 1) := Real.rpow_nonneg (le_of_lt hzpos) _
    simpa using mul_nonneg hnn hz0

end Work.FTS.PhiStar.Honesty.CSTools
