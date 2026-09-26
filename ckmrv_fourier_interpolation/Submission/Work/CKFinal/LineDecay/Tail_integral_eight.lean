import Mathlib
import Submission.Work.CKFinal.LineDecay.Prof_integrable
import Submission.Work.CKFinal.LineDecay.Tail_integrand_pointwise

namespace Work.CKFinal.LineDecay

open MeasureTheory Filter

/-- **The elementary tail integral.**  For every real exponent `A` there is `C > 0` such that for
all `y ≥ 1` the function `t ↦ (1+t)^A e^{-πt}/(1 + e^{2π(y-t)})` is integrable on `[1,∞)` and
`∫_{t ≥ 1} (1+t)^A e^{-πt}/(1 + e^{2π(y-t)}) dt ≤ C (1+y)^A e^{-πy}`.

Here `C` may depend on `A`.  Proof strategy: the kernel `1/(1+e^{2π(y-t)}) ≤ min (1, e^{2π(t-y)})`
is a bump of width `O(1)` at `t = y`; split the integral at `t = y`, bound
`∫_1^y (1+t)^A e^{πt} dt` and `∫_y^∞ (1+t)^A e^{-πt} dt` by `C_A (1+y)^A e^{πy}` and
`C_A (1+y)^A e^{-πy}` respectively (substituting `t = y - s`, resp. `t = y + s`, and using
`(1+y±s)^A ≤ C_A (1+y)^A (1+s)^{|A|}`).  Integrability follows from
`(1+t)^A e^{-πt}/(1+e^{2π(y-t)}) ≤ (1+t)^A e^{-πt}` together with the integrability of
`t ↦ (1+t)^{⌈A⌉₊} e^{-πt}` on `[1,∞)`. -/
theorem Tail_integral_eight (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ y →
      MeasureTheory.IntegrableOn (fun t : ℝ => (1 + t) ^ A *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))) (Set.Ici 1) ∧
      ∫ t in Set.Ici (1 : ℝ), (1 + t) ^ A *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))
        ≤ C * (1 + y) ^ A * Real.exp (-(Real.pi * y)) := by
  -- The profile `u ↦ (1 + |u|)^|A| e^{-π|u|}`, integrable on `ℝ`.
  set prof : ℝ → ℝ := fun u => (1 + |u|) ^ |A| * Real.exp (-(Real.pi * |u|)) with hprof
  have hprof_int : Integrable prof := Prof_integrable |A| (abs_nonneg A)
  have hC₀nn : 0 ≤ ∫ u, prof u := integral_nonneg (fun u => by rw [hprof]; positivity)
  refine ⟨(∫ u, prof u) + 1, by linarith, ?_⟩
  intro y hy
  -- The coefficient `c = (1+y)^A e^{-πy}` and the majorant `c · prof (· - y)`.
  set c : ℝ := (1 + y) ^ A * Real.exp (-(Real.pi * y)) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) A) (Real.exp_pos _).le
  have hmaj_int : Integrable (fun t : ℝ => c * prof (t - y)) := by
    have h := hprof_int.comp_add_right (-y)
    have h2 : (fun t : ℝ => prof (t + (-y))) = (fun t => prof (t - y)) := by
      funext t; rw [sub_eq_add_neg]
    rw [h2] at h
    exact h.const_mul c
  -- Continuity of the integrand on `[1,∞)`.
  have hcont : ContinuousOn (fun t : ℝ => (1 + t) ^ A *
      (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))) (Set.Ici 1) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp ht
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · exact ContinuousAt.rpow_const (continuousAt_const.add continuousAt_id) (Or.inl (by linarith))
    · apply ContinuousAt.div
      · exact (Real.continuous_exp.continuousAt).comp (continuousAt_const.mul continuousAt_id).neg
      · fun_prop
      · positivity
  -- The pointwise domination by the majorant.
  have hpt : ∀ t : ℝ, 1 ≤ t → (1 + t) ^ A *
      (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t)))) ≤ c * prof (t - y) := by
    intro t ht
    have h := Tail_integrand_pointwise A y t hy ht
    have heq : c * prof (t - y) = (1 + y) ^ A *
        ((1 + |t - y|) ^ |A| * Real.exp (-(Real.pi * |t - y|))) * Real.exp (-(Real.pi * y)) := by
      simp only [hc, hprof]
      ring
    rw [heq]; exact h
  -- Positivity of the integrand for `t ≥ 1`.
  have hf_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ (1 + t) ^ A *
      (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t)))) := by
    intro t ht
    have h1 : 0 ≤ (1 + t) ^ A := Real.rpow_nonneg (by linarith) A
    have h2 : 0 < 1 + Real.exp (2 * Real.pi * (y - t)) := by positivity
    exact mul_nonneg h1 (div_nonneg (Real.exp_pos _).le h2.le)
  -- Integrability of the integrand on `[1,∞)`, by domination.
  have hf_int : IntegrableOn (fun t : ℝ => (1 + t) ^ A *
      (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))) (Set.Ici 1) := by
    refine (hmaj_int.integrableOn).mono' ?_ ?_
    · exact hcont.aestronglyMeasurable measurableSet_Ici
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg t ht)]
      exact hpt t ht
  refine ⟨hf_int, ?_⟩
  have hmono : ∫ t in Set.Ici (1 : ℝ), (1 + t) ^ A *
        (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))
      ≤ ∫ t in Set.Ici (1 : ℝ), c * prof (t - y) := by
    refine integral_mono_ae hf_int hmaj_int.integrableOn ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hpt t ht
  have hconst : ∫ t in Set.Ici (1 : ℝ), c * prof (t - y) =
      c * ∫ t in Set.Ici (1 : ℝ), prof (t - y) :=
    MeasureTheory.integral_const_mul c _
  -- Shift invariance bounds the translated tail integral by the full integral of the profile.
  have hshift : ∫ t in Set.Ici (1 : ℝ), prof (t - y) ≤ ∫ u, prof u := by
    have hInt : Integrable (fun t : ℝ => prof (t - y)) := by
      have h := hprof_int.comp_add_right (-y)
      simpa only [sub_eq_add_neg] using h
    have hnn : 0 ≤ᵐ[volume] (fun t : ℝ => prof (t - y)) :=
      Filter.Eventually.of_forall (fun t => by rw [hprof]; positivity)
    calc ∫ t in Set.Ici (1 : ℝ), prof (t - y) ≤ ∫ t, prof (t - y) :=
          setIntegral_le_integral hInt hnn
      _ = ∫ u, prof u := MeasureTheory.integral_sub_right_eq_self prof y
  calc ∫ t in Set.Ici (1 : ℝ), (1 + t) ^ A *
        (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))
      ≤ ∫ t in Set.Ici (1 : ℝ), c * prof (t - y) := hmono
    _ = c * ∫ t in Set.Ici (1 : ℝ), prof (t - y) := hconst
    _ ≤ c * ∫ u, prof u := mul_le_mul_of_nonneg_left hshift hc0
    _ ≤ ((∫ u, prof u) + 1) * (1 + y) ^ A * Real.exp (-(Real.pi * y)) := by
        rw [hc]
        calc ((1 + y) ^ A * Real.exp (-(Real.pi * y))) * ∫ u, prof u
            ≤ ((1 + y) ^ A * Real.exp (-(Real.pi * y))) * ((∫ u, prof u) + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = ((∫ u, prof u) + 1) * (1 + y) ^ A * Real.exp (-(Real.pi * y)) := by ring

end Work.CKFinal.LineDecay
