import Mathlib

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped Interval

/-- **Sampling bound.**  The `ℓ¹(ℤ)` norm of the samples of a Schwartz function `f : ℝ → ℂ`
is controlled by the `L¹` norms of `f` and of its derivative:

`∑_{j ∈ ℤ} ‖f j‖ ≤ C (‖f‖₁ + ‖f'‖₁)`.

The proof is the elementary "unit interval" argument: on the interval `(j, j + 1]` the mean value
identity `f j = f x - ∫_j^x f'` gives `‖f j‖ ≤ ‖f x‖ + ∫_j^{j+1} ‖f'‖` for every `x` in the
interval, and integrating this over `x` of measure one yields
`‖f j‖ ≤ ∫_j^{j+1} ‖f‖ + ∫_j^{j+1} ‖f'‖`.  Summing over `j : ℤ` and using that the unit intervals
partition `ℝ` (Mathlib's `Integrable.hasSum_intervalIntegral`) gives the claim with `C = 1`. -/
theorem offSample :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ, ∑' j : ℤ, ‖f (j : ℝ)‖
      ≤ C * ((∫ x : ℝ, ‖f x‖) + ∫ x : ℝ, ‖deriv (f : ℝ → ℂ) x‖) := by
  refine ⟨1, one_pos, ?_⟩
  intro f
  have hderiv_cont : Continuous (deriv (f : ℝ → ℂ)) := (f.smooth ⊤).continuous_deriv (by simp)
  have hf_int : Integrable (fun x : ℝ => ‖f x‖) := (SchwartzMap.integrable f).norm
  have hd_int : Integrable (fun x : ℝ => ‖deriv (f : ℝ → ℂ) x‖) := by
    simpa using (SchwartzMap.integrable (SchwartzMap.derivCLM ℝ ℂ f)).norm
  have hg_int : Integrable (fun x : ℝ => ‖f x‖ + ‖deriv (f : ℝ → ℂ) x‖) := hf_int.add hd_int
  have hpt : ∀ j : ℤ, ‖f (j : ℝ)‖ ≤
      ∫ x in (j : ℝ)..((j : ℝ) + 1), (‖f x‖ + ‖deriv (f : ℝ → ℂ) x‖) := by
    intro j
    set a : ℝ := (j : ℝ) with ha
    have hab : a ≤ a + 1 := by linarith
    have hfii : IntervalIntegrable (fun x : ℝ => ‖f x‖) volume a (a + 1) :=
      f.continuous.norm.intervalIntegrable a (a + 1)
    have hdii : IntervalIntegrable (fun x : ℝ => ‖deriv (f : ℝ → ℂ) x‖) volume a (a + 1) :=
      hderiv_cont.norm.intervalIntegrable a (a + 1)
    have hA_ii : IntervalIntegrable (fun _ : ℝ => (‖f a‖ : ℝ)) volume a (a + 1) :=
      intervalIntegrable_const
    have hc_ii : IntervalIntegrable (fun _ : ℝ => (∫ t in a..(a + 1), ‖deriv (f : ℝ → ℂ) t‖))
        volume a (a + 1) := intervalIntegrable_const
    have hpoint : ∀ x ∈ Set.Icc a (a + 1),
        (‖f a‖ : ℝ) ≤ ‖f x‖ + ∫ t in a..(a + 1), ‖deriv (f : ℝ → ℂ) t‖ := by
      intro x hx
      obtain ⟨hax, hxb⟩ := hx
      have hFTC : ∫ t in a..x, deriv (f : ℝ → ℂ) t = f x - f a :=
        intervalIntegral.integral_deriv_eq_sub (fun y _ => f.differentiableAt)
          (hderiv_cont.intervalIntegrable a x)
      have hfa : f a = f x - ∫ t in a..x, deriv (f : ℝ → ℂ) t := by rw [hFTC]; abel
      calc (‖f a‖ : ℝ) = ‖f x - ∫ t in a..x, deriv (f : ℝ → ℂ) t‖ := by rw [hfa]
        _ ≤ ‖f x‖ + ‖∫ t in a..x, deriv (f : ℝ → ℂ) t‖ := norm_sub_le _ _
        _ ≤ ‖f x‖ + ∫ t in a..x, ‖deriv (f : ℝ → ℂ) t‖ :=
            add_le_add_right (intervalIntegral.norm_integral_le_integral_norm hax) _
        _ ≤ ‖f x‖ + ∫ t in a..(a + 1), ‖deriv (f : ℝ → ℂ) t‖ :=
            add_le_add_right (intervalIntegral.integral_mono_interval le_rfl hax hxb
              (ae_of_all _ (fun t => norm_nonneg _)) hdii) _
    have h_int_const : ∫ x in a..(a + 1), (‖f a‖ : ℝ) = ‖f a‖ := by
      rw [intervalIntegral.integral_const]
      simp [add_sub_cancel_left]
    have hmono := intervalIntegral.integral_mono_on hab hA_ii
      ((f.continuous.norm.add continuous_const).intervalIntegrable a (a + 1)) hpoint
    have h_int_rhs : ∫ x in a..(a + 1), (fun x => ‖f x‖ + ∫ t in a..(a + 1), ‖deriv (f : ℝ → ℂ) t‖) x
        = (∫ x in a..(a + 1), ‖f x‖) + ∫ x in a..(a + 1), ‖deriv (f : ℝ → ℂ) x‖ := by
      show ∫ x in a..(a + 1), ‖f x‖ + (∫ t in a..(a + 1), ‖deriv (f : ℝ → ℂ) t‖)
        = (∫ x in a..(a + 1), ‖f x‖) + ∫ x in a..(a + 1), ‖deriv (f : ℝ → ℂ) x‖
      rw [intervalIntegral.integral_add hfii hc_ii, intervalIntegral.integral_const]
      simp [add_sub_cancel_left]
    calc (‖f a‖ : ℝ) = ∫ x in a..(a + 1), (‖f a‖ : ℝ) := h_int_const.symm
      _ ≤ ∫ x in a..(a + 1), (fun x => ‖f x‖ + ∫ t in a..(a + 1), ‖deriv (f : ℝ → ℂ) t‖) x := hmono
      _ = (∫ x in a..(a + 1), ‖f x‖) + ∫ x in a..(a + 1), ‖deriv (f : ℝ → ℂ) x‖ := h_int_rhs
      _ = ∫ x in a..(a + 1), (‖f x‖ + ‖deriv (f : ℝ → ℂ) x‖) :=
            (intervalIntegral.integral_add hfii hdii).symm
      _ = ∫ x in (j : ℝ)..((j : ℝ) + 1), (‖f x‖ + ‖deriv (f : ℝ → ℂ) x‖) := by rw [ha]
  have hsum := hg_int.hasSum_intervalIntegral 0
  have hb : Summable (fun j : ℤ => ∫ x in (j : ℝ)..((j : ℝ) + 1), (‖f x‖ + ‖deriv (f : ℝ → ℂ) x‖)) := by
    have := hsum.summable
    simpa only [zero_add] using this
  have ha' : Summable (fun j : ℤ => ‖f (j : ℝ)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hpt hb
  have hineq := Summable.tsum_le_tsum hpt ha' hb
  have htsum_eq : ∑' j : ℤ, (∫ x in (j : ℝ)..((j : ℝ) + 1), (‖f x‖ + ‖deriv (f : ℝ → ℂ) x‖))
      = ∫ x : ℝ, (‖f x‖ + ‖deriv (f : ℝ → ℂ) x‖) := by
    have := hsum.tsum_eq
    simpa only [zero_add] using this
  calc ∑' j : ℤ, ‖f (j : ℝ)‖
      ≤ ∑' j : ℤ, (∫ x in (j : ℝ)..((j : ℝ) + 1), (‖f x‖ + ‖deriv (f : ℝ → ℂ) x‖)) := hineq
    _ = ∫ x : ℝ, (‖f x‖ + ‖deriv (f : ℝ → ℂ) x‖) := htsum_eq
    _ = (∫ x : ℝ, ‖f x‖) + ∫ x : ℝ, ‖deriv (f : ℝ → ℂ) x‖ := integral_add hf_int hd_int
    _ = 1 * ((∫ x : ℝ, ‖f x‖) + ∫ x : ℝ, ‖deriv (f : ℝ → ℂ) x‖) := by rw [one_mul]

end Work.KMTAreas.A4
