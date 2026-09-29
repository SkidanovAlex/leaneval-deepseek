import Mathlib

namespace Work.TMC7Core.Fourier

open MeasureTheory Set intervalIntegral

/-- Markov/Chebyshev-type deviation bound: a nonnegative continuous function whose
integral over `[0,1]` is at most `2/K` can exceed a level `κ > 0` on a set of
Lebesgue measure at most `2/(K κ)`. -/
theorem markov_deviation (f : ℝ → ℝ) (hf : Continuous f) (hfnn : ∀ x, 0 ≤ f x)
    (S : Set ℝ) (hSsub : S ⊆ Set.Icc (0:ℝ) 1) (κ : ℝ) (hκ : 0 < κ)
    (hSlarge : ∀ x ∈ S, κ ≤ f x) (K : ℝ) (hK : 0 < K)
    (hint : ∫ x in (0:ℝ)..1, f x ≤ 2 / K) :
    MeasureTheory.volume S ≤ ENNReal.ofReal (2 / (K * κ)) := by
  set A : Set ℝ := {x | κ ≤ f x} ∩ Set.Icc (0:ℝ) 1
  have hSA : S ⊆ A := fun x hx => ⟨hSlarge x hx, hSsub hx⟩
  have hAmeas : MeasurableSet A :=
    (isClosed_Ici.preimage hf).measurableSet.inter measurableSet_Icc
  have hAsub : A ⊆ Set.Icc (0:ℝ) 1 := Set.inter_subset_right
  have hvol : volume S ≤ volume A := measure_mono hSA
  have hAfin : volume A ≠ ⊤ := by
    have hle : volume A ≤ volume (Set.Icc (0:ℝ) 1) := measure_mono hAsub
    rw [Real.volume_Icc, sub_zero] at hle
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  -- The core measure/level inequality, in `ℝ≥0∞`.
  have hkey : ENNReal.ofReal κ * volume A ≤ ENNReal.ofReal (2 / K) := by
    have h1 : ∫⁻ x in A, ENNReal.ofReal κ ≤ ∫⁻ x in A, ENNReal.ofReal (f x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hAmeas] with x hx
      exact ENNReal.ofReal_le_ofReal hx.1
    have h2 : ∫⁻ x in A, ENNReal.ofReal (f x)
        ≤ ∫⁻ x in Set.Icc (0:ℝ) 1, ENNReal.ofReal (f x) :=
      lintegral_mono_set hAsub
    have h3 : ∫⁻ x in Set.Icc (0:ℝ) 1, ENNReal.ofReal (f x)
        = ENNReal.ofReal (∫ x in Set.Icc (0:ℝ) 1, f x) :=
      (ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc (a := 0) (b := 1))
        (Filter.Eventually.of_forall hfnn)).symm
    have h4 : ∫ x in Set.Icc (0:ℝ) 1, f x ≤ 2 / K := by
      rw [integral_Icc_eq_integral_Ioc, ← integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact hint
    calc ENNReal.ofReal κ * volume A = ∫⁻ x in A, ENNReal.ofReal κ := (setLIntegral_const A _).symm
      _ ≤ ∫⁻ x in A, ENNReal.ofReal (f x) := h1
      _ ≤ ∫⁻ x in Set.Icc (0:ℝ) 1, ENNReal.ofReal (f x) := h2
      _ = ENNReal.ofReal (∫ x in Set.Icc (0:ℝ) 1, f x) := h3
      _ ≤ ENNReal.ofReal (2 / K) := ENNReal.ofReal_le_ofReal h4
  have hstep : volume A ≤ ENNReal.ofReal (2 / (K * κ)) := by
    have h1 : volume A ≤ ENNReal.ofReal (2 / K) / ENNReal.ofReal κ := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hκ)))
        (Or.inl ENNReal.ofReal_ne_top)]
      rwa [mul_comm]
    rw [← ENNReal.ofReal_div_of_pos hκ, div_div] at h1
    exact h1
  calc volume S ≤ volume A := hvol
    _ ≤ ENNReal.ofReal (2 / (K * κ)) := hstep

end Work.TMC7Core.Fourier
