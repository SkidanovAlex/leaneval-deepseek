import Mathlib
import Submission.Work.FIArea6Hecke.S16CleanDefs

namespace Work.FIArea6Road

/-- **The frequency cutoff `L = ⌊exp(√log N)⌋` is at least `exp(√log N)/2`.**

Since `log N ≥ 1` we have `exp(√log N) ≥ exp 1 > 2`, and for `x ≥ 2` the natural-number floor
satisfies `⌊x⌋₊ ≥ x - 1 ≥ x/2`. -/
lemma half_le_freqL (Pa : Work.FITop.Params) (hv : 1 ≤ Real.log Pa.N) :
    Real.exp (Real.sqrt (Real.log Pa.N)) / 2 ≤ (Work.FIArea6Hecke.freqL Pa : ℝ) := by
  have hu1 : 1 ≤ Real.sqrt (Real.log Pa.N) := by
    have h := Real.sqrt_le_sqrt hv
    rwa [Real.sqrt_one] at h
  have hexp2 : (2:ℝ) ≤ Real.exp (Real.sqrt (Real.log Pa.N)) := by
    have h1 : Real.exp 1 ≤ Real.exp (Real.sqrt (Real.log Pa.N)) := Real.exp_le_exp.mpr hu1
    have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    linarith
  have h1 : Real.exp (Real.sqrt (Real.log Pa.N)) - 1
      < (⌊Real.exp (Real.sqrt (Real.log Pa.N))⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (Real.exp (Real.sqrt (Real.log Pa.N)))
    linarith
  have hf : (Work.FIArea6Hecke.freqL Pa : ℝ)
      = (⌊Real.exp (Real.sqrt (Real.log Pa.N))⌋₊ : ℝ) := rfl
  rw [hf]
  linarith

/-- **The exponential saving beats `1/N`.**  With `u = √log N ≥ 1` one has
`N·exp(-u) = exp(u² - u) ≥ 1` because `u² - u = u(u-1) ≥ 0`. -/
lemma one_le_N_mul_exp_neg (Pa : Work.FITop.Params) (hv : 1 ≤ Real.log Pa.N)
    (hN : 1 ≤ Pa.N) :
    1 ≤ Pa.N * Real.exp (-(Real.sqrt (Real.log Pa.N))) := by
  have hNpos : (0:ℝ) < Pa.N := by linarith
  have hlog0 : (0:ℝ) ≤ Real.log Pa.N := by linarith
  set u : ℝ := Real.sqrt (Real.log Pa.N) with hu
  have hu1 : 1 ≤ u := by
    rw [hu]
    have h := Real.sqrt_le_sqrt hv
    rwa [Real.sqrt_one] at h
  have hmul : Real.exp (u^2) * Real.exp (-u) = Real.exp (u^2 - u) := by
    rw [← Real.exp_add]
    congr 1
  have hsq : u ^ 2 = Real.log Pa.N := by
    rw [hu, Real.sq_sqrt hlog0]
  have hNexp : Real.exp (u^2) = Pa.N := by
    rw [hsq, Real.exp_log hNpos]
  have hu2u : 0 ≤ u^2 - u := by
    have : u^2 - u = u * (u - 1) := by ring
    rw [this]
    exact mul_nonneg (by linarith) (by linarith)
  calc (1:ℝ) ≤ Real.exp (u^2 - u) := Real.one_le_exp hu2u
    _ = Pa.N * Real.exp (-u) := by rw [← hmul, hNexp]

/-- **The frequency tail factor is bounded by the exponential saving.**
`N/L + 1 ≤ 2·N·exp(-√log N) + N·exp(-√log N) = 3·N·exp(-√log N)` using
`L ≥ exp(√log N)/2` (`half_le_freqL`) and `N·exp(-√log N) ≥ 1`
(`one_le_N_mul_exp_neg`). -/
theorem TailFreqLBound (Pa : Work.FITop.Params) (hv : 1 ≤ Real.log Pa.N) (hN : 1 ≤ Pa.N) :
    Pa.N / (Work.FIArea6Hecke.freqL Pa : ℝ) + 1
      ≤ 3 * Pa.N * Real.exp (-(Real.sqrt (Real.log Pa.N))) := by
  set u : ℝ := Real.sqrt (Real.log Pa.N) with hu
  have hNnonneg : (0:ℝ) ≤ Pa.N := by linarith
  have hfloor : Real.exp u / 2 ≤ (Work.FIArea6Hecke.freqL Pa : ℝ) := by
    have h := half_le_freqL Pa hv
    rwa [← hu] at h
  have hstep : Pa.N / (Real.exp u / 2) = 2 * Pa.N * Real.exp (-u) := by
    rw [Real.exp_neg]
    field_simp
  have hmain : Pa.N / (Work.FIArea6Hecke.freqL Pa : ℝ) ≤ 2 * Pa.N * Real.exp (-u) := by
    have hdiv := div_le_div_of_nonneg_left hNnonneg
      (show (0:ℝ) < Real.exp u / 2 by linarith [Real.exp_pos u]) hfloor
    rw [hstep] at hdiv
    exact hdiv
  have hone : (1:ℝ) ≤ Pa.N * Real.exp (-u) := by
    have h := one_le_N_mul_exp_neg Pa hv hN
    rwa [← hu] at h
  calc Pa.N / (Work.FIArea6Hecke.freqL Pa : ℝ) + 1
      ≤ 2 * Pa.N * Real.exp (-u) + Pa.N * Real.exp (-u) := add_le_add hmain hone
    _ = 3 * Pa.N * Real.exp (-u) := by ring

end Work.FIArea6Road
