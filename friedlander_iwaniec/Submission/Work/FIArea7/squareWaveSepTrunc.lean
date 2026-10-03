import Mathlib
import Submission.Work.FIArea7.exists_squareWave_fourier
import Submission.Work.FIArea7.smoothTransition_deriv_bounds
import Submission.Work.FIArea7.sqWaveCoeffExists
import Submission.Work.FIArea7.truncLeOfCoeffBounds

namespace Work.FIArea7

/-- **FI (20.17)–(20.19), truncated form.**  There is an absolute constant `C` such that for every
`R ≥ 2` there is a sequence `ĉ : ℤ → ℂ` of `ℓ¹`-norm at most `C log (2R)` whose *partial* sums of
order `K` separate the square wave `sign (cos α) = sign (Re wz)` on the arc `|Re wz| ≥ ‖w‖‖z‖/R`
to within `C R / (K+1)`.

The coefficients are the Fourier coefficients of the smoothed square wave `t(α) = sign(cos α)` of
`Work.FIArea7.exists_squareWave_fourier`; the point here is the uniform rate `R/(K+1)` of the
truncation, which is what §§20, 22–23 use when the separating series must be cut at a finite order
`K`.  The two analytic inputs are isolated as `sqWaveCoeffExists` (the coefficients exist with the
required `ℓ¹` bound, the two pointwise decay bounds and the full `HasSum` identity) and
`truncLeOfCoeffBounds` (coefficients with those decay bounds give the truncated approximation at
rate `R/(K+1)`). -/
theorem squareWaveSepTrunc :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R → ∃ ĉ : ℤ → ℂ,
      (∀ s : Finset ℤ, ∑ k ∈ s, ‖ĉ k‖ ≤ C * Real.log (2 * (R : ℝ))) ∧
      ∀ (K : ℕ) (w z : ℂ), w ≠ 0 → z ≠ 0 → ‖w‖ * ‖z‖ ≤ (R : ℝ) * |(w * z).re| →
        ‖(if 0 < (w * z).re then (1 : ℂ) else -1)
          - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              ĉ k * ((w / (‖w‖ : ℂ)) ^ k * (z / (‖z‖ : ℂ)) ^ k)‖
          ≤ C * (R : ℝ) / ((K : ℝ) + 1) := by
  obtain ⟨M, hM0, hM1, hM2⟩ := Work.FIArea7.smoothTransition_deriv_bounds
  refine ⟨20 * M + 2, by linarith, fun R hR => ?_⟩
  obtain ⟨ĉ, hcoeff, hdec1, hdec2, hhas⟩ :=
    Work.FIArea7.sqWaveCoeffExists M hM0 hM1 hM2 R hR
  refine ⟨ĉ, ?_, ?_⟩
  · intro s
    refine le_trans (hcoeff s) ?_
    apply mul_le_mul_of_nonneg_right (by linarith)
    apply Real.log_nonneg
    have h2R : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    linarith
  · intro K w z hw hz hroom
    have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have hden : (0 : ℝ) < ‖w‖ * ‖z‖ := mul_pos hwpos hzpos
    have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
    -- the unit modulus point `u` at which the single-variable series is evaluated
    set u : ℂ := (w / (‖w‖ : ℂ)) * (z / (‖z‖ : ℂ)) with hu
    have hu_eq : u = (w * z) / ((‖w‖ * ‖z‖ : ℝ) : ℂ) := by
      rw [hu]; push_cast; field_simp
    have hunorm : ‖u‖ = 1 := by
      rw [hu_eq, norm_div]
      have h1 : ‖(((‖w‖ * ‖z‖ : ℝ)) : ℂ)‖ = ‖w‖ * ‖z‖ := by
        rw [show ‖(((‖w‖ * ‖z‖ : ℝ)) : ℂ)‖ = |‖w‖ * ‖z‖| by simp,
          abs_of_nonneg hden.le]
      rw [h1, norm_mul, div_self (ne_of_gt hden)]
    have hure : u.re = (w * z).re / (‖w‖ * ‖z‖) := by
      rw [hu_eq, Complex.div_ofReal_re]
    -- the "room" hypothesis gives `1/R` separation for `u`
    have hrele : (1 : ℝ) / (R : ℝ) ≤ |u.re| := by
      rw [hure, abs_div, abs_of_pos hden, le_div_iff₀ hden]
      have hh : (1 : ℝ) / (R : ℝ) * (‖w‖ * ‖z‖) = (‖w‖ * ‖z‖) / (R : ℝ) := by ring
      rw [hh, div_le_iff₀ hR0]
      linarith [hroom]
    have hsign : 0 < u.re ↔ 0 < (w * z).re := by
      rw [hure, div_pos_iff]
      constructor
      · rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
        · exact h1
        · linarith
      · intro h1; exact Or.inl ⟨h1, hden⟩
    have hval : (if 0 < u.re then (1 : ℂ) else -1)
        = (if 0 < (w * z).re then (1 : ℂ) else -1) := by
      by_cases h : 0 < u.re
      · rw [if_pos h, if_pos (hsign.mp h)]
      · rw [if_neg h, if_neg (fun hh => h (hsign.mpr hh))]
    have hsumu : HasSum (fun k : ℤ => ĉ k * u ^ k) (if 0 < u.re then 1 else -1) :=
      hhas u hunorm hrele
    have hb := Work.FIArea7.truncLeOfCoeffBounds (K := K) hM0 hunorm hdec1 hdec2 hsumu
    rw [← hval]
    have hsum_eq : (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ĉ k * ((w / (‖w‖ : ℂ)) ^ k * (z / (‖z‖ : ℂ)) ^ k))
        = ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ĉ k * u ^ k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hu, mul_zpow]
    rw [hsum_eq]
    refine le_trans hb ?_
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg R)
    · positivity

end Work.FIArea7
