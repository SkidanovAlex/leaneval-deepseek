import Mathlib
import Submission.Work.Pert.CoordDefs
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Om_norm_bounds
import Submission.Work.Pert.norm_exp_sub_one_le_of_le_pi_half

set_option linter.unusedVariables false

namespace Work.Pert

open MandelDim Complex Set Metric

noncomputable section

/-- `‖2πi‖ = 2π`. -/
private lemma norm_two_pi_I : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- Norm bound on the first chord `[iη, -η]` of `JourA η`. -/
private lemma chord_norm_le {η : ℝ} (hη : 0 < η) {ζ : ℂ}
    (h : ∃ t ∈ Set.Icc (0 : ℝ) 1,
      ζ = (1 - t) * (Complex.I * (η : ℂ)) + t * (-(η : ℂ))) :
    ‖ζ‖ ≤ 53 * η / 40 := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨ht0, ht1⟩ := ht
  have hcast : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
  have h1 : ‖(1 - t) * (Complex.I * (η : ℂ))‖ = (1 - t) * η := by
    rw [norm_mul, hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  have h2 : ‖t * (-(η : ℂ))‖ = t * η := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  calc ‖(1 - t) * (Complex.I * (η : ℂ)) + t * (-(η : ℂ))‖
      ≤ (1 - t) * η + t * η := by
        refine (norm_add_le _ _).trans ?_
        rw [h1, h2]
    _ = η := by ring
    _ ≤ 53 * η / 40 := by linarith

/-- Norm bound on the second chord `[-η, -iη]` of `JourA η`. -/
private lemma chord2_norm_le {η : ℝ} (hη : 0 < η) {ζ : ℂ}
    (h : ∃ t ∈ Set.Icc (0 : ℝ) 1,
      ζ = (1 - t) * (-(η : ℂ)) + t * (-(Complex.I * (η : ℂ)))) :
    ‖ζ‖ ≤ 53 * η / 40 := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨ht0, ht1⟩ := ht
  have hcast : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
  have h1 : ‖(1 - t) * (-(η : ℂ))‖ = (1 - t) * η := by
    rw [norm_mul, hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  have h2 : ‖t * (-(Complex.I * (η : ℂ)))‖ = t * η := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hη]
  calc ‖(1 - t) * (-(η : ℂ)) + t * (-(Complex.I * (η : ℂ)))‖
      ≤ (1 - t) * η + t * η := by
        refine (norm_add_le _ _).trans ?_
        rw [h1, h2]
    _ = η := by ring
    _ ≤ 53 * η / 40 := by linarith

/-- The first chord `[iη, -η]` does not meet `0`. -/
private lemma chord_ne_zero {η : ℝ} (hη : 0 < η) {t : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) * (Complex.I * (η : ℂ)) + t * (-(η : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  rcases hre with h1 | h1
  · rcases him with h3 | h3
    · linarith
    · exact hη.ne' h3
  · exact hη.ne' h1

/-- The second chord `[-η, -iη]` does not meet `0`. -/
private lemma chord2_ne_zero {η : ℝ} (hη : 0 < η) {t : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) * (-(η : ℂ)) + t * (-(Complex.I * (η : ℂ))) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  rcases hre with h1 | h1
  · rcases him with h3 | h3
    · linarith
    · exact hη.ne' h3
  · exact hη.ne' h1

/-- Zeros of `z ↦ e^{-z} - 1` in the disc `‖z‖ < 2π`: only `z = 0`. -/
private lemma exp_neg_eq_one_of_norm_lt_aux {w : ℂ} (hw : ‖w‖ < 2 * Real.pi)
    (h : Complex.exp (-w) = 1) : w = 0 := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hnorm : ‖w‖ = |(n : ℝ)| * (2 * Real.pi) := by
    have h1 := congrArg norm hn
    rw [norm_neg, norm_mul, Complex.norm_intCast, norm_two_pi_I] at h1
    exact h1
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs : |(n : ℝ)| < 1 := by
    rw [hnorm] at hw
    nlinarith [hw, hpos]
  have hn0 : n = 0 := by
    have h3 : ((|n| : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
      rw [Int.cast_abs, Int.cast_one]
      exact habs
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h3)
  rw [hn0] at hn
  simpa using hn

/-- A LOWER bound for the universal cover `τ_f = tauC σ α` on the journey `JourA η`: this is the
hypothesis `2‖σ‖ ≤ ‖τ_f ζ‖` of `Work.Pert.u_dev_le_of_nearOn_b` (it places the second fixed point
`σ` well inside the segment `[σ, τ]`).  On `JourA η` one has `‖ζ‖ ≤ 53η/40` (`Om η` gives
`η + 13η/40`, the chords give `≤ η`), so with `w = -2πiαζ`,
`‖w‖ ≤ 2π‖α‖·53η/40 ≤ 53/2560 < 1/2`, and the denominator of
`τ_f ζ = σ/(1 - e^w)` satisfies `‖1 - e^w‖ ≤ 2‖w‖ ≤ 53/1280 < 1/2` — and is nonzero since
`e^w = 1` would force `w ∈ 2πiℤ` with `‖w‖ < 2π`, so `w = 0`, hence `αζ = 0` and `ζ = 0`, which
is not in `JourA η` (the discs are at distance `≥ 27η/40` and the chords at `≥ η/√2` from `0`).
Hence `‖τ_f ζ‖ ≥ 2‖σ‖`. -/
theorem tauC_lower_jourA {σ α u₀ : ℂ} {η : ℝ} (hη : 0 < η)
    (hσ : σ ≠ 0) (hα : α ≠ 0) (hu₀ : ‖u₀ - 1‖ ≤ 1 / 1024)
    (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64)
    (heq : 1 - σ * u₀ = Complex.exp (2 * Real.pi * Complex.I * α)) :
    ∀ ζ ∈ Work.Pert.JourA η, 2 * ‖σ‖ ≤ ‖Work.Pert.tauC σ α ζ‖ := by
  intro ζ hζ
  -- the two geometric facts about the journey
  have hζle : ‖ζ‖ ≤ 53 * η / 40 := by
    have hmem := hζ
    rw [Work.Pert.JourA] at hmem
    rw [Set.mem_union, Set.mem_union] at hmem
    rcases hmem with h | h
    · rcases h with h | h
      · exact (Om_norm_bounds hη ζ h).2
      · exact chord_norm_le hη h
    · exact chord2_norm_le hη h
  have hζne : ζ ≠ 0 := by
    have hmem := hζ
    rw [Work.Pert.JourA] at hmem
    rw [Set.mem_union, Set.mem_union] at hmem
    rcases hmem with h | h
    · rcases h with h | h
      · intro hz
        have hb := (Om_norm_bounds hη ζ h).1
        rw [hz, norm_zero] at hb
        linarith
      · obtain ⟨t, ht, rfl⟩ := h
        exact chord_ne_zero hη ht
    · obtain ⟨t, ht, rfl⟩ := h
      exact chord2_ne_zero hη ht
  -- the frequency `w = 2πi α ζ`
  set w : ℂ := (2 * Real.pi * Complex.I) * (α * ζ) with hwdef
  have hw_norm : ‖w‖ = 2 * Real.pi * ‖α‖ * ‖ζ‖ := by
    rw [hwdef, norm_mul, norm_two_pi_I, norm_mul]
    ring
  have hw_le : ‖w‖ ≤ 53 / 2560 := by
    rw [hw_norm]
    have hnn : (0 : ℝ) ≤ 2 * Real.pi * ‖α‖ := by positivity
    have h1 : 2 * Real.pi * ‖α‖ * ‖ζ‖ ≤ 2 * Real.pi * ‖α‖ * (53 * η / 40) :=
      mul_le_mul_of_nonneg_left hζle hnn
    have h2 : 2 * Real.pi * ‖α‖ * (53 * η / 40) = (53 / 40) * (2 * Real.pi * ‖α‖ * η) := by ring
    linarith
  have hw_lt : ‖w‖ < 2 * Real.pi := by linarith [hw_le, Real.pi_gt_three]
  have hw_lt_half : ‖w‖ < 1 / 2 := by linarith
  -- the denominator of `τ_f ζ = σ/(1 - e^{-w})` is close to `1` ...
  have hden_le : ‖(1 : ℂ) - Complex.exp (-w)‖ ≤ 1 / 2 := by
    have hpi : ‖(-w)‖ ≤ Real.pi / 2 := by
      rw [norm_neg]
      linarith [hw_lt_half, Real.pi_gt_three]
    have h := norm_exp_sub_one_le_of_le_pi_half (z := -w) hpi
    rw [norm_neg] at h
    have heq' : (1 : ℂ) - Complex.exp (-w) = -(Complex.exp (-w) - 1) := by ring
    rw [heq', norm_neg]
    have : (27 / 10 : ℝ) * ‖w‖ ≤ (27 / 10) * (53 / 2560) :=
      mul_le_mul_of_nonneg_left hw_le (by norm_num)
    linarith
  -- ... and nonzero
  have h2pii : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    intro h
    have hnorm := norm_two_pi_I
    rw [h, norm_zero] at hnorm
    linarith [Real.pi_pos]
  have hden_ne : (1 : ℂ) - Complex.exp (-w) ≠ 0 := by
    intro h0
    have hexp : Complex.exp (-w) = 1 := (sub_eq_zero.mp h0).symm
    have hw0 : w = 0 := exp_neg_eq_one_of_norm_lt_aux hw_lt hexp
    have h2 : (2 * Real.pi * Complex.I) * (α * ζ) = 0 := by rw [← hwdef]; exact hw0
    exact hζne ((mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left h2pii)).resolve_left hα)
  have hden_pos : 0 < ‖(1 : ℂ) - Complex.exp (-w)‖ := norm_pos_iff.mpr hden_ne
  -- the value of `τ_f` at `ζ`
  have htau : Work.Pert.tauC σ α ζ = σ / ((1 : ℂ) - Complex.exp (-w)) := by
    rw [Work.Pert.tauC]
    have harg : -(2 * Real.pi * Complex.I * α * ζ) = -w := by
      rw [hwdef]; ring
    rw [harg]
  rw [htau, Complex.norm_div, le_div_iff₀ hden_pos]
  nlinarith [hden_le, norm_nonneg σ]

end

end Work.Pert
