import Mathlib
import Submission.Work.Drive.shiftedNeedleDefs

/-!
# The window bound for the branch fraction of the shifted needle

`Work.Drive.needleFrac lam τ` is the fraction of the needle's retained arc / chord at which the
loop point `sweepLoopChamfer r D lam σ τ` sits.  This file proves `Work.Drive.needleFrac_window`:
over any window of loop parameters `τ - δ u` (`u ∈ [-1,1]`) of total length `2δ ≤ period/8`,
one of five uniform statements holds — the window is entirely on the arc side (with `τ` before
`period/2`, resp. after `period`), entirely inside the chord zone, or the branch fraction is
uniformly bounded below by `1 - lam - 32 δ/period`, resp. above by `lam + 32 δ/period`.

The proof is a case analysis on the position `T = τ/period` of the window (of half width
`c = δ/period ≤ 1/16`) modulo the period; the analytic content is the piecewise affine shape of
`needleFrac`, whose slope on the chord zone is `-2`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## Elementary floor facts -/

/-- The floor of a real in `[0,1)` is `0`. -/
lemma floor_eq_zero_of_mem_Ico {s : ℝ} (h : s ∈ Set.Ico (0 : ℝ) 1) : ⌊s⌋ = 0 := by
  rw [Int.floor_eq_iff]
  refine ⟨by simpa using h.1, ?_⟩
  push_cast
  linarith [h.2]

/-- The floor of a real in `[1,2)` is `1`. -/
lemma floor_eq_one_of_mem_Ico {s : ℝ} (h : s ∈ Set.Ico (1 : ℝ) 2) : ⌊s⌋ = 1 := by
  rw [Int.floor_eq_iff]
  refine ⟨by simpa using h.1, ?_⟩
  push_cast
  linarith [h.2]

/-- If the normalized parameter lies in `(0,1)`, the sawtooth is the parameter itself. -/
lemma sweepParam_eq_div_of_mem {t : ℝ} (h0 : 0 < t / period) (h1 : t / period < 1) :
    sweepParam t = t / period := by
  rw [sweepParam, floor_eq_zero_of_mem_Ico ⟨le_of_lt h0, h1⟩]
  push_cast
  ring

/-! ## The affine form of the chord fraction -/

/-- On the chord zone the chord fraction is affine with slope `-2`. -/
lemma sweepChordParam_eq_two {lam u : ℝ} (h : lam ≠ 1 / 2) :
    sweepChordParam lam u = (1 - lam) - 2 * (u - (1 / 2 + lam / 2)) := by
  have hd : (1 / 2 - lam : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [sweepChordParam, show (1 - 2 * lam : ℝ) = 2 * (1 / 2 - lam) by ring]
  rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ hd, mul_comm]

/-! ## The three analytic windows of the branch fraction -/

/-- **Lower bound of the branch fraction on a left window.**  If the sawtooth lies in
`[1/2 - 2c, 1/2 + lam/2 + 2c]`, then the branch fraction is `≥ 1 - lam - 32c`. -/
lemma needleFrac_lower_window {lam t c : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 16)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 16)
    (hlo : 1 / 2 - 2 * c ≤ sweepParam t)
    (hhi : sweepParam t ≤ 1 / 2 + lam / 2 + 2 * c) :
    1 - lam - 32 * c ≤ needleFrac lam t := by
  have hξ : sweepParam t < 1 := (sweepParam_mem t).2
  have hlam2 : lam ≠ 1 / 2 := by linarith
  have hsmall : lam + 2 * c ≤ 1 / 2 := by linarith
  rcases le_or_gt (sweepParam t) (1 / 2) with h | h
  · rw [needleFrac_arc h]
    have hstep : (1 - 2 * lam) * (1 - 4 * c) ≤ (1 - 2 * lam) * (2 * sweepParam t) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      linarith
    have hmid : 1 - lam - 32 * c ≤ lam + (1 - 2 * lam) * (1 - 4 * c) := by
      have h8 : (1 - 2 * lam) * (4 * c) ≤ 32 * c := by
        have h9 : (1 - 2 * lam : ℝ) ≤ 8 := by linarith
        have h10 := mul_le_mul_of_nonneg_right h9 (by linarith : (0 : ℝ) ≤ 4 * c)
        linarith
      nlinarith [h8]
    linarith
  · rcases le_or_gt (sweepParam t) (1 / 2 + lam / 2) with h2 | h2
    · rw [needleFrac_head (not_le.mpr h) h2]
      linarith
    · rw [needleFrac_chord (not_le.mpr h) (not_le.mpr h2) (by linarith),
        sweepChordParam_eq_two hlam2]
      linarith

/-- **Upper bound of the branch fraction on a right window.**  If the sawtooth lies in
`[1 - lam/2 - 2c, 1]`, then the branch fraction is `≤ lam + 32c`. -/
lemma needleFrac_upper_large_window {lam t c : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 16)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 16)
    (hlo : 1 - lam / 2 - 2 * c ≤ sweepParam t) :
    needleFrac lam t ≤ lam + 32 * c := by
  have hξ : sweepParam t < 1 := (sweepParam_mem t).2
  have hlam2 : lam ≠ 1 / 2 := by linarith
  have hge : 1 / 2 + lam / 2 ≤ sweepParam t := by linarith
  rcases le_or_gt (sweepParam t) (1 - lam / 2) with h | h
  · rw [needleFrac_chord (by linarith) (by linarith) h, sweepChordParam_eq_two hlam2]
    linarith
  · rw [needleFrac_tail (by linarith) (by linarith) (not_le.mpr h)]
    linarith

/-- **Upper bound of the branch fraction on a small window near the chord end.**  If the sawtooth
is `≤ 2c` (and `2c ≤ 1/2`, so that we are on the arc piece), the branch fraction is
`≤ lam + 32c`. -/
lemma needleFrac_upper_small_window {lam t c : ℝ} (h0 : 0 < lam) (hc0 : 0 < c)
    (hhi : sweepParam t ≤ 2 * c) (hc : 2 * c ≤ 1 / 2) :
    needleFrac lam t ≤ lam + 32 * c := by
  have hξ0 : (0 : ℝ) ≤ sweepParam t := (sweepParam_mem t).1
  rw [needleFrac_arc (by linarith)]
  have h1 : (1 - 2 * lam) * (2 * sweepParam t) ≤ 2 * sweepParam t := by
    have := mul_le_mul_of_nonneg_right (show (1 - 2 * lam : ℝ) ≤ 1 by linarith)
      (show (0 : ℝ) ≤ 2 * sweepParam t by linarith)
    simpa using this
  linarith

/-! ## The window theorem -/

theorem needleFrac_window {lam δ τ : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 16) (h2 : 0 < δ)
    (h3 : 16 * δ ≤ LeanEval.KnotTheory.Quadrisecant.period)
    (h4 : LeanEval.KnotTheory.Quadrisecant.period / 4 < τ)
    (h5 : τ < 5 * LeanEval.KnotTheory.Quadrisecant.period / 4) :
    ((∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
        Work.Drive.sweepParam (τ - δ * u) ≤ 1 / 2) ∧
        τ < LeanEval.KnotTheory.Quadrisecant.period / 2)
    ∨ ((∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
        Work.Drive.sweepParam (τ - δ * u) ≤ 1 / 2) ∧
        LeanEval.KnotTheory.Quadrisecant.period < τ)
    ∨ (∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
        1 / 2 + lam / 2 ≤ Work.Drive.sweepParam (τ - δ * u) ∧
          Work.Drive.sweepParam (τ - δ * u) ≤ 1 - lam / 2)
    ∨ (∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
        1 - lam - 32 * (δ / LeanEval.KnotTheory.Quadrisecant.period)
          ≤ Work.Drive.needleFrac lam (τ - δ * u))
    ∨ (∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
        Work.Drive.needleFrac lam (τ - δ * u)
          ≤ lam + 32 * (δ / LeanEval.KnotTheory.Quadrisecant.period)) := by
  set T : ℝ := τ / period with hT
  set c : ℝ := δ / period with hc
  have hP : 0 < period := period_pos
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 / 16 := by
    rw [hc, div_le_iff₀ hP]
    linarith
  have hT0 : 1 / 4 < T := by
    rw [hT, lt_div_iff₀ hP]
    linarith
  have hT1 : T < 5 / 4 := by
    rw [hT, div_lt_iff₀ hP]
    linarith
  have hcpos : (0 : ℝ) ≤ c := hc0.le
  have hTmc : 0 < T - c := by linarith
  have key_eq : ∀ u : ℝ, (τ - δ * u) / period = T - c * u := by
    intro u
    rw [hT, hc, sub_div]
    congr 1
    rw [div_mul_eq_mul_div]
  by_cases hA : T + c ≤ 1 / 2
  · -- the window is in the first half of the first period
    left
    refine ⟨?_, ?_⟩
    · intro u hu
      have hs : (τ - δ * u) / period = T - c * u := key_eq u
      have hcu_le : c * u ≤ c := by
        have := mul_le_mul_of_nonneg_left hu.2 hcpos
        simpa using this
      have hcu_ge : -c ≤ c * u := by
        have := mul_le_mul_of_nonneg_left hu.1 hcpos
        simpa using this
      have hsle : (τ - δ * u) / period ≤ 1 / 2 := by rw [hs]; linarith
      have hs0 : 0 < (τ - δ * u) / period := by rw [hs]; linarith [hTmc, hcu_le]
      have hfl : (0 : ℝ) ≤ ((⌊(τ - δ * u) / period⌋ : ℤ) : ℝ) := by
        have h0' : (0 : ℤ) ≤ ⌊(τ - δ * u) / period⌋ := by
          rw [Int.floor_nonneg]
          exact le_of_lt hs0
        exact_mod_cast h0'
      rw [sweepParam]
      linarith
    · have h : T < 1 / 2 := by linarith
      rw [hT, div_lt_iff₀ hP] at h
      linarith
  · by_cases hB : 1 ≤ T - c
    · -- the window is in the second half of the first period, after `period`
      right; left
      refine ⟨?_, ?_⟩
      · intro u hu
        have hs : (τ - δ * u) / period = T - c * u := key_eq u
        have hcu_le : c * u ≤ c := by
          have := mul_le_mul_of_nonneg_left hu.2 hcpos
          simpa using this
        have hcu_ge : -c ≤ c * u := by
          have := mul_le_mul_of_nonneg_left hu.1 hcpos
          simpa using this
        have hsge : 1 ≤ (τ - δ * u) / period := by rw [hs]; linarith
        have hsle : (τ - δ * u) / period ≤ T + c := by rw [hs]; linarith
        have hs2 : (τ - δ * u) / period < 2 := by linarith [hT1, hc1]
        have hfl : ⌊(τ - δ * u) / period⌋ = 1 := floor_eq_one_of_mem_Ico ⟨hsge, hs2⟩
        rw [sweepParam, hfl]
        push_cast
        linarith [hT1, hc1]
      · have h : 1 < T := by linarith
        rw [hT, lt_div_iff₀ hP] at h
        linarith
    · have hTc : T - c < 1 := lt_of_not_ge hB
      have hTpc : 1 / 2 < T + c := lt_of_not_ge hA
      by_cases hCa : 1 ≤ T + c
      · -- the window straddles a period boundary: clause (5)
        right; right; right; right
        intro u hu
        have hs : (τ - δ * u) / period = T - c * u := key_eq u
        have hcu_le : c * u ≤ c := by
          have := mul_le_mul_of_nonneg_left hu.2 hcpos
          simpa using this
        have hcu_ge : -c ≤ c * u := by
          have := mul_le_mul_of_nonneg_left hu.1 hcpos
          simpa using this
        have hs_ge : T - c ≤ (τ - δ * u) / period := by rw [hs]; linarith
        have hs_le : (τ - δ * u) / period ≤ T + c := by rw [hs]; linarith
        rcases lt_or_ge ((τ - δ * u) / period) 1 with hsl | hsg
        · have hs0 : 0 < (τ - δ * u) / period := by linarith [hTmc, hs_ge]
          have hfl : ⌊(τ - δ * u) / period⌋ = 0 :=
            floor_eq_zero_of_mem_Ico ⟨le_of_lt hs0, hsl⟩
          have hξ : sweepParam (τ - δ * u) = (τ - δ * u) / period := by
            rw [sweepParam, hfl]; push_cast; ring
          refine needleFrac_upper_large_window h0 h1 hc0 hc1 ?_
          rw [hξ]
          linarith [hs_ge, hCa]
        · have hs2 : (τ - δ * u) / period < 2 := by linarith [hT1, hc1, hs_le]
          have hfl : ⌊(τ - δ * u) / period⌋ = 1 := floor_eq_one_of_mem_Ico ⟨hsg, hs2⟩
          have hξ : sweepParam (τ - δ * u) = (τ - δ * u) / period - 1 := by
            rw [sweepParam, hfl]; push_cast; ring
          refine needleFrac_upper_small_window h0 hc0 ?_ ?_
          · rw [hξ]; linarith [hs_le, hTc]
          · linarith [hc1]
      · -- the window lies strictly inside one period
        have hTcl : T + c < 1 := lt_of_not_ge hCa
        by_cases hC1 : 1 / 2 + lam / 2 + c ≤ T ∧ T ≤ 1 - lam / 2 - c
        · -- the window is inside the chord zone: clause (3)
          right; right; left
          intro u hu
          have hs : (τ - δ * u) / period = T - c * u := key_eq u
          have hcu_le : c * u ≤ c := by
            have := mul_le_mul_of_nonneg_left hu.2 hcpos
            simpa using this
          have hcu_ge : -c ≤ c * u := by
            have := mul_le_mul_of_nonneg_left hu.1 hcpos
            simpa using this
          have hs_ge : T - c ≤ (τ - δ * u) / period := by rw [hs]; linarith
          have hs_le : (τ - δ * u) / period ≤ T + c := by rw [hs]; linarith
          have hs1 : (τ - δ * u) / period < 1 := by linarith
          have hs0 : 0 < (τ - δ * u) / period := by linarith [hTmc, hs_ge]
          have hξ : sweepParam (τ - δ * u) = (τ - δ * u) / period :=
            sweepParam_eq_div_of_mem hs0 hs1
          rw [hξ]
          exact ⟨by linarith [hs_ge, hC1.1], by linarith [hs_le, hC1.2]⟩
        · by_cases hC2 : T < 1 / 2 + lam / 2 + c
          · -- the window is at the left end of the chord zone: clause (4)
            right; right; right; left
            intro u hu
            have hs : (τ - δ * u) / period = T - c * u := key_eq u
            have hcu_le : c * u ≤ c := by
              have := mul_le_mul_of_nonneg_left hu.2 hcpos
              simpa using this
            have hcu_ge : -c ≤ c * u := by
              have := mul_le_mul_of_nonneg_left hu.1 hcpos
              simpa using this
            have hs_ge : T - c ≤ (τ - δ * u) / period := by rw [hs]; linarith
            have hs_le : (τ - δ * u) / period ≤ T + c := by rw [hs]; linarith
            have hs1 : (τ - δ * u) / period < 1 := by linarith
            have hs0 : 0 < (τ - δ * u) / period := by linarith [hTmc, hs_ge]
            have hξ : sweepParam (τ - δ * u) = (τ - δ * u) / period :=
              sweepParam_eq_div_of_mem hs0 hs1
            refine needleFrac_lower_window h0 h1 hc0 hc1 ?_ ?_
            · rw [hξ]; linarith [hs_ge, hTpc]
            · rw [hξ]; linarith [hs_le, hC2]
          · -- the window is at the right end of the chord zone: clause (5)
            right; right; right; right
            intro u hu
            have hT3 : 1 - lam / 2 - c < T := by
              by_contra hcon
              exact hC1 ⟨not_lt.mp hC2, not_lt.mp hcon⟩
            have hs : (τ - δ * u) / period = T - c * u := key_eq u
            have hcu_le : c * u ≤ c := by
              have := mul_le_mul_of_nonneg_left hu.2 hcpos
              simpa using this
            have hcu_ge : -c ≤ c * u := by
              have := mul_le_mul_of_nonneg_left hu.1 hcpos
              simpa using this
            have hs_ge : T - c ≤ (τ - δ * u) / period := by rw [hs]; linarith
            have hs_le : (τ - δ * u) / period ≤ T + c := by rw [hs]; linarith
            have hs1 : (τ - δ * u) / period < 1 := by linarith
            have hs0 : 0 < (τ - δ * u) / period := by linarith [hTmc, hs_ge]
            have hξ : sweepParam (τ - δ * u) = (τ - δ * u) / period :=
              sweepParam_eq_div_of_mem hs0 hs1
            refine needleFrac_upper_large_window h0 h1 hc0 hc1 ?_
            rw [hξ]; linarith [hs_ge, hT3]

end Work.Drive
