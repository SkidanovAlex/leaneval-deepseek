import Mathlib
import Submission.Work.Drive.N2Lead.upperArcToolkit

namespace Work.Drive.N2Lead

/-!
# The `y`-sign row of the two upper model arcs of the Möbius saddle

`Work.Drive.N2Lead.upperArcsYSigns`: on `[-2,2]` the untwisted arcs `α = mobiusAlpha` and
`β = mobiusBeta` lie in the half-spaces `{y > 0}` and `{y < 0}`.

After the two slab twists the `y`-coordinate of `α` is

  `y_α = -uaB · cos uaPsi + uaA · sin uaTh · sin uaPsi`

(`mobiusAlpha_one`), and the `y`-coordinate of `β` is its negative (`mobiusBeta_one`).  The sign
comes from the sign of the cosine of the two twist angles, which we read off through the identity
`cos (π · ST t) < 0 ↔ 1/2 < ST t` together with `ST (1/2) = 1/2` and the monotonicity of `ST`:

* `uaTh = π · ST ((a' - uaB)/(2a'))`, so `cos uaTh` has the sign of `uaB`
  (and vanishes exactly when `uaB = 0`);
* `uaX = uaA · cos uaTh`, so `uaX` has the sign of `uaB` as well (`uaA > 0`);
* `uaPsi = π · ST ((uaX + ε)/(2ε))`, so `cos uaPsi` has the sign of `uaX`.

Hence for `uaB > 0` the product `-uaB · cos uaPsi` is positive (negative times negative), for
`uaB < 0` positive (positive times positive), and for `uaB = 0` (i.e. `w = 0`) the first term
vanishes while `sin uaTh = sin uaPsi = 1` makes the second term `uaA > 0`.
-/

/-- `cos (π t) < 0 ↔ t > 1/2` for `t ∈ [0,1]`. -/
lemma cos_pi_mul_lt_zero_iff {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Real.cos (Real.pi * u) < 0 ↔ 1 / 2 < u := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hx : (0 : ℝ) ≤ Real.cos (Real.pi * u) :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by nlinarith [Real.pi_pos, h0], by nlinarith [Real.pi_pos, hcon]⟩
    linarith
  · intro h
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith [Real.pi_pos, h])
      (by nlinarith [Real.pi_pos, h1])

/-- `cos (π t) > 0 ↔ t < 1/2` for `t ∈ [0,1]`. -/
lemma cos_pi_mul_pos_iff {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 < Real.cos (Real.pi * u) ↔ u < 1 / 2 := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hx : Real.cos (Real.pi * u) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith [Real.pi_pos, hcon])
        (by nlinarith [Real.pi_pos, h1])
    linarith
  · intro h
    exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, h0], by nlinarith [Real.pi_pos, h]⟩

/-- The sign of `cos` of the first twist angle `π · ST ((A - b)/(2A))`, `A > 0`. -/
lemma cos_pi_st_div_neg_iff {A b : ℝ} (hA : 0 < A) :
    Real.cos (Real.pi * Real.smoothTransition ((A - b) / (2 * A))) < 0 ↔ b < 0 := by
  have h2A : (0 : ℝ) < 2 * A := by linarith
  have key := cos_pi_mul_lt_zero_iff (u := Real.smoothTransition ((A - b) / (2 * A)))
    (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
  rw [key, st_half_lt_iff, lt_div_iff₀ h2A]
  constructor <;> intro h <;> linarith

/-- The sign of `cos` of the first twist angle `π · ST ((A - b)/(2A))`, `A > 0`. -/
lemma cos_pi_st_div_pos_iff {A b : ℝ} (hA : 0 < A) :
    0 < Real.cos (Real.pi * Real.smoothTransition ((A - b) / (2 * A))) ↔ 0 < b := by
  have h2A : (0 : ℝ) < 2 * A := by linarith
  have key := cos_pi_mul_pos_iff (u := Real.smoothTransition ((A - b) / (2 * A)))
    (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
  rw [key, st_lt_half_iff, div_lt_iff₀ h2A]
  constructor <;> intro h <;> linarith

/-- The sign of `cos` of the second twist angle `π · ST ((x + ε)/(2ε))`, `ε > 0`. -/
lemma cos_pi_st_shift_neg_iff {ε x : ℝ} (hε : 0 < ε) :
    Real.cos (Real.pi * Real.smoothTransition ((x + ε) / (2 * ε))) < 0 ↔ 0 < x := by
  have h2ε : (0 : ℝ) < 2 * ε := by linarith
  have key := cos_pi_mul_lt_zero_iff (u := Real.smoothTransition ((x + ε) / (2 * ε)))
    (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
  rw [key, st_half_lt_iff, lt_div_iff₀ h2ε]
  constructor <;> intro h <;> linarith

/-- The sign of `cos` of the second twist angle `π · ST ((x + ε)/(2ε))`, `ε > 0`. -/
lemma cos_pi_st_shift_pos_iff {ε x : ℝ} (hε : 0 < ε) :
    0 < Real.cos (Real.pi * Real.smoothTransition ((x + ε) / (2 * ε))) ↔ x < 0 := by
  have h2ε : (0 : ℝ) < 2 * ε := by linarith
  have key := cos_pi_mul_pos_iff (u := Real.smoothTransition ((x + ε) / (2 * ε)))
    (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
  rw [key, st_lt_half_iff, div_lt_iff₀ h2ε]
  constructor <;> intro h <;> linarith

theorem upperArcsYSigns {η δ s a' ε : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hη : 0 < η)
    (hs : 0 < s) (ha' : 0 < a') (hε : 0 < ε) :
    ∀ w ∈ Set.Icc (-2) 2,
      0 < (Work.Drive.N2Lead.mobiusAlpha η δ s a' ε w) 1 ∧
      (Work.Drive.N2Lead.mobiusBeta η δ s a' ε w) 1 < 0 := by
  intro w _
  have hA : 0 < uaA η δ s w := uaA_pos hδ hη hs hδ₂ w
  have hθmem : uaTh η δ s a' w ∈ Set.Icc (0 : ℝ) Real.pi := by
    rw [uaTh]
    exact ⟨mul_nonneg Real.pi_pos.le (Real.smoothTransition.nonneg _),
      by nlinarith [Real.pi_pos,
        Real.smoothTransition.le_one ((a' - uaB η δ s w) / (2 * a'))]⟩
  have hψmem : uaPsi η δ s a' ε w ∈ Set.Icc (0 : ℝ) Real.pi := by
    rw [uaPsi]
    exact ⟨mul_nonneg Real.pi_pos.le (Real.smoothTransition.nonneg _),
      by nlinarith [Real.pi_pos,
        Real.smoothTransition.le_one ((uaX η δ s a' w + ε) / (2 * ε))]⟩
  have hsinθ : 0 ≤ Real.sin (uaTh η δ s a' w) := Real.sin_nonneg_of_mem_Icc hθmem
  have hsinψ : 0 ≤ Real.sin (uaPsi η δ s a' ε w) := Real.sin_nonneg_of_mem_Icc hψmem
  have h2 : 0 ≤ uaA η δ s w * Real.sin (uaTh η δ s a' w) * Real.sin (uaPsi η δ s a' ε w) :=
    mul_nonneg (mul_nonneg hA.le hsinθ) hsinψ
  have hα : 0 < -uaB η δ s w * Real.cos (uaPsi η δ s a' ε w)
      + uaA η δ s w * Real.sin (uaTh η δ s a' w) * Real.sin (uaPsi η δ s a' ε w) := by
    rcases lt_trichotomy (uaB η δ s w) 0 with hB | hB | hB
    · -- `uaB < 0`: `cos uaPsi > 0`, and `-uaB > 0`
      have hcosθ : Real.cos (uaTh η δ s a' w) < 0 := by
        rw [uaTh]
        exact (cos_pi_st_div_neg_iff (A := a') (b := uaB η δ s w) ha').mpr hB
      have hx : uaX η δ s a' w < 0 := by
        rw [uaX]
        exact mul_neg_of_pos_of_neg hA hcosθ
      have hcosψ : 0 < Real.cos (uaPsi η δ s a' ε w) := by
        rw [uaPsi]
        exact (cos_pi_st_shift_pos_iff (x := uaX η δ s a' w) hε).mpr hx
      have h1 : 0 < -uaB η δ s w * Real.cos (uaPsi η δ s a' ε w) :=
        mul_pos (by linarith) hcosψ
      linarith
    · -- `uaB = 0` (i.e. `w = 0`): both twist angles are `π/2`
      have harg : (a' - uaB η δ s w) / (2 * a') = 1 / 2 := by
        rw [hB, sub_zero, div_eq_iff (ne_of_gt (by linarith : (0 : ℝ) < 2 * a'))]
        ring
      have hθ : uaTh η δ s a' w = Real.pi / 2 := by
        rw [uaTh, harg, st_half]
        ring
      have hx : uaX η δ s a' w = 0 := by
        rw [uaX, hθ, Real.cos_pi_div_two, mul_zero]
      have harg2 : (uaX η δ s a' w + ε) / (2 * ε) = 1 / 2 := by
        rw [hx, zero_add, div_eq_iff (ne_of_gt (by linarith : (0 : ℝ) < 2 * ε))]
        ring
      have hψ : uaPsi η δ s a' ε w = Real.pi / 2 := by
        rw [uaPsi, harg2, st_half]
        ring
      have hsθ : Real.sin (uaTh η δ s a' w) = 1 := by rw [hθ, Real.sin_pi_div_two]
      have hsψ : Real.sin (uaPsi η δ s a' ε w) = 1 := by rw [hψ, Real.sin_pi_div_two]
      have hcψ : Real.cos (uaPsi η δ s a' ε w) = 0 := by rw [hψ, Real.cos_pi_div_two]
      rw [hcψ, hsθ, hsψ]
      simpa using hA
    · -- `0 < uaB`: `cos uaPsi < 0`, and `-uaB < 0`
      have hcosθ : 0 < Real.cos (uaTh η δ s a' w) := by
        rw [uaTh]
        exact (cos_pi_st_div_pos_iff (A := a') (b := uaB η δ s w) ha').mpr hB
      have hx : 0 < uaX η δ s a' w := by
        rw [uaX]
        exact mul_pos hA hcosθ
      have hcosψ : Real.cos (uaPsi η δ s a' ε w) < 0 := by
        rw [uaPsi]
        exact (cos_pi_st_shift_neg_iff (x := uaX η δ s a' w) hε).mpr hx
      have h1 : 0 < -uaB η δ s w * Real.cos (uaPsi η δ s a' ε w) :=
        mul_pos_of_neg_of_neg (by linarith) hcosψ
      linarith
  constructor
  · rw [mobiusAlpha_one η δ s a' ε w ha']
    exact hα
  · rw [mobiusBeta_one η δ s a' ε w]
    have hneg : uaB η δ s w * Real.cos (uaPsi η δ s a' ε w)
        - uaA η δ s w * Real.sin (uaTh η δ s a' w) * Real.sin (uaPsi η δ s a' ε w)
        = -( -uaB η δ s w * Real.cos (uaPsi η δ s a' ε w)
            + uaA η δ s w * Real.sin (uaTh η δ s a' w)
              * Real.sin (uaPsi η δ s a' ε w)) := by ring
    rw [hneg]
    linarith

end Work.Drive.N2Lead
