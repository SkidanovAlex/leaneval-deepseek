import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FIArea6V.S16_main_le_twoV
import Submission.Work.FITop4.Areas6c
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea6c.S16_char_bound_twoP
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea4.S15box
import Submission.Work.FIArea6.S16Assembly
import Submission.Work.FIArea6.DetSum_le_of_chiBound
import Submission.Work.FIArea6.S16_elem_alt
import Submission.Work.FIArea6.S16_beta_mass6
import Submission.Work.FIArea6.S16_exp_arith
import Submission.Work.FIArea6.S16_sum_chain
import Submission.Work.FIArea6.S16_final_arith
import Submission.Work.FIArea6c.area6c_error_bound
import Submission.Work.FIArea6.Ucut_sub_Umain_le
import Submission.Work.FIArea6.four_mul_le_Pz

set_option autoImplicit false

namespace Work.FIArea6V

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The §16 display for the cut `Ucut` in the clean (τ-vacuous) lane**, from the two-constant form
of Lemma 16.2 (`Work.FIArea6V.Area5TwoV`).

This is the V-lane counterpart of `Work.FIArea6.section16_Ucut_twoP`: the split
`‖Ucut‖ ≤ ‖Umain‖ + 2Σ_{d≤X}(φ(d)/d)‖Vd − MainSum‖` of `Ucut_sub_Umain_le` is fed the clean main
bound `S16_main_le_twoV` (the pin `Pa.τ = tauOf Pa.x Asave` replaced by `TauVac Pa φ`) and the
pin-independent error bound `area6c_error_bound`, and the two constants are amalgamated
(`max C1 C2`, with the `Pz`-threshold `four_mul_le_Pz` ensuring the error quality `X ≤ Pz/4`). -/
theorem section16_Ucut_twoV (h : Work.FIArea6V.Area5TwoV) : Work.FIArea6V.Section16UV := by
  intro η hη0 hη32
  obtain ⟨C1, c1, c2, x1, hC1, hc1, hc2, hx1, hmain⟩ := S16_main_le_twoV h η hη0 hη32
  obtain ⟨C2, x2, hC2, hx2, herr⟩ := Work.FIArea6.area6c_error_bound
  refine ⟨max C1 C2, c1, c2,
    max x1 (max x2 (Real.exp (4 * Real.exp (Work.FITop4.nuU + 2)))),
    lt_max_of_lt_left hC1, hc1, hc2,
    lt_max_of_lt_right (lt_max_of_lt_right (Real.exp_pos _)), ?_⟩
  intro Pa hx hηPa X φ z0 β hβ hτ hfar hX hXle hXcube
  have hx1' : x1 ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx
  have hx2' : x2 ≤ (Pa.x : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxT : Real.exp (4 * Real.exp (Work.FITop4.nuU + 2)) ≤ (Pa.x : ℝ) :=
    le_trans (le_trans (le_max_right x2 _) (le_max_right _ _)) hx
  have hP : 4 * X ≤ Pa.Pz := Work.FIArea6.four_mul_le_Pz Pa X hxT hXle
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hsplit := Work.FIArea6.Ucut_sub_Umain_le Pa X β
  have h1 := hmain Pa hx1' hηPa X φ z0 β hβ hτ hfar hX hXle hXcube
  have h2 := herr Pa X φ z0 β hx2' hβ hX hXle
  have hMnn : (0 : ℝ) ≤ (Real.exp (-(c1 * (Real.log Pa.N) ^ ((1 : ℝ) / 4)))
        + Real.exp (-(c2 * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
      * (X : ℝ) ^ (5 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log (2 + Pa.N)) ^ (13 : ℕ) := by
    have h5 : (0 : ℝ) ≤ (X : ℝ) ^ (5 : ℕ) := by positivity
    have h6 : (0 : ℝ) ≤ Pa.N ^ (2 : ℕ) := by positivity
    have h7 : (0 : ℝ) ≤ (Real.log (2 + Pa.N)) ^ (13 : ℕ) :=
      pow_nonneg (Real.log_nonneg (by linarith)) 13
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) h5) h6) h7
  have hEnn : (0 : ℝ) ≤ ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ (2 : ℕ) * Real.log Pa.N := by
    have hPzpos : (0 : ℝ) < (Pa.Pz : ℝ) := by
      have h : (2 : ℕ) ≤ Pa.Pz := Pa.hP2
      have h2 : (0 : ℕ) < Pa.Pz := lt_of_lt_of_le (by norm_num) h
      exact_mod_cast h2
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      have h : (0 : ℕ) < X := lt_of_lt_of_le Nat.zero_lt_one hX
      exact_mod_cast h
    have h1 : (0 : ℝ) ≤ (Pa.Pz : ℝ)⁻¹ := inv_nonneg.mpr hPzpos.le
    have h2 : (0 : ℝ) ≤ (X : ℝ)⁻¹ := inv_nonneg.mpr hXpos.le
    have h3 : (0 : ℝ) ≤ Pa.N ^ (2 : ℕ) := by positivity
    have h4 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
    exact mul_nonneg (mul_nonneg (add_nonneg h1 h2) h3) h4
  have step1 : ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β‖
      ≤ C1 * ((Real.exp (-(c1 * (Real.log Pa.N) ^ ((1 : ℝ) / 4)))
            + Real.exp (-(c2 * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
          * (X : ℝ) ^ (5 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log (2 + Pa.N)) ^ (13 : ℕ))
        + C2 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ (2 : ℕ) * Real.log Pa.N :=
    le_trans hsplit (add_le_add h1 h2)
  have hMc : C1 * ((Real.exp (-(c1 * (Real.log Pa.N) ^ ((1 : ℝ) / 4)))
          + Real.exp (-(c2 * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
        * (X : ℝ) ^ (5 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log (2 + Pa.N)) ^ (13 : ℕ))
      ≤ max C1 C2 * ((Real.exp (-(c1 * (Real.log Pa.N) ^ ((1 : ℝ) / 4)))
          + Real.exp (-(c2 * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
        * (X : ℝ) ^ (5 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log (2 + Pa.N)) ^ (13 : ℕ)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hMnn
  have hEc : C2 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ (2 : ℕ) * Real.log Pa.N
      ≤ max C1 C2 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ (2 : ℕ) * Real.log Pa.N := by
    have hA : (0 : ℝ) ≤ (Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹ := by
      have h1 : (0 : ℝ) < (Pa.Pz : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) Pa.hP2)
      have h2 : (0 : ℝ) < (X : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
      positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hA)
        (by positivity : (0 : ℝ) ≤ Pa.N ^ (2 : ℕ)))
      (Real.log_nonneg hN1)
  linarith [step1, hMc, hEc]

end

end Work.FIArea6V
