import Mathlib
import Submission.Work.FIArea2.R6.KCap
import Submission.Work.FIArea2.R6.sec9ErrSum6_bound
import Submission.Work.FIArea2.R6.area2_6e_A
import Submission.Work.FIArea2.R6.sec9_Z_bound_six

/-!
# `FIArea2/R6/A27` — the (9.10) half of area 2 at the raised lacunarity cap

`R6/area2_6e_A` proves (9.10) from `LacProp` (`K ≤ 2^10`).  Here we re-run the two-line reduction
(`sec9ErrSum6_bound`) with `R6/KCap.LacPropK (2^26 + 200)` instead, using the re-proved arithmetic
`R6/KCap.sec9ErrSum6_arithK`.  `area2_6e_A27` has exactly the same conclusion as `area2_6e_A`, so
the final assembly (`Submission/Work/FIArea2/area2_6e.lean`) only has to swap the input.

Nothing below `R6/area2_6e_A` is touched: `LacProp` and `hLMine` remain valid as they stand.
-/

set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- ***FI* (9.10) for the §9 error sum, from the raised-cap lacunarity input.** -/
theorem sec9ErrSum6_boundK (hL : Work.FIArea2.R6.LacPropK (2 ^ 26 + 200)) :
    ∀ η : ℝ, 0 < η → η < 3 / 32 →
    ∃ Cb x0 : ℝ, 0 < Cb ∧ 0 < x0 ∧
      ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
      ∀ (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
        Work.FIArea2.R6.sec9ErrSum6 Pa β
          ≤ Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
              * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
  intro η hη0 hη32
  obtain ⟨CL, hCL, KL, hKL, hLb⟩ := hL
  obtain ⟨CZ, hCZ, hZ⟩ := sec9_Z_bound_six
  obtain ⟨C, hC, hPsum⟩ := sec9Psum_le_of_Lsum_six CZ hCZ 8 hZ CL hCL KL hLb
  refine ⟨256 * 128 * 2 * C * CZ * CL, 4096, by positivity, by norm_num, ?_⟩
  intro Pa hx0 hη φ z0 β hβ
  have hN8 : 8 ≤ Pa.N := by
    have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by linarith
    have h4096 : ((4096 : ℝ)) ^ ((1 : ℝ) / 4) = 8 := by
      rw [show (4096 : ℝ) = (8 : ℝ) ^ 4 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (8 : ℝ))]
      norm_num
    have hstep1 : (8 : ℝ) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ (4096 : ℝ)) hx0
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
      rwa [h4096] at h
    have hstep2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [Pa.hη])
    have hlt : (8 : ℝ) < Pa.N := lt_of_le_of_lt (le_trans hstep1 hstep2) Pa.hNlo
    exact le_of_lt hlt
  have hη0' : 0 < Pa.η := by rw [hη]; exact hη0
  have hη32' : Pa.η < 3 / 32 := by rw [hη]; exact hη32
  have hErr := sec9ErrSum6_le_sec9Psum6 Pa φ z0 β hβ
  have hP := hPsum Pa β (fun z => Work.FIArea2.R6.IsBetaCoeff6.norm_le_tau hβ z)
  exact sec9ErrSum6_arithK Pa CZ CL C KL hCZ hCL hC hKL hN8 hη0' hη32' hErr hP

/-- **The (9.10) half of area 2 at the raised cap.**  Same conclusion as `R6/area2_6e_A`. -/
theorem area2_6e_A27 (hL : Work.FIArea2.R6.LacPropK (2 ^ 26 + 200)) :
    ∀ η : ℝ, 0 < η → η < 3 / 32 →
    ∃ Cb x0 : ℝ, 0 < Cb ∧ 0 < x0 ∧
      ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
      ∀ (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f) (φ : ℝ) (z0 : GaussianInt)
        (β : GaussianInt → ℂ),
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
        ‖((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
            - ((Work.FIArea2.R6.D0ex (Work.FITop.radN Pa) (Work.FIArea2.R6.majF Pa f hf) β : ℝ) : ℂ)‖
          ≤ Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FIArea2.R6.abs_Dstar_sub_D0ex_le_errSum
  intro η hη0 hη32
  obtain ⟨Cb, x0, hCbpos, hx0pos, hCb⟩ := sec9ErrSum6_boundK hL η hη0 hη32
  refine ⟨C * Cb, x0, by positivity, hx0pos, fun Pa hx hη f hf φ z0 β hβ => ?_⟩
  have h1 : ‖((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
        - ((Work.FIArea2.R6.D0ex (Work.FITop.radN Pa) (Work.FIArea2.R6.majF Pa f hf) β : ℝ) : ℂ)‖
      = |Work.FITop3.Dstar Pa f β
          - Work.FIArea2.R6.D0ex (Work.FITop.radN Pa) (Work.FIArea2.R6.majF Pa f hf) β| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [h1]
  calc |Work.FITop3.Dstar Pa f β
          - Work.FIArea2.R6.D0ex (Work.FITop.radN Pa) (Work.FIArea2.R6.majF Pa f hf) β|
      ≤ C * Work.FIArea2.R6.sec9ErrSum6 Pa β := hC Pa f hf φ z0 β hβ
    _ ≤ C * (Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
          * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)) :=
        mul_le_mul_of_nonneg_left (hCb Pa hx hη φ z0 β hβ) hCpos.le
    _ = C * Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
          * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by ring

end

end Work.FIArea2.R6
