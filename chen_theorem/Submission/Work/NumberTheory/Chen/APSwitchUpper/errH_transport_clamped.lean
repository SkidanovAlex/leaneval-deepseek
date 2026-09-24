/-
# The clamped `errH` transport (`∫` from `max (s-1) 2`)

The sharp error profile `errH` of the linear sieve satisfies the *tail transport*

  `∫_{s-1}^∞ errH ≤ (97/100)·s·errH s`   (`s ≥ 2`, `errH_transport`),

which is what makes the accumulated sieve error *contract* by `ρ = 97/100` per step.  For the
steps whose children range over `σ_q ∈ [2, ∞)` — i.e. whenever the level is below the cube of the
sift limit (`D ≤ Y³`), where the cube condition `q³ ≤ D` cuts the prime range at `D^{1/3}` and the
`σ`-range therefore *starts at* `2` rather than at `s-1` — the needed form is the clamped one,
with the bottom of the integral pinned at `2`:

  `∫_{max (s-1) 2}^∞ errH ≤ (97/100)·s·errH s`   (`s ≥ 1`).

Equivalently, the profile `ψ := errH / e^{-2}` satisfies
`(1/s)·∫_{max (s-1) 2}^∞ ψ ≤ (97/100)·ψ s`, which is exactly the "error coefficient pinned to the
state's own scale" transport of the two-state (excess/deficit) induction, see
`BTermCount/mpSum2_riUp_crux_NOTES2.md` §13.9.

`integral_Ioi_two_errH_le` is the companion estimate at the left end; both were previously
available only as `private` lemmas of `APSwitchUpper/profC_le_decay.lean`, and this file exports
them (with the same proofs).

Imports: `ErrProfile` (`errH`), `errH_transport` (the tail transport, `tail3_le`, the integral
machinery).
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile
import Submission.Work.NumberTheory.Chen.APSwitchUpper.errH_transport

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

open MeasureTheory Set

/-- `∫_2^∞ errH ≤ (97/100)·errH 2`.  This is the companion of the tail transport inequality at
the bottom of the range; it controls the clamped range `s ≤ 2`. -/
theorem integral_Ioi_two_errH_le :
    (∫ u in Set.Ioi (2:ℝ), errH u) ≤ (97/100) * Real.exp (-2) := by
  have hInt2 : IntegrableOn errH (Set.Ioi (2:ℝ)) := integrableOn_errH_Ioi (by norm_num)
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (f := errH) (a := (2:ℝ)) (b := (3:ℝ))
    hInt2 (by norm_num)
  have h23 : (∫ u in (2:ℝ)..3, errH u) = Real.exp (-2) - Real.exp (-3) := by
    have hcong : (∫ u in (2:ℝ)..3, errH u) = ∫ u in (2:ℝ)..3, Real.exp (-u) := by
      refine intervalIntegral.integral_congr ?_
      intro u hu
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)] at hu
      exact errH_eq_exp_neg hu.1 hu.2
    rw [hcong]
    have h := intervalIntegral.integral_Ioi_sub_Ioi (f := fun u : ℝ => Real.exp (-u))
      (a := (2:ℝ)) (b := (3:ℝ)) (integrableOn_exp_neg_Ioi (2:ℝ)) (by norm_num)
    rw [integral_exp_neg_Ioi, integral_exp_neg_Ioi] at h
    linarith
  have hI3 : (∫ u in Set.Ioi (3:ℝ), errH u) ≤ Real.exp (-3) - (3/50) * Real.exp (-2) := by
    have hcong : (∫ u in Set.Ioi (3:ℝ), errH u)
        = ∫ u in Set.Ioi (3:ℝ), 3 * Real.exp (-u) / u :=
      setIntegral_congr_fun measurableSet_Ioi (fun u hu => errH_of_three_lt hu)
    rw [hcong]
    exact tail3_le
  have hkey : (Real.exp (-2) - Real.exp (-3)) + (Real.exp (-3) - (3/50) * Real.exp (-2))
      = (47/50) * Real.exp (-2) := by ring
  have hcut : (47/50 : ℝ) * Real.exp (-2) ≤ (97/100) * Real.exp (-2) :=
    mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  linarith [hsplit, h23, hI3, hkey, hcut]

/-- **The clamped tail transport.**  `∫_{max (s-1) 2}^∞ errH ≤ (97/100)·s·errH s` for `s ≥ 1`.

For `s ≤ 2` the tail is dominated by `∫_2^∞ errH ≤ (97/100) errH s ≤ (97/100) s errH s`; for
`s ≥ 2` it is dominated by `∫_{s-1}^∞ errH = ∫_s^∞ errH (t-1) dt`, which `errH_transport`
controls by `(97/100) s errH s`. -/
theorem errH_transport_clamped (s : ℝ) (hs1 : 1 ≤ s) :
    (∫ u in Set.Ioi (max (s - 1) 2), errH u) ≤ (97/100) * s * errH s := by
  by_cases hs2 : s ≤ 2
  · have hmax : max (s - 1) 2 = (2:ℝ) := max_eq_right (by linarith)
    rw [hmax, errH_of_le_two hs2]
    have h := integral_Ioi_two_errH_le
    have he : (0:ℝ) < Real.exp (-2) := Real.exp_pos _
    nlinarith [h, he, hs1]
  · have hs2' : 2 ≤ s := le_of_lt (not_le.mp hs2)
    have hmono : (∫ u in Set.Ioi (max (s - 1) 2), errH u) ≤ ∫ u in Set.Ioi (s - 1), errH u := by
      refine setIntegral_mono_set (integrableOn_errH_Ioi (by linarith))
        (Filter.Eventually.of_forall errH_nonneg) ?_
      exact Filter.Eventually.of_forall (fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢; exact lt_of_le_of_lt (le_max_left _ _) hx)
    refine le_trans hmono ?_
    rw [← setIntegral_Ioi_comp_sub errH s 1]
    exact errH_transport.1 s hs2'

/-- The form in which the clamped transport is consumed: with the error coefficient pinned to
the state's own scale, `(1/s)·∫_2^∞ errH ≤ (97/100)·errH s` on `1 ≤ s ≤ 3`. -/
theorem inv_mul_integral_Ioi_two_errH_le (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    (1/s) * (∫ u in Set.Ioi (2:ℝ), errH u) ≤ (97/100) * errH s := by
  have hmax : max (s - 1) 2 = (2:ℝ) := max_eq_right (by linarith)
  have h := errH_transport_clamped s hs1
  rw [hmax] at h
  have hs0 : (0:ℝ) < s := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
  linarith [h]

end

end Work.NumberTheory.Chen.APSwitchUpper
