/-
# `Submission.Work.FIFinal.Clean6` — area 6 in a *clash-free* environment

`Work.FIArea6V.area6_6e` (the round-6 area-6 contract `Work.FITop4.Area6_6e`) is proved in
`Submission/Work/FIArea6V/Contract.lean`.  That module's import closure contains
`Submission.Work.FIArea6Hecke.R.LHBHead`, which imports
`Submission.Work.FIArea7.card_pairs_gBox_absDelta_lt`; the *area-7* lane used by
`Work.FIArea4.area4_6c` and `Work.FIArea7.area7_6b` is the clash-free copy
`Submission.Work.FIArea7CF`, which **re-declares** the same names (`Work.FIArea7.gRadius`, …).
Lean refuses to load two modules that declare the same name, so

    `Work.FIArea6V.area6_6e`  and  `Work.FIArea7.area7_6b`

**cannot be imported into one file** — and every composition of the seven areas
(`Work.FIRed6e.prop41_of_areas6f` and its siblings) needs both.  This module removes the clash by
re-proving the area-6 contract along a lane whose import closure the directory
`Submission/Work/FIFinal/CL/` holds: a verbatim copy of the `FIArea6Hecke`/`FIArea6V` modules on
the `LHBHead`-ward path, with each `FIArea6Hecke` import re-pointed to its copy and — in
`CL/FIArea6Hecke/R/LHBHead.lean` — the single import of the *non*-clash-free
`Work.FIArea7.card_pairs_gBox_absDelta_lt` replaced by the clash-free
`Work.FIArea7CF.card_pairs_gBox_absDelta_lt`, whose API is identical (`gRadius`,
`mem_gBox_iff_gRadius`, `card_filter_gRadius_eq_le`, …).

Consequently **this module and the `FIArea7CF` lane are compatible**, and the seven areas can be
composed.  The mathematics below is verbatim `Submission/Work/FIArea6V/Contract.lean`:
`tauVac_tauMax` ⇒ `isBetaCoeff6_tauMax_of_isCleanCoeff6` ⇒ `area6_6e_of_V` ⇒ the clean lane
`S16TsumHeart_of_invBound → … → area6_glueV`, at the Hecke inverse bound (16.23)/(16.24) of the
lane copy `Work.FIArea6V.heckeLcontInvBound_all_clean` (declared in
`Submission/Work/FIFinal/CL/FIArea6V/HeckeClean.lean`).
-/
import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FIArea6V.tau_le_tauMax_of_noSmallPrimes
import Submission.Work.FIArea6V.area6_glueV
import Submission.Work.FIArea6V.section16_Ucut_twoV
import Submission.Work.FIArea6V.Area5TwoV_of_S16CoreTwoV
import Submission.Work.FIArea6V.S16CoreTwoV_of_radialCoreTwoV
import Submission.Work.FIArea6V.S16RadialCoreTwoV_of_noClassTwoV
import Submission.Work.FIArea6V.S16RadialNoClassTwoV_of_cleanCoreA
import Submission.Work.FIArea6V.S16CleanCoreTwoA_of_heart
import Submission.Work.FIArea6.S16TsumHeart_of_invBound
import Submission.Work.FIFinal.CL.FIArea6V.HeckeClean

set_option autoImplicit false

namespace Work.FIFinal

open Finset
open scoped BigOperators

noncomputable section

/-- **The raised datum is τ-vacuous** (auxiliary API, verbatim from the area-6 lane). -/
theorem tauVac_tauMax : ∀ η : ℝ, 0 < η → ∃ x0 : ℝ,
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η → ∀ (φ : ℝ),
      Work.FIArea6V.TauVac (Work.FIArea6V.tauMax Pa) φ := by
  intro η hη
  obtain ⟨x0, hx0⟩ := Work.FIArea6V.tau_le_tauMax_of_noSmallPrimes η hη
  exact ⟨x0, fun Pa hx hη' φ z hz hz' => hx0 Pa hx hη' φ z hz hz'⟩

/-- **A clean coefficient is a round-6 coefficient at the raised datum `tauMax Pa`** (auxiliary
API, verbatim from the area-6 lane). -/
theorem isBetaCoeff6_tauMax_of_isCleanCoeff6 {Pa : Work.FITop.Params} {φ : ℝ}
    {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsCleanCoeff6 Pa φ z0 β) (hvac : Work.FIArea6V.TauVac (Work.FIArea6V.tauMax Pa) φ)
    (hfar : ∀ z, Work.FITop4.InPolarBox (Work.FIArea6V.tauMax Pa) φ z →
      Work.FITop4.IsAxisFree (Work.FIArea6V.tauMax Pa) z) :
    Work.FITop4.IsBetaCoeff6 (Work.FIArea6V.tauMax Pa) φ z0 β := by
  obtain ⟨q, p, hc1, hc2, hq0, hq1, hqsupp, hqd, hp0, hp1, hpsupp, hpd, hval⟩ := hβ
  refine ⟨q, p, hc1, hc2, hq0, hq1, hqsupp, hqd, hp0, hp1, hpsupp, hpd, ?_⟩
  intro z
  rw [hval z]
  by_cases hz : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
      Work.FITop4.SameClass8 z z0
  · have hτ : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ (Work.FIArea6V.tauMax Pa).τ :=
      hvac z hz.1 hz.2.1
    have hax : Work.FITop4.IsAxisFree (Work.FIArea6V.tauMax Pa) z := hfar z hz.1
    have hcond : Work.FITop4.InPolarBox (Work.FIArea6V.tauMax Pa) φ z
        ∧ Work.FITop4.NoSmallPrimes (Work.FIArea6V.tauMax Pa) z
        ∧ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ (Work.FIArea6V.tauMax Pa).τ
        ∧ Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree (Work.FIArea6V.tauMax Pa) z :=
      ⟨hz.1, hz.2.1, hτ, hz.2.2, hax⟩
    simp only [if_pos hz, if_pos hcond, Work.FIArea6V.tauMax_C]
  · have hcond : ¬ (Work.FITop4.InPolarBox (Work.FIArea6V.tauMax Pa) φ z
        ∧ Work.FITop4.NoSmallPrimes (Work.FIArea6V.tauMax Pa) z
        ∧ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ (Work.FIArea6V.tauMax Pa).τ
        ∧ Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree (Work.FIArea6V.tauMax Pa) z) :=
      fun hh => hz ⟨hh.1, hh.2.1, hh.2.2.2.1⟩
    simp only [if_neg hz, if_neg hcond]

/-- **`Area6_6V` implies the round-6 contract `Work.FITop4.Area6_6e`** (verbatim from the area-6
lane): apply the clean-lane contract at the raised datum, where the coefficient is round-6 and the
datum is τ-vacuous. -/
theorem area6_6e_of_V (h : Work.FIArea6V.Area6_6V) : Work.FITop4.Area6_6e := by
  intro η hη0 hη32
  obtain ⟨cν, x0, hcν, hH⟩ := h η hη0 hη32
  obtain ⟨x0t, hx0t⟩ := tauVac_tauMax η hη0
  refine ⟨cν, max x0 x0t, hcν, ?_⟩
  intro Pa hx hPaη X φ z0 β hβ hfar hX hXlog hXcube
  have hxt : x0t ≤ (Pa.x : ℝ) := le_trans (le_max_right x0 x0t) hx
  have hx0' : x0 ≤ (Pa.x : ℝ) := le_trans (le_max_left x0 x0t) hx
  have hvac : Work.FIArea6V.TauVac (Work.FIArea6V.tauMax Pa) φ := hx0t Pa hxt hPaη φ
  have hfar' : ∀ z, Work.FITop4.InPolarBox (Work.FIArea6V.tauMax Pa) φ z →
      Work.FITop4.IsAxisFree (Work.FIArea6V.tauMax Pa) z := fun z hz => hfar z hz
  have hβ' : Work.FITop4.IsBetaCoeff6 (Work.FIArea6V.tauMax Pa) φ z0 β :=
    isBetaCoeff6_tauMax_of_isCleanCoeff6 hβ hvac hfar'
  have hmain := hH (Work.FIArea6V.tauMax Pa) hx0' hPaη X φ z0 β hvac hβ' hfar' hX hXlog hXcube
  exact hmain

/-- **The clean area-6 lane, assembled** (verbatim from the area-6 lane), from the Hecke inverse
bound (16.23)/(16.24) declared in the lane copy of `HeckeClean`. -/
theorem area6_6e_of_invBound
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → Work.FITop4.Bridge.HeckeLcontInvBoundAll ε) :
    Work.FITop4.Area6_6e :=
  area6_6e_of_V (Work.FIArea6V.area6_glueV (Work.FIArea6V.section16_Ucut_twoV
    (Work.FIArea6V.Area5TwoV_of_S16CoreTwoV
      (Work.FIArea6V.S16CoreTwoV_of_radialCoreTwoV
        (Work.FIArea6V.S16RadialCoreTwoV_of_noClassTwoV
          (Work.FIArea6V.S16RadialNoClassTwoV_of_cleanCoreA
            (Work.FIArea6V.S16CleanCoreTwoA_of_heart
              (Work.FIArea6.S16TsumHeart_of_invBound h))))))))

/-- **The round-6 area-6 contract, in a clash-free environment**: the deliverable of this module.
Its import closure avoids `Submission.Work.FIArea7.card_pairs_gBox_absDelta_lt`, so it coexists
with the `FIArea7CF` area-7 lane. -/
theorem area6_6e : Work.FITop4.Area6_6e :=
  area6_6e_of_invBound Work.FIArea6V.heckeLcontInvBound_all_clean

end

end Work.FIFinal
