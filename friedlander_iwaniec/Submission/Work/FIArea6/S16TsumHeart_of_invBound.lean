/-
# `Submission.Work.FIArea6.S16TsumHeart_of_invBound` — the §16 heart from the Hecke inverse bound

`Work.FIArea6.S16TsumHeart` (*FI* (16.38) for the Möbius-twisted Hecke sum `Tsum`) is assembled
here from the three continuation/branch pieces that the `FIArea6Road` agent proved sorry-free in
`Submission/Work/FIArea6Road/`:

* `Work.FIArea6Road.HeartZcHypOfInvBound` — the `Z`-continuation in the non-vacuous regime
  (*FI* (16.31)–(16.35)), with a constant uniform in the datum;
* `Work.FIArea6Road.HeartZcTrivial` — the same in the regime where `ψ_m` is trivial on the primary
  units mod `4d` (then `L(s,ψ) = ζ(s)L(s,χ₄)G_d(s)` and the zero-free regions of `ζ`, `L(·,χ₄)`
  apply);
* `Work.FIArea6Road.HeartZcCore` — the contour shift itself (*FI* (16.36)–(16.38)), producing the
  fresh exponent constant `c` and the prefactor `C·C_z`.

The assembly (case split on the existence of an entire completion, maxima of the thresholds and of
the prefactors, and the monotonicity lemmas `heart_hinv_mono`, `heart_S16RH_mono`,
`heart_threshold`, `heart_mellin_rep_hyp` of `Submission/Work/FIArea6Road/HeartZcDefs`) is
transcribed from `Work.FIArea6Road.TsumHeartOfInvBound`, whose three *temporary local stub*
`sorry`s are exactly the three theorems above; this module replaces them by imports.
-/
import Mathlib
import Submission.Work.FIArea6.S16TsumHeartDefs
import Submission.Work.FIArea6.S16.HeartIface
import Submission.Work.FIArea6Road.HeartZcDefs
import Submission.Work.FIArea6Road.HeartZcHypOfInvBound
import Submission.Work.FIArea6Road.HeartZcTrivial
import Submission.Work.FIArea6Road.HeartZcCore

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- ***FI* §16, the analytic heart (16.29)–(16.38)**, from the Hecke inverse bound (16.23). -/
theorem S16TsumHeart_of_invBound
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → Work.FITop4.Bridge.HeckeLcontInvBoundAll ε) :
    Work.FIArea6.S16TsumHeart := by
  rw [Work.FIArea6.S16.s16TsumHeart_iff]
  intro ε hε hε4
  obtain ⟨c_h_h, C_h, hc_h_h, hC_h, hgen⟩ := h ε hε hε4
  obtain ⟨K_z2, c₀t, hK2, hc₀t, H2⟩ := Work.FIArea6Road.HeartZcTrivial ε hε hε4
  set c_h : ℝ := min (min (c_h_h / 2) 1) c₀t with hc_h_def
  have hc_h_pos : 0 < c_h := lt_min (lt_min (by linarith) one_pos) hc₀t
  have hc_h_le_h : c_h ≤ c_h_h / 2 :=
    le_trans (min_le_left (min (c_h_h / 2) 1) c₀t) (min_le_left (c_h_h / 2) 1)
  have hc_h_le_c0 : c_h ≤ c₀t := min_le_right (min (c_h_h / 2) 1) c₀t
  obtain ⟨K_z1, hK1, H1⟩ := Work.FIArea6Road.HeartZcHypOfInvBound ε c_h C_h hε hc_h_pos hC_h
  obtain ⟨c₀, C₀, x₀, hc₀, hC₀, hx₀, Hcore⟩ :=
    Work.FIArea6Road.HeartZcCore ε hε hε4 c_h hc_h_pos
  obtain ⟨x_thr, hx_thr, Hthr⟩ := Work.FIArea6Road.heart_threshold
  set K_z : ℝ := max K_z1 K_z2 with hK_z_def
  have hK_z_pos : 0 < K_z := lt_of_lt_of_le hK1 (le_max_left _ _)
  refine ⟨c₀, C₀ * K_z, max x₀ x_thr, hc₀, mul_pos hC₀ hK_z_pos,
    lt_of_lt_of_le hx₀ (le_max_left _ _), ?_⟩
  intro Pa hPa ν d m chi p hh
  obtain ⟨hν0, hν1, hd1, hdN, hm, hchi, hpC, hp0, hp1, hpsupp, hpd⟩ := hh
  have hPa_core : x₀ ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hPa
  have hPa_thr : x_thr ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hPa
  obtain ⟨hlogPz, hθ1, hlogN1, hσ2⟩ := Hthr Pa hPa_thr
  have hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := fun z => hchi.1.2.2.1 z
  have hh' : Work.FIArea6.S16.HeartHyp Pa ν d m chi p ε :=
    ⟨hν0, hν1, hd1, hdN, hm, hchi, hpC, hp0, hp1, hpsupp, hpd⟩
  have hMellin := Work.FIArea6Road.heart_mellin_rep_hyp Pa chi m p d hθ1 hh'
  have hfinal : Work.FIArea6.S16.HeartBound Pa c₀ (C₀ * K_z) d ε m chi p := by
    by_cases hnt : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
        Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ Work.FIArea5.S16Hecke.psi chi m z ≠ 1
    · obtain ⟨Lam, hLam, hag⟩ :=
        Work.FIArea6Hecke.R.heckeCompletionImprimitive d chi m hd1 hchi hnt
      have hinv := Work.FIArea6Road.heart_hinv_mono hd1 (by linarith [hc_h_le_h] : c_h ≤ c_h_h)
        (hgen d chi m Lam hd1 hchi hLam hag)
      obtain ⟨C_z, Zc, hCz_le, hZc⟩ := H1 Pa chi m d Lam hd1 hchi hlogPz hLam hag hinv
      have hb : Work.FIArea6.S16.HeartBound Pa c₀ (C₀ * C_z) d ε m chi p :=
        Hcore Pa hPa_core ν d m chi p hh' hchibd hMellin C_z Zc hZc
      refine le_trans hb (Work.FIArea6Road.heart_S16RH_mono Pa c₀ d ε ?_)
      exact mul_le_mul_of_nonneg_left (le_trans hCz_le (le_max_left _ _)) hC₀.le
    · push_neg at hnt
      obtain ⟨C_z, Zc, hCz_le, hZc⟩ := H2 Pa chi m d c_h hc_h_pos hc_h_le_c0 hd1 hchi hlogPz hnt
      have hb : Work.FIArea6.S16.HeartBound Pa c₀ (C₀ * C_z) d ε m chi p :=
        Hcore Pa hPa_core ν d m chi p hh' hchibd hMellin C_z Zc hZc
      refine le_trans hb (Work.FIArea6Road.heart_S16RH_mono Pa c₀ d ε ?_)
      exact mul_le_mul_of_nonneg_left (le_trans hCz_le (le_max_right _ _)) hC₀.le
  exact hfinal

end

end Work.FIArea6
