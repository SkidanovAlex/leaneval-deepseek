import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.Epoint_Kfun
import Submission.Work.Asymptotics.E_deviation_sharp
import Submission.Work.Asymptotics.E_TailClosed
import Submission.Work.Asymptotics.E_seminorm
import Submission.Work.Asymptotics.SKEC.FarWindowClean
import Submission.Work.Asymptotics.cuspRegion_seminorm_disk0
import Submission.Work.Kernels.All

namespace Work.Asymptotics

/-- **The seminorm bound for the CKMRV kernel transform on the cusp-`0` tile `E = KEpsilon`.**

This is `Work.Asymptotics.SeminormK_E ℓ d` (`Submission/Work/Asymptotics/KEpsilon.lean`): for every
`k l` there are `α β γ δ ≥ 0` with
`|r|^k ‖∂_r^l (kernelTransform (Kfun ℓ d) w ·) r‖ ≤ α (Im w)^{-β} + γ ‖w‖^δ` for all `w ∈ E` and
all `r : ℝ`.  By the `S`-transport (`Work.Asymptotics.kernelTransform_Khat_eq`) this is equivalent
to the moderate growth of the `K̂`-transform on the funnel (CKMRV Proposition 4.6 at the cusp `0`).

## Route (the existing `ERegimes` form is NOT provable for `d = 24`)

The cusp model `Aexp (Gcusp ℓ 24) w t` contains the term
`e^{2πt}·(Gcusp24 1 0 w + tI·Gcusp24 1 1 w)` with a non-vanishing coefficient, and it is valid for
`t ≥ Im (S • w) + 1`; hence at `t = scale w ≈ Im (S • w) + 2` the kernel has size
`e^{2πt}·poly(scale w)`.  So the plain window `‖K‖ ≤ C (scale w)^N (1+t)^M` (i.e.
`Work.Asymptotics.EPolyWindowE_one`, and hence `ERegimes` with any `N₀ ≥ 1`) is FALSE for `d = 24`,
and the two-regime split has to be taken at the *w-dependent* threshold `T := Im (S • w) + 1`
(`T ≤ scale w` by `Work.Asymptotics.im_S_smul_add_one_le_scale`) with:

* window `‖K(w,it)‖ ≤ C (scale w)^N (1+t)^M (1 + e^{2πt})` for `1 ≤ t ≤ T`
  (`Work.Asymptotics.E_window_exp`);
* tail `‖K(w,it) - Aexp (Gcusp ℓ d) w t‖ ≤ C (scale w)^N (1+t)^M e^{-π(t-T)}` for `t ≥ T`
  (`Work.Asymptotics.E_deviation_sharp`, whose rate is measured from the pole height `Im (S•w)`).

The layer `Work.Asymptotics.E_Expr` (with `Work.Asymptotics.E_Bw` replaced by this `T`), the closed
form `Work.Asymptotics.E_TailClosed` from `B = T`, the low layer
`Work.Asymptotics.E_layerLow_seminorm`, and the agreement machinery of
`Work.Asymptotics.E_F2_agreement` then give the bound; the two-regime machinery
`Work.Asymptotics.exists_bound_iteratedDeriv_tailIntegral_two_regime` has to be adapted to a general
threshold `B ≤ A` and to the exponential window, and the resulting `1/(πr² - 2π)` poles must cancel
against the `sinSq` factor (`Work.Asymptotics.sinSq_eq`,
`Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound`) exactly as in the closed form
`Work.Asymptotics.E_TailClosed_seminorm`.  (Note that the pieces of the layer have these poles and
only their `sinSq`-weighted combination is uniformly bounded, so the model's `∫ Aexp` must be paired
with the closed form from `B = T`, as in `Work.Asymptotics.E_Expr`.) -/
theorem SeminormK_E_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    Work.Asymptotics.SeminormK_E ℓ d := by
  have hflat : Work.Asymptotics.EFlat ℓ d := (Work.Asymptotics.Epoint_Kfun ℓ d hd).1
  obtain ⟨Cw, Nw, Mw, hCw, hNw, hMw, hwin_far⟩ :=
    Work.Asymptotics.EpolyWindowE_clean_far ℓ d hd
  obtain ⟨Cd, Nd, Md, hCd, hNd, hMd, hdev⟩ :=
    Work.Asymptotics.E_deviation_sharp ℓ d hd
  set C : ℝ := max Cw (Cd * Real.exp (-(Real.pi)) ) with hCdef
  set N : ℝ := max Nw Nd with hNdef
  set M : ℝ := max Mw Md with hMdef
  have hCpos : 0 < C := by rw [hCdef]; exact lt_max_of_lt_left hCw
  have hN0 : 0 ≤ N := by rw [hNdef]; exact le_max_of_le_left hNw
  have hM0 : 0 ≤ M := by rw [hMdef]; exact le_max_of_le_left hMw
  have hwin : ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon → 1 ≤ t →
      t ≤ Work.Asymptotics.E_T w →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
    intro w t hw ht1 htT
    have hb := hwin_far w t hw (lt_of_lt_of_le zero_lt_one ht1)
      (le_trans htT (Work.Asymptotics.E_T_le_scale hw))
    refine le_trans hb ?_
    have e1 : Cw ≤ C := by rw [hCdef]; exact le_max_left _ _
    have e2 : (Work.Kernels.scale w) ^ Nw ≤ (Work.Kernels.scale w) ^ N :=
      Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w)
        (by rw [hNdef]; exact le_max_left _ _)
    have e3 : (1 + t) ^ Mw ≤ (1 + t) ^ M :=
      Real.rpow_le_rpow_of_exponent_le (by linarith)
        (by rw [hMdef]; exact le_max_left _ _)
    calc Cw * (Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw
        = Cw * ((Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw) := by ring
      _ ≤ C * ((Work.Kernels.scale w) ^ N * (1 + t) ^ M) :=
          mul_le_mul e1 (mul_le_mul e2 e3 (Real.rpow_nonneg (by linarith) Mw)
            (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N))
            (mul_nonneg (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nw)
              (Real.rpow_nonneg (by linarith) Mw)) hCpos.le
      _ = C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by ring
  have htail : ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
      Work.Asymptotics.E_T w ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
            * Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w))) := by
    intro w t hw htT
    have hT1 : (1 : ℝ) ≤ Work.Asymptotics.E_T w := Work.Asymptotics.one_le_E_T hw
    have him : (ModularGroup.S • w).im + 1 ≤ t := by
      rw [show (ModularGroup.S • w).im + 1 = Work.Asymptotics.E_T w from rfl]; exact htT
    have hb := hdev w t hw him
    have hsplit : t - (ModularGroup.S • w).im = (t - Work.Asymptotics.E_T w) + 1 := by
      rw [show Work.Asymptotics.E_T w = (ModularGroup.S • w).im + 1 from rfl]; ring
    rw [hsplit] at hb
    rw [show -(Real.pi * ((t - Work.Asymptotics.E_T w) + 1))
        = -(Real.pi * (t - Work.Asymptotics.E_T w)) + -Real.pi from by ring,
      Real.exp_add] at hb
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
        ≤ Cd * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
            * (Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w))) * Real.exp (-Real.pi)) := hb
      _ = Cd * Real.exp (-(Real.pi)) * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
            * Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w))) := by ring
      _ ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
            * Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w))) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          have e1 : Cd * Real.exp (-(Real.pi)) ≤ C := by
            rw [hCdef]; exact le_max_right _ _
          have e2 : (Work.Kernels.scale w) ^ Nd ≤ (Work.Kernels.scale w) ^ N :=
            Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w)
              (by rw [hNdef]; exact le_max_right _ _)
          have e3 : (1 + t) ^ Md ≤ (1 + t) ^ M :=
            Real.rpow_le_rpow_of_exponent_le (by linarith)
              (by rw [hMdef]; exact le_max_right _ _)
          calc Cd * Real.exp (-(Real.pi)) * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
              = (Cd * Real.exp (-(Real.pi)))
                  * ((Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md) := by ring
            _ ≤ C * ((Work.Kernels.scale w) ^ N * (1 + t) ^ M) :=
                mul_le_mul e1 (mul_le_mul e2 e3 (Real.rpow_nonneg (by linarith) Md)
                  (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N))
                  (mul_nonneg (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nd)
                    (Real.rpow_nonneg (by linarith) Md)) hCpos.le
            _ = C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by ring
  exact Work.Asymptotics.SeminormK_E_of_assembled ℓ d hd hflat C N M hCpos hN0 hM0 hwin htail

end Work.Asymptotics
