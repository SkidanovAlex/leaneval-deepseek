import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.RepNorm
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.Lavaurs.Windows
import Submission.Work.PARIMPL2.Lavaurs.transit_exit_direct
import Submission.Work.PARIMPL2.Lavaurs.win_model
import Submission.Work.PARIMPL2.Lavaurs.wout_model
import Submission.Work.PARIMPL2.Lavaurs.exists_Rch_prime
import Submission.Work.PARIMPL2.Lavaurs.chartZeta_uniform_close
import Submission.Work.PARIMPL2.Lavaurs.norm_log_sub_log_le
import Submission.Work.PARIMPL2.Lavaurs.exists_log_mul_le
import Submission.Work.PARIMPL2.Lavaurs.gtc_uniform_close
import Submission.Work.PARIMPL2.Lavaurs.injOn_modulus
import Submission.Work.PARIMPL2.Lavaurs.L0_symmetry
import Submission.Work.PARIMPL2.LavaursA.Tools
import Submission.Work.PARIMPL2.LavaursA.pa_bounded
import Submission.Work.PARIMPL2.LavaursA.w0_increment
import Submission.Work.PARIMPL2.LavaursA.w0_im_bound
import Submission.Work.PARIMPL2.LavaursA.crossing_nat
import Submission.Work.PARIMPL2.LavaursA.log_le_lin
import Submission.Work.PARIMPL2.LavaursA.bound_le_add_mul_log_explicit
import Submission.Work.PARIMPL2.LavaursA.exit_region
import Submission.Work.PARIMPL2.LavaursA.exit_zeta_lo
import Submission.Work.PARIMPL2.LavaursA.wout_level
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.PARIMPL.Transit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 100000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

open Work.PARIMPL (ParNormal entryPt Ft gtc chartZeta approxU approxUin)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **The `φa`-shift, iterated**: `φa ((Ft c₀)^[j] y) = φa y + j` for `y` in the petal. -/
theorem phi_shift_iter (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁)
    (A : Work.FlowerGlue2.AttrCompare P fl.Pa fl.φa) (j : ℕ) {y : ℂ} (hy : y ∈ fl.Pa) :
    fl.φa ((Ft c₀)^[j] y) = fl.φa y + (j : ℂ) := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hk : (Ft c₀)^[k] y ∈ fl.Pa := (A.mapsTo_Pa.iterate k) hy
    rw [A.φa_shift _ hk, ih]
    push_cast
    ring

/-- The real part of `κ log w` is bounded by `‖κ‖ (log ‖w‖ + π)` for `‖w‖ ≥ 1`: the principal
branch of `Complex.log` differs from the logarithm of the modulus by at most `π` in the
imaginary part. -/
theorem kappalog_re_bound (κ w : ℂ) (hw : 1 ≤ ‖w‖) :
    (κ * Complex.log w).re ≤ ‖κ‖ * (Real.log ‖w‖ + Real.pi) := by
  have h1 : (κ * Complex.log w).re ≤ ‖κ * Complex.log w‖ := Complex.re_le_norm _
  have h2 : ‖κ * Complex.log w‖ = ‖κ‖ * ‖Complex.log w‖ := norm_mul _ _
  have h3 : ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im] at h3
  have h4 : |w.arg| ≤ Real.pi := Complex.abs_arg_le_pi w
  have h5 : |Real.log ‖w‖| ≤ Real.log ‖w‖ := le_of_eq (abs_of_nonneg (Real.log_nonneg hw))
  have h6 : ‖Complex.log w‖ ≤ Real.log ‖w‖ + Real.pi := by linarith
  calc (κ * Complex.log w).re ≤ ‖κ‖ * ‖Complex.log w‖ := by rw [← h2]; exact h1
    _ ≤ ‖κ‖ * (Real.log ‖w‖ + Real.pi) := mul_le_mul_of_nonneg_left h6 (norm_nonneg κ)

/-- **The `BT` bound.**  With `Xlo` above `A.N` and above `1`, `J₀` a depth threshold of the
deepening hypothesis and `saD` its phase constant, the real part of the `c₀`-chart coordinate at
time `J₀` is bounded on the whole box by a single constant `BT` independent of the box point. -/
theorem bt_bound (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁)
    (A : Work.FlowerGlue2.AttrCompare P fl.Pa fl.φa)
    {X₁ W H : ℝ} {saD : ℂ} {Xlo : ℝ} {J₀ : ℕ}
    (hXloN : A.N < Xlo) (hXlo1 : 1 ≤ Xlo)
    (hJ : ∀ y ∈ fl.Pa, X₁ ≤ (fl.φa y).re → (fl.φa y).re ≤ X₁ + W → |(fl.φa y).im| ≤ H →
      ∀ j ≥ J₀, Xlo < (Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).re ∧
        |(Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).im| ≤
          H + |saD.im| + 2 * ‖P.κ c₀‖ * Real.log (X₁ + W + j + 2) + 4) :
    ∃ BT : ℝ, ∀ y ∈ fl.Pa, X₁ ≤ (fl.φa y).re → (fl.φa y).re ≤ X₁ + W → |(fl.φa y).im| ≤ H →
      (Work.PARIMPL2.w0 P ((Ft c₀)^[J₀] y)).re ≤ BT := by
  set Bim : ℝ := H + |saD.im| + 2 * ‖P.κ c₀‖ * Real.log (X₁ + W + (J₀ : ℝ) + 2) + 4 with hBim
  obtain ⟨BT, hBT⟩ :=
    Work.PARIMPL2.LavaursA.exists_bound_le_add_mul_log (c := ‖P.κ c₀‖)
      (D := X₁ + W + (J₀ : ℝ) - A.sa.re + A.K / Xlo + ‖P.κ c₀‖ * Real.pi + Bim)
      (norm_nonneg _)
  refine ⟨BT, fun y hyPa h1 h2 h3 => ?_⟩
  have hJz := hJ y hyPa h1 h2 h3 J₀ le_rfl
  obtain ⟨hdeepre, hdeepim⟩ := hJz
  have hzPa : (Ft c₀)^[J₀] y ∈ fl.Pa := (A.mapsTo_Pa.iterate J₀) hyPa
  have hz1 : (Ft c₀)^[J₀] y ≠ d.z₁ := by
    intro h
    have h' : Xlo < (Work.PARIMPL2.w0 P ((Ft c₀)^[J₀] y)).re := hdeepre
    rw [h] at h'
    simp only [Work.PARIMPL2.w0, sub_self, div_zero, Complex.zero_re] at h'
    linarith [A.N_pos, hXloN]
  have hAN : A.N < (Work.FlowerGlue2.w0 P ((Ft c₀)^[J₀] y)).re := by
    simpa only [Work.FlowerGlue2.w0, Work.PARIMPL2.w0] using lt_trans hXloN hdeepre
  have hasympF := A.asymp ((Ft c₀)^[J₀] y) hzPa hz1 hAN
  set w : ℂ := Work.PARIMPL2.w0 P ((Ft c₀)^[J₀] y) with hw
  have hasymp : ‖fl.φa ((Ft c₀)^[J₀] y) - (Work.FatouCoord.approxCoord (P.κ c₀) w + A.sa)‖
      ≤ A.K / w.re := by
    rw [hw]
    simpa only [Work.FlowerGlue2.w0, Work.PARIMPL2.w0] using hasympF
  have hrew : fl.φa ((Ft c₀)^[J₀] y) = fl.φa y + (J₀ : ℂ) := phi_shift_iter P fl A J₀ hyPa
  have hwpos : 0 < w.re := lt_of_lt_of_le (lt_trans A.N_pos hXloN) hdeepre.le
  have hBimnn : 0 ≤ Bim := by linarith [abs_nonneg w.im, hdeepim]
  have hre : w.re - (P.κ c₀ * Complex.log w).re + A.sa.re ≤
      (fl.φa y).re + (J₀ : ℝ) + A.K / w.re := by
    have hpp : (Work.FatouCoord.approxCoord (P.κ c₀) w + A.sa).re
        = w.re - (P.κ c₀ * Complex.log w).re + A.sa.re := by
      simp only [Work.FatouCoord.approxCoord, Complex.sub_re, Complex.add_re]
    have h3' : (fl.φa ((Ft c₀)^[J₀] y)).re = (fl.φa y).re + (J₀ : ℝ) := by
      rw [hrew]; simp
    have h1' : (Work.FatouCoord.approxCoord (P.κ c₀) w + A.sa).re -
        (fl.φa ((Ft c₀)^[J₀] y)).re
        ≤ ‖fl.φa ((Ft c₀)^[J₀] y) - (Work.FatouCoord.approxCoord (P.κ c₀) w + A.sa)‖ := by
      have h := Complex.re_le_norm (Work.FatouCoord.approxCoord (P.κ c₀) w + A.sa -
        fl.φa ((Ft c₀)^[J₀] y))
      rwa [Complex.sub_re, norm_sub_rev] at h
    rw [hpp, h3'] at h1'
    linarith [hasymp]
  have hwn1 : 1 ≤ ‖w‖ := by
    have h := Complex.re_le_norm w
    linarith
  have hlogw : (P.κ c₀ * Complex.log w).re ≤ ‖P.κ c₀‖ * (Real.log ‖w‖ + Real.pi) :=
    kappalog_re_bound _ _ hwn1
  have hwnorm_le : ‖w‖ ≤ w.re + Bim := by
    have h1' : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    have h2' : |w.re| = w.re := abs_of_pos hwpos
    rw [h2'] at h1'
    linarith [hdeepim]
  have hwpos' : 0 < ‖w‖ := lt_of_lt_of_le one_pos hwn1
  have htpos : 0 < w.re + Bim := by linarith
  have hlogt : Real.log ‖w‖ ≤ Real.log (w.re + Bim) := Real.log_le_log hwpos' hwnorm_le
  have hK : A.K / w.re ≤ A.K / Xlo :=
    div_le_div_of_nonneg_left A.K_nonneg (lt_trans A.N_pos hXloN) hdeepre.le
  have hmain : w.re ≤ (X₁ + W) + (J₀ : ℝ) + A.K / Xlo - A.sa.re +
      ‖P.κ c₀‖ * (Real.log (w.re + Bim) + Real.pi) := by
    have hmul := mul_le_mul_of_nonneg_left hlogt (norm_nonneg (P.κ c₀))
    linarith [hre, hK, hlogw, hmul, h2]
  have hstep : w.re + Bim ≤
      (X₁ + W + (J₀ : ℝ) - A.sa.re + A.K / Xlo + ‖P.κ c₀‖ * Real.pi + Bim) +
        ‖P.κ c₀‖ * Real.log (w.re + Bim) := by linarith
  have hfin : w.re ≤ BT := by
    have h := hBT (w.re + Bim) htpos hstep
    linarith
  simpa only [← hw] using hfin

/-- **`A + B log (a + b R) ≤ R` eventually.** -/
theorem affine_log_le_self (A B a b : ℝ) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → A + B * Real.log (a + b * R) ≤ R := by
  obtain ⟨R₁, hR₁pos, hR₁⟩ :=
    Work.PARIMPL2.LavaursA.log_le_lin B a b (1 / 2) hB hb (by norm_num)
  refine ⟨max R₁ (2 * |A| + 1), lt_of_lt_of_le hR₁pos (le_max_left _ _), fun R hR => ?_⟩
  have h1 := hR₁ R (le_trans (le_max_left _ _) hR)
  have h2 : A ≤ R / 2 := by
    have h3 : 2 * |A| + 1 ≤ R := le_trans (le_max_right _ _) hR
    have h4 := le_abs_self A
    linarith
  linarith

/-- **`C (1 + log R)² ≤ δ R` eventually** (for `C ≥ 0`, `δ > 0`). -/
theorem log_sq_le_lin (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → C * (1 + Real.log R) ^ 2 ≤ δ * R := by
  refine ⟨max 2 (max ((25 * C / δ) ^ 2) 1), by positivity, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := by
    have h : 2 ≤ R := le_trans (le_max_left _ _) hR
    linarith
  have hRlt : 1 < R := lt_of_lt_of_le one_lt_two (le_trans (le_max_left _ _) hR)
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hlog0 : 0 ≤ Real.log R := Real.log_nonneg hR1
  -- `log R ≤ 4 R^{1/4}`
  have hlq : Real.log R ≤ 4 * R ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div (le_of_lt hRpos) (show (0 : ℝ) < 1 / 4 by norm_num)
    have h4 : R ^ (1 / 4 : ℝ) / (1 / 4) = 4 * R ^ (1 / 4 : ℝ) := by ring
    linarith [h, h4]
  -- hence `(1 + log R)² ≤ 25 √R`
  have h14 : R ^ (1 / 4 : ℝ) ≤ R ^ (1 / 2 : ℝ) :=
    (Real.rpow_le_rpow_left_iff hRlt).mpr (by norm_num)
  have h12 : (1 : ℝ) ≤ R ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow_left_iff hRlt |>.mpr (show (0:ℝ) ≤ 1/2 by norm_num)
    rw [Real.rpow_zero] at h
    exact h
  have hA : (R ^ (1 / 4 : ℝ)) ^ 2 = R ^ (1 / 2 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hRpos]
    norm_num
  have hB : (4 * R ^ (1 / 4 : ℝ)) ^ 2 = 16 * R ^ (1 / 2 : ℝ) := by
    rw [mul_pow, hA]; ring
  have hsq : (1 + Real.log R) ^ 2 ≤ 25 * R ^ (1 / 2 : ℝ) := by
    have h1 : 1 + Real.log R ≤ 1 + 4 * R ^ (1 / 4 : ℝ) := by linarith
    have h2 : (0 : ℝ) ≤ 1 + Real.log R := by linarith
    have h4 : (1 + Real.log R) ^ 2 ≤ (1 + 4 * R ^ (1 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ h2 h1 2
    have h5 : (1 + 4 * R ^ (1 / 4 : ℝ)) ^ 2 = 1 + 8 * R ^ (1 / 4 : ℝ) + 16 * R ^ (1 / 2 : ℝ) := by
      have hexp : (1 + 4 * R ^ (1 / 4 : ℝ)) ^ 2
          = 1 + 2 * (4 * R ^ (1 / 4 : ℝ)) + (4 * R ^ (1 / 4 : ℝ)) ^ 2 := by ring
      rw [hexp, hB]; ring
    rw [h5] at h4
    nlinarith [h4, h14, h12,
      Real.rpow_nonneg (le_of_lt hRpos) (1 / 4 : ℝ),
      Real.rpow_nonneg (le_of_lt hRpos) (1 / 2 : ℝ)]
  have hroot : 25 * C / δ ≤ R ^ (1 / 2 : ℝ) := by
    have h : (25 * C / δ) ^ 2 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
    have h2 : Real.sqrt ((25 * C / δ) ^ 2) ≤ Real.sqrt R := Real.sqrt_le_sqrt h
    have h3 : Real.sqrt ((25 * C / δ) ^ 2) = 25 * C / δ := Real.sqrt_sq (by positivity)
    rw [h3, Real.sqrt_eq_rpow] at h2
    exact h2
  have h1C : 25 * C ≤ δ * R ^ (1 / 2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hroot (le_of_lt hδ)
    rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at h
    linarith
  have hfin : 25 * C * R ^ (1 / 2 : ℝ) ≤ δ * R := by
    have h4 := mul_le_mul_of_nonneg_right h1C (Real.rpow_nonneg (le_of_lt hRpos) (1 / 2 : ℝ))
    have h5 : R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) = R := by
      rw [← Real.rpow_add hRpos]; norm_num
    nlinarith [h4, h5]
  calc C * (1 + Real.log R) ^ 2 ≤ C * (25 * R ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq hC
    _ = 25 * C * R ^ (1 / 2 : ℝ) := by ring
    _ ≤ δ * R := hfin

/-! ## §3 The threshold functions of the lock-step assembly

The assembly fixes one big depth `Rw` and uses the following explicit functions of it.  They are
kept as top-level definitions so that the (purely real-analytic) threshold argument is isolated in
`lockstep_conditions` below, with no dependence on the geometry. -/

/-- The crossing ceiling: an upper bound for the time at which the `c₀`-chart depth first
exceeds `R`. -/
noncomputable def lkJmax (J₀ : ℕ) (Xlo R : ℝ) : ℕ := ⌈(J₀ : ℝ) + (8 / 7) * (R - Xlo) + 2⌉₊

/-- The transit depth: `R` corrected by `Re κ · log R`. -/
noncomputable def lkRt (cre R : ℝ) : ℝ := R - cre * Real.log R - 1 / 4

/-- The explicit dominant of the `WinG` height bound coming from the deepening hypothesis. -/
noncomputable def lkHb (H SaD ρκ a₃ R : ℝ) : ℝ := H + SaD + 2 * ρκ * Real.log (a₃ + (8 / 7) * R) + 4

/-- The height bound of the incoming window. -/
noncomputable def lkHw (H SaD ρκ X₁ W : ℝ) (J₀ : ℕ) (Xlo R : ℝ) : ℝ :=
  H + SaD + 2 * ρκ *
    Real.log (max (max |X₁ + W + 2| |X₁ + W + (lkJmax J₀ Xlo R : ℝ) + 2|) 4) + 4

/-- The bound for the modulus of the `c₀`-chart coordinate of the exit point. -/
noncomputable def lkMf (ρκ C₅ cre R : ℝ) : ℝ :=
  max 1 (4 * (2 + ρκ + |lkRt cre R + C₅| + ρκ ^ 2) ^ 2)

/-- The `E`-error of the exit region. -/
noncomputable def lkEf (ρκ εo C₅ cre R : ℝ) : ℝ :=
  2 + εo + ρκ * (Real.log (lkMf ρκ C₅ cre R) + Real.pi)

/-- The height bound of the exit region. -/
noncomputable def lkHpf (ρκ εo Hout C₅ cre R : ℝ) : ℝ :=
  Hout + εo + ρκ * (Real.log (lkMf ρκ C₅ cre R) + Real.pi)

/-- The repelling-normalisation error at the exit. -/
noncomputable def lkErep (Krep ρκ εo Hout C₅ cre R : ℝ) : ℝ :=
  Krep * (1 + lkHpf ρκ εo Hout C₅ cre R) *
      (1 + Real.log (lkRt cre R + lkEf ρκ εo C₅ cre R)) /
    (lkRt cre R - lkEf ρκ εo C₅ cre R)

/-- An explicit dominant of `lkEf`. -/
noncomputable def lkEh (AE Bhp R : ℝ) : ℝ := AE + Bhp * Real.log R

/-- An explicit dominant of `lkHpf`. -/
noncomputable def lkHph (Ahp Bhp R : ℝ) : ℝ := Ahp + Bhp * Real.log R

/-- An explicit dominant of `lkErep`. -/
noncomputable def lkEreph (Cbig R : ℝ) : ℝ := Cbig * (1 + Real.log R) ^ 2 / R

/-- **The threshold lemma of the lock-step assembly.**  For `R` large enough all the size
conditions needed by the assembly hold simultaneously.  (Every condition is of the form
`O(log R) ≤ c R`; only the bookkeeping is lengthy.) -/
theorem lockstep_conditions (H W X₁ Xo : ℝ) (J₀ : ℕ)
    (Xlo ρκ cre SaD AK Ct Nrep Krep δΨ Rch Rw0 Re0 Ht Hout εo BT θcre : ℝ)
    (C₂ a₃ C₅ Cbank C₃ Ahp AE Bhp C₉ Cbig : ℝ)
    (hρκ : 0 ≤ ρκ) (hAK : 0 ≤ AK) (hCt0 : 0 ≤ Ct) (hKr : 0 ≤ Krep)
    (hδ : 0 < δΨ) (hHout0 : 0 ≤ Hout) (hεo0 : 0 ≤ εo) (hXlo0 : 0 ≤ Xlo) (hSaDnn : 0 ≤ SaD)
    (hC₂ : C₂ = |X₁ + W + 2| + (J₀ : ℝ) + 3) (ha₃ : a₃ = C₂ + 4)
    (hC₅ : C₅ = 2 + Hout + εo + ρκ * Real.pi) (hCbank : Cbank = |cre| + C₅ + 1)
    (hC₃ : C₃ = 2 + ρκ + ρκ ^ 2 + Cbank)
    (hAhp : Ahp = Hout + εo + ρκ * (Real.log (4 * C₃ ^ 2) + 2 + Real.pi))
    (hAE : AE = 2 + εo + ρκ * (Real.log (4 * C₃ ^ 2) + 2 + Real.pi))
    (hBhp : Bhp = 2 * ρκ) (hC₉ : C₉ = Real.log (2 + AE + Bhp) + 1)
    (hCbig : Cbig = 4 * Krep * (1 + Ahp + Bhp) * (1 + C₉)) (hHnn : 0 ≤ H) :
    ∀ᶠ R in Filter.atTop,
      (1 ≤ R) ∧ (BT < R) ∧ (Rch ≤ R) ∧
      (8 * (lkHb H SaD ρκ a₃ R + 1) ≤ R) ∧
      (16 * ρκ * (9 / 8 + lkHb H SaD ρκ a₃ R) ≤ R) ∧
      (max Rch (max (8 * (Ht + 2)) (max Rw0 (max Re0 (max 2 (8 * (Hout + 1)))))) ≤ lkRt cre R) ∧
      (lkEh AE Bhp R + 8 * (lkHph Ahp Bhp R + 1) + 2 ≤ lkRt cre R) ∧
      (Nrep + lkEh AE Bhp R ≤ lkRt cre R) ∧ (2 * lkEh AE Bhp R ≤ lkRt cre R) ∧
      (R / 2 ≤ lkRt cre R) ∧ (lkRt cre R ≤ 2 * R) ∧ (1 ≤ lkRt cre R) ∧
      (lkEreph Cbig R + Ct / lkRt cre R + (AK + 1) / R ≤ δΨ / 2) ∧
      ((lkJmax J₀ Xlo R : ℝ) + (X₁ + W) + θcre + Xo + Ct / lkRt cre R ≤ 2 * lkRt cre R) ∧
      ((R + 9 / 8 + lkHb H SaD ρκ a₃ R) ^ 2 ≤ 2 * R ^ 2) ∧
      (lkRt cre R ≤ (16 / 5) * R) ∧ (16 ≤ lkRt cre R) ∧
      (lkHw H SaD ρκ X₁ W J₀ Xlo R ≤ lkHb H SaD ρκ a₃ R) ∧
      (lkEf ρκ εo C₅ cre R ≤ lkEh AE Bhp R) ∧
      (lkHpf ρκ εo Hout C₅ cre R ≤ lkHph Ahp Bhp R) ∧
      (lkErep Krep ρκ εo Hout C₅ cre R ≤ lkEreph Cbig R) ∧
      (0 ≤ Real.log R) ∧ (Real.log R ≤ R) ∧ (0 ≤ lkEh AE Bhp R) ∧ (0 ≤ lkHph Ahp Bhp R) ∧
      ((lkJmax J₀ Xlo R : ℝ) ≤ (J₀ : ℝ) + (8 / 7) * (R - Xlo) + 3) ∧ (Ct + AK ≤ lkRt cre R) ∧
      (8 * (8 * (Hout + 1) + 1) ≤ lkRt cre R) ∧ (AK ≤ R) ∧ (Xlo ≤ R) := by
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have ha₃pos : 0 < a₃ := by rw [ha₃]; linarith
  have hC₅0 : 0 ≤ C₅ := by
    rw [hC₅]; nlinarith [hHout0, hεo0, mul_nonneg hρκ Real.pi_pos.le]
  have hCbank0 : 0 ≤ Cbank := by rw [hCbank]; linarith [abs_nonneg cre, hC₅0]
  have hC₃1 : 1 ≤ C₃ := by rw [hC₃]; nlinarith [hρκ, hCbank0]
  have hlog4C₃ : 0 ≤ Real.log (4 * C₃ ^ 2) := Real.log_nonneg (by nlinarith [hC₃1])
  have hAhp0 : 0 ≤ Ahp := by
    rw [hAhp]
    nlinarith [hHout0, hεo0, hρκ, hlog4C₃, Real.pi_pos,
      mul_nonneg hρκ (by linarith [hlog4C₃, Real.pi_pos] :
        (0:ℝ) ≤ Real.log (4 * C₃ ^ 2) + 2 + Real.pi)]
  have hAE0 : 0 ≤ AE := by
    rw [hAE]
    nlinarith [hεo0, hρκ, hlog4C₃, Real.pi_pos,
      mul_nonneg hρκ (by linarith [hlog4C₃, Real.pi_pos] :
        (0:ℝ) ≤ Real.log (4 * C₃ ^ 2) + 2 + Real.pi)]
  have hBhp0 : 0 ≤ Bhp := by rw [hBhp]; positivity
  have hC₉0 : 0 ≤ C₉ := by
    rw [hC₉]
    have h : 0 ≤ Real.log (2 + AE + Bhp) := Real.log_nonneg (by linarith [hAE0, hBhp0])
    linarith
  have hCbig0 : 0 ≤ Cbig := by
    rw [hCbig]
    have h1 : 0 ≤ 1 + Ahp + Bhp := by linarith [hAhp0, hBhp0]
    have h2 : 0 ≤ 1 + C₉ := by linarith
    positivity
  -- ## 6. the elementary eventual facts
  have hR1ev : ∀ᶠ R in Filter.atTop, (1 : ℝ) ≤ R := Filter.eventually_ge_atTop 1
  have hlogR0ev : ∀ᶠ R in Filter.atTop, 0 ≤ Real.log R := by
    filter_upwards [hR1ev] with R hR
    exact Real.log_nonneg hR
  have hlogRle : ∀ᶠ R in Filter.atTop, Real.log R ≤ R := by
    filter_upwards [hR1ev] with R hR
    exact Real.log_le_self (by linarith)
  have hRtge : ∀ C : ℝ, ∀ᶠ R in Filter.atTop, C ≤ lkRt cre R := by
    intro C
    obtain ⟨R₀, hR₀pos, hR₀⟩ :=
      affine_log_le_self (C + 1 / 4) |cre| 0 1 (abs_nonneg _) one_pos
    filter_upwards [Filter.eventually_ge_atTop R₀, hR1ev, hlogR0ev] with R hR hR1 hlog0
    have h1 : C + 1 / 4 + |cre| * Real.log R ≤ R := by simpa using hR₀ R hR
    have h3 : cre * Real.log R ≤ |cre| * Real.log R :=
      mul_le_mul_of_nonneg_right (le_abs_self cre) hlog0
    simp only [lkRt]
    linarith
  have hRtge_log : ∀ Aa B : ℝ, 0 ≤ B → ∀ᶠ R in Filter.atTop, Aa + B * Real.log R ≤ lkRt cre R := by
    intro Aa B hB
    obtain ⟨R₀, hR₀pos, hR₀⟩ :=
      affine_log_le_self (Aa + 1 / 4) (|cre| + B) 0 1 (by positivity) one_pos
    filter_upwards [Filter.eventually_ge_atTop R₀, hR1ev, hlogR0ev] with R hR hR1 hlog0
    have h1 : Aa + 1 / 4 + (|cre| + B) * Real.log R ≤ R := by
      have h := hR₀ R hR
      simpa only [zero_add, one_mul, add_mul] using h
    have h3 : cre * Real.log R ≤ |cre| * Real.log R :=
      mul_le_mul_of_nonneg_right (le_abs_self cre) hlog0
    simp only [lkRt]
    linarith
  have hRtHalf : ∀ᶠ R in Filter.atTop, R / 2 ≤ lkRt cre R := by
    obtain ⟨R₀, hR₀pos, hR₀⟩ :=
      affine_log_le_self (1 / 2) (2 * |cre|) 0 1 (by positivity) one_pos
    filter_upwards [Filter.eventually_ge_atTop R₀, hlogR0ev] with R hR hlog0
    have h1 : 1 / 2 + 2 * |cre| * Real.log R ≤ R := by simpa using hR₀ R hR
    have h3 : cre * Real.log R ≤ |cre| * Real.log R :=
      mul_le_mul_of_nonneg_right (le_abs_self cre) hlog0
    simp only [lkRt]
    linarith
  have hRt2R : ∀ᶠ R in Filter.atTop, lkRt cre R ≤ 2 * R := by
    obtain ⟨R₀, hR₀pos, hR₀⟩ := affine_log_le_self 0 |cre| 0 1 (abs_nonneg _) one_pos
    filter_upwards [Filter.eventually_ge_atTop R₀, hlogR0ev] with R hR hlog0
    have h1 : |cre| * Real.log R ≤ R := by simpa using hR₀ R hR
    have h3 : cre * Real.log R ≤ |cre| * Real.log R :=
      mul_le_mul_of_nonneg_right (le_abs_self cre) hlog0
    have h4 : -(cre * Real.log R) ≤ |cre| * Real.log R := by
      have h5 : -(cre * Real.log R) = -(cre) * Real.log R := by ring
      rw [h5]
      exact mul_le_mul_of_nonneg_right (neg_le_abs cre) hlog0
    simp only [lkRt]
    linarith
  have hJmaxub : ∀ᶠ R in Filter.atTop,
      (lkJmax J₀ Xlo R : ℝ) ≤ (J₀ : ℝ) + (8 / 7) * (R - Xlo) + 3 := by
    filter_upwards [Filter.eventually_ge_atTop Xlo, hR1ev] with R hRXlo hR1
    have h0 : 0 ≤ (J₀ : ℝ) + (8 / 7) * (R - Xlo) + 2 := by
      have h : 0 ≤ R - Xlo := by linarith
      positivity
    have h1 := Nat.ceil_lt_add_one h0
    have h2 : ((lkJmax J₀ Xlo R : ℕ) : ℝ) < (J₀ : ℝ) + (8 / 7) * (R - Xlo) + 2 + 1 := by
      simp only [lkJmax]
      exact h1
    linarith
  -- ## 7. domination of the raw functions by the explicit ones
  have hHwdom : ∀ᶠ R in Filter.atTop, lkHw H SaD ρκ X₁ W J₀ Xlo R ≤ lkHb H SaD ρκ a₃ R := by
    filter_upwards [hJmaxub, hR1ev] with R hJmax hR1
    have hpos : 0 ≤ (8 / 7) * R := by positivity
    have hJnn : 0 ≤ (lkJmax J₀ Xlo R : ℝ) := Nat.cast_nonneg _
    have hb1 : |X₁ + W + (lkJmax J₀ Xlo R : ℝ) + 2| ≤ a₃ + (8 / 7) * R := by
      have h1 : |X₁ + W + (lkJmax J₀ Xlo R : ℝ) + 2| ≤ |X₁ + W + 2| + (lkJmax J₀ Xlo R : ℝ) := by
        have h0 : X₁ + W + (lkJmax J₀ Xlo R : ℝ) + 2 = (X₁ + W + 2) + (lkJmax J₀ Xlo R : ℝ) := by ring
        rw [h0]
        have h1' := abs_add_le (X₁ + W + 2) ((lkJmax J₀ Xlo R : ℝ))
        have h1'' : |((lkJmax J₀ Xlo R : ℝ))| = (lkJmax J₀ Xlo R : ℝ) :=
          abs_of_nonneg (Nat.cast_nonneg _)
        linarith [h1', h1'']
      have h2 : (8 / 7) * (R - Xlo) ≤ (8 / 7) * R := by
        have h : (0 : ℝ) ≤ 8 / 7 := by norm_num
        nlinarith [hXlo0, h]
      have h3 : |X₁ + W + 2| + (lkJmax J₀ Xlo R : ℝ)
          ≤ C₂ + ((J₀ : ℝ) + (8 / 7) * (R - Xlo) + 3) := by
        rw [hC₂]; linarith
      rw [ha₃, hC₂]
      linarith
    have ha1 : |X₁ + W + 2| ≤ a₃ + (8 / 7) * R := by
      rw [ha₃, hC₂]
      linarith [hpos]
    have hmax : max (max |X₁ + W + 2| |X₁ + W + (lkJmax J₀ Xlo R : ℝ) + 2|) 4 ≤ a₃ + (8 / 7) * R :=
      max_le (max_le ha1 hb1) (by rw [ha₃, hC₂]; linarith [hpos])
    have hp1 : 0 < max (max |X₁ + W + 2| |X₁ + W + (lkJmax J₀ Xlo R : ℝ) + 2|) 4 := by positivity
    have hp2 : 0 < a₃ + (8 / 7) * R := by positivity
    have hlog := Real.log_le_log hp1 hmax
    simp only [lkHw, lkHb]
    nlinarith [hlog, hρκ, hSaDnn]
  have hMfdom : ∀ᶠ R in Filter.atTop, lkMf ρκ C₅ cre R ≤ 4 * C₃ ^ 2 * (1 + R) ^ 2 := by
    filter_upwards [hR1ev, hlogR0ev, hlogRle] with R hR1 hlog0 hlogle
    have h2' : cre * Real.log R ≤ |cre| * Real.log R :=
      mul_le_mul_of_nonneg_right (le_abs_self cre) hlog0
    have h2'' : |cre| * Real.log R ≤ |cre| * R := mul_le_mul_of_nonneg_left hlogle (abs_nonneg cre)
    have hcreR : cre * Real.log R ≤ |cre| * R := le_trans h2' h2''
    have hkey : lkRt cre R + C₅ ≤ (|cre| + C₅ + 1) * (1 + R) := by
      simp only [lkRt]
      have hcre2 : -(cre * Real.log R) ≤ |cre| * (1 + R) := by
        have h2 : -(cre * Real.log R) ≤ |cre| * Real.log R := by
          have h3 : -(cre) ≤ |cre| := neg_le_abs cre
          nlinarith [h3, hlog0]
        have h4 : |cre| * Real.log R ≤ |cre| * (1 + R) := by
          nlinarith [abs_nonneg cre, hlogle]
        linarith
      have hp2 : C₅ ≤ C₅ * (1 + R) := by nlinarith [hC₅0, hR1]
      have hp5 : R ≤ (|cre| + C₅ + 1) * (1 + R) := by
        have h1 : 0 ≤ C₅ * (1 + R) := by positivity
        have h2 : 0 ≤ |cre| * (1 + R) := by positivity
        nlinarith [hR1, hC₅0, abs_nonneg cre, h1, h2]
      linarith [hcre2, hp2, hp5, hR1]
    have hkey2 : -((|cre| + C₅ + 1) * (1 + R)) ≤ lkRt cre R + C₅ := by
      have h2 : 0 ≤ Real.log R := hlog0
      have hcreR2 : -(|cre| * Real.log R) ≤ -cre * Real.log R := by linarith [hcreR]
      have hb : -(C₅ * (1 + R)) ≤ 0 := by
        nlinarith [hC₅0, hR1]
      have hb2 : -((|cre| + C₅ + 1) * (1 + R)) = -(|cre| * (1 + R)) - C₅ * (1 + R) - (1 + R) := by ring
      have hc : -(|cre| * (1 + R)) ≤ -(|cre| * Real.log R) := by
        nlinarith [abs_nonneg cre, hlogle, h2, hR1]
      simp only [lkRt]
      rw [hb2]
      linarith [hcreR2, hc, hb, hR1]
    have hDf : |lkRt cre R + C₅| ≤ Cbank * (1 + R) := by
      rw [hCbank]
      exact abs_le.mpr ⟨by linarith [hkey2], by linarith [hkey]⟩
    have hinner0 : 0 ≤ 2 + ρκ + |lkRt cre R + C₅| + ρκ ^ 2 := by
      nlinarith [hρκ, abs_nonneg (lkRt cre R + C₅), sq_nonneg ρκ]
    have hC₃R : 2 + ρκ + |lkRt cre R + C₅| + ρκ ^ 2 ≤ C₃ * (1 + R) := by
      rw [hC₃]
      nlinarith [hDf, hρκ, sq_nonneg ρκ, hCbank0, hR1]
    have hpos : 0 ≤ C₃ * (1 + R) := by positivity
    have hsq : 4 * (2 + ρκ + |lkRt cre R + C₅| + ρκ ^ 2) ^ 2 ≤ 4 * C₃ ^ 2 * (1 + R) ^ 2 := by
      nlinarith [hC₃R, hinner0]
    have h1R : (1 : ℝ) ≤ 4 * C₃ ^ 2 * (1 + R) ^ 2 := by
      have h1 : (1 : ℝ) ≤ C₃ ^ 2 := by nlinarith [hC₃1]
      have h2 : (1 : ℝ) ≤ (1 + R) ^ 2 := by nlinarith [hR1]
      nlinarith [h1, h2]
    simp only [lkMf]
    exact max_le h1R hsq
  have hlogMf : ∀ᶠ R in Filter.atTop,
      Real.log (lkMf ρκ C₅ cre R) ≤ Real.log (4 * C₃ ^ 2) + 2 * (Real.log R + 1) := by
    filter_upwards [hMfdom, hR1ev] with R hM hR1
    have hpos : 0 < lkMf ρκ C₅ cre R := by simp only [lkMf]; positivity
    have h1 := Real.log_le_log hpos hM
    have h2 : Real.log (4 * C₃ ^ 2 * (1 + R) ^ 2) = Real.log (4 * C₃ ^ 2) + 2 * Real.log (1 + R) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      norm_num
    have h3 : Real.log (1 + R) ≤ Real.log R + 1 := by
      have h4 : 1 + R ≤ Real.exp 1 * R := by
        have h5 : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
        nlinarith [Real.exp_pos 1]
      have h6 := Real.log_le_log (by linarith : (0 : ℝ) < 1 + R) h4
      rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt (by linarith : (0 : ℝ) < R)), Real.log_exp] at h6
      linarith
    rw [h2] at h1
    linarith
  have hHpfdom : ∀ᶠ R in Filter.atTop, lkHpf ρκ εo Hout C₅ cre R ≤ lkHph Ahp Bhp R := by
    filter_upwards [hlogMf] with R hlog
    have h2 := mul_le_mul_of_nonneg_left
      (by linarith : Real.log (lkMf ρκ C₅ cre R) + Real.pi ≤
        Real.log (4 * C₃ ^ 2) + 2 * (Real.log R + 1) + Real.pi) hρκ
    simp only [lkHpf, lkHph]
    rw [hBhp]
    linarith
  have hEfdom : ∀ᶠ R in Filter.atTop, lkEf ρκ εo C₅ cre R ≤ lkEh AE Bhp R := by
    filter_upwards [hlogMf] with R hlog
    have h2 := mul_le_mul_of_nonneg_left
      (by linarith : Real.log (lkMf ρκ C₅ cre R) + Real.pi ≤
        Real.log (4 * C₃ ^ 2) + 2 * (Real.log R + 1) + Real.pi) hρκ
    simp only [lkEf, lkEh]
    rw [hBhp]
    linarith
  have hEhnn : ∀ᶠ R in Filter.atTop, 0 ≤ lkEh AE Bhp R := by
    filter_upwards [hlogR0ev] with R hlog0
    simp only [lkEh]
    nlinarith [hAE0, hBhp0]
  have hHphnn : ∀ᶠ R in Filter.atTop, 0 ≤ lkHph Ahp Bhp R := by
    filter_upwards [hlogR0ev] with R hlog0
    simp only [lkHph]
    nlinarith [hAhp0, hBhp0]
  -- ## 8. the conditions on the explicit functions
  have hc4 : ∀ᶠ R in Filter.atTop, 8 * (lkHb H SaD ρκ a₃ R + 1) ≤ R := by
    obtain ⟨R₀, hR₀pos, hR₀⟩ := affine_log_le_self (8 * (H + SaD + 5)) (16 * ρκ) a₃ (8 / 7)
      (by positivity) (by norm_num)
    filter_upwards [Filter.eventually_ge_atTop R₀] with R hR
    have h1 := hR₀ R hR
    have h2 : 8 * (lkHb H SaD ρκ a₃ R + 1) ≤ 8 * (H + SaD + 5) + 16 * ρκ * Real.log (a₃ + (8 / 7) * R) := by
      simp only [lkHb]
      nlinarith [hρκ]
    linarith
  have hc5 : ∀ᶠ R in Filter.atTop, 16 * ρκ * (9 / 8 + lkHb H SaD ρκ a₃ R) ≤ R := by
    obtain ⟨R₀, hR₀pos, hR₀⟩ := affine_log_le_self (16 * ρκ * (9 / 8 + H + SaD + 4))
      (32 * ρκ ^ 2) a₃ (8 / 7) (by positivity) (by norm_num)
    filter_upwards [Filter.eventually_ge_atTop R₀] with R hR
    have h1 := hR₀ R hR
    have h2 : 16 * ρκ * (9 / 8 + lkHb H SaD ρκ a₃ R) ≤ 16 * ρκ * (9 / 8 + H + SaD + 4) +
        32 * ρκ ^ 2 * Real.log (a₃ + (8 / 7) * R) := by
      simp only [lkHb]
      nlinarith [hρκ, sq_nonneg ρκ]
    linarith
  have hc7 : ∀ᶠ R in Filter.atTop, lkEh AE Bhp R + 8 * (lkHph Ahp Bhp R + 1) + 2 ≤ lkRt cre R := by
    filter_upwards [hRtge_log (AE + 8 * Ahp + 10) (Bhp + 8 * Bhp) (by positivity)] with R h4
    simp only [lkEh, lkHph]
    nlinarith [h4]
  have hc8 : ∀ᶠ R in Filter.atTop, Nrep + lkEh AE Bhp R ≤ lkRt cre R := by
    filter_upwards [hRtge_log (Nrep + AE) Bhp hBhp0] with R h4
    simp only [lkEh]
    linarith
  have hc9 : ∀ᶠ R in Filter.atTop, 2 * lkEh AE Bhp R ≤ lkRt cre R := by
    filter_upwards [hRtge_log (2 * AE) (2 * Bhp) (by positivity)] with R h4
    simp only [lkEh]
    linarith
  have hErepdom : ∀ᶠ R in Filter.atTop, lkErep Krep ρκ εo Hout C₅ cre R ≤ lkEreph Cbig R := by
    filter_upwards [hEfdom, hHpfdom, hRtHalf, hRt2R, hc9, hlogR0ev, hlogRle, hR1ev, hRtge 1]
      with R hEf hHpf hhalf h2R h9 hlog0 hlogle hR1 hRt1'
    have hAA : 0 ≤ 1 + Ahp + Bhp := by linarith [hAhp0, hBhp0]
    have hHpf' : lkHpf ρκ εo Hout C₅ cre R ≤ Ahp + Bhp * Real.log R := by
      simpa only [lkHph] using hHpf
    have hEf' : lkEf ρκ εo C₅ cre R ≤ AE + Bhp * Real.log R := by
      simpa only [lkEh] using hEf
    have hEfnn : 0 ≤ lkEf ρκ εo C₅ cre R := by
      rw [lkEf]
      have hMf1 : 1 ≤ lkMf ρκ C₅ cre R := le_max_left _ _
      have hl : 0 ≤ Real.log (lkMf ρκ C₅ cre R) := Real.log_nonneg hMf1
      nlinarith [hεo0, hρκ, hl, Real.pi_pos]
    have hHpfnn : 0 ≤ lkHpf ρκ εo Hout C₅ cre R := by
      rw [lkHpf]
      have hMf1 : 1 ≤ lkMf ρκ C₅ cre R := le_max_left _ _
      have hl : 0 ≤ Real.log (lkMf ρκ C₅ cre R) := Real.log_nonneg hMf1
      nlinarith [hHout0, hεo0, hρκ, hl, Real.pi_pos]
    have hpos : 0 < lkRt cre R - lkEf ρκ εo C₅ cre R := by linarith [hEhnn, h9]
    have hden : R / 4 ≤ lkRt cre R - lkEf ρκ εo C₅ cre R := by linarith
    have h1 : 1 + lkHpf ρκ εo Hout C₅ cre R ≤ (1 + Ahp + Bhp) * (1 + Real.log R) := by
      have hh : lkHpf ρκ εo Hout C₅ cre R ≤ Ahp + Bhp * Real.log R := by
        simpa only [lkHph] using hHpf
      nlinarith [hh, hAA, hlog0]
    have hsum : lkRt cre R + lkEf ρκ εo C₅ cre R ≤ (2 + AE + Bhp) * (1 + R) := by
      have he : lkEf ρκ εo C₅ cre R ≤ AE + Bhp * Real.log R := by
        simpa only [lkEh] using hEf
      nlinarith [he, hAE0, hBhp0, hlogle, h2R, hR1]
    have hCpos : 0 < 2 + AE + Bhp := by linarith [hAE0, hBhp0]
    have hlogsum : Real.log (lkRt cre R + lkEf ρκ εo C₅ cre R) ≤ Real.log (2 + AE + Bhp) + (Real.log R + 1) := by
      have hp : 0 < lkRt cre R + lkEf ρκ εo C₅ cre R := by
        linarith [h9, hEfnn, hRt1']
      have h3 := Real.log_le_log hp hsum
      rw [Real.log_mul (ne_of_gt hCpos) (ne_of_gt (by linarith : (0 : ℝ) < 1 + R))] at h3
      have h4 : Real.log (1 + R) ≤ Real.log R + 1 := by
        have h5 : 1 + R ≤ Real.exp 1 * R := by
          have h6 : (2 : ℝ) ≤ Real.exp 1 := by
            have := Real.add_one_le_exp (1 : ℝ)
            linarith
          nlinarith [Real.exp_pos 1]
        have h7 := Real.log_le_log (by linarith : (0 : ℝ) < 1 + R) h5
        rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt (by linarith : (0 : ℝ) < R)), Real.log_exp] at h7
        linarith
      linarith
    have h2 : 1 + Real.log (lkRt cre R + lkEf ρκ εo C₅ cre R) ≤ (1 + C₉) * (1 + Real.log R) := by
      rw [hC₉]
      nlinarith [hlogsum, hlog0]
    have h3 : 0 ≤ 1 + Real.log (lkRt cre R + lkEf ρκ εo C₅ cre R) := by
      have : 0 ≤ Real.log (lkRt cre R + lkEf ρκ εo C₅ cre R) :=
        Real.log_nonneg (by linarith [hEfnn, hRt1'])
      linarith
    have h4 : 0 ≤ (1 + C₉) * (1 + Real.log R) := by nlinarith [hC₉0, hlog0]
    have hnum : Krep * (1 + lkHpf ρκ εo Hout C₅ cre R) * (1 + Real.log (lkRt cre R + lkEf ρκ εo C₅ cre R)) ≤
        Krep * ((1 + Ahp + Bhp) * (1 + Real.log R)) * ((1 + C₉) * (1 + Real.log R)) := by
      have h5 : 0 ≤ Krep * (1 + lkHpf ρκ εo Hout C₅ cre R) := by
        have h6 : 0 ≤ lkHpf ρκ εo Hout C₅ cre R := hHpfnn
        nlinarith [hKr, h6]
      calc Krep * (1 + lkHpf ρκ εo Hout C₅ cre R) * (1 + Real.log (lkRt cre R + lkEf ρκ εo C₅ cre R))
          ≤ Krep * (1 + lkHpf ρκ εo Hout C₅ cre R) * ((1 + C₉) * (1 + Real.log R)) :=
            mul_le_mul_of_nonneg_left h2 h5
        _ ≤ Krep * ((1 + Ahp + Bhp) * (1 + Real.log R)) * ((1 + C₉) * (1 + Real.log R)) := by
            have h6 : Krep * (1 + lkHpf ρκ εo Hout C₅ cre R) ≤ Krep * ((1 + Ahp + Bhp) * (1 + Real.log R)) :=
              mul_le_mul_of_nonneg_left h1 hKr
            exact mul_le_mul_of_nonneg_right h6 h4
    have h7 : Krep * ((1 + Ahp + Bhp) * (1 + Real.log R)) * ((1 + C₉) * (1 + Real.log R))
        = (Krep * (1 + Ahp + Bhp) * (1 + C₉)) * (1 + Real.log R) ^ 2 := by ring
    rw [h7] at hnum
    have h8 : Cbig * (1 + Real.log R) ^ 2 = 4 * (Krep * (1 + Ahp + Bhp) * (1 + C₉)) * (1 + Real.log R) ^ 2 := by
      rw [hCbig]; ring
    have hK : 0 ≤ Krep * (1 + Ahp + Bhp) * (1 + C₉) := by linarith [hKr, hAA, hC₉0]
    have hs : 0 ≤ (1 + Real.log R) ^ 2 := sq_nonneg _
    have hmain : Krep * (1 + lkHpf ρκ εo Hout C₅ cre R) *
          (1 + Real.log (lkRt cre R + lkEf ρκ εo C₅ cre R)) * R
        ≤ Cbig * (1 + Real.log R) ^ 2 * (lkRt cre R - lkEf ρκ εo C₅ cre R) := by
      have hnum' : Krep * (1 + lkHpf ρκ εo Hout C₅ cre R) *
            (1 + Real.log (lkRt cre R + lkEf ρκ εo C₅ cre R))
          ≤ Cbig * (1 + Real.log R) ^ 2 / 4 := by linarith [hnum, h7, h8]
      have hden' : R ≤ 4 * (lkRt cre R - lkEf ρκ εo C₅ cre R) := by linarith [hden]
      have hQ0 : 0 ≤ Cbig * (1 + Real.log R) ^ 2 / 4 :=
        div_nonneg (mul_nonneg hCbig0 hs) (by norm_num)
      calc Krep * (1 + lkHpf ρκ εo Hout C₅ cre R) *
            (1 + Real.log (lkRt cre R + lkEf ρκ εo C₅ cre R)) * R
          ≤ (Cbig * (1 + Real.log R) ^ 2 / 4) *
              (4 * (lkRt cre R - lkEf ρκ εo C₅ cre R)) :=
            mul_le_mul hnum' hden' (by linarith : (0 : ℝ) ≤ R) hQ0
        _ = Cbig * (1 + Real.log R) ^ 2 * (lkRt cre R - lkEf ρκ εo C₅ cre R) := by ring
    simp only [lkErep, lkEreph]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < lkRt cre R - lkEf ρκ εo C₅ cre R),
      div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0:ℝ) < R)]
    exact hmain
  have hfin : ∀ᶠ R in Filter.atTop,
      (1 ≤ R) ∧ (BT < R) ∧ (Rch ≤ R) ∧
      (8 * (lkHb H SaD ρκ a₃ R + 1) ≤ R) ∧
      (16 * ρκ * (9 / 8 + lkHb H SaD ρκ a₃ R) ≤ R) ∧
      (max Rch (max (8 * (Ht + 2)) (max Rw0 (max Re0 (max 2 (8 * (Hout + 1)))))) ≤ lkRt cre R) ∧
      (lkEh AE Bhp R + 8 * (lkHph Ahp Bhp R + 1) + 2 ≤ lkRt cre R) ∧
      (Nrep + lkEh AE Bhp R ≤ lkRt cre R) ∧ (2 * lkEh AE Bhp R ≤ lkRt cre R) ∧
      (R / 2 ≤ lkRt cre R) ∧ (lkRt cre R ≤ 2 * R) ∧ (1 ≤ lkRt cre R) ∧
      (lkEreph Cbig R + Ct / lkRt cre R + (AK + 1) / R ≤ δΨ / 2) ∧
      ((lkJmax J₀ Xlo R : ℝ) + (X₁ + W) + θcre + Xo + Ct / lkRt cre R ≤ 2 * lkRt cre R) ∧
      ((R + 9 / 8 + lkHb H SaD ρκ a₃ R) ^ 2 ≤ 2 * R ^ 2) ∧ (lkRt cre R ≤ (16 / 5) * R) ∧ (16 ≤ lkRt cre R) ∧
      (lkHw H SaD ρκ X₁ W J₀ Xlo R ≤ lkHb H SaD ρκ a₃ R) ∧ (lkEf ρκ εo C₅ cre R ≤ lkEh AE Bhp R) ∧ (lkHpf ρκ εo Hout C₅ cre R ≤ lkHph Ahp Bhp R) ∧ (lkErep Krep ρκ εo Hout C₅ cre R ≤ lkEreph Cbig R) ∧
      (0 ≤ Real.log R) ∧ (Real.log R ≤ R) ∧ (0 ≤ lkEh AE Bhp R) ∧ (0 ≤ lkHph Ahp Bhp R) ∧
      ((lkJmax J₀ Xlo R : ℝ) ≤ (J₀ : ℝ) + (8 / 7) * (R - Xlo) + 3) ∧ (Ct + AK ≤ lkRt cre R) ∧
      (8 * (8 * (Hout + 1) + 1) ≤ lkRt cre R) ∧ (AK ≤ R) ∧ (Xlo ≤ R) := by
    have hconj13 : ∀ᶠ R in Filter.atTop,
        lkEreph Cbig R + Ct / lkRt cre R + (AK + 1) / R ≤ δΨ / 2 := by
      obtain ⟨R₀, hR₀pos, hR₀⟩ := log_sq_le_lin (2 * (Cbig + 2 * Ct + AK + 1)) (δΨ / 2)
        (by positivity) (by linarith)
      filter_upwards [hRtHalf, Filter.eventually_ge_atTop R₀, hR1ev] with R hHalf hmul hR1
      have hRpos : 0 < R := by linarith
      have hlog0 : 0 ≤ Real.log R := Real.log_nonneg hR1
      have hm : 2 * (Cbig + 2 * Ct + AK + 1) * (1 + Real.log R) ^ 2 ≤ (δΨ / 2) * R := hR₀ R hmul
      have hS1 : 1 ≤ (1 + Real.log R) ^ 2 := by nlinarith
      have hSsum : (Cbig + 2 * Ct + AK + 1) * (1 + Real.log R) ^ 2 / R ≤ δΨ / 4 := by
        rw [div_le_iff₀ hRpos]
        linarith [hm]
      have hCt_le : Ct / lkRt cre R ≤ 2 * Ct / R := by
        have h1 : Ct / lkRt cre R ≤ Ct / (R / 2) :=
          div_le_div_of_nonneg_left hCt0 (by linarith) hHalf
        have h2 : Ct / (R / 2) = 2 * Ct / R := by ring
        linarith
      have hCt_le2 : 2 * Ct / R ≤ 2 * Ct * (1 + Real.log R) ^ 2 / R := by
        apply div_le_div_of_nonneg_right _ hRpos.le
        simpa using mul_le_mul_of_nonneg_left hS1 (by linarith : (0 : ℝ) ≤ 2 * Ct)
      have hAK_le : (AK + 1) / R ≤ (AK + 1) * (1 + Real.log R) ^ 2 / R := by
        apply div_le_div_of_nonneg_right _ hRpos.le
        simpa using mul_le_mul_of_nonneg_left hS1 (by linarith : (0 : ℝ) ≤ AK + 1)
      have hkey : Cbig * (1 + Real.log R) ^ 2 / R + Ct / lkRt cre R + (AK + 1) / R
          ≤ (Cbig + 2 * Ct + AK + 1) * (1 + Real.log R) ^ 2 / R := by
        have h4 : (Cbig + 2 * Ct + AK + 1) * (1 + Real.log R) ^ 2 / R
            = Cbig * (1 + Real.log R) ^ 2 / R + 2 * Ct * (1 + Real.log R) ^ 2 / R
              + (AK + 1) * (1 + Real.log R) ^ 2 / R := by ring
        rw [h4]
        linarith [hCt_le, hCt_le2, hAK_le]
      simp only [lkEreph]
      linarith [hkey, hSsum]
    have hconj14 : ∀ᶠ R in Filter.atTop,
        (lkJmax J₀ Xlo R : ℝ) + (X₁ + W) + θcre + Xo + Ct / lkRt cre R ≤ 2 * lkRt cre R := by
      obtain ⟨R₀, hR₀pos, hR₀⟩ := affine_log_le_self
        (7 * ((J₀ : ℝ) + 3 + (X₁ + W) + θcre + Xo + 2 * Ct + 1 / 2)) (7 * (2 * |cre|)) 0 1
        (by positivity) one_pos
      filter_upwards [hJmaxub, Filter.eventually_ge_atTop R₀, hR1ev, hRtHalf]
        with R hJmax h1 hR1 hHalf
      have hlog0 : 0 ≤ Real.log R := Real.log_nonneg hR1
      have h2 := hR₀ R h1
      rw [zero_add, one_mul] at h2
      have hRtU : lkRt cre R = R - cre * Real.log R - 1 / 4 := rfl
      have hCt1 : Ct / (R - cre * Real.log R - 1 / 4) ≤ 2 * Ct := by
        have h3 : 2 * Ct / R ≤ 2 * Ct := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < R)]
          nlinarith [hCt0, hR1]
        have h4 : Ct / (R - cre * Real.log R - 1 / 4) ≤ 2 * Ct / R := by
          have h5 : R / 2 ≤ R - cre * Real.log R - 1 / 4 := by rw [← hRtU]; exact hHalf
          have h6 : Ct / (R - cre * Real.log R - 1 / 4) ≤ Ct / (R / 2) :=
            div_le_div_of_nonneg_left hCt0 (by linarith) h5
          have h7 : Ct / (R / 2) = 2 * Ct / R := by ring
          linarith
        linarith
      have hcremax : cre * Real.log R ≤ |cre| * Real.log R :=
        mul_le_mul_of_nonneg_right (le_abs_self cre) hlog0
      rw [hRtU]
      nlinarith [hJmax, h2, hCt1, hcremax, hXlo0, hR1]
    have hconj15 : ∀ᶠ R in Filter.atTop,
        (R + 9 / 8 + lkHb H SaD ρκ a₃ R) ^ 2 ≤ 2 * R ^ 2 := by
      obtain ⟨R₀, hR₀pos, hR₀⟩ := affine_log_le_self
        (8 * (H + SaD + 4 + 9 / 8)) (16 * ρκ) a₃ (8 / 7) (by positivity) (by norm_num)
      filter_upwards [Filter.eventually_ge_atTop R₀, hR1ev] with R h1 hR1
      have h2 := hR₀ R h1
      have h3 : 8 * (lkHb H SaD ρκ a₃ R + 9 / 8) ≤ R := by rw [lkHb]; linarith
      have hlhb4 : 4 ≤ lkHb H SaD ρκ a₃ R := by
        rw [lkHb]
        have hlog : 0 ≤ Real.log (a₃ + 8 / 7 * R) := Real.log_nonneg (by linarith [ha₃pos, hR1])
        nlinarith [hHnn, hSaDnn, hρκ, hlog]
      have hX0 : 0 ≤ R + 9 / 8 + lkHb H SaD ρκ a₃ R := by linarith
      have hXle : R + 9 / 8 + lkHb H SaD ρκ a₃ R ≤ (9 / 8) * R := by linarith
      calc (R + 9 / 8 + lkHb H SaD ρκ a₃ R) ^ 2 ≤ ((9 / 8) * R) ^ 2 :=
            pow_le_pow_left₀ hX0 hXle 2
        _ ≤ 2 * R ^ 2 := by nlinarith [sq_nonneg R]
    have hconj16 : ∀ᶠ R in Filter.atTop, lkRt cre R ≤ (16 / 5) * R := by
      obtain ⟨R₀, hR₀pos, hR₀⟩ := affine_log_le_self 0 |cre| 0 1 (abs_nonneg _) one_pos
      filter_upwards [Filter.eventually_ge_atTop R₀, hR1ev] with R h1 hR1
      have h2 : |cre| * Real.log R ≤ R := by
        have h := hR₀ R h1
        simpa only [zero_add, one_mul] using h
      have hlog0 : 0 ≤ Real.log R := Real.log_nonneg hR1
      have h4 : -(cre * Real.log R) ≤ |cre| * Real.log R := by
        have h5 : -(cre) ≤ |cre| := neg_le_abs cre
        have h6 : -(cre) * Real.log R ≤ |cre| * Real.log R := mul_le_mul_of_nonneg_right h5 hlog0
        have h7 : -(cre) * Real.log R = -(cre * Real.log R) := by ring
        linarith
      rw [lkRt]
      linarith
    filter_upwards [hR1ev, Filter.eventually_gt_atTop BT, Filter.eventually_ge_atTop Rch,
      hc4, hc5, hRtge _, hc7, hc8, hc9, hRtHalf, hRt2R, hRtge 1,
      hconj13, hconj14, hconj15, hconj16,
      hRtge 16, hHwdom, hEfdom, hHpfdom, hErepdom, hlogR0ev, hlogRle, hEhnn, hHphnn, hJmaxub,
      hRtge (Ct + AK), hRtge (8 * (8 * (Hout + 1) + 1)), Filter.eventually_ge_atTop AK,
      Filter.eventually_ge_atTop Xlo] with
      R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24
        h25 h26 h27 h28 h29 h30
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩
  exact hfin



theorem lockstep_complex {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (A : Work.FlowerGlue2.AttrCompare P fl.Pa fl.φa) (hrn : Work.PARIMPL2.Lavaurs.RepNorm P fl.Ψ)
    (hdeep : ∀ X₁ W H : ℝ, ∃ sa : ℂ, ∀ X : ℝ, ∃ J : ℕ, ∀ y ∈ fl.Pa,
      X₁ ≤ (fl.φa y).re → (fl.φa y).re ≤ X₁ + W → |(fl.φa y).im| ≤ H →
        ∀ j ≥ J, X < (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[j] y)).re ∧
          |(Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[j] y)).im|
            ≤ H + |sa.im| + 2 * ‖P.κ c₀‖ * Real.log (X₁ + W + j + 2) + 4)
    (nIn : ℕ) (hentry : Work.PARIMPL.entryPt P nIn c₀ ∈ fl.Pa) :
    ∃ θc : ℂ, Work.PARIMPL2.LockstepAll c₀ P.Nm
      (fun c => (((fl.φa (Work.PARIMPL.entryPt P nIn c₀)).re - Real.pi / P.lam c : ℝ) : ℂ) + θc)
      nIn (fun c z => Work.PARIMPL.Ft c z) fl.Pa fl.φa fl.Ψ
      ((fl.φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)) := by
  obtain ⟨sr, Nrep, Krep, hNr, hKr, hrep⟩ := hrn
  set θc : ℂ := sr - A.sa with hθcdef
  refine ⟨θc, ?_⟩
  intro H W Xo η X₁ hη
  by_cases hHneg : H < 0
  · refine ⟨1, one_pos, ?_⟩
    intro c hc y y' n hPa h1 h2 h3 hy' hu1 hu2
    exact absurd h3 (fun hle => by linarith [abs_nonneg (fl.φa y).im, hle, hHneg])
  rw [not_lt] at hHneg
  -- ## 1. the level rectangle and the modulus of continuity of `Ψ`
  obtain ⟨δΨ₀, hδΨ₀pos, hδΨ₀⟩ :=
    psi_unif fl Xo (|θc.im| + H + 2) (by linarith : (0 : ℝ) < η / 2)
  set δΨ : ℝ := min δΨ₀ 1 with hδΨdef
  have hδΨpos : 0 < δΨ := lt_min hδΨ₀pos one_pos
  have hδΨle₀ : δΨ ≤ δΨ₀ := min_le_left _ _
  have hδΨle1 : δΨ ≤ 1 := min_le_right _ _
  -- ## 2. the deepening data
  set saD : ℂ := Classical.choose (hdeep X₁ W H) with hsaDdef
  have hsaDspec := Classical.choose_spec (hdeep X₁ W H)
  obtain ⟨Rlo, hRlopos, hRloincr⟩ := Work.PARIMPL2.LavaursA.w0_increment P A H (by norm_num : (0 : ℝ) < 1 / 8)
  set Xlo : ℝ := max (max A.N 0 + 2) (Rlo + 1) with hXlodef
  have hXloN : A.N < Xlo := by
    rw [hXlodef]
    have h1 : A.N ≤ max A.N 0 := le_max_left A.N 0
    have h2 : max A.N 0 + 2 ≤ max (max A.N 0 + 2) (Rlo + 1) := le_max_left _ _
    linarith
  have hXlo1 : 1 ≤ Xlo := by
    rw [hXlodef]
    have h2 : Rlo + 1 ≤ max (max A.N 0 + 2) (Rlo + 1) := le_max_right _ _
    linarith
  have hXlo0 : 0 ≤ Xlo := le_trans zero_le_one hXlo1
  set J₀ : ℕ := Classical.choose (hsaDspec Xlo) with hJ₀def
  have hJ₀spec := Classical.choose_spec (hsaDspec Xlo)
  obtain ⟨BT, hBT⟩ := bt_bound P fl A hXloN hXlo1 hJ₀spec
  -- ## 3. the fixed heights and tolerances
  set ρκ : ℝ := ‖P.κ c₀‖ with hρκdef
  set cre : ℝ := (P.κ c₀).re with hcredef
  set Sa : ℝ := |A.sa.im| with hSadef
  set SaD : ℝ := |saD.im| with hSaDdef
  set Hin : ℝ := H + Sa + 1 with hHindef
  set Ht : ℝ := Hin + 1 with hHtdef
  set Hout : ℝ := Ht + 1 with hHoutdef
  set εw : ℝ := min (1 / 8) (δΨ / 8) with hεwdef
  set εo : ℝ := min (1 / 8) (δΨ / 8) with hεodef
  set C₅ : ℝ := 2 + Hout + εo + ρκ * Real.pi with hC₅def
  -- ## 4. the parameter thresholds
  obtain ⟨Rch, hRch4, hRchOK⟩ := exists_Rch' P
  obtain ⟨Ct, hCt0, hCt⟩ := transit_exit_direct P Ht Rch hRch4 hRchOK
  obtain ⟨Rw0, hRw0pos, hRw0spec⟩ := Work.PARIMPL2.LavaursA.wout_level P
  obtain ⟨Re0, hRe0pos, hRe0spec⟩ := Work.PARIMPL2.LavaursA.exit_zeta_lo P
  have hρκnn : 0 ≤ ρκ := by rw [hρκdef]; exact norm_nonneg _
  have hεw8 : εw ≤ 1 / 8 := by rw [hεwdef]; exact min_le_left _ _
  have hεo8 : εo ≤ 1 / 8 := by rw [hεodef]; exact min_le_left _ _
  have hεo0 : 0 ≤ εo := by
    rw [hεodef]
    exact le_of_lt (lt_min (by norm_num) (by linarith [hδΨpos]))
  have hHout0 : 0 ≤ Hout := by
    rw [hHoutdef, hHtdef, hHindef, hSadef]
    have h : 0 ≤ |A.sa.im| := abs_nonneg _
    linarith
  have hC₅0 : 0 ≤ C₅ := by
    rw [hC₅def]
    nlinarith [hHout0, hεo0, mul_nonneg hρκnn Real.pi_pos.le]
  have hSaDnn : 0 ≤ SaD := by rw [hSaDdef]; exact abs_nonneg _
  have hHout0 : 0 ≤ Hout := by
    rw [hHoutdef, hHtdef, hHindef, hSadef]
    have h : 0 ≤ |A.sa.im| := abs_nonneg _
    linarith
  set C₂ : ℝ := |X₁ + W + 2| + (J₀ : ℝ) + 3 with hC₂def
  set a₃ : ℝ := C₂ + 4 with ha₃def
  set Cbank : ℝ := |cre| + C₅ + 1 with hCbankdef
  set C₃ : ℝ := 2 + ρκ + ρκ ^ 2 + Cbank with hC₃def
  set A_hp : ℝ := Hout + εo + ρκ * (Real.log (4 * C₃ ^ 2) + 2 + Real.pi) with hA_hpdef
  set A_E : ℝ := 2 + εo + ρκ * (Real.log (4 * C₃ ^ 2) + 2 + Real.pi) with hA_Edef
  set Bhp : ℝ := 2 * ρκ with hBhpdef
  set C₉ : ℝ := Real.log (2 + A_E + Bhp) + 1 with hC₉def
  set Cbig : ℝ := 4 * Krep * (1 + A_hp + Bhp) * (1 + C₉) with hCbigdef
  -- ## 5. the numerical thresholds (see `lockstep_conditions`)
  have hcond := lockstep_conditions H W X₁ Xo J₀ Xlo ρκ cre SaD A.K Ct Nrep Krep δΨ Rch Rw0 Re0
    Ht Hout εo BT θc.re C₂ a₃ C₅ Cbank C₃ A_hp A_E Bhp C₉ Cbig
    hρκnn A.K_nonneg hCt0 hKr hδΨpos hHout0 hεo0 hXlo0 hSaDnn hC₂def ha₃def hC₅def hCbankdef
    hC₃def hA_hpdef hA_Edef hBhpdef hC₉def hCbigdef hHneg
  obtain ⟨Rw, hRw⟩ := Filter.eventually_atTop.mp hcond
  have hRwall := hRw Rw le_rfl
  obtain ⟨hRw1, hRwBT, hRwRch, hRwHb, hRwo, hRwmax, hRwEf, hRwNrep, hRw2Ef, hRwHalf, hRw2R,
    hRwRt1, hRwErr, hRwJmax, hRwsq, hRwRt16b, hRw16, hHwdom, hEfdom, hHpfdom, hErepdom,
    hlogR0, hlogRle, hEh0, hHph0, hJmaxub, hCtle, hRwHout2, hAKle, hXloRw⟩ := hRwall
  -- ## 6. the radii of the perturbation
  obtain ⟨Rpa, hRpa0, hRpa⟩ := Work.PARIMPL2.LavaursA.pa_bounded fl
  have hHw8 : 8 * (lkHw H SaD ρκ X₁ W J₀ Xlo Rw + 1) ≤ Rw := by linarith [hHwdom, hRwHb]
  have hεopos : 0 < εo := by
    rw [hεodef]
    exact lt_min (by norm_num) (by linarith [hδΨpos])
  have hwm1 : Rch ≤ lkRt cre Rw := le_trans (le_max_left _ _) hRwmax
  have hwm2 : max (8 * (Ht + 2)) (max Rw0 (max Re0 (max 2 (8 * (Hout + 1))))) ≤ lkRt cre Rw :=
    le_trans (le_max_right _ _) hRwmax
  have hwm3 : 8 * (Ht + 2) ≤ lkRt cre Rw := le_trans (le_max_left _ _) hwm2
  have hwm4 : max Rw0 (max Re0 (max 2 (8 * (Hout + 1)))) ≤ lkRt cre Rw :=
    le_trans (le_max_right _ _) hwm2
  have hwm5 : Rw0 ≤ lkRt cre Rw := le_trans (le_max_left _ _) hwm4
  have hwm6 : max Re0 (max 2 (8 * (Hout + 1))) ≤ lkRt cre Rw := le_trans (le_max_right _ _) hwm4
  have hwm7 : Re0 ≤ lkRt cre Rw := le_trans (le_max_left _ _) hwm6
  have hwm8 : max 2 (8 * (Hout + 1)) ≤ lkRt cre Rw := le_trans (le_max_right _ _) hwm6
  have hwm9 : 2 ≤ lkRt cre Rw := le_trans (le_max_left _ _) hwm8
  have hwm10 : 8 * (Hout + 1) ≤ lkRt cre Rw := le_trans (le_max_right _ _) hwm8
  have hRwpos : 0 < Rw := by linarith
  have hRTpos : 0 < lkRt cre Rw := by linarith
  have hεwpos : 0 < εw := by
    rw [hεwdef]
    exact lt_min (by norm_num) (by linarith [hδΨpos])
  obtain ⟨ρw, δw, hρw, hδw, hwin⟩ :=
    win_model P Rw (lkHw H SaD ρκ X₁ W J₀ Xlo Rw) (hRchOK Rw hRwRch).1 hHw8 εw hεwpos
  set εch : ℝ := min (1 / 8) (1 / (4 * Rw)) with hεchdef
  have hεchpos : 0 < εch := by
    rw [hεchdef]
    exact lt_min (by norm_num) (by positivity)
  obtain ⟨ρch, δch, hρch, hδch, hchart⟩ :=
    chartZeta_uniform_close P Rw (lkHw H SaD ρκ X₁ W J₀ Xlo Rw) εch hHw8 hεchpos
  have hRneed : max Rch (8 * (Ht + 2)) ≤ lkRt cre Rw := max_le hwm1 hwm3
  obtain ⟨ρt, hρt, htrans⟩ := hCt (lkRt cre Rw) hRneed
  obtain ⟨ρo, hρo, hwout'⟩ := hRw0spec (lkRt cre Rw) hwm5 Hout hwm10 εo hεopos
  obtain ⟨ρl, hρl, hexit'⟩ := hRe0spec (lkRt cre Rw) hwm7 (8 * (Hout + 1)) hRwHout2
  -- the chart coordinate of the parabolic point is small
  have hz1small : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
      ‖Work.PARIMPL.chartZeta P c d.z₁‖ ≤ 1 / (8 * lkRt cre Rw) := by
    have hm : ContinuousAt (fun c => P.m c) c₀ :=
      P.cont_m.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
    have hsn : ContinuousAt (fun c => P.s c) c₀ :=
      P.cont_s.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
    have hlim : Work.PARIMPL.chartZeta P c₀ d.z₁ = 0 := by
      simp [Work.PARIMPL.chartZeta, P.m₀]
    have hcont : ContinuousAt (fun c => Work.PARIMPL.chartZeta P c d.z₁) c₀ := by
      have h1 : ContinuousAt (fun c => d.z₁ - P.m c) c₀ := continuousAt_const.sub hm
      have h2 : ContinuousAt (fun c => (d.z₁ - P.m c) / P.s c) c₀ :=
        h1.div hsn (P.s_ne c₀ (Metric.mem_ball_self P.hρ₀))
      simpa [Work.PARIMPL.chartZeta] using h2
    obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousAt_iff.mp hcont (1 / (8 * lkRt cre Rw)) (by positivity)
    refine ⟨ρ, hρ, fun c hc => ?_⟩
    have hd : dist c c₀ < ρ := Metric.mem_ball.mp hc.2
    have hthis := hρ' hd
    rw [hlim, dist_zero_right] at hthis
    exact le_of_lt hthis
  obtain ⟨ρz1₀, hρz1₀, hz1spec₀⟩ := hz1small
  have hparrad : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
      ‖P.m c - d.z₁‖ ≤ ‖P.s c₀‖ / 2 ∧ ‖P.s c‖ ≤ 2 * ‖P.s c₀‖ := by
    have hm : ContinuousAt (fun c => P.m c) c₀ :=
      P.cont_m.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
    have hsn : ContinuousAt (fun c => P.s c) c₀ :=
      P.cont_s.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
    have hs0 : 0 < ‖P.s c₀‖ := norm_pos_iff.mpr (P.s_ne c₀ (Metric.mem_ball_self P.hρ₀))
    obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := Metric.continuousAt_iff.mp hm (‖P.s c₀‖ / 2) (by positivity)
    obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := Metric.continuousAt_iff.mp hsn (‖P.s c₀‖) (by positivity)
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun c hc => ?_⟩
    have hc₁ : dist c c₀ < ρ₁ := lt_of_lt_of_le (Metric.mem_ball.mp hc.2) (min_le_left _ _)
    have hc₂ : dist c c₀ < ρ₂ := lt_of_lt_of_le (Metric.mem_ball.mp hc.2) (min_le_right _ _)
    have h1 := hρ₁' hc₁
    rw [dist_eq_norm, P.m₀] at h1
    have h2 := hρ₂' hc₂
    rw [dist_eq_norm] at h2
    have h3 : ‖P.s c‖ ≤ ‖P.s c₀‖ + ‖P.s c - P.s c₀‖ := by
      have h := norm_add_le (P.s c₀) (P.s c - P.s c₀)
      have h4 : P.s c₀ + (P.s c - P.s c₀) = P.s c := by ring
      rwa [h4] at h
    exact ⟨le_of_lt h1, by linarith [h2, h3]⟩
  obtain ⟨ρpar, hρpar, hparspec₀⟩ := hparrad
  set ρz1 : ℝ := min ρz1₀ ρpar with hρz1def
  have hρz1 : 0 < ρz1 := by rw [hρz1def]; positivity
  have hρz1le₁ : ρz1 ≤ ρz1₀ := by rw [hρz1def]; exact min_le_left _ _
  have hρz1le₂ : ρz1 ≤ ρpar := by rw [hρz1def]; exact min_le_right _ _
  have hz1spec : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρz1,
      ‖Work.PARIMPL.chartZeta P c d.z₁‖ ≤ 1 / (8 * lkRt cre Rw) := by
    intro c hc
    exact hz1spec₀ c ⟨hc.1, lt_of_lt_of_le (Metric.mem_ball.mp hc.2) hρz1le₁⟩
  have hparspec : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρz1,
      ‖P.m c - d.z₁‖ ≤ ‖P.s c₀‖ / 2 ∧ ‖P.s c‖ ≤ 2 * ‖P.s c₀‖ := by
    intro c hc
    exact hparspec₀ c ⟨hc.1, lt_of_lt_of_le (Metric.mem_ball.mp hc.2) hρz1le₂⟩
  have hNrepEf : Nrep + lkEf ρκ εo C₅ cre Rw ≤ lkRt cre Rw := by linarith [hRwNrep, hEfdom]
  have hHwo : 16 * ρκ * (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) ≤ Rw := by
    nlinarith [hRwo, hHwdom, hρκnn]
  -- ## 7. the crossing of the deepening window
  set Kq : Set ℂ := Metric.closedBall 0 (max Rpa (‖d.z₁‖ + ‖P.s c₀‖) + 1) with hKqdef
  have hKqcomp : IsCompact Kq := by rw [hKqdef]; exact isCompact_closedBall _ _
  have hyK : ∀ z ∈ fl.Pa, z ∈ Kq := by
    intro z hz
    have h1 := hRpa z hz
    rw [hKqdef, Metric.mem_closedBall, dist_zero_right]
    linarith [le_max_left Rpa (‖d.z₁‖ + ‖P.s c₀‖)]
  set εft : ℝ := min δw δch / 4 with hεftdef
  have hεftpos : 0 < εft := by rw [hεftdef]; positivity
  obtain ⟨ρft, hρft, hft⟩ := ft_iter_unif hKqcomp (lkJmax J₀ Xlo Rw + 1) hεftpos
  obtain ⟨δ2, hδ2, hft2⟩ := ft_same_iter_unif hKqcomp (lkJmax J₀ Xlo Rw + 1) hεftpos
  obtain ⟨ρsuf, hρsuf, hsuf⟩ := ft_iter_unif hKqcomp (Nat.ceil (2 * lkRt cre Rw + 4 + |X₁| + |θc.re| + Ct / lkRt cre Rw)) (by linarith : (0 : ℝ) < η / 2)
  obtain ⟨Jhi, hJhi⟩ := hsaDspec (Rw + 1)
  have hRlo_le : Rlo ≤ Xlo := by
    rw [hXlodef]
    have h : Rlo + 1 ≤ max (max A.N 0 + 2) (Rlo + 1) := le_max_right _ _
    linarith
  have hcross : ∀ y ∈ fl.Pa, X₁ ≤ (fl.φa y).re → (fl.φa y).re ≤ X₁ + W → |(fl.φa y).im| ≤ H →
      ∃ j : ℕ, J₀ < j ∧ j ≤ lkJmax J₀ Xlo Rw ∧ Rw ≤ (Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).re ∧
        (Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).re ≤ Rw + 9 / 8 ∧
        |(Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).im| ≤ lkHw H SaD ρκ X₁ W J₀ Xlo Rw := by
    intro y hyPa h1 h2 h3
    have hJz := hJ₀spec y hyPa h1 h2 h3
    have hJhi' := hJhi y hyPa h1 h2 h3
    have hbty : (Work.PARIMPL2.w0 P ((Ft c₀)^[J₀] y)).re < Rw :=
      lt_of_le_of_lt (hBT y hyPa h1 h2 h3) hRwBT
    have hincr : ∀ j : ℕ, J₀ ≤ j →
        (7 / 8 : ℝ) ≤ (fun j => (Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).re) (j + 1) -
          (fun j => (Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).re) j ∧
        (fun j => (Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).re) (j + 1) -
          (fun j => (Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).re) j ≤ 9 / 8 := by
      intro j hj
      have hJj := hJz j hj
      have hzPa : (Ft c₀)^[j] y ∈ fl.Pa := (A.mapsTo_Pa.iterate j) hyPa
      have himz : |(fl.φa ((Ft c₀)^[j] y)).im| ≤ H := by
        rw [phi_shift_iter P fl A j hyPa]
        simpa using h3
      have hinc := hRloincr ((Ft c₀)^[j] y) hzPa (by linarith [hJj.1, hRlo_le])
        (lt_trans hXloN hJj.1) himz
      have hsucc : (fun j => (Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).re) (j + 1) =
          (Work.PARIMPL2.w0 P (Ft c₀ ((Ft c₀)^[j] y))).re := by
        simp only [Function.iterate_succ_apply']
      rw [hsucc]
      exact ⟨by linarith [hinc.1], by linarith [hinc.2]⟩
    have hex : ∃ j : ℕ, Rw ≤ (fun j => (Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).re) j :=
      ⟨Jhi, le_of_lt (lt_of_le_of_lt (by linarith : Rw ≤ Rw + 1) (hJhi' Jhi le_rfl).1)⟩
    obtain ⟨j, hjJ, hjRw, hjov, hjub⟩ :=
      Work.PARIMPL2.LavaursA.crossing_nat (s := fun j => (Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).re)
        (J := J₀) (Xlo := Xlo) (Rw := Rw) (hJz J₀ le_rfl).1 hincr hbty hex
    have h1' : (j : ℝ) ≤ (J₀ : ℝ) + (8 / 7) * (Rw - Xlo) + 1 := hjub
    have h2' : (J₀ : ℝ) + (8 / 7) * (Rw - Xlo) + 1 ≤ (lkJmax J₀ Xlo Rw : ℝ) := by
      have h3' := Nat.le_ceil ((J₀ : ℝ) + (8 / 7) * (Rw - Xlo) + 2)
      simp only [lkJmax]
      linarith
    have hjJM : j ≤ lkJmax J₀ Xlo Rw := by exact_mod_cast le_trans h1' h2'
    refine ⟨j, hjJ, hjJM, hjRw, hjov, ?_⟩
    · -- the height bound at the crossing time
      have hJj := hJz j (le_of_lt hjJ)
      have hjr : (j : ℝ) ≤ (lkJmax J₀ Xlo Rw : ℝ) := by exact_mod_cast hjJM
      have hlogmono : Real.log (X₁ + W + (j : ℝ) + 2) ≤
          Real.log (max (max |X₁ + W + 2| |X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2|) 4) := by
        have hlogabs : ∀ a : ℝ, |a| ≤
            max (max |X₁ + W + 2| |X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2|) 4 →
            Real.log a ≤ Real.log (max (max |X₁ + W + 2| |X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2|) 4) := by
          intro a ha
          have h1a : Real.log |a| ≤
              Real.log (max (max |X₁ + W + 2| |X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2|) 4) := by
            rcases eq_or_lt_of_le (abs_nonneg a) with h | h
            · rw [← h, Real.log_zero]
              exact Real.log_nonneg (by linarith [le_max_right (max |X₁ + W + 2| |X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2|) 4])
            · exact Real.log_le_log h ha
          rwa [Real.log_abs] at h1a
        refine hlogabs _ ?_
        rw [abs_le]
        constructor
        · have h4 : -(X₁ + W + (j : ℝ) + 2) ≤ -(X₁ + W + 2) := by
            have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
            linarith
          have h5 : -(X₁ + W + 2) ≤ |X₁ + W + 2| := neg_le_abs _
          have h6 : |X₁ + W + 2| ≤
              max (max |X₁ + W + 2| |X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2|) 4 :=
            le_trans (le_max_left _ _) (le_max_left _ _)
          linarith
        · have h4 : X₁ + W + (j : ℝ) + 2 ≤ X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2 := by linarith [hjr]
          have h5 : X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2 ≤
              |X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2| := le_abs_self _
          have h6 : |X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2| ≤
              max (max |X₁ + W + 2| |X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2|) 4 :=
            le_trans (le_max_right _ _) (le_max_left _ _)
          linarith
      have h2'' : |(Work.PARIMPL2.w0 P ((Ft c₀)^[j] y)).im| ≤
          H + |saD.im| + 2 * ‖P.κ c₀‖ * Real.log (X₁ + W + (j : ℝ) + 2) + 4 := hJj.2
      have hρκnn' : 0 ≤ ‖P.κ c₀‖ := by rw [← hρκdef]; exact hρκnn
      simp only [lkHw, hρκdef, hSaDdef]
      nlinarith [h2'', hlogmono, hρκnn', abs_nonneg saD.im]
  -- ## 8. the per-point argument
  set ρ₁ : ℝ := min ρw δ2 with hρ₁def
  set ρ₂ : ℝ := min ρch ρt with hρ₂def
  set ρ₃ : ℝ := min ρo ρl with hρ₃def
  set ρ₄ : ℝ := min ρz1 (min ρft (min ρsuf 1)) with hρ₄def
  set ρ₅ : ℝ := min ρ₁ (min ρ₂ (min ρ₃ ρ₄)) with hρ₅def
  have hρ₅pos : 0 < ρ₅ := by
    rw [hρ₅def, hρ₁def, hρ₂def, hρ₃def, hρ₄def]
    positivity
  have h5w : ρ₅ ≤ ρw := by
    have h1 : ρ₅ ≤ ρ₁ := by rw [hρ₅def]; exact min_le_left _ _
    have h2 : ρ₁ ≤ ρw := by rw [hρ₁def]; exact min_le_left _ _
    linarith
  have h5δ2 : ρ₅ ≤ δ2 := by
    have h1 : ρ₅ ≤ ρ₁ := by rw [hρ₅def]; exact min_le_left _ _
    have h2 : ρ₁ ≤ δ2 := by rw [hρ₁def]; exact min_le_right _ _
    linarith
  have h5ch : ρ₅ ≤ ρch := by
    have h1 : ρ₅ ≤ min ρ₂ (min ρ₃ ρ₄) := by rw [hρ₅def]; exact min_le_right _ _
    have h2 : min ρ₂ (min ρ₃ ρ₄) ≤ ρ₂ := min_le_left _ _
    have h3 : ρ₂ ≤ ρch := by rw [hρ₂def]; exact min_le_left _ _
    linarith
  have h5t : ρ₅ ≤ ρt := by
    have h1 : ρ₅ ≤ min ρ₂ (min ρ₃ ρ₄) := by rw [hρ₅def]; exact min_le_right _ _
    have h2 : min ρ₂ (min ρ₃ ρ₄) ≤ ρ₂ := min_le_left _ _
    have h3 : ρ₂ ≤ ρt := by rw [hρ₂def]; exact min_le_right _ _
    linarith
  have h5o : ρ₅ ≤ ρo := by
    have h1 : ρ₅ ≤ min ρ₂ (min ρ₃ ρ₄) := by rw [hρ₅def]; exact min_le_right _ _
    have h2 : min ρ₂ (min ρ₃ ρ₄) ≤ min ρ₃ ρ₄ := min_le_right _ _
    have h3 : min ρ₃ ρ₄ ≤ ρ₃ := min_le_left _ _
    have h4 : ρ₃ ≤ ρo := by rw [hρ₃def]; exact min_le_left _ _
    linarith
  have h5l : ρ₅ ≤ ρl := by
    have h1 : ρ₅ ≤ min ρ₂ (min ρ₃ ρ₄) := by rw [hρ₅def]; exact min_le_right _ _
    have h2 : min ρ₂ (min ρ₃ ρ₄) ≤ min ρ₃ ρ₄ := min_le_right _ _
    have h3 : min ρ₃ ρ₄ ≤ ρ₃ := min_le_left _ _
    have h4 : ρ₃ ≤ ρl := by rw [hρ₃def]; exact min_le_right _ _
    linarith
  have h5z1 : ρ₅ ≤ ρz1 := by
    have h1 : ρ₅ ≤ min ρ₂ (min ρ₃ ρ₄) := by rw [hρ₅def]; exact min_le_right _ _
    have h2 : min ρ₂ (min ρ₃ ρ₄) ≤ min ρ₃ ρ₄ := min_le_right _ _
    have h3 : min ρ₃ ρ₄ ≤ ρ₄ := min_le_right _ _
    have h4 : ρ₄ ≤ ρz1 := by rw [hρ₄def]; exact min_le_left _ _
    linarith
  have h5ft : ρ₅ ≤ ρft := by
    have h1 : ρ₅ ≤ min ρ₂ (min ρ₃ ρ₄) := by rw [hρ₅def]; exact min_le_right _ _
    have h2 : min ρ₂ (min ρ₃ ρ₄) ≤ min ρ₃ ρ₄ := min_le_right _ _
    have h3 : min ρ₃ ρ₄ ≤ ρ₄ := min_le_right _ _
    have h4 : ρ₄ ≤ min ρft (min ρsuf 1) := by rw [hρ₄def]; exact min_le_right _ _
    have h6 : min ρft (min ρsuf 1) ≤ ρft := min_le_left _ _
    linarith
  have h5suf : ρ₅ ≤ ρsuf := by
    have h1 : ρ₅ ≤ min ρ₂ (min ρ₃ ρ₄) := by rw [hρ₅def]; exact min_le_right _ _
    have h2 : min ρ₂ (min ρ₃ ρ₄) ≤ min ρ₃ ρ₄ := min_le_right _ _
    have h3 : min ρ₃ ρ₄ ≤ ρ₄ := min_le_right _ _
    have h4 : ρ₄ ≤ min ρft (min ρsuf 1) := by rw [hρ₄def]; exact min_le_right _ _
    have h6 : min ρft (min ρsuf 1) ≤ min ρsuf 1 := min_le_right _ _
    have h7 : min ρsuf 1 ≤ ρsuf := min_le_left _ _
    linarith
  have h51 : ρ₅ ≤ 1 := by
    have h1 : ρ₅ ≤ min ρ₂ (min ρ₃ ρ₄) := by rw [hρ₅def]; exact min_le_right _ _
    have h2 : min ρ₂ (min ρ₃ ρ₄) ≤ min ρ₃ ρ₄ := min_le_right _ _
    have h3 : min ρ₃ ρ₄ ≤ ρ₄ := min_le_right _ _
    have h4 : ρ₄ ≤ min ρft (min ρsuf 1) := by rw [hρ₄def]; exact min_le_right _ _
    have h6 : min ρft (min ρsuf 1) ≤ min ρsuf 1 := min_le_right _ _
    have h7 : min ρsuf 1 ≤ 1 := min_le_right _ _
    linarith
  refine ⟨ρ₅, hρ₅pos, ?_⟩
  intro c hc y y' n hPa hY₁ hY₂ hY₃ hy' u hu1 hu2
  obtain ⟨hcNm, hcball₀⟩ := hc
  have hcball : ‖c - c₀‖ < ρ₅ := by
    have h := Metric.mem_ball.mp hcball₀
    rwa [dist_eq_norm] at h
  have hbw : c ∈ Metric.ball c₀ ρw := by
    rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hcball h5w
  have hbch : c ∈ Metric.ball c₀ ρch := by
    rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hcball h5ch
  have hbt : c ∈ Metric.ball c₀ ρt := by
    rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hcball h5t
  have hbo : c ∈ Metric.ball c₀ ρo := by
    rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hcball h5o
  have hbl : c ∈ Metric.ball c₀ ρl := by
    rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hcball h5l
  have hbz1 : c ∈ Metric.ball c₀ ρz1 := by
    rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hcball h5z1
  have hcw : ‖c - c₀‖ < ρw := lt_of_lt_of_le hcball h5w
  have hcδ2 : ‖c - c₀‖ < δ2 := lt_of_lt_of_le hcball h5δ2
  have hcch : ‖c - c₀‖ < ρch := lt_of_lt_of_le hcball h5ch
  have hct : ‖c - c₀‖ < ρt := lt_of_lt_of_le hcball h5t
  have hco : ‖c - c₀‖ < ρo := lt_of_lt_of_le hcball h5o
  have hcl : ‖c - c₀‖ < ρl := lt_of_lt_of_le hcball h5l
  have hcz1 : ‖c - c₀‖ < ρz1 := lt_of_lt_of_le hcball h5z1
  have hcft : ‖c - c₀‖ < ρft := lt_of_lt_of_le hcball h5ft
  have hcsuf : ‖c - c₀‖ < ρsuf := lt_of_lt_of_le hcball h5suf
  have hc1 : ‖c - c₀‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hcball h51)
  have hcy' : ‖y' - y‖ ≤ 1 := le_trans hy' h51
  -- the crossing
  obtain ⟨j, hjJ, hjJM, hjs, hjsov, hjsim⟩ := hcross y hPa hY₁ hY₂ hY₃
  set p : ℂ := (Ft c₀)^[j] y with hpdef
  set p' : ℂ := (Ft c)^[j] y' with hp'def
  have hpPa : p ∈ fl.Pa := (A.mapsTo_Pa.iterate j) hPa
  have hpne : p ≠ d.z₁ := by
    intro h
    rw [h] at hjs
    simp only [Work.PARIMPL2.w0, sub_self, div_zero, Complex.zero_re] at hjs
    linarith
  have hpWin : p ∈ Work.PARIMPL2.WinG P Rw (lkHw H SaD ρκ X₁ W J₀ Xlo Rw) :=
    ⟨hpne, ⟨hjs, by linarith [hjsov]⟩, hjsim⟩
  have hyK1 : y ∈ Kq := hyK y hPa
  have hyK2 : y' ∈ Kq := by
    have h2 : ‖y'‖ ≤ ‖y - y'‖ + ‖y‖ := by
      have h3 : ‖y - (y - y')‖ ≤ ‖y‖ + ‖y - y'‖ := norm_sub_le y (y - y')
      have h4 : y - (y - y') = y' := by ring
      have h5 : ‖y'‖ ≤ ‖y‖ + ‖y - y'‖ := by rwa [h4] at h3
      linarith
    have h4 : ‖y - y'‖ = ‖y' - y‖ := norm_sub_rev _ _
    rw [h4] at h2
    have h5 := hRpa y hPa
    rw [hKqdef, Metric.mem_closedBall, dist_zero_right]
    linarith [le_max_left Rpa (‖d.z₁‖ + ‖P.s c₀‖)]
  have hft1 : ‖(Ft c)^[j] y' - (Ft c₀)^[j] y'‖ ≤ εft :=
    hft c hcft j (by omega) y' hyK2
  have hft2' : ‖(Ft c₀)^[j] y' - (Ft c₀)^[j] y‖ ≤ εft :=
    hft2 j (by omega) y' hyK2 y hyK1 (le_trans hy' h5δ2)
  have hp'dist : ‖p' - p‖ ≤ min δw δch := by
    have h1 : εft = min δw δch / 4 := hεftdef
    have h2 : ‖p' - p‖ ≤ εft + εft := by
      rw [hpdef, hp'def]
      have hsplit : (Ft c)^[j] y' - (Ft c₀)^[j] y =
          ((Ft c)^[j] y' - (Ft c₀)^[j] y') + ((Ft c₀)^[j] y' - (Ft c₀)^[j] y) := by ring
      rw [hsplit]
      exact le_trans (norm_add_le _ _) (by linarith [hft1, hft2'])
    have h3 : 0 ≤ min δw δch := le_min hδw.le hδch.le
    rw [h1] at h2
    linarith
  -- the incoming model estimate
  have hwin' := hwin c ⟨hcNm, hbw⟩ p hpWin p' (le_trans hp'dist (min_le_left _ _))
  -- the log bridge pinning the model coordinate of `p`
  have hHWnn : 0 ≤ 9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw := by
    have hlog4 : 0 ≤ Real.log (max (max |X₁ + W + 2| |X₁ + W + (lkJmax J₀ Xlo Rw : ℝ) + 2|) 4) :=
      Real.log_nonneg (le_trans (by norm_num) (le_max_right _ _))
    simp only [lkHw]
    nlinarith [hρκnn, hSaDnn]
  have ho' : 2 * ρκ * (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw ≤ 1 / 8 := by
    have h2 : 16 * ρκ * (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) ≤ Rw := hHwo
    rw [div_le_iff₀ hRwpos]
    nlinarith [h2]
  have hlogbridge : (P.κ c₀ * Complex.log (Work.PARIMPL2.w0 P p)).re -
      (P.κ c₀).re * Real.log Rw ≤ 2 * ρκ * (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw ∧
      -((P.κ c₀ * Complex.log (Work.PARIMPL2.w0 P p)).re -
      (P.κ c₀).re * Real.log Rw) ≤ 2 * ρκ * (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw := by
    have hlogl : ‖Complex.log (Work.PARIMPL2.w0 P p) - Complex.log ((Rw : ℝ) : ℂ)‖ ≤
        ‖Work.PARIMPL2.w0 P p - ((Rw : ℝ) : ℂ)‖ / Rw :=
      norm_log_sub_log_le (c := Rw) hRwpos (z := Work.PARIMPL2.w0 P p) (w := ((Rw : ℝ) : ℂ))
        hjs (by simp)
    have hnorm : ‖Work.PARIMPL2.w0 P p - ((Rw : ℝ) : ℂ)‖ ≤
        9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw := by
      have h1 : |(Work.PARIMPL2.w0 P p - ((Rw : ℝ) : ℂ)).re| ≤ 9 / 8 := by
        simp only [Complex.sub_re, Complex.ofReal_re]
        rw [abs_le]
        exact ⟨by linarith [hjs], by linarith [hjsov]⟩
      have h2 : |(Work.PARIMPL2.w0 P p - ((Rw : ℝ) : ℂ)).im| ≤
          lkHw H SaD ρκ X₁ W J₀ Xlo Rw := by
        simpa using hjsim
      calc ‖Work.PARIMPL2.w0 P p - ((Rw : ℝ) : ℂ)‖
          ≤ |(Work.PARIMPL2.w0 P p - ((Rw : ℝ) : ℂ)).re| +
            |(Work.PARIMPL2.w0 P p - ((Rw : ℝ) : ℂ)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw := by linarith
    have hlog2 : ‖Complex.log (Work.PARIMPL2.w0 P p) - Complex.log ((Rw : ℝ) : ℂ)‖ ≤
        (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw :=
      calc ‖Complex.log (Work.PARIMPL2.w0 P p) - Complex.log ((Rw : ℝ) : ℂ)‖
          ≤ ‖Work.PARIMPL2.w0 P p - ((Rw : ℝ) : ℂ)‖ / Rw := hlogl
        _ ≤ (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw :=
            div_le_div_of_nonneg_right hnorm hRwpos.le
    have hlogRw : Complex.log ((Rw : ℝ) : ℂ) = ((Real.log Rw : ℝ) : ℂ) :=
      (Complex.ofReal_log hRwpos.le).symm
    have hκ : (P.κ c₀ * Complex.log (Work.PARIMPL2.w0 P p)).re - (P.κ c₀).re * Real.log Rw
        = (P.κ c₀ * (Complex.log (Work.PARIMPL2.w0 P p) - Complex.log ((Rw : ℝ) : ℂ))).re := by
      rw [hlogRw]
      simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hρκeq : ‖P.κ c₀‖ = ρκ := hρκdef.symm
    have hmain : ‖(P.κ c₀ * (Complex.log (Work.PARIMPL2.w0 P p) -
        Complex.log ((Rw : ℝ) : ℂ))).re‖ ≤
        2 * ρκ * (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw := by
      calc |(P.κ c₀ * (Complex.log (Work.PARIMPL2.w0 P p) -
            Complex.log ((Rw : ℝ) : ℂ))).re|
          ≤ ‖P.κ c₀ * (Complex.log (Work.PARIMPL2.w0 P p) - Complex.log ((Rw : ℝ) : ℂ))‖ :=
            Complex.abs_re_le_norm _
        _ = ‖P.κ c₀‖ * ‖Complex.log (Work.PARIMPL2.w0 P p) - Complex.log ((Rw : ℝ) : ℂ)‖ :=
            norm_mul _ _
        _ ≤ ‖P.κ c₀‖ * ((9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw) :=
            mul_le_mul_of_nonneg_left hlog2 (norm_nonneg _)
        _ = ‖P.κ c₀‖ * (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw := by ring
        _ ≤ 2 * ρκ * (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw := by
            rw [hρκeq]
            have h2 : (0 : ℝ) ≤ ρκ * (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw :=
              div_nonneg (mul_nonneg hρκnn hHWnn) hRwpos.le
            have h3 : 2 * ρκ * (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw =
                2 * (ρκ * (9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw) / Rw) := by ring
            rw [h3]
            linarith
    rw [hκ]
    have h := abs_le.mp hmain
    exact ⟨h.2, by linarith [h.1]⟩
  -- the window of `approxCoord` at `p`
  have hbridge1 : lkRt cre Rw + 1 / 8 ≤
      (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).re := by
    have happ : (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).re =
        (Work.PARIMPL2.w0 P p).re - (P.κ c₀ * Complex.log (Work.PARIMPL2.w0 P p)).re := by
      simp [Work.FatouCoord.approxCoord, Complex.sub_re]
    have h2 := hlogbridge.1
    rw [happ]
    simp only [lkRt]
    linarith
  have hbridge2 : (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).re ≤
      lkRt cre Rw + 15 / 8 := by
    have happ : (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).re =
        (Work.PARIMPL2.w0 P p).re - (P.κ c₀ * Complex.log (Work.PARIMPL2.w0 P p)).re := by
      simp [Work.FatouCoord.approxCoord, Complex.sub_re]
    have h2 := hlogbridge.2
    rw [happ]
    simp only [lkRt]
    linarith
  -- the asymptotic comparison at `p`
  have hNRw : A.N < (Work.FlowerGlue2.w0 P p).re := by
    have h1 : A.N < (Work.PARIMPL2.w0 P p).re := lt_of_lt_of_le (lt_of_lt_of_le hXloN hXloRw) hjs
    simpa only [Work.FlowerGlue2.w0, Work.PARIMPL2.w0] using h1
  have hasymp_p := A.asymp p hpPa hpne hNRw
  have hAppIm : |(Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).im| ≤
      H + |A.sa.im| + 1 := by
    have himp : (fl.φa p).im = (fl.φa y).im := by
      rw [phi_shift_iter P fl A j hPa]
      simp
    have h1 : |(Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) + A.sa).im -
        (fl.φa p).im| ≤ A.K / (Work.PARIMPL2.w0 P p).re := by
      calc |(Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) + A.sa).im - (fl.φa p).im|
          = |((Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) + A.sa) -
              fl.φa p).im| := by rw [Complex.sub_im]
        _ ≤ ‖(Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) + A.sa) - fl.φa p‖ :=
            Complex.abs_im_le_norm _
        _ = ‖fl.φa p - (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) + A.sa)‖ :=
            norm_sub_rev _ _
        _ ≤ A.K / (Work.PARIMPL2.w0 P p).re := hasymp_p
    have h2 : A.K / (Work.PARIMPL2.w0 P p).re ≤ 1 := by
      rw [div_le_one (by linarith [hXloN, A.N_pos])]
      exact le_trans hAKle hjs
    have h3 : |(Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).im| ≤
        |(Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) + A.sa).im| + |A.sa.im| := by
      have h4 : (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).im =
          ((Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).im + A.sa.im) +
            (-A.sa.im) := by ring
      rw [h4]
      calc |((Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).im + A.sa.im) +
            (-A.sa.im)|
          ≤ |(Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).im + A.sa.im| +
            |-A.sa.im| := abs_add_le _ _
        _ = |(Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).im + A.sa.im| +
            |A.sa.im| := by rw [abs_neg]
    have h5 : |(Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) + A.sa).im| ≤
        |(fl.φa p).im| + 1 := by
      have h1'' : |(Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) + A.sa).im -
          (fl.φa p).im| ≤ 1 := le_trans h1 h2
      have hz : (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) + A.sa).im =
          (fl.φa p).im + ((Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) + A.sa).im -
            (fl.φa p).im) := by ring
      rw [hz]
      exact le_trans (abs_add_le _ _) (by linarith)
    rw [himp] at h5
    linarith [h3, h5, hY₃]
  have hUin_re : (Work.PARIMPL.approxUin P c p').re ∈
      Set.Icc (Real.pi / P.lam c - lkRt cre Rw - 2) (Real.pi / P.lam c - lkRt cre Rw) := by
    have h1 : |(Work.PARIMPL.approxUin P c p' -
        (((Real.pi / P.lam c : ℝ) : ℂ) - Work.FatouCoord.approxCoord (P.κ c₀)
          (Work.PARIMPL2.w0 P p))).re| ≤ εw :=
      le_trans (Complex.abs_re_le_norm _) hwin'
    have h2 : (Work.PARIMPL.approxUin P c p').re =
        (Real.pi / P.lam c - (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).re) +
        (Work.PARIMPL.approxUin P c p' -
          (((Real.pi / P.lam c : ℝ) : ℂ) - Work.FatouCoord.approxCoord (P.κ c₀)
            (Work.PARIMPL2.w0 P p))).re := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      ring
    rw [abs_le] at h1
    constructor
    · rw [h2]; linarith [h1.1, hbridge1, hbridge2, hεw8]
    · rw [h2]; linarith [h1.2, hbridge1, hbridge2, hεw8]
  have hUin_im : |(Work.PARIMPL.approxUin P c p').im| ≤ Ht := by
    have hsub : (Work.PARIMPL.approxUin P c p' -
        (((Real.pi / P.lam c : ℝ) : ℂ) - Work.FatouCoord.approxCoord (P.κ c₀)
          (Work.PARIMPL2.w0 P p))).im =
        (Work.PARIMPL.approxUin P c p').im -
        (((Real.pi / P.lam c : ℝ) : ℂ) - Work.FatouCoord.approxCoord (P.κ c₀)
          (Work.PARIMPL2.w0 P p)).im := by
      simp [Complex.sub_im]
    have h1 : |(Work.PARIMPL.approxUin P c p').im -
        (((Real.pi / P.lam c : ℝ) : ℂ) - Work.FatouCoord.approxCoord (P.κ c₀)
          (Work.PARIMPL2.w0 P p)).im| ≤ 1 / 8 := by
      rw [← hsub]
      exact le_trans (le_trans (Complex.abs_im_le_norm _) hwin') hεw8
    have h2 : (((Real.pi / P.lam c : ℝ) : ℂ) - Work.FatouCoord.approxCoord (P.κ c₀)
          (Work.PARIMPL2.w0 P p)).im = -(Work.FatouCoord.approxCoord (P.κ c₀)
          (Work.PARIMPL2.w0 P p)).im := by
      simp [Complex.sub_im]
    rw [abs_le] at h1
    rw [h2] at h1
    have h3 : Ht = H + |A.sa.im| + 2 := by rw [hHtdef, hHindef, hSadef]; ring
    rw [h3, abs_le]
    constructor <;> linarith [h1.1, h1.2, hAppIm,
      le_abs_self (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).im,
      neg_le_abs (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p)).im]
  -- the chart conditions at `p'`
  have hζre : (Work.PARIMPL.chartZeta P c p').re < 0 := by
    have hchart' := hchart c ⟨hcNm, hbch⟩ p hpWin p' (le_trans hp'dist (min_le_right _ _))
    have hz : Work.PARIMPL.chartZeta P c₀ p = -1 / Work.PARIMPL2.w0 P p := by
      have hs0 : P.s c₀ ≠ 0 := P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)
      have hp0 : p - d.z₁ ≠ 0 := sub_ne_zero.mpr hpne
      rw [Work.PARIMPL.chartZeta, P.m₀, Work.PARIMPL2.w0]
      field_simp <;> ring
    have hre0 : (Work.PARIMPL.chartZeta P c₀ p).re = -(Work.PARIMPL2.w0 P p).re /
        ‖Work.PARIMPL2.w0 P p‖ ^ 2 := by
      rw [hz, Complex.div_re]
      simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im, zero_mul, add_zero]
      rw [Complex.normSq_eq_norm_sq]
      ring
    have hpos : 0 < (Work.PARIMPL2.w0 P p).re := lt_of_lt_of_le hRwpos hjs
    have h1 : -(Work.PARIMPL2.w0 P p).re / ‖Work.PARIMPL2.w0 P p‖ ^ 2 ≤ -(1 / 2) / Rw := by
      rw [neg_div, neg_div]
      refine neg_le_neg ?_
      have h2 : ‖Work.PARIMPL2.w0 P p‖ ^ 2 ≤ 2 * Rw ^ 2 := by
        have h4 : 9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw ≤
            9 / 8 + lkHb H SaD ρκ a₃ Rw := by linarith [hHwdom]
        have h6 : ‖Work.PARIMPL2.w0 P p‖ ≤ Rw + 9 / 8 + lkHw H SaD ρκ X₁ W J₀ Xlo Rw := by
          have h7 : ‖Work.PARIMPL2.w0 P p‖ ≤ |(Work.PARIMPL2.w0 P p).re| +
              |(Work.PARIMPL2.w0 P p).im| := Complex.norm_le_abs_re_add_abs_im _
          rw [abs_of_pos hpos] at h7
          linarith [h7, hjsov, hjsim]
        have h6' : ‖Work.PARIMPL2.w0 P p‖ ≤ Rw + 9 / 8 + lkHb H SaD ρκ a₃ Rw := by linarith
        calc ‖Work.PARIMPL2.w0 P p‖ ^ 2 ≤ (Rw + 9 / 8 + lkHb H SaD ρκ a₃ Rw) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h6' 2
          _ ≤ 2 * Rw ^ 2 := hRwsq
      have h8 : Rw ≤ ‖Work.PARIMPL2.w0 P p‖ := by
        have h9 := Complex.re_le_norm (Work.PARIMPL2.w0 P p)
        linarith
      have hw0pne : Work.PARIMPL2.w0 P p ≠ 0 := by
        rw [Work.PARIMPL2.w0]
        exact div_ne_zero (neg_ne_zero.mpr (P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)))
          (sub_ne_zero.mpr hpne)
      have hw0p2 : 0 < ‖Work.PARIMPL2.w0 P p‖ ^ 2 := pow_pos (norm_pos_iff.mpr hw0pne) 2
      rw [div_le_div_iff₀ hRwpos hw0p2]
      nlinarith [h2, h8, hpos, hRwpos]
    have h2' : -(1 / 2) / Rw = -(1 / (2 * Rw)) := by field_simp <;> ring
    have h4' : εch ≤ 1 / (4 * Rw) := by rw [hεchdef]; exact min_le_right _ _
    have h54 : 1 / (4 * Rw) < 1 / (2 * Rw) := by
      rw [div_lt_div_iff₀ (by linarith : (0 : ℝ) < 4 * Rw) (by linarith : (0 : ℝ) < 2 * Rw)]
      linarith
    have h6 : (Work.PARIMPL.chartZeta P c p').re ≤ (Work.PARIMPL.chartZeta P c p').re -
        (Work.PARIMPL.chartZeta P c₀ p).re + (Work.PARIMPL.chartZeta P c₀ p).re := by
      rw [sub_add_cancel]
    have h7 : (Work.PARIMPL.chartZeta P c p').re - (Work.PARIMPL.chartZeta P c₀ p).re ≤
        εch := by
      have h := Complex.re_le_norm (Work.PARIMPL.chartZeta P c p' - Work.PARIMPL.chartZeta P c₀ p)
      rw [Complex.sub_re] at h
      exact le_trans h hchart'
    rw [hre0] at h6
    rw [h2'] at h1
    linarith [h6, h7, h1, h4', h54]
  have hζnorm : ‖Work.PARIMPL.chartZeta P c p'‖ ≤ 4 / lkRt cre Rw := by
    have hchart' := hchart c ⟨hcNm, hbch⟩ p hpWin p' (le_trans hp'dist (min_le_right _ _))
    have hz : Work.PARIMPL.chartZeta P c₀ p = -1 / Work.PARIMPL2.w0 P p := by
      have hs0 : P.s c₀ ≠ 0 := P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)
      have hp0 : p - d.z₁ ≠ 0 := sub_ne_zero.mpr hpne
      rw [Work.PARIMPL.chartZeta, P.m₀, Work.PARIMPL2.w0]
      field_simp <;> ring
    have h1 : ‖Work.PARIMPL.chartZeta P c₀ p‖ = 1 / ‖Work.PARIMPL2.w0 P p‖ := by
      rw [hz, norm_div, norm_neg, norm_one]
    have h2 : 1 / ‖Work.PARIMPL2.w0 P p‖ ≤ 1 / Rw := by
      apply div_le_div_of_nonneg_left (by norm_num) hRwpos
      have h9 := Complex.re_le_norm (Work.PARIMPL2.w0 P p)
      linarith
    have h3 : ‖Work.PARIMPL.chartZeta P c p'‖ ≤ εch + 1 / Rw := by
      calc ‖Work.PARIMPL.chartZeta P c p'‖ ≤ ‖Work.PARIMPL.chartZeta P c p' -
            Work.PARIMPL.chartZeta P c₀ p‖ + ‖Work.PARIMPL.chartZeta P c₀ p‖ := by
            have htri := norm_le_insert' (Work.PARIMPL.chartZeta P c p')
              (Work.PARIMPL.chartZeta P c₀ p)
            linarith
        _ ≤ εch + 1 / Rw := by
            have hcb : ‖Work.PARIMPL.chartZeta P c₀ p‖ ≤ 1 / Rw := by rw [h1]; exact h2
            linarith
    have h4 : εch ≤ 1 / (4 * Rw) := by rw [hεchdef]; exact min_le_right _ _
    have h5 : 1 / Rw + 1 / (4 * Rw) ≤ 4 / lkRt cre Rw := by
      have hRw40 : 0 < 4 * Rw := by linarith
      have h4 : 1 / Rw + 1 / (4 * Rw) = 5 / (4 * Rw) := by
        field_simp
        ring
      rw [h4, div_le_div_iff₀ hRw40 hRTpos]
      nlinarith [hRwRt16b]
    linarith
  -- the transit
  obtain ⟨k, hq1, hq2, hq3, hq4⟩ := htrans c ⟨hcNm, hbt⟩ p' hUin_re hUin_im hζre hζnorm
  set q' : ℂ := (Ft c)^[k] p' with hq'def
  have hqIm : |(Work.PARIMPL.approxU P c q').im| ≤ Hout := by
    have hsub : (Work.PARIMPL.approxU P c q' -
        (Work.PARIMPL.approxUin P c p' - (k : ℂ))).im =
        (Work.PARIMPL.approxU P c q').im - (Work.PARIMPL.approxUin P c p').im := by
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.natCast_im, sub_zero]
    have h1 : |(Work.PARIMPL.approxU P c q').im - (Work.PARIMPL.approxUin P c p').im| ≤
        Ct / lkRt cre Rw := by
      rw [← hsub]
      exact le_trans (Complex.abs_im_le_norm _) hq4
    have h2 : Ct / lkRt cre Rw ≤ 1 := by
      rw [div_le_one hRTpos]
      linarith [hCtle, A.K_nonneg]
    rw [abs_le] at h1
    obtain ⟨hUin_im_lo, hUin_im_hi⟩ := abs_le.mp hUin_im
    have h3 : Hout = Ht + 1 := by rw [hHoutdef]
    rw [h3, hHtdef, hHindef, hSadef]
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, hUin_im_lo, hUin_im_hi]
  -- the exit estimates
  have hqIm8 : |(Work.PARIMPL.approxU P c q').im| ≤ 8 * (Hout + 1) := by linarith [hqIm]
  have hzeta_lo_q : 1 / (4 * lkRt cre Rw) ≤ ‖Work.PARIMPL.chartZeta P c q'‖ :=
    hexit' c ⟨hcNm, hbl⟩ q' hq3 hq2 hq1 hqIm8
  have hqne : q' ≠ d.z₁ := by
    intro h
    have h1 : ‖Work.PARIMPL.chartZeta P c d.z₁‖ ≤ 1 / (8 * lkRt cre Rw) := hz1spec c ⟨hcNm, hbz1⟩
    have hlt : 1 / (8 * lkRt cre Rw) < 1 / (4 * lkRt cre Rw) := by
      rw [div_lt_div_iff₀ (by linarith : (0 : ℝ) < 8 * lkRt cre Rw)
        (by linarith : (0 : ℝ) < 4 * lkRt cre Rw)]
      linarith
    rw [h] at hzeta_lo_q
    linarith [h1, hzeta_lo_q, hlt]
  have hwout'' := hwout' c ⟨hcNm, hbo⟩ q' hqne hq3 hq2 hq1 hqIm
  obtain ⟨hwout_lo, hwout_bd⟩ := hwout''
  -- `‖w0 q'‖ ≥ 1`
  have hw0q1 : 1 ≤ ‖Work.PARIMPL2.w0 P q'‖ := by
    have h1 : Work.PARIMPL.chartZeta P c q' = (q' - P.m c) / P.s c := by
      simp [Work.PARIMPL.chartZeta]
    have h2 : ‖q' - P.m c‖ ≤ (4 / lkRt cre Rw) * ‖P.s c‖ := by
      rw [h1, norm_div] at hq3
      rw [div_le_iff₀ (by rw [norm_pos_iff]; exact P.s_ne c (P.Nm_subset_ball hcNm))] at hq3
      linarith [hq3]
    have h3 := hparspec c ⟨hcNm, hbz1⟩
    have h4 : ‖q' - d.z₁‖ ≤ ‖P.s c₀‖ := by
      have h5 : ‖q' - d.z₁‖ ≤ ‖q' - P.m c‖ + ‖P.m c - d.z₁‖ := by
        have h6 : q' - d.z₁ = (q' - P.m c) + (P.m c - d.z₁) := by ring
        rw [h6]
        exact norm_add_le _ _
      have h7 : (4 / lkRt cre Rw) * ‖P.s c‖ ≤ ‖P.s c₀‖ / 2 := by
        have h8 : (4 / lkRt cre Rw) * ‖P.s c‖ ≤ (4 / lkRt cre Rw) * (2 * ‖P.s c₀‖) :=
          mul_le_mul_of_nonneg_left h3.2 (by positivity)
        have hb : 4 / lkRt cre Rw ≤ 1 / 4 := by
          rw [div_le_iff₀ hRTpos]
          linarith [hRw16]
        have h10 : (4 / lkRt cre Rw) * (2 * ‖P.s c₀‖) ≤ ‖P.s c₀‖ / 2 := by
          calc (4 / lkRt cre Rw) * (2 * ‖P.s c₀‖) ≤ (1 / 4) * (2 * ‖P.s c₀‖) :=
                mul_le_mul_of_nonneg_right hb (by positivity)
            _ = ‖P.s c₀‖ / 2 := by ring
        linarith
      linarith [h5, h2, h7, h3.1]
    have h11 : Work.PARIMPL2.w0 P q' = -P.s c₀ / (q' - d.z₁) := rfl
    rw [h11, norm_div, norm_neg]
    have hq'z1 : 0 < ‖q' - d.z₁‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr hqne
    rw [le_div_iff₀ hq'z1]
    simpa using h4
  -- the exit region estimates
  have hRep_core : ‖Work.PARIMPL.approxU P c q' +
      Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P q')‖ ≤ εo := hwout_bd
  have hUq_bd : ‖Work.PARIMPL.approxU P c q'‖ ≤ lkRt cre Rw + 2 + Hout := by
    have h1 : (Work.PARIMPL.approxU P c q').re ≤ lkRt cre Rw + 2 := hq1.2
    have h2 : (Work.PARIMPL.approxU P c q').re ≥ lkRt cre Rw := hq1.1
    have h3 := Complex.norm_le_abs_re_add_abs_im (Work.PARIMPL.approxU P c q')
    rw [abs_of_nonneg (by linarith)] at h3
    linarith [h3, hqIm, abs_of_nonneg (by linarith : (0:ℝ) ≤ (Work.PARIMPL.approxU P c q').re)]
  have hexit_geom := Work.PARIMPL2.LavaursA.exit_region P (R := lkRt cre Rw) (H := Hout) (ε := εo)
    (M := lkMf ρκ C₅ cre Rw) hRTpos hHout0 hεo0 (by rw [lkMf]; exact le_max_left _ _) hw0q1
    (by
      intro t ht hle
      have h := Work.PARIMPL2.LavaursA.bound_le_add_mul_log_explicit (c := ‖P.κ c₀‖)
        (D := lkRt cre Rw + C₅) hρκnn t ht
      have h2 : lkRt cre Rw + 2 + Hout + εo + ‖P.κ c₀‖ * Real.pi = lkRt cre Rw + C₅ := by
        rw [hC₅def]; ring
      rw [h2] at hle
      rw [hρκdef]
      simp only [lkMf]
      exact h hle)
    (by
      calc ‖Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P q')‖
          = ‖-(Work.PARIMPL.approxU P c q') + (Work.PARIMPL.approxU P c q' +
            Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P q'))‖ := by
            congr 1
            ring
        _ ≤ ‖Work.PARIMPL.approxU P c q'‖ + εo := by
            refine norm_add_le _ _ |>.trans ?_
            rw [norm_neg]
            linarith [hRep_core]
        _ ≤ lkRt cre Rw + 2 + Hout + εo := by linarith [hUq_bd])
    (by
      have h := Complex.abs_re_le_norm (Work.PARIMPL.approxU P c q' +
        Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P q'))
      rw [abs_le] at h
      simp only [Complex.add_re] at h
      linarith [h.1, hRep_core, hq1.2])
    (by
      have h := Complex.re_le_norm (Work.PARIMPL.approxU P c q' +
        Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P q'))
      have h2 : (Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P q')).re ≤
          -(Work.PARIMPL.approxU P c q').re + εo := by
        simp only [Complex.add_re] at h
        linarith [h, hRep_core]
      linarith [h2, hq1.1])
    (by
      have h := Complex.abs_im_le_norm (Work.PARIMPL.approxU P c q' +
        Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P q'))
      rw [abs_le] at h
      simp only [Complex.add_im] at h
      rw [abs_le]
      constructor <;> linarith [h.1, h.2, hRep_core, le_abs_self (Work.PARIMPL.approxU P c q').im,
        neg_le_abs (Work.PARIMPL.approxU P c q').im, hqIm])
  obtain ⟨hEx1, hEx2⟩ := hexit_geom
  -- the level of the exit point and the repelling normalisation
  have hEx1' : |(Work.PARIMPL2.w0 P q').re + lkRt cre Rw| ≤ lkEf ρκ εo C₅ cre Rw := by
    have h := hEx1
    rw [← hρκdef] at h
    rw [lkEf]
    exact h
  have hEx2' : |(Work.PARIMPL2.w0 P q').im| ≤ lkHpf ρκ εo Hout C₅ cre Rw := by
    have h := hEx2
    rw [← hρκdef] at h
    rw [lkHpf]
    exact h
  obtain ⟨hEx1a, hEx1b⟩ := abs_le.mp hEx1'
  have hw0qre : -(Work.PARIMPL2.w0 P q').re ≤ lkRt cre Rw + lkEf ρκ εo C₅ cre Rw := by linarith
  have hw0qre' : lkRt cre Rw - lkEf ρκ εo C₅ cre Rw ≤ -(Work.PARIMPL2.w0 P q').re := by linarith
  have hHpq : |(Work.PARIMPL2.w0 P q').im| ≤ lkHpf ρκ εo Hout C₅ cre Rw := hEx2'
  -- the repelling normalisation at the exit point
  have hEfRt2 : lkEf ρκ εo C₅ cre Rw + 8 * (lkHpf ρκ εo Hout C₅ cre Rw + 1) + 2 ≤ lkRt cre Rw := by
    linarith [hEfdom, hHpfdom, hRwEf]
  have hNrepRT : Nrep ≤ -(Work.PARIMPL2.w0 P q').re := by
    linarith [hNrepEf, hEfdom, hw0qre']
  have hHPFrt : 8 * (lkHpf ρκ εo Hout C₅ cre Rw + 1) ≤ -(Work.PARIMPL2.w0 P q').re := by
    linarith [hEfdom, hHpfdom, hRwEf, hw0qre']
  have hWout : q' ∈ Work.PARIMPL2.WoutG P (-(Work.PARIMPL2.w0 P q').re)
      (lkHpf ρκ εo Hout C₅ cre Rw) := by
    refine ⟨hqne, ⟨?_, hHpq⟩⟩
    exact ⟨by linarith, by linarith⟩
  obtain ⟨uq, huq1, huq2, huq3⟩ := hrep (-(Work.PARIMPL2.w0 P q').re) hNrepRT
    (lkHpf ρκ εo Hout C₅ cre Rw) hHPFrt q' hWout
  have hErepQ : ‖uq - (Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P q') + sr)‖ ≤
      lkErep Krep ρκ εo Hout C₅ cre Rw := by
    have hRp_pos : 0 < -(Work.PARIMPL2.w0 P q').re := by linarith [hw0qre', hEfRt2]
    have hden_pos : 0 < lkRt cre Rw - lkEf ρκ εo C₅ cre Rw := by linarith [hEfRt2]
    have h6 : 0 ≤ 1 + lkHpf ρκ εo Hout C₅ cre Rw := by
      have h6' : 0 ≤ lkHpf ρκ εo Hout C₅ cre Rw := by
        rw [lkHpf]
        have hMf1 : 1 ≤ lkMf ρκ C₅ cre Rw := le_max_left _ _
        have hl : 0 ≤ Real.log (lkMf ρκ C₅ cre Rw) := Real.log_nonneg hMf1
        nlinarith [hHout0, hεo0, hρκnn, hl, Real.pi_pos]
      linarith
    have hnum : Krep * (1 + lkHpf ρκ εo Hout C₅ cre Rw) *
          (1 + Real.log (-(Work.PARIMPL2.w0 P q').re)) ≤
        Krep * (1 + lkHpf ρκ εo Hout C₅ cre Rw) *
          (1 + Real.log (lkRt cre Rw + lkEf ρκ εo C₅ cre Rw)) := by
      have h7 : Real.log (-(Work.PARIMPL2.w0 P q').re) ≤
          Real.log (lkRt cre Rw + lkEf ρκ εo C₅ cre Rw) :=
        Real.log_le_log hRp_pos (by linarith [hw0qre])
      exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hKr h6)
    have hc : 0 ≤ Krep * (1 + lkHpf ρκ εo Hout C₅ cre Rw) *
        (1 + Real.log (lkRt cre Rw + lkEf ρκ εo C₅ cre Rw)) := by
      have h7 : 0 ≤ Real.log (lkRt cre Rw + lkEf ρκ εo C₅ cre Rw) :=
        Real.log_nonneg (by linarith [hEfRt2])
      exact mul_nonneg (mul_nonneg hKr h6) (by linarith)
    refine le_trans huq3 ?_
    simp only [lkErep]
    exact div_le_div₀ hc hnum hden_pos hw0qre'
  -- the suffix
  set T : ℂ := ((Real.pi / P.lam c : ℝ) : ℂ) with hTdef
  have hu_eq : (((fl.φa (Work.PARIMPL.entryPt P nIn c₀)).re - Real.pi / P.lam c : ℝ) : ℂ) + θc -
      (nIn : ℂ) - (((fl.φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ) : ℝ) : ℂ) +
      (n : ℂ) + fl.φa y = θc + (n : ℂ) - T + fl.φa y := by
    rw [hTdef]
    push_cast
    ring
  have hu1c : (-Xo) ≤ (θc + (n : ℂ) - T + fl.φa y).re := by
    rw [← hu_eq] at ⊢
    exact hu1
  have hu2c : (θc + (n : ℂ) - T + fl.φa y).re < -1 := by
    rw [← hu_eq] at ⊢
    exact hu2
  have hu1r : -Xo - θc.re + Real.pi / P.lam c - (fl.φa y).re ≤ (n : ℝ) := by
    have h2 : (θc + (n : ℂ) - T + fl.φa y).re = θc.re + (n : ℝ) - Real.pi / P.lam c +
        (fl.φa y).re := by
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.natCast_re, hTdef]
    have h3 := hu1c
    rw [h2] at h3
    linarith
  have hkub : (k : ℝ) ≤ Real.pi / P.lam c - 2 * lkRt cre Rw + Ct / lkRt cre Rw := by
    have h4 : (Work.PARIMPL.approxU P c q').re - (Work.PARIMPL.approxUin P c p').re + (k : ℝ)
        ≤ Ct / lkRt cre Rw := by
      have h6 := Complex.abs_re_le_norm (Work.PARIMPL.approxU P c q' -
        (Work.PARIMPL.approxUin P c p' - (k : ℂ)))
      have h7 : (Work.PARIMPL.approxU P c q' -
          (Work.PARIMPL.approxUin P c p' - (k : ℂ))).re =
          (Work.PARIMPL.approxU P c q').re - (Work.PARIMPL.approxUin P c p').re + (k : ℝ) := by
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.natCast_re]
        ring
      rw [h7] at h6
      have h8 : (Work.PARIMPL.approxU P c q').re - (Work.PARIMPL.approxUin P c p').re + (k : ℝ) ≤
          ‖Work.PARIMPL.approxU P c q' - (Work.PARIMPL.approxUin P c p' - (k : ℂ))‖ :=
        le_trans (le_abs_self _) h6
      linarith [h8, hq4]
    linarith [h4, hq1.1, hUin_re.2]
  have hnge : j + k ≤ n := by
    have h8 : (j : ℝ) ≤ (lkJmax J₀ Xlo Rw : ℝ) := by exact_mod_cast hjJM
    have h9 : (fl.φa y).re ≤ X₁ + W := hY₂
    have hreal : ((j + k : ℕ) : ℝ) ≤ (n : ℝ) := by
      have hjk : ((j + k : ℕ) : ℝ) = (j : ℝ) + (k : ℝ) := by push_cast; ring
      rw [hjk]
      linarith [hu1r, hkub, h8, hRwJmax, h9]
    exact_mod_cast hreal
  set m : ℕ := n - (j + k) with hmdef
  have hn' : j + k + m = n := by
    rw [hmdef]
    omega
  have hmn : m + (j + k) = n := by omega
  have hiter1 : (Ft c)^[j + k] y' = q' := by
    rw [Nat.add_comm j k, Function.iterate_add_apply, ← hp'def, ← hq'def]
  have hiter : (Ft c)^[n] y' = (Ft c)^[m] q' := by
    calc (Ft c)^[n] y' = (Ft c)^[m + (j + k)] y' := by rw [← hmn]
      _ = (Ft c)^[m] ((Ft c)^[j + k] y') := Function.iterate_add_apply (Ft c) m (j + k) y'
      _ = (Ft c)^[m] q' := by rw [hiter1]
  -- the level identity
  set X : ℂ := Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P q') + sr with hXdef
  set Y : ℂ := -(Work.PARIMPL.approxU P c q') + sr with hYdef
  set Z : ℂ := -(Work.PARIMPL.approxUin P c p' - (k : ℂ)) + sr with hZdef
  set Wl : ℂ := -(T - Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) - (k : ℂ)) + sr
    with hWldef
  set V : ℂ := -(T - (fl.φa p - A.sa) - (k : ℂ)) + sr with hVdef
  have hB1 : ‖uq - X‖ ≤ lkErep Krep ρκ εo Hout C₅ cre Rw := by
    rw [hXdef]
    exact hErepQ
  have hB2 : ‖X - Y‖ ≤ εo := by
    have h1 : X - Y = Work.PARIMPL.approxU P c q' +
        Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P q') := by
      rw [hXdef, hYdef]; ring
    rw [h1]; exact hRep_core
  have hB3 : ‖Y - Z‖ ≤ Ct / lkRt cre Rw := by
    have h1 : Y - Z = -(Work.PARIMPL.approxU P c q' -
        (Work.PARIMPL.approxUin P c p' - (k : ℂ))) := by
      rw [hYdef, hZdef]; ring
    rw [h1, norm_neg]; exact hq4
  have hB4 : ‖Z - Wl‖ ≤ εw := by
    have h1 : Z - Wl = -(Work.PARIMPL.approxUin P c p' -
        (T - Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p))) := by
      rw [hZdef, hWldef]; ring
    rw [h1, norm_neg]; exact hwin'
  have hB5 : ‖Wl - V‖ ≤ A.K / Rw := by
    have h1 : Wl - V = Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) -
        fl.φa p + A.sa := by
      rw [hWldef, hVdef]; ring
    have h2 : Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) - fl.φa p + A.sa =
        -((fl.φa p - (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P p) + A.sa))) := by
      ring
    rw [h1, h2, norm_neg]
    refine le_trans hasymp_p ?_
    have hjs' : Rw ≤ (Work.FlowerGlue2.w0 P p).re := by
      simpa only [Work.FlowerGlue2.w0, Work.PARIMPL2.w0] using hjs
    exact div_le_div_of_nonneg_left A.K_nonneg hRwpos hjs'
  have hB6 : V + (m : ℂ) - (θc + (n : ℂ) - T + fl.φa y) = 0 := by
    rw [hVdef]
    have hphi : fl.φa p = fl.φa y + (j : ℂ) := phi_shift_iter P fl A j hPa
    have hn'' : (n : ℂ) = (j : ℂ) + (k : ℂ) + (m : ℂ) := by
      rw [← hn']; push_cast; ring
    rw [hphi, hn'', hθcdef]
    ring
  have htel : uq + (m : ℂ) - (θc + (n : ℂ) - T + fl.φa y) =
      (uq - X) + (X - Y) + (Y - Z) + (Z - Wl) + (Wl - V) +
        (V + (m : ℂ) - (θc + (n : ℂ) - T + fl.φa y)) := by ring
  have hfinal : ‖uq + (m : ℂ) - (θc + (n : ℂ) - T + fl.φa y)‖ ≤ δΨ := by
    have htri : ‖(uq - X) + (X - Y) + (Y - Z) + (Z - Wl) + (Wl - V) +
        (V + (m : ℂ) - (θc + (n : ℂ) - T + fl.φa y))‖ ≤
        ‖uq - X‖ + ‖X - Y‖ + ‖Y - Z‖ + ‖Z - Wl‖ + ‖Wl - V‖ +
          ‖V + (m : ℂ) - (θc + (n : ℂ) - T + fl.φa y)‖ := by
      have h2 := norm_add_le ((uq - X) + (X - Y) + (Y - Z) + (Z - Wl) + (Wl - V))
        (V + (m : ℂ) - (θc + (n : ℂ) - T + fl.φa y))
      have h3 := norm_add_le ((uq - X) + (X - Y) + (Y - Z) + (Z - Wl)) (Wl - V)
      have h4 := norm_add_le ((uq - X) + (X - Y) + (Y - Z)) (Z - Wl)
      have h5 := norm_add_le ((uq - X) + (X - Y)) (Y - Z)
      have h6 := norm_add_le (uq - X) (X - Y)
      linarith
    rw [← htel, hB6, norm_zero, add_zero] at htri
    have h7 : lkErep Krep ρκ εo Hout C₅ cre Rw ≤ lkEreph Cbig Rw := hErepdom
    have h8 : lkEreph Cbig Rw + Ct / lkRt cre Rw + (A.K + 1) / Rw ≤ δΨ / 2 := hRwErr
    have h9 : A.K / Rw ≤ (A.K + 1) / Rw :=
      div_le_div_of_nonneg_right (by linarith) hRwpos.le
    have h10 : εw ≤ δΨ / 8 := by rw [hεwdef]; exact min_le_right _ _
    have h11 : εo ≤ δΨ / 8 := by rw [hεodef]; exact min_le_right _ _
    linarith [htri, hB1, hB2, hB3, hB4, hB5, h7, h8, h9, h10, h11]
  have hq'K : q' ∈ Kq := by
    rw [hKqdef, Metric.mem_closedBall, dist_zero_right]
    have h1 := hparspec c ⟨hcNm, hbz1⟩
    have h2 : ‖q' - d.z₁‖ ≤ ‖P.s c₀‖ := by
      have h3 : ‖q' - d.z₁‖ ≤ ‖q' - P.m c‖ + ‖P.m c - d.z₁‖ := by
        have h4 : q' - d.z₁ = (q' - P.m c) + (P.m c - d.z₁) := by ring
        rw [h4]; exact norm_add_le _ _
      have h5 : Work.PARIMPL.chartZeta P c q' = (q' - P.m c) / P.s c := by
        simp [Work.PARIMPL.chartZeta]
      have h6 : ‖q' - P.m c‖ ≤ (4 / lkRt cre Rw) * ‖P.s c‖ := by
        rw [h5, norm_div] at hq3
        rw [div_le_iff₀ (by rw [norm_pos_iff]; exact P.s_ne c (P.Nm_subset_ball hcNm))] at hq3
        linarith [hq3]
      have h7 : (4 / lkRt cre Rw) * ‖P.s c‖ ≤ ‖P.s c₀‖ / 2 := by
        have h8 : ‖P.s c‖ ≤ 2 * ‖P.s c₀‖ := h1.2
        have hb : 4 / lkRt cre Rw ≤ 1 / 4 := by
          rw [div_le_iff₀ hRTpos]
          linarith [hRw16]
        calc (4 / lkRt cre Rw) * ‖P.s c‖ ≤ (4 / lkRt cre Rw) * (2 * ‖P.s c₀‖) :=
              mul_le_mul_of_nonneg_left h8 (by positivity)
          _ ≤ (1 / 4) * (2 * ‖P.s c₀‖) :=
              mul_le_mul_of_nonneg_right hb (by positivity)
          _ = ‖P.s c₀‖ / 2 := by ring
      linarith [h3, h6, h7, h1.1]
    have htri : ‖q'‖ ≤ ‖q' - d.z₁‖ + ‖d.z₁‖ := by
      have h := norm_add_le (q' - d.z₁) d.z₁
      have h4 : (q' - d.z₁) + d.z₁ = q' := by ring
      rwa [h4] at h
    linarith [h2, htri, le_max_right Rpa (‖d.z₁‖ + ‖P.s c₀‖)]
  have hsufM : m ≤ Nat.ceil (2 * lkRt cre Rw + 4 + |X₁| + |θc.re| + Ct / lkRt cre Rw) := by
    have h2 : (θc + (n : ℂ) - T + fl.φa y).re = θc.re + (n : ℝ) - Real.pi / P.lam c +
        (fl.φa y).re := by
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.natCast_re, hTdef]
    have hu2d : θc.re + (n : ℝ) - Real.pi / P.lam c + (fl.φa y).re < -1 := by
      rw [← h2] at ⊢
      exact hu2c
    have hn1 : (n : ℝ) < -1 - θc.re + Real.pi / P.lam c - (fl.φa y).re := by linarith
    have hk1 : Real.pi / P.lam c - 2 * lkRt cre Rw - 4 - Ct / lkRt cre Rw ≤ (k : ℝ) := by
      have herr : |(Work.PARIMPL.approxU P c q').re - (Work.PARIMPL.approxUin P c p').re + (k : ℝ)| ≤
          Ct / lkRt cre Rw := by
        have h6 := Complex.abs_re_le_norm (Work.PARIMPL.approxU P c q' -
          (Work.PARIMPL.approxUin P c p' - (k : ℂ)))
        have h7 : (Work.PARIMPL.approxU P c q' -
            (Work.PARIMPL.approxUin P c p' - (k : ℂ))).re =
            (Work.PARIMPL.approxU P c q').re - (Work.PARIMPL.approxUin P c p').re + (k : ℝ) := by
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.natCast_re]
          ring
        rw [h7] at h6
        rw [abs_le] at h6
        rw [abs_le]
        exact ⟨by linarith [h6.1, hq4], by linarith [h6.2, hq4]⟩
      rw [abs_le] at herr
      linarith [herr.1, hq1.1, hq1.2, hUin_re.1, hUin_re.2]
    have hmn' : (m : ℝ) = (n : ℝ) - ((j : ℝ) + (k : ℝ)) := by
      have h3 : ((m + (j + k) : ℕ) : ℝ) = (n : ℝ) := by rw [hmn]
      push_cast at h3
      linarith
    have hA2 : -θc.re ≤ |θc.re| := neg_le_abs _
    have hB2 : -X₁ ≤ |X₁| := neg_le_abs _
    have hjk0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hA : (m : ℝ) ≤ 2 * lkRt cre Rw + 4 + |X₁| + |θc.re| + Ct / lkRt cre Rw := by
      rw [hmn']
      linarith [hn1, hk1, hA2, hB2, hjk0, hY₁]
    exact Nat.cast_le.mp (le_trans hA (Nat.le_ceil _))
  have hsuf1 : ‖(Ft c)^[m] q' - (Ft c₀)^[m] q'‖ ≤ η / 2 :=
    hsuf c hcsuf m (Nat.cast_le.mp (le_trans hsufM (Nat.le_ceil _))) q' hq'K
  have hsuf2 : (Ft c₀)^[m] q' = fl.Ψ (uq + (m : ℂ)) := by
    rw [← huq2]
    exact (psi_shift_iter fl m uq).symm
  have hsuf3 : ‖fl.Ψ (uq + (m : ℂ)) - fl.Ψ (θc + (n : ℂ) - T + fl.φa y)‖ ≤ η / 2 := by
    have hu_im : |(θc + (n : ℂ) - T + fl.φa y).im| ≤ |θc.im| + H + 1 := by
      have h1 : (θc + (n : ℂ) - T + fl.φa y).im = θc.im + (fl.φa y).im := by
        simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.natCast_im, sub_zero,
          add_zero, hTdef]
      rw [h1]
      have := abs_add_le θc.im (fl.φa y).im
      linarith [hY₃]
    have hu_re1 : (θc + (n : ℂ) - T + fl.φa y).re ≥ -Xo := by
      have h1 : (θc + (n : ℂ) - T + fl.φa y).re = θc.re + (n : ℝ) - Real.pi / P.lam c +
          (fl.φa y).re := by
        simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.natCast_re, hTdef]
      rw [h1] at hu1c
      linarith
    have hu_re2 : (θc + (n : ℂ) - T + fl.φa y).re < 0 := by
      have h1 : (θc + (n : ℂ) - T + fl.φa y).re = θc.re + (n : ℝ) - Real.pi / P.lam c +
          (fl.φa y).re := by
        simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.natCast_re, hTdef]
      rw [h1] at hu2c
      linarith
    refine hδΨ₀ (uq + (m : ℂ)) (θc + (n : ℂ) - T + fl.φa y) ?_ ?_ ?_ ?_ ?_
    · obtain ⟨h1a, h1b⟩ := abs_le.mp
        (Complex.abs_re_le_norm (uq + (m : ℂ) - (θc + (n : ℂ) - T + fl.φa y)))
      rw [Complex.sub_re] at h1a h1b
      rw [Set.mem_Icc]
      constructor <;> linarith [h1a, h1b, hfinal, hδΨle1, hu_re1, hu2c]
    · obtain ⟨h1a, h1b⟩ := abs_le.mp
        (Complex.abs_im_le_norm (uq + (m : ℂ) - (θc + (n : ℂ) - T + fl.φa y)))
      rw [Complex.sub_im] at h1a h1b
      obtain ⟨him_lo, him_hi⟩ := abs_le.mp hu_im
      rw [abs_le]
      constructor <;> linarith [h1a, h1b, hfinal, hδΨle1, him_lo, him_hi]
    · rw [Set.mem_Icc]; exact ⟨by linarith, hu_re2.le⟩
    · exact le_trans hu_im (by linarith)
    · exact le_trans hfinal hδΨle₀
  have hgoal1 : ‖(Ft c)^[n] y' - fl.Ψ (θc + (n : ℂ) - T + fl.φa y)‖ ≤ η := by
    rw [hiter]
    calc ‖(Ft c)^[m] q' - fl.Ψ (θc + (n : ℂ) - T + fl.φa y)‖
        = ‖((Ft c)^[m] q' - (Ft c₀)^[m] q') +
          (fl.Ψ (uq + (m : ℂ)) - fl.Ψ (θc + (n : ℂ) - T + fl.φa y))‖ := by
          rw [hsuf2]
          congr 1
          ring
      _ ≤ ‖(Ft c)^[m] q' - (Ft c₀)^[m] q'‖ +
          ‖fl.Ψ (uq + (m : ℂ)) - fl.Ψ (θc + (n : ℂ) - T + fl.φa y)‖ := norm_add_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add hsuf1 hsuf3
      _ = η := by ring
  have hgoal2 : ‖(Ft c)^[n] y' - fl.Ψ u‖ ≤ η := by
    have h := hgoal1
    rw [← hu_eq] at h
    exact h
  exact hgoal2

end Work.PARIMPL2.Lavaurs
