/-
Copyright: work module for the Elgindi finite-time singularity project.

# `cmode m F t = o(t^{3/2})` at `t = 0`

`Work.FTS.PhiStar.Series.cmode m F z` is the `e_m`-coefficient of the angular slice `F z ·`
in the self-adjoint weight `cos θ dθ`.  For a source `F` that is `C^∞` on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen F`) and honestly in the weighted space `ℋ¹`
(`Work.Spaces.HkMem α 1 F`) we prove that the mode coefficient vanishes faster than `t^{3/2}`
at the origin:

  `∀ ε > 0, ∃ δ > 0, ∀ t ∈ (0, δ], |cmode m F t| ≤ ε · t^{3/2}`.

**Route.**  Let `G z = ∫_θ HkIntegrand α 1 F z θ`, so that `G ≥ 0` and `G` is integrable on
`Iz = [0,∞)` (`HkMem α 1 F`).  The four inputs are:

* *(slice mass, `cmode_slice_mass_le`)* for `z > 0`,
  `(∫_θ (F z θ)² sin(2θ)^{-η}) · w z² ≤ G z` — the `i = 0` summand of `HkIntegrand`;
* *(per-mode bound, `eNorm_mul_cmode_sq_le_sliceMass`)*
  `eNorm m · (cmode m F z)² ≤ ∫_θ (F z θ)² sin(2θ)^{-η}`;
* *(small point, `exists_lt_average_witness`)* for `t > 0` some `u ∈ [t/2, t]` has
  `G u · t ≤ 4 ∫_{t/2}^{t} G`, hence `(cmode m F u)² ≤ 4 t³ ∫_{t/2}^{t} G / eNorm m`;
* *(variation, `cmode_variation_le`)* for `0 < y ≤ x`,
  `|cmode m F x - cmode m F y| ≤ K x^{3/2} √(∫_y^x G)`;
  the source is that the `z`-difference quotient is controlled by the `i = 1` summand of
  `HkIntegrand`, whose weight `w z / z` supplies one extra power of `z`.

Combining the last two at `(t, u)` and using `∫_{t/2}^{t} G ≤ ∫_0^t G → 0` gives
`|cmode m F t| ≤ (K + 2) t^{3/2} √(∫_0^t G)`, and `∫_0^t G → 0` as `t → 0⁺` finishes.

This is the `z^{-4}`-weight finiteness input of `Honesty.radGreen_modeEnergy_of_o`
(see `NOTES_bslOp_sol_exists_s4.md` §3, item 6).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one
import Submission.Work.FTS.PhiStar.Honesty.cmode_sq_le_slice
import Submission.Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
import Submission.Work.FTS.PhiStar.Honesty.cmode_slice_mass_le
import Submission.Work.FTS.PhiStar.Honesty.cmode_variation_le
import Submission.Work.FTS.PhiStar.Honesty.exists_lt_average_witness

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## Two elementary numerical lemmas -/

/-- `(t^{3/2})² = t³`, with the exponent `3` written as a *natural* power on the right. -/
private lemma sq_rpow_three_halves {t : ℝ} (ht : 0 ≤ t) :
    (t ^ ((3 : ℝ) / 2)) ^ 2 = t ^ ((3 : ℕ) : ℝ) := by
  rw [← Real.rpow_mul_natCast ht ((3 : ℝ) / 2) 2]
  norm_num

/-- `1 / w u ^ 2 ≤ t ^ 4` for `0 < u ≤ t`, where `w u = (1+u)²/u²`. -/
private lemma one_div_w_sq_le {u t : ℝ} (hu : 0 < u) (hut : u ≤ t) :
    1 / (Work.Spaces.w u) ^ 2 ≤ t ^ 4 := by
  have hu2 : (0 : ℝ) < u ^ 2 := by positivity
  have hw1 : (1 : ℝ) ≤ (1 + u) ^ 2 := by nlinarith [sq_nonneg u]
  have hwpos : 0 < Work.Spaces.w u := by
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hu 2)
  have hw : 1 / u ^ 2 ≤ Work.Spaces.w u := by
    rw [Work.Spaces.w]
    exact div_le_div_of_nonneg_right hw1 (by positivity)
  have h1 : 1 / Work.Spaces.w u ≤ 1 / (1 / u ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hw
  have h2 : 1 / (1 / u ^ 2) = u ^ 2 := by
    rw [one_div_one_div]
  have h3 : (1 / Work.Spaces.w u) ^ 2 ≤ (u ^ 2) ^ 2 := by
    rw [← h2]
    exact pow_le_pow_left₀ (le_of_lt (one_div_pos.mpr hwpos)) h1 2
  have h4 : (u ^ 2) ^ 2 = u ^ 4 := by ring
  have h5 : u ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ hu.le hut 4
  refine le_trans (le_of_eq ?_) (le_trans h3 (le_trans (le_of_eq h4) h5))
  rw [show (1 : ℝ) / (Work.Spaces.w u) ^ 2 = (1 / Work.Spaces.w u) ^ 2 from by
    rw [div_pow, one_pow]]

/-! ## The main theorem -/

theorem cmode_isLittleO_at_zero {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF1 : Work.Spaces.HkMem α 1 F) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |Work.FTS.PhiStar.Series.cmode m F t| ≤ ε * t ^ ((3 : ℝ) / 2) := by
  intro ε hε
  obtain ⟨K, hKpos, hK⟩ := cmode_variation_le m
  -- the mode norm is at least `1`
  have hE1 : 1 ≤ Work.EllipticEst.ModalSolution.eNorm m := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmm : (0 : ℝ) ≤ (m : ℝ) ^ 2 := sq_nonneg _
    rw [Work.EllipticEst.ModalSolution.eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m,
      one_le_div (by positivity : (0 : ℝ) < 4 * (m : ℝ) + 5)]
    nlinarith [hm0, hmm]
  have hEpos : 0 < Work.EllipticEst.ModalSolution.eNorm m := lt_of_lt_of_le one_pos hE1
  -- the integrated `ℋ¹`-integrand
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F z θ with hGdef
  have hHknn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 1 F z θ := by
    intro z θ
    rw [Work.Spaces.HkIntegrand]
    refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs with h
      · exact sq_nonneg _
      · exact le_refl 0
  have hGintIz : MeasureTheory.IntegrableOn G Work.Spaces.Iz := by
    rw [hGdef]
    exact hF1.2
  have hGnnIz : ∀ z ∈ Work.Spaces.Iz, 0 ≤ G z := by
    intro z _
    rw [hGdef]
    exact MeasureTheory.integral_nonneg fun θ => hHknn z θ
  -- one-sided continuity of the primitive of `G` at `0`
  have hGintIcc : MeasureTheory.IntegrableOn G (Set.Icc (0 : ℝ) 1) :=
    hGintIz.mono_set (fun z hz => hz.1)
  have hGintU : MeasureTheory.IntegrableOn G (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hGintIcc
  have hΨc : ContinuousOn (fun b : ℝ => ∫ x in (0 : ℝ)..b, G x) (Set.Icc (0 : ℝ) 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval (f := G) (a := (0 : ℝ)) (b := 1)
      hGintU
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  have hΨcw : ContinuousWithinAt (fun b : ℝ => ∫ x in (0 : ℝ)..b, G x) (Set.Icc (0 : ℝ) 1) 0 :=
    hΨc.continuousWithinAt ⟨le_refl 0, by norm_num⟩
  have hΨtend1 : Filter.Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, G x)
      (𝓝[Set.Icc (0 : ℝ) 1] 0) (𝓝 0) := by
    have h := hΨcw
    rw [ContinuousWithinAt] at h
    simpa using h
  have hle : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝[Set.Icc (0 : ℝ) 1] 0 := by
    rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Ioo (-1) 1, Ioo_mem_nhds (by norm_num) (by norm_num),
      fun y hy => ⟨hy.2.le, hy.1.2.le⟩⟩
  have hΨtend : Filter.Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, G x)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    hΨtend1.mono_left hle
  -- choose the radius
  have hδev : ∀ᶠ b in 𝓝[Set.Ioi (0 : ℝ)] 0,
      ∫ x in (0 : ℝ)..b, G x < (ε / (K + 2)) ^ 2 :=
    hΨtend.eventually (Iio_mem_nhds (show (0 : ℝ) < (ε / (K + 2)) ^ 2 by positivity))
  have hδmem : {b : ℝ | ∫ x in (0 : ℝ)..b, G x < (ε / (K + 2)) ^ 2}
      ∈ 𝓝[Set.Ioi (0 : ℝ)] 0 := hδev
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hδmem
  obtain ⟨U, hUnhds, hUsub⟩ := hδmem
  obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp hUnhds
  set δ : ℝ := min (r / 2) 1 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) one_pos
  have hδU : δ ∈ U := by
    refine hr ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδpos, hδdef]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδc : ∫ x in (0 : ℝ)..δ, G x < (ε / (K + 2)) ^ 2 := hUsub ⟨hδU, hδpos⟩
  have hδnn : 0 ≤ ∫ x in (0 : ℝ)..δ, G x :=
    intervalIntegral.integral_nonneg hδpos.le (fun s hs => hGnnIz s hs.1)
  have hK2pos : 0 < K + 2 := by linarith
  have hδsqrt : Real.sqrt (∫ x in (0 : ℝ)..δ, G x) < ε / (K + 2) := by
    rw [Real.sqrt_lt' (by positivity : (0 : ℝ) < ε / (K + 2))]
    exact hδc
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htd
  -- interval integrability of `G` on the two windows
  have hGintU0t : MeasureTheory.IntegrableOn G (Set.uIcc (0 : ℝ) t) := by
    refine hGintIz.mono_set ?_
    intro z hz
    rw [Set.uIcc_of_le ht.le] at hz
    exact hz.1
  have hGintU0δ : MeasureTheory.IntegrableOn G (Set.uIcc (0 : ℝ) δ) := by
    refine hGintIz.mono_set ?_
    intro z hz
    rw [Set.uIcc_of_le hδpos.le] at hz
    exact hz.1
  have hGintt : IntervalIntegrable G MeasureTheory.volume (0 : ℝ) t :=
    hGintU0t.intervalIntegrable
  have hGintδ : IntervalIntegrable G MeasureTheory.volume (0 : ℝ) δ :=
    hGintU0δ.intervalIntegrable
  have hGaet : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)] G :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => hGnnIz s hs.1.le)
  have hGaeδ : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) δ)] G :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => hGnnIz s hs.1.le)
  have hBw_nn : 0 ≤ ∫ s in (t / 2)..t, G s :=
    intervalIntegral.integral_nonneg (by linarith)
      (fun s hs => hGnnIz s (Set.mem_Ici.mpr (le_trans (by linarith : (0 : ℝ) ≤ t / 2) hs.1)))
  have hΨmono : ∫ x in (0 : ℝ)..t, G x ≤ ∫ x in (0 : ℝ)..δ, G x :=
    intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := δ) (a := (0 : ℝ)) (b := t)
      (le_refl 0) ht.le htd hGaeδ hGintδ
  have hBw_le : ∫ s in (t / 2)..t, G s ≤ ∫ x in (0 : ℝ)..t, G x :=
    intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := t) (a := t / 2) (b := t)
      (by linarith) (by linarith) (le_refl t) hGaet hGintt
  -- the point of the window where `G` is small
  obtain ⟨u, huIcc, huG⟩ := exists_lt_average_witness ht hGintIz hGnnIz
  have hupos : 0 < u := lt_of_lt_of_le (by linarith : (0 : ℝ) < t / 2) huIcc.1
  have hut : u ≤ t := huIcc.2
  -- the slice-mass bound at `u`
  obtain ⟨hAint, hAle, -, -⟩ := cmode_slice_mass_le hsm hF1 hupos
  have hEcm : Work.EllipticEst.ModalSolution.eNorm m * (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, (F u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    eNorm_mul_cmode_sq_le_sliceMass (m := m) (F := F) (z := u) hAint
  have hwupos : 0 < Work.Spaces.w u := by
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hupos 2)
  have hGu_nn : 0 ≤ G u := hGnnIz u (Set.mem_Ici.mpr hupos.le)
  have hEprod : 0 < Work.EllipticEst.ModalSolution.eNorm m * (Work.Spaces.w u) ^ 2 :=
    mul_pos hEpos (pow_pos hwupos 2)
  have h1 : Work.EllipticEst.ModalSolution.eNorm m * (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
        * (Work.Spaces.w u) ^ 2 ≤ G u :=
    le_trans (mul_le_mul_of_nonneg_right hEcm (sq_nonneg _)) hAle
  have hcu2 : (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
      ≤ t ^ 4 * G u / Work.EllipticEst.ModalSolution.eNorm m := by
    have h2 : (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
        ≤ G u / (Work.EllipticEst.ModalSolution.eNorm m * (Work.Spaces.w u) ^ 2) := by
      rw [le_div_iff₀ hEprod]
      rw [show (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
            * (Work.EllipticEst.ModalSolution.eNorm m * (Work.Spaces.w u) ^ 2)
          = Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.cmode m F u) ^ 2 * (Work.Spaces.w u) ^ 2 from by ring]
      exact h1
    have h3 : 1 / (Work.Spaces.w u) ^ 2 ≤ t ^ 4 := one_div_w_sq_le hupos hut
    have h4 : G u / (Work.EllipticEst.ModalSolution.eNorm m * (Work.Spaces.w u) ^ 2)
        = (G u / Work.EllipticEst.ModalSolution.eNorm m) * (1 / (Work.Spaces.w u) ^ 2) := by
      field_simp
    have h5 : t ^ 4 * G u / Work.EllipticEst.ModalSolution.eNorm m
        = (G u / Work.EllipticEst.ModalSolution.eNorm m) * t ^ 4 := by ring
    calc (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
        ≤ G u / (Work.EllipticEst.ModalSolution.eNorm m * (Work.Spaces.w u) ^ 2) := h2
      _ = (G u / Work.EllipticEst.ModalSolution.eNorm m) * (1 / (Work.Spaces.w u) ^ 2) := h4
      _ ≤ (G u / Work.EllipticEst.ModalSolution.eNorm m) * t ^ 4 :=
          mul_le_mul_of_nonneg_left h3 (div_nonneg hGu_nn hEpos.le)
      _ = t ^ 4 * G u / Work.EllipticEst.ModalSolution.eNorm m := h5.symm
  have hGu_le : G u ≤ 4 * (∫ s in (t / 2)..t, G s) / t := by
    rw [le_div_iff₀ ht]
    exact huG
  have hcu4 : (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
      ≤ 4 * t ^ 3 * (∫ s in (t / 2)..t, G s) / Work.EllipticEst.ModalSolution.eNorm m := by
    refine le_trans hcu2 ?_
    refine le_trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hGu_le (by positivity : (0 : ℝ) ≤ t ^ 4)) hEpos.le) ?_
    rw [show t ^ 4 * (4 * (∫ s in (t / 2)..t, G s) / t) / Work.EllipticEst.ModalSolution.eNorm m
          = 4 * t ^ 3 * (∫ s in (t / 2)..t, G s) / Work.EllipticEst.ModalSolution.eNorm m from by
        field_simp]
  have hpow : (2 * t ^ ((3 : ℝ) / 2)) ^ 2 * (∫ s in (t / 2)..t, G s)
      = 4 * t ^ 3 * (∫ s in (t / 2)..t, G s) := by
    rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, ← Real.rpow_natCast t 3,
      ← sq_rpow_three_halves ht.le]
  have hcu4' : (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
      ≤ (2 * t ^ ((3 : ℝ) / 2)) ^ 2 * (∫ s in (t / 2)..t, G s) := by
    rw [hpow]
    refine le_trans hcu4 ?_
    rw [div_le_iff₀ hEpos]
    exact le_mul_of_one_le_right (by positivity) hE1
  have hcu_le : |Work.FTS.PhiStar.Series.cmode m F u|
      ≤ 2 * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x) := by
    have h2 : Real.sqrt ((2 * t ^ ((3 : ℝ) / 2)) ^ 2 * (∫ s in (t / 2)..t, G s))
        = 2 * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ s in (t / 2)..t, G s) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    calc |Work.FTS.PhiStar.Series.cmode m F u|
        = Real.sqrt ((Work.FTS.PhiStar.Series.cmode m F u) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((2 * t ^ ((3 : ℝ) / 2)) ^ 2 * (∫ s in (t / 2)..t, G s)) :=
          Real.sqrt_le_sqrt hcu4'
      _ = 2 * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ s in (t / 2)..t, G s) := h2
      _ ≤ 2 * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBw_le) (by positivity)
  -- the variation bound
  have hmono_u : ∫ s in u..t, G s ≤ ∫ x in (0 : ℝ)..t, G x :=
    intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := t) (a := u) (b := t)
      hupos.le hut (le_refl t) hGaet hGintt
  have hvar : |Work.FTS.PhiStar.Series.cmode m F t - Work.FTS.PhiStar.Series.cmode m F u|
      ≤ K * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x) := by
    refine le_trans (hK α F hsm hF1 hupos hut) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.sqrt_le_sqrt hmono_u
  -- assembly
  calc |Work.FTS.PhiStar.Series.cmode m F t|
      ≤ |Work.FTS.PhiStar.Series.cmode m F t - Work.FTS.PhiStar.Series.cmode m F u|
          + |Work.FTS.PhiStar.Series.cmode m F u| := by
        have h := abs_sub_abs_le_abs_sub (Work.FTS.PhiStar.Series.cmode m F t)
          (Work.FTS.PhiStar.Series.cmode m F u)
        linarith
    _ ≤ K * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x)
          + 2 * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x) := by
        linarith [hvar, hcu_le]
    _ = (K + 2) * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x) := by ring
    _ ≤ (K + 2) * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..δ, G x) := by
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hΨmono)
          (le_of_lt (mul_pos hK2pos (Real.rpow_pos_of_pos ht _)))
    _ ≤ ε * t ^ ((3 : ℝ) / 2) := by
        have h2 : (K + 2) * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..δ, G x)
            < (K + 2) * t ^ ((3 : ℝ) / 2) * (ε / (K + 2)) :=
          mul_lt_mul_of_pos_left hδsqrt
            (mul_pos hK2pos (Real.rpow_pos_of_pos ht _))
        have h3 : (K + 2) * t ^ ((3 : ℝ) / 2) * (ε / (K + 2))
            = ε * t ^ ((3 : ℝ) / 2) := by
          field_simp
        rw [h3] at h2
        exact le_of_lt h2

end Work.FTS.PhiStar.Honesty
