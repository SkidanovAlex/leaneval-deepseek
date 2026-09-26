import Mathlib
import Submission.Work.Asymptotics.Tile.tileLayerDefs
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.TailIntegral
import Submission.Work.Asymptotics.windowIntegral_bound
import Submission.Work.Asymptotics.ae_bound_of_two_regime
import Submission.Work.Asymptotics.exists_bound_iteratedDeriv_tailIntegral_two_regime
import Submission.Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound
import Submission.Work.Asymptotics.layerTrunc_seminorm
import Submission.Work.Asymptotics.layerPieces_smooth
import Submission.Work.Asymptotics.EtailE.Basic
import Submission.Work.Asymptotics.GcuspDefs

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ContDiff

namespace Work.Asymptotics.Tile

/-! ## Geometry: `Im (S • w)` is bounded by `scale w`

The threshold `2 Im (S • w) + 1` of the sharp tile tail is itself bounded by a constant multiple of
`scale w`: indeed `Im (S • w) = Im w / ‖w‖² ≤ 1 / Im w ≤ scale w`. -/
lemma im_S_smul_le_scale (w : UpperHalfPlane) : (ModularGroup.S • w).im ≤ Work.Kernels.scale w := by
  rw [Work.Asymptotics.EtailE.E_im_S]
  have him : 0 < w.im := w.im_pos
  have hsq : w.im ^ 2 ≤ ‖(w : ℂ)‖ ^ 2 := Work.Asymptotics.EtailE.im_sq_le_normSq w
  have h1 : w.im / ‖(w : ℂ)‖ ^ 2 ≤ w.im / w.im ^ 2 :=
    div_le_div_of_nonneg_left him.le (pow_pos him 2) hsq
  have h2 : w.im / w.im ^ 2 = 1 / w.im := by field_simp
  have h3 : (1 : ℝ) / w.im ≤ Work.Kernels.scale w := by
    rw [Work.Kernels.scale]
    have hb : (0 : ℝ) ≤ ‖(w : ℂ)‖ := norm_nonneg _
    have h4 : w.im⁻¹ = 1 / w.im := by rw [one_div]
    linarith [h4, hb]
  linarith

/-! ## A decay constant adapted to the *shifted* sharp regime

The sharp regime `e^{-π(t - Im (S•w))}` on `t ≥ 2 Im (S•w) + 1` has `t - Im (S•w) ≥ t/2`; after
factoring out the mandatory `e^{-πλ}` (`λ = r²`) one is left with the decay `e^{-πt/2}`, whose
integral is the constant `shiftDecay`. -/
noncomputable def shiftDecay (p : ℝ) : ℝ :=
  ∫ t in Set.Ici (1 : ℝ), t ^ p * Real.exp (-(Real.pi / 2 * t))

lemma shiftDecay_nonneg (p : ℝ) : 0 ≤ shiftDecay p := by
  rw [shiftDecay]
  refine setIntegral_nonneg measurableSet_Ici (fun t ht => ?_)
  exact mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (Set.mem_Ici.mp ht)) _)
    (Real.exp_pos _).le

lemma shiftDecay_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) : shiftDecay p ≤ shiftDecay q := by
  have hq : 0 ≤ q := le_trans hp hpq
  have hint1 : IntegrableOn (fun t : ℝ => t ^ p * Real.exp (-(Real.pi / 2 * t))) (Set.Ici (1 : ℝ)) :=
    Work.Asymptotics.integrableOn_rpow_mul_exp_neg p (Real.pi / 2) hp (by positivity)
  have hint2 : IntegrableOn (fun t : ℝ => t ^ q * Real.exp (-(Real.pi / 2 * t))) (Set.Ici (1 : ℝ)) :=
    Work.Asymptotics.integrableOn_rpow_mul_exp_neg q (Real.pi / 2) hq (by positivity)
  rw [shiftDecay, shiftDecay]
  refine integral_mono_ae hint1 hint2 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp ht
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht1 hpq) (Real.exp_pos _).le

/-! ## The two-regime bound for the shifted tail integral -/

private lemma norm_neg_pi_mul_pow' {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ‖(((-(Real.pi * t)) : ℝ) : ℂ) ^ m‖ = (Real.pi * t) ^ m := by
  rw [norm_pow, Work.Asymptotics.norm_ofReal_eq_abs,
    abs_of_neg (by nlinarith [Real.pi_pos, ht])]
  ring

/-- **The shifted two-regime bound.**  Let `h` satisfy a polynomial bound
`‖h t‖ ≤ Cw A^Nw (1+t)^Mw` on the window `1 ≤ t ≤ 2T+1` and a *shifted* exponential bound
`‖h t‖ ≤ Cs A^Ns t^Ms e^{-π(t-T)}` beyond it.  Then the iterated derivatives of the tail integral
`∫_{t ≥ 1} h t e^{-πλt} dt` are bounded by `c A^N e^{-πλ}`, *uniformly in `T`*: the shift in the
exponential is harmless precisely because the threshold `2T+1` forces `t - T ≥ t/2` on the sharp
region.  This is the tile analogue of
`Work.Asymptotics.exists_bound_iteratedDeriv_tailIntegral_two_regime`. -/
theorem exists_bound_iteratedDeriv_tailIntegral_shift
    (l : ℕ) (Cw Nw Mw Cs Ns Ms : ℝ)
    (hCw : 0 ≤ Cw) (hNw : 0 ≤ Nw) (hMw : 0 ≤ Mw)
    (hCs : 0 ≤ Cs) (hNs : 0 ≤ Ns) (hMs : 0 ≤ Ms) :
    ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧
      ∀ (h : ℝ → ℂ) (A T Cg Mg : ℝ), 1 ≤ A → 0 ≤ T → T ≤ A → 0 ≤ Cg → 0 ≤ Mg →
        MeasureTheory.AEStronglyMeasurable h (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))) →
        (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))),
          ‖h t‖ ≤ Cg * t ^ Mg * Real.exp (-(Real.pi * t))) →
        (∀ t : ℝ, 1 ≤ t → t ≤ 2 * T + 1 → ‖h t‖ ≤ Cw * A ^ Nw * (1 + t) ^ Mw) →
        (∀ t : ℝ, 2 * T + 1 ≤ t →
          ‖h t‖ ≤ Cs * A ^ Ns * t ^ Ms * Real.exp (-(Real.pi * (t - T)))) →
        ∀ m : ℕ, m ≤ l → ∀ lam : ℝ, 0 ≤ lam →
          ‖iteratedDeriv m (Work.Asymptotics.tailIntegral h) lam‖
            ≤ c * A ^ N * Real.exp (-(Real.pi * lam)) := by
  refine ⟨Cw * Real.pi ^ l * (4 : ℝ) ^ (Mw + (l : ℝ) + 1) + Cs * Real.pi ^ l * shiftDecay (Ms + l),
    Nw + Mw + (l : ℝ) + 1 + Ns, ?_, ?_, ?_⟩
  · have h1 : 0 ≤ Cw * Real.pi ^ l * (4 : ℝ) ^ (Mw + (l : ℝ) + 1) :=
      mul_nonneg (mul_nonneg hCw (pow_nonneg Real.pi_pos.le l))
        (Real.rpow_nonneg (by norm_num) _)
    have h2 : 0 ≤ Cs * Real.pi ^ l * shiftDecay (Ms + l) :=
      mul_nonneg (mul_nonneg hCs (pow_nonneg Real.pi_pos.le l)) (shiftDecay_nonneg _)
    linarith
  · have h0 : 0 ≤ Nw + Mw + (l : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
      linarith
    linarith
  · intro h A T Cg Mg hA hT hTA hCg hMg hmeas hb hwin hsharp m hm lam hlam
    have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
    set B : ℝ := 2 * T + 1 with hBdef
    have hB1 : (1 : ℝ) ≤ B := by rw [hBdef]; linarith
    have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
    -- the amplitude multiplied by `(-πt)^m`
    set G : ℝ → ℂ := fun t => h t * (((-(Real.pi * t)) : ℝ) : ℂ) ^ m with hGdef
    have hGmeas : AEStronglyMeasurable G (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))) :=
      hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
        (((-(Real.pi * t)) : ℝ) : ℂ) ^ m).aestronglyMeasurable
    have hGbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))),
        ‖G t‖ ≤ Cg * Real.pi ^ m * t ^ (Mg + (m : ℝ)) * Real.exp (-(Real.pi * t)) := by
      simpa only [hGdef] using Work.Asymptotics.tailIntegral_amp_ae_bound h hb m
    -- the integrand `F = G · e^{-πλt}`
    set F : ℝ → ℂ := fun t => G t * (Real.exp (-(Real.pi * lam * t)) : ℂ) with hFdef
    have hFint : IntegrableOn F (Set.Ici (1 : ℝ)) := by
      rw [hFdef]
      exact Work.Asymptotics.integrableOn_tailIntegral G hGmeas
        (mul_nonneg hCg (pow_nonneg Real.pi_pos.le m))
        (add_nonneg hMg (Nat.cast_nonneg m)) hGbound (by linarith)
    have hderiv : iteratedDeriv m (Work.Asymptotics.tailIntegral h) lam
        = ∫ t in Set.Ici (1 : ℝ), F t := by
      rw [Work.Asymptotics.tailIntegral_iteratedDeriv h hmeas hCg hMg hb m lam (by linarith),
        Work.Asymptotics.tailIntegral]
    rw [hderiv, Work.Asymptotics.setIntegral_Ici_split_at_Icc_Ioi hB1 hFint]
    have hnormF : IntegrableOn (fun t : ℝ => ‖F t‖) (Set.Ici (1 : ℝ)) := hFint.norm
    have hnorm_win : IntegrableOn (fun t : ℝ => ‖F t‖) (Set.Icc (1 : ℝ) B) :=
      hnormF.mono_set (fun _ ht => ht.1)
    have hnorm_tail : IntegrableOn (fun t : ℝ => ‖F t‖) (Set.Ioi B) :=
      hnormF.mono_set (fun _ ht => le_trans hB1 ht.le)
    -- pointwise window bound
    have hwin_pt : ∀ t ∈ Set.Icc (1 : ℝ) B,
        ‖F t‖ ≤ (Cw * A ^ Nw * Real.pi ^ m)
          * ((1 + t) ^ Mw * t ^ m * Real.exp (-(Real.pi * lam * t))) := by
      intro t ht
      obtain ⟨ht1, htB⟩ := ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
      have hht : ‖h t‖ ≤ Cw * A ^ Nw * (1 + t) ^ Mw :=
        hwin t ht1 (by rw [hBdef] at htB; exact htB)
      have hnormG : ‖G t‖ = ‖h t‖ * (Real.pi * t) ^ m := by
        simp only [hGdef]
        rw [norm_mul, norm_neg_pi_mul_pow' ht0]
      have hFt : ‖F t‖ = ‖G t‖ * Real.exp (-(Real.pi * lam * t)) := by
        simp only [hFdef]
        rw [norm_mul, Work.Asymptotics.norm_ofReal_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc ‖F t‖ = ‖h t‖ * (Real.pi * t) ^ m * Real.exp (-(Real.pi * lam * t)) := by
            rw [hFt, hnormG]
        _ ≤ (Cw * A ^ Nw * (1 + t) ^ Mw) * (Real.pi * t) ^ m
              * Real.exp (-(Real.pi * lam * t)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hht (pow_nonneg (mul_nonneg Real.pi_pos.le ht0.le) m))
              (Real.exp_pos _).le
        _ = (Cw * A ^ Nw * Real.pi ^ m)
              * ((1 + t) ^ Mw * t ^ m * Real.exp (-(Real.pi * lam * t))) := by
            rw [mul_pow]; ring
    -- integrability of the window majorant
    have hmaj_win_int : IntegrableOn
        (fun t : ℝ => (1 + t) ^ Mw * t ^ m * Real.exp (-(Real.pi * lam * t)))
        (Set.Icc (1 : ℝ) B) := by
      refine Measure.integrableOn_of_bounded (M := (1 + B) ^ Mw * B ^ m) ?_ ?_ ?_
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      · measurability
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have ht1 : (1 : ℝ) ≤ t := ht.1
        have htB : t ≤ B := ht.2
        have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
        have h1t : (0 : ℝ) < 1 + t := by linarith
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg h1t.le _) (pow_nonneg ht0.le _))
            (Real.exp_pos _).le)]
        have h3 : (1 + t) ^ Mw ≤ (1 + B) ^ Mw := Real.rpow_le_rpow h1t.le (by linarith) hMw
        have h4 : t ^ m ≤ B ^ m := pow_le_pow_left₀ ht0.le htB m
        have h5 : Real.exp (-(Real.pi * lam * t)) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by
            have hπl : (0 : ℝ) ≤ Real.pi * lam := mul_nonneg Real.pi_pos.le hlam
            have h2 : (0 : ℝ) ≤ Real.pi * lam * t := mul_nonneg hπl (by linarith)
            linarith)
        have h3B : (0 : ℝ) ≤ (1 + B) ^ Mw := Real.rpow_nonneg (by linarith) Mw
        calc (1 + t) ^ Mw * t ^ m * Real.exp (-(Real.pi * lam * t))
            ≤ (1 + B) ^ Mw * B ^ m * 1 :=
              mul_le_mul (mul_le_mul h3 h4 (pow_nonneg ht0.le m) h3B) h5 (Real.exp_pos _).le
                (mul_nonneg h3B (pow_nonneg hB0.le m))
          _ = (1 + B) ^ Mw * B ^ m := by ring
    -- the window integral estimate
    have hwin_bd : ∫ t in Set.Icc (1 : ℝ) B, ‖F t‖
        ≤ Cw * A ^ Nw * Real.pi ^ m
          * ((1 + B) ^ (Mw + (l : ℝ) + 1) * Real.exp (-(Real.pi * lam))) := by
      have hC0 : (0 : ℝ) ≤ Cw * A ^ Nw * Real.pi ^ m :=
        mul_nonneg (mul_nonneg hCw (Real.rpow_nonneg hA0.le Nw)) (pow_nonneg Real.pi_pos.le m)
      have h1 := setIntegral_mono_on hnorm_win
        (hmaj_win_int.const_mul (Cw * A ^ Nw * Real.pi ^ m)) measurableSet_Icc hwin_pt
      rw [integral_const_mul] at h1
      calc ∫ t in Set.Icc (1 : ℝ) B, ‖F t‖
          ≤ (Cw * A ^ Nw * Real.pi ^ m)
              * ∫ t in Set.Icc (1 : ℝ) B,
                  (1 + t) ^ Mw * t ^ m * Real.exp (-(Real.pi * lam * t)) := h1
        _ ≤ (Cw * A ^ Nw * Real.pi ^ m)
              * ((1 + B) ^ (Mw + (l : ℝ) + 1) * Real.exp (-(Real.pi * lam))) :=
            mul_le_mul_of_nonneg_left (windowIntegral_bound Mw hMw B hB1 l hlam hm) hC0
    -- pointwise tail bound
    have htail_pt : ∀ t ∈ Set.Ioi B,
        ‖F t‖ ≤ (Cs * A ^ Ns * Real.pi ^ m)
          * (Real.exp (-(Real.pi * lam))
              * (t ^ (Ms + (m : ℝ)) * Real.exp (-(Real.pi / 2 * t)))) := by
      intro t ht
      have htB : B < t := ht
      have h2T1 : 2 * T + 1 ≤ t := by
        have h := htB; rw [hBdef] at h; linarith
      have ht1 : (1 : ℝ) ≤ t := le_trans hB1 (le_of_lt htB)
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
      have hht : ‖h t‖ ≤ Cs * A ^ Ns * t ^ Ms * Real.exp (-(Real.pi * (t - T))) := hsharp t h2T1
      have hnormG : ‖G t‖ = ‖h t‖ * (Real.pi * t) ^ m := by
        simp only [hGdef]
        rw [norm_mul, norm_neg_pi_mul_pow' ht0]
      have hFt : ‖F t‖ = ‖G t‖ * Real.exp (-(Real.pi * lam * t)) := by
        simp only [hFdef]
        rw [norm_mul, Work.Asymptotics.norm_ofReal_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hexp : Real.exp (-(Real.pi * (t - T))) * Real.exp (-(Real.pi * lam * t))
          ≤ Real.exp (-(Real.pi * lam)) * Real.exp (-(Real.pi / 2 * t)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h1 : (0 : ℝ) ≤ lam * (t - 1) := mul_nonneg hlam (by linarith)
        have h2 : (0 : ℝ) ≤ t / 2 - T := by linarith
        have h3 : (0 : ℝ) ≤ Real.pi * (t / 2 - T) := mul_nonneg Real.pi_pos.le h2
        have h4 : (0 : ℝ) ≤ Real.pi * (lam * (t - 1)) := mul_nonneg Real.pi_pos.le h1
        nlinarith [h3, h4]
      have hpowadd : t ^ Ms * t ^ m = t ^ (Ms + (m : ℝ)) := by
        have h1 : (t ^ m : ℝ) = t ^ (m : ℝ) := (Real.rpow_natCast t m).symm
        rw [h1, ← Real.rpow_add ht0]
      calc ‖F t‖ = ‖h t‖ * (Real.pi * t) ^ m * Real.exp (-(Real.pi * lam * t)) := by
            rw [hFt, hnormG]
        _ ≤ (Cs * A ^ Ns * t ^ Ms * Real.exp (-(Real.pi * (t - T))))
              * (Real.pi * t) ^ m * Real.exp (-(Real.pi * lam * t)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hht (pow_nonneg (mul_nonneg Real.pi_pos.le ht0.le) m))
              (Real.exp_pos _).le
        _ = (Cs * A ^ Ns * Real.pi ^ m)
              * (t ^ (Ms + (m : ℝ))
                  * (Real.exp (-(Real.pi * (t - T))) * Real.exp (-(Real.pi * lam * t)))) := by
            rw [mul_pow, ← hpowadd]; ring
        _ ≤ (Cs * A ^ Ns * Real.pi ^ m)
              * (t ^ (Ms + (m : ℝ))
                  * (Real.exp (-(Real.pi * lam)) * Real.exp (-(Real.pi / 2 * t)))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht0.le _)) (by positivity)
        _ = (Cs * A ^ Ns * Real.pi ^ m)
              * (Real.exp (-(Real.pi * lam))
                  * (t ^ (Ms + (m : ℝ)) * Real.exp (-(Real.pi / 2 * t)))) := by ring
    -- integrability of the tail majorant
    have hmaj_tail_int : IntegrableOn
        (fun t : ℝ => Real.exp (-(Real.pi * lam))
            * (t ^ (Ms + (m : ℝ)) * Real.exp (-(Real.pi / 2 * t)))) (Set.Ioi B) := by
      refine ((Work.Asymptotics.integrableOn_rpow_mul_exp_neg (Ms + m) (Real.pi / 2)
        (by positivity) (by positivity)).mono_set ?_).const_mul _
      intro t ht
      exact le_trans hB1 (le_of_lt ht)
    have htail_bd : ∫ t in Set.Ioi B, ‖F t‖
        ≤ Cs * A ^ Ns * Real.pi ^ m
            * (Real.exp (-(Real.pi * lam)) * shiftDecay (Ms + (m : ℝ))) := by
      have hC0 : (0 : ℝ) ≤ Cs * A ^ Ns * Real.pi ^ m :=
        mul_nonneg (mul_nonneg hCs (Real.rpow_nonneg hA0.le Ns)) (pow_nonneg Real.pi_pos.le m)
      have hmono : ∫ t in Set.Ioi B, t ^ (Ms + (m : ℝ)) * Real.exp (-(Real.pi / 2 * t))
          ≤ shiftDecay (Ms + (m : ℝ)) := by
        rw [shiftDecay]
        refine setIntegral_mono_set
          (Work.Asymptotics.integrableOn_rpow_mul_exp_neg (Ms + m) (Real.pi / 2)
            (by positivity) (by positivity)) ?_ ?_
        · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
          exact mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (Set.mem_Ici.mp ht)) _)
            (Real.exp_pos _).le
        · exact Filter.Eventually.of_forall (fun t ht => le_trans hB1 (le_of_lt ht))
      have h1 := setIntegral_mono_on hnorm_tail
        (hmaj_tail_int.const_mul (Cs * A ^ Ns * Real.pi ^ m)) measurableSet_Ioi htail_pt
      rw [integral_const_mul] at h1
      calc ∫ t in Set.Ioi B, ‖F t‖
          ≤ (Cs * A ^ Ns * Real.pi ^ m)
              * ∫ t in Set.Ioi B, (Real.exp (-(Real.pi * lam))
                  * (t ^ (Ms + (m : ℝ)) * Real.exp (-(Real.pi / 2 * t)))) := h1
        _ = (Cs * A ^ Ns * Real.pi ^ m)
              * (Real.exp (-(Real.pi * lam))
                  * ∫ t in Set.Ioi B, t ^ (Ms + (m : ℝ)) * Real.exp (-(Real.pi / 2 * t))) := by
            rw [integral_const_mul]
        _ ≤ (Cs * A ^ Ns * Real.pi ^ m)
              * (Real.exp (-(Real.pi * lam)) * shiftDecay (Ms + (m : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le) hC0
    -- arithmetic: absorb the polynomial factors
    have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hπpow : Real.pi ^ m ≤ Real.pi ^ l := pow_le_pow_right₀ hpi hm
    have hmm : (Ms + (m : ℝ)) ≤ (Ms + (l : ℝ)) := by
      have : (m : ℝ) ≤ (l : ℝ) := by exact_mod_cast hm
      linarith
    have hshift : shiftDecay (Ms + (m : ℝ)) ≤ shiftDecay (Ms + l) :=
      shiftDecay_mono (by positivity) hmm
    have hB4 : (1 + B) ^ (Mw + (l : ℝ) + 1)
        ≤ (4 : ℝ) ^ (Mw + (l : ℝ) + 1) * A ^ (Mw + (l : ℝ) + 1) := by
      have h1 : 1 + B ≤ 4 * A := by rw [hBdef]; nlinarith [hA, hT, hTA]
      have h2 : (1 + B) ^ (Mw + (l : ℝ) + 1) ≤ (4 * A) ^ (Mw + (l : ℝ) + 1) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
      rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hA0.le] at h2
    have hNap : Nw + (Mw + (l : ℝ) + 1) ≤ Nw + Mw + (l : ℝ) + 1 + Ns := by
      have : (0 : ℝ) ≤ Ns := hNs
      linarith
    set E : ℝ := Real.exp (-(Real.pi * lam)) with hEdef
    have hE0 : 0 ≤ E := by rw [hEdef]; positivity
    have hterm1 : Cw * A ^ Nw * Real.pi ^ m * ((1 + B) ^ (Mw + (l : ℝ) + 1) * E)
        ≤ Cw * Real.pi ^ l * (4 : ℝ) ^ (Mw + (l : ℝ) + 1)
            * A ^ (Nw + Mw + (l : ℝ) + 1 + Ns) * E := by
      have hstep1 : Cw * A ^ Nw * Real.pi ^ m * ((1 + B) ^ (Mw + (l : ℝ) + 1) * E)
          ≤ (Cw * A ^ Nw * Real.pi ^ l)
              * (((4 : ℝ) ^ (Mw + (l : ℝ) + 1) * A ^ (Mw + (l : ℝ) + 1)) * E) := by
        refine mul_le_mul ?_ ?_ ?_ ?_
        · exact mul_le_mul_of_nonneg_left hπpow
            (mul_nonneg hCw (Real.rpow_nonneg hA0.le Nw))
        · exact mul_le_mul_of_nonneg_right hB4 hE0
        · exact mul_nonneg (Real.rpow_nonneg (by linarith [hA] : (0 : ℝ) ≤ 1 + B) _) hE0
        · exact mul_nonneg (mul_nonneg hCw (Real.rpow_nonneg hA0.le Nw))
            (pow_nonneg Real.pi_pos.le l)
      have hstep2 : (Cw * A ^ Nw * Real.pi ^ l)
              * (((4 : ℝ) ^ (Mw + (l : ℝ) + 1) * A ^ (Mw + (l : ℝ) + 1)) * E)
          = (Cw * Real.pi ^ l * (4 : ℝ) ^ (Mw + (l : ℝ) + 1) * E)
              * A ^ (Nw + (Mw + (l : ℝ) + 1)) := by
        have hAadd : A ^ (Nw + (Mw + (l : ℝ) + 1))
            = A ^ Nw * A ^ (Mw + (l : ℝ) + 1) := Real.rpow_add hA0 Nw (Mw + (l : ℝ) + 1)
        rw [hAadd]; ring
      have hstep3 : (Cw * Real.pi ^ l * (4 : ℝ) ^ (Mw + (l : ℝ) + 1) * E)
              * A ^ (Nw + (Mw + (l : ℝ) + 1))
          ≤ (Cw * Real.pi ^ l * (4 : ℝ) ^ (Mw + (l : ℝ) + 1) * E)
              * A ^ (Nw + Mw + (l : ℝ) + 1 + Ns) := by
        refine mul_le_mul_of_nonneg_left ?_ ?_
        · exact Real.rpow_le_rpow_of_exponent_le hA (by linarith [hNs])
        · exact mul_nonneg (mul_nonneg (mul_nonneg hCw (pow_nonneg Real.pi_pos.le l))
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)) hE0
      refine le_trans hstep1 (le_trans (le_of_eq hstep2) (le_trans hstep3 (le_of_eq ?_)))
      ring
    have hterm2 : Cs * A ^ Ns * Real.pi ^ m * (E * shiftDecay (Ms + (m : ℝ)))
        ≤ Cs * Real.pi ^ l * shiftDecay (Ms + l)
            * A ^ (Nw + Mw + (l : ℝ) + 1 + Ns) * E := by
      have hNsN : Ns ≤ Nw + Mw + (l : ℝ) + 1 + Ns := by
        have h0 : (0 : ℝ) ≤ Nw + Mw + (l : ℝ) + 1 := by
          have : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
          linarith [hNw, hMw]
        linarith
      have hpish : Real.pi ^ m * shiftDecay (Ms + (m : ℝ))
          ≤ Real.pi ^ l * shiftDecay (Ms + l) :=
        mul_le_mul hπpow hshift (shiftDecay_nonneg _) (pow_nonneg Real.pi_pos.le l)
      have hstep1 : Cs * A ^ Ns * Real.pi ^ m * (E * shiftDecay (Ms + (m : ℝ)))
          = (Cs * A ^ Ns * E) * (Real.pi ^ m * shiftDecay (Ms + (m : ℝ))) := by ring
      have hstep2 : (Cs * A ^ Ns * E) * (Real.pi ^ m * shiftDecay (Ms + (m : ℝ)))
          ≤ (Cs * A ^ Ns * E) * (Real.pi ^ l * shiftDecay (Ms + l)) :=
        mul_le_mul_of_nonneg_left hpish
          (mul_nonneg (mul_nonneg hCs (Real.rpow_nonneg hA0.le Ns)) hE0)
      have hstep3 : (Cs * A ^ Ns * E) * (Real.pi ^ l * shiftDecay (Ms + l))
          = (Cs * Real.pi ^ l * shiftDecay (Ms + l) * E) * A ^ Ns := by ring
      have hstep4 : (Cs * Real.pi ^ l * shiftDecay (Ms + l) * E) * A ^ Ns
          ≤ (Cs * Real.pi ^ l * shiftDecay (Ms + l) * E)
              * A ^ (Nw + Mw + (l : ℝ) + 1 + Ns) := by
        refine mul_le_mul_of_nonneg_left ?_ ?_
        · exact Real.rpow_le_rpow_of_exponent_le hA hNsN
        · exact mul_nonneg (mul_nonneg (mul_nonneg hCs (pow_nonneg Real.pi_pos.le l))
            (shiftDecay_nonneg _)) hE0
      refine le_trans (le_of_eq hstep1) (le_trans hstep2 (le_trans (le_of_eq hstep3) (le_trans hstep4 (le_of_eq ?_))))
      ring
    have hsum : Cw * A ^ Nw * Real.pi ^ m
          * ((1 + B) ^ (Mw + (l : ℝ) + 1) * E)
        + Cs * A ^ Ns * Real.pi ^ m * (E * shiftDecay (Ms + (m : ℝ)))
        ≤ (Cw * Real.pi ^ l * (4 : ℝ) ^ (Mw + (l : ℝ) + 1)
            + Cs * Real.pi ^ l * shiftDecay (Ms + l))
            * A ^ (Nw + Mw + (l : ℝ) + 1 + Ns) * E := by
      have h : Cw * Real.pi ^ l * (4 : ℝ) ^ (Mw + (l : ℝ) + 1)
            * A ^ (Nw + Mw + (l : ℝ) + 1 + Ns) * E
          + Cs * Real.pi ^ l * shiftDecay (Ms + l)
            * A ^ (Nw + Mw + (l : ℝ) + 1 + Ns) * E
          = (Cw * Real.pi ^ l * (4 : ℝ) ^ (Mw + (l : ℝ) + 1)
              + Cs * Real.pi ^ l * shiftDecay (Ms + l))
              * A ^ (Nw + Mw + (l : ℝ) + 1 + Ns) * E := by ring
      linarith [hterm1, hterm2, h]
    rw [hEdef] at hsum
    calc ‖(∫ t in Set.Icc (1 : ℝ) B, F t) + (∫ t in Set.Ioi B, F t)‖
        ≤ ‖∫ t in Set.Icc (1 : ℝ) B, F t‖ + ‖∫ t in Set.Ioi B, F t‖ := norm_add_le _ _
      _ ≤ (∫ t in Set.Icc (1 : ℝ) B, ‖F t‖) + (∫ t in Set.Ioi B, ‖F t‖) :=
          add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _)
      _ ≤ Cw * A ^ Nw * Real.pi ^ m * ((1 + B) ^ (Mw + (l : ℝ) + 1) * Real.exp (-(Real.pi * lam)))
            + Cs * A ^ Ns * Real.pi ^ m
                * (Real.exp (-(Real.pi * lam)) * shiftDecay (Ms + (m : ℝ))) :=
          add_le_add hwin_bd htail_bd
      _ ≤ (Cw * Real.pi ^ l * (4 : ℝ) ^ (Mw + (l : ℝ) + 1) + Cs * Real.pi ^ l * shiftDecay (Ms + l))
            * A ^ (Nw + Mw + (l : ℝ) + 1 + Ns) * Real.exp (-(Real.pi * lam)) := by
          simpa only [hEdef] using hsum

/-! ## The main theorem -/

/-- The amplitude `Kaxis (Kfun ℓ d) (n+w) · - Aexp (Gcusp ℓ d) (n+w) ·` on the cusp-`±1` tiles is
controlled in the two regimes: polynomially on `[1, 2 Im (S•w)+1]` (from `hwin`) and by
`e^{-π(t - Im(S•w))}` beyond (from `hsharp`).  This is exactly the input of the shifted two-regime
tail estimate; we package it with the a.e. global bound needed for the parametric integral. -/
lemma tile_amplitude_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hwin : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M)
    (hsharp : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M
              * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))))
    (w : UpperHalfPlane) (n : ℤ) (hw : w ∈ Work.Asymptotics.KEpsilon) (hn : n = 1 ∨ n = -1) :
    ∃ Cg Mg : ℝ, 0 ≤ Cg ∧ 0 ≤ Mg ∧
      AEStronglyMeasurable (fun t : ℝ =>
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t)
        (volume.restrict (Set.Ici (1 : ℝ))) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ Cg * t ^ Mg * Real.exp (-(Real.pi * t))) := by
  obtain ⟨Cw, Nw, Mw, hCwpos, hNw, hMw, hwinb⟩ := hwin
  obtain ⟨Cs, Ns, Ms, hCspos, hNs, hMs, hsharpb⟩ := hsharp
  set h : ℝ → ℂ := fun t =>
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t with hhdef
  have hmeas : AEStronglyMeasurable h (volume.restrict (Set.Ici (1 : ℝ))) := by
    rw [hhdef]
    have h1 : Measurable (fun t : ℝ =>
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t) :=
      Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd _
    have h2 : Measurable (fun t : ℝ =>
        Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t) := by
      unfold Work.Asymptotics.Aexp; fun_prop
    exact (h1.sub h2).aestronglyMeasurable
  have hB1 : (1 : ℝ) ≤ 2 * (ModularGroup.S • w).im + 1 := by linarith [hw.2]
  have hD1 : 0 ≤ Cw * (Work.Kernels.scale w) ^ Nw :=
    mul_nonneg hCwpos.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nw)
  have hD2 : 0 ≤ Cs * (Work.Kernels.scale w) ^ Ns * Real.exp (Real.pi * (ModularGroup.S • w).im) :=
    mul_nonneg (mul_nonneg hCspos.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Ns))
      (Real.exp_pos _).le
  have hb1 : ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
      ‖h t‖ ≤ (Cw * (Work.Kernels.scale w) ^ Nw) * (1 + t) ^ Mw := by
    intro t ht1 ht2
    have h1 : ‖h t‖ ≤ Cw * (Work.Kernels.scale w) ^ Nw * t ^ Mw := by
      rw [hhdef]; exact hwinb w n hn hw t ht1 ht2
    have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
    have h2 : t ^ Mw ≤ (1 + t) ^ Mw :=
      Real.rpow_le_rpow ht0 (by linarith) hMw
    calc ‖h t‖ ≤ Cw * (Work.Kernels.scale w) ^ Nw * t ^ Mw := h1
      _ ≤ Cw * (Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCwpos.le
            (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nw))
  have hb2 : ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
      ‖h t‖ ≤ (Cs * (Work.Kernels.scale w) ^ Ns * Real.exp (Real.pi * (ModularGroup.S • w).im))
          * t ^ Ms * Real.exp (-(Real.pi * t)) := by
    intro t ht
    have h1 : ‖h t‖ ≤ Cs * (Work.Kernels.scale w) ^ Ns * t ^ Ms
        * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := by
      rw [hhdef]; exact hsharpb w n hn hw t ht
    have hexp : Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
        = Real.exp (Real.pi * (ModularGroup.S • w).im) * Real.exp (-(Real.pi * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖h t‖ ≤ Cs * (Work.Kernels.scale w) ^ Ns * t ^ Ms
          * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := h1
      _ = (Cs * (Work.Kernels.scale w) ^ Ns * Real.exp (Real.pi * (ModularGroup.S • w).im))
            * t ^ Ms * Real.exp (-(Real.pi * t)) := by
          rw [hexp]; ring
  obtain ⟨Cg, Mg, hCg, hMg, hglob⟩ :=
    Work.Asymptotics.ae_bound_of_two_regime h hB1 hD1 hD2 hMw hMs hb1 hb2
  refine ⟨Cg, Mg, hCg, hMg, hmeas, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact hglob t (Set.mem_Ici.mp ht)

theorem tileLayerTrunc_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hwin : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M)
    (hsharp : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M
              * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      (∀ (w : UpperHalfPlane) (n : ℤ), w ∈ Work.Asymptotics.KEpsilon → (n = 1 ∨ n = -1) →
        ContDiff ℝ ⊤ (fun s : ℝ =>
          Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d ((n : ℝ) +ᵥ w) s)) ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), w ∈ Work.Asymptotics.KEpsilon → (n = 1 ∨ n = -1) →
        ∀ r : ℝ, (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d ((n : ℝ) +ᵥ w) s) r‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  intro k l
  -- the constants of the two inputs
  have hwin_c := hwin
  have hsharp_c := hsharp
  obtain ⟨Cw, Nw, Mw, hCwpos, hNw, hMw, hwinb⟩ := hwin_c
  obtain ⟨Cs, Ns, Ms, hCspos, hNs, hMs, hsharpb⟩ := hsharp_c
  -- the shifted two-regime tail estimate and the chain-rule composition estimate
  obtain ⟨ct, Nt, hct, hNt, htail⟩ :=
    exists_bound_iteratedDeriv_tailIntegral_shift l Cw Nw Mw Cs Ns Ms
      hCwpos.le hNw hMw hCspos.le hNs hMs
  obtain ⟨cc, hcc, hcomp⟩ := Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound k l
  refine ⟨cc * ct, Nt, mul_nonneg hcc hct, hNt, ?_, ?_⟩
  · -- smoothness of `layerTrunc` on the tiles
    intro w n hw hn
    obtain ⟨Cg, Mg, hCg, hMg, hmeas, hbglob⟩ := tile_amplitude_bound ℓ d hd hwin hsharp w n hw hn
    set g : ℝ → ℂ := fun t =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t with hgdef
    have hcont : ContDiffOn ℝ ⊤ (Work.Asymptotics.tailIntegral g) (Set.Ioi (-1)) :=
      Work.Asymptotics.contDiffOn_real_tailIntegral g hmeas hCg hMg hbglob
    have hsq : ContDiff ℝ ⊤ (fun r : ℝ => r ^ 2) := contDiff_id.pow 2
    have hcomp2 : ContDiffOn ℝ ⊤ (fun r : ℝ => Work.Asymptotics.tailIntegral g (r ^ 2)) Set.univ :=
      hcont.comp hsq.contDiffOn (fun r _ => by
        simp only [Set.mem_Ioi]; linarith [sq_nonneg r])
    have htr : ContDiff ℝ ⊤ (fun r : ℝ => Work.Asymptotics.tailIntegral g (r ^ 2)) :=
      contDiffOn_univ.mp hcomp2
    have hcos : ContDiff ℝ ⊤ (fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ)) := by
      have h1 : ContDiff ℝ ⊤ (fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℝ)) := by fun_prop
      have h2 : ContDiff ℝ ⊤ (fun r : ℝ => ((2 - 2 * Real.cos (Real.pi * r ^ 2) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp h1
      simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat] using h2
    have hfun : (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d
          ((n : ℝ) +ᵥ w) s)
        = fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ)
            * Work.Asymptotics.tailIntegral g (r ^ 2) := by
      funext r
      rw [Work.Asymptotics.layerTrunc_eq_tailIntegral, hgdef]
    rw [hfun]
    exact hcos.mul htr
  · -- the seminorm bound
    intro w n hw hn r
    obtain ⟨Cg, Mg, hCg, hMg, hmeas, hbglob⟩ := tile_amplitude_bound ℓ d hd hwin hsharp w n hw hn
    set g : ℝ → ℂ := fun t =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t with hgdef
    have hA1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hT0 : (0 : ℝ) ≤ (ModularGroup.S • w).im := by linarith [hw.2]
    have hTA : (ModularGroup.S • w).im ≤ Work.Kernels.scale w := im_S_smul_le_scale w
    have hwinG : ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖g t‖ ≤ Cw * (Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw := by
      intro t ht1 ht2
      have h1 : ‖g t‖ ≤ Cw * (Work.Kernels.scale w) ^ Nw * t ^ Mw := by
        rw [hgdef]; exact hwinb w n hn hw t ht1 ht2
      have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
      have h2 : t ^ Mw ≤ (1 + t) ^ Mw := Real.rpow_le_rpow ht0 (by linarith) hMw
      calc ‖g t‖ ≤ Cw * (Work.Kernels.scale w) ^ Nw * t ^ Mw := h1
        _ ≤ Cw * (Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hCwpos.le
              (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nw))
    have hsharpG : ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
        ‖g t‖ ≤ Cs * (Work.Kernels.scale w) ^ Ns * t ^ Ms
            * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := by
      intro t ht
      rw [hgdef]; exact hsharpb w n hn hw t ht
    have hFdiff : ContDiffOn ℝ (l : WithTop ℕ∞) (Work.Asymptotics.tailIntegral g) (Set.Ioi (-1)) :=
      Work.Asymptotics.tailIntegral_contDiffOn l g hmeas hCg hMg hbglob
    have hbound : ∀ m : ℕ, m ≤ l → ∀ x : ℝ, 0 ≤ x →
        ‖iteratedDeriv m (Work.Asymptotics.tailIntegral g) x‖
          ≤ (ct * (Work.Kernels.scale w) ^ Nt) * Real.exp (-(Real.pi * x)) :=
      fun m hm x hx => htail g (Work.Kernels.scale w) ((ModularGroup.S • w).im) Cg Mg
        hA1 hT0 hTA hCg hMg hmeas hbglob hwinG hsharpG m hm x hx
    have hmain := hcomp (Work.Asymptotics.tailIntegral g) (ct * (Work.Kernels.scale w) ^ Nt)
      (by positivity) hFdiff hbound r
    have hfun : (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d
          ((n : ℝ) +ᵥ w) s)
        = fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
            * Work.Asymptotics.tailIntegral g (s ^ 2) := by
      funext s
      rw [Work.Asymptotics.layerTrunc_eq_tailIntegral, hgdef]
    rw [hfun]
    calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
          * Work.Asymptotics.tailIntegral g (s ^ 2)) r‖
        ≤ cc * (ct * (Work.Kernels.scale w) ^ Nt) := hmain
      _ = (cc * ct) * (Work.Kernels.scale w) ^ Nt := by ring

end Work.Asymptotics.Tile
