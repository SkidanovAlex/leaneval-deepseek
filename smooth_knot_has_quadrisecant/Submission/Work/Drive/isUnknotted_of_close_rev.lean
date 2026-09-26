import Mathlib
import Submission.Work.Drive.isUnknotted_of_close
import Submission.Work.Drive.familyRadiusAlt
import Submission.Work.Drive.smallCorrectionKnot

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## Calculus helpers for curves into `Space` -/

private lemma velocity_add_r {f g : ℝ → Space} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    velocity (fun u : ℝ => f u + g u) t = velocity f t + velocity g t := by
  have h : (fun u : ℝ => f u + g u) = f + g := rfl
  unfold velocity
  rw [h, deriv_add hf hg]

private lemma velocity_sub_r {f g : ℝ → Space} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    velocity (fun u : ℝ => f u - g u) t = velocity f t - velocity g t := by
  have h : (fun u : ℝ => f u - g u) = f - g := rfl
  unfold velocity
  rw [h, deriv_sub hf hg]

private lemma velocity_const_smul_r {w : ℝ → Space} (c : ℝ) {t : ℝ}
    (hw : DifferentiableAt ℝ w t) :
    velocity (fun u : ℝ => c • w u) t = c • velocity w t := by
  have h : (fun u : ℝ => c • w u) = c • w := rfl
  unfold velocity
  rw [h, deriv_const_smul c hw]

private lemma contDiff_slice_r {R : ℝ → ℝ → Space} {s : ℝ}
    (hR : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2)) :
    ContDiff ℝ ⊤ (fun t : ℝ => R t s) :=
  hR.comp (contDiff_id.prodMk contDiff_const)

private lemma diffAt_slice_r {R : ℝ → ℝ → Space} {s t : ℝ}
    (hR : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2)) :
    DifferentiableAt ℝ (fun u : ℝ => R u s) t :=
  ((contDiff_slice_r (s := s) hR).differentiable (by simp)).differentiableAt

private lemma diffAt_of_contDiff_r {f : ℝ → Space} {t : ℝ} (hf : ContDiff ℝ ⊤ f) :
    DifferentiableAt ℝ f t :=
  (hf.differentiable (by simp)).differentiableAt

/-- **Unknottedness is open in the C¹ topology.**  If `r` is an unknotted smooth
knot, then every smooth knot `r'` that is C¹-close to `r` is again unknotted:
the analytic unknotting of `r` is corrected by the *small* difference `r' - r`,
and the slices of the corrected family are knots by the fixed-knot criterion
`smallCorrectionKnot` (near `s = 0`, where the corrected family equals `r` plus
a small correction) and by the uniform perturbation radius `uniformRadiusAlt`
(away from `s = 0`, where it equals the slice `R · s` plus a uniformly small
correction). -/
theorem isUnknotted_of_close_rev {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hun : LeanEval.KnotTheory.Quadrisecant.IsUnknotted r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r' : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r' →
      (∀ t : ℝ, ‖r' t - r t‖ < ε ∧
        ‖LeanEval.KnotTheory.Quadrisecant.velocity r' t -
          LeanEval.KnotTheory.Quadrisecant.velocity r t‖ < ε) →
      LeanEval.KnotTheory.Quadrisecant.IsUnknotted r' := by
  obtain ⟨εr, hεr_pos, hεr⟩ := smallCorrectionKnot hr
  refine ⟨εr / 4, by positivity, ?_⟩
  intro r' hr' hclose
  obtain ⟨R, hRsm, hR0, hR1, hRslice⟩ := hun
  -- the `C¹`-window at `s = 0` (two-sided, hence a one-sided window on `[0, δ]`)
  obtain ⟨δ, hδpos, hδb⟩ :=
    familyWindowAt hRsm hRslice ⟨le_rfl, zero_le_one⟩ (γ := εr / 2) (by positivity)
  -- the uniform perturbation radius for the slices of the family
  obtain ⟨ρ, hρpos, hρ⟩ := uniformRadiusAlt hRsm hRslice
  -- the window, shrunk so that `1 - s₂ ≥ 1/2`
  set s₂ : ℝ := min δ (1 / 2) with hs₂
  have hs₂_pos : 0 < s₂ := by rw [hs₂]; exact lt_min hδpos (by norm_num)
  have hs₂_half : s₂ ≤ 1 / 2 := by rw [hs₂]; exact min_le_right _ _
  have hs₂_δ : s₂ ≤ δ := by rw [hs₂]; exact min_le_left _ _
  have hs₂_one : s₂ ≤ 1 := by linarith
  have h1s₂_pos : 0 < 1 - s₂ := by linarith
  have h1s₂_lt : 1 - s₂ < 1 := by linarith
  -- the degree of the correcting polynomial
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 - s₂) ^ N * (εr / 4) < ρ := by
    have hx : 0 < ρ / (εr / 4) := by positivity
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hx h1s₂_lt
    refine ⟨N, ?_⟩
    have hε4 : (0 : ℝ) < εr / 4 := by positivity
    have h := mul_lt_mul_of_pos_right hN hε4
    rw [div_mul_cancel₀ ρ (ne_of_gt hε4)] at h
    exact h
  have hN_le : N ≤ max N 1 := le_max_left _ _
  have hN_bound : (1 - s₂) ^ (max N 1) * (εr / 4) < ρ := by
    have hle := pow_le_pow_of_le_one (le_of_lt h1s₂_pos) (le_of_lt h1s₂_lt) hN_le
    have hε4 : (0 : ℝ) < εr / 4 := by positivity
    nlinarith [hle, hN, hε4]
  -- the corrected family, now running from `r'` to the round circle
  refine ⟨fun t s => R t s + ((1 - s) ^ (max N 1)) • (r' t - r t), ?_, ?_, ?_, ?_⟩
  · -- joint analyticity
    exact hRsm.add (ContDiff.smul
      (ContDiff.pow (contDiff_const.sub contDiff_snd) (max N 1))
      ((hr'.smooth.sub hr.smooth).comp contDiff_fst))
  · -- starts at `r'`
    intro t
    show R t 0 + ((1 - 0) ^ (max N 1)) • (r' t - r t) = r' t
    rw [hR0 t, show (1 : ℝ) - 0 = 1 by norm_num, one_pow, one_smul]
    abel
  · -- ends at the round circle
    intro t
    show R t 1 + ((1 - 1) ^ (max N 1)) • (r' t - r t) = standardCircle t
    rw [hR1 t, show (1 : ℝ) - 1 = 0 by norm_num,
      zero_pow (by omega : ¬ (max N 1) = 0), zero_smul, add_zero]
  · -- every slice is a knot
    intro s hs
    by_cases hsle : s ≤ s₂
    · -- ## Region 1: `s ≤ s₂`, the slice is `r` plus a small correction
      have hsr : |s - 0| ≤ δ := by
        rw [sub_zero, abs_of_nonneg hs.1]
        exact le_trans hsle hs₂_δ
      have hw1' : ∀ t : ℝ, ‖R t s - R t 0‖ ≤ εr / 2 := fun t => (hδb s hs hsr t).1
      have hw2' : ∀ t : ℝ,
          ‖velocity (fun u : ℝ => R u s) t - velocity (fun u : ℝ => R u 0) t‖ ≤ εr / 2 :=
        fun t => (hδb s hs hsr t).2
      have hψ0 : 0 ≤ (1 - s) ^ (max N 1) := pow_nonneg (by linarith [hs.2]) _
      have hψ1 : (1 - s) ^ (max N 1) ≤ 1 :=
        pow_le_one₀ (by linarith [hs.2]) (by linarith [hs.1])
      have hkey : (fun t : ℝ => R t s + ((1 - s) ^ (max N 1)) • (r' t - r t)) =
          fun t : ℝ => r t +
            ((R t s - R t 0) + ((1 - s) ^ (max N 1)) • (r' t - r t)) := by
        funext t
        rw [hR0 t]
        module
      rw [hkey]
      refine hεr _ ?_ ?_ ?_
      · -- analytic
        exact ((contDiff_slice_r (s := s) hRsm).sub (contDiff_slice_r (s := 0) hRsm)).add
          (ContDiff.const_smul ((1 - s) ^ (max N 1)) (hr'.smooth.sub hr.smooth))
      · -- periodic
        intro t
        have h1 : R (t + period) s = R t s := (hRslice s hs).periodic t
        have h2 : R (t + period) 0 = R t 0 :=
          (hRslice 0 (by constructor <;> norm_num)).periodic t
        have h3 : r' (t + period) = r' t := hr'.periodic t
        have h4 : r (t + period) = r t := hr.periodic t
        simp only [h1, h2, h3, h4]
      · -- small
        intro t
        constructor
        · have h4 : ‖r' t - r t‖ < εr / 4 := (hclose t).1
          calc ‖(R t s - R t 0) + ((1 - s) ^ (max N 1)) • (r' t - r t)‖
              ≤ ‖R t s - R t 0‖ + ‖((1 - s) ^ (max N 1)) • (r' t - r t)‖ :=
                norm_add_le _ _
            _ = ‖R t s - R t 0‖ + (1 - s) ^ (max N 1) * ‖r' t - r t‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hψ0]
            _ ≤ εr / 2 + 1 * (εr / 4) := by
                have hnn := norm_nonneg (r' t - r t)
                nlinarith [hw1' t, hψ1, h4, hnn]
            _ < εr := by linarith
        · -- velocity bound
          have hd1 : DifferentiableAt ℝ (fun u : ℝ => R u s - R u 0) t :=
            (diffAt_slice_r (s := s) hRsm).sub (diffAt_slice_r (s := 0) hRsm)
          have hd2 : DifferentiableAt ℝ (fun u : ℝ => r' u - r u) t :=
            diffAt_of_contDiff_r (hr'.smooth.sub hr.smooth)
          have hd3 : DifferentiableAt ℝ
              (fun u : ℝ => ((1 - s) ^ (max N 1)) • (r' u - r u)) t :=
            diffAt_of_contDiff_r (ContDiff.const_smul ((1 - s) ^ (max N 1))
              (hr'.smooth.sub hr.smooth))
          have hsub : velocity (fun u : ℝ => R u s - R u 0) t
              = velocity (fun u : ℝ => R u s) t - velocity (fun u : ℝ => R u 0) t :=
            velocity_sub_r (diffAt_slice_r (s := s) hRsm) (diffAt_slice_r (s := 0) hRsm)
          have hsub' : velocity (fun u : ℝ => r' u - r u) t
              = velocity r' t - velocity r t :=
            velocity_sub_r (diffAt_of_contDiff_r hr'.smooth) (diffAt_of_contDiff_r hr.smooth)
          have hsmul : velocity (fun u : ℝ =>
                ((1 - s) ^ (max N 1)) • (r' u - r u)) t
              = ((1 - s) ^ (max N 1)) • velocity (fun u : ℝ => r' u - r u) t :=
            velocity_const_smul_r ((1 - s) ^ (max N 1)) hd2
          have hvel_eq : velocity (fun u : ℝ =>
                (R u s - R u 0) + ((1 - s) ^ (max N 1)) • (r' u - r u)) t =
              velocity (fun u : ℝ => R u s - R u 0) t +
                ((1 - s) ^ (max N 1)) • velocity (fun u : ℝ => r' u - r u) t := by
            rw [velocity_add_r hd1 hd3, hsmul]
          have h6 : ‖velocity (fun u : ℝ => R u s - R u 0) t‖ ≤ εr / 2 := by
            rw [hsub]; exact hw2' t
          have h7 : ‖velocity (fun u : ℝ => r' u - r u) t‖ < εr / 4 := by
            rw [hsub']; exact (hclose t).2
          calc ‖velocity (fun u : ℝ =>
                  (R u s - R u 0) + ((1 - s) ^ (max N 1)) • (r' u - r u)) t‖
              = ‖velocity (fun u : ℝ => R u s - R u 0) t +
                  ((1 - s) ^ (max N 1)) • velocity (fun u : ℝ => r' u - r u) t‖ := by
                rw [hvel_eq]
            _ ≤ ‖velocity (fun u : ℝ => R u s - R u 0) t‖ +
                  ‖((1 - s) ^ (max N 1)) • velocity (fun u : ℝ => r' u - r u) t‖ :=
                norm_add_le _ _
            _ = ‖velocity (fun u : ℝ => R u s - R u 0) t‖ +
                  (1 - s) ^ (max N 1) *
                    ‖velocity (fun u : ℝ => r' u - r u) t‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hψ0]
            _ ≤ εr / 2 + 1 * (εr / 4) := by
                have hnn := norm_nonneg (velocity (fun u : ℝ => r' u - r u) t)
                nlinarith [h6, hψ1, h7, hnn]
            _ < εr := by linarith
    · -- ## Region 2: `s ≥ s₂`, the slice is the family slice plus a small correction
      have hs_ge : s₂ ≤ s := le_of_lt (not_le.mp hsle)
      have hψ0 : 0 ≤ (1 - s) ^ (max N 1) := pow_nonneg (by linarith [hs.2]) _
      have hψ_le : (1 - s) ^ (max N 1) ≤ (1 - s₂) ^ (max N 1) :=
        pow_le_pow_left₀ (by linarith [hs.2]) (by linarith) _
      have hbound : (1 - s) ^ (max N 1) * (εr / 4) ≤ (1 - s₂) ^ (max N 1) * (εr / 4) :=
        mul_le_mul_of_nonneg_right hψ_le (by positivity)
      have hzsm : ContDiff ℝ ⊤ (fun t : ℝ => ((1 - s) ^ (max N 1)) • (r' t - r t)) :=
        ContDiff.const_smul _ (hr'.smooth.sub hr.smooth)
      have hzper : Function.Periodic (fun t : ℝ => ((1 - s) ^ (max N 1)) • (r' t - r t)) period := by
        intro t
        simp only [hr'.periodic t, hr.periodic t]
      have hz1 : ∀ t : ℝ, ‖((1 - s) ^ (max N 1)) • (r' t - r t)‖ < ρ := by
        intro t
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hψ0]
        have h4 : ‖r' t - r t‖ < εr / 4 := (hclose t).1
        calc (1 - s) ^ (max N 1) * ‖r' t - r t‖
            ≤ (1 - s) ^ (max N 1) * (εr / 4) :=
              mul_le_mul_of_nonneg_left (le_of_lt h4) hψ0
          _ ≤ (1 - s₂) ^ (max N 1) * (εr / 4) := hbound
          _ < ρ := hN_bound
      have hz2 : ∀ t : ℝ, ‖velocity (fun u : ℝ => ((1 - s) ^ (max N 1)) • (r' u - r u)) t‖ < ρ := by
        intro t
        have hd : DifferentiableAt ℝ (fun u : ℝ => r' u - r u) t :=
          diffAt_of_contDiff_r (hr'.smooth.sub hr.smooth)
        have hderiv : velocity (fun u : ℝ => ((1 - s) ^ (max N 1)) • (r' u - r u)) t
            = ((1 - s) ^ (max N 1)) • velocity (fun u : ℝ => r' u - r u) t :=
          velocity_const_smul_r ((1 - s) ^ (max N 1)) hd
        rw [hderiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hψ0]
        have hsub' : velocity (fun u : ℝ => r' u - r u) t = velocity r' t - velocity r t :=
          velocity_sub_r (diffAt_of_contDiff_r hr'.smooth) (diffAt_of_contDiff_r hr.smooth)
        have h4 : ‖velocity (fun u : ℝ => r' u - r u) t‖ < εr / 4 := by
          rw [hsub']; exact (hclose t).2
        calc (1 - s) ^ (max N 1) * ‖velocity (fun u : ℝ => r' u - r u) t‖
            ≤ (1 - s) ^ (max N 1) * (εr / 4) :=
              mul_le_mul_of_nonneg_left (le_of_lt h4) hψ0
          _ ≤ (1 - s₂) ^ (max N 1) * (εr / 4) := hbound
          _ < ρ := hN_bound
      exact hρ s hs _ hzsm hzper hz1 hz2

end Work.Drive
