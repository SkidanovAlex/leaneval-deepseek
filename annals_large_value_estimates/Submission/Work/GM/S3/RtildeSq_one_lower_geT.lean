import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.RtildeSq_one_lower

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun energy Separated hhat hfun Iterm Spart nzCount)

/-- **Lower bound for the smoothing at `u = 1`, in the regime `T ≤ B_s = (N:ℝ)·B`.**

Unlike `Work.GM.S3.RtildeSq_one_lower` (which needs `B_s ≤ T` and gives `⪰ |W|² B_s/T`, and whose
docstring notes that the `B_s/T` form is false without that hypothesis), here the smoothing window
is *narrower* than the `1/T`-neighbourhood of `1` on which `‖R‖` is large, so the bound is the clean
`⪰ |W|²`.

`RtildeSq W N B ψ₃ ψ₂ 1 = ∫ B_s ψ₃(B_s(1-u')) ψ₂(u') ‖R(u')‖² du'` is an integral of a
non-negative function; on the set `|1-u'| ≤ r := min(δ₂, δ₃/B_s, 1/(4T))` (with `ψ₂ ≥ 1/2` on
`|x-1| ≤ δ₂`, `ψ₃ ≥ 1/2` on `|x| ≤ δ₃`, obtained from continuity and `ψ₂ 1 = ψ₃ 0 = 1`) one has
`|log |u'|| ≤ 2|u'-1| ≤ 1/(2T)`, so `‖R(u')‖ ≥ |W|/2` by `Rfun_lower_near_one`
(`Submission/Work/GM/S3/Defs.lean`); hence `RtildeSq(1) ≥ 2r·B_s·|W|²/16`, and
`2 r B_s ≥ 2·min(δ₂, δ₃, 1/4) > 0` because `B_s ≥ T ≥ 1` and `T ≤ B_s`.  (Same technique as
`Submission/Work/GM/S3/RtildeSq_one_lower.lean`; only the choice of `r` and the final arithmetic
change.) -/
theorem RtildeSq_one_lower_geT (ψ₂ ψ₃ : ℝ → ℝ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (h₂ : Work.GM.S3.IsBumpAtOne ψ₂ C₀) (h₃ : Work.GM.S3.IsBumpAtZero ψ₃ C₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ (W : Finset ℝ) (N : ℕ) (T B : ℝ), 1 ≤ T → (∀ t ∈ W, |t| ≤ T) →
      1 ≤ (N : ℝ) * B → T ≤ (N : ℝ) * B →
      c * (W.card : ℝ) ^ 2 ≤ Work.GM.S3.RtildeSq W N B ψ₃ ψ₂ 1 := by
  unfold IsBumpAtOne at h₂
  unfold IsBumpAtZero at h₃
  obtain ⟨hcont₂, hnn₂, hsupp₂, hval₂, _⟩ := h₂
  obtain ⟨hcont₃, hnn₃, hsupp₃, hval₃, _⟩ := h₃
  have hc₂ : Continuous ψ₂ := hcont₂.continuous
  have hc₃ : Continuous ψ₃ := hcont₃.continuous
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  -- `ψ₂ ≥ 1/2` near `1`
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x - 1| ≤ δ → (1 : ℝ) / 2 ≤ ψ₂ x := by
    obtain ⟨ε, hεpos, hε⟩ :=
      (Metric.continuousAt_iff.mp (hc₂.continuousAt (x := (1 : ℝ)))) (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun x hx => ?_⟩
    have hd : dist x (1 : ℝ) < ε := by rw [Real.dist_eq]; linarith
    have h := hε hd
    rw [Real.dist_eq, hval₂] at h
    have := neg_abs_le (ψ₂ x - 1)
    linarith
  -- `ψ₃ ≥ 1/2` near `0`
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ :
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| ≤ δ → (1 : ℝ) / 2 ≤ ψ₃ x := by
    obtain ⟨ε, hεpos, hε⟩ :=
      (Metric.continuousAt_iff.mp (hc₃.continuousAt (x := (0 : ℝ)))) (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun x hx => ?_⟩
    have hd : dist x (0 : ℝ) < ε := by rw [Real.dist_eq, sub_zero]; linarith
    have h := hε hd
    rw [Real.dist_eq, hval₃] at h
    have := neg_abs_le (ψ₃ x - 1)
    linarith
  set m : ℝ := min δ₂ (min δ₃ (1 / 4)) with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    exact lt_min hδ₂pos (lt_min hδ₃pos (by norm_num))
  have hm2 : m ≤ δ₂ := by rw [hmdef]; exact min_le_left _ _
  have hm3 : m ≤ δ₃ := by
    rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hm4 : m ≤ (1 : ℝ) / 4 := by
    rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨m / 8, by positivity, ?_⟩
  intro W N T B hT hW hBs1 hBsT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  set Bs : ℝ := (N : ℝ) * B with hBsdef
  have hBspos : 0 < Bs := lt_of_lt_of_le zero_lt_one hBs1
  have hBsge1 : 1 ≤ Bs := hBs1
  -- the smoothing window radius
  set r : ℝ := min δ₂ (min (δ₃ / Bs) (1 / (4 * T))) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact lt_min hδ₂pos (lt_min (div_pos hδ₃pos hBspos) (by positivity))
  have hr2 : r ≤ δ₂ := by rw [hrdef]; exact min_le_left _ _
  have hr3 : Bs * r ≤ δ₃ := by
    have hmin : r ≤ δ₃ / Bs := by
      rw [hrdef]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    calc Bs * r ≤ Bs * (δ₃ / Bs) := mul_le_mul_of_nonneg_left hmin hBspos.le
      _ = δ₃ := by field_simp
  have hr4 : r ≤ 1 / (4 * T) := by
    rw [hrdef]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hr1 : r ≤ 1 / 4 := by
    refine le_trans hr4 ?_
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * T) (by norm_num : (0 : ℝ) < 4)]
    linarith
  -- the window is wide enough
  have hmr : m ≤ r * Bs := by
    have hmul : r * Bs = min (δ₂ * Bs) (min δ₃ (Bs / (4 * T))) := by
      rw [hrdef, min_mul_of_nonneg _ _ hBspos.le, min_mul_of_nonneg _ _ hBspos.le,
        div_mul_cancel₀ δ₃ hBspos.ne']
      ring_nf
    rw [hmul]
    refine min_le_min ?_ (min_le_min le_rfl ?_)
    · nlinarith [hδ₂pos.le, hBsge1]
    · rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity : (0 : ℝ) < 4 * T)]
      nlinarith [hBsT]
  -- the enclosing interval and the small interval
  set A : ℝ := min (1 / C₀) (3 / 4) with hAdef
  set Bb : ℝ := max C₀ (5 / 4) with hBbdef
  have hAle' : A ≤ 1 / C₀ := by rw [hAdef]; exact min_le_left _ _
  have hA34 : A ≤ 3 / 4 := by rw [hAdef]; exact min_le_right _ _
  have hC₀le : C₀ ≤ Bb := by rw [hBbdef]; exact le_max_left _ _
  have hB54 : (5 : ℝ) / 4 ≤ Bb := by rw [hBbdef]; exact le_max_right _ _
  have hApos : 0 < A := by
    rw [hAdef]; exact lt_min (by positivity) (by norm_num)
  have hAB : A ≤ Bb := by
    refine le_trans hAle' (le_trans ?_ hC₀le)
    rw [div_le_iff₀ hC₀pos]
    nlinarith [hC₀]
  have hAle : A ≤ 1 - r := by linarith [hA34, hr1]
  have hBB : 1 + r ≤ Bb := by linarith [hB54, hr1]
  have hrr : 1 - r ≤ 1 + r := by linarith [hrpos]
  let F : ℝ → ℝ := fun u' => Bs * ψ₃ (Bs * (1 - u')) * ψ₂ u' * ‖Rfun W u'‖ ^ 2
  have hFsupp : ∀ u' : ℝ, u' ∉ Set.Icc A Bb → F u' = 0 := by
    intro u' hu'
    have h2 : ψ₂ u' = 0 := by
      by_contra hne
      exact hu' (Set.Icc_subset_Icc hAle' hC₀le (hsupp₂ u' hne))
    simp [F, h2]
  have hFnonneg : ∀ u' : ℝ, 0 ≤ F u' := by
    intro u'
    simp only [F]
    exact mul_nonneg (mul_nonneg (mul_nonneg hBspos.le (hnn₃ _)) (hnn₂ _)) (sq_nonneg _)
  have hFnonneg_ae : 0 ≤ᵐ[volume.restrict (Set.Ioc A Bb)] F := Filter.Eventually.of_forall hFnonneg
  -- continuity of `F` on the positive interval
  have hFcont : ContinuousOn F (Set.uIcc A Bb) := by
    rw [Set.uIcc_of_le hAB]
    have hposint : ∀ x ∈ Set.Icc A Bb, 0 < x := fun x hx => lt_of_lt_of_le hApos hx.1
    have hsum : ContinuousOn
        (fun x : ℝ => ∑ t ∈ W, (((x : ℝ) : ℂ) ^ (I * (t : ℂ)))) (Set.Icc A Bb) :=
      continuousOn_finsetSum W (f := fun (t : ℝ) (x : ℝ) => (((x : ℝ) : ℂ) ^ (I * (t : ℂ))))
        (fun t ht => ContinuousOn.cpow_const (f := fun x : ℝ => ((x : ℝ) : ℂ))
          Complex.continuous_ofReal.continuousOn
          (fun x hx => Complex.ofReal_mem_slitPlane.mpr (hposint x hx)))
    have hnorm2 : ContinuousOn
        (fun x : ℝ => ‖∑ t ∈ W, (((x : ℝ) : ℂ) ^ (I * (t : ℂ)))‖ ^ 2) (Set.Icc A Bb) :=
      hsum.norm.pow 2
    have hcontprod : Continuous fun x : ℝ => Bs * ψ₃ (Bs * (1 - x)) * ψ₂ x :=
      ((continuous_const : Continuous fun _ : ℝ => Bs).mul
        (hc₃.comp ((continuous_const : Continuous fun _ : ℝ => Bs).mul
          ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).sub continuous_id)))).mul hc₂
    have hmain : ContinuousOn (fun x : ℝ => Bs * ψ₃ (Bs * (1 - x)) * ψ₂ x *
        ‖∑ t ∈ W, (((x : ℝ) : ℂ) ^ (I * (t : ℂ)))‖ ^ 2) (Set.Icc A Bb) :=
      hcontprod.continuousOn.mul hnorm2
    refine hmain.congr (fun x hx => ?_)
    have hxabs : |x| = x := abs_of_pos (hposint x hx)
    have hRfun : Rfun W x = ∑ t ∈ W, (((x : ℝ) : ℂ) ^ (I * (t : ℂ))) := by
      simp only [Rfun]
      exact Finset.sum_congr rfl (fun t ht => by rw [hxabs])
    show Bs * ψ₃ (Bs * (1 - x)) * ψ₂ x * ‖Rfun W x‖ ^ 2 =
      Bs * ψ₃ (Bs * (1 - x)) * ψ₂ x * ‖∑ t ∈ W, (((x : ℝ) : ℂ) ^ (I * (t : ℂ)))‖ ^ 2
    rw [hRfun]
  -- pointwise lower bound on the small interval
  have hmono_on : ∀ x ∈ Set.Icc (1 - r) (1 + r),
      Bs * (W.card : ℝ) ^ 2 / 16 ≤ F x := by
    intro x hx
    obtain ⟨hxl, hxr⟩ := hx
    have hxabs : |x - 1| ≤ r := by rw [abs_le]; constructor <;> linarith
    have hxpos : 0 < x := by linarith [hxl, hr1]
    have hpsi2 : (1 : ℝ) / 2 ≤ ψ₂ x := hδ₂ x (by linarith [hxabs, hr2])
    have hpsi3 : (1 : ℝ) / 2 ≤ ψ₃ (Bs * (1 - x)) := by
      apply hδ₃
      rw [abs_mul, abs_of_nonneg hBspos.le]
      calc Bs * |1 - x| ≤ Bs * r :=
            mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hxabs) hBspos.le
        _ ≤ δ₃ := hr3
    have hlog : abs (Real.log |x|) ≤ 1 / (2 * T) := by
      rw [abs_of_pos hxpos]
      have hx1le : |x - 1| ≤ 1 / 2 := by linarith [hxabs, hr1]
      have h2 : |Real.log (1 + (x - 1))| ≤ 2 * |x - 1| := abs_log_one_add_le hx1le
      have h3 : 2 * |x - 1| ≤ 1 / (2 * T) := by
        have h4 : 2 * r ≤ 2 * (1 / (4 * T)) := by linarith [hr4]
        have h5 : 2 * (1 / (4 * T)) = 1 / (2 * T) := by field_simp; ring
        linarith
      have hxeq : x = 1 + (x - 1) := by ring
      rw [hxeq]
      exact le_trans h2 h3
    have hR := Rfun_lower_near_one W hTpos hW (ne_of_gt hxpos) hlog
    have hsq : ((W.card : ℝ) / 2) ^ 2 ≤ ‖Rfun W x‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hR 2
    have hstep1 : Bs * (1 / 2) * (1 / 2) ≤ Bs * ψ₃ (Bs * (1 - x)) * ψ₂ x :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpsi3 hBspos.le) hpsi2 (by norm_num) (by positivity)
    have hstep2 : Bs * (1 / 2) * (1 / 2) * ((W.card : ℝ) / 2) ^ 2 ≤
        Bs * ψ₃ (Bs * (1 - x)) * ψ₂ x * ‖Rfun W x‖ ^ 2 :=
      mul_le_mul hstep1 hsq (by positivity) (by positivity)
    have heq : Bs * (W.card : ℝ) ^ 2 / 16 =
        Bs * (1 / 2) * (1 / 2) * ((W.card : ℝ) / 2) ^ 2 := by ring
    show Bs * (W.card : ℝ) ^ 2 / 16 ≤ Bs * ψ₃ (Bs * (1 - x)) * ψ₂ x * ‖Rfun W x‖ ^ 2
    rw [heq]
    exact hstep2
  have hF_ind : F = (Set.Icc A Bb).indicator F := by
    funext u'
    by_cases h : u' ∈ Set.Icc A Bb
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, hFsupp u' h]
  have hInt1 : ∫ u', F u' = ∫ x in A..Bb, F x := by
    have h1 : ∫ u', F u' = ∫ x in Set.Icc A Bb, F x := by
      conv_lhs => rw [hF_ind]
      exact MeasureTheory.integral_indicator measurableSet_Icc
    rw [h1, MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm,
      ← intervalIntegral.integral_of_le hAB]
  have hFintAB : IntervalIntegrable F volume A Bb := hFcont.intervalIntegrable
  have hFintR : IntervalIntegrable F volume (1 - r) (1 + r) :=
    (hFcont.mono (by
      intro x hx
      rw [Set.uIcc_of_le hrr, Set.mem_Icc] at hx
      rw [Set.uIcc_of_le hAB, Set.mem_Icc]
      exact ⟨le_trans hAle hx.1, le_trans hx.2 hBB⟩)).intervalIntegrable
  have hstepAB : ∫ x in (1 - r)..(1 + r), F x ≤ ∫ x in A..Bb, F x :=
    intervalIntegral.integral_mono_interval (f := F) (μ := volume) hAle hrr hBB
      hFnonneg_ae hFintAB
  have hintc : IntervalIntegrable (fun _ : ℝ => Bs * (W.card : ℝ) ^ 2 / 16) volume
      (1 - r) (1 + r) := intervalIntegrable_const
  have hstep3 : ∫ x in (1 - r)..(1 + r), (fun _ : ℝ => Bs * (W.card : ℝ) ^ 2 / 16) x ≤
      ∫ x in (1 - r)..(1 + r), F x :=
    intervalIntegral.integral_mono_on (f := fun _ : ℝ => Bs * (W.card : ℝ) ^ 2 / 16) (g := F)
      (μ := volume) hrr hintc hFintR hmono_on
  have hmain_ineq : m / 8 * (W.card : ℝ) ^ 2 ≤ ∫ u', F u' := by
    have hlow : 2 * r * (Bs * (W.card : ℝ) ^ 2 / 16) ≤ ∫ u', F u' := by
      calc 2 * r * (Bs * (W.card : ℝ) ^ 2 / 16)
          = ∫ x in (1 - r)..(1 + r), (fun _ : ℝ => Bs * (W.card : ℝ) ^ 2 / 16) x := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
        _ ≤ ∫ x in (1 - r)..(1 + r), F x := hstep3
        _ ≤ ∫ x in A..Bb, F x := hstepAB
        _ = ∫ u', F u' := hInt1.symm
    have hmr' : m ≤ r * Bs := hmr
    have h2 : m / 8 * (W.card : ℝ) ^ 2 ≤ (r * Bs / 8) * (W.card : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith
    have h3 : 2 * r * (Bs * (W.card : ℝ) ^ 2 / 16) = (r * Bs / 8) * (W.card : ℝ) ^ 2 := by
      ring
    linarith [hlow, h2, h3.le, h3.ge]
  have hgoal_eq : (∫ u', F u') = RtildeSq W N B ψ₃ ψ₂ 1 := by
    have hFfun : (fun u' : ℝ => F u') =
        (fun u' : ℝ => (N : ℝ) * B * ψ₃ ((N : ℝ) * B * (1 - u')) * ψ₂ u' *
          ‖Rfun W u'‖ ^ 2) := by
      funext u'
      simp only [F, hBsdef]
    rw [hFfun]
    rfl
  rw [← hgoal_eq]
  exact hmain_ineq

end Work.GM.S3
