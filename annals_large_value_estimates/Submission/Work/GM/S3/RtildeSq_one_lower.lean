import Mathlib
import Submission.Work.GM.S3.Defs

/-!
# GM §7: the smoothing `R̃` is `≫ |W|² B_s / T` at `u = 1`

`RtildeSq W N B ψ₃ ψ₂ u = ∫ (N B) ψ₃ ((N B) (u - u')) ψ₂ u' ‖R(u')‖² du'`; at `u = 1` the
integrand is large on the interval `|u' - 1| ≲ 1/T`: `ψ₂ ≫ 1` near `1`, `ψ₃ ≫ 1` near `0` and
`‖R(u')‖ ≥ |W|/2` for `|log |u'|| ≤ 1/(2T)` when `W ⊆ [-T,T]`.  The hypothesis `N B ≤ T` is what
makes that interval shorter than `1`.
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun energy Separated hhat hfun Iterm Spart nzCount)

/-- `|log (1 + x)| ≤ 2|x|` on `|x| ≤ 1/2`. -/
lemma abs_log_one_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) : |Real.log (1 + x)| ≤ 2 * |x| := by
  have hxge : -(1 / 2 : ℝ) ≤ x := by linarith [neg_abs_le x]
  have h1x : 0 < 1 + x := by linarith
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hinv : Real.log ((1 + x)⁻¹) = -Real.log (1 + x) := Real.log_inv _
    have hpos : 0 < (1 + x)⁻¹ := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have h2 : (1 + x)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have h3 : (1 + x)⁻¹ - 1 ≤ 2 * |x| := by
      have h4 : (1 + x)⁻¹ - 1 = (-x) * (1 + x)⁻¹ := by field_simp; ring
      rw [h4]
      calc (-x) * (1 + x)⁻¹ ≤ |x| * (1 + x)⁻¹ :=
            mul_le_mul_of_nonneg_right (neg_le_abs x) (by positivity)
        _ ≤ |x| * 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg x)
        _ = 2 * |x| := by ring
    have h5 : Real.log ((1 + x)⁻¹) ≤ 2 * |x| := le_trans h h3
    rw [hinv] at h5
    linarith
  · have h := Real.log_le_sub_one_of_pos h1x
    have h2 : x ≤ 2 * |x| := by linarith [le_abs_self x, abs_nonneg x]
    linarith

/-- **Lower bound for the smoothing at `u = 1`.** With `1 ≤ T`, `W ⊆ [-T,T]` and
`1 ≤ B_s = N·B ≤ T`, we have `RtildeSq W N B ψ₃ ψ₂ 1 ⪰ |W|² B_s / T` with a constant depending only
on the bumps.  Reason: `ψ₂ ≥ 1/2` near `1` (continuity, `ψ₂ 1 = 1`), `ψ₃ ≥ 1/2` near `0`
(`ψ₃ 0 = 1`), and `‖Rfun W v‖ ≥ |W|/2` for `|log |v|| ≤ 1/(2T)`
(`Rfun_lower_near_one` in `Defs.lean`); on the interval `|1 - u'| ≤ r` with
`r = min(δ₂, δ₃/B_s, 1/(4T)) > 0` (length `≍ 1/T` when `B_s ≤ T`, using
`(N:ℝ) * B ≤ T`) the integrand is `≥ B_s |W|²/8`.  Note the hypothesis `(N:ℝ) * B ≤ T` is
ESSENTIAL: without it the statement is false (take `W = {0}`, `T = 1`, `B → ∞`: then
`RtildeSq ... 1 → |W|² ∫ψ₃` is bounded, while the RHS grows like `B`). -/
theorem RtildeSq_one_lower : ∀ (ψ₂ ψ₃ : ℝ → ℝ) (C₀ : ℝ), 1 ≤ C₀ → IsBumpAtOne ψ₂ C₀ →
    IsBumpAtZero ψ₃ C₀ →
    ∃ c : ℝ, 0 < c ∧ ∀ (W : Finset ℝ) (N : ℕ) (T B : ℝ), 1 ≤ T → (∀ t ∈ W, |t| ≤ T) →
      1 ≤ (N : ℝ) * B → (N : ℝ) * B ≤ T →
      c * (W.card : ℝ) ^ 2 * ((N : ℝ) * B) / T ≤ RtildeSq W N B ψ₃ ψ₂ 1 := by
  intro ψ₂ ψ₃ C₀ hC₀ hψ₂ hψ₃
  unfold IsBumpAtOne at hψ₂
  unfold IsBumpAtZero at hψ₃
  obtain ⟨hcont₂, hnn₂, hsupp₂, hval₂, _⟩ := hψ₂
  obtain ⟨hcont₃, hnn₃, hsupp₃, hval₃, _⟩ := hψ₃
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
  have hm3 : m ≤ δ₃ := by rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hm4 : m ≤ (1 : ℝ) / 4 := by
    rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨m / 8, by positivity, ?_⟩
  intro W N T B hT hW hBs1 hBs2
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  set Bs : ℝ := (N : ℝ) * B with hBsdef
  have hBspos : 0 < Bs := lt_of_lt_of_le zero_lt_one hBs1
  set r : ℝ := m / T with hrdef
  have hrpos : 0 < r := by positivity
  have hr1 : r ≤ 1 / 4 := by
    rw [hrdef, div_le_iff₀ hTpos]
    nlinarith [hm4, hT]
  have hr2 : r ≤ δ₂ := by
    have h : r ≤ m := by rw [hrdef]; exact div_le_self hmpos.le hT
    linarith [hm2]
  have hr3 : Bs * r ≤ δ₃ := by
    have h1 : r ≤ δ₃ / Bs := by
      have ha : r ≤ δ₃ / T := by
        rw [hrdef]; exact div_le_div_of_nonneg_right hm3 hTpos.le
      refine le_trans ha ?_
      rw [div_le_div_iff₀ hTpos hBspos]
      nlinarith [hBs2, hδ₃pos.le]
    calc Bs * r ≤ Bs * (δ₃ / Bs) := mul_le_mul_of_nonneg_left h1 hBspos.le
      _ = δ₃ := by field_simp
  have hr4 : r ≤ 1 / (4 * T) := by
    rw [hrdef, div_le_div_iff₀ hTpos (by positivity)]
    nlinarith [hm4, hTpos]
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
  have hmain_ineq : m / 8 * (W.card : ℝ) ^ 2 * Bs / T ≤ ∫ u', F u' := by
    calc m / 8 * (W.card : ℝ) ^ 2 * Bs / T
        = 2 * r * (Bs * (W.card : ℝ) ^ 2 / 16) := by rw [hrdef]; ring_nf
      _ = ∫ x in (1 - r)..(1 + r), (fun _ : ℝ => Bs * (W.card : ℝ) ^ 2 / 16) x := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ ∫ x in (1 - r)..(1 + r), F x := hstep3
      _ ≤ ∫ x in A..Bb, F x := hstepAB
      _ = ∫ u', F u' := hInt1.symm
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
