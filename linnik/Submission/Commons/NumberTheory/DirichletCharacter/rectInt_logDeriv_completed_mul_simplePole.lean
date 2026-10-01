import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_completed_tentF_eq

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

/-- `rectInt` of a finite sum of simple-pole kernels `c v / (s - v)`, the points `v`
avoiding the boundary. -/
lemma rectInt_finset_div_sub {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (S : Finset ℂ) (hS_nb : ∀ v ∈ S, v ∉ rectBoundary z w) (c : ℂ → ℂ) :
    rectInt z w (fun s => ∑ v ∈ S, c v / (s - v)) =
      ∑ v ∈ S, c v * (if z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im then
        2 * (Real.pi : ℂ) * Complex.I else 0) := by
  have hcont : ∀ v ∈ S, ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ => c v / (s - v)) s := by
    intro v hv s hs
    have hsv : s - v ≠ 0 := sub_ne_zero.mpr (fun h => hS_nb v hv (h ▸ hs))
    exact ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) hsv
  rw [rectInt_finset_sum_of_boundary S hcont]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  by_cases hvin : z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im
  · rw [if_pos hvin, rectInt_const_div_sub_inside (c v) hzre hzim hvin]
  · rw [if_neg hvin, rectInt_const_div_sub_outside (c v) hzre hzim
      (outside_of_not_inside hzre hzim hvin (hS_nb v hv)), mul_zero]

/-- `rectInt` of `(∑ v ∈ S, d v (1/(s-v)+1/v)) / (s-u)` for `u` strictly inside the
rectangle and not in `S`. -/
lemma rectInt_kernel_finset_div_sub {z w u : ℂ}
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im)
    (S : Finset ℂ) (hS_ne : ∀ v ∈ S, v ≠ 0) (hS_nb : ∀ v ∈ S, v ∉ rectBoundary z w)
    (hu_nS : u ∉ S) (d : ℂ → ℂ) :
    rectInt z w (fun s => (∑ v ∈ S, d v * (1 / (s - v) + 1 / v)) / (s - u)) =
      2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v ∈ S, d v * (1 / (u - v) + 1 / v)) +
          ∑ v ∈ S, d v * (if z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im then
            1 / (v - u) else 0)) := by
  let FR : ℂ → ℂ := fun s => ∑ v ∈ S, d v * (1 / (s - v) + 1 / v)
  have hFRu : FR u = ∑ v ∈ S, d v * (1 / (u - v) + 1 / v) := rfl
  have hpt : ∀ s ∈ rectBoundary z w,
      FR s / (s - u) =
        (∑ v ∈ S, (d v / (v - u)) / (s - v)) + FR u / (s - u) := by
    intro s hs
    have hsu : s ≠ u := ne_of_mem_rectBoundary_of_inside huin hs
    have hsv : ∀ v ∈ S, s ≠ v := fun v hv h => hS_nb v hv (h ▸ hs)
    have huv : ∀ v ∈ S, u - v ≠ 0 := by
      intro v hv h
      exact hu_nS (sub_eq_zero.mp h ▸ hv)
    have hvu : ∀ v ∈ S, v - u ≠ 0 := by
      intro v hv h
      rw [sub_eq_zero] at h
      exact hu_nS (h ▸ hv)
    have hsub : FR s - FR u = ∑ v ∈ S, d v * (1 / (s - v) - 1 / (u - v)) := by
      dsimp only [FR]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    have hmain : (FR s - FR u) / (s - u) = ∑ v ∈ S, (d v / (v - u)) / (s - v) := by
      rw [hsub, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v hv
      have hs1 : s - v ≠ 0 := sub_ne_zero.mpr (hsv v hv)
      have hs2 : u - v ≠ 0 := huv v hv
      have hs2' : v - u ≠ 0 := hvu v hv
      have hs3 : s - u ≠ 0 := sub_ne_zero.mpr hsu
      field_simp
      ring
    rw [show FR s / (s - u) = (FR s - FR u) / (s - u) + FR u / (s - u) by
          rw [← add_div]; ring, hmain]
  have hcont1 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
      ∑ v ∈ S, (d v / (v - u)) / (s - v)) s := by
    intro s hs
    refine tendsto_finsetSum _ ?_
    intro v hv
    have hsv : s - v ≠ 0 := sub_ne_zero.mpr (fun h => hS_nb v hv (h ▸ hs))
    exact ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) hsv
  have hcont2 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ => FR u / (s - u)) s := by
    intro s hs
    have hsu : s - u ≠ 0 := sub_ne_zero.mpr (ne_of_mem_rectBoundary_of_inside huin hs)
    exact ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) hsu
  obtain ⟨a1, a2, a3, a4⟩ := intervalIntegrable_of_boundary_continuousAt hcont1
  obtain ⟨b1, b2, b3, b4⟩ := intervalIntegrable_of_boundary_continuousAt hcont2
  have hcongr : rectInt z w (fun s => FR s / (s - u)) =
      rectInt z w (fun s => (∑ v ∈ S, (d v / (v - u)) / (s - v)) + FR u / (s - u)) :=
    rectInt_congr_boundary' hpt
  rw [hcongr, rectInt_add'' a1 b1 a2 b2 a3 b3 a4 b4,
    rectInt_finset_div_sub hzre hzim S hS_nb (fun v => d v / (v - u)),
    rectInt_const_div_sub_inside (FR u) hzre hzim huin]
  have h1 : (∑ v ∈ S, (d v / (v - u)) *
        (if z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im then
          2 * (Real.pi : ℂ) * Complex.I else 0)) =
      2 * (Real.pi : ℂ) * Complex.I *
        (∑ v ∈ S, d v * (if z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im then
          1 / (v - u) else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hvin : z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im
    · rw [if_pos hvin, if_pos hvin]; ring
    · rw [if_neg hvin, if_neg hvin]; ring
  rw [h1, hFRu, mul_add]
  ring

/-- Additivity of `rectInt` for functions continuous at every boundary point. -/
lemma rectInt_add_of_boundary_continuousAt {z w : ℂ} {f g : ℂ → ℂ}
    (hf : ∀ s ∈ rectBoundary z w, ContinuousAt f s)
    (hg : ∀ s ∈ rectBoundary z w, ContinuousAt g s) :
    rectInt z w (fun s => f s + g s) = rectInt z w f + rectInt z w g := by
  obtain ⟨a1, a2, a3, a4⟩ := intervalIntegrable_of_boundary_continuousAt hf
  obtain ⟨b1, b2, b3, b4⟩ := intervalIntegrable_of_boundary_continuousAt hg
  exact rectInt_add'' a1 b1 a2 b2 a3 b3 a4 b4

/-- `logDeriv` is continuous at a point where the function is analytic and nonzero. -/
lemma continuousAt_logDeriv_of_analyticAt {f : ℂ → ℂ} {s : ℂ}
    (han : AnalyticAt ℂ f s) (h : f s ≠ 0) :
    ContinuousAt (fun s => logDeriv f s) s := by
  rw [show (fun s => logDeriv f s) = fun s => deriv f s / f s from
    funext (fun s => logDeriv_apply _ _)]
  exact (han.deriv.continuousAt).div han.continuousAt h

theorem rectInt_logDeriv_completed_mul_simplePole {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {G : ℂ → ℂ} {s₀ : ℂ} {r : ℂ}
    (hG : Differentiable ℂ (fun u => G u - r / (u - s₀)))
    {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im)
    (hs0in : z.re < s₀.re ∧ s₀.re < w.re ∧ z.im < s₀.im ∧ s₀.im < w.im)
    (hΛs0 : DirichletCharacter.completedLFunction χ s₀ ≠ 0)
    (hins : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
      z.re < ρ.re ∧ ρ.re < w.re)
    (hnz : ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectBoundary z w,
      DirichletCharacter.completedLFunction χ s ≠ 0)
    {M : ℝ} (hMb : ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectSet z w,
      ‖G s - r / (s - s₀)‖ ≤ M) :
    Commons.NumberTheory.DirichletCharacter.rectInt z w
        (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s * G s) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
            ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
              G ρ else 0))
          + logDeriv (DirichletCharacter.completedLFunction χ) s₀ * r) := by
  obtain ⟨c, hc0, hc⟩ := partialFraction_limit_bound χ hχ hχprim
  have hzre' : z.re < 0 := h0in.1
  have hwre' : 0 < w.re := h0in.2.1
  have hzim' : z.im < 0 := h0in.2.2.1
  have hwim' : 0 < w.im := h0in.2.2.2
  let H : ℂ → ℂ := fun u => G u - r / (u - s₀)
  have hH : Differentiable ℂ H := hG
  have hHbound : ∀ s ∈ rectSet z w, ‖H s‖ ≤ M := by
    intro s hs; simpa only [H] using hMb s hs
  set K : ℝ := |z.re| + |w.re| + |z.im| + |w.im| + 1 with hK
  set δ : ℝ := min (s₀.re - z.re) (min (w.re - s₀.re) (min (s₀.im - z.im) (w.im - s₀.im)))
    with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (by linarith [hs0in.1])
      (lt_min (by linarith [hs0in.2.1])
        (lt_min (by linarith [hs0in.2.2.1]) (by linarith [hs0in.2.2.2])))
  have hdist : ∀ s ∈ rectBoundary z w, δ ≤ ‖s - s₀‖ := by
    intro s hs
    have him_le : |s.im - s₀.im| ≤ ‖s - s₀‖ := by
      simpa using Complex.abs_im_le_norm (s - s₀)
    have hre_le : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa using Complex.abs_re_le_norm (s - s₀)
    rw [hδ]
    rcases hs with ⟨hre, him | him⟩ | ⟨him, hre | hre⟩
    · rw [him] at him_le
      rw [abs_of_neg (by linarith [hs0in.2.2.1]), neg_sub] at him_le
      exact le_trans (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))) him_le
    · rw [him] at him_le
      rw [abs_of_pos (by linarith [hs0in.2.2.2])] at him_le
      exact le_trans (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))) him_le
    · rw [hre] at hre_le
      rw [abs_of_neg (by linarith [hs0in.1]), neg_sub] at hre_le
      exact le_trans (min_le_left _ _) hre_le
    · rw [hre] at hre_le
      rw [abs_of_pos (by linarith [hs0in.2.1])] at hre_le
      exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) hre_le
  have hnorm_le : ∀ s ∈ rectSet z w, ‖s‖ ≤ K := by
    intro s hs
    rw [hK]
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hs
    rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
    rw [Set.uIcc_of_le (le_of_lt hzim)] at him
    have h1 : |s.re| ≤ |z.re| + |w.re| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le z.re, hre.1, abs_nonneg w.re],
        by linarith [le_abs_self w.re, hre.2, abs_nonneg z.re]⟩
    have h2 : |s.im| ≤ |z.im| + |w.im| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le z.im, him.1, abs_nonneg w.im],
        by linarith [le_abs_self w.im, him.2, abs_nonneg z.im]⟩
    have h3 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    linarith
  have hinside_norm : ∀ ρ : ℂ, z.re < ρ.re → ρ.re < w.re → z.im < ρ.im → ρ.im < w.im →
      ‖ρ‖ ≤ K := by
    intro ρ h1 h2 h3 h4
    rw [hK]
    have hre : |ρ.re| ≤ |z.re| + |w.re| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le z.re, h1, abs_nonneg w.re],
        by linarith [le_abs_self w.re, h2, abs_nonneg z.re]⟩
    have him : |ρ.im| ≤ |z.im| + |w.im| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le z.im, h3, abs_nonneg w.im],
        by linarith [le_abs_self w.im, h4, abs_nonneg z.im]⟩
    have h5 : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    linarith
  have hG_boundary : ∀ s ∈ rectBoundary z w, ‖G s‖ ≤ M + ‖r‖ / δ := by
    intro s hs
    have hHle : ‖H s‖ ≤ M := hHbound s (rectBoundary_subset_rectSet hzre hzim hs)
    have hGeq : G s = H s + r / (s - s₀) := by simp only [H]; ring
    have hdiv : ‖r / (s - s₀)‖ ≤ ‖r‖ / δ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg r) hδpos (hdist s hs)
    rw [hGeq]
    linarith [norm_add_le (H s) (r / (s - s₀)), hHle, hdiv]
  have hkey : ∀ R : ℝ, 2 ≤ R → K ≤ R / 4 →
      ‖rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s * G s) -
        (2 * (Real.pi : ℂ) * Complex.I) *
          ((∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
              ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) * G ρ
              else 0))
            + logDeriv (DirichletCharacter.completedLFunction χ) s₀ * r)‖ ≤
        2 * ((w.re - z.re) + (w.im - z.im)) *
            ((c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) * (M + ‖r‖ / δ))
          + 2 * Real.pi * ‖r‖ * (c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) := by
    intro R hR hR4
    have hRpos : (0 : ℝ) < R := by linarith
    have hlog0g : (0 : ℝ) ≤ Real.log (R + 2) + Real.log (N : ℝ) + 2 := by
      have h3 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by
        exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ R + 2)]
    let dR : ℂ → ℤ := fun v => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R) v
    have hdRfin : dR.support.Finite := by
      simpa only [dR] using
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall (0 : ℂ) R)
    let S : Finset ℂ := hdRfin.toFinset
    have hS_mem : ∀ u : ℂ, u ∈ S ↔ dR u ≠ 0 := fun u => hdRfin.mem_toFinset
    have hS_zero : ∀ u ∈ S, DirichletCharacter.completedLFunction χ u = 0 := by
      intro u hu
      have hnorm : ‖u‖ ≤ R := by
        by_contra hcon
        refine (hS_mem u).mp hu ?_
        dsimp only [dR]
        exact (MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem
          (fun hmem => hcon (by simpa [dist_eq_norm] using hmem))
      refine eq_zero_of_divisor_ne_zero (U := Metric.closedBall 0 R)
        (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z)
        (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hnorm)) ?_
      simpa only [dR] using (hS_mem u).mp hu
    have hS_ne : ∀ u ∈ S, u ≠ 0 := by
      intro u hu h0
      exact Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
        (h0 ▸ hS_zero u hu)
    have hS_nb : ∀ u ∈ S, u ∉ rectBoundary z w := by
      intro u hu hb
      exact hnz u hb (hS_zero u hu)
    have hS_norm : ∀ u ∈ S, ‖u‖ ≤ R := by
      intro u hu
      by_contra hcon
      have h0 : dR u = 0 := by
        dsimp only [dR]
        exact (MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem
          (fun hmem => hcon (by simpa [dist_eq_norm] using hmem))
      exact (hS_mem u).mp hu h0
    have hs0_notin_S : s₀ ∉ S := fun h => hΛs0 (hS_zero s₀ h)
    let FR : ℂ → ℂ := fun s => ∑ v ∈ S, ((dR v : ℤ) : ℂ) * (1 / (s - v) + 1 / v)
    let TR : ℂ → ℂ := fun s => logDeriv (DirichletCharacter.completedLFunction χ) s -
      logDeriv (DirichletCharacter.completedLFunction χ) 0 - FR s
    have hFR_eq : ∀ s : ℂ, FR s =
        ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) * (1 / (s - u) + 1 / u) := by
      intro s
      dsimp only [FR]
      refine (finsum_eq_sum_of_support_subset _ ?_).symm
      intro u hu
      rw [Function.mem_support] at hu
      exact (hS_mem u).mpr (fun hz => hu (by simp [hz]))
    -- abbreviated finite sums
    set SH : ℂ := ∑ v ∈ S, ((dR v : ℤ) : ℂ) *
      (if z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im then H v else 0)
      with hSH
    set S1 : ℂ := ∑ v ∈ S, ((dR v : ℤ) : ℂ) *
      (if z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im then 1 / (v - s₀) else 0)
      with hS1
    set FRs0 : ℂ := ∑ v ∈ S, ((dR v : ℤ) : ℂ) * (1 / (s₀ - v) + 1 / v) with hFRs0
    have hTRs0 : TR s₀ = logDeriv (DirichletCharacter.completedLFunction χ) s₀ -
        logDeriv (DirichletCharacter.completedLFunction χ) 0 - FRs0 := by
      dsimp only [TR, FR]
    -- continuity on the boundary
    have hFRcont : ∀ s ∈ rectBoundary z w, ContinuousAt FR s := by
      intro s hs
      dsimp only [FR]
      refine tendsto_finsetSum _ ?_
      intro u hu
      have hsu : s - u ≠ 0 := sub_ne_zero.mpr (fun h => hS_nb u hu (h ▸ hs))
      exact ContinuousAt.mul continuousAt_const
        (ContinuousAt.add (ContinuousAt.div continuousAt_const
          (continuousAt_id.sub continuousAt_const) hsu) continuousAt_const)
    have hlogcont : ∀ s ∈ rectBoundary z w,
        ContinuousAt (fun s : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) s) s := by
      intro s hs
      exact continuousAt_logDeriv_of_analyticAt
        ((DirichletCharacter.differentiable_completedLFunction hχ).analyticAt s) (hnz s hs)
    have hGcont : ∀ s ∈ rectBoundary z w, ContinuousAt G s := by
      intro s hs
      have hne : s - s₀ ≠ 0 := sub_ne_zero.mpr (ne_of_mem_rectBoundary_of_inside hs0in hs)
      have heq : G = fun u => H u + r / (u - s₀) := by funext u; simp only [H]; ring
      rw [heq]
      exact ((hH s).continuousAt).add
        (ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) hne)
    -- (a) the integral of `G` itself
    have hGint : rectInt z w G = 2 * (Real.pi : ℂ) * Complex.I * r := by
      have hpt : ∀ s ∈ rectBoundary z w, G s = H s + r / (s - s₀) := by
        intro s hs; simp only [H]; ring
      have hcontH : ∀ s ∈ rectBoundary z w, ContinuousAt H s := fun s _ => (hH s).continuousAt
      have hconstr : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ => r / (s - s₀)) s := by
        intro s hs
        have hne : s - s₀ ≠ 0 := sub_ne_zero.mpr (ne_of_mem_rectBoundary_of_inside hs0in hs)
        exact ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) hne
      rw [rectInt_congr_boundary' hpt, rectInt_add_of_boundary_continuousAt hcontH hconstr,
        rectInt_entire_eq_zero hH, rectInt_const_div_sub_inside r hzre hzim hs0in]
      ring
    -- (b) the divisor-sum part
    have hFRH : rectInt z w (fun s => FR s * H s) = (2 * (Real.pi : ℂ) * Complex.I) * SH := by
      have h := rectInt_kernel_finset_mul_entire (z := z) (w := w) hH hzre hzim S hS_ne hS_nb
        (fun v => ((dR v : ℤ) : ℂ))
      have h2 : rectInt z w (fun s => FR s * H s) =
          ∑ u ∈ S, ((dR u : ℤ) : ℂ) *
            (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
              H u * (2 * (Real.pi : ℂ) * Complex.I) else 0) := by
        simpa only [FR] using h
      have h' : (∑ u ∈ S, ((dR u : ℤ) : ℂ) *
            (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
              H u * (2 * (Real.pi : ℂ) * Complex.I) else 0)) =
          (2 * (Real.pi : ℂ) * Complex.I) * SH := by
        rw [hSH, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        by_cases hu' : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
        · rw [if_pos hu', if_pos hu']; ring
        · rw [if_neg hu', if_neg hu']; ring
      rw [h2, h']
    have hFRdiv : rectInt z w (fun s => FR s / (s - s₀)) =
        2 * (Real.pi : ℂ) * Complex.I * (FRs0 + S1) := by
      simpa only [FR, hFRs0, hS1] using
        rectInt_kernel_finset_div_sub (z := z) (w := w) (u := s₀) hzre hzim hs0in
          S hS_ne hS_nb hs0_notin_S (fun v => ((dR v : ℤ) : ℂ))
    have hFRG : rectInt z w (fun s => FR s * G s) =
        (2 * (Real.pi : ℂ) * Complex.I) * SH
          + r * ((2 * (Real.pi : ℂ) * Complex.I) * (FRs0 + S1)) := by
      have hpt : ∀ s ∈ rectBoundary z w,
          FR s * G s = FR s * H s + r * (FR s / (s - s₀)) := by
        intro s hs
        have hGeq : G s = H s + r / (s - s₀) := by simp only [H]; ring
        rw [hGeq]; ring
      have hc1 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ => FR s * H s) s := by
        intro s hs; exact (hFRcont s hs).mul (hH s).continuousAt
      have hc2 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ => r * (FR s / (s - s₀))) s := by
        intro s hs
        have hne : s - s₀ ≠ 0 := sub_ne_zero.mpr (ne_of_mem_rectBoundary_of_inside hs0in hs)
        exact continuousAt_const.mul
          (ContinuousAt.div (hFRcont s hs) (continuousAt_id.sub continuousAt_const) hne)
      rw [rectInt_congr_boundary' hpt, rectInt_add_of_boundary_continuousAt hc1 hc2,
        rectInt_const_mul' r (fun s => FR s / (s - s₀)), hFRH, hFRdiv]
    have hTRGcont : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ => TR s * G s) s := by
      intro s hs
      have hTRc : ContinuousAt TR s := by
        dsimp only [TR]
        exact ((hlogcont s hs).sub continuousAt_const).sub (hFRcont s hs)
      exact hTRc.mul (hGcont s hs)
    -- (c) assembly
    have htotal : rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s * G s) =
        (2 * (Real.pi : ℂ) * Complex.I) *
            (logDeriv (DirichletCharacter.completedLFunction χ) 0 * r + SH + r * (FRs0 + S1))
          + rectInt z w (fun s => TR s * G s) := by
      have hpt : ∀ s ∈ rectBoundary z w,
          logDeriv (DirichletCharacter.completedLFunction χ) s * G s =
            logDeriv (DirichletCharacter.completedLFunction χ) 0 * G s + FR s * G s + TR s * G s := by
        intro s hs; simp only [TR]; ring
      have hcA : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
          logDeriv (DirichletCharacter.completedLFunction χ) 0 * G s + FR s * G s) s := by
        intro s hs
        exact (continuousAt_const.mul (hGcont s hs)).add ((hFRcont s hs).mul (hGcont s hs))
      have hc1 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
          logDeriv (DirichletCharacter.completedLFunction χ) 0 * G s) s := by
        intro s hs; exact continuousAt_const.mul (hGcont s hs)
      have hc2 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ => FR s * G s) s := by
        intro s hs; exact (hFRcont s hs).mul (hGcont s hs)
      rw [rectInt_congr_boundary' hpt, rectInt_add_of_boundary_continuousAt hcA hTRGcont,
        rectInt_add_of_boundary_continuousAt hc1 hc2,
        rectInt_const_mul' (logDeriv (DirichletCharacter.completedLFunction χ) 0) G,
        hGint, hFRG]
      ring
    have hT : (∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
          ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) * G ρ
          else 0)) = SH + r * S1 := by
      have hsupp : Function.support (fun ρ : ℂ =>
          (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
            ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) * G ρ
            else 0)) ⊆ ↑S := by
        intro ρ hρ
        rw [Function.mem_support] at hρ
        have hP : z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im := by
          by_contra h
          rw [if_neg h] at hρ
          exact hρ rfl
        have hm : ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) ≠ 0 := by
          intro h
          rw [if_pos hP, h, zero_mul] at hρ
          exact hρ rfl
        have hm' : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 := by
          exact_mod_cast hm
        have hρR : ‖ρ‖ ≤ R :=
          le_trans (hinside_norm ρ hP.1 hP.2.1 hP.2.2.1 hP.2.2.2) (by linarith)
        have hd : dR ρ ≠ 0 := by
          dsimp only [dR]
          rw [divisor_eq_analyticOrderNatAt (U := Metric.closedBall 0 R)
            (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z)
            (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hρR))]
          exact_mod_cast hm'
        exact (hS_mem ρ).mpr hd
      rw [finsum_eq_sum_of_support_subset _ hsupp]
      have hstep : ∀ v ∈ S, (if z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im then
            ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) v : ℕ) : ℂ) * G v
            else 0) =
          ((dR v : ℤ) : ℂ) * (if z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im
              then H v else 0)
            + r * (((dR v : ℤ) : ℂ) * (if z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im
              then 1 / (v - s₀) else 0)) := by
        intro v hv
        by_cases hP : z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im
        · rw [if_pos hP, if_pos hP, if_pos hP]
          have hmv : ((dR v : ℤ) : ℂ) =
              ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) v : ℕ) : ℂ) := by
            have h1 : dR v = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) v : ℤ) := by
              dsimp only [dR]
              exact divisor_eq_analyticOrderNatAt (U := Metric.closedBall 0 R)
                (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z)
                (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hS_norm v hv))
            rw [h1]; norm_num
          by_cases hm0 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) v = 0
          · rw [hm0] at hmv
            rw [hmv, hm0]; simp
          · have hzero : DirichletCharacter.completedLFunction χ v = 0 :=
              apply_eq_zero_of_analyticOrderNatAt_ne_zero hm0
            have hvs : v ≠ s₀ := fun h => hΛs0 (h ▸ hzero)
            have hGv : G v = H v + r / (v - s₀) := by simp only [H]; ring
            rw [hmv, hGv]; ring
        · rw [if_neg hP, if_neg hP, if_neg hP]; ring
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
      have hA : (∑ v ∈ S, ((dR v : ℤ) : ℂ) *
          (if z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im then H v else 0)) = SH := rfl
      have hB : (∑ v ∈ S, r * (((dR v : ℤ) : ℂ) *
          (if z.re < v.re ∧ v.re < w.re ∧ z.im < v.im ∧ v.im < w.im then 1 / (v - s₀) else 0)))
          = r * S1 := by rw [Finset.mul_sum]
      rw [hA, hB]
    have hdisc : rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s * G s) -
        (2 * (Real.pi : ℂ) * Complex.I) *
          ((∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
              ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) * G ρ
              else 0))
            + logDeriv (DirichletCharacter.completedLFunction χ) s₀ * r)
        = -(2 * (Real.pi : ℂ) * Complex.I) * r * TR s₀
          + rectInt z w (fun s => TR s * G s) := by
      rw [htotal, hT, hTRs0]
      ring
    -- (d) tail bound
    have htail_bound : ‖rectInt z w (fun s => TR s * G s)‖ ≤
        2 * ((w.re - z.re) + (w.im - z.im)) *
          ((c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) * (M + ‖r‖ / δ)) := by
      refine norm_rectInt_le (M := (c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
          (M + ‖r‖ / δ)) hzre hzim hTRGcont ?_
      intro s hs
      have hnorm_s : ‖s‖ ≤ K := hnorm_le s (rectBoundary_subset_rectSet hzre hzim hs)
      have htail_le := hc s (hnz s hs) R hR (by linarith [hnorm_s, hR4])
      have hlog0 : (0 : ℝ) ≤ Real.log (R + 2) + Real.log (N : ℝ) + 2 := by
        have h3 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by
          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
        linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ R + 2)]
      have hTRle : ‖TR s‖ ≤ c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
        have htr : TR s = logDeriv (DirichletCharacter.completedLFunction χ) s -
            logDeriv (DirichletCharacter.completedLFunction χ) 0 -
            ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) * (1 / (s - u) + 1 / u) := by
          dsimp only [TR]
          rw [hFR_eq s]
        rw [htr]
        calc ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
              logDeriv (DirichletCharacter.completedLFunction χ) 0 -
              ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)‖
              ≤ c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := htail_le
          _ ≤ c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
              apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ R)
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hnorm_s hc0) hlog0
      rw [norm_mul]
      have h2 : (0 : ℝ) ≤ c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by positivity
      exact mul_le_mul hTRle (hG_boundary s hs) (norm_nonneg _) h2
    -- (e) the discrepancy bound
    have hTRs0le : ‖TR s₀‖ ≤ c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
      have hnorm_s0 : ‖s₀‖ ≤ K :=
        hinside_norm s₀ hs0in.1 hs0in.2.1 hs0in.2.2.1 hs0in.2.2.2
      have htail_s0 := hc s₀ hΛs0 R hR (by linarith [hnorm_s0, hR4])
      have hlog0 : (0 : ℝ) ≤ Real.log (R + 2) + Real.log (N : ℝ) + 2 := by
        have h3 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by
          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
        linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ R + 2)]
      have htr : TR s₀ = logDeriv (DirichletCharacter.completedLFunction χ) s₀ -
          logDeriv (DirichletCharacter.completedLFunction χ) 0 -
          ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) * (1 / (s₀ - u) + 1 / u) := by
        dsimp only [TR]
        rw [hFR_eq s₀]
      rw [htr]
      calc ‖logDeriv (DirichletCharacter.completedLFunction χ) s₀ -
            logDeriv (DirichletCharacter.completedLFunction χ) 0 -
            ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) * (1 / (s₀ - u) + 1 / u)‖
            ≤ c * ‖s₀‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := htail_s0
        _ ≤ c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
            apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ R)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hnorm_s0 hc0) hlog0
    have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
      simp [Real.pi_pos.le]
    have hb : (0 : ℝ) ≤ c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by positivity
    have hA : (0 : ℝ) ≤ 2 * Real.pi * ‖r‖ := by positivity
    calc ‖rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s * G s) -
          (2 * (Real.pi : ℂ) * Complex.I) *
            ((∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
                ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) * G ρ
                else 0))
              + logDeriv (DirichletCharacter.completedLFunction χ) s₀ * r)‖
        = ‖-(2 * (Real.pi : ℂ) * Complex.I) * r * TR s₀
            + rectInt z w (fun s => TR s * G s)‖ := by rw [hdisc]
      _ ≤ ‖-(2 * (Real.pi : ℂ) * Complex.I) * r * TR s₀‖
            + ‖rectInt z w (fun s => TR s * G s)‖ := norm_add_le _ _
      _ = ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ * ‖r‖ * ‖TR s₀‖
            + ‖rectInt z w (fun s => TR s * G s)‖ := by rw [norm_mul, norm_mul, norm_neg]
      _ ≤ 2 * Real.pi * ‖r‖ * (c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R)
            + 2 * ((w.re - z.re) + (w.im - z.im)) *
              ((c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) * (M + ‖r‖ / δ)) := by
          rw [h2pi]
          have h1 : 2 * Real.pi * ‖r‖ * ‖TR s₀‖ ≤
              2 * Real.pi * ‖r‖ * (c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) :=
            mul_le_mul_of_nonneg_left hTRs0le hA
          linarith [h1, htail_bound]
      _ = 2 * ((w.re - z.re) + (w.im - z.im)) *
              ((c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) * (M + ‖r‖ / δ))
            + 2 * Real.pi * ‖r‖ * (c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) := by ring
  have hlim : Tendsto (fun R : ℝ =>
        2 * ((w.re - z.re) + (w.im - z.im)) *
            ((c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) * (M + ‖r‖ / δ))
          + 2 * Real.pi * ‖r‖ * (c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R))
      atTop (𝓝 0) := by
    set w1 : ℝ → ℝ := fun R => (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R with hw1
    have h1 : Tendsto w1 atTop (𝓝 0) := by
      rw [hw1]
      have hlog := Commons.NumberTheory.Linnik.log_add_two_div_self_tendsto_zero
      have hc2 : Tendsto (fun R : ℝ => (Real.log (N : ℝ) + 2) / R) atTop (𝓝 0) := by
        have hnum : Tendsto (fun _ : ℝ => Real.log (N : ℝ) + 2) atTop
            (𝓝 (Real.log (N : ℝ) + 2)) := tendsto_const_nhds
        have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
        have := hnum.mul hinv
        simpa [div_eq_mul_inv] using this
      have := hlog.add hc2
      simpa [add_div, add_assoc] using this
    have h2 : Tendsto (fun R : ℝ => c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R)
        atTop (𝓝 0) := by
      have hcast : (fun R : ℝ => c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R)
          = fun R : ℝ => (c * K) * w1 R := by
        funext R; rw [hw1]; ring
      rw [hcast]
      simpa using (tendsto_const_nhds (x := c * K)).mul h1
    have h3 : Tendsto (fun R : ℝ =>
        (c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) * (M + ‖r‖ / δ))
        atTop (𝓝 0) := by
      simpa using h2.mul tendsto_const_nhds
    have h4 : Tendsto (fun R : ℝ =>
        (2 * ((w.re - z.re) + (w.im - z.im))) *
          ((c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) * (M + ‖r‖ / δ)))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 2 * ((w.re - z.re) + (w.im - z.im)))).mul h3
    have h5 : Tendsto (fun R : ℝ =>
        (2 * Real.pi * ‖r‖) * (c * K * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 2 * Real.pi * ‖r‖)).mul h2
    have := h4.add h5
    simpa [mul_assoc] using this
  have hzero : ‖rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s * G s) -
      (2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
            ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) * G ρ
            else 0))
          + logDeriv (DirichletCharacter.completedLFunction χ) s₀ * r)‖ ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (max 2 (4 * K))] with R hR
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    have hR4 : K ≤ R / 4 := by
      have := le_trans (le_max_right 2 (4 * K)) hR
      linarith
    exact hkey R hR2 hR4
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))

end

end Commons.NumberTheory.DirichletCharacter
