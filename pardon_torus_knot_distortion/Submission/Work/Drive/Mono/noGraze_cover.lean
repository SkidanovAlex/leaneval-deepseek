import Mathlib
import Submission.Work.Drive.Mono.NoGrazeDefs

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set

noncomputable section


/-- The flat height is differentiable. -/
theorem differentiable_flatHeight (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Differentiable ℝ (flatHeight K c σ u) := by
  have h1 : Differentiable ℝ K.curve := K.smooth.differentiable (by norm_num)
  have h2 : Differentiable ℝ
      (fun t : ℝ => inner ℝ (Work.BoxShrink.shiftVσ σ 1) (K.curve t)) :=
    Differentiable.inner ℝ (differentiable_const (Work.BoxShrink.shiftVσ σ 1)) h1
  have h4 : flatHeight K c σ u
      = fun t : ℝ => inner ℝ (Work.BoxShrink.shiftVσ σ 1) (K.curve t) - (c (σ 2) + u) := by
    funext t; rw [flatHeight_apply, inner_shiftVσ_one]
  rw [h4]
  exact h2.sub (differentiable_const _)

/-- The derivative of the flat height is continuous. -/
theorem continuous_deriv_flatHeight (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Continuous (deriv (flatHeight K c σ u)) := by
  have h : deriv (flatHeight K c σ u) = fun t : ℝ => (deriv K.curve t) (σ 2) := by
    funext t; rw [deriv_flatHeight]
  rw [h]
  exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).comp
    (K.smooth.continuous_deriv (by norm_num))

/-- A finite union of neighbourhoods, uniformly: if at every point of a finite set `T` the function
`f` is bounded below by `cc` on a neighbourhood, then there is one radius `δ` that works for all of
`T` at once. -/
theorem exists_pos_le_of_forall_near (T : Finset ℝ) (f : ℝ → ℝ) (cc : ℝ)
    (hT : ∀ t' ∈ T, ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x - t'| < r → cc ≤ f x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, (∃ t' ∈ T, |x - t'| < δ) → cc ≤ f x := by
  classical
  revert hT
  refine Finset.induction_on T ?_ ?_
  · intro _
    exact ⟨1, one_pos, fun x hx => absurd hx (by simp)⟩
  · intro a s ha ih hT
    obtain ⟨r, hr, hr'⟩ := hT a (Finset.mem_insert_self a s)
    obtain ⟨δ, hδ, hδ'⟩ := ih (fun t' ht' => hT t' (Finset.mem_insert_of_mem ht'))
    refine ⟨min r δ, lt_min hr hδ, fun x hx => ?_⟩
    obtain ⟨t', ht', hlt⟩ := hx
    rcases Finset.mem_insert.mp ht' with rfl | ht's
    · exact hr' x (lt_of_lt_of_le hlt (min_le_left r δ))
    · exact hδ' x ⟨t', ht's, lt_of_lt_of_le hlt (min_le_right r δ)⟩

end

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
theorem noGraze_cover (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) {s u : ℝ}
    (hcut : Work.Drive.Mono.CutTransverse K s c σ u) :
    ∃ lam m ρ : ℝ, 0 < lam ∧ 0 < m ∧ 0 < ρ ∧
      (∀ t ∈ Work.Drive.Mono.crossingSet K c σ s u hcut,
        lam ≤ |deriv (Work.Drive.Mono.flatHeight K c σ u) t|) ∧
      (∀ t : ℝ, t ∈ Set.Icc 0 (2 * Real.pi) →
        K.curve t ∈ closure (Submission.PBox s c σ) →
        (∀ t' ∈ Work.Drive.Mono.crossingSet K c σ s u hcut, ρ ≤ |t - t'|) →
        m ≤ |Work.Drive.Mono.flatHeight K c σ u t|) ∧
      (∀ t : ℝ, t ∈ Set.Icc 0 (2 * Real.pi) →
        K.curve t ∈ closure (Submission.PBox s c σ) →
        |Work.Drive.Mono.flatHeight K c σ u t| < m →
        ∃ t' ∈ Work.Drive.Mono.crossingSet K c σ s u hcut,
          lam * |t - t'| ≤ 2 * |Work.Drive.Mono.flatHeight K c σ u t|) := by
  classical
  obtain ⟨lam, hlam_pos, hlam⟩ := exists_flatSpeed_pos hcut
  have hcont : Continuous (deriv (flatHeight K c σ u)) := continuous_deriv_flatHeight K c σ u
  have hper : ∀ t' ∈ crossingSet K c σ s u hcut,
      ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x - t'| < r → lam / 2 ≤ |deriv (flatHeight K c σ u) x| := by
    intro t' ht'
    have hcf : ContinuousAt (fun x : ℝ => |deriv (flatHeight K c σ u) x|) t' :=
      (continuous_abs.comp hcont).continuousAt
    have hpos : 0 < |deriv (flatHeight K c σ u) t'| :=
      abs_pos.mpr (crossingSet_spec ht').2
    obtain ⟨r, hr, hr'⟩ := Metric.continuousAt_iff.mp hcf
      (|deriv (flatHeight K c σ u) t'| / 2) (by linarith)
    refine ⟨r, hr, fun x hx => ?_⟩
    have hspec' : lam ≤ |deriv (flatHeight K c σ u) t'| := hlam t' ht'
    have h1 := hr' (x := x) (by rw [Real.dist_eq]; exact hx)
    rw [Real.dist_eq, abs_lt] at h1
    linarith [h1.1, hspec']
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_le_of_forall_near (crossingSet K c σ s u hcut)
    (fun x => |deriv (flatHeight K c σ u) x|) (lam / 2) hper
  set ρ : ℝ := min δ 1 with hρdef
  have hρpos : 0 < ρ := lt_min hδpos one_pos
  have hρδ : ρ ≤ δ := min_le_left δ 1
  obtain ⟨m, hmpos, hm⟩ := exists_margin_off_flatCrossings K c σ (s := s) (u := u) hρpos
  refine ⟨lam, m, ρ, hlam_pos, hmpos, hρpos, hlam, ?_, ?_⟩
  · intro t htIcc htbox hfar
    exact hm t htIcc htbox (fun t' ht'Icc ht'box ht'lev =>
      hfar t' (mem_crossingSet.mpr ⟨ht'Icc, ht'box, ht'lev⟩))
  · intro t htIcc htbox hlt
    have hnear : ∃ t' ∈ crossingSet K c σ s u hcut, |t - t'| < ρ := by
      by_contra hcon
      have hcon' : ∀ t' : ℝ, t' ∈ crossingSet K c σ s u hcut → ρ ≤ |t - t'| := by
        intro t' ht'
        by_contra hlt'
        exact hcon ⟨t', ht', not_le.mp hlt'⟩
      exact absurd (hm t htIcc htbox (fun t' ht'Icc ht'box ht'lev =>
        hcon' t' (mem_crossingSet.mpr ⟨ht'Icc, ht'box, ht'lev⟩))) (not_le.mpr hlt)
    obtain ⟨t', ht', hdist⟩ := hnear
    have hφt' : flatHeight K c σ u t' = 0 := by
      have h3 : (K.curve t') (σ 2) = c (σ 2) + u := (mem_crossingSet.mp ht').2.2
      rw [flatHeight_apply]; linarith
    have hdthin : |t - t'| < δ := lt_of_lt_of_le hdist hρδ
    have hdiff : Differentiable ℝ (flatHeight K c σ u) := differentiable_flatHeight K c σ u
    refine ⟨t', ht', ?_⟩
    rcases eq_or_ne t t' with h | hne
    · rw [h, sub_self, abs_zero, mul_zero, hφt', abs_zero, mul_zero]
    · rcases lt_or_gt_of_ne hne with hlt' | hgt'
      · obtain ⟨ξ, hξ, hξ'⟩ := exists_deriv_eq_slope (flatHeight K c σ u) hlt'
          hdiff.continuous.continuousOn hdiff.differentiableOn
        have hξnear : |ξ - t'| < δ := by
          have hcomp : |ξ - t'| < |t - t'| := by
            rw [abs_of_neg (by linarith [hξ.2] : ξ - t' < 0),
              abs_of_neg (by linarith : t - t' < 0)]
            linarith [hξ.1]
          linarith
        have hge := hδ ξ ⟨t', ht', hξnear⟩
        have hne0 : t' - t ≠ 0 := by linarith
        have hprod : deriv (flatHeight K c σ u) ξ * (t' - t) = -flatHeight K c σ u t := by
          rw [hξ', hφt', zero_sub, div_mul_cancel₀ _ hne0]
        have habs : |deriv (flatHeight K c σ u) ξ| * |t' - t| = |flatHeight K c σ u t| := by
          rw [← abs_mul, hprod, abs_neg]
        have hstep : lam / 2 * |t' - t| ≤ |flatHeight K c σ u t| := by
          rw [← habs]
          exact mul_le_mul_of_nonneg_right hge (abs_nonneg _)
        rw [abs_sub_comm t t']
        nlinarith [hstep]
      · obtain ⟨ξ, hξ, hξ'⟩ := exists_deriv_eq_slope (flatHeight K c σ u) hgt'
          hdiff.continuous.continuousOn hdiff.differentiableOn
        have hξnear : |ξ - t'| < δ := by
          have hcomp : |ξ - t'| < |t - t'| := by
            rw [abs_of_pos (by linarith [hξ.1] : 0 < ξ - t'),
              abs_of_pos (by linarith : 0 < t - t')]
            linarith [hξ.2]
          linarith
        have hge := hδ ξ ⟨t', ht', hξnear⟩
        have hne0 : t - t' ≠ 0 := by linarith
        have hprod : deriv (flatHeight K c σ u) ξ * (t - t') = flatHeight K c σ u t := by
          rw [hξ', hφt', sub_zero, div_mul_cancel₀ _ hne0]
        have habs : |deriv (flatHeight K c σ u) ξ| * |t - t'| = |flatHeight K c σ u t| := by
          rw [← abs_mul, hprod]
        have hstep : lam / 2 * |t - t'| ≤ |flatHeight K c σ u t| := by
          rw [← habs]
          exact mul_le_mul_of_nonneg_right hge (abs_nonneg _)
        nlinarith [hstep]


end Work.Drive.Mono
