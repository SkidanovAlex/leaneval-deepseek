import Mathlib
import Submission.Lib.Unif2.Work.Potential.harmonic_extend_punctured_ball

open Set Metric Filter
open scoped Topology Real

set_option linter.unusedVariables false

namespace Work.Potential

/-! ## A centred form of the annulus maximum principle -/

/-- **Maximum principle on a closed annulus** with an arbitrary centre `a`: a function harmonic on
the open annulus `r < ‖z - a‖ < R`, continuous on the closed annulus, and bounded by `M` on both
boundary circles, is bounded by `M` on the whole closed annulus.  This is
`Commons.Analysis.Complex.Harmonic.annulus_le_boundary` translated by `a`. -/
private theorem annulus_le_boundary_center_aux {u : ℂ → ℝ} {a : ℂ} {r R M : ℝ} (hr : 0 < r)
    (hrR : r < R)
    (hu : ∀ z : ℂ, r < ‖z - a‖ → ‖z - a‖ < R → InnerProductSpace.HarmonicAt u z)
    (hc : ContinuousOn u {z : ℂ | r ≤ ‖z - a‖ ∧ ‖z - a‖ ≤ R})
    (hM : ∀ z : ℂ, (‖z - a‖ = r ∨ ‖z - a‖ = R) → u z ≤ M) :
    ∀ z : ℂ, r ≤ ‖z - a‖ → ‖z - a‖ ≤ R → u z ≤ M := by
  set v : ℂ → ℝ := fun y => u (a + y) with hv
  have hvhar : InnerProductSpace.HarmonicOnNhd v {y : ℂ | r < ‖y‖ ∧ ‖y‖ < R} := by
    intro y hy
    have h1 : InnerProductSpace.HarmonicAt u (a + y) :=
      hu (a + y) (by simpa using hy.1) (by simpa using hy.2)
    have h2 : AnalyticAt ℂ (fun z : ℂ => a + z) y := analyticAt_const.add analyticAt_id
    have h3 : InnerProductSpace.HarmonicAt (fun z : ℂ => u (a + z)) y :=
      Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic h2 h1
    simpa [hv] using h3
  have hvcont : ContinuousOn v {y : ℂ | r ≤ ‖y‖ ∧ ‖y‖ ≤ R} := by
    have hmap : ContinuousOn (fun y : ℂ => a + y) {y : ℂ | r ≤ ‖y‖ ∧ ‖y‖ ≤ R} :=
      (continuous_const.add continuous_id).continuousOn
    have hmaps : MapsTo (fun y : ℂ => a + y) {y : ℂ | r ≤ ‖y‖ ∧ ‖y‖ ≤ R}
        {z : ℂ | r ≤ ‖z - a‖ ∧ ‖z - a‖ ≤ R} := fun y hy => by simpa using hy
    have h := hc.comp hmap hmaps
    simpa [hv, Function.comp_def] using h
  have hMv : ∀ y : ℂ, (‖y‖ = r ∨ ‖y‖ = R) → v y ≤ M := by
    intro y hy
    refine hM (a + y) ?_
    rcases hy with hy | hy
    · left; simpa using hy
    · right; simpa using hy
  intro z hzr hzR
  have h := Commons.Analysis.Complex.Harmonic.annulus_le_boundary (u := v) (r := r) (R := R)
    (M := M) hr hrR hvhar hvcont hMv (z - a) (by simpa using hzr) (by simpa using hzR)
  rw [hv] at h
  simpa using h

/-- **A harmonic function on a punctured disc that is bounded at the puncture takes its sup on the outer circle.**

`w` is harmonic on the punctured disc `0 < ‖z - a‖ < ρ`, is bounded by `C` on the smaller punctured disc `0 < ‖z - a‖ < ε` (with `ε < r < ρ`), and `|w| ≤ M` on the circle `‖z - a‖ = r`.  Then `|w| ≤ M` on the whole punctured disc `0 < ‖z - a‖ < r`.

ROUTE.  (i) `Work.Potential.harmonic_extend_punctured_ball` (file `Submission/Work/Potential/harmonic_extend_punctured_ball.lean`) with radius `ε` and bound `C` extends `w` across `a` on the disc of radius `ε`; the maximum principle on that disc (`Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le`, file `Submission/Commons/Analysis/Complex/Harmonic/harmonic_le_of_boundary_le.lean`, applied to the extension and its negative) shows `|w| ≤ C` on `0 < ‖z - a‖ < ε` (the extension is continuous on the closed disc because it agrees with `w`, which is harmonic in the larger disc of radius `ρ > ε`, near every point of the circle `‖z-a‖ = ε`).
(ii) The maximum principle on the closed annulus `ε ≤ ‖z - a‖ ≤ r` (`Commons.Analysis.Complex.Harmonic.annulus_le_boundary`, file `Submission/Commons/Analysis/Complex/Harmonic/annulus_le_boundary.lean`, or its centered form `Submission.annulus_le_boundary_center` in `Submission/GreenFunction.lean`, which needs `w` continuous on the closed annulus — true since the closed annulus lies in the open punctured disc of radius `ρ`) bounds `|w|` on it by `max C (sup over the circle of radius r of |w|)`, giving a global bound `M₀` for `|w|` on the whole punctured disc of radius `r`.
(iii) Extend `w` across `a` on the disc of radius `r` with the bound `M₀`; the maximum principle on that disc, with boundary data `w` on the circle of radius `r`, gives `|w| ≤ M` on `0 < ‖z - a‖ < r`. -/
theorem punctured_ball_abs_le_of_bounded_near {a : ℂ} {ρ r M : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r < ρ) {w : ℂ → ℝ}
    (hw : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → InnerProductSpace.HarmonicAt w z)
    (hb : ∃ C : ℝ, ∃ ε : ℝ, 0 < ε ∧ ε < r ∧
      ∀ z : ℂ, 0 < ‖z - a‖ → ‖z - a‖ < ε → |w z| ≤ C)
    (hsphere : ∀ z : ℂ, ‖z - a‖ = r → |w z| ≤ M) :
    ∀ z : ℂ, ‖z - a‖ < r → z ≠ a → |w z| ≤ M := by
  classical
  obtain ⟨C, ε, hε0, hεr, hbnd⟩ := hb
  set M₀ : ℝ := max C M with hM₀
  have hCM : C ≤ M₀ := by rw [hM₀]; exact le_max_left _ _
  have hMM : M ≤ M₀ := by rw [hM₀]; exact le_max_right _ _
  -- (ii) the annulus bound for every inner radius `δ ∈ (0, ε)`
  have hann : ∀ δ : ℝ, 0 < δ → δ < ε → ∀ z : ℂ, δ ≤ ‖z - a‖ → ‖z - a‖ ≤ r →
      |w z| ≤ M₀ := by
    intro δ hδ0 hδε z hzδ hzr
    have hδr : δ < r := lt_trans hδε hεr
    have hharm : ∀ y : ℂ, δ < ‖y - a‖ → ‖y - a‖ < r →
        InnerProductSpace.HarmonicAt w y := by
      intro y hy1 hy2
      have hyne : y ≠ a := sub_ne_zero.mp (norm_pos_iff.mp (lt_trans hδ0 hy1))
      exact hw y (lt_trans hy2 hrρ) hyne
    have hcont : ContinuousOn w {y : ℂ | δ ≤ ‖y - a‖ ∧ ‖y - a‖ ≤ r} := by
      intro y hy
      have hyne : y ≠ a := sub_ne_zero.mp (norm_pos_iff.mp (lt_of_lt_of_le hδ0 hy.1))
      exact ((hw y (lt_of_le_of_lt hy.2 hrρ) hyne).1.continuousAt).continuousWithinAt
    refine abs_le.mpr ⟨?_, ?_⟩
    · -- `-M₀ ≤ w`
      have h := annulus_le_boundary_center_aux (u := fun y => -w y) (r := δ) (R := r) (M := M₀)
        hδ0 hδr (fun y hy1 hy2 => (hharm y hy1 hy2).neg) hcont.neg (fun y hy => ?_) z hzδ hzr
      · linarith
      rcases hy with hy | hy
      · have h2 : |w y| ≤ C := hbnd y (by rw [hy]; exact hδ0) (by rw [hy]; exact hδε)
        linarith [neg_le_abs (w y), h2, hCM]
      · have h2 : |w y| ≤ M := hsphere y hy
        linarith [neg_le_abs (w y), h2, hMM]
    · -- `w ≤ M₀`
      refine annulus_le_boundary_center_aux (u := w) (r := δ) (R := r) (M := M₀)
        hδ0 hδr hharm hcont (fun y hy => ?_) z hzδ hzr
      rcases hy with hy | hy
      · have h2 : |w y| ≤ C := hbnd y (by rw [hy]; exact hδ0) (by rw [hy]; exact hδε)
        linarith [le_abs_self (w y), h2, hCM]
      · have h2 : |w y| ≤ M := hsphere y hy
        linarith [le_abs_self (w y), h2, hMM]
  -- the bound `|w| ≤ M₀` on the whole punctured disc of radius `r`
  have hbound : ∀ z : ℂ, 0 < ‖z - a‖ → ‖z - a‖ < r → |w z| ≤ M₀ := by
    intro z hzpos hzr
    refine hann (min (ε / 2) ‖z - a‖) (lt_min (by linarith) hzpos)
      (lt_of_le_of_lt (min_le_left _ _) (by linarith)) z (min_le_right _ _) hzr.le
  -- (iii) extend `w` across `a` on the disc of radius `r`
  obtain ⟨H, hHharm, hHeq⟩ :=
    Work.Potential.harmonic_extend_punctured_ball (a := a) (ρ := r) (M := M₀) hr
      (fun z hz hzne => hw z (lt_trans hz hrρ) hzne)
      (fun z hz hzne => hbound z (norm_pos_iff.mpr (sub_ne_zero.mpr hzne)) hz)
  -- the glued function `if ‖z - a‖ < r then H z else w z` is continuous on the closed disc
  have hgcont : ContinuousOn (fun z : ℂ => if ‖z - a‖ < r then H z else w z)
      (Metric.closedBall a r) := by
    intro z hz
    have hzle : ‖z - a‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    rcases lt_or_ge ‖z - a‖ r with hlt | hge
    · have heq : (fun y : ℂ => if ‖y - a‖ < r then H y else w y) =ᶠ[𝓝 z] H := by
        filter_upwards [Metric.isOpen_ball.mem_nhds
          (by rw [Metric.mem_ball, dist_eq_norm]; exact hlt)] with y hy
        have hy' : ‖y - a‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hy
        show (if ‖y - a‖ < r then H y else w y) = H y
        rw [if_pos hy']
      exact ((hHharm z hlt).1.continuousAt.congr heq.symm).continuousWithinAt
    · have hzn : ‖z - a‖ = r := le_antisymm hzle hge
      have hze : z ≠ a := by rintro rfl; rw [sub_self, norm_zero] at hge; linarith
      have heq : (fun y : ℂ => if ‖y - a‖ < r then H y else w y) =ᶠ[𝓝 z] w := by
        have hzmem : z ∈ {y : ℂ | r / 2 < ‖y - a‖} := by
          show r / 2 < ‖z - a‖
          rw [hzn]; linarith
        have hnb : {y : ℂ | r / 2 < ‖y - a‖} ∈ 𝓝 z :=
          (isOpen_lt continuous_const
            (continuous_norm.comp (continuous_id.sub continuous_const))).mem_nhds hzmem
        filter_upwards [hnb] with y hy
        by_cases hyr : ‖y - a‖ < r
        · have hyne : y ≠ a := sub_ne_zero.mp (norm_pos_iff.mp (lt_trans (by linarith : (0:ℝ) < r / 2) hy))
          show (if ‖y - a‖ < r then H y else w y) = w y
          rw [if_pos hyr, hHeq y hyr hyne]
        · show (if ‖y - a‖ < r then H y else w y) = w y
          rw [if_neg hyr]
      exact ((hw z (by rw [hzn]; exact hrρ) hze).1.continuousAt.congr heq.symm).continuousWithinAt
  have hsphere' : ∀ z : ℂ, z ∈ Metric.sphere a r → w z ≤ M := fun z hz =>
    le_trans (le_abs_self _) (hsphere z (by simpa [Metric.mem_sphere, dist_eq_norm] using hz))
  have hle : ∀ z : ℂ, ‖z - a‖ < r → H z ≤ M :=
    Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le (c := a) (R := r) (M := M)
      (F := w) (u := H) hr hsphere' (fun z hz => hHharm z hz) hgcont
  have hle' : ∀ z : ℂ, ‖z - a‖ < r → -H z ≤ M := by
    have hgneg : ContinuousOn (fun z : ℂ => if ‖z - a‖ < r then -H z else -w z)
        (Metric.closedBall a r) := by
      have heq : (fun z : ℂ => if ‖z - a‖ < r then -H z else -w z)
          = fun z : ℂ => -(if ‖z - a‖ < r then H z else w z) := by
        funext z
        by_cases h : ‖z - a‖ < r <;> simp [h]
      rw [heq]
      exact hgcont.neg
    exact Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le (c := a) (R := r) (M := M)
      (F := fun z : ℂ => -w z) (u := fun z : ℂ => -H z) hr
      (fun z hz => by
        have h := hsphere z (by simpa [Metric.mem_sphere, dist_eq_norm] using hz)
        linarith [neg_le_abs (w z)])
      (fun z hz => (hHharm z hz).neg) hgneg
  intro z hz hzne
  have hzw : H z = w z := hHeq z hz hzne
  rw [← hzw]
  exact abs_le.mpr ⟨by linarith [hle' z hz], hle z hz⟩

end Work.Potential
