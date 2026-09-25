import Mathlib
import Submission.Commons.Analysis.Complex.rectIntegral_sub_inv_inside
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.tan_norm_le_of_abs_im_ge
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_truncatedPerron
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_truncatedPerron_refined
import Submission.Commons.NumberTheory.Zeta.divisor_xi_eq_logDeriv_pole_order
import Submission.Commons.NumberTheory.Zeta.edgeL_farleft_neg_three_halves_bound
import Submission.Commons.NumberTheory.Zeta.lSeries_mangoldt_integral_eq_zeta_logDeriv
import Submission.Commons.NumberTheory.Zeta.zeta1_ball_zeroFree
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_goodHeight
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_goodHeight_delta
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_left_compact
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_left_mid_delta
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_left_mid_nodelta
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal
import Submission.Commons.NumberTheory.Zeta.zeta1_mid_pointwise
import Submission.Commons.NumberTheory.Zeta.zetaZeroBall
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_fe_expanded
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_left_far_strip_bound
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_left_strip_bound
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_negStrip_bound
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_right_logsq
import Submission.Commons.NumberTheory.Zeta.zeta_ne_zero_of_rh_gt_half

set_option maxHeartbeats 4000000


-- ==== begin p2_contour ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# P2 engine: the rectangle multi-pole residue theorem

T-R3.1's rectangle identity (Tao 254A Notes 2, Thm 21) needs: for a rectangle with corners
`z w` (`z.re < w.re`, `z.im < w.im`) and poles `u i` strictly inside carrying coefficients
`c i`, plus a remainder `G` complex-differentiable on the closed rectangle,

    rectInt z w (fun t => (∑ i, c i / (t - u i)) + G t) = (∑ i, c i) · 2πi

(where `rectInt` is the counterclockwise boundary integral of
`Commons.NumberTheory.Zeta`).  It follows by linearity of `rectInt` over finite sums
(`rectInt_add`/`rectInt_sum_edge`), the single-pole identity
`rectInt (c/(·−u)) = c·2πi` (rectIntegral_sub_inv_inside), and Cauchy's theorem
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) annihilating `G`.

The ζ-content (assembled elsewhere from the published P1/P0.5 pole-removal lemmas) is to
express `psiIntF x s = −(ζ′/ζ)(s)·x^s/s` on the rectangle boundary as exactly such a model
with poles `u := 1` (c := x) and each zero `ρ` (c := −m_ρ·x^ρ/ρ), the remainder `G` being the
boundary value of a function differentiable on the closed rectangle (the removable-singularity
extensions at the poles).  Then the Perron identity converts the right-hand vertical side to
`ψ(x)`, giving the explicit formula.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- integrability of `f` on the four edges of the rectangle with corners `z w`. -/
def EdgeInt (z w : ℂ) (f : ℂ → ℂ) : Prop :=
  IntervalIntegrable (fun u : ℝ => f ((u : ℂ) + (z.im : ℂ) * Complex.I)) volume z.re w.re ∧
  IntervalIntegrable (fun u : ℝ => f ((u : ℂ) + (w.im : ℂ) * Complex.I)) volume z.re w.re ∧
  IntervalIntegrable (fun v : ℝ => f ((w.re : ℂ) + (v : ℂ) * Complex.I)) volume z.im w.im ∧
  IntervalIntegrable (fun v : ℝ => f ((z.re : ℂ) + (v : ℂ) * Complex.I)) volume z.im w.im

private lemma edge_cont_horiz_of_contOnRect {f : ℂ → ℂ} {z w : ℂ}
    (hcont : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im)) {r : ℝ}
    (hr : r ∈ Set.uIcc z.im w.im) :
    ContinuousOn (fun u : ℝ => f ((u : ℂ) + (r : ℂ) * Complex.I)) (Set.uIcc z.re w.re) := by
  have hE : ContinuousOn (fun u : ℝ => (u : ℂ) + (r : ℂ) * Complex.I)
      (Set.uIcc z.re w.re) := by fun_prop
  have hm : Set.MapsTo (fun u : ℝ => (u : ℂ) + (r : ℂ) * Complex.I)
      (Set.uIcc z.re w.re) (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    intro u hu
    exact Complex.mem_reProdIm.mpr ⟨by simpa using hu, by simpa using hr⟩
  exact hcont.comp hE hm

private lemma edge_cont_vert_of_contOnRect {f : ℂ → ℂ} {z w : ℂ}
    (hcont : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im)) {s : ℝ}
    (hs : s ∈ Set.uIcc z.re w.re) :
    ContinuousOn (fun v : ℝ => f ((s : ℂ) + (v : ℂ) * Complex.I)) (Set.uIcc z.im w.im) := by
  have hE : ContinuousOn (fun v : ℝ => (s : ℂ) + (v : ℂ) * Complex.I)
      (Set.uIcc z.im w.im) := by fun_prop
  have hm : Set.MapsTo (fun v : ℝ => (s : ℂ) + (v : ℂ) * Complex.I)
      (Set.uIcc z.im w.im) (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    intro v hv
    exact Complex.mem_reProdIm.mpr ⟨by simpa using hs, by simpa using hv⟩
  exact hcont.comp hE hm

lemma EdgeInt.of_continuousOn {z w : ℂ} {f : ℂ → ℂ}
    (hcont : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im)) : EdgeInt z w f := by
  have h1 : IntervalIntegrable (fun u : ℝ => f ((u : ℂ) + (z.im : ℂ) * Complex.I)) volume z.re w.re :=
    (edge_cont_horiz_of_contOnRect hcont (by simp)).intervalIntegrable
  have h2 : IntervalIntegrable (fun u : ℝ => f ((u : ℂ) + (w.im : ℂ) * Complex.I)) volume z.re w.re :=
    (edge_cont_horiz_of_contOnRect hcont (by simp)).intervalIntegrable
  have h3 : IntervalIntegrable (fun v : ℝ => f ((w.re : ℂ) + (v : ℂ) * Complex.I)) volume z.im w.im :=
    (edge_cont_vert_of_contOnRect hcont (by simp)).intervalIntegrable
  have h4 : IntervalIntegrable (fun v : ℝ => f ((z.re : ℂ) + (v : ℂ) * Complex.I)) volume z.im w.im :=
    (edge_cont_vert_of_contOnRect hcont (by simp)).intervalIntegrable
  exact ⟨h1, h2, h3, h4⟩

lemma EdgeInt.add {z w : ℂ} {f g : ℂ → ℂ} (hf : EdgeInt z w f) (hg : EdgeInt z w g) :
    EdgeInt z w (fun t => f t + g t) := by
  exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

lemma EdgeInt.sum {ι : Type*} {z w : ℂ} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, EdgeInt z w (f i)) : EdgeInt z w (fun t : ℂ => ∑ i ∈ s, f i t) := by
  have h1 : IntervalIntegrable
      (fun u : ℝ => (fun t : ℂ => ∑ i ∈ s, f i t) ((u : ℂ) + (z.im : ℂ) * Complex.I))
      volume z.re w.re := by
    have hS := IntervalIntegrable.sum s (fun i hi => (h i hi).1)
    have hEq : (∑ i ∈ s, fun u : ℝ => f i ((u : ℂ) + (z.im : ℂ) * Complex.I)) =
        fun u : ℝ => (fun t : ℂ => ∑ i ∈ s, f i t) ((u : ℂ) + (z.im : ℂ) * Complex.I) := by
      funext u
      simp [Finset.sum_apply]
    rw [hEq] at hS
    exact hS
  have h2 : IntervalIntegrable
      (fun u : ℝ => (fun t : ℂ => ∑ i ∈ s, f i t) ((u : ℂ) + (w.im : ℂ) * Complex.I))
      volume z.re w.re := by
    have hS := IntervalIntegrable.sum s (fun i hi => (h i hi).2.1)
    have hEq : (∑ i ∈ s, fun u : ℝ => f i ((u : ℂ) + (w.im : ℂ) * Complex.I)) =
        fun u : ℝ => (fun t : ℂ => ∑ i ∈ s, f i t) ((u : ℂ) + (w.im : ℂ) * Complex.I) := by
      funext u
      simp [Finset.sum_apply]
    rw [hEq] at hS
    exact hS
  have h3 : IntervalIntegrable
      (fun v : ℝ => (fun t : ℂ => ∑ i ∈ s, f i t) ((w.re : ℂ) + (v : ℂ) * Complex.I))
      volume z.im w.im := by
    have hS := IntervalIntegrable.sum s (fun i hi => (h i hi).2.2.1)
    have hEq : (∑ i ∈ s, fun v : ℝ => f i ((w.re : ℂ) + (v : ℂ) * Complex.I)) =
        fun v : ℝ => (fun t : ℂ => ∑ i ∈ s, f i t) ((w.re : ℂ) + (v : ℂ) * Complex.I) := by
      funext v
      simp [Finset.sum_apply]
    rw [hEq] at hS
    exact hS
  have h4 : IntervalIntegrable
      (fun v : ℝ => (fun t : ℂ => ∑ i ∈ s, f i t) ((z.re : ℂ) + (v : ℂ) * Complex.I))
      volume z.im w.im := by
    have hS := IntervalIntegrable.sum s (fun i hi => (h i hi).2.2.2)
    have hEq : (∑ i ∈ s, fun v : ℝ => f i ((z.re : ℂ) + (v : ℂ) * Complex.I)) =
        fun v : ℝ => (fun t : ℂ => ∑ i ∈ s, f i t) ((z.re : ℂ) + (v : ℂ) * Complex.I) := by
      funext v
      simp [Finset.sum_apply]
    rw [hEq] at hS
    exact hS
  exact ⟨h1, h2, h3, h4⟩

lemma rectInt_add_edge {z w : ℂ} {f g : ℂ → ℂ} (hf : EdgeInt z w f) (hg : EdgeInt z w g) :
    rectInt z w (fun t => f t + g t) = rectInt z w f + rectInt z w g := by
  exact rectInt_add hf.1 hg.1 hf.2.1 hg.2.1 hf.2.2.1 hg.2.2.1 hf.2.2.2 hg.2.2.2

/-- rectangle integral of the identically-zero function is zero. -/
lemma rectInt_zero {z w : ℂ} : rectInt z w (fun _ : ℂ => 0) = 0 := by
  unfold rectInt
  simp

/-- finite linearity of the rectangle integral over the edges. -/
lemma rectInt_sum_edge {ι : Type*} [DecidableEq ι] {z w : ℂ} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, EdgeInt z w (f i)) :
    rectInt z w (fun t : ℂ => ∑ i ∈ s, f i t) = ∑ i ∈ s, rectInt z w (f i) := by
  classical
  revert h
  refine Finset.induction_on s ?base ?step
  · intro h
    simp [Finset.sum_empty, rectInt_zero]
  · intro a s' has ih hfull
    have hfa : EdgeInt z w (f a) := hfull a (Finset.mem_insert_self a s')
    have hfs : EdgeInt z w (fun t : ℂ => ∑ i ∈ s', f i t) :=
      EdgeInt.sum s' f (fun i hi => hfull i (Finset.mem_insert_of_mem hi))
    have hsub : rectInt z w (fun t : ℂ => ∑ i ∈ s', f i t) =
        ∑ i ∈ s', rectInt z w (f i) := ih (fun i hi => hfull i (Finset.mem_insert_of_mem hi))
    calc
      rectInt z w (fun t : ℂ => ∑ i ∈ insert a s', f i t)
          = rectInt z w (fun t : ℂ => f a t + (∑ i ∈ s', f i t)) := by
              apply congrArg (rectInt z w)
              funext t
              rw [Finset.sum_insert has]
      _ = rectInt z w (f a) + rectInt z w (fun t : ℂ => ∑ i ∈ s', f i t) := rectInt_add_edge hfa hfs
      _ = rectInt z w (f a) + ∑ i ∈ s', rectInt z w (f i) := by rw [hsub]
      _ = ∑ i ∈ insert a s', rectInt z w (f i) := by
              rw [Finset.sum_insert has]

/-- integrability of a single-pole term `c/(·−u)` along the edges (pole strictly inside). -/
lemma EdgeInt.polar {z w u : ℂ} (c : ℂ)
    (hu : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    EdgeInt z w (fun t : ℂ => c / (t - u)) := by
  have h1 : IntervalIntegrable (fun t : ℝ => c / (((t : ℂ) + (z.im : ℂ) * Complex.I) - u))
      volume z.re w.re := by
    have hc : ContinuousOn (fun t : ℝ => c / (((t : ℂ) + (z.im : ℂ) * Complex.I) - u))
        (Set.uIcc z.re w.re) := by
      intro t ht
      refine ContinuousAt.continuousWithinAt ?_
      have hne : ((t : ℂ) + (z.im : ℂ) * Complex.I) - u ≠ 0 := by
        intro hzero
        have hval : (((t : ℂ) + (z.im : ℂ) * Complex.I) - u).im = z.im - u.im := by simp
        have h0 : (((t : ℂ) + (z.im : ℂ) * Complex.I) - u).im = 0 := by rw [hzero]; simp
        have hz0 : z.im - u.im = 0 := by linarith
        have hne2 : z.im ≠ u.im := ne_of_lt hu.2.2.1
        exact hne2 (by linarith)
      fun_prop
    exact hc.intervalIntegrable
  have h2 : IntervalIntegrable (fun t : ℝ => c / (((t : ℂ) + (w.im : ℂ) * Complex.I) - u))
      volume z.re w.re := by
    have hc : ContinuousOn (fun t : ℝ => c / (((t : ℂ) + (w.im : ℂ) * Complex.I) - u))
        (Set.uIcc z.re w.re) := by
      intro t ht
      refine ContinuousAt.continuousWithinAt ?_
      have hne : ((t : ℂ) + (w.im : ℂ) * Complex.I) - u ≠ 0 := by
        intro hzero
        have hval : (((t : ℂ) + (w.im : ℂ) * Complex.I) - u).im = w.im - u.im := by simp
        have h0 : (((t : ℂ) + (w.im : ℂ) * Complex.I) - u).im = 0 := by rw [hzero]; simp
        have hw0 : w.im - u.im = 0 := by linarith
        have hne2 : w.im ≠ u.im := ne_of_gt hu.2.2.2
        exact hne2 (by linarith)
      fun_prop
    exact hc.intervalIntegrable
  have h3 : IntervalIntegrable (fun v : ℝ => c / (((w.re : ℂ) + (v : ℂ) * Complex.I) - u))
      volume z.im w.im := by
    have hc : ContinuousOn (fun v : ℝ => c / (((w.re : ℂ) + (v : ℂ) * Complex.I) - u))
        (Set.uIcc z.im w.im) := by
      intro v hv
      refine ContinuousAt.continuousWithinAt ?_
      have hne : ((w.re : ℂ) + (v : ℂ) * Complex.I) - u ≠ 0 := by
        intro hzero
        have hval : (((w.re : ℂ) + (v : ℂ) * Complex.I) - u).re = w.re - u.re := by simp
        have h0 : (((w.re : ℂ) + (v : ℂ) * Complex.I) - u).re = 0 := by rw [hzero]; simp
        have hw0 : w.re - u.re = 0 := by linarith
        have hne2 : w.re ≠ u.re := ne_of_gt hu.2.1
        exact hne2 (by linarith)
      fun_prop
    exact hc.intervalIntegrable
  have h4 : IntervalIntegrable (fun v : ℝ => c / (((z.re : ℂ) + (v : ℂ) * Complex.I) - u))
      volume z.im w.im := by
    have hc : ContinuousOn (fun v : ℝ => c / (((z.re : ℂ) + (v : ℂ) * Complex.I) - u))
        (Set.uIcc z.im w.im) := by
      intro v hv
      refine ContinuousAt.continuousWithinAt ?_
      have hne : ((z.re : ℂ) + (v : ℂ) * Complex.I) - u ≠ 0 := by
        intro hzero
        have hval : (((z.re : ℂ) + (v : ℂ) * Complex.I) - u).re = z.re - u.re := by simp
        have h0 : (((z.re : ℂ) + (v : ℂ) * Complex.I) - u).re = 0 := by rw [hzero]; simp
        have hz0 : z.re - u.re = 0 := by linarith
        have hne2 : z.re ≠ u.re := ne_of_lt hu.1
        exact hne2 (by linarith)
      fun_prop
    exact hc.intervalIntegrable
  exact ⟨h1, h2, h3, h4⟩

/-- rectangle integral of `c / (s − u)` is `c · 2πi` (u strictly inside). -/
lemma rectInt_polar_u {z w u : ℂ} (c : ℂ) (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hu : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    rectInt z w (fun s : ℂ => c / (s - u)) = c * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  calc
    rectInt z w (fun s : ℂ => c / (s - u))
        = rectInt z w (fun s : ℂ => c * (s - u)⁻¹) := by
          apply congrArg (rectInt z w)
          funext s
          exact div_eq_mul_inv c (s - u)
    _ = c * rectInt z w (fun s : ℂ => (s - u)⁻¹) := rectInt_const_mul c (fun s : ℂ => (s - u)⁻¹)
    _ = c * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
          have hsub : rectInt z w (fun s : ℂ => (s - u)⁻¹) =
              (2 : ℂ) * (Real.pi : ℂ) * Complex.I := by
            simpa [rectInt] using
              (Commons.Analysis.Complex.rectIntegral_sub_inv_inside (z := z) (w := w) (u := u)
                hzre hzim hu)
          rw [hsub]

/-- Cauchy: rectangle integral of a function differentiable on the closed rectangle is zero. -/
lemma rectInt_differentiableOn_zero {z w : ℂ} {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im)) :
    rectInt z w G = 0 := by
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G z w hG
  simpa [rectInt] using hc

/-- **P2 ENGINE — multi-pole residue theorem for a rectangle**: if the poles `u i` are
strictly inside and `G` is differentiable on the closed rectangle, then

    rectInt z w (fun t => (∑ i, c i / (t - u i)) + G t) = (∑ i, c i) · 2πi . -/
theorem rectInt_model_multi_pole {ι : Type*} [DecidableEq ι] {s : Finset ι} {z w : ℂ}
    (u c : ι → ℂ) {G : ℂ → ℂ}
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hu : ∀ i ∈ s, z.re < (u i).re ∧ (u i).re < w.re ∧ z.im < (u i).im ∧ (u i).im < w.im)
    (hG : DifferentiableOn ℂ G (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im)) :
    rectInt z w (fun t : ℂ => (∑ i ∈ s, c i / (t - u i)) + G t) =
      (∑ i ∈ s, c i) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  classical
  let P : ℂ → ℂ := fun t => ∑ i ∈ s, c i / (t - u i)
  have hP_edge : EdgeInt z w P := by
    dsimp [P]
    exact EdgeInt.sum s (fun i t => c i / (t - u i)) (fun i hi => EdgeInt.polar (c i) (hu i hi))
  have hG_edge : EdgeInt z w G := EdgeInt.of_continuousOn hG.continuousOn
  calc
    rectInt z w (fun t : ℂ => (∑ i ∈ s, c i / (t - u i)) + G t)
        = rectInt z w P + rectInt z w G := by
            exact rectInt_add_edge (f := P) hP_edge hG_edge
    _ = (∑ i ∈ s, c i) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
          have hP : rectInt z w P = ∑ i ∈ s, rectInt z w (fun t => c i / (t - u i)) := by
            dsimp [P]
            exact rectInt_sum_edge s (fun i t => c i / (t - u i))
              (fun i hi => EdgeInt.polar (c i) (hu i hi))
          have hG0 : rectInt z w G = 0 := rectInt_differentiableOn_zero hG
          rw [hG0, add_zero, hP]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact rectInt_polar_u (c i) hzre hzim (hu i hi)


end Commons.NumberTheory.Zeta
end


-- ==== begin p2_zeroRect ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# P2-ζ (part 1): the finite zero-Finset of `ζ₁` inside the rectangle

`Commons.NumberTheory.Zeta.zetaZeroBall` (dispatched, child L271) produces, for each ball,
the Finset of ALL zeros of `riemannZeta₁` in that ball.  This module wraps it into the
Finset of zeros strictly inside an open rectangle (filtered), with the locational and
completeness lemmas the contour identity needs.  The parameterised form (with `hS` and
`hrect` as explicit inputs) keeps this module compiling independently of the child's
`zetaZeroBall`; instantiation with the commons lemma is one `rcases` away.
-/

open scoped BigOperators
open Complex

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- inside of the open rectangle with corners `z w`. -/
def RectInside (z w : ℂ) (ρ : ℂ) : Prop :=
  z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im

/-- zeros of `ζ₁` strictly inside the open rectangle `(z,w)`, taken from a complete
zero-Finset `S` of a ball around `0` containing the closed rectangle. -/
noncomputable def zetaZeroRectFinset {R : ℝ} (hR : 0 ≤ R) (S : Finset ℂ)
    (hS : ∀ ρ : ℂ, ρ ∈ S ↔ ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta₁ ρ = 0)
    (z w : ℂ) : Finset ℂ := by
  classical
  exact S.filter (fun ρ => RectInside z w ρ)

lemma memS_zetaZeroRectFinset {R : ℝ} (hR : 0 ≤ R) {S : Finset ℂ}
    (hS : ∀ ρ : ℂ, ρ ∈ S ↔ ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta₁ ρ = 0)
    {z w ρ : ℂ} :
    ρ ∈ zetaZeroRectFinset hR S hS z w ↔ ρ ∈ S ∧ RectInside z w ρ := by
  classical
  simp [zetaZeroRectFinset]

lemma zetaZeroRectFinset_in_S {R : ℝ} (hR : 0 ≤ R) {S : Finset ℂ}
    (hS : ∀ ρ : ℂ, ρ ∈ S ↔ ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta₁ ρ = 0)
    {z w ρ : ℂ} (hρ : ρ ∈ zetaZeroRectFinset hR S hS z w) : ρ ∈ S := by
  rw [memS_zetaZeroRectFinset hR hS] at hρ
  exact hρ.1

lemma zetaZeroRectFinset_inside {R : ℝ} (hR : 0 ≤ R) {S : Finset ℂ}
    (hS : ∀ ρ : ℂ, ρ ∈ S ↔ ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta₁ ρ = 0)
    {z w ρ : ℂ} (hρ : ρ ∈ zetaZeroRectFinset hR S hS z w) : RectInside z w ρ := by
  rw [memS_zetaZeroRectFinset hR hS] at hρ
  exact hρ.2

lemma zetaZeroRectFinset_zero {R : ℝ} (hR : 0 ≤ R) {S : Finset ℂ}
    (hS : ∀ ρ : ℂ, ρ ∈ S ↔ ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta₁ ρ = 0)
    {z w ρ : ℂ} (hρ : ρ ∈ zetaZeroRectFinset hR S hS z w) : riemannZeta₁ ρ = 0 := by
  have hS' : ρ ∈ S := zetaZeroRectFinset_in_S hR hS hρ
  have hspec := hS ρ
  rw [hspec] at hS'
  exact hS'.2

lemma zetaZeroRectFinset_in_ball {R : ℝ} (hR : 0 ≤ R) {S : Finset ℂ}
    (hS : ∀ ρ : ℂ, ρ ∈ S ↔ ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta₁ ρ = 0)
    {z w ρ : ℂ} (hρ : ρ ∈ zetaZeroRectFinset hR S hS z w) :
    ρ ∈ Metric.closedBall (0 : ℂ) R := by
  have hS' : ρ ∈ S := zetaZeroRectFinset_in_S hR hS hρ
  have hspec := hS ρ
  rw [hspec] at hS'
  exact hS'.1

/-- completeness: every zero of `ζ₁` strictly inside the open rectangle (whose closed
rectangle lies in the ball) is an element of the Finset. -/
lemma zetaZeroRectFinset_complete {R : ℝ} (hR : 0 ≤ R) {S : Finset ℂ}
    (hS : ∀ ρ : ℂ, ρ ∈ S ↔ ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta₁ ρ = 0)
    {z w ρ : ℂ}
    (hrect : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → ‖s‖ ≤ R)
    (hin : RectInside z w ρ) (hρ0 : riemannZeta₁ ρ = 0) :
    ρ ∈ zetaZeroRectFinset hR S hS z w := by
  rw [memS_zetaZeroRectFinset hR hS]
  constructor
  · rw [hS]
    constructor
    · apply Metric.mem_closedBall.mpr
      have hin' : z.re ≤ ρ.re ∧ ρ.re ≤ w.re ∧ z.im ≤ ρ.im ∧ ρ.im ≤ w.im := by
        exact ⟨le_of_lt hin.1, le_of_lt hin.2.1, le_of_lt hin.2.2.1, le_of_lt hin.2.2.2⟩
      have hb := hrect ρ hin'.1 hin'.2.1 hin'.2.2.1 hin'.2.2.2
      simpa [dist_eq_norm, sub_zero] using hb
    · exact hρ0
  · exact hin

/-- `1` is not a zero of `ζ₁`, so the pole `s = 1` is not among the zero-Finset elements. -/
lemma one_not_mem_zetaZeroRectFinset {R : ℝ} (hR : 0 ≤ R) {S : Finset ℂ}
    (hS : ∀ ρ : ℂ, ρ ∈ S ↔ ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta₁ ρ = 0)
    {z w : ℂ} : (1 : ℂ) ∉ zetaZeroRectFinset hR S hS z w := by
  intro h
  have h1S : (1 : ℂ) ∈ S := zetaZeroRectFinset_in_S hR hS h
  have hspec := hS (1 : ℂ)
  rw [hspec] at h1S
  have hz : riemannZeta₁ (1 : ℂ) = 0 := h1S.2
  exact zero_ne_one (hz.symm.trans riemannZeta₁_one)



end Commons.NumberTheory.Zeta
end


-- ==== begin p2_zeroRect_inst ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# P2-ζ (part 1, instantiation): the concrete finite zero-Finset inside the rectangle

Instantiation of the parameterised `p2_zeroRect.lean` with the commons lemma
`Commons.NumberTheory.Zeta.zetaZeroBall` (which provides, for each ball, the complete Finset
of zeros of `riemannZeta₁` in that ball).
-/

open scoped BigOperators
open Complex

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- the complete zero-Finset of `ζ₁` in `closedBall 0 R` (choice from the commons lemma). -/
noncomputable def zetaZeroBallFin (R : ℝ) (hR : 0 ≤ R) : Finset ℂ :=
  Classical.choose (zetaZeroBall R hR)

lemma zetaZeroBallFin_spec (R : ℝ) (hR : 0 ≤ R) (ρ : ℂ) :
    ρ ∈ zetaZeroBallFin R hR ↔ ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta₁ ρ = 0 :=
  Classical.choose_spec (zetaZeroBall R hR) ρ

/-- the concrete finite zero-Finset of `ζ₁` strictly inside the open rectangle `(z,w)`. -/
noncomputable def zetaZeroRectFin {R : ℝ} (hR : 0 ≤ R) (z w : ℂ) : Finset ℂ :=
  zetaZeroRectFinset hR (zetaZeroBallFin R hR) (zetaZeroBallFin_spec R hR) z w

lemma memS_zetaZeroRectFin {R : ℝ} (hR : 0 ≤ R) {z w ρ : ℂ} :
    ρ ∈ zetaZeroRectFin (R := R) hR z w ↔ ρ ∈ zetaZeroBallFin R hR ∧ RectInside z w ρ := by
  dsimp [zetaZeroRectFin]
  exact memS_zetaZeroRectFinset hR (zetaZeroBallFin_spec R hR)

lemma zetaZeroRectFin_inside {R : ℝ} (hR : 0 ≤ R) {z w ρ : ℂ}
    (hρ : ρ ∈ zetaZeroRectFin (R := R) hR z w) : RectInside z w ρ :=
  zetaZeroRectFinset_inside hR (zetaZeroBallFin_spec R hR) hρ

lemma zetaZeroRectFin_zero {R : ℝ} (hR : 0 ≤ R) {z w ρ : ℂ}
    (hρ : ρ ∈ zetaZeroRectFin (R := R) hR z w) : riemannZeta₁ ρ = 0 :=
  zetaZeroRectFinset_zero hR (zetaZeroBallFin_spec R hR) hρ

lemma zetaZeroRectFin_in_ball {R : ℝ} (hR : 0 ≤ R) {z w ρ : ℂ}
    (hρ : ρ ∈ zetaZeroRectFin (R := R) hR z w) : ρ ∈ Metric.closedBall (0 : ℂ) R :=
  zetaZeroRectFinset_in_ball hR (zetaZeroBallFin_spec R hR) hρ

/-- completeness of the concrete Finset: every zero of `ζ₁` strictly inside the open
rectangle is an element (closed rectangle assumed inside the ball). -/
lemma zetaZeroRectFin_complete {R : ℝ} (hR : 0 ≤ R) {z w ρ : ℂ}
    (hrect : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → ‖s‖ ≤ R)
    (hin : RectInside z w ρ) (hρ0 : riemannZeta₁ ρ = 0) :
    ρ ∈ zetaZeroRectFin (R := R) hR z w := by
  dsimp [zetaZeroRectFin]
  exact zetaZeroRectFinset_complete hR (zetaZeroBallFin_spec R hR) hrect hin hρ0

/-- the pole `s = 1` is not among the zero elements. -/
lemma one_not_mem_zetaZeroRectFin {R : ℝ} (hR : 0 ≤ R) {z w : ℂ} :
    (1 : ℂ) ∉ zetaZeroRectFin (R := R) hR z w := by
  dsimp [zetaZeroRectFin]
  exact one_not_mem_zetaZeroRectFinset hR (zetaZeroBallFin_spec R hR)



end Commons.NumberTheory.Zeta
end


-- ==== begin p2_rectIdentity ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# T-R3.1 spine: the truncated von Mangoldt rectangle identity

For the rectangle with corners `z := a − i·T′`, `w := b + i·T′` (`0 < a < 1 < b`, `T′ > 0`,
boundary free of zeros), with `Z` the Finset of zeros of `ζ₁` strictly inside
(`zetaZeroRectFin`), the model integrand

    model(x,Z,G)(t) := (Σ_{ρ ∈ insert 1 Z} coeff(ρ)/(t−ρ)) + G(t)
    coeff(1) = x ;  coeff(ρ) = −m_ρ·x^ρ/ρ for ρ ∈ Z   (m_ρ = zeta1Order ρ)

satisfies, for any `G` differentiable on the closed rectangle (P2 engine):

    rectInt z w model = 2πi · (x − Σ_{ρ∈Z} m_ρ·x^ρ/ρ)        (engine sum, proved below)

Once the remainder construction shows `G` differentiable with `psiIntF x` agreeing with
`model` on the boundary (per-zero pole removal via P0.5 + dslope difference quotients), the
same identity holds for `psiIntF x` — the contour identity that feeds the truncated Perron
formula and yields the explicit formula.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- lower-left corner `a − i·T′` of the contour rectangle. -/
def zRect (a Tp : ℝ) : ℂ := (a : ℂ) - Complex.I * (Tp : ℂ)

/-- upper-right corner `b + i·T′` of the contour rectangle. -/
def wRect (b Tp : ℝ) : ℂ := (b : ℂ) + Complex.I * (Tp : ℂ)

lemma zRect_re (a Tp : ℝ) : (zRect a Tp).re = a := by simp [zRect]
lemma zRect_im (a Tp : ℝ) : (zRect a Tp).im = -Tp := by simp [zRect]
lemma wRect_re (b Tp : ℝ) : (wRect b Tp).re = b := by simp [wRect]
lemma wRect_im (b Tp : ℝ) : (wRect b Tp).im = Tp := by simp [wRect]

/-- the closed contour rectangle (as a set). -/
def closedContourRect (a b Tp : ℝ) : Set ℂ :=
  Set.uIcc a b ×ℂ Set.uIcc (-Tp) Tp

/-- the multiplicity of the zero `ρ` of `ζ₁` (from `zeta1_logDeriv_pole_removal`). -/
noncomputable def zeta1Order (ρ : ℂ) : ℕ :=
  if h : riemannZeta₁ ρ = 0 then Classical.choose (zeta1_logDeriv_pole_removal ρ h) else 0

lemma zeta1Order_ge_one {ρ : ℂ} (hρ : riemannZeta₁ ρ = 0) : 1 ≤ zeta1Order ρ := by
  unfold zeta1Order
  rw [dif_pos hρ]
  exact (Classical.choose_spec (zeta1_logDeriv_pole_removal ρ hρ)).1

/-- per-zero coefficient: `x` at `s = 1`, `−m_s·x^s/s` elsewhere (m_s := zeta1Order s). -/
noncomputable def rectCoeff (x : ℝ) (s : ℂ) : ℂ :=
  if s = 1 then (x : ℂ) else - (zeta1Order s : ℂ) * (x : ℂ) ^ s / s

lemma rectCoeff_one (x : ℝ) : rectCoeff x (1 : ℂ) = (x : ℂ) := by
  unfold rectCoeff
  simp

lemma rectCoeff_of_ne_one {x : ℝ} {s : ℂ} (hs : s ≠ 1) :
    rectCoeff x s = - (zeta1Order s : ℂ) * (x : ℂ) ^ s / s := by
  unfold rectCoeff
  rw [if_neg hs]

/-- the zero Finset of the contour rectangle at height `Tp` (zeros strictly inside). -/
noncomputable def zRectZeros {R : ℝ} (hR : 0 ≤ R) (a b Tp : ℝ) : Finset ℂ :=
  zetaZeroRectFin hR (zRect a Tp) (wRect b Tp)

lemma mem_zRectZeros_inside {R : ℝ} (hR : 0 ≤ R) (a b Tp : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ zRectZeros hR a b Tp) : RectInside (zRect a Tp) (wRect b Tp) ρ := by
  dsimp [zRectZeros] at hρ
  exact zetaZeroRectFin_inside hR hρ

lemma one_not_mem_zRectZeros {R : ℝ} (hR : 0 ≤ R) (a b Tp : ℝ) : (1 : ℂ) ∉ zRectZeros hR a b Tp := by
  dsimp [zRectZeros]
  exact one_not_mem_zetaZeroRectFin hR

lemma zRectZeros_zero {R : ℝ} (hR : 0 ≤ R) (a b Tp : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ zRectZeros hR a b Tp) : riemannZeta₁ ρ = 0 := by
  dsimp [zRectZeros] at hρ
  exact zetaZeroRectFin_zero hR hρ

/-- the model integrand of the contour identity (sum over the zeros plus the pole at 1,
plus the differentiable remainder `G`). -/
noncomputable def rectModel (x : ℝ) {R : ℝ} (hR : 0 ≤ R) (a b Tp : ℝ) (G : ℂ → ℂ) : ℂ → ℂ :=
  fun t => (∑ ρ ∈ insert 1 (zRectZeros hR a b Tp), rectCoeff x ρ / (t - ρ)) + G t

/-- **ENGINE-SUM half of the spine**: for any `G` differentiable on the closed rectangle and
any parameters with `a < 1 < b`, `0 < T′`, the boundary rectangle integral of the model is
`2πi·(x − Σ_{ρ∈Z} m_ρ·x^ρ/ρ)`.  (The zeros `Z` are those strictly inside; the pole `s = 1`
carries `x`, each zero carries `−m_ρ·x^ρ/ρ`.) -/
theorem rectInt_engineSum_zeroRect {R a b Tp x : ℝ} {G : ℂ → ℂ}
    (hR : 0 ≤ R) (hab : a < b) (hTp : 0 < Tp)
    (h1a : a < 1) (h1b : 1 < b)
    (hG : DifferentiableOn ℂ G (closedContourRect a b Tp)) :
    rectInt (zRect a Tp) (wRect b Tp) (rectModel x hR a b Tp G) =
      ((x : ℂ) - ∑ ρ ∈ zRectZeros hR a b Tp,
          (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ) *
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  let Z : Finset ℂ := zRectZeros hR a b Tp
  have hone : (1 : ℂ) ∉ Z := by dsimp [Z]; exact one_not_mem_zRectZeros hR a b Tp
  have hzre : (zRect a Tp).re < (wRect b Tp).re := by rw [zRect_re, wRect_re]; exact hab
  have him : (zRect a Tp).im < (wRect b Tp).im := by rw [zRect_im, wRect_im]; linarith
  have hu1 : RectInside (zRect a Tp) (wRect b Tp) (1 : ℂ) := by
    dsimp [RectInside]
    rw [zRect_re, wRect_re, zRect_im, wRect_im]
    exact ⟨h1a, h1b, by linarith, by linarith⟩
  have hu : ∀ ρ : ℂ, ρ ∈ insert 1 Z → RectInside (zRect a Tp) (wRect b Tp) ρ := by
    intro ρ hρ
    rw [Finset.mem_insert] at hρ
    rcases hρ with rfl | hρZ
    · exact hu1
    · dsimp [Z] at hρZ
      exact zetaZeroRectFin_inside hR hρZ
  have hG' : DifferentiableOn ℂ G
      (Set.uIcc (zRect a Tp).re (wRect b Tp).re ×ℂ Set.uIcc (zRect a Tp).im (wRect b Tp).im) := by
    simpa [closedContourRect, zRect_re, wRect_re, zRect_im, wRect_im] using hG
  have hEng := rectInt_model_multi_pole (ι := ℂ) (s := insert 1 Z)
    (u := fun s : ℂ => s) (c := rectCoeff x)
    (z := zRect a Tp) (w := wRect b Tp) (G := G) hzre him hu hG' 
  have hLHS : rectInt (zRect a Tp) (wRect b Tp) (rectModel x hR a b Tp G) =
      rectInt (zRect a Tp) (wRect b Tp) (fun t : ℂ =>
        (∑ ρ ∈ insert 1 Z, rectCoeff x ρ / (t - ρ)) + G t) := by
    apply congrArg (rectInt (zRect a Tp) (wRect b Tp))
    funext t
    rfl
  have hρ1 : ∀ ρ : ℂ, ρ ∈ Z → ρ ≠ 1 := by
    intro ρ hρ hρ1
    have h1Z : (1 : ℂ) ∈ Z := by simpa [hρ1] using hρ
    exact (one_not_mem_zRectZeros hR a b Tp) h1Z
  have hper : ∀ ρ : ℂ, ρ ∈ Z →
      rectCoeff x ρ = - ((zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ) := by
    intro ρ hρ
    rw [rectCoeff_of_ne_one (hρ1 ρ hρ)]
    ring
  have hsum : (∑ ρ ∈ insert 1 Z, rectCoeff x ρ) =
      (x : ℂ) - ∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
    calc
      (∑ ρ ∈ insert 1 Z, rectCoeff x ρ)
          = rectCoeff x 1 + (∑ ρ ∈ Z, rectCoeff x ρ) := by rw [Finset.sum_insert hone]
      _ = (x : ℂ) + (∑ ρ ∈ Z, rectCoeff x ρ) := by rw [rectCoeff_one]
      _ = (x : ℂ) + (∑ ρ ∈ Z, - ((zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ)) := by
            apply congrArg (fun v : ℂ => (x : ℂ) + v)
            exact Finset.sum_congr rfl (by intro ρ hρ; exact hper ρ hρ)
      _ = (x : ℂ) - ∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
            rw [Finset.sum_neg_distrib]
            ring
  calc
    rectInt (zRect a Tp) (wRect b Tp) (rectModel x hR a b Tp G)
        = rectInt (zRect a Tp) (wRect b Tp) (fun t : ℂ =>
            (∑ ρ ∈ insert 1 Z, rectCoeff x ρ / (t - ρ)) + G t) := hLHS
    _ = (∑ ρ ∈ insert 1 Z, rectCoeff x ρ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := hEng
    _ = ((x : ℂ) - ∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ) *
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by rw [hsum]


end Commons.NumberTheory.Zeta
end


-- ==== begin p2_poleLocal ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# T-R3.1 boundary-agreement (local patch): pole removal at a single zero

Around a zero `ρ` of `ζ₁` (multiplicity `m := zeta1Order ρ`), the ζ₁-form of the Perron
integrand

    psiIntF1 x s := −(ζ₁′/ζ₁)(s)·x^s/s + x^s/(s·(s−1))

has a simple pole with residue `−m·x^ρ/ρ`; hence `psiIntF1 x s + m·x^ρ/ρ·(s−ρ)⁻¹` extends
analytically through `ρ`.  Explicitly: with `F₀` the P0.5 pole-removal function and
`DQ := dslope (x^·/·) ρ` the difference quotient of the analytic map `w ↦ x^w/w`,

    F(s) := −F₀(s)·(x^s/s) − m·DQ(s) + x^s/(s·(s−1))

is analytic at ρ and agrees on a punctured neighbourhood.  This is the local "junk-at-poles"
value-patching lemma; the global remainder `G` is a finite sum of such patches.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- the ζ₁-form of the Perron integrand (equals `psiIntF x s` wherever `ζ₁ s ≠ 0`, `s ≠ 1`). -/
def psiIntF1 (x : ℝ) (s : ℂ) : ℂ :=
  - (logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s) + (x : ℂ) ^ s / (s * (s - 1))

/-- analyticity of `w ↦ x^w / w` at a nonzero point (`x > 0`). -/
lemma cpow_div_self_analyticAt {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ0 : ρ ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => (x : ℂ) ^ w / w) ρ := by
  have hpow := (Commons.NumberTheory.Zeta.cpow_differentiable hx).analyticAt ρ
  exact AnalyticAt.div hpow analyticAt_id hρ0

/-- generic: the dslope (difference quotient with the derivative value patched at the point)
of a function differentiable on an open neighbourhood of `c` is analytic at `c`. -/
lemma analyticAt_dslope_of_differentiableOn {f : ℂ → ℂ} {c : ℂ} {s : Set ℂ}
    (hopen : IsOpen s) (hcs : c ∈ s) (hd : DifferentiableOn ℂ f s) :
    AnalyticAt ℂ (dslope f c) c := by
  have hd' : DifferentiableOn ℂ (dslope f c) s :=
    (Complex.differentiableOn_dslope (f := f) (c := c) (s := s) (hopen.mem_nhds hcs)).mpr hd
  have hnear : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ (dslope f c) z := by
    filter_upwards [hopen.mem_nhds hcs] with z hz
    exact hd'.differentiableAt (hopen.mem_nhds hz)
  have hd_ev : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ (dslope f c) z :=
    hnear.filter_mono nhdsWithin_le_nhds
  have hc : ContinuousAt (dslope f c) c :=
    continuousAt_dslope_same.2 (hd.differentiableAt (hopen.mem_nhds hcs))
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd_ev hc

/-- punctured equality of `dslope f c` with the raw difference quotient `(f − f c)/(·−c)`. -/
lemma dslope_eventuallyEq_quotient (f : ℂ → ℂ) (c : ℂ) :
    Filter.Eventually (fun s => dslope f c s = (f s - f c) / (s - c))
      (nhdsWithin c {s : ℂ | s ≠ c}) := by
  have h := dslope_eventuallyEq_slope_nhdsNE (f := f) (a := c)
  filter_upwards [h] with s hs
  unfold slope at hs
  rw [div_eq_mul_inv]
  rw [hs]
  exact mul_comm _ _

/-- **LOCAL POLE REMOVAL**: at a zero `ρ` of `ζ₁` (multiplicity `zeta1Order ρ`), the function
`psiIntF1 x s + m·x^ρ/ρ·(s−ρ)⁻¹` extends analytically through `ρ`. -/
theorem psiIntF1_pole_removal_at_zero {x : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hρ : riemannZeta₁ ρ = 0) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F ρ ∧
      Filter.Eventually (fun s => F s = psiIntF1 x s +
          (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ * (s - ρ)⁻¹)
        (nhdsWithin ρ {s : ℂ | s ≠ ρ}) := by
  classical
  let m : ℕ := zeta1Order ρ
  have hm_eq : Classical.choose (zeta1_logDeriv_pole_removal ρ hρ) = m := by
    dsimp [m, zeta1Order]
    rw [dif_pos hρ]
  have hspec := Classical.choose_spec (zeta1_logDeriv_pole_removal ρ hρ)
  have hspec' : 1 ≤ m ∧ ∃ F0 : ℂ → ℂ, AnalyticAt ℂ F0 ρ ∧
      Filter.Eventually (fun s => F0 s = logDeriv riemannZeta₁ s - (m : ℂ) / (s - ρ))
        (nhdsWithin ρ {s : ℂ | s ≠ ρ}) := by
    simpa [hm_eq] using hspec
  rcases hspec' with ⟨hm1, F0, hF0a, hF0e⟩
  let DQ : ℂ → ℂ := dslope (fun w : ℂ => (x : ℂ) ^ w / w) ρ
  let F : ℂ → ℂ := fun s =>
    - (F0 s * ((x : ℂ) ^ s / s)) - (m : ℂ) * DQ s + (x : ℂ) ^ s / (s * (s - 1))
  refine ⟨F, ?_, ?_⟩
  · dsimp [F]
    have hxpow : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) ρ :=
      (Commons.NumberTheory.Zeta.cpow_differentiable hx).analyticAt ρ
    have hdiv_s : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) ρ :=
      cpow_div_self_analyticAt hx hρ0
    have hDQ : AnalyticAt ℂ DQ ρ := by
      dsimp [DQ]
      exact analyticAt_dslope_of_differentiableOn (f := fun w : ℂ => (x : ℂ) ^ w / w)
        (s := {w : ℂ | w ≠ 0}) isOpen_ne hρ0
        (Commons.NumberTheory.Zeta.cpow_div_self_differentiableOn hx)
    have hdiv_ss : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / (s * (s - 1))) ρ := by
      have hS : AnalyticAt ℂ (fun s : ℂ => s * (s - 1)) ρ :=
        analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
      have hS0 : ρ * (ρ - 1) ≠ 0 := mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)
      exact AnalyticAt.div hxpow hS hS0
    have hterm1 : AnalyticAt ℂ (fun s : ℂ => - (F0 s * ((x : ℂ) ^ s / s))) ρ :=
      (hF0a.mul hdiv_s).neg
    have hterm2 : AnalyticAt ℂ (fun s : ℂ => (m : ℂ) * DQ s) ρ :=
      analyticAt_const.mul hDQ
    exact (hterm1.sub hterm2).add hdiv_ss
  · have hF0e' : Filter.Eventually (fun s => F0 s = logDeriv riemannZeta₁ s - (m : ℂ) * (s - ρ)⁻¹)
        (nhdsWithin ρ {s : ℂ | s ≠ ρ}) := by
      simpa [div_eq_mul_inv] using hF0e
    have hDQe : Filter.Eventually (fun s => DQ s = ((x : ℂ) ^ s / s - (x : ℂ) ^ ρ / ρ) * (s - ρ)⁻¹)
        (nhdsWithin ρ {s : ℂ | s ≠ ρ}) := by
      have h := dslope_eventuallyEq_quotient (fun w : ℂ => (x : ℂ) ^ w / w) ρ
      filter_upwards [h] with s hs
      have hs' : dslope (fun w : ℂ => (x : ℂ) ^ w / w) ρ s =
          ((x : ℂ) ^ s / s - (x : ℂ) ^ ρ / ρ) * (s - ρ)⁻¹ := by
        rw [hs]
        rw [div_eq_mul_inv]
      simpa [DQ] using hs'
    have hz0 : Filter.Eventually (fun s => s ≠ 0) (nhdsWithin ρ {s : ℂ | s ≠ ρ}) := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_ne.mem_nhds hρ0] with s hs
      exact fun _ => by simpa using hs
    have hz1 : Filter.Eventually (fun s => s ≠ 1) (nhdsWithin ρ {s : ℂ | s ≠ ρ}) := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_ne.mem_nhds hρ1] with s hs
      exact fun _ => by simpa using hs
    filter_upwards [hF0e', hDQe, hz0, hz1, self_mem_nhdsWithin (a := ρ) (s := {z : ℂ | z ≠ ρ})]
      with s hF0s hDQs hs0 hs1 hsne
    dsimp [F]
    rw [hDQs]
    dsimp [psiIntF1, DQ]
    -- hF0s : F0 s = logDeriv ζ₁ s − m·(s−ρ)⁻¹  ⇒  logDeriv ζ₁ s = F0 s + m·(s−ρ)⁻¹
    have hld : logDeriv riemannZeta₁ s = F0 s + (m : ℂ) * (s - ρ)⁻¹ := by
      rw [hF0s]
      ring
    rw [hld]
    field_simp [hs0, hs1, sub_ne_zero.mpr hsne]
    ring

/-- **LOCAL POLE REMOVAL at `s = 1`**: in the ζ₁-form of the Perron integrand the pole at
`s = 1` has principal part `x/(s−1)`; subtracting it leaves an analytic germ.  Concretely
`−(ζ₁′/ζ₁)(s)·x^s/s + dslope(x^·/·) 1 s` is analytic at `1` (the second summand patches
`x^s/(s(s−1)) − x/(s−1)`). -/
lemma psiIntF1_sub_polar_one_removal {x : ℝ} (hx : 0 < x) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (1 : ℂ) ∧
      Filter.Eventually (fun s => F s = psiIntF1 x s - (x : ℂ) / (s - 1))
        (nhdsWithin (1 : ℂ) {s : ℂ | s ≠ 1}) := by
  let f : ℂ → ℂ := fun w : ℂ => (x : ℂ) ^ w / w
  let F : ℂ → ℂ := fun s => - (logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s) + dslope f 1 s
  refine ⟨F, ?_, ?_⟩
  · dsimp [F]
    have hAnLog : AnalyticAt ℂ (fun s : ℂ => logDeriv riemannZeta₁ s) (1 : ℂ) := by
      -- ζ₁′/ζ₁ = (deriv ζ₁)·ζ₁⁻¹ ; ζ₁ analytic everywhere, ζ₁(1)=1 ≠ 0
      have hd : AnalyticAt ℂ (fun s : ℂ => deriv riemannZeta₁ s) (1 : ℂ) :=
        (Differentiable.deriv differentiable_riemannZeta₁).analyticAt 1
      have hz : AnalyticAt ℂ riemannZeta₁ (1 : ℂ) :=
        differentiable_riemannZeta₁.analyticAt 1
      have h1ne : riemannZeta₁ (1 : ℂ) ≠ 0 := by
        rw [riemannZeta₁_one]
        norm_num
      exact AnalyticAt.div hd hz h1ne
    have hdiv_s : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) (1 : ℂ) :=
      cpow_div_self_analyticAt hx (by norm_num : (1 : ℂ) ≠ 0)
    have hd0 : AnalyticAt ℂ (dslope f 1) (1 : ℂ) := by
      dsimp [f]
      exact analyticAt_dslope_of_differentiableOn (f := fun w : ℂ => (x : ℂ) ^ w / w)
        (s := {w : ℂ | w ≠ 0}) isOpen_ne (by norm_num : (1 : ℂ) ∈ {w : ℂ | w ≠ 0})
        (Commons.NumberTheory.Zeta.cpow_div_self_differentiableOn hx)
    have hneg : AnalyticAt ℂ (fun s : ℂ => - logDeriv riemannZeta₁ s) (1 : ℂ) :=
      AnalyticAt.neg hAnLog
    have h1 : AnalyticAt ℂ (fun s : ℂ => - logDeriv riemannZeta₁ s * ((x : ℂ) ^ s / s)) (1 : ℂ) :=
      AnalyticAt.mul hneg hdiv_s
    exact AnalyticAt.add h1 hd0
  · have hfE : Filter.Eventually (fun s => dslope f 1 s = (f s - f 1) / (s - 1))
        (nhdsWithin (1 : ℂ) {s : ℂ | s ≠ 1}) :=
      dslope_eventuallyEq_quotient f (1 : ℂ)
    have hf1 : f 1 = (x : ℂ) := by
      dsimp [f]
      simp
    have hz1 : Filter.Eventually (fun s => s ≠ 1) (nhdsWithin (1 : ℂ) {s : ℂ | s ≠ 1}) := by
      exact self_mem_nhdsWithin (a := (1 : ℂ)) (s := {s : ℂ | s ≠ 1})
    filter_upwards [hfE, hz1] with s hs hsn
    dsimp [F]
    rw [hs]
    rw [hf1]
    dsimp [f, psiIntF1]
    field_simp [sub_ne_zero.mpr hsn]
    ring

/-- the chosen analytic removal function at a zero `ρ` (extension of
`psiIntF1 x s + m·x^ρ/ρ·(s−ρ)⁻¹`, i.e. of `psiIntF1 x s − c_ρ·(s−ρ)⁻¹` with
`c_ρ = −m·x^ρ/ρ`). -/
noncomputable def psiZeroRemoval (x : ℝ) (hx : 0 < x) (ρ : ℂ)
    (hρ : riemannZeta₁ ρ = 0) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) : ℂ → ℂ :=
  Classical.choose (psiIntF1_pole_removal_at_zero (x := x) (ρ := ρ) hx hρ hρ0 hρ1)

lemma psiZeroRemoval_analyticAt {x : ℝ} (hx : 0 < x) (ρ : ℂ)
    (hρ : riemannZeta₁ ρ = 0) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    AnalyticAt ℂ (psiZeroRemoval x hx ρ hρ hρ0 hρ1) ρ :=
  (Classical.choose_spec (psiIntF1_pole_removal_at_zero (x := x) (ρ := ρ) hx hρ hρ0 hρ1)).1

lemma psiZeroRemoval_eventually {x : ℝ} (hx : 0 < x) (ρ : ℂ)
    (hρ : riemannZeta₁ ρ = 0) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    Filter.Eventually (fun s => psiZeroRemoval x hx ρ hρ hρ0 hρ1 s =
        psiIntF1 x s + (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ * (s - ρ)⁻¹)
      (nhdsWithin ρ {s : ℂ | s ≠ ρ}) :=
  (Classical.choose_spec (psiIntF1_pole_removal_at_zero (x := x) (ρ := ρ) hx hρ hρ0 hρ1)).2

/-- the chosen analytic removal function at `s = 1` (extension of `psiIntF1 x s − x/(s−1)`). -/
noncomputable def psiOneRemoval (x : ℝ) (hx : 0 < x) : ℂ → ℂ :=
  Classical.choose (psiIntF1_sub_polar_one_removal hx)

lemma psiOneRemoval_analyticAt {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℂ (psiOneRemoval x hx) (1 : ℂ) :=
  (Classical.choose_spec (psiIntF1_sub_polar_one_removal hx)).1

lemma psiOneRemoval_eventually {x : ℝ} (hx : 0 < x) :
    Filter.Eventually (fun s => psiOneRemoval x hx s = psiIntF1 x s - (x : ℂ) / (s - 1))
      (nhdsWithin (1 : ℂ) {s : ℂ | s ≠ 1}) :=
  (Classical.choose_spec (psiIntF1_sub_polar_one_removal hx)).2

end Commons.NumberTheory.Zeta
end


-- ==== begin p2_zeroFree ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# P2-ζ (part 2): the zero-free rectangle boundary

The truncated von Mangoldt contour identity needs the rectangle with corners
`z := a − i·T′`, `w := b + i·T′` (`0 < a < 1/2 < 1 ≤ b`), with `T′` chosen by
`exists_good_height`, to have a boundary free of zeros of `riemannZeta₁`:

  * vertical sides: right at `Re = b ≥ 1` — zero-free unconditionally
    (`riemannZeta_ne_zero_of_one_le_re`); left at `Re = a ∈ (0, 1/2)` — zero-free under RH
    (RH forces every non-trivial zero onto `Re = 1/2`);
  * horizontal sides `Im = ±T′` — zero-free for the `T′` produced by `exists_good_height`
    from the finite zero Finset of the surrounding box (they meet the corners only at the
    vertical sides, already handled).

This module proves the `ζ₁`-level vertical freeness and the bridge `ζ₁ s ≠ 0 ↔ ζ s ≠ 0`
(off `s = 1`, via `riemannZeta_eq_inv_sub_mul`), so the ζ-side facts transfer to ζ₁.
-/

open Complex

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- RH, mirrored below the critical line: no non-trivial zero has real part `< 1/2`. -/
theorem zeta_ne_zero_of_rh_lt_half (h : RiemannHypothesis) {s : ℂ}
    (hs0 : 0 < s.re) (hs : s.re < (1 / 2 : ℝ)) : riemannZeta s ≠ 0 := by
  intro h0
  have hs1 : s ≠ 1 := by
    intro hs1
    have hs_re : s.re = (1 : ℂ).re := by rw [hs1]
    rw [hs_re] at hs
    norm_num at hs
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    rw [hn] at hs0
    have hre : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
      norm_num
    rw [hre] at hs0
    have hn0 : (0 : ℝ) ≤ n + 1 := by positivity
    nlinarith
  have hhalf : s.re = 1 / 2 := h s h0 htriv hs1
  linarith

/-- for `s ≠ 1`, a zero of `ζ₁` is a zero of `ζ` and conversely (via `ζ(s) = (s−1)⁻¹ ζ₁(s)`). -/
lemma zeta1_ne_zero_iff_zeta_ne_zero {s : ℂ} (hs1 : s ≠ 1) :
    riemannZeta₁ s ≠ 0 ↔ riemannZeta s ≠ 0 := by
  have hs1c : (s : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hfac : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    have h := riemannZeta_eq_inv_sub_mul hs1
    rw [h]
    field_simp [hs1c]
  constructor
  · intro hz1 hz0
    apply hz1
    rw [hfac, hz0]
    ring
  · intro hz hz10
    have hmul : (s - 1) * riemannZeta s = 0 := by rw [← hfac, hz10]
    apply hz
    exact (mul_eq_zero.mp hmul).resolve_left hs1c

/-- `ζ₁` does not vanish on `Re s ≥ 1`. -/
lemma zeta1_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    exact (by norm_num : riemannZeta₁ 1 ≠ 0)
  · exact (zeta1_ne_zero_iff_zeta_ne_zero hs1).mpr (riemannZeta_ne_zero_of_one_le_re hs)

/-- under RH, `ζ₁` does not vanish in the strip `0 < Re s < 1/2`. -/
lemma zeta1_ne_zero_of_rh_lt_half (h : RiemannHypothesis) {s : ℂ}
    (hs0 : 0 < s.re) (hs : s.re < (1 / 2 : ℝ)) : riemannZeta₁ s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    norm_num at hs
  · exact (zeta1_ne_zero_iff_zeta_ne_zero hs1).mpr (zeta_ne_zero_of_rh_lt_half h hs0 hs)

/-- **vertical sides of the contour rectangle are zero-free**: right side at `Re = b ≥ 1`
(unconditional), left side at `Re = a ∈ (0, 1/2)` (under RH). -/
theorem zeta1_zero_free_vertical_sides (h : RiemannHypothesis) {a b : ℝ}
    (ha0 : 0 < a) (ha12 : a < (1 / 2 : ℝ)) (h1b : 1 ≤ b) :
    (∀ t : ℝ, riemannZeta₁ ((b : ℂ) + Complex.I * (t : ℂ)) ≠ 0) ∧
    (∀ t : ℝ, riemannZeta₁ ((a : ℂ) + Complex.I * (t : ℂ)) ≠ 0) := by
  constructor
  · intro t
    apply zeta1_ne_zero_of_one_le_re
    -- Re(b + it) = b ≥ 1
    have hre : (((b : ℂ) + Complex.I * (t : ℂ)).re) = b := by simp
    rw [hre]
    exact h1b
  · intro t
    apply zeta1_ne_zero_of_rh_lt_half h
    · have hre : (((a : ℂ) + Complex.I * (t : ℂ)).re) = a := by simp
      rw [hre]
      exact ha0
    · have hre : (((a : ℂ) + Complex.I * (t : ℂ)).re) = a := by simp
      rw [hre]
      exact ha12


end Commons.NumberTheory.Zeta
end


-- ==== begin p2_remainder ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# P2-ζ (part 2): the global differentiable remainder and the contour identity

For the rectangle with corners `z := a − i·T′`, `w := b + i·T′` (`0 < a < 1/2 < 1 < b`,
`T′ > 0`, closed rectangle inside `closedBall 0 R`, horizontal sides free of zeros:
`hgood : ∀ ρ, ζ₁ρ = 0 → ρ.im ≠ ±T′`; vertical sides free under RH), the remainder

    G(s) := patched (psiIntF1 x s − x/(s−1) − Σ_{ρ∈Z} coeff(ρ)/(s−ρ))

is made analytic at every pole point (`s = 1` and each `ρ ∈ Z`) by the per-pole removals
`psiOneRemoval`/`psiZeroRemoval`; off the poles it is the literal difference.  This module
proves `G` is differentiable on the closed rectangle and that `psiIntF1 x` agrees with
`rectModel x hR a b T′ G` on the boundary — hence, with the engine-sum theorem of
`p2_rectIdentity`,

    rectInt z w (psiIntF1 x) = 2πi·(x − Σ_{ρ∈Z} m_ρ·x^ρ/ρ)        (P4, THEOREM below).
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- membership in the closed contour rectangle, as scalar inequalities. -/
lemma mem_closedContourRect {a b Tp : ℝ} (hab : a ≤ b) (hT : -Tp ≤ Tp) (s : ℂ) :
    s ∈ closedContourRect a b Tp ↔ a ≤ s.re ∧ s.re ≤ b ∧ -Tp ≤ s.im ∧ s.im ≤ Tp := by
  rw [closedContourRect]
  rw [Set.uIcc_of_le hab, Set.uIcc_of_le hT]
  simp [mem_reProdIm]
  tauto

/-- an element of the zero Finset is a zero of `ζ₁` off `0` (given `0 < a`). -/
lemma zRectZeros_ne_zero {R : ℝ} (hR : 0 ≤ R) {a b Tp : ℝ} (ha0 : 0 < a) {ρ : ℂ}
    (hρ : ρ ∈ zRectZeros hR a b Tp) : ρ ≠ 0 := by
  intro h0
  have hin := mem_zRectZeros_inside hR a b Tp hρ
  dsimp [RectInside] at hin
  rw [zRect_re, wRect_re, zRect_im, wRect_im] at hin
  have hrea : a < ρ.re := hin.1
  rw [h0] at hrea
  norm_num at hrea
  linarith

/-- an element of the zero Finset is not `1`. -/
lemma zRectZeros_ne_one {R : ℝ} (hR : 0 ≤ R) {a b Tp : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zRectZeros hR a b Tp) : ρ ≠ 1 := by
  intro hρ1
  have h1Z : (1 : ℂ) ∈ zRectZeros hR a b Tp := by simpa [hρ1] using hρ
  exact one_not_mem_zRectZeros hR a b Tp h1Z

/-- the global patched remainder: `psiIntF1 − (pole at 1) − Σ_{ρ∈Z} coeff(ρ)/(·−ρ)`,
patched at `s = 1` and at each zero `ρ ∈ Z` by the per-pole analytic removals. -/
noncomputable def psiRemainderG (x : ℝ) (hx : 0 < x) {R : ℝ} (hR : 0 ≤ R)
    (a b Tp : ℝ) (ha0 : 0 < a) (s : ℂ) : ℂ :=
  if hs1 : s = 1 then
    psiOneRemoval x hx s - ∑ ρ ∈ zRectZeros hR a b Tp, rectCoeff x ρ / (s - ρ)
  else if hsZ : s ∈ zRectZeros hR a b Tp then
    psiZeroRemoval x hx s (zRectZeros_zero hR a b Tp hsZ)
      (zRectZeros_ne_zero hR ha0 hsZ) (zRectZeros_ne_one hR hsZ) s
      - (x : ℂ) / (s - 1) - ∑ ρ ∈ zRectZeros hR a b Tp, rectCoeff x ρ / (s - ρ)
  else
    psiIntF1 x s - (x : ℂ) / (s - 1) - ∑ ρ ∈ zRectZeros hR a b Tp, rectCoeff x ρ / (s - ρ)

/-- value of `G` off the pole set: it is the literal difference. -/
lemma psiRemainderG_eq_diff {x : ℝ} (hx : 0 < x) {R : ℝ} (hR : 0 ≤ R) {a b Tp : ℝ}
    (ha0 : 0 < a) {s : ℂ} (hs1 : s ≠ 1) (hsZ : s ∉ zRectZeros hR a b Tp) :
    psiRemainderG x hx hR a b Tp ha0 s =
      psiIntF1 x s - (x : ℂ) / (s - 1) -
        ∑ ρ ∈ zRectZeros hR a b Tp, rectCoeff x ρ / (s - ρ) := by
  unfold psiRemainderG
  simp [hs1, hsZ]

/-- pointwise: off the pole set, `psiIntF1 = rectModel(·,G)`. -/
lemma psiIntF1_eq_rectModel_add_remainder {x : ℝ} (hx : 0 < x) {R : ℝ} (hR : 0 ≤ R)
    {a b Tp : ℝ} (ha0 : 0 < a) {t : ℂ} (ht1 : t ≠ 1) (htZ : t ∉ zRectZeros hR a b Tp) :
    psiIntF1 x t = rectModel x hR a b Tp (psiRemainderG x hx hR a b Tp ha0) t := by
  have hG := psiRemainderG_eq_diff (x := x) (hx := hx) (hR := hR) (ha0 := ha0)
    (s := t) ht1 htZ
  let Z : Finset ℂ := zRectZeros hR a b Tp
  have hone : (1 : ℂ) ∉ Z := by dsimp [Z]; exact one_not_mem_zRectZeros hR a b Tp
  have hsplit : (∑ ρ ∈ insert 1 Z, rectCoeff x ρ / (t - ρ)) =
      (x : ℂ) / (t - 1) + (∑ ρ ∈ Z, rectCoeff x ρ / (t - ρ)) := by
    rw [Finset.sum_insert hone]
    rw [rectCoeff_one]
  symm
  calc
    rectModel x hR a b Tp (psiRemainderG x hx hR a b Tp ha0) t
        = (∑ ρ ∈ insert 1 Z, rectCoeff x ρ / (t - ρ)) + psiRemainderG x hx hR a b Tp ha0 t := rfl
    _ = (∑ ρ ∈ insert 1 Z, rectCoeff x ρ / (t - ρ)) +
          (psiIntF1 x t - (x : ℂ) / (t - 1) -
            ∑ ρ ∈ Z, rectCoeff x ρ / (t - ρ)) := by rw [hG]
    _ = ((x : ℂ) / (t - 1) + (∑ ρ ∈ Z, rectCoeff x ρ / (t - ρ))) +
          (psiIntF1 x t - (x : ℂ) / (t - 1) -
            ∑ ρ ∈ Z, rectCoeff x ρ / (t - ρ)) := by rw [hsplit]
    _ = psiIntF1 x t := by dsimp [Z]; ring

/-- finite sums of analytic functions are analytic. -/
lemma analyticAt_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {z : ℂ}
    (h : ∀ i : ι, i ∈ s → AnalyticAt ℂ (f i) z) :
    AnalyticAt ℂ (fun w : ℂ => ∑ i ∈ s, f i w) z := by
  classical
  exact (Finset.induction_on s (motive := fun u : Finset ι =>
    (∀ j : ι, j ∈ u → AnalyticAt ℂ (f j) z) → AnalyticAt ℂ (fun w : ℂ => ∑ j ∈ u, f j w) z)
    (by
      intro h0
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z))
    (by
      intro i t hit ih hAll
      have h2 : AnalyticAt ℂ (fun w : ℂ => f i w) z := hAll i (Finset.mem_insert_self i t)
      have h_t : ∀ j : ι, j ∈ t → AnalyticAt ℂ (f j) z := fun j hj => hAll j (Finset.mem_insert_of_mem hj)
      have h1 : AnalyticAt ℂ (fun w : ℂ => ∑ j ∈ t, f j w) z := ih h_t
      have hsum : (fun w : ℂ => ∑ j ∈ insert i t, f j w) =
          (fun w : ℂ => f i w + ∑ j ∈ t, f j w) := by
        funext w
        rw [Finset.sum_insert hit]
      rw [hsum]
      exact AnalyticAt.add h2 h1)) h

/-- eventually, a point outside a finite Finset stays outside. -/
lemma eventually_not_mem_finset {S : Finset ℂ} {s : ℂ} (hs : s ∉ S) :
    ∀ᶠ z in 𝓝 s, z ∉ S := by
  have hcl : IsClosed (S : Set ℂ) := (S.finite_toSet).isClosed
  have hop : IsOpen ((S : Set ℂ)ᶜ) := hcl.isOpen_compl
  have hmem : s ∈ (S : Set ℂ)ᶜ := hs
  exact Filter.eventually_of_mem (hop.mem_nhds hmem) (by intro z hz; exact hz)

/-- `ζ₁′/ζ₁` is analytic away from the zeros of `ζ₁`. -/
lemma logDeriv_zeta1_analyticAt {s : ℂ} (hs : riemannZeta₁ s ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ => logDeriv riemannZeta₁ z) s := by
  have hd : AnalyticAt ℂ (fun z : ℂ => deriv riemannZeta₁ z) s :=
    (Differentiable.deriv differentiable_riemannZeta₁).analyticAt s
  have hz : AnalyticAt ℂ riemannZeta₁ s := differentiable_riemannZeta₁.analyticAt s
  exact AnalyticAt.div hd hz hs

/-- `x^s/s` is analytic at `s` (for `0 < x`, `s ≠ 0`). -/
lemma cpow_div_self_analyticAt' {x : ℝ} (hx : 0 < x) {s : ℂ} (hs0 : s ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z / z) s :=
  cpow_div_self_analyticAt hx hs0

/-- an element of the zero Finset `Z` is not equal to `1` (also for `1 ∉ Z`). -/
lemma one_ne_of_mem_zRectZeros {R : ℝ} (hR : 0 ≤ R) {a b Tp : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zRectZeros hR a b Tp) : (1 : ℂ) ≠ ρ := by
  exact fun h => zRectZeros_ne_one hR hρ h.symm

/-- `Z.erase ρ`-membership: an element of the erased set is an element of `Z` different from
the erased element. -/
lemma mem_erase_zRectZeros {R : ℝ} (hR : 0 ≤ R) {a b Tp : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zRectZeros hR a b Tp) {u : ℂ} (hu : u ∈ (zRectZeros hR a b Tp).erase ρ) :
    u ∈ zRectZeros hR a b Tp ∧ u ≠ ρ := by
  have hu' := Finset.mem_erase.mp hu
  exact ⟨hu'.2, hu'.1⟩

/-- **closed-rectangle zeros are collected**: under RH (for the left vertical side) and
`hgood` (horizontal freeness), a zero of `ζ₁` lying in the closed rectangle is strictly
inside and hence is an element of the zero Finset `Z`. -/
lemma zeta1_zero_of_mem_closedContourRect (h : RiemannHypothesis) {R : ℝ} (hR : 0 ≤ R)
    {a b Tp : ℝ} (ha0 : 0 < a) (ha12 : a < (1 / 2 : ℝ)) (h1b : 1 < b) (hTp : 0 < Tp)
    (hrect : closedContourRect a b Tp ⊆ Metric.closedBall (0 : ℂ) R)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp)
    {s : ℂ} (hs : s ∈ closedContourRect a b Tp) (hz : riemannZeta₁ s = 0) :
    s ∈ zRectZeros hR a b Tp := by
  have hab : a ≤ b := by linarith
  have hT : -Tp ≤ Tp := by linarith
  have hmem := (mem_closedContourRect hab hT s).mp hs
  have hvf := zeta1_zero_free_vertical_sides h ha0 ha12 (le_of_lt h1b)
  have hs1 : a < s.re := by
    by_contra hnot
    have hle : s.re ≤ a := le_of_not_gt hnot
    have heq : s.re = a := le_antisymm hle hmem.1
    have hseq : s = (a : ℂ) + Complex.I * (s.im : ℂ) := by
        apply Complex.ext <;> simp [heq]
    rw [hseq] at hz
    exact (hvf.2 s.im) hz
  have hs2 : s.re < b := by
    by_contra hnot
    have hle : b ≤ s.re := le_of_not_gt hnot
    have heq : s.re = b := le_antisymm hmem.2.1 hle
    have hseq : s = (b : ℂ) + Complex.I * (s.im : ℂ) := by
        apply Complex.ext <;> simp [heq]
    rw [hseq] at hz
    exact (hvf.1 s.im) hz
  have hs3 : -Tp < s.im := by
    by_contra hnot
    have hle : s.im ≤ -Tp := le_of_not_gt hnot
    have heq : s.im = -Tp := le_antisymm hle hmem.2.2.1
    exact (hgood s hz).2 heq
  have hs4 : s.im < Tp := by
    by_contra hnot
    have hle : Tp ≤ s.im := le_of_not_gt hnot
    have heq : s.im = Tp := le_antisymm hmem.2.2.2 hle
    exact (hgood s hz).1 heq
  have hinside : RectInside (zRect a Tp) (wRect b Tp) s := by
    dsimp [RectInside]
    rw [zRect_re, wRect_re, zRect_im, wRect_im]
    exact ⟨hs1, hs2, hs3, hs4⟩
  have hrect' : ∀ u : ℂ, (zRect a Tp).re ≤ u.re → u.re ≤ (wRect b Tp).re →
      (zRect a Tp).im ≤ u.im → u.im ≤ (wRect b Tp).im → ‖u‖ ≤ R := by
    intro u h1u h2u h3u h4u
    have hu : u ∈ closedContourRect a b Tp := by
      rw [mem_closedContourRect hab hT u]
      exact ⟨by simpa [zRect_re] using h1u, ⟨by simpa [wRect_re] using h2u,
        ⟨by simpa [zRect_im] using h3u, by simpa [wRect_im] using h4u⟩⟩⟩
    have hub := hrect hu
    simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hub)
  have hrec := zetaZeroRectFin_complete hR hrect' hinside hz
  simpa [zRectZeros] using hrec

/-- a point of the closed rectangle that is not in `Z` is not a zero of `ζ₁`. -/
lemma closedRect_zeta1_ne_zero_of_not_mem_Z (h : RiemannHypothesis) {R : ℝ} (hR : 0 ≤ R)
    {a b Tp : ℝ} (ha0 : 0 < a) (ha12 : a < (1 / 2 : ℝ)) (h1b : 1 < b) (hTp : 0 < Tp)
    (hrect : closedContourRect a b Tp ⊆ Metric.closedBall (0 : ℂ) R)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp)
    {s : ℂ} (hs : s ∈ closedContourRect a b Tp) (hsZ : s ∉ zRectZeros hR a b Tp) :
    riemannZeta₁ s ≠ 0 := by
  intro hz
  exact hsZ (zeta1_zero_of_mem_closedContourRect h hR ha0 ha12 h1b hTp hrect hgood hs hz)

/-- `x^s/(s(s−1))` is analytic at `s` (for `0 < x`, `s ≠ 0, 1`). -/
lemma cpow_div_mul_sub_one_analyticAt {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z / (z * (z - 1))) s := by
  have hpow := (Commons.NumberTheory.Zeta.cpow_differentiable hx).analyticAt s
  have hS : AnalyticAt ℂ (fun z : ℂ => z * (z - 1)) s :=
    analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
  have hS0 : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  exact AnalyticAt.div hpow hS hS0



/-- the polar term `(x:ℂ)/(z−1)` is analytic away from `z = 1`. -/
lemma polar_one_analyticAt {x : ℝ} {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => (x : ℂ) / (z - 1)) s := by
  have hden : AnalyticAt ℂ (fun z : ℂ => z - 1) s :=
    AnalyticAt.sub analyticAt_id analyticAt_const
  exact AnalyticAt.div analyticAt_const hden (sub_ne_zero.mpr hs1)

/-- each pole term `rectCoeff x ρ/(z−ρ)` (ρ ∈ Z) is analytic away from `z = ρ`. -/
lemma pole_at_zero_analyticAt {x : ℝ} {R : ℝ} (hR : 0 ≤ R) {a b Tp : ℝ} {ρ s : ℂ}
    (hρ : ρ ∈ zRectZeros hR a b Tp) (hsne : s ≠ ρ) :
    AnalyticAt ℂ (fun z : ℂ => rectCoeff x ρ / (z - ρ)) s := by
  have hden : AnalyticAt ℂ (fun z : ℂ => z - ρ) s := by
    exact AnalyticAt.sub analyticAt_id (analyticAt_const (v := ρ))
  exact AnalyticAt.div analyticAt_const hden (sub_ne_zero.mpr hsne)

/-- the naive difference `psiIntF1 − x/(·−1) − Σ_{ρ∈Z} coeff(ρ)/(·−ρ)` is analytic at a
point of the closed rectangle that is not a pole. -/
lemma diff_analyticAt {x : ℝ} (hx : 0 < x) {R : ℝ} (hR : 0 ≤ R) {a b Tp : ℝ} {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hζ : riemannZeta₁ s ≠ 0)
    (hsZ : s ∉ zRectZeros hR a b Tp) :
    AnalyticAt ℂ (fun z : ℂ => psiIntF1 x z - (x : ℂ) / (z - 1) -
        ∑ ρ ∈ zRectZeros hR a b Tp, rectCoeff x ρ / (z - ρ)) s := by
  have hlog : AnalyticAt ℂ (fun z : ℂ => logDeriv riemannZeta₁ z) s := logDeriv_zeta1_analyticAt hζ
  have hdiv1 : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z / z) s := cpow_div_self_analyticAt' hx hs0
  have hterm1 : AnalyticAt ℂ (fun z : ℂ => - logDeriv riemannZeta₁ z * ((x : ℂ) ^ z / z)) s :=
    AnalyticAt.mul (AnalyticAt.neg hlog) hdiv1
  have hterm2 : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z / (z * (z - 1))) s :=
    cpow_div_mul_sub_one_analyticAt hx hs0 hs1
  have hpsi : AnalyticAt ℂ (fun z : ℂ => psiIntF1 x z) s := by
    dsimp [psiIntF1]
    exact AnalyticAt.add hterm1 hterm2
  have hpolar : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) / (z - 1)) s := polar_one_analyticAt hs1
  have hsum : AnalyticAt ℂ (fun z : ℂ =>
      ∑ ρ ∈ zRectZeros hR a b Tp, rectCoeff x ρ / (z - ρ)) s := by
    apply analyticAt_sum
    intro ρ hρ
    exact pole_at_zero_analyticAt (x := x) hR hρ (by
      intro hsρ
      exact hsZ (by simpa [hsρ] using hρ))
  exact AnalyticAt.sub (AnalyticAt.sub hpsi hpolar) hsum

/-- `G` is analytic at points of the closed rectangle that are not poles. -/
lemma psiRemainderG_analyticAt_of_not_mem (h : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    {R : ℝ} (hR : 0 ≤ R) {a b Tp : ℝ} (ha0 : 0 < a) (ha12 : a < (1 / 2 : ℝ))
    (h1b : 1 < b) (hTp : 0 < Tp)
    (hrect : closedContourRect a b Tp ⊆ Metric.closedBall (0 : ℂ) R)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp)
    {s : ℂ} (hs : s ∈ closedContourRect a b Tp) (hs1 : s ≠ 1)
    (hsZ : s ∉ zRectZeros hR a b Tp) :
    AnalyticAt ℂ (psiRemainderG x hx hR a b Tp ha0) s := by
  have hζ : riemannZeta₁ s ≠ 0 := closedRect_zeta1_ne_zero_of_not_mem_Z h hR ha0 ha12 h1b hTp hrect hgood hs hsZ
  have hs0 : s ≠ 0 := by
    have hab : a ≤ b := by linarith
    have hT : -Tp ≤ Tp := by linarith
    have hmem := (mem_closedContourRect hab hT s).mp hs
    intro h0
    have hsrea : 0 < s.re := lt_of_lt_of_le ha0 hmem.1
    rw [h0] at hsrea
    norm_num at hsrea
  have hD := diff_analyticAt (x := x) (hx := hx) (hR := hR) hs0 hs1 hζ hsZ
  have hEv1 : ∀ᶠ z in 𝓝 s, z ≠ 1 := by
    exact Filter.eventually_of_mem (isOpen_ne.mem_nhds hs1) (fun z hz => hz)
  have hEvZ : ∀ᶠ z in 𝓝 s, z ∉ zRectZeros hR a b Tp := eventually_not_mem_finset hsZ
  have hEv : psiRemainderG x hx hR a b Tp ha0 =ᶠ[𝓝 s]
      (fun z : ℂ => psiIntF1 x z - (x : ℂ) / (z - 1) -
        ∑ ρ ∈ zRectZeros hR a b Tp, rectCoeff x ρ / (z - ρ)) := by
    filter_upwards [hEv1, hEvZ] with z hz1 hzZ
    exact psiRemainderG_eq_diff (x := x) (hx := hx) (hR := hR) (ha0 := ha0) hz1 hzZ
  exact AnalyticAt.congr hD hEv.symm


/-- splitting a full sum over `Z` at the member `ρ` (for `z ≠ ρ` the denominators are
genuine on both sides). -/
lemma sum_Z_eq_self_add_erase {x : ℝ} {R : ℝ} (hR : 0 ≤ R) {a b Tp : ℝ} {ρ z : ℂ}
    (hρ : ρ ∈ zRectZeros hR a b Tp) (hzρ : z ≠ ρ) :
    (∑ u ∈ zRectZeros hR a b Tp, rectCoeff x u / (z - u)) =
      rectCoeff x ρ / (z - ρ) +
        (∑ u ∈ (zRectZeros hR a b Tp).erase ρ, rectCoeff x u / (z - u)) := by
  have hZeq : insert ρ ((zRectZeros hR a b Tp).erase ρ) = zRectZeros hR a b Tp := by
    exact Finset.insert_erase hρ
  calc
    (∑ u ∈ zRectZeros hR a b Tp, rectCoeff x u / (z - u))
        = rectCoeff x ρ / (z - ρ) + (∑ u ∈ (zRectZeros hR a b Tp).erase ρ, rectCoeff x u / (z - u)) := by
          conv_lhs => rw [← hZeq]
          rw [Finset.sum_insert (by simp : ρ ∉ (zRectZeros hR a b Tp).erase ρ)]

/-- the sum over `Z` at the point `z = ρ` equals the sum over the erased set (the
self-term is `0`). -/
lemma sum_Z_eq_erase_at_self {x : ℝ} {R : ℝ} (hR : 0 ≤ R) {a b Tp : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zRectZeros hR a b Tp) :
    (∑ u ∈ zRectZeros hR a b Tp, rectCoeff x u / (ρ - u)) =
      (∑ u ∈ (zRectZeros hR a b Tp).erase ρ, rectCoeff x u / (ρ - u)) := by
  have hZeq : insert ρ ((zRectZeros hR a b Tp).erase ρ) = zRectZeros hR a b Tp := by
    exact Finset.insert_erase hρ
  calc
    (∑ u ∈ zRectZeros hR a b Tp, rectCoeff x u / (ρ - u))
        = (∑ u ∈ (zRectZeros hR a b Tp).erase ρ, rectCoeff x u / (ρ - u)) := by
          conv_lhs => rw [← hZeq]
          rw [Finset.sum_insert (by simp : ρ ∉ (zRectZeros hR a b Tp).erase ρ)]
          simp

/-- **`G` is analytic at the pole `s = 1`.** -/
lemma psiRemainderG_analyticAt_one {x : ℝ} (hx : 0 < x) {R : ℝ} (hR : 0 ≤ R)
    {a b Tp : ℝ} (ha0 : 0 < a) :
    AnalyticAt ℂ (psiRemainderG x hx hR a b Tp ha0) (1 : ℂ) := by
  let B1 : ℂ → ℂ := fun z => psiOneRemoval x hx z -
      (∑ ρ ∈ zRectZeros hR a b Tp, rectCoeff x ρ / (z - ρ))
  have hB1 : AnalyticAt ℂ B1 (1 : ℂ) := by
    dsimp [B1]
    have h1 : AnalyticAt ℂ (psiOneRemoval x hx) (1 : ℂ) := psiOneRemoval_analyticAt hx
    have hsum : AnalyticAt ℂ (fun z : ℂ =>
        ∑ ρ ∈ zRectZeros hR a b Tp, rectCoeff x ρ / (z - ρ)) (1 : ℂ) := by
      apply analyticAt_sum
      intro ρ hρ
      exact pole_at_zero_analyticAt (x := x) hR hρ (one_ne_of_mem_zRectZeros hR hρ)
    exact AnalyticAt.sub h1 hsum
  have hEvZ : ∀ᶠ z in 𝓝 (1 : ℂ), z ∉ zRectZeros hR a b Tp :=
    eventually_not_mem_finset (one_not_mem_zRectZeros hR a b Tp)
  have hE1 := psiOneRemoval_eventually hx
  have hE1' : ∀ᶠ z in 𝓝 (1 : ℂ), z ≠ 1 → psiOneRemoval x hx z =
      psiIntF1 x z - (x : ℂ) / (z - 1) := by
    rwa [eventually_nhdsWithin_iff] at hE1
  have hEv : psiRemainderG x hx hR a b Tp ha0 =ᶠ[𝓝 (1 : ℂ)] B1 := by
    filter_upwards [hEvZ, hE1'] with z hzZ hzeq
    by_cases hz1 : z = 1
    · subst z
      dsimp [B1, psiRemainderG]
      simp
    · have hz1' : z ≠ 1 := hz1
      have hGz : psiRemainderG x hx hR a b Tp ha0 z =
          psiIntF1 x z - (x : ℂ) / (z - 1) -
            (∑ ρ ∈ zRectZeros hR a b Tp, rectCoeff x ρ / (z - ρ)) := by
        exact psiRemainderG_eq_diff (x := x) (hx := hx) (hR := hR) (ha0 := ha0) hz1' hzZ
      have hOz := hzeq hz1'
      dsimp [B1]
      rw [hGz, hOz]
  exact AnalyticAt.congr hB1 hEv.symm

/-- **`G` is analytic at each zero `ρ ∈ Z`.** -/
lemma psiRemainderG_analyticAt_of_mem_Z {x : ℝ} (hx : 0 < x) {R : ℝ} (hR : 0 ≤ R)
    {a b Tp : ℝ} (ha0 : 0 < a) {ρ : ℂ} (hρ : ρ ∈ zRectZeros hR a b Tp) :
    AnalyticAt ℂ (psiRemainderG x hx hR a b Tp ha0) ρ := by
  have hρ0 : ρ ≠ 0 := zRectZeros_ne_zero hR ha0 hρ
  have hρ1 : ρ ≠ 1 := zRectZeros_ne_one hR hρ
  let Bρ : ℂ → ℂ := fun z =>
    psiZeroRemoval x hx ρ (zRectZeros_zero hR a b Tp hρ) hρ0 hρ1 z
      - (x : ℂ) / (z - 1)
      - (∑ u ∈ (zRectZeros hR a b Tp).erase ρ, rectCoeff x u / (z - u))
  have hBρ : AnalyticAt ℂ Bρ ρ := by
    dsimp [Bρ]
    have hrem : AnalyticAt ℂ
        (psiZeroRemoval x hx ρ (zRectZeros_zero hR a b Tp hρ) hρ0 hρ1) ρ :=
      psiZeroRemoval_analyticAt hx ρ (zRectZeros_zero hR a b Tp hρ) hρ0 hρ1
    have hpolar : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) / (z - 1)) ρ := polar_one_analyticAt hρ1
    have hsum : AnalyticAt ℂ (fun z : ℂ =>
        ∑ u ∈ (zRectZeros hR a b Tp).erase ρ, rectCoeff x u / (z - u)) ρ := by
      apply analyticAt_sum
      intro u hu
      have hu' := mem_erase_zRectZeros hR hρ hu
      exact pole_at_zero_analyticAt (x := x) hR hu'.1 (fun h => hu'.2 h.symm)
    exact AnalyticAt.sub (AnalyticAt.sub hrem hpolar) hsum
  have hErem := psiZeroRemoval_eventually hx ρ (zRectZeros_zero hR a b Tp hρ) hρ0 hρ1
  have hErem' : ∀ᶠ z in 𝓝 ρ, z ≠ ρ → psiZeroRemoval x hx ρ (zRectZeros_zero hR a b Tp hρ) hρ0 hρ1 z =
      psiIntF1 x z + (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ * (z - ρ)⁻¹ := by
    rwa [eventually_nhdsWithin_iff] at hErem
  have hEvZ : ∀ᶠ z in 𝓝 ρ, z ∉ (zRectZeros hR a b Tp).erase ρ :=
    eventually_not_mem_finset (by simp : ρ ∉ (zRectZeros hR a b Tp).erase ρ)
  have hEv1 : ∀ᶠ z in 𝓝 ρ, z ≠ 1 := by
    exact Filter.eventually_of_mem (isOpen_ne.mem_nhds hρ1) (fun z hz => hz)
  have hEv : psiRemainderG x hx hR a b Tp ha0 =ᶠ[𝓝 ρ] Bρ := by
    filter_upwards [hEvZ, hEv1, hErem'] with z hzE hz1 hzrem
    by_cases hzρ : z = ρ
    · subst z
      dsimp [Bρ, psiRemainderG]
      simp [hρ1, hρ]
    · have hzρ' : z ≠ ρ := hzρ
      have hzZ : z ∉ zRectZeros hR a b Tp := by
        intro hzZm
        exact hzE (Finset.mem_erase.mpr ⟨hzρ', hzZm⟩)
      have hGz : psiRemainderG x hx hR a b Tp ha0 z =
          psiIntF1 x z - (x : ℂ) / (z - 1) -
            (∑ u ∈ zRectZeros hR a b Tp, rectCoeff x u / (z - u)) := by
        exact psiRemainderG_eq_diff (x := x) (hx := hx) (hR := hR) (ha0 := ha0) hz1 hzZ
      have hOz := hzrem hzρ'
      have hc : (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ = - rectCoeff x ρ := by
        rw [rectCoeff_of_ne_one hρ1]
        ring
      dsimp [Bρ]
      rw [hGz]
      rw [sum_Z_eq_self_add_erase (x := x) hR hρ hzρ']
      rw [hOz]
      rw [hc]
      ring_nf
  exact AnalyticAt.congr hBρ hEv.symm


/-- **`G` is differentiable on the closed contour rectangle.** -/
theorem psiRemainderG_differentiableOn (h : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    {R : ℝ} (hR : 0 ≤ R) {a b Tp : ℝ} (ha0 : 0 < a) (ha12 : a < (1 / 2 : ℝ))
    (h1b : 1 < b) (hTp : 0 < Tp)
    (hrect : closedContourRect a b Tp ⊆ Metric.closedBall (0 : ℂ) R)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp) :
    DifferentiableOn ℂ (psiRemainderG x hx hR a b Tp ha0) (closedContourRect a b Tp) := by
  intro s hs
  by_cases hs1 : s = 1
  · subst s
    exact (psiRemainderG_analyticAt_one hx hR ha0).differentiableAt.differentiableWithinAt
  · by_cases hsZ : s ∈ zRectZeros hR a b Tp
    · exact ((psiRemainderG_analyticAt_of_mem_Z hx hR ha0 hsZ).differentiableAt.differentiableWithinAt)
    · exact ((psiRemainderG_analyticAt_of_not_mem h hx hR ha0 ha12 h1b hTp hrect hgood hs hs1 hsZ).differentiableAt.differentiableWithinAt)

/-- a point on the boundary of the closed contour rectangle is not a pole of the model
(nor a zero of `ζ₁`); the parametrised boundary points are covered by `hre`. -/
lemma boundary_point_eq (h : RiemannHypothesis) {x : ℝ} (hx : 0 < x) {R : ℝ} (hR : 0 ≤ R)
    {a b Tp : ℝ} (ha0 : 0 < a) (ha12 : a < (1 / 2 : ℝ)) (h1b : 1 < b) (hTp : 0 < Tp)
    (hrect : closedContourRect a b Tp ⊆ Metric.closedBall (0 : ℂ) R)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp)
    {t : ℂ} (ht : t ∈ closedContourRect a b Tp)
    (hre : t.re = a ∨ t.re = b ∨ t.im = -Tp ∨ t.im = Tp) :
    psiIntF1 x t = rectModel x hR a b Tp (psiRemainderG x hx hR a b Tp ha0) t := by
  have ht1 : t ≠ 1 := by
    intro htc
    have hre1 : t.re = 1 := congrArg Complex.re htc
    have him1 : t.im = 0 := by rw [htc]; simp
    rcases hre with hra | hrb | himn | himp
    · rw [hra] at hre1
      norm_num at hre1
      linarith [ha12]
    · rw [hrb] at hre1
      linarith
    · rw [himn] at him1
      linarith
    · rw [himp] at him1
      linarith
  have hzζ : riemannZeta₁ t ≠ 0 := by
    intro hz0
    have hvf := zeta1_zero_free_vertical_sides h ha0 ha12 (le_of_lt h1b)
    rcases hre with hra | hrb | himn | himp
    · have hseq : t = (a : ℂ) + Complex.I * (t.im : ℂ) := by
        apply Complex.ext <;> simp [hra]
      rw [hseq] at hz0
      exact (hvf.2 t.im) hz0
    · have hseq : t = (b : ℂ) + Complex.I * (t.im : ℂ) := by
        apply Complex.ext <;> simp [hrb]
      rw [hseq] at hz0
      exact (hvf.1 t.im) hz0
    · exact (hgood t hz0).2 himn
    · exact (hgood t hz0).1 himp
  have htZ : t ∉ zRectZeros hR a b Tp := by
    intro htz
    exact hzζ (zRectZeros_zero hR a b Tp htz)
  exact psiIntF1_eq_rectModel_add_remainder hx hR ha0 ht1 htZ


/-- membership of a parametrised boundary point `(x : ℂ) + im·I` with `im = ±Tp` in the
closed contour rectangle. -/
lemma edge_h_mem {a b Tp x : ℝ} (hab : a ≤ b) (hT : -Tp ≤ Tp) (hx : x ∈ Set.uIcc a b) :
    ((x : ℂ) + (-Tp : ℂ) * Complex.I) ∈ closedContourRect a b Tp := by
  rw [mem_closedContourRect hab hT ((x : ℂ) + (-Tp : ℂ) * Complex.I)]
  have hx' : a ≤ x ∧ x ≤ b := by
    rw [Set.uIcc_of_le hab] at hx
    exact hx
  have hre : (((x : ℂ) + (-Tp : ℂ) * Complex.I).re) = x := by simp
  have him : (((x : ℂ) + (-Tp : ℂ) * Complex.I).im) = -Tp := by simp
  rw [hre, him]
  exact ⟨hx'.1, ⟨hx'.2, ⟨le_rfl, by linarith⟩⟩⟩

/-- **CONTOUR IDENTITY (P4)**: with corners `z = a − iTp`, `w = b + iTp` (`0<a<1/2<1<b`,
`Tp>0`, closed rectangle inside a ball, `hgood`: horizontal sides carry no zeros), under
RH, the boundary rectangle integral of `psiIntF1` equals `2πi·(x − Σ_{ρ∈Z} m_ρ·x^ρ/ρ)`. -/
theorem rectInt_psiIntF1_engineSum (h : RiemannHypothesis) {R a b Tp x : ℝ}
    (hR : 0 ≤ R) (hx : 0 < x) (ha0 : 0 < a) (ha12 : a < (1 / 2 : ℝ)) (h1b : 1 < b)
    (hTp : 0 < Tp)
    (hrect : closedContourRect a b Tp ⊆ Metric.closedBall (0 : ℂ) R)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp) :
    rectInt (zRect a Tp) (wRect b Tp) (psiIntF1 x) =
      ((x : ℂ) - ∑ ρ ∈ zRectZeros hR a b Tp,
          (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ) *
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  have hGdiff : DifferentiableOn ℂ (psiRemainderG x hx hR a b Tp ha0)
      (closedContourRect a b Tp) :=
    psiRemainderG_differentiableOn h hx hR ha0 ha12 h1b hTp hrect hgood
  have hab : a ≤ b := by linarith
  have hablt : a < b := by linarith
  have hT : -Tp ≤ Tp := by linarith
  let G : ℂ → ℂ := psiRemainderG x hx hR a b Tp ha0
  have h1 : ∀ x0 ∈ Set.uIcc (zRect a Tp).re (wRect b Tp).re,
      psiIntF1 x (x0 + (zRect a Tp).im * Complex.I) =
        rectModel x hR a b Tp G (x0 + (zRect a Tp).im * Complex.I) := by
    intro x0 hx0
    have hx0' : x0 ∈ Set.uIcc a b := by simpa [zRect_re, wRect_re] using hx0
    apply boundary_point_eq h hx hR ha0 ha12 h1b hTp hrect hgood
      (t := (x0 : ℂ) + (zRect a Tp).im * Complex.I)
    · rw [mem_closedContourRect hab hT ((x0 : ℂ) + (zRect a Tp).im * Complex.I)]
      have hx0i : a ≤ x0 ∧ x0 ≤ b := by
        rw [Set.uIcc_of_le hab] at hx0'
        exact hx0'
      have hre : (((x0 : ℂ) + (zRect a Tp).im * Complex.I).re) = x0 := by simp
      have him : (((x0 : ℂ) + (zRect a Tp).im * Complex.I).im) = -Tp := by simp [zRect_im]
      rw [hre, him]
      exact ⟨hx0i.1, ⟨hx0i.2, ⟨le_rfl, by linarith⟩⟩⟩
    · have him : (((x0 : ℂ) + (zRect a Tp).im * Complex.I).im) = -Tp := by
        simp [zRect_im]
      exact Or.inr (Or.inr (Or.inl him))
  have h2 : ∀ x0 ∈ Set.uIcc (zRect a Tp).re (wRect b Tp).re,
      psiIntF1 x (x0 + (wRect b Tp).im * Complex.I) =
        rectModel x hR a b Tp G (x0 + (wRect b Tp).im * Complex.I) := by
    intro x0 hx0
    have hx0' : x0 ∈ Set.uIcc a b := by simpa [zRect_re, wRect_re] using hx0
    apply boundary_point_eq h hx hR ha0 ha12 h1b hTp hrect hgood
      (t := (x0 : ℂ) + (wRect b Tp).im * Complex.I)
    · rw [wRect_im]
      rw [mem_closedContourRect hab hT ((x0 : ℂ) + (Tp : ℂ) * Complex.I)]
      have hx0i : a ≤ x0 ∧ x0 ≤ b := by
        rw [Set.uIcc_of_le hab] at hx0'
        exact hx0'
      have hre : (((x0 : ℂ) + (Tp : ℂ) * Complex.I).re) = x0 := by simp
      have him : (((x0 : ℂ) + (Tp : ℂ) * Complex.I).im) = Tp := by simp
      rw [hre, him]
      exact ⟨hx0i.1, ⟨hx0i.2, ⟨by linarith, le_rfl⟩⟩⟩
    · have him : (((x0 : ℂ) + (wRect b Tp).im * Complex.I).im) = Tp := by
        simp [wRect_im]
      exact Or.inr (Or.inr (Or.inr him))
  have h3 : ∀ y ∈ Set.uIcc (zRect a Tp).im (wRect b Tp).im,
      psiIntF1 x ((wRect b Tp).re + y * Complex.I) =
        rectModel x hR a b Tp G ((wRect b Tp).re + y * Complex.I) := by
    intro y hy
    have hy' : y ∈ Set.uIcc (-Tp) Tp := by simpa [zRect_im, wRect_im] using hy
    apply boundary_point_eq h hx hR ha0 ha12 h1b hTp hrect hgood
      (t := (wRect b Tp).re + y * Complex.I)
    · rw [wRect_re]
      rw [mem_closedContourRect hab hT ((b : ℂ) + y * Complex.I)]
      have hyi : -Tp ≤ y ∧ y ≤ Tp := by
        rw [Set.uIcc_of_le hT] at hy'
        exact hy'
      have hre : (((b : ℂ) + y * Complex.I).re) = b := by simp
      have him : (((b : ℂ) + y * Complex.I).im) = y := by simp
      rw [hre, him]
      exact ⟨hab, ⟨le_rfl, ⟨hyi.1, hyi.2⟩⟩⟩
    · have hre : (((wRect b Tp).re + y * Complex.I).re) = b := by
        simp [wRect_re]
      exact Or.inr (Or.inl hre)
  have h4 : ∀ y ∈ Set.uIcc (zRect a Tp).im (wRect b Tp).im,
      psiIntF1 x ((zRect a Tp).re + y * Complex.I) =
        rectModel x hR a b Tp G ((zRect a Tp).re + y * Complex.I) := by
    intro y hy
    have hy' : y ∈ Set.uIcc (-Tp) Tp := by simpa [zRect_im, wRect_im] using hy
    apply boundary_point_eq h hx hR ha0 ha12 h1b hTp hrect hgood
      (t := (zRect a Tp).re + y * Complex.I)
    · rw [zRect_re]
      rw [mem_closedContourRect hab hT ((a : ℂ) + y * Complex.I)]
      have hyi : -Tp ≤ y ∧ y ≤ Tp := by
        rw [Set.uIcc_of_le hT] at hy'
        exact hy'
      have hre : (((a : ℂ) + y * Complex.I).re) = a := by simp
      have him : (((a : ℂ) + y * Complex.I).im) = y := by simp
      rw [hre, him]
      exact ⟨le_rfl, ⟨hab, ⟨hyi.1, hyi.2⟩⟩⟩
    · have hre : (((zRect a Tp).re + y * Complex.I).re) = a := by
        simp [zRect_re]
      exact Or.inl hre
  have hcong := rectInt_congr_boundary (z := zRect a Tp) (w := wRect b Tp)
    (f := psiIntF1 x) (g := rectModel x hR a b Tp G) h1 h2 h3 h4
  have hEng := rectInt_engineSum_zeroRect (x := x) (R := R) (hR := hR) (a := a) (b := b)
    (Tp := Tp) (G := G) hablt hTp (by linarith : a < 1) h1b hGdiff
  rw [hcong]
  exact hEng


end Commons.NumberTheory.Zeta
end


-- ==== begin p2_perronLink ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# T-R3.1 (P4′): from the contour identity to the truncated explicit formula

`rectInt_psiIntF1_engineSum` (p2_remainder) gives the rectangle identity for `psiIntF1`
(the ζ₁-form of the Perron integrand).  On the right edge (`Re = b > 1`) `psiIntF1`
coincides with the classical ζ-form `psiIntF = −(ζ′/ζ)·x^s/s`, i.e. with the
von-Mangoldt `LSeries` integrand of `chebyshevPsi_truncatedPerron`; so the right-edge
integral is `2π` times the truncated-Perron integral.  Writing the rectangle integral as
bottom − top + `I`·right − `I`·left and solving for the Perron integral, the contour
identity yields the truncated explicit formula

    ψ(x) = x − Σ_{ρ∈Z} m_ρ·x^ρ/ρ  +  O(x·log²x/T′) + (left/bottom/top side error)

where the side error is expressed through the norms of the three side integrals `B,T,L`
(bounded in the P5 module).  This module fixes the algebra; `Z = zRectZeros`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- bottom-edge integral `∫_a^b f (x − i·Tp) dx`. -/
def edgeB (a b Tp : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ (x : ℝ) in a..b, f ((x : ℂ) + (zRect a Tp).im * Complex.I))

/-- top-edge integral `∫_a^b f (x + i·Tp) dx`. -/
def edgeT (a b Tp : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ (x : ℝ) in a..b, f ((x : ℂ) + (wRect b Tp).im * Complex.I))

/-- right-edge integral `∫_{−Tp}^{Tp} f (b + i·y) dy`. -/
def edgeR (b Tp : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ (y : ℝ) in -Tp..Tp, f ((wRect b Tp).re + y * Complex.I))

/-- left-edge integral `∫_{−Tp}^{Tp} f (a + i·y) dy`. -/
def edgeL (a Tp : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ (y : ℝ) in -Tp..Tp, f ((zRect a Tp).re + y * Complex.I))

/-- the rectangle boundary integral decomposes into the four oriented edges. -/
lemma rectInt_decompose (a b Tp : ℝ) (f : ℂ → ℂ) :
    rectInt (zRect a Tp) (wRect b Tp) f =
      edgeB a b Tp f - edgeT a b Tp f +
        Complex.I • edgeR b Tp f - Complex.I • edgeL a Tp f := by
  unfold rectInt edgeB edgeT edgeR edgeL
  rw [zRect_re, wRect_re, zRect_im, wRect_im]

/-- on the right edge (`Re = b ≥ 1`, off `1` and zeros), the ζ₁-form integrand equals the
ζ-form one. -/
lemma psiIntF1_eq_psiIntF_on_re_ge_one {x : ℝ} {s : ℂ} (h1 : 1 ≤ s.re) (hs1 : s ≠ 1) :
    psiIntF1 x s = psiIntF x s := by
  have hz1 : riemannZeta₁ s ≠ 0 := zeta1_ne_zero_of_one_le_re h1
  have hs0 : s ≠ 0 := by
    intro hs0
    have hs0re : s.re = 0 := congrArg Complex.re hs0
    rw [hs0re] at h1
    norm_num at h1
  have hζ : riemannZeta s ≠ 0 := by
    rw [riemannZeta_eq_inv_sub_mul hs1]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs1)) hz1
  have hid : -(deriv riemannZeta s / riemannZeta s) =
      -logDeriv riemannZeta₁ s + (s - 1)⁻¹ := by
    have h := deriv_zeta_div_zeta_eq s hs1 hz1
    dsimp [logDeriv] at h ⊢
    rw [h]
    ring
  calc
    psiIntF1 x s = -logDeriv riemannZeta₁ s * ((x : ℂ) ^ s / s) + (x : ℂ) ^ s / (s * (s - 1)) := rfl
    _ = (-logDeriv riemannZeta₁ s + (s - 1)⁻¹) * ((x : ℂ) ^ s / s) := by
          field_simp [hs0, sub_ne_zero.mpr hs1]
    _ = -(deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s) := by rw [← hid]
    _ = psiIntF x s := by
          dsimp [psiIntF]
          ring

/-- the right-edge integral of `psiIntF1` equals the raw truncated-Perron integrand
integral (the `LSeries`-vonMangoldt form at `Re = b > 1`, height `Tp`). -/
lemma edgeR_eq_perron_raw (x : ℝ) (b Tp : ℝ) (h1b : 1 < b) :
    edgeR b Tp (psiIntF1 x) =
      (∫ (t : ℝ) in -Tp..Tp,
        (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            (((b : ℝ) : ℂ) + Complex.I * (t : ℂ))) *
          (x : ℂ) ^ (((b : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
          (((b : ℝ) : ℂ) + Complex.I * (t : ℂ))) := by
  unfold edgeR
  rw [wRect_re]
  have hcong : (∫ (y : ℝ) in -Tp..Tp, psiIntF1 x ((b : ℂ) + y * Complex.I)) =
      (∫ (y : ℝ) in -Tp..Tp,
        (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            ((b : ℂ) + Complex.I * (y : ℂ))) *
          (x : ℂ) ^ ((b : ℂ) + Complex.I * (y : ℂ)) /
          ((b : ℂ) + Complex.I * (y : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hs : (b : ℂ) + (t : ℂ) * Complex.I = (b : ℂ) + Complex.I * (t : ℂ) := by ring
    change psiIntF1 x ((b : ℂ) + (t : ℂ) * Complex.I) =
        (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            ((b : ℂ) + Complex.I * (t : ℂ))) *
          (x : ℂ) ^ ((b : ℂ) + Complex.I * (t : ℂ)) /
          ((b : ℂ) + Complex.I * (t : ℂ))
    rw [hs]
    have h1s : (1 : ℝ) < ((b : ℂ) + Complex.I * (t : ℂ)).re := by
      simp
      exact h1b
    have hs1 : (b : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
      intro hs
      have hb1 : (1 : ℝ) = b := by
        have hre := congrArg Complex.re hs
        simp at hre
        exact hre.symm
      linarith
    -- psiIntF1 = psiIntF = −ζ′/ζ·x^s/s = LSeries Λ · x^s/s   (1 < Re)
    have hz1 : riemannZeta₁ ((b : ℂ) + Complex.I * (t : ℂ)) ≠ 0 :=
      zeta1_ne_zero_of_one_le_re (le_of_lt h1s)
    have hp1 : psiIntF1 x ((b : ℂ) + Complex.I * (t : ℂ)) =
        psiIntF x ((b : ℂ) + Complex.I * (t : ℂ)) :=
      psiIntF1_eq_psiIntF_on_re_ge_one (x := x) (s := (b : ℂ) + Complex.I * (t : ℂ))
        (le_of_lt h1s) hs1
    have hL : LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          ((b : ℂ) + Complex.I * (t : ℂ)) =
        -deriv riemannZeta ((b : ℂ) + Complex.I * (t : ℂ)) /
          riemannZeta ((b : ℂ) + Complex.I * (t : ℂ)) := by
      simpa using (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (b : ℂ) + Complex.I * (t : ℂ)) h1s)
    calc
      psiIntF1 x ((b : ℂ) + Complex.I * (t : ℂ))
          = psiIntF x ((b : ℂ) + Complex.I * (t : ℂ)) := hp1
      _ = (-(deriv riemannZeta ((b : ℂ) + Complex.I * (t : ℂ))) /
            riemannZeta ((b : ℂ) + Complex.I * (t : ℂ))) *
            (x : ℂ) ^ ((b : ℂ) + Complex.I * (t : ℂ)) /
            ((b : ℂ) + Complex.I * (t : ℂ)) := by
            dsimp [psiIntF]
      _ = (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            ((b : ℂ) + Complex.I * (t : ℂ))) *
            (x : ℂ) ^ ((b : ℂ) + Complex.I * (t : ℂ)) /
            ((b : ℂ) + Complex.I * (t : ℂ)) := by rw [← hL]
  exact hcong


/-- **Truncated explicit formula (algebra part)**: the Perron integral (right edge divided
by `2π`) differs from `x − Σ_{ρ∈Z} m_ρ x^ρ/ρ` by the (norm-bounded) three side integrals. -/
theorem perron_raw_sub_zero_sum_bound (h : RiemannHypothesis) {R a b Tp x : ℝ}
    (hR : 0 ≤ R) (hx : 0 < x) (ha0 : 0 < a) (ha12 : a < (1 / 2 : ℝ)) (h1b : 1 < b)
    (hTp : 0 < Tp)
    (hrect : closedContourRect a b Tp ⊆ Metric.closedBall (0 : ℂ) R)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp) :
    ‖edgeR b Tp (psiIntF1 x) * ((2 : ℂ) * (Real.pi : ℂ))⁻¹ -
        ((x : ℂ) - ∑ ρ ∈ zRectZeros hR a b Tp, (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ)‖ ≤
      (‖edgeB a b Tp (psiIntF1 x)‖ + ‖edgeT a b Tp (psiIntF1 x)‖ +
        ‖edgeL a Tp (psiIntF1 x)‖) * ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ := by
  have h4 := rectInt_psiIntF1_engineSum h hR hx ha0 ha12 h1b hTp hrect hgood
  have hdec := rectInt_decompose a b Tp (psiIntF1 x)
  rw [hdec] at h4
  let K : ℂ := (2 : ℂ) * (Real.pi : ℂ) * Complex.I
  let c : ℂ := (x : ℂ) -
      ∑ ρ ∈ zRectZeros hR a b Tp, (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  let Bv : ℂ := edgeB a b Tp (psiIntF1 x)
  let Tv : ℂ := edgeT a b Tp (psiIntF1 x)
  let Rv : ℂ := edgeR b Tp (psiIntF1 x)
  let Lv : ℂ := edgeL a Tp (psiIntF1 x)
  have h4' : Bv - Tv + Complex.I • Rv - Complex.I • Lv = c * K := by
    simpa [K, c, Bv, Tv, Rv, Lv] using h4
  have hRI : Complex.I • Rv = K * c - Bv + Tv + Complex.I • Lv := by
    calc
      Complex.I • Rv = (Bv - Tv + Complex.I • Rv - Complex.I • Lv) - (Bv - Tv - Complex.I • Lv) := by ring
      _ = K * c - Bv + Tv + Complex.I • Lv := by rw [h4']; ring
  have hRI'' : Rv * Complex.I = K * c - Bv + Tv + Complex.I • Lv := by
    calc
      Rv * Complex.I = Complex.I • Rv := by ring
      _ = K * c - Bv + Tv + Complex.I • Lv := hRI
  have hR : Rv = (K * c - Bv + Tv + Complex.I • Lv) / Complex.I := by
    have hI : Complex.I ≠ 0 := by simp
    calc
      Rv = (Rv * Complex.I) / Complex.I := by field_simp [hI]
      _ = (K * c - Bv + Tv + Complex.I • Lv) / Complex.I := by rw [hRI'']
  have hmain : ‖Rv * ((2 : ℂ) * (Real.pi : ℂ))⁻¹ - c‖ ≤
      (‖Bv‖ + ‖Tv‖ + ‖Lv‖) * ‖K⁻¹‖ := by
    have hI : Complex.I ≠ 0 := by simp
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    have hpi : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hK : K ≠ 0 := by
      dsimp [K]
      exact mul_ne_zero (mul_ne_zero htwo hpi) hI
    have hpi2 : ((2 : ℂ) * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero htwo hpi
    have hstep : Rv * ((2 : ℂ) * (Real.pi : ℂ))⁻¹ - c =
        (- Bv + Tv + Complex.I • Lv) * K⁻¹ := by
      rw [hR]
      dsimp [K, c]
      field_simp [hI, htwo, hpi]
      ring
    rw [hstep]
    calc
      ‖(- Bv + Tv + Complex.I • Lv) * K⁻¹‖
          = ‖- Bv + Tv + Complex.I • Lv‖ * ‖K⁻¹‖ := by rw [norm_mul]
      _ ≤ (‖Bv‖ + ‖Tv‖ + ‖Lv‖) * ‖K⁻¹‖ := by
            have h1 : ‖-Bv + Tv + Complex.I • Lv‖ ≤ ‖-Bv + Tv‖ + ‖Lv‖ := by
              have h1' : ‖-Bv + Tv + Complex.I • Lv‖ ≤ ‖-Bv + Tv‖ + ‖Complex.I • Lv‖ :=
                norm_add_le (-Bv + Tv) (Complex.I • Lv)
              have h2' : ‖Complex.I • Lv‖ = ‖Lv‖ := by simp
              linarith
            have h1a : ‖-Bv + Tv‖ ≤ ‖-Bv‖ + ‖Tv‖ := norm_add_le (-Bv) Tv
            have h1c : ‖-Bv‖ = ‖Bv‖ := by rw [norm_neg]
            have hS : ‖-Bv + Tv + Complex.I • Lv‖ ≤ ‖Bv‖ + ‖Tv‖ + ‖Lv‖ := by
              linarith
            have hm : 0 ≤ ‖K⁻¹‖ := norm_nonneg _
            nlinarith
  simpa [K, c, Bv, Tv, Rv, Lv] using hmain

/-- the norm of `(2πi)⁻¹` is `1/(2π)`. -/
lemma norm_inv_two_pi_I : ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ = 1 / (2 * Real.pi) := by
  rw [norm_inv]
  have hnorm : ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul]
    simp [Complex.norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos, two_mul]
  rw [hnorm]
  field_simp [Real.pi_ne_zero]


end Commons.NumberTheory.Zeta
end


-- ==== begin p2_symm ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# P5 support: conjugation symmetry of `ζ₁` and its log-derivative

For the side estimates of the T-R3.1 rectangle we need
`|logDeriv ζ₁ (σ + iT)| = |logDeriv ζ₁ (σ − iT)|` (the bottom- and top-edge integrands
are conjugate).  `ζ₁ s = 1 + (s−1)·ζ₀ s` with `ζ₀ s = if s = 1 then γ else ζ s − (s−1)⁻¹`
inherits the conjugation symmetry `riemannZeta_conj` of Mathlib; derivative symmetry then
follows from the `conj ∘ f ∘ conj` calculus (Analysis/Calculus/Deriv/Star.lean).
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators ComplexConjugate

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- conjugation symmetry of the entire completion `ζ₀`. -/
lemma riemannZeta₀_conj (s : ℂ) : riemannZeta₀ (conj s) = conj (riemannZeta₀ s) := by
  by_cases hs : s = 1
  · subst s
    simp [riemannZeta₀]
  · unfold riemannZeta₀
    rw [if_neg hs, if_neg (by exact (map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hs)]
    rw [riemannZeta_conj]
    simp

/-- conjugation symmetry of the entire completion `ζ₁`. -/
lemma riemannZeta₁_conj (s : ℂ) : riemannZeta₁ (conj s) = conj (riemannZeta₁ s) := by
  unfold riemannZeta₁
  simp [riemannZeta₀_conj]

/-- `ζ₁` equals `conj ∘ ζ₁ ∘ conj` (functional form of the symmetry). -/
lemma riemannZeta₁_conj_comp : riemannZeta₁ = conj ∘ riemannZeta₁ ∘ conj := by
  funext s
  calc
    riemannZeta₁ s = conj (conj (riemannZeta₁ s)) := by simp
    _ = conj (riemannZeta₁ (conj s)) := by rw [← riemannZeta₁_conj]
    _ = (conj ∘ riemannZeta₁ ∘ conj) s := by simp

/-- derivative conjugation symmetry of `ζ₁`. -/
lemma deriv_riemannZeta₁_conj (s : ℂ) : deriv riemannZeta₁ (conj s) = conj (deriv riemannZeta₁ s) := by
  have hsymm : riemannZeta₁ = conj ∘ riemannZeta₁ ∘ conj := riemannZeta₁_conj_comp
  have hd := deriv_conj_conj (f := riemannZeta₁)
  have hmain : deriv riemannZeta₁ s = conj (deriv riemannZeta₁ (conj s)) := by
    calc
      deriv riemannZeta₁ s = deriv (conj ∘ riemannZeta₁ ∘ conj) s := by rw [← hsymm]
      _ = (conj ∘ deriv riemannZeta₁ ∘ conj) s := by rw [hd]
      _ = conj (deriv riemannZeta₁ (conj s)) := by simp
  calc
    deriv riemannZeta₁ (conj s) = conj (conj (deriv riemannZeta₁ (conj s))) := by simp
    _ = conj (deriv riemannZeta₁ s) := by rw [hmain]

/-- log-derivative conjugation symmetry of `ζ₁`. -/
lemma logDeriv_riemannZeta₁_conj (s : ℂ) :
    logDeriv riemannZeta₁ (conj s) = conj (logDeriv riemannZeta₁ s) := by
  unfold logDeriv
  change deriv riemannZeta₁ (conj s) / riemannZeta₁ (conj s) =
      conj (deriv riemannZeta₁ s / riemannZeta₁ s)
  rw [deriv_riemannZeta₁_conj, riemannZeta₁_conj, map_div₀]

/-- norm symmetry of the log-derivative under conjugation. -/
lemma norm_logDeriv_riemannZeta₁_conj (s : ℂ) :
    ‖logDeriv riemannZeta₁ (conj s)‖ = ‖logDeriv riemannZeta₁ s‖ := by
  rw [logDeriv_riemannZeta₁_conj]
  simp


end Commons.NumberTheory.Zeta
end


-- ==== begin p2_sideBounds ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# P5: pointwise bounds for the ψ-integrand `psiIntF1 x s`

`psiIntF1 x s = −logDeriv ζ₁(s)·x^s/s + x^s/(s(s−1))` is the ζ₁-form of the Perron
integrand.  This module collects the pointwise estimates used to bound the three side
integrals `edgeB/edgeT/edgeL` of the T-R3.1 rectangle:

* `logDeriv_zeta1_eq` : `logDeriv ζ₁ s = ζ'/ζ(s) + (s−1)⁻¹` (off `s = 1`, `ζ₁ s ≠ 0`);
* `psiIntF1_norm_le` : `‖psiIntF1 x s‖ ≤ (‖ζ'/ζ(s)‖ + 2/‖s−1‖)·x^{Re s}/‖s‖`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators ComplexConjugate

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- `logDeriv ζ₁ s = ζ'/ζ(s) + (s−1)⁻¹` for `s ≠ 1`, `ζ₁ s ≠ 0`. -/
lemma logDeriv_zeta1_eq {s : ℂ} (hs : s ≠ 1) (hz1 : riemannZeta₁ s ≠ 0) :
    logDeriv riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ := by
  have h := deriv_zeta_div_zeta_eq s hs hz1
  have h1 : logDeriv riemannZeta₁ s = deriv riemannZeta₁ s / riemannZeta₁ s := rfl
  rw [h1]
  rw [h]
  ring

/-- Pointwise bound: `‖psiIntF1 x s‖ ≤ (‖ζ'/ζ(s)‖ + 2/‖s−1‖)·x^{Re s}/‖s‖`. -/
lemma psiIntF1_norm_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) (hz1 : riemannZeta₁ s ≠ 0) :
    ‖psiIntF1 x s‖ ≤ (‖deriv riemannZeta s / riemannZeta s‖ + 2 / ‖s - 1‖) *
      ((x : ℝ) ^ s.re / ‖s‖) := by
  have hxpos : 0 ≤ x := le_of_lt hx
  have hnorm_cpow : ‖(x : ℂ) ^ s‖ = (x : ℝ) ^ s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hx s
  have hnorm_s : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  have hnorm_s1 : (0 : ℝ) ≤ ‖s - 1‖ := norm_nonneg (s - 1)
  -- decompose psiIntF1
  have hdecomp : psiIntF1 x s =
      -(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s) + (x : ℂ) ^ s / (s * (s - 1)) := rfl
  have h1 : ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s)‖ =
      ‖logDeriv riemannZeta₁ s‖ * ((x : ℝ) ^ s.re / ‖s‖) := by
    rw [norm_mul, norm_neg, norm_div, hnorm_cpow]
  have h2 : ‖(x : ℂ) ^ s / (s * (s - 1))‖ = (x : ℝ) ^ s.re / (‖s‖ * ‖s - 1‖) := by
    rw [norm_div, norm_mul, hnorm_cpow]
  have hsplit : ‖psiIntF1 x s‖ ≤
      ‖logDeriv riemannZeta₁ s‖ * ((x : ℝ) ^ s.re / ‖s‖) + (x : ℝ) ^ s.re / (‖s‖ * ‖s - 1‖) := by
    rw [hdecomp]
    calc
      ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s) + (x : ℂ) ^ s / (s * (s - 1))‖
          ≤ ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s)‖ + ‖(x : ℂ) ^ s / (s * (s - 1))‖ :=
            norm_add_le _ _
      _ = _ := by rw [h1, h2]
  -- bound logDeriv ζ₁
  have hlD : ‖logDeriv riemannZeta₁ s‖ ≤ ‖deriv riemannZeta s / riemannZeta s‖ + 1 / ‖s - 1‖ := by
    rw [logDeriv_zeta1_eq hs hz1]
    calc
      ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖
          ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := norm_add_le _ _
      _ = ‖deriv riemannZeta s / riemannZeta s‖ + 1 / ‖s - 1‖ := by rw [norm_inv, one_div]
  -- combine
  have hxpow : (0 : ℝ) ≤ (x : ℝ) ^ s.re := Real.rpow_nonneg hxpos s.re
  have hstep1 : ‖logDeriv riemannZeta₁ s‖ * ((x : ℝ) ^ s.re / ‖s‖) ≤
      (‖deriv riemannZeta s / riemannZeta s‖ + 1 / ‖s - 1‖) * ((x : ℝ) ^ s.re / ‖s‖) :=
    mul_le_mul_of_nonneg_right hlD (div_nonneg hxpow hnorm_s)
  have hstep2 : (x : ℝ) ^ s.re / (‖s‖ * ‖s - 1‖) =
      ((x : ℝ) ^ s.re / ‖s‖) * (1 / ‖s - 1‖) := by
    field_simp
  rw [hstep2] at hsplit
  calc
    ‖psiIntF1 x s‖ ≤ ‖logDeriv riemannZeta₁ s‖ * ((x : ℝ) ^ s.re / ‖s‖) +
        ((x : ℝ) ^ s.re / ‖s‖) * (1 / ‖s - 1‖) := hsplit
    _ ≤ (‖deriv riemannZeta s / riemannZeta s‖ + 1 / ‖s - 1‖) * ((x : ℝ) ^ s.re / ‖s‖) +
        ((x : ℝ) ^ s.re / ‖s‖) * (1 / ‖s - 1‖) := by
        exact add_le_add hstep1 le_rfl
    _ = (‖deriv riemannZeta s / riemannZeta s‖ + 2 / ‖s - 1‖) * ((x : ℝ) ^ s.re / ‖s‖) := by
        ring


/-- Pointwise bound in terms of `logDeriv ζ₁` (no hypotheses, total functions). -/
lemma psiIntF1_norm_le_logDeriv {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖psiIntF1 x s‖ ≤ (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) *
      ((x : ℝ) ^ s.re / ‖s‖) := by
  have hxpos : 0 ≤ x := le_of_lt hx
  have hnorm_cpow : ‖(x : ℂ) ^ s‖ = (x : ℝ) ^ s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hx s
  have hnorm_s : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  have hnorm_s1 : (0 : ℝ) ≤ ‖s - 1‖ := norm_nonneg (s - 1)
  have h1 : ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s)‖ =
      ‖logDeriv riemannZeta₁ s‖ * ((x : ℝ) ^ s.re / ‖s‖) := by
    rw [norm_mul, norm_neg, norm_div, hnorm_cpow]
  have h2 : ‖(x : ℂ) ^ s / (s * (s - 1))‖ = (x : ℝ) ^ s.re / (‖s‖ * ‖s - 1‖) := by
    rw [norm_div, norm_mul, hnorm_cpow]
  have hsplit : ‖psiIntF1 x s‖ ≤
      ‖logDeriv riemannZeta₁ s‖ * ((x : ℝ) ^ s.re / ‖s‖) +
        (x : ℝ) ^ s.re / (‖s‖ * ‖s - 1‖) := by
    calc
      ‖psiIntF1 x s‖ = ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s) +
          (x : ℂ) ^ s / (s * (s - 1))‖ := rfl
      _ ≤ ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s)‖ +
            ‖(x : ℂ) ^ s / (s * (s - 1))‖ := norm_add_le _ _
      _ = _ := by rw [h1, h2]
  have hxpow : (0 : ℝ) ≤ (x : ℝ) ^ s.re := Real.rpow_nonneg hxpos s.re
  have hstep2 : (x : ℝ) ^ s.re / (‖s‖ * ‖s - 1‖) =
      ((x : ℝ) ^ s.re / ‖s‖) * (1 / ‖s - 1‖) := by
    field_simp
  rw [hstep2] at hsplit
  calc
    ‖psiIntF1 x s‖ ≤ ‖logDeriv riemannZeta₁ s‖ * ((x : ℝ) ^ s.re / ‖s‖) +
        ((x : ℝ) ^ s.re / ‖s‖) * (1 / ‖s - 1‖) := hsplit
    _ = (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) * ((x : ℝ) ^ s.re / ‖s‖) := by
        ring

/-- **P5-left**: pointwise bound on the left slab `σ ∈ [1/4, 3/8]` (under RH), from the
commons `zeta_logDeriv_left_strip_bound`. -/
lemma psiIntF1_left_pointwise (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ σ t : ℝ, (1 / 4 : ℝ) ≤ σ → σ ≤ (3 / 8 : ℝ) →
      (2 : ℝ) ≤ |t| →
      ‖psiIntF1 x (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (Real.log (|t| + 3) + 1) ^ 3 *
          ((x : ℝ) ^ σ / ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖) := by
  rcases zeta_logDeriv_left_strip_bound h with ⟨C1, hC1pos, hC1⟩
  refine ⟨C1 + 2, by linarith, ?_⟩
  intro x hx1 σ t hσ1 hσ2 ht
  have hx0 : 0 < x := by linarith
  let s : ℂ := ((σ : ℂ) + Complex.I * (t : ℂ))
  have hL1 : (1 : ℝ) ≤ (Real.log (|t| + 3) + 1) ^ 3 := by
    have hlog : 1 ≤ Real.log (|t| + 3) + 1 := by
      have : 1 ≤ |t| + 3 := by
        have : (2 : ℝ) ≤ |t| := ht
        linarith
      have := Real.log_le_log (by norm_num : (0:ℝ) < 1) this
      simpa using this
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (Real.log (|t| + 3) + 1) ^ 3 := by exact pow_le_pow_left₀ (by norm_num) hlog 3
  have hs1 : s ≠ 1 := by
    intro hs
    have hre : s.re = σ := by simp [s]
    have him : s.im = t := by simp [s]
    have h0 := congrArg Complex.im hs
    simp [him] at h0
    have ht0 : t = 0 := h0
    rw [ht0, abs_zero] at ht
    linarith
  have hs1norm : (1 / ‖s - 1‖) ≤ 1 / (5 / 8 : ℝ) := by
    have hsre : s.re = σ := by simp [s]
    have hnorm : (5 / 8 : ℝ) ≤ ‖s - 1‖ := by
      have hre2 : (s - 1).re = σ - 1 := by simp [s]
      have hle : |(s - 1).re| ≤ ‖s - 1‖ := Complex.abs_re_le_norm (s - 1)
      rw [hre2] at hle
      have : (5 / 8 : ℝ) ≤ |σ - 1| := by
        rw [abs_of_nonpos (by linarith : σ - 1 ≤ 0)]
        linarith
      linarith
    exact one_div_le_one_div_of_le (by norm_num) hnorm
  have hlogd := hC1 σ t (by linarith) hσ2 ht
  have hnorm := psiIntF1_norm_le_logDeriv hx0 s
  have hstep : ‖psiIntF1 x s‖ ≤ (C1 + 2) * (Real.log (|t| + 3) + 1) ^ 3 *
      ((x : ℝ) ^ s.re / ‖s‖) := by
    calc
      ‖psiIntF1 x s‖ ≤ (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) *
          ((x : ℝ) ^ s.re / ‖s‖) := hnorm
      _ ≤ (C1 * (Real.log (|t| + 3) + 1) ^ 3 + 1 / (5 / 8 : ℝ)) *
          ((x : ℝ) ^ s.re / ‖s‖) := by
          have hA : ‖logDeriv riemannZeta₁ s‖ ≤ C1 * (Real.log (|t| + 3) + 1) ^ 3 := by
            simpa [s] using hlogd
          have hB : (1 / ‖s - 1‖) ≤ 1 / (5 / 8 : ℝ) := hs1norm
          have hc : (0 : ℝ) ≤ (x : ℝ) ^ s.re / ‖s‖ :=
            div_nonneg (Real.rpow_nonneg (le_of_lt hx0) s.re) (norm_nonneg s)
          exact mul_le_mul_of_nonneg_right (add_le_add hA hB) hc
      _ ≤ (C1 + 2) * (Real.log (|t| + 3) + 1) ^ 3 * ((x : ℝ) ^ s.re / ‖s‖) := by
          have hc : (0 : ℝ) ≤ (x : ℝ) ^ s.re / ‖s‖ :=
            div_nonneg (Real.rpow_nonneg (le_of_lt hx0) s.re) (norm_nonneg s)
          have hCB : C1 * (Real.log (|t| + 3) + 1) ^ 3 + 1 / (5 / 8 : ℝ) ≤
              (C1 + 2) * (Real.log (|t| + 3) + 1) ^ 3 := by nlinarith [hL1, hC1pos]
          exact mul_le_mul_of_nonneg_right hCB hc
  simpa [s, Complex.ofReal_re] using hstep

/-- **P5-right**: pointwise bound on the right slab `σ ∈ [5/8, 2]` (under RH), from the
commons `zeta_logDeriv_strip_bound_rh` with `δ = 1/8`. -/
lemma psiIntF1_right_pointwise (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ σ t : ℝ, (5 / 8 : ℝ) ≤ σ → σ ≤ (2 : ℝ) →
      (2 : ℝ) ≤ |t| →
      ‖psiIntF1 x (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (Real.log (|t| + 3) + 1) ^ 3 *
          ((x : ℝ) ^ σ / ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖) := by
  rcases zeta_logDeriv_strip_bound_rh with ⟨C1, hC1pos, hC1⟩
  refine ⟨729 * C1 + 1, by positivity, ?_⟩
  intro x hx1 σ t hσ1 hσ2 ht
  have hx0 : 0 < x := by linarith
  let s : ℂ := ((σ : ℂ) + Complex.I * (t : ℂ))
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hL1 : (1 : ℝ) ≤ (Real.log (|t| + 3) + 1) ^ 3 := by
    have hlog : 1 ≤ Real.log (|t| + 3) + 1 := by
      have h1 : 1 ≤ |t| + 3 := by
        have : (2 : ℝ) ≤ |t| := ht
        linarith
      have := Real.log_le_log (by norm_num : (0:ℝ) < 1) h1
      simpa using this
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (Real.log (|t| + 3) + 1) ^ 3 := by exact pow_le_pow_left₀ (by norm_num) hlog 3
  have hs1 : s ≠ 1 := by
    intro hs
    have h0 := congrArg Complex.im hs
    simp [hsim] at h0
    have ht0 : t = 0 := h0
    rw [ht0, abs_zero] at ht
    linarith
  have hz1 : riemannZeta₁ s ≠ 0 := by
    have hζ : riemannZeta s ≠ 0 := by
      apply zeta_ne_zero_of_rh_gt_half h
      rw [hsre]
      linarith
    have hfac : riemannZeta₁ s = (s - 1) * riemannZeta s := by
      have := riemannZeta_eq_inv_sub_mul hs1
      rw [this]
      field_simp [sub_ne_zero.mpr hs1]
    rw [hfac]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hζ
  have hlogd : ‖logDeriv riemannZeta₁ s‖ ≤ 729 * C1 * (Real.log (|t| + 3) + 1) ^ 3 + 1 / 2 := by
    rw [logDeriv_zeta1_eq hs1 hz1]
    have hdist : (1 / 4 : ℝ) ≤ ‖s - 1‖ := by
      have him : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
      have himv : (s - 1).im = t := by simp [s]
      rw [himv] at him
      linarith
    have hstrip := hC1 h (1 / 8) σ t (by norm_num) (by norm_num) (by linarith) hσ2 hdist
    have h729 : (1 + 1 / (1 / 8 : ℝ)) ^ 3 = 729 := by norm_num
    rw [h729] at hstrip
    have hstrip' : ‖deriv riemannZeta s / riemannZeta s‖ ≤
        729 * C1 * (Real.log (|t| + 3) + 1) ^ 3 := by
      have h := hstrip
      rw [mul_comm C1 729] at h
      simpa [s] using h
    have hinv : ‖(s - 1)⁻¹‖ = 1 / ‖s - 1‖ := by rw [norm_inv, one_div]
    have hhalf : 1 / ‖s - 1‖ ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have him : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
      have himv : (s - 1).im = t := by simp [s]
      rw [himv] at him
      linarith
    calc
      ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖
          ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := norm_add_le _ _
      _ ≤ 729 * C1 * (Real.log (|t| + 3) + 1) ^ 3 + 1 / 2 := by
          rw [hinv]
          linarith
  have hnorm := psiIntF1_norm_le_logDeriv hx0 s
  have hsel : (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) ≤
      (729 * C1 + 1) * (Real.log (|t| + 3) + 1) ^ 3 := by
    have hhalf : 1 / ‖s - 1‖ ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have him : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
      have himv : (s - 1).im = t := by simp [s]
      rw [himv] at him
      linarith
    nlinarith [hlogd, hhalf, hL1, hC1pos]
  have hc : (0 : ℝ) ≤ (x : ℝ) ^ s.re / ‖s‖ :=
    div_nonneg (Real.rpow_nonneg (le_of_lt hx0) s.re) (norm_nonneg s)
  calc
    ‖psiIntF1 x s‖ ≤ (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) *
        ((x : ℝ) ^ s.re / ‖s‖) := hnorm
    _ ≤ (729 * C1 + 1) * (Real.log (|t| + 3) + 1) ^ 3 * ((x : ℝ) ^ s.re / ‖s‖) :=
        mul_le_mul_of_nonneg_right hsel hc
    _ = (729 * C1 + 1) * (Real.log (|t| + 3) + 1) ^ 3 *
        ((x : ℝ) ^ σ / ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖) := by
        rw [hsre]


end Commons.NumberTheory.Zeta
end


-- ==== begin p2_edgeBounds ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# P5 (side bounds): the *right* part of the horizontal edges

The truncated explicit formula (T-R3.1) needs bounds for the three non-Peron side integrals
`edgeB`, `edgeT` (horizontal segments `[a,b]` at heights `∓Tp`) and `edgeL` (left vertical
segment `Re = a`, `Im ∈ [−Tp,Tp]`).

This module handles the piece `σ ∈ [5/8, b]` of the horizontal segments, where the pointwise
bound `psiIntF1_right_pointwise` (p2_sideBounds) applies.  The middle piece
`[1/2, 5/8]` and the left piece `[a, 1/2]` are handled with the good-height tools
(`zeta1_mid_pointwise` / `zeta1_mid_primitive_integral` / the functional equation), and the
left vertical edge with `psiIntF1_left_pointwise` plus the compact bound
`zeta1_logDeriv_left_compact`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- Right part of a horizontal segment: for `x ≥ 1`, `5/8 ≤ b ≤ 2` and `|t| ≥ 2`,

  `‖∫_{5/8}^{b} psiIntF1 x (σ + i t) dσ‖ ≤ C·(log(|t|+3)+1)^3·x^b·(b − 5/8)/|t|`.

(Under RH: the RH-conditional right-strip bound `zeta_logDeriv_strip_bound_rh` controls the
integrand; on this range the factor `x^{Re s}` is at most `x^b` and `‖s‖ ≥ |t|`.) -/
theorem edge_horiz_right_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x b t : ℝ), 1 ≤ x → (5 / 8 : ℝ) ≤ b → b ≤ 2 → 2 ≤ |t| →
      ‖∫ σ in (5 / 8)..b, psiIntF1 x ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        C * (Real.log (|t| + 3) + 1) ^ 3 * ((x : ℝ) ^ b * (b - 5 / 8) / |t|) := by
  rcases psiIntF1_right_pointwise h with ⟨C₁, hC₁pos, h₁⟩
  refine ⟨C₁, hC₁pos, ?_⟩
  intro x b t hx hb1 hb2 ht
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have htpos : (0 : ℝ) < |t| := by linarith
  have hlog3 : (0 : ℝ) < (Real.log (|t| + 3) + 1) ^ 3 := by
    have h1 : 1 ≤ |t| + 3 := by linarith
    have h2 : (0 : ℝ) ≤ Real.log (|t| + 3) := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 1) h1
      simpa using this
    have : (0 : ℝ) < Real.log (|t| + 3) + 1 := by linarith
    positivity
  -- pointwise bound on the whole interval
  have hpoint : ∀ σ ∈ Set.uIoc (5 / 8) b,
      ‖psiIntF1 x ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        C₁ * (Real.log (|t| + 3) + 1) ^ 3 * ((x : ℝ) ^ b / |t|) := by
    intro σ hσ
    rw [Set.uIoc_of_le hb1] at hσ
    have hσ1 : (5 / 8 : ℝ) ≤ σ := le_of_lt hσ.1
    have hσ2 : σ ≤ 2 := le_trans hσ.2 hb2
    have hp := h₁ x hx σ t hσ1 hσ2 ht
    have hle_pow : (x : ℝ) ^ σ ≤ (x : ℝ) ^ b :=
      Real.rpow_le_rpow_of_exponent_le hx hσ.2
    have hnorm_ge : |t| ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ := by
      have him : (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ).im = t := by simp
      have h := Complex.abs_im_le_norm (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)
      rwa [him] at h
    have hdiv : (x : ℝ) ^ σ / ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        (x : ℝ) ^ b / |t| := by
      apply div_le_div₀ (Real.rpow_nonneg (le_of_lt hx0) b) hle_pow (by positivity) hnorm_ge
    calc ‖psiIntF1 x ((σ : ℂ) + Complex.I * (t : ℂ))‖
        ≤ C₁ * (Real.log (|t| + 3) + 1) ^ 3 *
            ((x : ℝ) ^ σ / ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖) := hp
      _ ≤ C₁ * (Real.log (|t| + 3) + 1) ^ 3 * ((x : ℝ) ^ b / |t|) := by
          exact mul_le_mul_of_nonneg_left hdiv (by positivity)
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (5 / 8 : ℝ)) (b := b)
    (C := C₁ * (Real.log (|t| + 3) + 1) ^ 3 * ((x : ℝ) ^ b / |t|)) hpoint
  have habs : |b - 5 / 8| = b - 5 / 8 := abs_of_nonneg (by linarith)
  rw [habs] at hmain
  calc ‖∫ σ in (5 / 8)..b, psiIntF1 x ((σ : ℂ) + Complex.I * (t : ℂ))‖
      ≤ (C₁ * (Real.log (|t| + 3) + 1) ^ 3 * ((x : ℝ) ^ b / |t|)) * (b - 5 / 8) := hmain
    _ = C₁ * (Real.log (|t| + 3) + 1) ^ 3 * ((x : ℝ) ^ b * (b - 5 / 8) / |t|) := by
        field_simp


end Commons.NumberTheory.Zeta
end


-- ==== begin p2_edgeL2 ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# P5: the left vertical edge bound

`edgeL a Tp (psiIntF1 x) = ∫_{−Tp}^{Tp} psiIntF1 x (a + iy) dy` for `a ∈ [1/4,3/8]`.

The integrand is dominated by `K/(|y|+1)`, where the `1/|y|` decay comes from the `1/s`
factor of `psiIntF1` (via `psiIntF1_left_pointwise` for `|y| ≥ 2`) and the compactness
bound `zeta1_logDeriv_left_compact` for `|y| ≤ 2`.  Integrating `∫ dy/(|y|+1)` gives the
factor `log Tp`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Zeta

/-- **Left vertical edge bound** (P5): under RH, for `x ≥ 1`, `a ∈ [1/4,3/8]` and `Tp ≥ 5`,

  `‖edgeL a Tp (psiIntF1 x)‖ ≤ C·x^{3/8}·(log(Tp+3)+1)^4`. -/
theorem edgeL_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x a Tp : ℝ), 1 ≤ x → (1 / 4 : ℝ) ≤ a → a ≤ (3 / 8 : ℝ) →
      5 ≤ Tp →
      ‖edgeL a Tp (psiIntF1 x)‖ ≤
        C * (x : ℝ) ^ (3 / 8 : ℝ) * (Real.log (Tp + 3) + 1) ^ 4 := by
  rcases zeta1_logDeriv_left_compact h with ⟨C₀, hC₀, hC₀b⟩
  rcases psiIntF1_left_pointwise h with ⟨C₁, hC₁, h₁⟩
  refine ⟨4 * (12 * (C₀ + 2) + 2 * C₁ + 1), by linarith, ?_⟩
  intro x a Tp hx ha1 ha2 hTp
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  set F : ℝ → ℂ := fun y => psiIntF1 x ((a : ℂ) + Complex.I * (y : ℂ)) with hF
  set xr : ℝ := (x : ℝ) ^ (3 / 8 : ℝ) with hxr
  set LT : ℝ := Real.log (Tp + 3) + 1 with hLT
  have hxr0 : 0 ≤ xr := by rw [hxr]; exact Real.rpow_nonneg (le_of_lt hx0) _
  have hLT1 : 1 ≤ LT := by
    rw [hLT]
    have h2 : (0 : ℝ) ≤ Real.log (Tp + 3) :=
      Real.log_nonneg (by linarith)
    linarith
  have hLT0 : 0 ≤ LT := le_trans zero_le_one hLT1
  set K : ℝ := 12 * (C₀ + 2) * xr + 2 * C₁ * LT ^ 3 * xr with hK
  have hxrpos : 0 < xr := by rw [hxr]; exact Real.rpow_pos_of_pos hx0 _
  have hKpos : 0 < K := by
    rw [hK]
    have h1 : 0 < 12 * (C₀ + 2) * xr := mul_pos (by linarith) hxrpos
    have h2 : 0 ≤ 2 * C₁ * LT ^ 3 * xr := by positivity
    linarith
  -- pointwise domination
  have hdom : ∀ y ∈ Set.Ioc (-Tp) Tp, ‖F y‖ ≤ K / (|y| + 1) := by
    intro y hy
    have hden : (0 : ℝ) < |y| + 1 := by positivity
    by_cases hy2 : |y| ≤ 2
    · -- compact part
      have hnorm1 : ‖logDeriv riemannZeta₁ ((a : ℂ) + Complex.I * (y : ℂ))‖ ≤ C₀ :=
        hC₀b _ (by simpa using ha1) (by simpa using ha2) (by simpa using hy2)
      have hge1 : (5 / 8 : ℝ) ≤ ‖(((a : ℂ) + Complex.I * (y : ℂ) : ℂ)) - 1‖ := by
        have hle := Complex.abs_re_le_norm ((((a : ℂ) + Complex.I * (y : ℂ) : ℂ)) - 1)
        have hre : ((((a : ℂ) + Complex.I * (y : ℂ) : ℂ)) - 1).re = a - 1 := by simp
        rw [hre] at hle
        have h58 : (5 / 8 : ℝ) ≤ |a - 1| := by
          rw [abs_of_nonpos (by linarith)]; linarith
        linarith
      have hge2 : (1 / 4 : ℝ) ≤ ‖((a : ℂ) + Complex.I * (y : ℂ) : ℂ)‖ := by
        have hle := Complex.abs_re_le_norm ((a : ℂ) + Complex.I * (y : ℂ) : ℂ)
        have hre : (((a : ℂ) + Complex.I * (y : ℂ) : ℂ)).re = a := by simp
        rw [hre] at hle
        have h14 : (1 / 4 : ℝ) ≤ |a| := by rw [abs_of_nonneg (by linarith)]; exact ha1
        linarith
      have hnorm2 : 1 / ‖(((a : ℂ) + Complex.I * (y : ℂ) : ℂ)) - 1‖ ≤ 2 := by
        rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5 / 8) hge1)]
        linarith
      have hnorm3 : (1 : ℝ) / ‖((a : ℂ) + Complex.I * (y : ℂ) : ℂ)‖ ≤ 4 := by
        rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hge2)]
        linarith
      have hs := psiIntF1_norm_le_logDeriv hx0 ((a : ℂ) + Complex.I * (y : ℂ))
      have hre : (((a : ℂ) + Complex.I * (y : ℂ) : ℂ)).re = a := by simp
      have hxs : (x : ℝ) ^ a ≤ xr := by rw [hxr]; exact Real.rpow_le_rpow_of_exponent_le hx ha2
      have hFn : ‖F y‖ ≤ (C₀ + 2) * (xr * 4) := by
        rw [hF]
        have h1 : ‖logDeriv riemannZeta₁ ((a : ℂ) + Complex.I * (y : ℂ))‖ +
            1 / ‖(((a : ℂ) + Complex.I * (y : ℂ) : ℂ)) - 1‖ ≤ C₀ + 2 := by linarith
        have h2 : (x : ℝ) ^ (((a : ℂ) + Complex.I * (y : ℂ) : ℂ)).re /
            ‖((a : ℂ) + Complex.I * (y : ℂ) : ℂ)‖ ≤ xr * 4 := by
          rw [hre]
          have h3 : (x : ℝ) ^ a / ‖((a : ℂ) + Complex.I * (y : ℂ) : ℂ)‖ ≤
              xr / ‖((a : ℂ) + Complex.I * (y : ℂ) : ℂ)‖ :=
            div_le_div_of_nonneg_right hxs (norm_nonneg _)
          have h4 : xr / ‖((a : ℂ) + Complex.I * (y : ℂ) : ℂ)‖ ≤ xr * 4 := by
            rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hge2)]
            nlinarith [hge2, hxr0]
          linarith
        calc ‖psiIntF1 x ((a : ℂ) + Complex.I * (y : ℂ))‖
            ≤ (‖logDeriv riemannZeta₁ ((a : ℂ) + Complex.I * (y : ℂ))‖ +
                1 / ‖(((a : ℂ) + Complex.I * (y : ℂ) : ℂ)) - 1‖) *
                ((x : ℝ) ^ (((a : ℂ) + Complex.I * (y : ℂ) : ℂ)).re /
                  ‖((a : ℂ) + Complex.I * (y : ℂ) : ℂ)‖) := hs
          _ ≤ (C₀ + 2) * (xr * 4) := mul_le_mul h1 h2 (by positivity) (by linarith)
      -- and `(C₀+2)*4*xr ≤ K/(|y|+1)`
      have hy3 : |y| + 1 ≤ 3 := by linarith
      have hKg : 12 * (C₀ + 2) * xr ≤ K := by
        rw [hK]
        have h2 : 0 ≤ 2 * C₁ * LT ^ 3 * xr := by positivity
        linarith
      have hgoal : (C₀ + 2) * (xr * 4) ≤ K / (|y| + 1) := by
        rw [le_div_iff₀ hden]
        have h1 : (C₀ + 2) * (xr * 4) * (|y| + 1) ≤ (C₀ + 2) * (xr * 4) * 3 :=
          mul_le_mul_of_nonneg_left hy3 (by positivity)
        have h2 : (C₀ + 2) * (xr * 4) * 3 = 12 * (C₀ + 2) * xr := by ring
        rw [h2] at h1
        linarith [h1, hKg]
      linarith [hFn, hgoal]
    · -- far part
      push_neg at hy2
      have hypos : (0 : ℝ) < |y| := by linarith
      have hys : |y| ≤ Tp := abs_le.mpr ⟨le_of_lt hy.1, hy.2⟩
      have hnorm1 := h₁ x hx a y (by linarith : (1 / 4 : ℝ) ≤ a) ha2 (le_of_lt hy2)
      have hFn : ‖F y‖ ≤ C₁ * LT ^ 3 * (xr / |y|) := by
        rw [hF]
        have hlog : Real.log (|y| + 3) + 1 ≤ LT := by
          rw [hLT]
          have h1 : Real.log (|y| + 3) ≤ Real.log (Tp + 3) :=
            Real.log_le_log (by linarith) (by linarith)
          linarith
        have hlog0 : (0 : ℝ) ≤ Real.log (|y| + 3) + 1 := by
          have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ |y| + 3)
          linarith
        have hp3 : (Real.log (|y| + 3) + 1) ^ 3 ≤ LT ^ 3 := pow_le_pow_left₀ hlog0 hlog 3
        have hxs : (x : ℝ) ^ a ≤ xr := by rw [hxr]; exact Real.rpow_le_rpow_of_exponent_le hx ha2
        have hden2 : |y| ≤ ‖((a : ℂ) + Complex.I * (y : ℂ) : ℂ)‖ := by
          have him : |(((a : ℂ) + Complex.I * (y : ℂ) : ℂ)).im| ≤
              ‖((a : ℂ) + Complex.I * (y : ℂ) : ℂ)‖ := Complex.abs_im_le_norm _
          have h2 : (((a : ℂ) + Complex.I * (y : ℂ) : ℂ)).im = y := by simp
          rw [h2] at him
          exact him
        have hdiv : (x : ℝ) ^ a / ‖((a : ℂ) + Complex.I * (y : ℂ) : ℂ)‖ ≤ xr / |y| :=
          div_le_div₀ hxr0 hxs hypos hden2
        calc ‖psiIntF1 x ((a : ℂ) + Complex.I * (y : ℂ))‖
            ≤ C₁ * (Real.log (|y| + 3) + 1) ^ 3 *
                ((x : ℝ) ^ a / ‖((a : ℂ) + Complex.I * (y : ℂ) : ℂ)‖) := hnorm1
          _ ≤ C₁ * LT ^ 3 * (xr / |y|) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hp3 (le_of_lt hC₁)) hdiv
                (by positivity) (by positivity)
      have hKg : 2 * C₁ * LT ^ 3 * xr ≤ K := by
        rw [hK]
        have h2 : 0 ≤ 12 * (C₀ + 2) * xr := by positivity
        linarith
      have hgoal : C₁ * LT ^ 3 * (xr / |y|) ≤ K / (|y| + 1) := by
        rw [← mul_div_assoc, div_le_div_iff₀ hypos hden]
        have h1 : C₁ * LT ^ 3 * xr * (|y| + 1) ≤ C₁ * LT ^ 3 * xr * (2 * |y|) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have h2 : C₁ * LT ^ 3 * xr * (2 * |y|) = (2 * C₁ * LT ^ 3 * xr) * |y| := by ring
        rw [h2] at h1
        have h3 : (2 * C₁ * LT ^ 3 * xr) * |y| ≤ K * |y| :=
          mul_le_mul_of_nonneg_right hKg (le_of_lt hypos)
        linarith [h1, h3]
      linarith [hFn, hgoal]
  -- integral of the dominating function
  have hGcont : Continuous fun y : ℝ => K / (|y| + 1) := by
    have hden : Continuous fun y : ℝ => |y| + 1 := continuous_abs.add continuous_const
    have hne : ∀ y : ℝ, |y| + 1 ≠ 0 := fun y => by positivity
    exact continuous_const.div hden hne
  have hEdgeL : edgeL a Tp (psiIntF1 x) = ∫ y in (-Tp)..Tp, F y := by
    rw [edgeL, zRect_re]
    apply intervalIntegral.integral_congr
    intro y hy
    change psiIntF1 x ((a : ℂ) + y * Complex.I) = psiIntF1 x ((a : ℂ) + Complex.I * (y : ℂ))
    rw [mul_comm]
  rw [hEdgeL]
  have hnorm : ‖∫ y in (-Tp)..Tp, F y‖ ≤ ∫ y in (-Tp)..Tp, K / (|y| + 1) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Filter.Eventually.of_forall (fun y hy => ?_)) (hGcont.intervalIntegrable _ _)
    exact hdom y hy
  have hmid : ∫ y in (-1)..1, K / (|y| + 1) ≤ 2 * K := by
    have h1 : ‖∫ y in (-1)..1, K / (|y| + 1)‖ ≤ K * |(1 : ℝ) - (-1)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => by
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hy
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact div_le_self (le_of_lt hKpos) (by linarith [abs_nonneg y]))
    have h2 : |(1 : ℝ) - (-1)| = 2 := by norm_num
    have hnn : (0 : ℝ) ≤ ∫ y in (-1)..1, K / (|y| + 1) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun y _ => by positivity)
    rw [h2, Real.norm_eq_abs, abs_of_nonneg hnn] at h1
    linarith
  have hright : ∫ y in (1)..Tp, K / (|y| + 1) = K * Real.log ((Tp + 1) / 2) := by
    have heq : (∫ y in (1)..Tp, K / (|y| + 1)) =
        ∫ y in (1)..Tp, (fun u : ℝ => K / u) (y + 1) := by
      apply intervalIntegral.integral_congr
      intro y hy
      show K / (|y| + 1) = K / (y + 1)
      rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ Tp)] at hy
      rw [abs_of_nonneg (by linarith [hy.1] : (0:ℝ) ≤ y)]
    rw [heq]
    have hcomp : (∫ y in (1)..Tp, (fun u : ℝ => K / u) (y + 1)) =
        ∫ u in (2)..(Tp + 1), K / u := by
      rw [intervalIntegral.integral_comp_add_right (f := fun u : ℝ => K / u)
        (a := (1 : ℝ)) (b := Tp) (d := 1)]
      norm_num
    rw [hcomp]
    have hstep : (∫ u in (2)..(Tp + 1), K / u) = K * ∫ u in (2)..(Tp + 1), u⁻¹ :=
      intervalIntegral.integral_const_mul K (fun u : ℝ => u⁻¹)
    rw [hstep, integral_inv_of_pos (by norm_num : (0 : ℝ) < 2)
      (by linarith : (0 : ℝ) < Tp + 1),
      Real.log_div (by linarith : (Tp + 1 : ℝ) ≠ 0) (by norm_num)]
  have hleft : ∫ y in (-Tp)..(-1), K / (|y| + 1) = K * Real.log ((Tp + 1) / 2) := by
    have hsym : (∫ y in (-Tp)..(-1), K / (|y| + 1)) = ∫ y in (1)..Tp, K / (|y| + 1) := by
      have hh := intervalIntegral.integral_comp_neg (f := fun u : ℝ => K / (|u| + 1))
        (a := (1 : ℝ)) (b := Tp)
      simpa using hh.symm
    rw [hsym, hright]
  have hsplit : ∫ y in (-Tp)..Tp, K / (|y| + 1) =
      (∫ y in (-Tp)..(-1), K / (|y| + 1)) + (∫ y in (-1)..1, K / (|y| + 1)) +
        (∫ y in (1)..Tp, K / (|y| + 1)) := by
    rw [(intervalIntegral.integral_add_adjacent_intervals
      (hGcont.intervalIntegrable (-Tp) (-1)) (hGcont.intervalIntegrable (-1) Tp)).symm]
    rw [(intervalIntegral.integral_add_adjacent_intervals
      (hGcont.intervalIntegrable (-1) 1) (hGcont.intervalIntegrable 1 Tp)).symm]
    ring
  -- final bookkeeping
  have hlog : Real.log ((Tp + 1) / 2) ≤ LT := by
    rw [hLT]
    have h1 : Real.log ((Tp + 1) / 2) ≤ Real.log (Tp + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log ((Tp + 1) / 2) := Real.log_nonneg (by linarith)
  have hLT3 : (1 : ℝ) ≤ LT ^ 3 := one_le_pow₀ hLT1
  have hKle : K ≤ (12 * (C₀ + 2) + 2 * C₁) * xr * LT ^ 3 := by
    have h2 : 2 * C₁ * LT ^ 3 * xr = 2 * C₁ * xr * LT ^ 3 := by ring
    rw [hK, h2]
    have h1 : 12 * (C₀ + 2) * xr ≤ 12 * (C₀ + 2) * xr * LT ^ 3 :=
      le_mul_of_one_le_right (by positivity) hLT3
    have h3 : (12 * (C₀ + 2) + 2 * C₁) * xr * LT ^ 3 =
        12 * (C₀ + 2) * xr * LT ^ 3 + 2 * C₁ * xr * LT ^ 3 := by ring
    rw [h3]
    linarith
  have hKL : K * Real.log ((Tp + 1) / 2) ≤ (12 * (C₀ + 2) + 2 * C₁) * xr * LT ^ 4 := by
    have h1 : K * Real.log ((Tp + 1) / 2) ≤
        (12 * (C₀ + 2) + 2 * C₁) * xr * LT ^ 3 * LT :=
      mul_le_mul hKle hlog hlog0 (by positivity)
    have h2 : (12 * (C₀ + 2) + 2 * C₁) * xr * LT ^ 3 * LT =
        (12 * (C₀ + 2) + 2 * C₁) * xr * LT ^ 4 := by ring
    linarith [h1, h2]
  have h2K : 2 * K ≤ 2 * ((12 * (C₀ + 2) + 2 * C₁) * xr * LT ^ 4) := by
    have h1 : 2 * K ≤ 2 * ((12 * (C₀ + 2) + 2 * C₁) * xr * LT ^ 3) :=
      mul_le_mul_of_nonneg_left hKle (by norm_num)
    have h34 : LT ^ 3 ≤ LT ^ 4 := by
      simpa using pow_le_pow_right₀ hLT1 (by norm_num : (3 : ℕ) ≤ 4)
    have h2 : (12 * (C₀ + 2) + 2 * C₁) * xr * LT ^ 3 ≤
        (12 * (C₀ + 2) + 2 * C₁) * xr * LT ^ 4 :=
      mul_le_mul_of_nonneg_left h34 (by positivity)
    linarith
  have hfin : K * Real.log ((Tp + 1) / 2) + 2 * K + K * Real.log ((Tp + 1) / 2) ≤
      4 * (12 * (C₀ + 2) + 2 * C₁ + 1) * xr * LT ^ 4 := by
    have hsum : K * Real.log ((Tp + 1) / 2) + 2 * K + K * Real.log ((Tp + 1) / 2) ≤
        4 * (12 * (C₀ + 2) + 2 * C₁) * xr * LT ^ 4 := by linarith [hKL, h2K]
    have hxLT : (0 : ℝ) ≤ xr * LT ^ 4 := by positivity
    have hM : 4 * (12 * (C₀ + 2) + 2 * C₁) ≤ 4 * (12 * (C₀ + 2) + 2 * C₁ + 1) := by linarith
    have := mul_le_mul_of_nonneg_right hM hxLT
    nlinarith [hsum, this]
  calc ‖∫ y in (-Tp)..Tp, F y‖
      ≤ ∫ y in (-Tp)..Tp, K / (|y| + 1) := hnorm
    _ ≤ K * Real.log ((Tp + 1) / 2) + 2 * K + K * Real.log ((Tp + 1) / 2) := by
        rw [hsplit, hleft, hright]
        linarith [hmid]
    _ ≤ 4 * (12 * (C₀ + 2) + 2 * C₁ + 1) * xr * LT ^ 4 := hfin
    _ = 4 * (12 * (C₀ + 2) + 2 * C₁ + 1) * (x : ℝ) ^ (3 / 8 : ℝ) *
          (Real.log (Tp + 3) + 1) ^ 4 := by rw [hxr, hLT]


end Commons.NumberTheory.Zeta
end


-- ==== begin p2_horizBounds ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# P5 (continued): the middle and left parts of the horizontal edges

`edge_horiz_right_bound` (p2_edgeBounds) bounds the piece `σ ∈ [5/8, b]` of a horizontal edge
at height `Tp` by the RH right-strip bound.  Here we add the remaining pieces of the
horizontal edges `[a, 5/8]` (with `a ∈ [1/4,3/8]`):

* `zeta_logDeriv_horiz_right` : pointwise bound for `ζ'/ζ(σ + iTp)` on `σ ∈ [1/2,3/4]`
  (middle strip `[1/2,5/8]` from `zeta1_mid_pointwise`, right strip `[5/8,3/4]` from
  `zeta_logDeriv_strip_bound_rh`);
* `psiIntF1_horiz_left_pointwise` : pointwise bound for `psiIntF1 x (σ + iTp)` on
  `σ ∈ [1/4,1/2]`, via the functional equation `zeta_logDeriv_fe_expanded`;
* `edge_horiz_left_mid_bound` : the integral bound for `[1/4,5/8]`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators ComplexConjugate

noncomputable section
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Zeta

/-- From "no nontrivial zero within `δ` of the ordinate `Tp`" one gets the same statement at
`-Tp`, by conjugation symmetry of the zeta zeros. -/
lemma no_zero_neg_im {Tp δ : ℝ}
    (hno : ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im - Tp| ≤ δ → False) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im + Tp| ≤ δ → False := by
  intro ρ hz h
  refine hno (conj ρ) ?_ ?_
  · rw [riemannZeta_conj, hz, map_zero]
  · have him : (conj ρ).im = -ρ.im := Complex.conj_im ρ
    rw [him]
    have h2 : -ρ.im - Tp = -(ρ.im + Tp) := by ring
    rw [h2, abs_neg]
    exact h

/-- conjugation symmetry of `ζ` in composition form. -/
lemma riemannZeta_conj_comp : riemannZeta = conj ∘ riemannZeta ∘ conj := by
  funext z
  simp [Function.comp, riemannZeta_conj]

/-- derivative conjugation symmetry of `ζ`. -/
lemma deriv_riemannZeta_conj (z : ℂ) :
    deriv riemannZeta (conj z) = conj (deriv riemannZeta z) := by
  have hsymm : riemannZeta = conj ∘ riemannZeta ∘ conj := riemannZeta_conj_comp
  have hd := deriv_conj_conj (f := riemannZeta)
  have hmain : deriv riemannZeta z = conj (deriv riemannZeta (conj z)) := by
    calc deriv riemannZeta z = deriv (conj ∘ riemannZeta ∘ conj) z := by rw [← hsymm]
      _ = (conj ∘ deriv riemannZeta ∘ conj) z := by rw [hd]
      _ = conj (deriv riemannZeta (conj z)) := by simp
  calc deriv riemannZeta (conj z) = conj (conj (deriv riemannZeta (conj z))) := by simp
    _ = conj (deriv riemannZeta z) := by rw [hmain]

/-- conjugation symmetry of the zeta log-derivative. -/
lemma logDeriv_conj_zeta (z : ℂ) :
    deriv riemannZeta (conj z) / riemannZeta (conj z) =
      conj (deriv riemannZeta z / riemannZeta z) := by
  rw [deriv_riemannZeta_conj, riemannZeta_conj, map_div₀]

/-- On the critical line at a height `Tp` whose `2 + iTp`-ball of radius `3/2 + δ²/4` is
zero-free, `ζ` has no zero. -/
lemma riemannZeta_ne_zero_of_half_ball {Tp δ : ℝ} (hTp0 : Tp ≠ 0) (_hδ0 : 0 < δ)
    (hball : ∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (Tp : ℂ))‖ < (3 / 2 : ℝ) + δ ^ 2 / 4 →
      riemannZeta₁ w ≠ 0)
    {w : ℂ} (hre : w.re = 1 / 2) (him : w.im = Tp) : riemannZeta w ≠ 0 := by
  intro hz
  have hw1 : w ≠ 1 := by
    intro hh
    have h2 := congrArg Complex.im hh
    rw [him] at h2
    simp at h2
    exact hTp0 h2
  have hz1 : riemannZeta₁ w ≠ 0 := hball w (by
    have hsub : w - ((2 : ℂ) + Complex.I * (Tp : ℂ)) = ((1 / 2 - 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [hre]
      · simp [him]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonpos (by norm_num : (1 / 2 : ℝ) - 2 ≤ 0)]
    have h4 : (0 : ℝ) < δ ^ 2 / 4 := by positivity
    linarith)
  have hfac2 : riemannZeta₁ w = (w - 1) * riemannZeta w := by
    have hh := riemannZeta_eq_inv_sub_mul hw1
    rw [hh]
    field_simp [sub_ne_zero.mpr hw1]
  exact hz1 (by rw [hfac2, hz, mul_zero])

/-- **P5 middle/right pointwise bound**: on `σ ∈ [1/2, 3/4]` at a good height `Tp`,

`‖ζ'/ζ(σ + iTp)‖ ≤ C·(log(T+3)+1)^3/δ^4`. -/
theorem zeta_logDeriv_horiz_right (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ T Tp δ : ℝ, 5 ≤ T → T ≤ Tp → Tp ≤ T + 1 → 0 < δ → δ ≤ 1 / 4 →
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (Tp : ℂ))‖ < (3 / 2 : ℝ) + δ ^ 2 / 4 →
        riemannZeta₁ w ≠ 0) →
      ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → σ ≤ (3 / 4 : ℝ) →
        ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (Tp : ℂ)) : ℂ)) /
            riemannZeta (((σ : ℂ) + Complex.I * (Tp : ℂ)) : ℂ)‖ ≤
          C * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ := by
  rcases zeta1_mid_pointwise h with ⟨C₁, hC₁, h₁⟩
  rcases zeta_logDeriv_strip_bound_rh with ⟨C₂, hC₂, h₂⟩
  refine ⟨max (16 * C₁ + 1) (5832 * C₂ + 1), by positivity, ?_⟩
  intro T Tp δ hT hTTp hTp1 hδ0 hδ4 hball σ hσ1 hσ2
  have hTp5 : 5 ≤ Tp := le_trans hT hTTp
  have hTp0 : 0 < Tp := by linarith
  set s : ℂ := (σ : ℂ) + Complex.I * (Tp : ℂ) with hs
  have hsim : s.im = Tp := by simp [hs]
  have hδ4pos : 0 < δ ^ 4 := by positivity
  have hδ4le1 : δ ^ 4 ≤ 1 := by
    have hh := pow_le_pow_left₀ (le_of_lt hδ0) hδ4 4
    norm_num at hh
    linarith
  have hDinv1 : (1 : ℝ) ≤ (δ ^ 4)⁻¹ := (one_le_inv₀ hδ4pos).mpr hδ4le1
  have hlog1 : 1 ≤ Real.log (T + 3) + 1 := by
    have h2 : (0 : ℝ) ≤ Real.log (T + 3) := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ T + 3)
      simpa using this
    linarith
  have hL3ge1 : (1 : ℝ) ≤ (Real.log (T + 3) + 1) ^ 3 := one_le_pow₀ hlog1
  have hL3pos : (0 : ℝ) < (Real.log (T + 3) + 1) ^ 3 := by linarith
  have hDge : δ ^ 2 / 4 ≤ σ - 1 / 2 + δ ^ 2 / 4 := by linarith
  have hDpos : 0 < σ - 1 / 2 + δ ^ 2 / 4 := lt_of_lt_of_le (by positivity) hDge
  -- `1/(σ-1/2+δ²/4)² ≤ 16·δ⁻⁴`
  have hinv : ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2)⁻¹ ≤ 16 * (δ ^ 4)⁻¹ := by
    have h2 : δ ^ 4 / 16 ≤ (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 := by
      have h3 : (δ ^ 2 / 4) ^ 2 ≤ (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hDge 2
      have h4 : (δ ^ 2 / 4) ^ 2 = δ ^ 4 / 16 := by ring
      rw [h4] at h3
      exact h3
    have h := (inv_le_inv₀ (pow_pos hDpos 2) (by positivity : (0 : ℝ) < δ ^ 4 / 16)).mpr h2
    rwa [show (δ ^ 4 / 16)⁻¹ = 16 * (δ ^ 4)⁻¹ by field_simp] at h
  by_cases hmid : σ ≤ 5 / 8
  · have hb := h₁ T Tp δ hT hTTp hTp1 hδ0 hδ4 hball σ hσ1 hmid
    have hb' : ‖logDeriv riemannZeta₁ s‖ ≤
        C₁ * (Real.log (T + 3) + 1) * ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2)⁻¹ := by
      rw [hs]
      simpa only [div_eq_mul_inv] using hb
    have hs1 : s ≠ 1 := by
      intro hh
      have h2 := congrArg Complex.im hh
      simp [hsim] at h2
      linarith
    have hfac2 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
      have hh := riemannZeta_eq_inv_sub_mul hs1
      rw [hh]
      field_simp [sub_ne_zero.mpr hs1]
    have hz : riemannZeta s ≠ 0 := by
      intro hzs
      have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
        rintro ⟨n, hn⟩
        have h2 := congrArg Complex.im hn
        simp [hsim] at h2
        linarith
      have hre : s.re = 1 / 2 := h s hzs htriv hs1
      exact riemannZeta_ne_zero_of_half_ball (ne_of_gt hTp0) hδ0 hball (w := s)
        (by simpa [hs] using hre) (by rw [hs]; simp) hzs
    have hz1 : riemannZeta₁ s ≠ 0 := by
      rw [hfac2]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) hz
    have hid : deriv riemannZeta s / riemannZeta s =
        logDeriv riemannZeta₁ s - (s - 1)⁻¹ := by
      have hh := logDeriv_zeta1_eq hs1 hz1
      rw [hh]
      ring
    rw [hid]
    have hinv2 : ‖(s - 1)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      refine inv_le_one_of_one_le₀ ?_
      have him : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
      have h2 : (s - 1).im = Tp := by simp [hs]
      rw [h2, abs_of_pos hTp0] at him
      linarith
    have hb2 : C₁ * (Real.log (T + 3) + 1) * ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2)⁻¹ + 1 ≤
        (16 * C₁ + 1) * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ := by
      have h1 : C₁ * (Real.log (T + 3) + 1) * ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2)⁻¹ ≤
          C₁ * (Real.log (T + 3) + 1) * (16 * (δ ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      have h2 : C₁ * (Real.log (T + 3) + 1) ≤ C₁ * (Real.log (T + 3) + 1) ^ 3 :=
        mul_le_mul_of_nonneg_left
          (by simpa using pow_le_pow_right₀ hlog1 (by norm_num : (1 : ℕ) ≤ 3)) (le_of_lt hC₁)
      have h3 : C₁ * (Real.log (T + 3) + 1) * (16 * (δ ^ 4)⁻¹) =
          16 * C₁ * (Real.log (T + 3) + 1) * (δ ^ 4)⁻¹ := by ring
      have h4 : (16 * C₁ + 1) * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ =
          16 * C₁ * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ +
          (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ := by ring
      have h5 : 16 * C₁ * (Real.log (T + 3) + 1) * (δ ^ 4)⁻¹ ≤
          16 * C₁ * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ := by
        have hab : 16 * C₁ * (Real.log (T + 3) + 1) ≤
            16 * C₁ * (Real.log (T + 3) + 1) ^ 3 := by nlinarith [h2, hC₁]
        exact mul_le_mul_of_nonneg_right hab (by positivity)
      have h6 : (1 : ℝ) ≤ (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ := by
        have hh := mul_le_mul hL3ge1 hDinv1 (by norm_num) (le_of_lt hL3pos)
        simpa using hh
      rw [h4]
      linarith
    have htri : ‖logDeriv riemannZeta₁ s - (s - 1)⁻¹‖ ≤
        ‖logDeriv riemannZeta₁ s‖ + ‖(s - 1)⁻¹‖ := norm_sub_le _ _
    have hmid2 : ‖logDeriv riemannZeta₁ s‖ + ‖(s - 1)⁻¹‖ ≤
        C₁ * (Real.log (T + 3) + 1) * ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2)⁻¹ + 1 :=
      add_le_add hb' hinv2
    have hfin : C₁ * (Real.log (T + 3) + 1) * ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2)⁻¹ + 1 ≤
        max (16 * C₁ + 1) (5832 * C₂ + 1) * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ :=
      le_trans hb2 (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hL3pos)) (by positivity))
    exact le_trans htri (le_trans hmid2 hfin)
  · -- right strip
    push_neg at hmid
    have hb := h₂ h (1 / 8) σ Tp (by norm_num) (by norm_num)
      (by linarith [hmid]) (by linarith [hσ2])
      (by
        have him : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
        have h1 : (s - 1).im = Tp := by simp [hs]
        rw [h1, abs_of_pos hTp0] at him
        linarith)
    have h729 : (1 + 1 / (1 / 8 : ℝ)) ^ 3 = 729 := by norm_num
    rw [h729] at hb
    have hb' : ‖deriv riemannZeta s / riemannZeta s‖ ≤
        729 * C₂ * (Real.log (Tp + 3) + 1) ^ 3 := by
      have hthis := hb
      simpa [abs_of_pos hTp0, mul_comm C₂ 729] using hthis
    have hlogTp : Real.log (Tp + 3) + 1 ≤ 2 * (Real.log (T + 3) + 1) := by
      have h1 : Tp + 3 ≤ 2 * (T + 3) := by linarith
      have h2 : Real.log (Tp + 3) ≤ Real.log (2 * (T + 3)) :=
        Real.log_le_log (by linarith) h1
      rw [Real.log_mul (by norm_num) (by linarith)] at h2
      have h3 : Real.log 2 ≤ Real.log (T + 3) :=
        Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hcube : (Real.log (Tp + 3) + 1) ^ 3 ≤ 8 * (Real.log (T + 3) + 1) ^ 3 := by
      have h0 : (0 : ℝ) ≤ Real.log (Tp + 3) + 1 := by
        have h2 : (0 : ℝ) ≤ Real.log (Tp + 3) := by
          have := Real.log_le_log (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ Tp + 3)
          simpa using this
        linarith
      calc (Real.log (Tp + 3) + 1) ^ 3 ≤ (2 * (Real.log (T + 3) + 1)) ^ 3 :=
            pow_le_pow_left₀ h0 hlogTp 3
        _ = 8 * (Real.log (T + 3) + 1) ^ 3 := by ring
    have hM : 729 * (8 * C₂) ≤ max (16 * C₁ + 1) (5832 * C₂ + 1) := by
      have h1 : 729 * (8 * C₂) = 5832 * C₂ := by ring
      rw [h1]
      exact le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _)
    calc ‖deriv riemannZeta s / riemannZeta s‖
        ≤ 729 * C₂ * (Real.log (Tp + 3) + 1) ^ 3 := hb'
      _ ≤ 729 * C₂ * (8 * (Real.log (T + 3) + 1) ^ 3) :=
          mul_le_mul_of_nonneg_left hcube (by positivity)
      _ = (729 * (8 * C₂)) * (Real.log (T + 3) + 1) ^ 3 := by ring
      _ ≤ max (16 * C₁ + 1) (5832 * C₂ + 1) * (Real.log (T + 3) + 1) ^ 3 :=
          mul_le_mul_of_nonneg_right hM (le_of_lt hL3pos)
      _ ≤ max (16 * C₁ + 1) (5832 * C₂ + 1) * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ :=
          le_mul_of_one_le_right (by positivity) hDinv1


/-- Pointwise bound for `psiIntF1 x (σ + iTp)` on the left half `σ ∈ [1/4, 1/2]` of a
horizontal edge, via the functional equation `zeta_logDeriv_fe_expanded`. -/
theorem psiIntF1_horiz_left_pointwise (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T Tp δ : ℝ, 1 ≤ x → 5 ≤ T → T ≤ Tp → Tp ≤ T + 1 →
      0 < δ → δ ≤ 1 / 4 →
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (Tp : ℂ))‖ < (3 / 2 : ℝ) + δ ^ 2 / 4 →
        riemannZeta₁ w ≠ 0) →
      ∀ σ : ℝ, (1 / 4 : ℝ) ≤ σ → σ ≤ (1 / 2 : ℝ) →
        ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤
          C * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ *
            ((x : ℝ) ^ (1 / 2 : ℝ) / Tp) := by
  rcases zeta_logDeriv_horiz_right h with ⟨C₁, hC₁, h₁⟩
  refine ⟨C₁ + 20, by positivity, ?_⟩
  intro x T Tp δ hx hT hTTp hTp1 hδ0 hδ4 hball σ hσ1 hσ2
  set L : ℝ := Real.log (T + 3) + 1 with hLdef
  set Dinv : ℝ := (δ ^ 4)⁻¹ with hDdef
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hTp5 : 5 ≤ Tp := le_trans hT hTTp
  have hTp0 : 0 < Tp := by linarith
  have hTpne : Tp ≠ 0 := ne_of_gt hTp0
  have hδ4pos : 0 < δ ^ 4 := by positivity
  have hδ4le1 : δ ^ 4 ≤ 1 := by
    have hh := pow_le_pow_left₀ (le_of_lt hδ0) hδ4 4
    norm_num at hh
    linarith
  have hDinv1 : (1 : ℝ) ≤ Dinv := by
    rw [hDdef]; exact (one_le_inv₀ hδ4pos).mpr hδ4le1
  have hDinvpos : (0 : ℝ) < Dinv := by rw [hDdef]; positivity
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h2 : (0 : ℝ) ≤ Real.log (T + 3) := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ T + 3)
      simpa using this
    linarith
  have hL3ge1 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
  have hL3pos : (0 : ℝ) < L ^ 3 := by linarith
  have hA1 : (1 : ℝ) ≤ L ^ 3 * Dinv := by
    have hh := mul_le_mul hL3ge1 hDinv1 (by norm_num) (le_of_lt hL3pos)
    simpa using hh
  have hApos : (0 : ℝ) < L ^ 3 * Dinv := by linarith
  have hLA : L ≤ L ^ 3 * Dinv := by
    have h2 : L ≤ L ^ 3 := by
      simpa using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 3)
    calc L ≤ L ^ 3 := h2
      _ ≤ L ^ 3 * Dinv := le_mul_of_one_le_right (le_of_lt hL3pos) hDinv1
  set s : ℂ := (σ : ℂ) + Complex.I * (Tp : ℂ) with hs
  set u : ℂ := ((1 - σ : ℝ) : ℂ) + Complex.I * (Tp : ℂ) with hu
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = Tp := by simp [hs]
  have hure : u.re = 1 - σ := by simp [hu]
  have huim : u.im = Tp := by simp [hu]
  have hw : 1 - s = conj u := by
    apply Complex.ext <;> simp [hs, hu]
  have hs1 : s ≠ 1 := by
    intro hh
    have h2 := congrArg Complex.im hh
    simp [hsim] at h2
    linarith
  have hs0 : s ≠ 0 := by
    intro hh
    have h2 := congrArg Complex.im hh
    simp [hsim] at h2
    linarith
  have hζs : riemannZeta s ≠ 0 := by
    by_cases hσh : σ = 1 / 2
    · exact riemannZeta_ne_zero_of_half_ball hTpne hδ0 hball (by rw [hsre]; exact hσh)
        (by rw [hsim])
    · intro hz
      have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
        rintro ⟨n, hn⟩
        have h2 := congrArg Complex.im hn
        simp [hsim] at h2
        linarith
      have hhalf : s.re = 1 / 2 := h s hz htriv hs1
      exact hσh (by rw [← hsre]; exact hhalf)
  have hζw : riemannZeta (1 - s) ≠ 0 := by
    have huwn : riemannZeta u ≠ 0 := by
      by_cases hu2 : u.re = 1 / 2
      · exact riemannZeta_ne_zero_of_half_ball hTpne hδ0 hball hu2 (by rw [huim])
      · have hle : (1 / 2 : ℝ) ≤ u.re := by rw [hure]; linarith
        exact zeta_ne_zero_of_rh_gt_half h (lt_of_le_of_ne hle (Ne.symm hu2))
    rw [hw]
    intro hc
    refine huwn ?_
    have hcong := congrArg conj hc
    simpa [riemannZeta_conj] using hcong
  have hΓ : ∀ n : ℕ, 1 - s ≠ -↑n := by
    intro n hn
    have him := congrArg Complex.im hn
    have h1 : (1 - s).im = -Tp := by simp [hs]
    rw [h1] at him
    simp at him
    linarith
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    rcases hc with ⟨k, hk⟩
    have him := congrArg Complex.im hk
    have h1 : (↑Real.pi * (1 - s) / 2).im = -(Real.pi * Tp / 2) := by
      simp [hs]; ring
    have h2 : (((2 * (k : ℂ) + 1) * (↑Real.pi) / 2 : ℂ)).im = 0 := by
      have hcast : ((2 * (k : ℂ) + 1) * (↑Real.pi) / 2 : ℂ) =
          (((2 * (k : ℝ) + 1) * Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hcast]; simp
    rw [h1, h2] at him
    have hpos : 0 < Real.pi * Tp / 2 := by
      have hπ : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
      positivity
    linarith
  have hFE := zeta_logDeriv_fe_expanded hζs hζw hs0 hs1 hΓ hcos
  have hdig : ‖Complex.digamma (1 - s)‖ ≤ L + 2 := by
    have hd := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
      (1 - σ) (-Tp) (by linarith) (by linarith)
    have heq : (((1 - σ : ℝ) : ℂ) + ((-Tp : ℝ) : ℂ) * Complex.I) = 1 - s := by
      simp [hs]; ring
    rw [heq, abs_neg, abs_of_pos hTp0] at hd
    have hlog : Real.log (2 + Tp) ≤ L := by
      rw [hLdef]
      have h1 : Real.log (2 + Tp) ≤ Real.log (T + 3) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    linarith
  have htan : ‖Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤ 4 := by
    refine Commons.Analysis.SpecialFunctions.Trigonometric.tan_norm_le_of_abs_im_ge _ ?_
    have h1 : (↑Real.pi * (1 - s) / 2).im = -(Real.pi * Tp / 2) := by simp [hs]; ring
    rw [h1, abs_neg, abs_of_nonneg (by positivity)]
    have : (1 : ℝ) ≤ Real.pi * Tp / 2 := by
      have hπ : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
      nlinarith
    linarith
  have hlog2π : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ ≤ 7 := by
    rw [show Complex.log ((2 * Real.pi : ℝ) : ℂ) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) by
      rw [Complex.ofReal_log (le_of_lt (by positivity : (0 : ℝ) < 2 * Real.pi))]]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have h1 : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.pi < 4 := Real.pi_lt_four
    linarith
  have hπ2 : ‖((Real.pi / 2 : ℝ) : ℂ)‖ = Real.pi / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have htan2 : ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤ 8 := by
    rw [norm_mul, hπ2]
    have h1 : Real.pi / 2 * ‖Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤ Real.pi / 2 * 4 :=
      mul_le_mul_of_nonneg_left htan (by positivity)
    have h2 : Real.pi / 2 * 4 = 2 * Real.pi := by ring
    rw [h2] at h1
    have h3 : 2 * Real.pi ≤ 8 := by have := Real.pi_lt_four; linarith
    linarith
  have hconj : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ C₁ * L ^ 3 * Dinv := by
    have heq : deriv riemannZeta (1 - s) / riemannZeta (1 - s) =
        conj (deriv riemannZeta u / riemannZeta u) := by
      rw [hw]; exact logDeriv_conj_zeta u
    rw [heq, Complex.norm_conj]
    have hres := h₁ T Tp δ hT hTTp hTp1 hδ0 hδ4 hball (1 - σ) (by linarith) (by linarith)
    have hres' : ‖deriv riemannZeta u / riemannZeta u‖ ≤
        C₁ * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ := by simpa [hu] using hres
    simpa only [hLdef, hDdef] using hres'
  have hbig : ‖deriv riemannZeta s / riemannZeta s‖ ≤ (C₁ + 18) * L ^ 3 * Dinv := by
    have hterm : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤ 17 + L := by
      have hb1 : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s)‖ ≤ 7 + (L + 2) :=
        le_trans (norm_sub_le _ _) (add_le_add hlog2π hdig)
      calc ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖
          ≤ ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s)‖ +
            ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ := norm_add_le _ _
        _ ≤ (7 + (L + 2)) + 8 := add_le_add hb1 htan2
        _ = 17 + L := by ring
    have h17 : (17 : ℝ) ≤ 17 * (L ^ 3 * Dinv) := le_mul_of_one_le_right (by norm_num) hA1
    rw [hFE]
    calc ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
          ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2) -
          deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖
        ≤ ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
          ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := norm_sub_le _ _
      _ ≤ (17 + L) + C₁ * L ^ 3 * Dinv := add_le_add hterm hconj
      _ ≤ (C₁ + 18) * L ^ 3 * Dinv := by nlinarith [hLA, h17, hC₁, hApos]
  have hz1 : riemannZeta₁ s ≠ 0 := by
    have hfac2 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
      have hh := riemannZeta_eq_inv_sub_mul hs1
      rw [hh]
      field_simp [sub_ne_zero.mpr hs1]
    rw [hfac2]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hζs
  have hinv1 : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    refine inv_le_one_of_one_le₀ ?_
    have him : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
    have h2 : (s - 1).im = Tp := by simp [hs]
    rw [h2, abs_of_pos hTp0] at him
    linarith
  have hlogd : ‖logDeriv riemannZeta₁ s‖ ≤ (C₁ + 19) * L ^ 3 * Dinv := by
    rw [logDeriv_zeta1_eq hs1 hz1]
    have htri : ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖ ≤
        ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := norm_add_le _ _
    have hb : (C₁ + 18) * L ^ 3 * Dinv + 1 ≤ (C₁ + 19) * L ^ 3 * Dinv := by
      rw [show (C₁ + 19) * L ^ 3 * Dinv = (C₁ + 18) * L ^ 3 * Dinv + L ^ 3 * Dinv by ring]
      linarith [hA1]
    linarith [htri, hbig, hinv1, hb]
  have hsum : ‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖ ≤ (C₁ + 20) * L ^ 3 * Dinv := by
    have hinv2 : (1 : ℝ) / ‖s - 1‖ ≤ 1 := by simpa [one_div] using hinv1
    have hb : (C₁ + 19) * L ^ 3 * Dinv + 1 ≤ (C₁ + 20) * L ^ 3 * Dinv := by
      rw [show (C₁ + 20) * L ^ 3 * Dinv = (C₁ + 19) * L ^ 3 * Dinv + L ^ 3 * Dinv by ring]
      linarith [hA1]
    linarith [hlogd, hinv2, hb]
  have hnorm := psiIntF1_norm_le_logDeriv hx0 s
  have hdiv : (x : ℝ) ^ s.re / ‖s‖ ≤ (x : ℝ) ^ (1 / 2 : ℝ) / Tp := by
    have hnum : (x : ℝ) ^ s.re ≤ (x : ℝ) ^ (1 / 2 : ℝ) := by
      rw [hsre]
      exact Real.rpow_le_rpow_of_exponent_le hx hσ2
    have hden : Tp ≤ ‖s‖ := by
      have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      rw [hsim, abs_of_pos hTp0] at him
      exact him
    exact div_le_div₀ (Real.rpow_nonneg (le_of_lt hx0) _) hnum hTp0 hden
  have hbpos : (0 : ℝ) ≤ (C₁ + 20) * L ^ 3 * Dinv := by positivity
  calc ‖psiIntF1 x s‖
      ≤ (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) * ((x : ℝ) ^ s.re / ‖s‖) := hnorm
    _ ≤ (C₁ + 20) * L ^ 3 * Dinv * ((x : ℝ) ^ (1 / 2 : ℝ) / Tp) :=
        mul_le_mul hsum hdiv (by positivity) hbpos

/-- Integral bound for the piece `σ ∈ [1/4, 5/8]` of a horizontal edge at height `Tp`. -/
theorem psiIntF1_horiz_mid_pointwise (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T Tp δ : ℝ, 1 ≤ x → 5 ≤ T → T ≤ Tp → Tp ≤ T + 1 →
      0 < δ → δ ≤ 1 / 4 →
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (Tp : ℂ))‖ < (3 / 2 : ℝ) + δ ^ 2 / 4 →
        riemannZeta₁ w ≠ 0) →
      ∀ σ : ℝ, (1 / 4 : ℝ) ≤ σ → σ ≤ (5 / 8 : ℝ) →
        ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤
          C * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ *
            ((x : ℝ) ^ (5 / 8 : ℝ) / Tp) := by
  rcases psiIntF1_horiz_left_pointwise h with ⟨C₁, hC₁, h₁⟩
  rcases zeta1_mid_pointwise h with ⟨C₂, hC₂, h₂⟩
  refine ⟨17 * C₁ + 16 * C₂ + 1, by positivity, ?_⟩
  intro x T Tp δ hx hT hTTp hTp1 hδ0 hδ4 hball σ hσ1 hσ2
  set L : ℝ := Real.log (T + 3) + 1 with hLdef
  set Dinv : ℝ := (δ ^ 4)⁻¹ with hDdef
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hTp5 : 5 ≤ Tp := le_trans hT hTTp
  have hTp0 : 0 < Tp := by linarith
  have hTpne : Tp ≠ 0 := ne_of_gt hTp0
  have hδ4pos : 0 < δ ^ 4 := by positivity
  have hδ4le1 : δ ^ 4 ≤ 1 := by
    have hh := pow_le_pow_left₀ (le_of_lt hδ0) hδ4 4
    norm_num at hh
    linarith
  have hDinv1 : (1 : ℝ) ≤ Dinv := by
    rw [hDdef]; exact (one_le_inv₀ hδ4pos).mpr hδ4le1
  have hDinvpos : (0 : ℝ) < Dinv := by rw [hDdef]; positivity
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h2 : (0 : ℝ) ≤ Real.log (T + 3) := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ T + 3)
      simpa using this
    linarith
  have hL3ge1 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
  have hL3pos : (0 : ℝ) < L ^ 3 := by linarith
  have hL3le : L ≤ L ^ 3 := by
    simpa using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 3)
  have hA1 : (1 : ℝ) ≤ L ^ 3 * Dinv := by
    have hh := mul_le_mul hL3ge1 hDinv1 (by norm_num) (le_of_lt hL3pos)
    simpa using hh
  have hApos : (0 : ℝ) < L ^ 3 * Dinv := by linarith
  have h23 : (0 : ℝ) < δ ^ 2 / 4 := by positivity
  have hxle : (x : ℝ) ^ (1 / 2 : ℝ) ≤ (x : ℝ) ^ (5 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hxle2 : (x : ℝ) ^ σ ≤ (x : ℝ) ^ (5 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx hσ2
  have hX0 : (0 : ℝ) ≤ (x : ℝ) ^ (5 / 8 : ℝ) / Tp :=
    div_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (le_of_lt hTp0)
  by_cases hσh : σ ≤ 1 / 2
  · have hp := h₁ x T Tp δ hx hT hTTp hTp1 hδ0 hδ4 hball σ hσ1 hσh
    have hp' : ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤
        C₁ * L ^ 3 * Dinv * ((x : ℝ) ^ (1 / 2 : ℝ) / Tp) := by
      simpa only [hLdef, hDdef] using hp
    have h1 : C₁ * L ^ 3 * Dinv * ((x : ℝ) ^ (1 / 2 : ℝ) / Tp) ≤
        (17 * C₁ + 16 * C₂ + 1) * L ^ 3 * Dinv * ((x : ℝ) ^ (5 / 8 : ℝ) / Tp) := by
      have hle : C₁ ≤ 17 * C₁ + 16 * C₂ + 1 := by linarith [hC₂]
      have hA : (0 : ℝ) ≤ L ^ 3 * Dinv := le_of_lt hApos
      calc C₁ * L ^ 3 * Dinv * ((x : ℝ) ^ (1 / 2 : ℝ) / Tp)
          = C₁ * (L ^ 3 * Dinv) * ((x : ℝ) ^ (1 / 2 : ℝ) / Tp) := by ring
        _ ≤ (17 * C₁ + 16 * C₂ + 1) * (L ^ 3 * Dinv) * ((x : ℝ) ^ (1 / 2 : ℝ) / Tp) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hle hA) (by positivity)
        _ ≤ (17 * C₁ + 16 * C₂ + 1) * (L ^ 3 * Dinv) * ((x : ℝ) ^ (5 / 8 : ℝ) / Tp) := by
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hxle (le_of_lt hTp0)) (by positivity)
        _ = (17 * C₁ + 16 * C₂ + 1) * L ^ 3 * Dinv * ((x : ℝ) ^ (5 / 8 : ℝ) / Tp) := by ring
    linarith [hp']
  · push_neg at hσh
    have hσ1' : (1 / 2 : ℝ) ≤ σ := le_of_lt hσh
    have hs := h₂ T Tp δ hT hTTp hTp1 hδ0 hδ4 hball σ hσ1' hσ2
    set s : ℂ := (σ : ℂ) + Complex.I * (Tp : ℂ) with hsdef
    have hsre : s.re = σ := by simp [hsdef]
    have hsim : s.im = Tp := by simp [hsdef]
    have hDge : δ ^ 2 / 4 ≤ σ - 1 / 2 + δ ^ 2 / 4 := by linarith
    have hDpos : 0 < σ - 1 / 2 + δ ^ 2 / 4 := lt_of_lt_of_le h23 hDge
    have hinv : ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2)⁻¹ ≤ 16 * Dinv := by
      have h2 : δ ^ 4 / 16 ≤ (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 := by
        have h3 : (δ ^ 2 / 4) ^ 2 ≤ (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hDge 2
        have h4 : (δ ^ 2 / 4) ^ 2 = δ ^ 4 / 16 := by ring
        rw [h4] at h3
        exact h3
      have h := (inv_le_inv₀ (pow_pos hDpos 2) (by positivity : (0 : ℝ) < δ ^ 4 / 16)).mpr h2
      rw [show (δ ^ 4 / 16)⁻¹ = 16 * (δ ^ 4)⁻¹ by field_simp] at h
      simpa [hDdef] using h
    have hs1 : s ≠ 1 := by
      intro hh
      have h2 := congrArg Complex.im hh
      simp [hsim] at h2
      linarith
    have hz : riemannZeta s ≠ 0 := by
      by_cases hσh' : σ = 1 / 2
      · exact riemannZeta_ne_zero_of_half_ball hTpne hδ0 hball (by rw [hsre]; exact hσh')
          (by rw [hsim])
      · exact zeta_ne_zero_of_rh_gt_half h (by rw [hsre]; linarith)
    have hz1 : riemannZeta₁ s ≠ 0 := by
      have hfac2 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
        have hh := riemannZeta_eq_inv_sub_mul hs1
        rw [hh]
        field_simp [sub_ne_zero.mpr hs1]
      rw [hfac2]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) hz
    have hnorm := psiIntF1_norm_le_logDeriv hx0 s
    have hdiv : (x : ℝ) ^ s.re / ‖s‖ ≤ (x : ℝ) ^ (5 / 8 : ℝ) / Tp := by
      have hnum : (x : ℝ) ^ s.re ≤ (x : ℝ) ^ (5 / 8 : ℝ) := by
        rw [hsre]
        exact hxle2
      have hden : Tp ≤ ‖s‖ := by
        have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
        rw [hsim, abs_of_pos hTp0] at him
        exact him
      exact div_le_div₀ (Real.rpow_nonneg (le_of_lt hx0) _) hnum hTp0 hden
    have hinv1 : ‖(s - 1)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      refine inv_le_one_of_one_le₀ ?_
      have him : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
      have h2 : (s - 1).im = Tp := by simp [hsdef]
      rw [h2, abs_of_pos hTp0] at him
      linarith
    have hld : ‖logDeriv riemannZeta₁ s‖ ≤ 16 * C₂ * L ^ 3 * Dinv := by
      have h1 : ‖logDeriv riemannZeta₁ s‖ ≤ C₂ * (Real.log (T + 3) + 1) *
          ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2)⁻¹ := by
        rw [hsdef]
        simpa only [div_eq_mul_inv] using hs
      have h2 : C₂ * (Real.log (T + 3) + 1) * ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2)⁻¹ ≤
          C₂ * L ^ 3 * (16 * Dinv) := by
        have h3 : C₂ * (Real.log (T + 3) + 1) ≤ C₂ * L ^ 3 := by
          rw [hLdef]
          exact mul_le_mul_of_nonneg_left hL3le (le_of_lt hC₂)
        calc C₂ * (Real.log (T + 3) + 1) * ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2)⁻¹
            ≤ C₂ * (Real.log (T + 3) + 1) * (16 * Dinv) :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
          _ ≤ C₂ * L ^ 3 * (16 * Dinv) :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
      have h5 : C₂ * L ^ 3 * (16 * Dinv) = 16 * C₂ * L ^ 3 * Dinv := by ring
      rw [h5] at h2
      linarith [h1, h2]
    have hsum : ‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖ ≤ (16 * C₂ + 1) * L ^ 3 * Dinv := by
      have hinv2 : (1 : ℝ) / ‖s - 1‖ ≤ 1 := by simpa [one_div] using hinv1
      have hge : 16 * C₂ * L ^ 3 * Dinv ≤ (16 * C₂ + 1) * L ^ 3 * Dinv := by
        have h1 : (16 * C₂ : ℝ) * (L ^ 3 * Dinv) ≤ (16 * C₂ + 1) * (L ^ 3 * Dinv) :=
          mul_le_mul_of_nonneg_right (by linarith : (16 * C₂ : ℝ) ≤ 16 * C₂ + 1)
            (le_of_lt hApos)
        nlinarith [h1]
      have hge1 : (1 : ℝ) ≤ (16 * C₂ + 1) * L ^ 3 * Dinv := by
        have h1 : (1 : ℝ) * (L ^ 3 * Dinv) ≤ (16 * C₂ + 1) * (L ^ 3 * Dinv) :=
          mul_le_mul_of_nonneg_right (by linarith [hC₂] : (1 : ℝ) ≤ 16 * C₂ + 1)
            (le_of_lt hApos)
        nlinarith [h1]
      linarith [hld, hinv2, hge, hge1]
    have hbpos : (0 : ℝ) ≤ (16 * C₂ + 1) * L ^ 3 * Dinv := by
      have h1 : (0 : ℝ) ≤ (16 * C₂ + 1) * L ^ 3 := by positivity
      exact mul_nonneg h1 (le_of_lt hDinvpos)
    calc ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖
        ≤ (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) * ((x : ℝ) ^ s.re / ‖s‖) := by
          simpa [hsdef] using hnorm
      _ ≤ (16 * C₂ + 1) * L ^ 3 * Dinv * ((x : ℝ) ^ (5 / 8 : ℝ) / Tp) :=
          mul_le_mul hsum hdiv (by positivity) hbpos
      _ ≤ (17 * C₁ + 16 * C₂ + 1) * L ^ 3 * Dinv * ((x : ℝ) ^ (5 / 8 : ℝ) / Tp) := by
          have hle : 16 * C₂ + 1 ≤ 17 * C₁ + 16 * C₂ + 1 := by linarith [hC₁]
          have hstep : (16 * C₂ + 1) * L ^ 3 * Dinv ≤
              (17 * C₁ + 16 * C₂ + 1) * L ^ 3 * Dinv :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hle (le_of_lt hL3pos)) (le_of_lt hDinvpos)
          exact mul_le_mul_of_nonneg_right hstep
            (div_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (le_of_lt hTp0))
/-- Integral bound for the piece `σ ∈ [1/4, 5/8]` of a horizontal edge. -/
theorem edge_horiz_left_mid_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T Tp δ : ℝ, 1 ≤ x → 5 ≤ T → T ≤ Tp → Tp ≤ T + 1 →
      0 < δ → δ ≤ 1 / 4 →
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (Tp : ℂ))‖ < (3 / 2 : ℝ) + δ ^ 2 / 4 →
        riemannZeta₁ w ≠ 0) →
      ‖∫ σ in (1 / 4)..(5 / 8), psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤
        C * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ * ((x : ℝ) ^ (5 / 8 : ℝ) / Tp) := by
  rcases psiIntF1_horiz_mid_pointwise h with ⟨C, hC, hCb⟩
  refine ⟨C, hC, ?_⟩
  intro x T Tp δ hx hT hTTp hTp1 hδ0 hδ4 hball
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hTp0 : 0 < Tp := by linarith
  have hpt : ∀ σ : ℝ, σ ∈ Set.uIoc (1 / 4) (5 / 8) →
      ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤
        C * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ * ((x : ℝ) ^ (5 / 8 : ℝ) / Tp) := by
    intro σ hσ
    rw [Set.uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 5 / 8)] at hσ
    exact hCb x T Tp δ hx hT hTTp hTp1 hδ0 hδ4 hball σ (le_of_lt hσ.1) hσ.2
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 4 : ℝ)) (b := (5 / 8 : ℝ))
    (C := C * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ * ((x : ℝ) ^ (5 / 8 : ℝ) / Tp)) hpt
  have hlen2 : |(5 / 8 : ℝ) - 1 / 4| = 3 / 8 := by norm_num
  rw [hlen2] at hint
  have hpos : (0 : ℝ) ≤ C * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ := by
    have h4 : (0 : ℝ) < δ ^ 4 := by positivity
    have hL0 : (0 : ℝ) ≤ Real.log (T + 3) + 1 := by
      have h2 : (0 : ℝ) ≤ Real.log (T + 3) := by
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ T + 3)
        simpa using this
      linarith
    exact mul_nonneg (mul_nonneg (le_of_lt hC) (pow_nonneg hL0 3)) (inv_nonneg.mpr (le_of_lt h4))
  calc ‖∫ σ in (1 / 4)..(5 / 8), psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖
      ≤ C * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ * ((x : ℝ) ^ (5 / 8 : ℝ) / Tp) * (3 / 8) :=
        hint
    _ ≤ C * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ * ((x : ℝ) ^ (5 / 8 : ℝ) / Tp) * 1 :=
        mul_le_mul_of_nonneg_left (by norm_num)
          (mul_nonneg hpos (div_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (le_of_lt hTp0)))
    _ = C * (Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ * ((x : ℝ) ^ (5 / 8 : ℝ) / Tp) := by ring


/-- `(x : ℂ) ^ (conj s) = conj ((x : ℂ) ^ s)` for `x > 0`. -/
lemma cpow_conj_ofReal {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (conj s) = conj ((x : ℂ) ^ s) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hx0,
    ← Complex.ofReal_log (le_of_lt hx)]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal]

/-- conjugation symmetry of the Perron integrand `psiIntF1`. -/
lemma psiIntF1_conj {x : ℝ} (hx : 0 < x) (s : ℂ) :
    psiIntF1 x (conj s) = conj (psiIntF1 x s) := by
  have hlog : logDeriv riemannZeta₁ (conj s) = conj (logDeriv riemannZeta₁ s) :=
    logDeriv_riemannZeta₁_conj s
  have hpow : (x : ℂ) ^ (conj s) = conj ((x : ℂ) ^ s) := cpow_conj_ofReal hx s
  unfold psiIntF1
  simp only [psiIntF1, hlog, hpow, map_add, map_mul, map_neg, map_sub, map_one, map_div₀,
    Complex.conj_conj] <;> ring

/-- the bottom horizontal edge integral is the conjugate of the top one. -/
lemma edgeB_eq_conj_edgeT {x : ℝ} (hx : 0 < x) (a b Tp : ℝ) :
    edgeB a b Tp (psiIntF1 x) = conj (edgeT a b Tp (psiIntF1 x)) := by
  unfold edgeB edgeT
  rw [zRect_im, wRect_im]
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro t ht
  change psiIntF1 x ((t : ℂ) + ((-Tp : ℝ) : ℂ) * Complex.I) =
    conj (psiIntF1 x ((t : ℂ) + (Tp : ℂ) * Complex.I))
  have h1 : (t : ℂ) + ((-Tp : ℝ) : ℂ) * Complex.I =
      conj ((t : ℂ) + (Tp : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp
  rw [h1, psiIntF1_conj hx]

/-- **Top horizontal edge bound** (P5): the integral of `psiIntF1 x` along the horizontal
segment `Im = Tp`, `Re ∈ [a,b]` with `1/4 ≤ a ≤ 3/8`, `5/8 ≤ b ≤ 2`.

Two regimes: on `[a,5/8]` the middle-strip bound gives the factor `(log T)^3/δ^4` but with
weight `x^{5/8}`; on `[5/8,b]` the classical RH bound `ζ'/ζ = O(log²t)`
(`zeta_logDeriv_right_logsq`) gives weight `x^b` with only a `(log T)^2` factor. -/
theorem edgeT_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x a b T Tp δ : ℝ, 1 ≤ x → (1 / 4 : ℝ) ≤ a → a ≤ (3 / 8 : ℝ) →
      (5 / 8 : ℝ) ≤ b → b ≤ 2 → 5 ≤ T → T ≤ Tp → Tp ≤ T + 1 → 0 < δ → δ ≤ 1 / 4 →
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (Tp : ℂ))‖ < (3 / 2 : ℝ) + δ ^ 2 / 4 →
        riemannZeta₁ w ≠ 0) →
      ‖edgeT a b Tp (psiIntF1 x)‖ ≤
        C * ((Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ * ((x : ℝ) ^ (5 / 8 : ℝ)) +
              (Real.log (T + 3) + 1) ^ 2 * ((x : ℝ) ^ b)) / Tp := by
  rcases psiIntF1_horiz_mid_pointwise h with ⟨C₁, hC₁, h₁⟩
  rcases zeta_logDeriv_right_logsq h with ⟨CR, hCR, hR⟩
  refine ⟨2 * (C₁ + 4 * (CR + 2) + 1), by positivity, ?_⟩
  intro x a b T Tp δ hx ha1 ha2 hb1 hb2 hT hTTp hTp1 hδ0 hδ4 hball
  set L : ℝ := Real.log (T + 3) + 1 with hLdef
  set Dinv : ℝ := (δ ^ 4)⁻¹ with hDdef
  set A1 : ℝ := L ^ 3 * Dinv * ((x : ℝ) ^ (5 / 8 : ℝ)) with hA1def
  set B1 : ℝ := L ^ 2 * ((x : ℝ) ^ b) with hB1def
  set XC : ℝ := C₁ * A1 + 4 * (CR + 2) * B1 with hXCdef
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hTp5 : 5 ≤ Tp := le_trans hT hTTp
  have hTp0 : 0 < Tp := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h2 : (0 : ℝ) ≤ Real.log (T + 3) := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ T + 3)
      simpa using this
    linarith
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
  have hδ4pos : 0 < δ ^ 4 := by positivity
  have hDinv0 : (0 : ℝ) ≤ Dinv := by rw [hDdef]; exact inv_nonneg.mpr (le_of_lt hδ4pos)
  have hA1nn : (0 : ℝ) ≤ A1 := by
    rw [hA1def]; exact mul_nonneg (mul_nonneg (pow_nonneg hL0 3) hDinv0)
      (Real.rpow_nonneg (le_of_lt hx0) _)
  have hB1nn : (0 : ℝ) ≤ B1 := by
    rw [hB1def]
    exact mul_nonneg (pow_nonneg hL0 2) (Real.rpow_nonneg (le_of_lt hx0) _)
  have hK0 : (0 : ℝ) ≤ C₁ + 4 * (CR + 2) + 1 := by linarith
  have hXC0 : (0 : ℝ) ≤ XC := by
    rw [hXCdef]
    have h2 : (0 : ℝ) ≤ 4 * (CR + 2) * B1 := mul_nonneg (by linarith) hB1nn
    linarith [mul_nonneg (le_of_lt hC₁) hA1nn, h2]
  have hab : a ≤ b := by linarith
  have hEdge : edgeT a b Tp (psiIntF1 x) =
      ∫ σ in a..b, psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ)) := by
    rw [edgeT, wRect_im]
    apply intervalIntegral.integral_congr
    intro σ hσ
    change psiIntF1 x ((σ : ℂ) + (Tp : ℂ) * Complex.I) =
      psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))
    rw [show (σ : ℂ) + (Tp : ℂ) * Complex.I = (σ : ℂ) + Complex.I * (Tp : ℂ) by rw [mul_comm]]
  rw [hEdge]
  have hre : ∀ σ : ℝ, (((σ : ℂ) + Complex.I * (Tp : ℂ)) : ℂ).re = σ := fun σ => by simp
  have him : ∀ σ : ℝ, (((σ : ℂ) + Complex.I * (Tp : ℂ)) : ℂ).im = Tp := fun σ => by simp
  have hpt : ∀ σ : ℝ, σ ∈ Set.uIoc a b →
      ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤ XC / Tp := by
    intro σ hσ
    rw [Set.uIoc_of_le hab] at hσ
    have hσ1 : (1 / 4 : ℝ) ≤ σ := le_of_lt (lt_of_le_of_lt ha1 hσ.1)
    have hσ2 : σ ≤ 2 := le_trans hσ.2 hb2
    have hxle : (x : ℝ) ^ σ ≤ (x : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_le hx hσ.2
    by_cases hσm : σ ≤ 5 / 8
    · have hp := h₁ x T Tp δ hx hT hTTp hTp1 hδ0 hδ4 hball σ hσ1 hσm
      have hp' : ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤ C₁ * A1 / Tp := by
        have hh := hp
        rw [← hLdef, ← hDdef] at hh
        rw [show C₁ * A1 / Tp = C₁ * L ^ 3 * Dinv * (((x : ℝ) ^ (5 / 8 : ℝ)) / Tp) by
          rw [hA1def]; ring]
        exact hh
      have hle : C₁ * A1 / Tp ≤ XC / Tp := by
        rw [hXCdef]
        apply div_le_div_of_nonneg_right _ (le_of_lt hTp0)
        have h2 : (0 : ℝ) ≤ 4 * (CR + 2) * B1 := mul_nonneg (by linarith) hB1nn
        linarith
      linarith [hp', hle]
    · push_neg at hσm
      have hσm' : (5 / 8 : ℝ) ≤ σ := le_of_lt hσm
      have hz : riemannZeta ((σ : ℂ) + Complex.I * (Tp : ℂ)) ≠ 0 := by
        intro hzs
        have htriv : ¬∃ n : ℕ, ((σ : ℂ) + Complex.I * (Tp : ℂ)) = -2 * (n + 1) := by
          rintro ⟨n, hnn⟩
          have h2 := congrArg Complex.im hnn
          rw [him σ] at h2
          simp at h2
          linarith
        have hs1 : ((σ : ℂ) + Complex.I * (Tp : ℂ)) ≠ 1 := by
          intro hh
          have h2 := congrArg Complex.im hh
          rw [him σ] at h2
          simp at h2
          linarith
        have hhalf : (((σ : ℂ) + Complex.I * (Tp : ℂ))).re = 1 / 2 := h _ hzs htriv hs1
        rw [hre σ] at hhalf
        linarith
      have hs1 : ((σ : ℂ) + Complex.I * (Tp : ℂ)) ≠ 1 := by
        intro hh
        have h2 := congrArg Complex.im hh
        rw [him σ] at h2
        simp at h2
        linarith
      have hfac2 : riemannZeta₁ ((σ : ℂ) + Complex.I * (Tp : ℂ)) =
          (((σ : ℂ) + Complex.I * (Tp : ℂ)) - 1) * riemannZeta ((σ : ℂ) + Complex.I * (Tp : ℂ)) := by
        have hh := riemannZeta_eq_inv_sub_mul hs1
        rw [hh]
        field_simp [sub_ne_zero.mpr hs1]
      have hz1 : riemannZeta₁ ((σ : ℂ) + Complex.I * (Tp : ℂ)) ≠ 0 := by
        rw [hfac2]
        exact mul_ne_zero (sub_ne_zero.mpr hs1) hz
      have hkey := hR σ Tp hσm' hσ2 (by rw [abs_of_pos hTp0]; linarith)
      have hinv1 : ‖(((σ : ℂ) + Complex.I * (Tp : ℂ)) - 1)⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        refine inv_le_one_of_one_le₀ ?_
        have h5 := Complex.abs_im_le_norm (((σ : ℂ) + Complex.I * (Tp : ℂ)) - 1)
        have h6 : (((σ : ℂ) + Complex.I * (Tp : ℂ)) - 1).im = Tp := by simp
        rw [h6, abs_of_pos hTp0] at h5
        linarith
      have hlogd : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤
          (CR + 2) * L ^ 2 := by
        rw [logDeriv_zeta1_eq hs1 hz1]
        have h3 := norm_add_le (deriv riemannZeta ((σ : ℂ) + Complex.I * (Tp : ℂ)) /
            riemannZeta ((σ : ℂ) + Complex.I * (Tp : ℂ)))
          (((σ : ℂ) + Complex.I * (Tp : ℂ)) - 1)⁻¹
        have h2 : CR * (Real.log (|Tp| + 3)) ^ 2 + 1 ≤ (CR + 2) * L ^ 2 := by
          rw [abs_of_pos hTp0]
          have hlog : Real.log (Tp + 3) ≤ L := by
            rw [hLdef]
            have h1 : Tp + 3 ≤ 2 * (T + 3) := by linarith
            have h2 : Real.log (Tp + 3) ≤ Real.log (2 * (T + 3)) :=
              Real.log_le_log (by linarith) h1
            rw [Real.log_mul (by norm_num) (by linarith)] at h2
            have h3 : Real.log 2 ≤ 1 := by
              have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
              linarith
            linarith
          have hlog0 : (0 : ℝ) ≤ Real.log (Tp + 3) := Real.log_nonneg (by linarith)
          have hsq : (Real.log (Tp + 3)) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
          have hCR0 : (0 : ℝ) ≤ CR := le_of_lt hCR
          nlinarith [hsq, hL1, hL0, hCR0]
        linarith [h3, hkey, hinv1, h2]
      have hden : Tp ≤ ‖((σ : ℂ) + Complex.I * (Tp : ℂ))‖ := by
        have h5 := Complex.abs_im_le_norm (((σ : ℂ) + Complex.I * (Tp : ℂ)) : ℂ)
        rw [him σ, abs_of_pos hTp0] at h5
        exact h5
      have hdiv : (x : ℝ) ^ σ / ‖((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤ (x : ℝ) ^ b / Tp :=
        div_le_div₀ (Real.rpow_nonneg (le_of_lt hx0) _) hxle hTp0 hden
      have hn := psiIntF1_norm_le_logDeriv hx0 ((σ : ℂ) + Complex.I * (Tp : ℂ))
      rw [hre σ] at hn
      have hinv2 : (1 : ℝ) / ‖((σ : ℂ) + Complex.I * (Tp : ℂ)) - 1‖ ≤ 1 := by
        simpa [one_div] using hinv1
      have h1 : ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤
          ((CR + 2) * L ^ 2 + 1) * ((x : ℝ) ^ σ / ‖((σ : ℂ) + Complex.I * (Tp : ℂ))‖) := by
        have hsum : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ +
            1 / ‖((σ : ℂ) + Complex.I * (Tp : ℂ)) - 1‖ ≤ (CR + 2) * L ^ 2 + 1 := by
          linarith [hlogd, hinv2]
        calc ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖
            ≤ (‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ +
                1 / ‖((σ : ℂ) + Complex.I * (Tp : ℂ)) - 1‖) *
                ((x : ℝ) ^ σ / ‖((σ : ℂ) + Complex.I * (Tp : ℂ))‖) := hn
          _ ≤ ((CR + 2) * L ^ 2 + 1) *
                ((x : ℝ) ^ σ / ‖((σ : ℂ) + Complex.I * (Tp : ℂ))‖) :=
              mul_le_mul_of_nonneg_right hsum (by positivity)
      have hp' : ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤ 4 * (CR + 2) * B1 / Tp := by
        rw [hB1def]
        have h5 : (CR + 2) * L ^ 2 + 1 ≤ 4 * (CR + 2) * L ^ 2 := by nlinarith [hCR, hL1]
        calc ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖
            ≤ ((CR + 2) * L ^ 2 + 1) * ((x : ℝ) ^ σ / ‖((σ : ℂ) + Complex.I * (Tp : ℂ))‖) := h1
          _ ≤ ((CR + 2) * L ^ 2 + 1) * ((x : ℝ) ^ b / Tp) :=
              mul_le_mul_of_nonneg_left hdiv (by positivity)
          _ ≤ 4 * (CR + 2) * L ^ 2 * ((x : ℝ) ^ b / Tp) :=
              mul_le_mul_of_nonneg_right h5 (by positivity)
          _ = 4 * (CR + 2) * (L ^ 2 * ((x : ℝ) ^ b)) / Tp := by ring
      have hle : 4 * (CR + 2) * B1 / Tp ≤ XC / Tp := by
        rw [hXCdef]
        apply div_le_div_of_nonneg_right _ (le_of_lt hTp0)
        have h2 : (0 : ℝ) ≤ C₁ * A1 := mul_nonneg (le_of_lt hC₁) hA1nn
        linarith
      linarith [hp', hle]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (C := XC / Tp) hpt
  have hlen : |b - a| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hC0 : (0 : ℝ) ≤ XC / Tp := div_nonneg hXC0 (le_of_lt hTp0)
  have hfin : 2 * XC ≤ 2 * (C₁ + 4 * (CR + 2) + 1) * (A1 + B1) := by
    have hAB : (0 : ℝ) ≤ A1 + B1 := by linarith
    have h1 : C₁ * A1 + 4 * (CR + 2) * B1 ≤ (C₁ + 4 * (CR + 2)) * (A1 + B1) := by
      have e1 : C₁ * A1 ≤ C₁ * (A1 + B1) := mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hC₁)
      have e2 : 4 * (CR + 2) * B1 ≤ 4 * (CR + 2) * (A1 + B1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith [hCR])
      have e3 : C₁ * (A1 + B1) + 4 * (CR + 2) * (A1 + B1) =
          (C₁ + 4 * (CR + 2)) * (A1 + B1) := by ring
      linarith [e1, e2, e3]
    have h2 : (C₁ + 4 * (CR + 2)) * (A1 + B1) ≤ (C₁ + 4 * (CR + 2) + 1) * (A1 + B1) :=
      mul_le_mul_of_nonneg_right (by linarith) hAB
    rw [hXCdef]
    linarith [h1, h2]
  calc ‖∫ σ in a..b, psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤ XC / Tp * |b - a| := hint
    _ ≤ XC / Tp * 2 := mul_le_mul_of_nonneg_left hlen hC0
    _ = 2 * XC / Tp := by ring
    _ ≤ 2 * (C₁ + 4 * (CR + 2) + 1) * (A1 + B1) / Tp :=
        div_le_div_of_nonneg_right hfin (le_of_lt hTp0)
    _ = 2 * (C₁ + 4 * (CR + 2) + 1) *
          ((Real.log (T + 3) + 1) ^ 3 * (δ ^ 4)⁻¹ * ((x : ℝ) ^ (5 / 8 : ℝ)) +
            (Real.log (T + 3) + 1) ^ 2 * ((x : ℝ) ^ b)) / Tp := by
        rw [hA1def, hB1def, hLdef, hDdef]


end Commons.NumberTheory.Zeta
end


-- ==== begin p3_edgeBounds2 ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# Improved side bounds for the far-left contour (`Re = -1/2`)

The efficiency of the sharp Mertens estimate (and hence the size of the finite CA table in the
Robin endgame) is governed by the *left* vertical edge of the Perron contour: with the edge at
`Re = 1/4` the contour contributes `x^{1/4} log^4 T`, which is far too large; with the edge
pushed to `Re = -1/2` it contributes only `x^{-1/2} log^4 T`.

This module provides the two pointwise/integral bounds for the far-left region
`Re ∈ [-1/2, 1/8]`, using the commons far-left log-derivative estimate
`zeta_logDeriv_left_far_strip_bound`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Zeta

/-- Pointwise bound of the Perron integrand on the far-left strip `Re ∈ [-1/2, 1/8]`,
`|Im| ≥ 5`: it is `O(log^3 T · x^{1/8} / T)`. -/
theorem psiIntF1_farleft_pointwise (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T Tp : ℝ, 1 ≤ x → 5 ≤ T → T ≤ Tp → Tp ≤ T + 1 →
      ∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ (1 / 8 : ℝ) →
        ‖psiIntF1 x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤
          C * (Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / Tp) := by
  rcases zeta_logDeriv_left_far_strip_bound h with ⟨C₁, hC₁, h₁⟩
  refine ⟨8 * C₁ + 1, by positivity, ?_⟩
  intro x T Tp hx hT hTTp hTp1 σ hσlo hσhi
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hTp5 : 5 ≤ Tp := le_trans hT hTTp
  have hTp0 : 0 < Tp := by linarith
  set s : ℂ := (σ : ℂ) + Complex.I * (Tp : ℂ) with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = Tp := by simp [hs]
  have hTs : |s.im| = Tp := by rw [hsim, abs_of_pos hTp0]
  have hlog1 : (0 : ℝ) ≤ Real.log (Tp + 3) := Real.log_nonneg (by linarith)
  have hLmono : (Real.log (Tp + 3) + 1) ^ 3 ≤ (2 * (Real.log (T + 3) + 1)) ^ 3 := by
    apply pow_le_pow_left₀ (by linarith)
    have h1 : Real.log (Tp + 3) + 1 ≤ Real.log (2 * (T + 3)) + 1 := by
      have h2 : Real.log (Tp + 3) ≤ Real.log (2 * (T + 3)) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    have h3 : Real.log (2 * (T + 3)) = Real.log 2 + Real.log (T + 3) :=
      Real.log_mul (by norm_num) (by linarith)
    have h4 : Real.log 2 ≤ Real.log (T + 3) := Real.log_le_log (by norm_num) (by linarith)
    rw [h3] at h1
    linarith
  have hζ : ‖logDeriv riemannZeta₁ s‖ ≤ C₁ * (2 * (Real.log (T + 3) + 1)) ^ 3 := by
    have h2 : 2 ≤ |Tp| := by rw [abs_of_pos hTp0]; linarith
    have hb := h₁ σ Tp hσlo hσhi h2
    have hb' : ‖logDeriv riemannZeta₁ s‖ ≤ C₁ * (Real.log (Tp + 3) + 1) ^ 3 := by
      simpa [hs, abs_of_pos hTp0] using hb
    refine le_trans hb' ?_
    have h3 : (Real.log (Tp + 3) + 1) ^ 3 ≤ (2 * (Real.log (T + 3) + 1)) ^ 3 := hLmono
    exact mul_le_mul_of_nonneg_left h3 hC₁.le
  have hs1 : (0 : ℝ) < ‖s - 1‖ := by
    rw [norm_pos_iff]
    intro h0
    have h1 : s = 1 := sub_eq_zero.mp h0
    have := congrArg Complex.im h1
    simp [hsim] at this
    linarith
  have hnorm_s : Tp ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rw [hTs] at h
    exact h
  have hnorm_s1 : Tp ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    have h1 : (s - 1).im = Tp := by simp [hs]
    rw [h1, abs_of_pos hTp0] at h
    exact h
  have hspos : (0 : ℝ) < ‖s‖ := by
    rw [norm_pos_iff]
    intro h0
    have := congrArg Complex.im h0
    simp [hsim] at this
    linarith
  have hs1 : (0 : ℝ) < ‖s - 1‖ := by
    rw [norm_pos_iff]
    intro h0
    have h1 : s = 1 := sub_eq_zero.mp h0
    have := congrArg Complex.im h1
    simp [hsim] at this
    linarith
  have hnorm_s : Tp ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rw [hTs] at h
    exact h
  have hnorm_s1 : Tp ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    have h1 : (s - 1).im = Tp := by simp [hs]
    rw [h1, abs_of_pos hTp0] at h
    exact h
  have hxpow : ‖(x : ℂ) ^ s‖ = x ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0 s, hsre]
  have hxσ : x ^ σ ≤ x ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx hσhi
  have hx8 : (0 : ℝ) ≤ x ^ (1 / 8 : ℝ) := Real.rpow_nonneg hx0.le _
  have hdiv1 : x ^ σ / ‖s‖ ≤ x ^ (1 / 8 : ℝ) / Tp := by
    rw [div_le_div_iff₀ hspos hTp0]
    nlinarith [hx8, hxσ, hTp0, hnorm_s]
  have hdiv2 : x ^ σ / (‖s‖ * ‖s - 1‖) ≤ (x ^ (1 / 8 : ℝ) / Tp) / Tp := by
    have hmul : (0 : ℝ) < ‖s‖ * ‖s - 1‖ := mul_pos hspos hs1
    rw [div_le_div_iff₀ hmul hTp0]
    have h1 : Tp * Tp ≤ ‖s‖ * ‖s - 1‖ := by
      exact mul_le_mul hnorm_s hnorm_s1 hTp0.le (norm_nonneg _)
    have h2 : x ^ σ ≤ x ^ (1 / 8 : ℝ) := hxσ
    have h3 : x ^ σ * Tp ≤ x ^ (1 / 8 : ℝ) * Tp := by
      exact mul_le_mul_of_nonneg_right h2 hTp0.le
    have h4 : x ^ (1 / 8 : ℝ) * Tp ≤ (x ^ (1 / 8 : ℝ) / Tp) * (‖s‖ * ‖s - 1‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hTp0]
      nlinarith [hx8, h1, hTp0]
    linarith
  have hL0 : (0 : ℝ) ≤ 2 * (Real.log (T + 3) + 1) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 3)
    linarith
  have hb0 : 0 ≤ C₁ * (2 * (Real.log (T + 3) + 1)) ^ 3 :=
    mul_nonneg hC₁.le (pow_nonneg hL0 3)
  have hstep : ‖psiIntF1 x s‖ ≤
      (C₁ * (2 * (Real.log (T + 3) + 1)) ^ 3) * (x ^ (1 / 8 : ℝ) / Tp)
        + (x ^ (1 / 8 : ℝ) / Tp) / Tp := by
    calc ‖psiIntF1 x s‖
        = ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s) + (x : ℂ) ^ s / (s * (s - 1))‖ := by
          rw [psiIntF1]
      _ ≤ ‖(-(logDeriv riemannZeta₁ s)) * ((x : ℂ) ^ s / s)‖ +
            ‖(x : ℂ) ^ s / (s * (s - 1))‖ := norm_add_le _ _
      _ = ‖logDeriv riemannZeta₁ s‖ * ‖(x : ℂ) ^ s / s‖ + ‖(x : ℂ) ^ s / (s * (s - 1))‖ := by
          rw [show (-(logDeriv riemannZeta₁ s)) * ((x : ℂ) ^ s / s) =
              -((logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s)) by ring, norm_neg, norm_mul]
      _ = ‖logDeriv riemannZeta₁ s‖ * (x ^ σ / ‖s‖) + x ^ σ / (‖s‖ * ‖s - 1‖) := by
          have h1 : ‖(x : ℂ) ^ s / s‖ = x ^ σ / ‖s‖ := by rw [norm_div, hxpow]
          have h2 : ‖(x : ℂ) ^ s / (s * (s - 1))‖ = x ^ σ / (‖s‖ * ‖s - 1‖) := by
            rw [norm_div, norm_mul, hxpow]
          rw [h1, h2]
      _ ≤ (C₁ * (2 * (Real.log (T + 3) + 1)) ^ 3) * (x ^ (1 / 8 : ℝ) / Tp)
            + (x ^ (1 / 8 : ℝ) / Tp) / Tp := by
          refine add_le_add ?_ hdiv2
          exact mul_le_mul hζ hdiv1 (div_nonneg (Real.rpow_nonneg hx0.le σ) hspos.le) hb0
  have hL3 : (1 : ℝ) ≤ (Real.log (T + 3) + 1) ^ 3 := by
    have h1 : (1 : ℝ) ≤ Real.log (T + 3) + 1 := by
      have : (0 : ℝ) ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
      linarith
    exact one_le_pow₀ h1
  have h8 : (2 * (Real.log (T + 3) + 1)) ^ 3 = 8 * (Real.log (T + 3) + 1) ^ 3 := by ring
  rw [h8] at hstep
  have hB : (x ^ (1 / 8 : ℝ) / Tp) / Tp ≤ (Real.log (T + 3) + 1) ^ 3 * (x ^ (1 / 8 : ℝ) / Tp) := by
    have h1 : (1 : ℝ) / Tp ≤ (Real.log (T + 3) + 1) ^ 3 := by
      rw [div_le_iff₀ hTp0]
      nlinarith [hL3, hTp0]
    have h2 : (x ^ (1 / 8 : ℝ) / Tp) / Tp = (x ^ (1 / 8 : ℝ) / Tp) * (1 / Tp) := by
      field_simp
    rw [h2]
    calc (x ^ (1 / 8 : ℝ) / Tp) * (1 / Tp) ≤ (x ^ (1 / 8 : ℝ) / Tp) * (Real.log (T + 3) + 1) ^ 3 :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hx8 hTp0.le)
      _ = (Real.log (T + 3) + 1) ^ 3 * (x ^ (1 / 8 : ℝ) / Tp) := by ring
  refine le_trans hstep ?_
  have hA : (0 : ℝ) ≤ (Real.log (T + 3) + 1) ^ 3 * (x ^ (1 / 8 : ℝ) / Tp) :=
    mul_nonneg (by positivity) (div_nonneg hx8 hTp0.le)
  have := mul_le_mul_of_nonneg_left hB (le_of_lt hC₁)
  nlinarith [hA, hC₁]


/-- Pointwise bound of the Perron integrand on the middle strip `Re ∈ [1/2, 5/8]` at a **good
height** `T`: `O(log^3 T · x^{5/8}/T)`, with NO factors of `delta` (this is what makes the
sharp Mertens estimate effective at moderate `x`). -/
theorem psiIntF1_mid_nodelta_pointwise (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T δ : ℝ, 1 ≤ x → 5 ≤ T → 0 < δ →
      1 ≤ (Real.log (T + 3) + 1) * δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → σ ≤ (5 / 8 : ℝ) →
        ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
          C * (Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ (5 / 8 : ℝ) / T) := by
  rcases zeta1_logDeriv_goodHeight h with ⟨C₁, hC₁, h₁⟩
  refine ⟨C₁ + 1, by positivity, ?_⟩
  intro x T δ hx hT hδ0 hδ1 hgap σ hσ1 hσ2
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hT0 : 0 < T := by linarith
  set s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = T := by simp [hs]
  have hζ : ‖logDeriv riemannZeta₁ s‖ ≤ C₁ * (Real.log (T + 3) + 1) ^ 3 := by
    have hb := h₁ T δ hT hδ0 hδ1 hgap σ hσ1 hσ2
    simpa [hs] using hb
  have hspos : (0 : ℝ) < ‖s‖ := by
    rw [norm_pos_iff]
    intro h0
    have := congrArg Complex.im h0
    simp [hsim] at this
    linarith
  have hs1 : (0 : ℝ) < ‖s - 1‖ := by
    rw [norm_pos_iff]
    intro h0
    have h1 : s = 1 := sub_eq_zero.mp h0
    have := congrArg Complex.im h1
    simp [hsim] at this
    linarith
  have hnorm_s : T ≤ ‖s‖ := by
    have h2 := Complex.abs_im_le_norm s
    rw [hsim] at h2
    rwa [ abs_of_pos hT0] at h2
  have hnorm_s1 : T ≤ ‖s - 1‖ := by
    have h2 := Complex.abs_im_le_norm (s - 1)
    have h3 : (s - 1).im = T := by simp [hs]
    rw [h3, abs_of_pos hT0] at h2
    exact h2
  have hxpow : ‖(x : ℂ) ^ s‖ = x ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0 s, hsre]
  have hxσ : x ^ σ ≤ x ^ (5 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ2
  have hx8 : (0 : ℝ) ≤ x ^ (5 / 8 : ℝ) := Real.rpow_nonneg hx0.le _
  have hL0 : (0 : ℝ) ≤ (Real.log (T + 3) + 1) ^ 3 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 3)
    positivity
  have hdiv1 : x ^ σ / ‖s‖ ≤ x ^ (5 / 8 : ℝ) / T := by
    rw [div_le_div_iff₀ hspos hT0]
    nlinarith [hx8, hxσ, hT0, hnorm_s]
  have hdiv2 : x ^ σ / (‖s‖ * ‖s - 1‖) ≤ (x ^ (5 / 8 : ℝ) / T) / T := by
    have hmul : (0 : ℝ) < ‖s‖ * ‖s - 1‖ := mul_pos hspos hs1
    rw [div_le_div_iff₀ hmul hT0]
    have h1 : T * T ≤ ‖s‖ * ‖s - 1‖ := mul_le_mul hnorm_s hnorm_s1 hT0.le (norm_nonneg _)
    have h3 : x ^ σ * T ≤ x ^ (5 / 8 : ℝ) * T := mul_le_mul_of_nonneg_right hxσ hT0.le
    have h4 : x ^ (5 / 8 : ℝ) * T ≤ (x ^ (5 / 8 : ℝ) / T) * (‖s‖ * ‖s - 1‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hT0]
      nlinarith [hx8, h1, hT0]
    linarith
  have hB0 : 0 ≤ C₁ * (Real.log (T + 3) + 1) ^ 3 := mul_nonneg hC₁.le hL0
  have hstep : ‖psiIntF1 x s‖ ≤
      (C₁ * (Real.log (T + 3) + 1) ^ 3) * (x ^ (5 / 8 : ℝ) / T)
        + (x ^ (5 / 8 : ℝ) / T) / T := by
    calc ‖psiIntF1 x s‖
        = ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s) + (x : ℂ) ^ s / (s * (s - 1))‖ := by
          rw [psiIntF1]
      _ ≤ ‖(-(logDeriv riemannZeta₁ s)) * ((x : ℂ) ^ s / s)‖ +
            ‖(x : ℂ) ^ s / (s * (s - 1))‖ := norm_add_le _ _
      _ = ‖logDeriv riemannZeta₁ s‖ * ‖(x : ℂ) ^ s / s‖ + ‖(x : ℂ) ^ s / (s * (s - 1))‖ := by
          rw [show (-(logDeriv riemannZeta₁ s)) * ((x : ℂ) ^ s / s) =
              -((logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s)) by ring, norm_neg, norm_mul]
      _ = ‖logDeriv riemannZeta₁ s‖ * (x ^ σ / ‖s‖) + x ^ σ / (‖s‖ * ‖s - 1‖) := by
          have h1 : ‖(x : ℂ) ^ s / s‖ = x ^ σ / ‖s‖ := by rw [norm_div, hxpow]
          have h2 : ‖(x : ℂ) ^ s / (s * (s - 1))‖ = x ^ σ / (‖s‖ * ‖s - 1‖) := by
            rw [norm_div, norm_mul, hxpow]
          rw [h1, h2]
      _ ≤ (C₁ * (Real.log (T + 3) + 1) ^ 3) * (x ^ (5 / 8 : ℝ) / T)
            + (x ^ (5 / 8 : ℝ) / T) / T := by
          refine add_le_add ?_ hdiv2
          exact mul_le_mul hζ hdiv1 (div_nonneg (Real.rpow_nonneg hx0.le σ) hspos.le) hB0
  have hL3 : (1 : ℝ) ≤ (Real.log (T + 3) + 1) ^ 3 := by
    have h1 : (1 : ℝ) ≤ Real.log (T + 3) + 1 := by
      have : (0 : ℝ) ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
      linarith
    exact one_le_pow₀ h1
  have hB : (x ^ (5 / 8 : ℝ) / T) / T ≤ (Real.log (T + 3) + 1) ^ 3 * (x ^ (5 / 8 : ℝ) / T) := by
    have h1 : (1 : ℝ) / T ≤ (Real.log (T + 3) + 1) ^ 3 := by
      rw [div_le_iff₀ hT0]
      nlinarith [hL3, hT0]
    have h2 : (x ^ (5 / 8 : ℝ) / T) / T = (x ^ (5 / 8 : ℝ) / T) * (1 / T) := by field_simp
    rw [h2]
    calc (x ^ (5 / 8 : ℝ) / T) * (1 / T) ≤ (x ^ (5 / 8 : ℝ) / T) * (Real.log (T + 3) + 1) ^ 3 :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hx8 hT0.le)
      _ = (Real.log (T + 3) + 1) ^ 3 * (x ^ (5 / 8 : ℝ) / T) := by ring
  refine le_trans hstep ?_
  have hA : (0 : ℝ) ≤ (Real.log (T + 3) + 1) ^ 3 * (x ^ (5 / 8 : ℝ) / T) :=
    mul_nonneg hL0 (div_nonneg hx8 hT0.le)
  have := mul_le_mul_of_nonneg_left hB (le_of_lt hC₁)
  nlinarith [hA, hC₁]

/-- Integrated form: the middle part `Re ∈ [1/2, 5/8]` of the top edge is `O(log^3 T x^{5/8}/T)`,
with no `delta` factors. -/
theorem edgeT_mid_nodelta_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T δ : ℝ, 1 ≤ x → 5 ≤ T → 0 < δ →
      1 ≤ (Real.log (T + 3) + 1) * δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ‖edgeT (1 / 2) (5 / 8) T (psiIntF1 x)‖ ≤
        C * (Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ (5 / 8 : ℝ) / T) := by
  rcases psiIntF1_mid_nodelta_pointwise h with ⟨C₁, hC₁, h₁⟩
  refine ⟨(1 / 8) * C₁, by positivity, ?_⟩
  intro x T δ hx hT hδ0 hδ1 hgap
  have hpoint : ∀ σ ∈ Set.uIoc (1 / 2 : ℝ) (5 / 8),
      ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
        C₁ * (Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ (5 / 8 : ℝ) / T) := by
    intro σ hσ
    rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 8)] at hσ
    exact h₁ x T δ hx hT hδ0 hδ1 hgap σ (le_of_lt hσ.1) hσ.2
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := (5 / 8 : ℝ))
    (C := C₁ * (Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ (5 / 8 : ℝ) / T)) hpoint
  have habs : |(5 / 8 : ℝ) - 1 / 2| = 1 / 8 := by norm_num
  rw [habs] at hmain
  have hcoe : (C₁ * (Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ (5 / 8 : ℝ) / T)) * (1 / 8) =
      (1 / 8) * C₁ * (Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ (5 / 8 : ℝ) / T) := by ring
  rw [hcoe] at hmain
  simpa [edgeT, wRect, mul_comm] using hmain


end Commons.NumberTheory.Zeta
end


-- ==== begin p3_zeroSets ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# Route B, step 0: zero-set bookkeeping for the integrated explicit formula

Under the Riemann hypothesis every zero of `riemannZeta₁` with real part in `(−2, 2)` lies on
the critical line `Re = 1/2`, so the rectangle zero-Finset `zRectZeros` depends on its
parameters only through the height and the *ball*: it is the set of zeros of the ball Finset
with `Re = 1/2` and `|Im| < T`.  This makes the comparison of zero-Finsets at different
heights/radii a purely combinatorial matter, which is what the "fixed height on `[x,Y]`"
step of Route B needs.
-/

open Classical Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- The concrete rectangle zero-Finset is the ball zero-Finset filtered by `RectInside`. -/
lemma zetaZeroRectFin_eq_filter {R : ℝ} (hR : 0 ≤ R) (z w : ℂ) :
    zetaZeroRectFin (R := R) hR z w =
      (zetaZeroBallFin R hR).filter (fun ρ => RectInside z w ρ) := rfl

/-- Under RH, a zero of `ζ₁` in the ball of radius `R` whose real part lies in `(a,b)` with
`−2 < a < 1/2` has real part `1/2`. -/
lemma re_eq_half_of_rect_mem (h : RiemannHypothesis) {R : ℝ} (hR : 0 ≤ R) {a b T : ℝ}
    (ha2 : -2 < a) (ha : a < (1 / 2 : ℝ)) {ρ : ℂ}
    (hball : ρ ∈ zetaZeroBallFin R hR) (hins : RectInside (zRect a T) (wRect b T) ρ) :
    ρ.re = 1 / 2 := by
  have hζ₁ : riemannZeta₁ ρ = 0 := ((zetaZeroBallFin_spec R hR ρ).mp hball).2
  simp only [RectInside, zRect_re, zRect_im, wRect_re, wRect_im] at hins
  obtain ⟨hlo, _, _, _⟩ := hins
  have hmass : ¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre : ρ.re = -2 * ((n : ℝ) + 1) := by
      rw [hn]
      simp [Complex.mul_re, Complex.add_re]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hρ1 : ρ ≠ 1 := by
    intro h1
    rw [h1, riemannZeta₁_one] at hζ₁
    exact one_ne_zero hζ₁
  have hζ : riemannZeta ρ = 0 := by
    rw [riemannZeta_eq_inv_sub_mul hρ1, hζ₁, mul_zero]
  exact h ρ hζ hmass hρ1

/-- **Normal form of the rectangle zero-Finset.**  Under RH, with `−2 < a < 1/2 < b`, the
zeros of `ζ₁` strictly inside the rectangle `(a,b) × (−T,T)` are exactly the zeros of `ζ₁` in
the ball of radius `R` whose real part is `1/2` and whose imaginary part has modulus `< T`. -/
theorem zRectZeros_eq_filter (h : RiemannHypothesis) {R : ℝ} (hR : 0 ≤ R)
    {a b T : ℝ} (ha2 : -2 < a) (ha : a < (1 / 2 : ℝ)) (hb : (1 / 2 : ℝ) < b) :
    zRectZeros (R := R) hR a b T =
      (zetaZeroBallFin R hR).filter (fun ρ => ρ.re = 1 / 2 ∧ |ρ.im| < T) := by
  rw [show zRectZeros (R := R) hR a b T
      = (zetaZeroBallFin R hR).filter (fun ρ => RectInside (zRect a T) (wRect b T) ρ) from
    zetaZeroRectFin_eq_filter hR (zRect a T) (wRect b T)]
  apply Finset.ext
  intro ρ
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hball, hins⟩
    simp only [RectInside, zRect_re, zRect_im, wRect_re, wRect_im] at hins
    obtain ⟨hlo, hhi, hTlo, hThi⟩ := hins
    exact ⟨hball, re_eq_half_of_rect_mem h hR ha2 ha hball
      (by simp only [RectInside, zRect_re, zRect_im, wRect_re, wRect_im]
          exact ⟨hlo, hhi, hTlo, hThi⟩), abs_lt.mpr ⟨hTlo, hThi⟩⟩
  · rintro ⟨hball, hre, him⟩
    refine ⟨hball, ?_⟩
    obtain ⟨hTlo, hThi⟩ := abs_lt.mp him
    simp only [RectInside, zRect_re, zRect_im, wRect_re, wRect_im]
    exact ⟨by linarith, by linarith, hTlo, hThi⟩

/-- **Comparison of rectangle zero-Finsets across balls and heights.**  If `T₁ ≤ T₂` and every
zero on the critical line with `|Im| < T₁` lies in both the ball of radius `R₁` and that of
radius `R₂`, then the zero-Finset at height `T₁` (ball `R₁`) is the height-`T₁` sub-Finset of
the zero-Finset at height `T₂` (ball `R₂`). -/
theorem zRectZeros_eq_filter_of_ball (h : RiemannHypothesis) {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁)
    (hR₂ : 0 ≤ R₂) {a₁ b₁ a₂ b₂ T₁ T₂ : ℝ} (ha2₁ : -2 < a₁) (ha₁ : a₁ < (1 / 2 : ℝ))
    (hb₁ : (1 / 2 : ℝ) < b₁) (ha2₂ : -2 < a₂) (ha₂ : a₂ < (1 / 2 : ℝ))
    (hb₂ : (1 / 2 : ℝ) < b₂) (hT : T₁ ≤ T₂)
    (hrad : ∀ ρ : ℂ, ρ.re = 1 / 2 → |ρ.im| < T₁ → ‖ρ‖ ≤ min R₁ R₂) :
    zRectZeros (R := R₁) hR₁ a₁ b₁ T₁ =
      (zRectZeros (R := R₂) hR₂ a₂ b₂ T₂).filter (fun ρ => |ρ.im| < T₁) := by
  rw [zRectZeros_eq_filter h hR₁ ha2₁ ha₁ hb₁, zRectZeros_eq_filter h hR₂ ha2₂ ha₂ hb₂]
  -- collapse the two filters on the right to the single height-`T₁` filter
  have hstep : ((zetaZeroBallFin R₂ hR₂).filter
        (fun ρ => ρ.re = 1 / 2 ∧ |ρ.im| < T₂)).filter (fun ρ => |ρ.im| < T₁)
      = (zetaZeroBallFin R₂ hR₂).filter (fun ρ => ρ.re = 1 / 2 ∧ |ρ.im| < T₁) := by
    apply Finset.ext
    intro ρ
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hball, hre, _⟩, him⟩
      exact ⟨hball, hre, him⟩
    · rintro ⟨hball, hre, him⟩
      exact ⟨⟨hball, hre, lt_of_lt_of_le him hT⟩, him⟩
  rw [hstep]
  -- move from the ball of radius `R₁` to the ball of radius `R₂`
  apply Finset.ext
  intro ρ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hball, hre, him⟩
    refine ⟨?_, hre, him⟩
    rw [zetaZeroBallFin_spec]
    rw [zetaZeroBallFin_spec] at hball
    refine ⟨?_, hball.2⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hball ⊢
    exact le_trans (hrad ρ hre him) (min_le_right _ _)
  · rintro ⟨hball, hre, him⟩
    refine ⟨?_, hre, him⟩
    rw [zetaZeroBallFin_spec]
    rw [zetaZeroBallFin_spec] at hball
    refine ⟨?_, hball.2⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hball ⊢
    exact le_trans (hrad ρ hre him) (min_le_left _ _)


end Commons.NumberTheory.Zeta
end


-- ==== begin p3_farLeft ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# The far-left Perron contour (`Re = -1/2`): the residue at `s = 0`

The truncated explicit formula for `ψ` (P4, `rectInt_psiIntF1_engineSum`) uses the contour
`Re ∈ (1/4, 1+1/log x)`.  To make the *integrated* version effective at moderate `x` we must
move the left edge down to `Re = -1/2`, which costs a new pole: `s = 0` is then strictly
inside the rectangle.  The Perron kernel `psiIntF1 x s = -(ζ₁′/ζ₁)(s)·x^s/s + x^s/(s(s-1))`
has a **simple pole at `s = 0` with residue `-log(2π)`** (the classical constant of the
explicit formula), and after subtracting it the function extends analytically through `0`.

Main contents:
* `logDeriv_riemannZeta₁_zero` : `logDeriv ζ₁ 0 = log(2π) - 1`;
* `zeta1_ne_zero_of_re_le_zero` : `ζ₁ ≠ 0` on `-3/2 ≤ Re s ≤ 0` (functional equation; no RH);
* `psiIntF1_sub_polar_zero_removal` : the local pole removal at `0`;
* `rectInt_split_vertical` : additivity of `rectInt` over adjacent rectangles;
* `rectInt_strip_zeroPole` : `rectInt` over a strip `[a, c] × [-Tp, Tp]` with `a < 0 < c ≤ 1/4`
  (only the pole at `0` is inside) equals `-log(2π)·2πi`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section

set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Zeta

/-! ## The residue of `psiIntF1` at `s = 0` -/

lemma riemannZeta₁_zero : riemannZeta₁ (0 : ℂ) = 1 / 2 := by
  rw [riemannZeta₁, riemannZeta₀]
  rw [if_neg (by norm_num : (0 : ℂ) ≠ 1)]
  rw [riemannZeta_zero]
  norm_num

lemma logDeriv_riemannZeta₁_zero :
    logDeriv riemannZeta₁ (0 : ℂ) = Complex.log (2 * (Real.pi : ℂ)) - 1 := by
  have hcongr : logDeriv riemannZeta₁ =ᶠ[𝓝 (0 : ℂ)]
      logDeriv (fun s : ℂ => (s - 1) * riemannZeta s) := by
    apply logDeriv_congr_nhds
    filter_upwards [isOpen_ne.mem_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with s hs
    rw [riemannZeta₁, riemannZeta₀]
    rw [if_neg hs]
    have h := riemannZeta_eq_inv_sub_add (s := s) hs
    rw [h]
    have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    field_simp
    ring
  rw [hcongr.eq_of_nhds]
  erw [logDeriv_mul (f := fun s : ℂ => s - 1) (g := riemannZeta) 0 (by norm_num) (by rw [riemannZeta_zero]; norm_num)
      (by fun_prop) (differentiableAt_riemannZeta (by norm_num))]
  have h1 : logDeriv (fun s : ℂ => s - 1) 0 = -1 := by
    rw [logDeriv_apply]
    have hd : deriv (fun s : ℂ => s - 1) 0 = 1 := by
      simpa using (hasDerivAt_id (0 : ℂ)).sub_const 1
    rw [hd]; norm_num
  have h2 : logDeriv riemannZeta (0 : ℂ) = Complex.log (2 * (Real.pi : ℂ)) := by
    rw [logDeriv_apply, deriv_riemannZeta_zero, riemannZeta_zero]
    field_simp
  rw [h1, h2]; ring

/-- the residue of `psiIntF1 x ·` at `s = 0`, `-log(2π)`. -/
noncomputable def caZeroCoeff : ℂ := -Complex.log (2 * (Real.pi : ℂ))

lemma caZeroCoeff_eq_logDeriv : caZeroCoeff = -(logDeriv riemannZeta₁ 0 + 1) := by
  rw [caZeroCoeff, logDeriv_riemannZeta₁_zero]; ring

/-! ## Zero-freeness of `ζ₁` on `-1/2 ≤ Re ≤ 0` -/

lemma zeta1_ne_zero_of_re_le_zero {s : ℂ} (hlo : -(3 / 2 : ℝ) ≤ s.re) (hhi : s.re ≤ 0) :
    riemannZeta₁ s ≠ 0 := by
  intro hz
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hhi
    norm_num at hhi
  have hzeta : riemannZeta s = 0 := by
    rw [riemannZeta_eq_inv_sub_mul hs1, hz, mul_zero]
  by_cases hs0 : s = 0
  · rw [hs0, riemannZeta_zero] at hzeta
    norm_num at hzeta
  · have ht1 : (1 - s) ≠ 1 := by
      intro h
      apply hs0
      linear_combination -h
    have htneg : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
      intro n hn
      have hre : (1 - s).re = -(n : ℝ) := by rw [hn]; simp
      rw [Complex.sub_re, Complex.one_re] at hre
      have : s.re = (n : ℝ) + 1 := by linarith
      linarith [hhi]
    have hfe := riemannZeta_one_sub htneg ht1
    rw [show (1:ℂ) - (1 - s) = s by ring, hzeta] at hfe
    have hA : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 := by
      refine mul_ne_zero (by norm_num) ?_
      rw [Complex.cpow_ne_zero_iff]
      left
      exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    have hB : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero htneg
    have hC : Complex.cos (Real.pi * (1 - s) / 2) ≠ 0 := by
      intro hc
      obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
      have h1 : (1 - s) = 2 * (k : ℂ) + 1 := by
        have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        field_simp at hk
        linear_combination hk
      have hre : s.re = -2 * (k : ℝ) := by
        have h := congrArg Complex.re h1
        simp [Complex.sub_re, Complex.one_re] at h
        linarith
      have him : s.im = 0 := by
        have h := congrArg Complex.im h1
        simpa using h
      have hk1 : (0 : ℝ) ≤ (k : ℝ) := by linarith [hre, hhi]
      have hk2 : k ≤ 0 := by
        by_contra h
        push_neg at h
        have h3 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
        linarith [hre, hlo]
      have hk_nonneg : 0 ≤ k := by
        by_contra h
        push_neg at h
        have h3 : (k : ℝ) ≤ -1 := by
          have : k ≤ -1 := by omega
          exact_mod_cast this
        linarith
      have hk0 : k = 0 := by omega
      have hzre : s.re = 0 := by rw [hre, hk0]; simp
      have : s = 0 := by
        apply Complex.ext
        · simpa using hzre
        · simpa using him
      exact hs0 this
    have hABC : ((2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - s))) * Complex.Gamma (1 - s) *
        Complex.cos (Real.pi * (1 - s) / 2) ≠ 0 := mul_ne_zero (mul_ne_zero hA hB) hC
    have hzeta1 : riemannZeta (1 - s) = 0 := by
      have h := hfe.symm
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 hABC
      · exact h1
    exact riemannZeta_ne_zero_of_one_le_re (by rw [Complex.sub_re, Complex.one_re]; linarith) hzeta1

/-! ## The local pole removal at `s = 0` -/

lemma psiIntF1_sub_polar_zero_removal {x : ℝ} (hx : 0 < x) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (0 : ℂ) ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), F s = psiIntF1 x s - caZeroCoeff * s⁻¹ := by
  let R : ℂ → ℂ := fun s => logDeriv riemannZeta₁ s * (x : ℂ) ^ s + (x : ℂ) ^ s / (1 - s)
  have hR0 : R 0 = Complex.log (2 * (Real.pi : ℂ)) := by
    dsimp [R]
    rw [logDeriv_riemannZeta₁_zero]
    norm_num
  have hU : IsOpen {w : ℂ | riemannZeta₁ w ≠ 0 ∧ w ≠ 1} := by
    have h1 : IsOpen {w : ℂ | riemannZeta₁ w ≠ 0} :=
      (isClosed_singleton.preimage differentiable_riemannZeta₁.continuous).isOpen_compl
    have h2 : IsOpen {w : ℂ | w ≠ 1} := isOpen_ne
    rw [Set.setOf_and]
    exact h1.inter h2
  have h0U : (0 : ℂ) ∈ {w : ℂ | riemannZeta₁ w ≠ 0 ∧ w ≠ 1} := by
    refine ⟨?_, by norm_num⟩
    rw [riemannZeta₁_zero]; norm_num
  have hRdiff : DifferentiableOn ℂ R {w : ℂ | riemannZeta₁ w ≠ 0 ∧ w ≠ 1} := by
    intro w hw
    have hlog : DifferentiableAt ℂ (fun s : ℂ => logDeriv riemannZeta₁ s) w :=
      (logDeriv_zeta1_analyticAt hw.1).differentiableAt
    have hpow : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) w :=
      (Commons.NumberTheory.Zeta.cpow_differentiable hx).differentiableAt
    have hden : DifferentiableAt ℂ (fun s : ℂ => 1 - s) w := by fun_prop
    have hden0 : (1 - w) ≠ 0 := by
      intro h
      exact hw.2 (sub_eq_zero.mp h).symm
    have h2 : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s / (1 - s)) w := hpow.div hden hden0
    exact ((hlog.mul hpow).add h2).differentiableWithinAt
  have hdslope : AnalyticAt ℂ (dslope R 0) (0 : ℂ) :=
    analyticAt_dslope_of_differentiableOn hU h0U hRdiff
  refine ⟨fun s => -(dslope R 0 s), hdslope.neg, ?_⟩
  have hquot : ∀ᶠ s in 𝓝[≠] (0 : ℂ), dslope R 0 s = (R s - R 0) / (s - 0) := by
    exact dslope_eventuallyEq_quotient R 0
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards with s hs
    exact hs
  filter_upwards [hquot, hne] with s hs hs0
  rw [hs, hR0]
  dsimp [R, psiIntF1]
  rw [caZeroCoeff]
  field_simp
  have h1 : (1 : ℂ) / (1 - s) = -(1 / (s - 1)) := by
    rw [show (1 - s : ℂ) = -(s - 1) by ring]
    simp only [one_div, inv_neg]
  rw [h1]
  ring

noncomputable def psiZeroPoleRemoval (x : ℝ) (hx : 0 < x) : ℂ → ℂ :=
  Classical.choose (psiIntF1_sub_polar_zero_removal (x := x) hx)

lemma psiZeroPoleRemoval_analyticAt {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℂ (psiZeroPoleRemoval x hx) (0 : ℂ) :=
  (Classical.choose_spec (psiIntF1_sub_polar_zero_removal (x := x) hx)).1

lemma psiZeroPoleRemoval_eventually {x : ℝ} (hx : 0 < x) :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      psiZeroPoleRemoval x hx s = psiIntF1 x s - caZeroCoeff * s⁻¹ :=
  (Classical.choose_spec (psiIntF1_sub_polar_zero_removal (x := x) hx)).2

/-! ## Splitting `rectInt` over adjacent rectangles -/

lemma rectInt_split_vertical (f : ℂ → ℂ) {a b c Tp : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (h1 : IntervalIntegrable (fun x : ℝ => f (x + (zRect a Tp).im * Complex.I)) volume a c)
    (h2 : IntervalIntegrable (fun x : ℝ => f (x + (zRect a Tp).im * Complex.I)) volume c b)
    (h3 : IntervalIntegrable (fun x : ℝ => f (x + (wRect b Tp).im * Complex.I)) volume a c)
    (h4 : IntervalIntegrable (fun x : ℝ => f (x + (wRect b Tp).im * Complex.I)) volume c b) :
    rectInt (zRect a Tp) (wRect b Tp) f
      = rectInt (zRect a Tp) (wRect c Tp) f + rectInt (zRect c Tp) (wRect b Tp) f := by
  have hbottom := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have htop := intervalIntegral.integral_add_adjacent_intervals h3 h4
  simp only [rectInt, zRect_re, zRect_im, wRect_re, wRect_im] at *
  rw [← hbottom, ← htop]
  ring

/-! ## The strip `[a, c] × [-Tp, Tp]` with `a < 0 < c ≤ 1/4`: only the pole at `0` is inside -/

lemma ne_zero_of_im_eq {t : ℂ} {Tp : ℝ} (hTp : 0 < Tp) (h : t.im = -Tp ∨ t.im = Tp) : t ≠ 0 := by
  intro h0
  have him : t.im = 0 := by rw [h0]; simp
  rcases h with h | h <;> linarith

lemma ne_zero_of_re_neg_pos {t : ℂ} {a c : ℝ} (ha : a < 0) (hc : 0 < c)
    (h : t.re = a ∨ t.re = c) : t ≠ 0 := by
  intro h0
  have hre : t.re = 0 := by rw [h0]; simp
  rcases h with h | h <;> linarith

/-- `psiIntF1 x` is analytic where `ζ₁ ≠ 0` and `s ∉ {0, 1}`. -/
lemma psiIntF1_analyticAt {x : ℝ} (hx : 0 < x) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζ : riemannZeta₁ s ≠ 0) : AnalyticAt ℂ (fun z : ℂ => psiIntF1 x z) s := by
  have hlog : AnalyticAt ℂ (fun z : ℂ => logDeriv riemannZeta₁ z) s := logDeriv_zeta1_analyticAt hζ
  have hdiv1 : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z / z) s := cpow_div_self_analyticAt' hx hs0
  have hterm1 : AnalyticAt ℂ (fun z : ℂ => - logDeriv riemannZeta₁ z * ((x : ℂ) ^ z / z)) s :=
    AnalyticAt.mul (AnalyticAt.neg hlog) hdiv1
  have hterm2 : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z / (z * (z - 1))) s :=
    cpow_div_mul_sub_one_analyticAt hx hs0 hs1
  have hpsi : AnalyticAt ℂ (fun z : ℂ => psiIntF1 x z) s := by
    dsimp [psiIntF1]
    exact AnalyticAt.add hterm1 hterm2
  exact hpsi

/-- the remainder of `psiIntF1 x ·` after removing the pole at `0`, patched at `0`. -/
noncomputable def psiStripRemainder (x : ℝ) (hx : 0 < x) : ℂ → ℂ :=
  fun s => if s = 0 then psiZeroPoleRemoval x hx s else psiIntF1 x s - caZeroCoeff * s⁻¹

lemma psiStripRemainder_eq {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    psiStripRemainder x hx s = psiIntF1 x s - caZeroCoeff * s⁻¹ := by
  unfold psiStripRemainder
  rw [if_neg hs]

lemma psiStripRemainder_analyticAt_zero {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℂ (psiStripRemainder x hx) (0 : ℂ) := by
  have hrem := psiZeroPoleRemoval_analyticAt hx
  have h1 : psiStripRemainder x hx =ᶠ[𝓝 (0 : ℂ)] psiZeroPoleRemoval x hx := by
    have hev := psiZeroPoleRemoval_eventually hx
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with s hs
    by_cases h0 : s = 0
    · subst h0
      unfold psiStripRemainder
      rw [if_pos rfl]
    · unfold psiStripRemainder
      rw [if_neg h0]
      exact (hs h0).symm
  exact hrem.congr h1.symm

lemma psiStripRemainder_analyticAt {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0)
    (hs1 : s ≠ 1) (hζ : riemannZeta₁ s ≠ 0) :
    AnalyticAt ℂ (psiStripRemainder x hx) s := by
  have hpsi := psiIntF1_analyticAt hx hs hs1 hζ
  have hdiv : AnalyticAt ℂ (fun z : ℂ => caZeroCoeff / z) s :=
    AnalyticAt.div (analyticAt_const (v := caZeroCoeff)) analyticAt_id hs
  have hinv : AnalyticAt ℂ (fun z : ℂ => caZeroCoeff * z⁻¹) s := by
    simpa [div_eq_mul_inv] using hdiv
  have hEq : psiStripRemainder x hx =ᶠ[𝓝 s] (fun z => psiIntF1 x z - caZeroCoeff * z⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact psiStripRemainder_eq hx hz
  exact (hpsi.sub hinv).congr hEq.symm

lemma psiStripRemainder_differentiableOn (h : RiemannHypothesis) {x a c Tp : ℝ} (hx : 0 < x)
    (ha : -(3 / 2 : ℝ) ≤ a) (ha0 : a < 0) (hc0 : 0 < c) (hc4 : c ≤ 1 / 4) (hTp : 0 < Tp) :
    DifferentiableOn ℂ (psiStripRemainder x hx) (closedContourRect a c Tp) := by
  intro s hs
  have hab : a ≤ c := by linarith
  have hT : -Tp ≤ Tp := by linarith
  have hmem := (mem_closedContourRect hab hT s).mp hs
  obtain ⟨hre1, hre2, him1, him2⟩ := hmem
  by_cases hs0 : s = 0
  · subst hs0
    exact (psiStripRemainder_analyticAt_zero hx).differentiableAt.differentiableWithinAt
  · have hζ : riemannZeta₁ s ≠ 0 := by
      by_cases hle : s.re ≤ 0
      · exact zeta1_ne_zero_of_re_le_zero (by linarith) hle
      · push_neg at hle
        exact zeta1_ne_zero_of_rh_lt_half h hle (by linarith)
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1] at hre2
      simp at hre2
      linarith
    exact (psiStripRemainder_analyticAt hx hs0 hs1 hζ).differentiableAt.differentiableWithinAt

/-- **The strip identity**: for `-1/2 ≤ a < 0 < c ≤ 1/4`, `Tp > 0`, the rectangle integral of
`psiIntF1 x ·` over `[a,c] × [-Tp, Tp]` is `2πi·(-log(2π))` (the pole at `0` is the only pole
inside). -/
theorem rectInt_strip_zeroPole (h : RiemannHypothesis) {x a c Tp : ℝ} (hx : 0 < x)
    (ha : -(3 / 2 : ℝ) ≤ a) (ha0 : a < 0) (hc0 : 0 < c) (hc4 : c ≤ 1 / 4) (hTp : 0 < Tp) :
    rectInt (zRect a Tp) (wRect c Tp) (psiIntF1 x)
      = caZeroCoeff * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  have hG := psiStripRemainder_differentiableOn h hx ha ha0 hc0 hc4 hTp
  have hG' : DifferentiableOn ℂ (psiStripRemainder x hx)
      (Set.uIcc (zRect a Tp).re (wRect c Tp).re ×ℂ
        Set.uIcc (zRect a Tp).im (wRect c Tp).im) := by
    simpa [closedContourRect, zRect_re, zRect_im, wRect_re, wRect_im] using hG
  have hzre : (zRect a Tp).re < (wRect c Tp).re := by
    simp [zRect_re, wRect_re]; linarith
  have hzim : (zRect a Tp).im < (wRect c Tp).im := by
    simp [zRect_im, wRect_im]; linarith
  have hu : ∀ i ∈ ({0} : Finset ℂ), (zRect a Tp).re < i.re ∧ i.re < (wRect c Tp).re ∧
      (zRect a Tp).im < i.im ∧ i.im < (wRect c Tp).im := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Complex.zero_re, Complex.zero_im, zRect_re, zRect_im,
      wRect_re, wRect_im] <;> linarith
  have hmodel : rectInt (zRect a Tp) (wRect c Tp)
      (fun t => (∑ i ∈ ({0} : Finset ℂ), caZeroCoeff / (t - (i : ℂ))) + psiStripRemainder x hx t)
      = caZeroCoeff * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    have hm := rectInt_model_multi_pole (ι := ℂ) (s := ({0} : Finset ℂ)) (u := fun i => (i : ℂ))
      (c := fun _ => caZeroCoeff) (G := psiStripRemainder x hx) hzre hzim hu hG'
    simpa using hm
  have hcong : rectInt (zRect a Tp) (wRect c Tp)
      (fun t => (∑ i ∈ ({0} : Finset ℂ), caZeroCoeff / (t - (i : ℂ))) + psiStripRemainder x hx t)
      = rectInt (zRect a Tp) (wRect c Tp) (psiIntF1 x) := by
    apply rectInt_congr_boundary
    · intro x0 _
      have ht0 : (x0 + (zRect a Tp).im * Complex.I) ≠ 0 :=
        ne_zero_of_im_eq hTp (Or.inl (by simp [zRect_im]))
      rw [Finset.sum_singleton, psiStripRemainder_eq hx ht0, div_eq_mul_inv, sub_zero]
      ring
    · intro x0 _
      have ht0 : (x0 + (wRect c Tp).im * Complex.I) ≠ 0 :=
        ne_zero_of_im_eq hTp (Or.inr (by simp [wRect_im]))
      rw [Finset.sum_singleton, psiStripRemainder_eq hx ht0, div_eq_mul_inv, sub_zero]
      ring
    · intro y _
      have ht0 : ((wRect c Tp).re + y * Complex.I) ≠ 0 :=
        ne_zero_of_re_neg_pos ha0 hc0 (Or.inr (by simp [wRect_re]))
      rw [Finset.sum_singleton, psiStripRemainder_eq hx ht0, div_eq_mul_inv, sub_zero]
      ring
    · intro y _
      have ht0 : ((zRect a Tp).re + y * Complex.I) ≠ 0 :=
        ne_zero_of_re_neg_pos ha0 hc0 (Or.inl (by simp [zRect_re]))
      rw [Finset.sum_singleton, psiStripRemainder_eq hx ht0, div_eq_mul_inv, sub_zero]
      ring
  rw [← hcong]
  exact hmodel

lemma psiIntF1_intervalIntegrable_horiz (h : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    {Tp a b : ℝ} (hTp : 0 < Tp)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp)
    {s : ℝ} (hs : s = -Tp ∨ s = Tp) :
    IntervalIntegrable (fun u : ℝ => psiIntF1 x ((u : ℂ) + (s : ℂ) * Complex.I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  have hsim : ((u : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
  have hsne : s ≠ 0 := by
    rcases hs with h' | h' <;> rw [h'] <;> linarith
  have hne0 : (u : ℂ) + (s : ℂ) * Complex.I ≠ 0 := by
    intro h0
    have him : ((u : ℂ) + (s : ℂ) * Complex.I).im = 0 := by rw [h0]; simp
    rw [hsim] at him
    exact hsne him
  have hne1 : (u : ℂ) + (s : ℂ) * Complex.I ≠ 1 := by
    intro h0
    have him : ((u : ℂ) + (s : ℂ) * Complex.I).im = 0 := by rw [h0]; simp
    rw [hsim] at him
    exact hsne him
  have hζ : riemannZeta₁ ((u : ℂ) + (s : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    rcases hs with h' | h'
    · exact (hgood _ hz).2 (by rw [hsim, h'])
    · exact (hgood _ hz).1 (by rw [hsim, h'])
  have hg : ContinuousAt (fun u : ℝ => (u : ℂ) + (s : ℂ) * Complex.I) u :=
    continuous_ofReal.continuousAt.add continuousAt_const
  have hc : ContinuousAt (fun u : ℝ => psiIntF1 x ((u : ℂ) + (s : ℂ) * Complex.I)) u :=
    ContinuousAt.comp (g := fun z : ℂ => psiIntF1 x z)
      (f := fun u : ℝ => (u : ℂ) + (s : ℂ) * Complex.I)
      (psiIntF1_analyticAt hx hne0 hne1 hζ).continuousAt hg
  exact hc.continuousWithinAt

/-- **The far-left explicit formula** (T-R3.1 at the improved contour): for `-3/2 ≤ a < 0`,
`1 < b`, `Tp > 0`, the closed rectangle inside the ball of radius `R` and no zero of `ζ₁` on
the horizontal sides, the rectangle integral of the ζ₁-Perron kernel equals `2πi` times
`x - log(2π) - Σ_ρ m_ρ x^ρ/ρ`. -/
theorem rectInt_psiIntF1_engineSum_farLeft (h : RiemannHypothesis) {R a b Tp x : ℝ}
    (hR : 0 ≤ R) (hx : 0 < x) (ha : -(3 / 2 : ℝ) ≤ a) (ha0 : a < 0) (h1b : 1 < b)
    (hTp : 0 < Tp)
    (hrect : closedContourRect a b Tp ⊆ Metric.closedBall (0 : ℂ) R)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp) :
    rectInt (zRect a Tp) (wRect b Tp) (psiIntF1 x) =
      ((x : ℂ) - Complex.log (2 * (Real.pi : ℂ)) -
        ∑ ρ ∈ zRectZeros hR a b Tp, (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ) *
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  have hrectq : closedContourRect (1 / 4) b Tp ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    apply hrect
    have hab : (1 / 4 : ℝ) ≤ b := by linarith
    have hT : -Tp ≤ Tp := by linarith
    rw [mem_closedContourRect hab hT z] at hz
    rw [mem_closedContourRect (by linarith : a ≤ b) hT z]
    exact ⟨by linarith [hz.1], hz.2.1, hz.2.2⟩
  have hquarter := rectInt_psiIntF1_engineSum h hR hx (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1 / 2) h1b hTp hrectq hgood
  have hstrip := rectInt_strip_zeroPole h hx ha ha0 (by norm_num : (0 : ℝ) < 1 / 4)
    (le_refl (1 / 4 : ℝ)) hTp
  have hI1 : IntervalIntegrable (fun x0 : ℝ => psiIntF1 x (x0 + (zRect a Tp).im * Complex.I))
      volume a (1 / 4) := by
    have := psiIntF1_intervalIntegrable_horiz h hx hTp hgood (s := -Tp) (Or.inl rfl) (a := a)
      (b := (1 / 4 : ℝ))
    simpa only [zRect_im] using this
  have hI2 : IntervalIntegrable (fun x0 : ℝ => psiIntF1 x (x0 + (zRect a Tp).im * Complex.I))
      volume (1 / 4) b := by
    have := psiIntF1_intervalIntegrable_horiz h hx hTp hgood (s := -Tp) (Or.inl rfl)
      (a := (1 / 4 : ℝ)) (b := b)
    simpa only [zRect_im] using this
  have hI3 : IntervalIntegrable (fun x0 : ℝ => psiIntF1 x (x0 + (wRect b Tp).im * Complex.I))
      volume a (1 / 4) := by
    have := psiIntF1_intervalIntegrable_horiz h hx hTp hgood (s := Tp) (Or.inr rfl) (a := a)
      (b := (1 / 4 : ℝ))
    simpa only [wRect_im] using this
  have hI4 : IntervalIntegrable (fun x0 : ℝ => psiIntF1 x (x0 + (wRect b Tp).im * Complex.I))
      volume (1 / 4) b := by
    have := psiIntF1_intervalIntegrable_horiz h hx hTp hgood (s := Tp) (Or.inr rfl)
      (a := (1 / 4 : ℝ)) (b := b)
    simpa only [wRect_im] using this
  have hsplit := rectInt_split_vertical (psiIntF1 x) (a := a) (b := b) (c := 1 / 4)
    (by linarith) (by linarith) hI1 hI2 hI3 hI4
  have hZ : zRectZeros hR (1 / 4) b Tp = zRectZeros hR a b Tp := by
    rw [zRectZeros_eq_filter h hR (by linarith : -2 < a) (by linarith : a < (1 / 2 : ℝ))
        (by linarith : (1 / 2 : ℝ) < b),
      zRectZeros_eq_filter h hR (by norm_num : -2 < (1 / 4 : ℝ))
        (by norm_num : (1 / 4 : ℝ) < (1 / 2 : ℝ)) (by linarith : (1 / 2 : ℝ) < b)]
  rw [hsplit, hstrip, hquarter, hZ, caZeroCoeff]
  ring


end Commons.NumberTheory.Zeta
end


-- ==== begin p3_farLeftBounds ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# The far-left contour, part 2: the horizontal side bounds without `delta`

This module collects the **pointwise** and **integrated** bounds for the top/bottom edges of
the far-left rectangle `[-1/2, b] × [-T, T]` (`b ≤ 2`) at a *fixed good height* `T`:
`sigma in [-1/2,1/8]` (functional-equation strip), `[1/8,1/2]` (left middle strip, delta-free
`zeta1_logDeriv_left_mid_nodelta`), `[1/2,5/8]` (`psiIntF1_mid_nodelta_pointwise`) and
`[5/8,b]` (right strip).  The delta factors disappear at a good height, which is what makes
the integrated explicit formula effective at moderate `x`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Zeta

/-- the pointwise far-left bound at a fixed height `T` (specialisation of
`psiIntF1_farleft_pointwise` to `Tp = T`). -/
theorem psiIntF1_farleft_pointwise_fixed (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T : ℝ, 1 ≤ x → 5 ≤ T →
      ∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ (1 / 8 : ℝ) →
        ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
          C * (Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T) := by
  rcases psiIntF1_farleft_pointwise h with ⟨C, hC, h₁⟩
  refine ⟨C, hC, ?_⟩
  intro x T hx hT σ hσ1 hσ2
  have := h₁ x T T hx hT le_rfl (by linarith) σ hσ1 hσ2
  simpa using this

/-- `ζ₁` does not vanish on the horizontal line `Im = T` when `T` is a good height. -/
lemma zeta1_ne_zero_of_gap {T δ σ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) :
    riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := by
  intro hz
  have h := hgap _ hz
  have him : (((σ : ℂ) + Complex.I * (T : ℂ)) : ℂ).im = T := by simp
  rw [him, sub_self, abs_zero] at h
  linarith

/-- interval integrability of the Perron kernel along the horizontal line `Im = T` at a good
height. -/
lemma psiIntF1_intervalIntegrable_line {x T δ : ℝ} (hx : 0 < x) (hT : 5 ≤ T) (hδ : 0 < δ)
    (hgap : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) (p q : ℝ) :
    IntervalIntegrable (fun σ : ℝ => psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))) volume p q := by
  apply ContinuousOn.intervalIntegrable
  intro σ _
  have hζ : riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := zeta1_ne_zero_of_gap hδ hgap
  have hne0 : ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := by
    intro h0
    have him : (((σ : ℂ) + Complex.I * (T : ℂ)) : ℂ).im = T := by simp
    rw [h0] at him
    simp at him
    linarith
  have hne1 : ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 1 := by
    intro h0
    have him : (((σ : ℂ) + Complex.I * (T : ℂ)) : ℂ).im = T := by simp
    rw [h0] at him
    simp at him
    linarith
  have hg : ContinuousAt (fun σ : ℝ => (σ : ℂ) + Complex.I * (T : ℂ)) σ := by fun_prop
  have hcomp : ContinuousAt ((fun z : ℂ => psiIntF1 x z) ∘
      fun σ : ℝ => (σ : ℂ) + Complex.I * (T : ℂ)) σ :=
    ContinuousAt.comp (g := fun z : ℂ => psiIntF1 x z)
      (f := fun σ : ℝ => (σ : ℂ) + Complex.I * (T : ℂ))
      (psiIntF1_analyticAt hx hne0 hne1 hζ).continuousAt hg
  exact hcomp.continuousWithinAt

theorem psiIntF1_leftmid_nodelta_pointwise (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T δ : ℝ, 1 ≤ x → 5 ≤ T → 0 < δ →
      1 ≤ (Real.log (T + 3) + 1) * δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ∀ σ : ℝ, (1 / 8 : ℝ) ≤ σ → σ ≤ (1 / 2 : ℝ) →
        ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
          C * (Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T) := by
  rcases zeta1_logDeriv_left_mid_nodelta h with ⟨C₁, hC₁, h₁⟩
  refine ⟨C₁ + 1, by positivity, ?_⟩
  intro x T δ hx hT hδ0 hδ1 hgap σ hσ1 hσ2
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hT0 : 0 < T := by linarith
  set s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = T := by simp [hs]
  have hζ : ‖logDeriv riemannZeta₁ s‖ ≤ C₁ * (Real.log (T + 3) + 1) ^ 3 := by
    have hb := h₁ T δ hT hδ0 hδ1 hgap σ hσ1 hσ2
    simpa [hs] using hb
  have hspos : (0 : ℝ) < ‖s‖ := by
    rw [norm_pos_iff]
    intro h0
    have := congrArg Complex.im h0
    simp [hsim] at this
    linarith
  have hs1 : (0 : ℝ) < ‖s - 1‖ := by
    rw [norm_pos_iff]
    intro h0
    have h1 : s = 1 := sub_eq_zero.mp h0
    have := congrArg Complex.im h1
    simp [hsim] at this
    linarith
  have hnorm_s : T ≤ ‖s‖ := by
    have h2 := Complex.abs_im_le_norm s
    rw [hsim] at h2
    rwa [ abs_of_pos hT0] at h2
  have hnorm_s1 : T ≤ ‖s - 1‖ := by
    have h2 := Complex.abs_im_le_norm (s - 1)
    have h3 : (s - 1).im = T := by simp [hs]
    rw [h3, abs_of_pos hT0] at h2
    exact h2
  have hxpow : ‖(x : ℂ) ^ s‖ = x ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0 s, hsre]
  have hxσ : x ^ σ ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ2
  have hx8 : (0 : ℝ) ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hL0 : (0 : ℝ) ≤ (Real.log (T + 3) + 1) ^ 3 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 3)
    positivity
  have hdiv1 : x ^ σ / ‖s‖ ≤ x ^ (1 / 2 : ℝ) / T := by
    rw [div_le_div_iff₀ hspos hT0]
    nlinarith [hx8, hxσ, hT0, hnorm_s]
  have hdiv2 : x ^ σ / (‖s‖ * ‖s - 1‖) ≤ (x ^ (1 / 2 : ℝ) / T) / T := by
    have hmul : (0 : ℝ) < ‖s‖ * ‖s - 1‖ := mul_pos hspos hs1
    rw [div_le_div_iff₀ hmul hT0]
    have h1 : T * T ≤ ‖s‖ * ‖s - 1‖ := mul_le_mul hnorm_s hnorm_s1 hT0.le (norm_nonneg _)
    have h3 : x ^ σ * T ≤ x ^ (1 / 2 : ℝ) * T := mul_le_mul_of_nonneg_right hxσ hT0.le
    have h4 : x ^ (1 / 2 : ℝ) * T ≤ (x ^ (1 / 2 : ℝ) / T) * (‖s‖ * ‖s - 1‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hT0]
      nlinarith [hx8, h1, hT0]
    linarith
  have hB0 : 0 ≤ C₁ * (Real.log (T + 3) + 1) ^ 3 := mul_nonneg hC₁.le hL0
  have hstep : ‖psiIntF1 x s‖ ≤
      (C₁ * (Real.log (T + 3) + 1) ^ 3) * (x ^ (1 / 2 : ℝ) / T)
        + (x ^ (1 / 2 : ℝ) / T) / T := by
    calc ‖psiIntF1 x s‖
        = ‖-(logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s) + (x : ℂ) ^ s / (s * (s - 1))‖ := by
          rw [psiIntF1]
      _ ≤ ‖(-(logDeriv riemannZeta₁ s)) * ((x : ℂ) ^ s / s)‖ +
            ‖(x : ℂ) ^ s / (s * (s - 1))‖ := norm_add_le _ _
      _ = ‖logDeriv riemannZeta₁ s‖ * ‖(x : ℂ) ^ s / s‖ + ‖(x : ℂ) ^ s / (s * (s - 1))‖ := by
          rw [show (-(logDeriv riemannZeta₁ s)) * ((x : ℂ) ^ s / s) =
              -((logDeriv riemannZeta₁ s) * ((x : ℂ) ^ s / s)) by ring, norm_neg, norm_mul]
      _ = ‖logDeriv riemannZeta₁ s‖ * (x ^ σ / ‖s‖) + x ^ σ / (‖s‖ * ‖s - 1‖) := by
          have h1 : ‖(x : ℂ) ^ s / s‖ = x ^ σ / ‖s‖ := by rw [norm_div, hxpow]
          have h2 : ‖(x : ℂ) ^ s / (s * (s - 1))‖ = x ^ σ / (‖s‖ * ‖s - 1‖) := by
            rw [norm_div, norm_mul, hxpow]
          rw [h1, h2]
      _ ≤ (C₁ * (Real.log (T + 3) + 1) ^ 3) * (x ^ (1 / 2 : ℝ) / T)
            + (x ^ (1 / 2 : ℝ) / T) / T := by
          refine add_le_add ?_ hdiv2
          exact mul_le_mul hζ hdiv1 (div_nonneg (Real.rpow_nonneg hx0.le σ) hspos.le) hB0
  have hL3 : (1 : ℝ) ≤ (Real.log (T + 3) + 1) ^ 3 := by
    have h1 : (1 : ℝ) ≤ Real.log (T + 3) + 1 := by
      have : (0 : ℝ) ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
      linarith
    exact one_le_pow₀ h1
  have hB : (x ^ (1 / 2 : ℝ) / T) / T ≤ (Real.log (T + 3) + 1) ^ 3 * (x ^ (1 / 2 : ℝ) / T) := by
    have h1 : (1 : ℝ) / T ≤ (Real.log (T + 3) + 1) ^ 3 := by
      rw [div_le_iff₀ hT0]
      nlinarith [hL3, hT0]
    have h2 : (x ^ (1 / 2 : ℝ) / T) / T = (x ^ (1 / 2 : ℝ) / T) * (1 / T) := by field_simp
    rw [h2]
    calc (x ^ (1 / 2 : ℝ) / T) * (1 / T) ≤ (x ^ (1 / 2 : ℝ) / T) * (Real.log (T + 3) + 1) ^ 3 :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hx8 hT0.le)
      _ = (Real.log (T + 3) + 1) ^ 3 * (x ^ (1 / 2 : ℝ) / T) := by ring
  refine le_trans hstep ?_
  have hA : (0 : ℝ) ≤ (Real.log (T + 3) + 1) ^ 3 * (x ^ (1 / 2 : ℝ) / T) :=
    mul_nonneg hL0 (div_nonneg hx8 hT0.le)
  have := mul_le_mul_of_nonneg_left hB (le_of_lt hC₁)
  nlinarith [hA, hC₁]


/-- **Top/bottom edge bound at a good height, without `delta`**: for `-1/2 ≤ a ≤ 5/8 ≤ b ≤ 2`
the horizontal edge integral of the Perron kernel is `O((log T)^3 x^b / T)`. -/
theorem edgeT_bound_nodelta (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x a b T δ : ℝ), 1 ≤ x → -(1 / 2 : ℝ) ≤ a → a ≤ (1 / 8 : ℝ) →
      (5 / 8 : ℝ) ≤ b → b ≤ 2 → 5 ≤ T → 0 < δ → 1 ≤ (Real.log (T + 3) + 1) * δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ‖edgeT a b T (psiIntF1 x)‖ ≤
        C * ((Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ b / T)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := psiIntF1_farleft_pointwise_fixed h
  obtain ⟨C₂, hC₂, h₂⟩ := psiIntF1_leftmid_nodelta_pointwise h
  obtain ⟨C₃, hC₃, h₃⟩ := edgeT_mid_nodelta_bound h
  obtain ⟨C₄, hC₄, h₄⟩ := edge_horiz_right_bound h
  refine ⟨(5 / 8) * C₁ + (3 / 8) * C₂ + C₃ + (11 / 8) * C₄ + 1, by positivity, ?_⟩
  intro x a b T δ hx ha hab hb1 hb2 hT hδ0 hδ1 hgap
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set L : ℝ := Real.log (T + 3) + 1 with hL
  have hL0 : 0 ≤ L := by
    rw [hL]
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 3)
    linarith
  have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL0 3
  have hxb : 0 ≤ (x : ℝ) ^ b := Real.rpow_nonneg hx0.le b
  have hpow18 : (x : ℝ) ^ (1 / 8 : ℝ) ≤ (x : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hpow12 : (x : ℝ) ^ (1 / 2 : ℝ) ≤ (x : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hpow58 : (x : ℝ) ^ (5 / 8 : ℝ) ≤ (x : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hx hb1
  set F : ℝ → ℂ := fun σ => psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ)) with hF
  have hInt : ∀ p q : ℝ, IntervalIntegrable F volume p q :=
    fun p q =>
      psiIntF1_intervalIntegrable_line hx0 hT hδ0 hgap p q
  have hE1 : (∫ σ in a..(1 / 8), F σ) + (∫ σ in (1 / 8)..b, F σ) = ∫ σ in a..b, F σ :=
    intervalIntegral.integral_add_adjacent_intervals (hInt a (1 / 8)) (hInt (1 / 8) b)
  have hE2 : (∫ σ in (1 / 8)..(1 / 2), F σ) + (∫ σ in (1 / 2)..b, F σ) =
      ∫ σ in (1 / 8)..b, F σ :=
    intervalIntegral.integral_add_adjacent_intervals (hInt (1 / 8) (1 / 2)) (hInt (1 / 2) b)
  have hE3 : (∫ σ in (1 / 2)..(5 / 8), F σ) + (∫ σ in (5 / 8)..b, F σ) =
      ∫ σ in (1 / 2)..b, F σ :=
    intervalIntegral.integral_add_adjacent_intervals (hInt (1 / 2) (5 / 8)) (hInt (5 / 8) b)
  -- the edge integral in the `F` form
  have hE : edgeT a b T (psiIntF1 x) = ∫ σ in a..b, F σ := by
    rw [edgeT]
    apply intervalIntegral.integral_congr
    intro σ _
    show psiIntF1 x ((σ : ℂ) + ((wRect b T).im : ℂ) * Complex.I) = F σ
    rw [hF]
    congr 1
    rw [wRect_im, mul_comm]
  -- piece bounds
  have hB1 : ‖∫ σ in a..(1 / 8), F σ‖ ≤ (5 / 8) * (C₁ * L ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T)) := by
    have hp : ∀ σ ∈ Set.uIoc a (1 / 8),
        ‖F σ‖ ≤ C₁ * L ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T) := by
      intro σ hσ
      rw [Set.uIoc_of_le (by linarith : a ≤ 1 / 8)] at hσ
      have hσ1 : -(1 / 2 : ℝ) ≤ σ := le_trans ha (le_of_lt hσ.1)
      have := h₁ x T hx hT σ hσ1 hσ.2
      simpa only [hF, hL] using this
    have hm := intervalIntegral.norm_integral_le_of_norm_le_const hp
    have hlen : |(1 / 8 : ℝ) - a| ≤ 5 / 8 := by
      rw [abs_le]; constructor <;> linarith
    have hC0 : 0 ≤ C₁ * L ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T) :=
      mul_nonneg (mul_nonneg hC₁.le hL3) (div_nonneg (Real.rpow_nonneg hx0.le _) hT0.le)
    calc ‖∫ σ in a..(1 / 8), F σ‖ ≤ (C₁ * L ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T)) * |(1 / 8 : ℝ) - a| := hm
      _ ≤ (C₁ * L ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T)) * (5 / 8) :=
          mul_le_mul_of_nonneg_left hlen hC0
      _ = (5 / 8) * (C₁ * L ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T)) := by ring
  have hB2 : ‖∫ σ in (1 / 8)..(1 / 2), F σ‖ ≤ (3 / 8) * (C₂ * L ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T)) := by
    have hp : ∀ σ ∈ Set.uIoc (1 / 8) (1 / 2),
        ‖F σ‖ ≤ C₂ * L ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T) := by
      intro σ hσ
      rw [Set.uIoc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2)] at hσ
      have := h₂ x T δ hx hT hδ0 hδ1 hgap σ (le_of_lt hσ.1) hσ.2
      simpa only [hF, hL] using this
    have hm := intervalIntegral.norm_integral_le_of_norm_le_const hp
    have hlen : |(1 / 2 : ℝ) - 1 / 8| ≤ 3 / 8 := by norm_num
    have hC0 : 0 ≤ C₂ * L ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T) :=
      mul_nonneg (mul_nonneg hC₂.le hL3) (div_nonneg (Real.rpow_nonneg hx0.le _) hT0.le)
    calc ‖∫ σ in (1 / 8)..(1 / 2), F σ‖ ≤ (C₂ * L ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T)) * |(1 / 2 : ℝ) - 1 / 8| := hm
      _ ≤ (C₂ * L ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T)) * (3 / 8) :=
          mul_le_mul_of_nonneg_left hlen hC0
      _ = (3 / 8) * (C₂ * L ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T)) := by ring
  have hB3 : ‖∫ σ in (1 / 2)..(5 / 8), F σ‖ ≤ C₃ * L ^ 3 * ((x : ℝ) ^ (5 / 8 : ℝ) / T) := by
    have hm := h₃ x T δ hx hT hδ0 hδ1 hgap
    have hEq : edgeT (1 / 2) (5 / 8) T (psiIntF1 x) = ∫ σ in (1 / 2)..(5 / 8), F σ := by
      rw [edgeT]
      apply intervalIntegral.integral_congr
      intro σ _
      show psiIntF1 x ((σ : ℂ) + ((wRect (5 / 8) T).im : ℂ) * Complex.I) = F σ
      rw [hF]
      congr 1
      rw [wRect_im, mul_comm]
    rw [hEq, ← hL] at hm
    exact hm
  have hB4 : ‖∫ σ in (5 / 8)..b, F σ‖ ≤ (11 / 8) * (C₄ * L ^ 3 * ((x : ℝ) ^ b / T)) := by
    have hTabs : |T| = T := abs_of_nonneg hT0.le
    have hm := h₄ x b T hx hb1 hb2 (by rw [hTabs]; linarith)
    rw [hTabs] at hm
    have hm' : ‖∫ σ in (5 / 8)..b, F σ‖ ≤ C₄ * L ^ 3 * ((x : ℝ) ^ b * (b - 5 / 8) / T) := by
      rw [hF]
      simpa only [hL] using hm
    have hle : b - 5 / 8 ≤ 11 / 8 := by linarith
    have hC0 : 0 ≤ C₄ * L ^ 3 * ((x : ℝ) ^ b / T) :=
      mul_nonneg (mul_nonneg hC₄.le hL3) (div_nonneg hxb hT0.le)
    have hstep : C₄ * L ^ 3 * ((x : ℝ) ^ b * (b - 5 / 8) / T) ≤
        (11 / 8) * (C₄ * L ^ 3 * ((x : ℝ) ^ b / T)) := by
      have h1 : (x : ℝ) ^ b * (b - 5 / 8) / T = ((x : ℝ) ^ b / T) * (b - 5 / 8) := by ring
      rw [h1]
      calc C₄ * L ^ 3 * (((x : ℝ) ^ b / T) * (b - 5 / 8))
          = (C₄ * L ^ 3 * ((x : ℝ) ^ b / T)) * (b - 5 / 8) := by ring
        _ ≤ (C₄ * L ^ 3 * ((x : ℝ) ^ b / T)) * (11 / 8) :=
            mul_le_mul_of_nonneg_left hle hC0
        _ = (11 / 8) * (C₄ * L ^ 3 * ((x : ℝ) ^ b / T)) := by ring
    exact le_trans hm' hstep
  -- combine
  have hK0 : 0 ≤ (5 / 8) * C₁ + (3 / 8) * C₂ + C₃ + (11 / 8) * C₄ := by positivity
  have hK0' : 0 ≤ (5 / 8) * C₁ + (3 / 8) * C₂ + C₃ + (11 / 8) * C₄ + 1 := by positivity
  have htgt : 0 ≤ L ^ 3 * ((x : ℝ) ^ b / T) := mul_nonneg hL3 (div_nonneg hxb hT0.le)
  have hB1' : ‖∫ σ in a..(1 / 8), F σ‖ ≤
      (5 / 8) * C₁ * (L ^ 3 * ((x : ℝ) ^ b / T)) := by
    have hpow : (x : ℝ) ^ (1 / 8 : ℝ) / T ≤ (x : ℝ) ^ b / T :=
      div_le_div_of_nonneg_right hpow18 hT0.le
    have h1 : C₁ * L ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T) ≤ C₁ * (L ^ 3 * ((x : ℝ) ^ b / T)) := by
      have h2 : L ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T) ≤ L ^ 3 * ((x : ℝ) ^ b / T) :=
        mul_le_mul_of_nonneg_left hpow hL3
      calc C₁ * L ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T) = C₁ * (L ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T)) := by ring
        _ ≤ C₁ * (L ^ 3 * ((x : ℝ) ^ b / T)) := mul_le_mul_of_nonneg_left h2 hC₁.le
    calc ‖∫ σ in a..(1 / 8), F σ‖ ≤ (5 / 8) * (C₁ * L ^ 3 * ((x : ℝ) ^ (1 / 8 : ℝ) / T)) := hB1
      _ ≤ (5 / 8) * (C₁ * (L ^ 3 * ((x : ℝ) ^ b / T))) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (5 / 8) * C₁ * (L ^ 3 * ((x : ℝ) ^ b / T)) := by ring
  have hB2' : ‖∫ σ in (1 / 8)..(1 / 2), F σ‖ ≤
      (3 / 8) * C₂ * (L ^ 3 * ((x : ℝ) ^ b / T)) := by
    have hpow : (x : ℝ) ^ (1 / 2 : ℝ) / T ≤ (x : ℝ) ^ b / T :=
      div_le_div_of_nonneg_right hpow12 hT0.le
    have h1 : C₂ * L ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T) ≤ C₂ * (L ^ 3 * ((x : ℝ) ^ b / T)) := by
      have h2 : L ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T) ≤ L ^ 3 * ((x : ℝ) ^ b / T) :=
        mul_le_mul_of_nonneg_left hpow hL3
      calc C₂ * L ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T) = C₂ * (L ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T)) := by ring
        _ ≤ C₂ * (L ^ 3 * ((x : ℝ) ^ b / T)) := mul_le_mul_of_nonneg_left h2 hC₂.le
    calc ‖∫ σ in (1 / 8)..(1 / 2), F σ‖ ≤ (3 / 8) * (C₂ * L ^ 3 * ((x : ℝ) ^ (1 / 2 : ℝ) / T)) := hB2
      _ ≤ (3 / 8) * (C₂ * (L ^ 3 * ((x : ℝ) ^ b / T))) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (3 / 8) * C₂ * (L ^ 3 * ((x : ℝ) ^ b / T)) := by ring
  have hB3' : ‖∫ σ in (1 / 2)..(5 / 8), F σ‖ ≤ C₃ * (L ^ 3 * ((x : ℝ) ^ b / T)) := by
    have hpow : (x : ℝ) ^ (5 / 8 : ℝ) / T ≤ (x : ℝ) ^ b / T :=
      div_le_div_of_nonneg_right hpow58 hT0.le
    have h2 : L ^ 3 * ((x : ℝ) ^ (5 / 8 : ℝ) / T) ≤ L ^ 3 * ((x : ℝ) ^ b / T) :=
      mul_le_mul_of_nonneg_left hpow hL3
    calc ‖∫ σ in (1 / 2)..(5 / 8), F σ‖ ≤ C₃ * L ^ 3 * ((x : ℝ) ^ (5 / 8 : ℝ) / T) := hB3
      _ = C₃ * (L ^ 3 * ((x : ℝ) ^ (5 / 8 : ℝ) / T)) := by ring
      _ ≤ C₃ * (L ^ 3 * ((x : ℝ) ^ b / T)) := mul_le_mul_of_nonneg_left h2 hC₃.le
  have hB4' : ‖∫ σ in (5 / 8)..b, F σ‖ ≤
      (11 / 8) * C₄ * (L ^ 3 * ((x : ℝ) ^ b / T)) := by
    calc ‖∫ σ in (5 / 8)..b, F σ‖ ≤ (11 / 8) * (C₄ * L ^ 3 * ((x : ℝ) ^ b / T)) := hB4
      _ = (11 / 8) * C₄ * (L ^ 3 * ((x : ℝ) ^ b / T)) := by ring
  have htri1 := norm_add_le (∫ σ in a..(1 / 8), F σ)
    ((∫ σ in (1 / 8)..(1 / 2), F σ) + ((∫ σ in (1 / 2)..(5 / 8), F σ) +
      ∫ σ in (5 / 8)..b, F σ))
  have htri2 := norm_add_le (∫ σ in (1 / 8)..(1 / 2), F σ)
    ((∫ σ in (1 / 2)..(5 / 8), F σ) + ∫ σ in (5 / 8)..b, F σ)
  have htri3 := norm_add_le (∫ σ in (1 / 2)..(5 / 8), F σ) (∫ σ in (5 / 8)..b, F σ)
  have htot : ‖edgeT a b T (psiIntF1 x)‖ ≤
      ((5 / 8) * C₁ + (3 / 8) * C₂ + C₃ + (11 / 8) * C₄) * (L ^ 3 * ((x : ℝ) ^ b / T)) := by
    rw [hE, ← hE1, ← hE2, ← hE3]
    have hfinal : ‖(∫ σ in a..(1 / 8), F σ) +
        ((∫ σ in (1 / 8)..(1 / 2), F σ) +
          ((∫ σ in (1 / 2)..(5 / 8), F σ) + ∫ σ in (5 / 8)..b, F σ))‖ ≤
        (5 / 8) * C₁ * (L ^ 3 * ((x : ℝ) ^ b / T)) + ((3 / 8) * C₂ * (L ^ 3 * ((x : ℝ) ^ b / T)) +
          (C₃ * (L ^ 3 * ((x : ℝ) ^ b / T)) + (11 / 8) * C₄ * (L ^ 3 * ((x : ℝ) ^ b / T)))) := by
      calc ‖(∫ σ in a..(1 / 8), F σ) + ((∫ σ in (1 / 8)..(1 / 2), F σ) +
            ((∫ σ in (1 / 2)..(5 / 8), F σ) + ∫ σ in (5 / 8)..b, F σ))‖
          ≤ ‖∫ σ in a..(1 / 8), F σ‖ +
              ‖(∫ σ in (1 / 8)..(1 / 2), F σ) + ((∫ σ in (1 / 2)..(5 / 8), F σ) +
                ∫ σ in (5 / 8)..b, F σ)‖ := htri1
        _ ≤ ‖∫ σ in a..(1 / 8), F σ‖ +
              (‖∫ σ in (1 / 8)..(1 / 2), F σ‖ + ‖(∫ σ in (1 / 2)..(5 / 8), F σ) +
                ∫ σ in (5 / 8)..b, F σ‖) := by linarith [htri2]
        _ ≤ ‖∫ σ in a..(1 / 8), F σ‖ +
              (‖∫ σ in (1 / 8)..(1 / 2), F σ‖ + (‖∫ σ in (1 / 2)..(5 / 8), F σ‖ +
                ‖∫ σ in (5 / 8)..b, F σ‖)) := by linarith [htri3]
        _ ≤ _ := by linarith [hB1', hB2', hB3', hB4']
    have heq : ((5 / 8) * C₁ * (L ^ 3 * ((x : ℝ) ^ b / T)) + ((3 / 8) * C₂ * (L ^ 3 * ((x : ℝ) ^ b / T)) +
          (C₃ * (L ^ 3 * ((x : ℝ) ^ b / T)) + (11 / 8) * C₄ * (L ^ 3 * ((x : ℝ) ^ b / T))))) =
        ((5 / 8) * C₁ + (3 / 8) * C₂ + C₃ + (11 / 8) * C₄) * (L ^ 3 * ((x : ℝ) ^ b / T)) := by ring
    rw [heq] at hfinal
    exact hfinal
  calc ‖edgeT a b T (psiIntF1 x)‖
      ≤ ((5 / 8) * C₁ + (3 / 8) * C₂ + C₃ + (11 / 8) * C₄) * (L ^ 3 * ((x : ℝ) ^ b / T)) := htot
    _ ≤ ((5 / 8) * C₁ + (3 / 8) * C₂ + C₃ + (11 / 8) * C₄ + 1) * (L ^ 3 * ((x : ℝ) ^ b / T)) := by
        apply mul_le_mul_of_nonneg_right _ htgt
        linarith
    _ = ((5 / 8) * C₁ + (3 / 8) * C₂ + C₃ + (11 / 8) * C₄ + 1) *
        ((Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ b / T)) := by rw [hL]



end Commons.NumberTheory.Zeta
end


-- ==== begin p3_negBounds ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# Bounds for the Perron kernel on the far-left strip `-3/2 ≤ Re ≤ -1/4`

The far-left contour identity `rectInt_psiIntF1_engineSum_farLeft_neg` allows the left edge to be
at `Re = -3/2`.  This file collects the matching *analytic* bounds for the kernel
`psiIntF1 x` on that strip: the compact bound for `logDeriv ζ₁` (via the zero-freeness of `ζ₁`
on `-3/2 ≤ Re ≤ 0`) and (later) the edge bounds used by the truncated explicit formula.
-/

open Complex Filter Metric Set
open scoped Real Topology

noncomputable section
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Zeta

/-- `logDeriv ζ₁` is bounded on the compact rectangle `-3/2 ≤ Re s ≤ -1/4`, `|Im s| ≤ 3`.-/
theorem zeta1_logDeriv_negCompact :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(3/2 : ℝ) ≤ s.re → s.re ≤ -(1/4 : ℝ) → |s.im| ≤ 3 →
      ‖logDeriv riemannZeta₁ s‖ ≤ C := by
  let K : Set ℂ := {s : ℂ | -(3 / 2 : ℝ) ≤ s.re ∧ s.re ≤ -(1 / 4 : ℝ) ∧ |s.im| ≤ 3}
  have hKcompact : IsCompact K := by
    have himg : K = (fun p : ℝ × ℝ => ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))) ''
        (Set.Icc (-(3 / 2 : ℝ)) (-(1 / 4 : ℝ)) ×ˢ Set.Icc (-3 : ℝ) 3) := by
      ext s
      constructor
      · rintro ⟨h1, h2, h3⟩
        rw [abs_le] at h3
        exact ⟨(s.re, s.im), ⟨⟨h1, h2⟩, h3⟩, by
          apply Complex.ext <;> simp⟩
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
        have hre : (((p.1 : ℂ) + Complex.I * (p.2 : ℂ))).re = p.1 := by simp
        have him : (((p.1 : ℂ) + Complex.I * (p.2 : ℂ))).im = p.2 := by simp
        refine ⟨?_, ?_, ?_⟩
        · rw [hre]; exact hp1
        · rw [hre]; exact hp2
        · rw [him, abs_le]; exact ⟨hp3, hp4⟩
    rw [himg]
    exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hKne : K.Nonempty := ⟨((-(1 / 4 : ℝ)) : ℂ), by
    refine ⟨by norm_num, by norm_num, by norm_num⟩⟩
  have hne : ∀ s ∈ K, riemannZeta₁ s ≠ 0 := by
    intro s hs
    exact zeta1_ne_zero_of_re_le_zero hs.1 (by linarith [hs.2.1])
  have hcont : ContinuousOn (fun s : ℂ => ‖logDeriv riemannZeta₁ s‖) K := by
    have hderiv : Continuous (deriv riemannZeta₁) :=
      (differentiable_riemannZeta₁.contDiff (n := ⊤)).continuous_deriv le_top
    have hdiv : ContinuousOn (logDeriv riemannZeta₁) K :=
      hderiv.continuousOn.div differentiable_riemannZeta₁.continuous.continuousOn hne
    exact hdiv.norm
  rcases hKcompact.exists_isMaxOn hKne hcont with ⟨a, _haK, hmax⟩
  refine ⟨‖logDeriv riemannZeta₁ a‖ + 1, by positivity, ?_⟩
  intro s hs1 hs2 hs3
  have hsK : s ∈ K := ⟨hs1, hs2, hs3⟩
  have hle : ‖logDeriv riemannZeta₁ s‖ ≤ ‖logDeriv riemannZeta₁ a‖ := hmax hsK
  linarith


end Commons.NumberTheory.Zeta
end


-- ==== begin p3_negT ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# The top/bottom edge bound for the far-left contour `Re ∈ [-3/2, 1/8]`

To push the left edge of the Perron rectangle down to `Re = -3/2` we need the horizontal
(top/bottom) edge bounds over the enlarged `σ`-range `[-3/2, 1/8]`.  The new ingredient is
the piece `σ ∈ [-3/2, -1/2]`, where `logDeriv ζ₁` is bounded by `zeta_logDeriv_negStrip_bound`
and the kernel contributes `x^{σ}/‖s‖ ≤ x^{-1/2}/T`.

The `δ`-dependence is carried multiplicatively (`K` with `1 ≤ K·L·δ`), because the natural
good-height gap produced by `exists_gap_height` is only `δ ≈ 1/(c log T)`, i.e. `L·δ` is
bounded below but not by `1`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Zeta

/-- Conversion of a `logDeriv ζ₁` bound on the line `Im = T` into a bound for the Perron
kernel: if `‖logDeriv ζ₁ (σ+iT)‖ ≤ M` with `1 ≤ T` then
`‖psiIntF1 x (σ+iT)‖ ≤ (M+1)·(x^σ/T)`. -/
lemma psiIntF1_line_le_of_logDeriv {x T M σ : ℝ} (hx : 0 < x) (hT : 1 ≤ T)
    (hM : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ M) :
    ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ (M + 1) * ((x : ℝ) ^ σ / T) := by
  set s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = T := by simp [hs]
  have hT0 : 0 < T := by linarith
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hnorm_s : T ≤ ‖s‖ := by
    have h2 := Complex.abs_im_le_norm s
    rw [hsim, abs_of_pos hT0] at h2
    exact h2
  have hnorm_s1 : (1 : ℝ) ≤ ‖s - 1‖ := by
    have h2 := Complex.abs_im_le_norm (s - 1)
    have h3 : (s - 1).im = T := by simp [hs]
    rw [h3, abs_of_pos hT0] at h2
    linarith
  have hxσ : 0 ≤ (x : ℝ) ^ σ := Real.rpow_nonneg hx.le σ
  have hnorm := psiIntF1_norm_le_logDeriv hx s
  have hspos : 0 < ‖s‖ := lt_of_lt_of_le hT0 hnorm_s
  have h1 : (x : ℝ) ^ s.re / ‖s‖ ≤ (x : ℝ) ^ σ / T := by
    rw [hsre]
    rw [div_le_div_iff₀ hspos hT0]
    nlinarith [hxσ, hnorm_s]
  have h2 : 1 / ‖s - 1‖ ≤ 1 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnorm_s1
    simpa using this
  calc ‖psiIntF1 x s‖
      ≤ (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) * ((x : ℝ) ^ s.re / ‖s‖) := hnorm
    _ ≤ (M + 1) * ((x : ℝ) ^ σ / T) := by
        apply mul_le_mul (add_le_add hM h2) h1 (div_nonneg (Real.rpow_nonneg hx.le s.re) hspos.le)
        linarith [hM0]

/-- **Pointwise kernel bound on the far-left strip** `σ ∈ [-3/2, -1/2]`, `T ≥ 5`:
`‖psiIntF1 x (σ+iT)‖ ≤ C·L³·x^{-1/2}/T`. -/
theorem psiIntF1_negStrip_pointwise (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T : ℝ, 1 ≤ x → 5 ≤ T → ∀ σ : ℝ,
      -(3 / 2 : ℝ) ≤ σ → σ ≤ -(1 / 2 : ℝ) →
      ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
        C * (Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ (-(1 / 2) : ℝ) / T) := by
  obtain ⟨C₁, hC₁, h₁⟩ := zeta_logDeriv_negStrip_bound h
  refine ⟨C₁ + 1, by linarith, ?_⟩
  intro x T hx hT σ hσ1 hσ2
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set L : ℝ := Real.log (T + 3) + 1 with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    simp only [hL]; linarith
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have hlogeq : Real.log (|T| + 3) + 1 = L := by
    rw [abs_of_nonneg hT0.le]
  have ht2 : (2 : ℝ) ≤ |T| := by rw [abs_of_nonneg hT0.le]; linarith
  have hld : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ C₁ * L ^ 3 := by
    have hb := h₁ σ T hσ1 hσ2 ht2
    rwa [hlogeq] at hb
  have hp := psiIntF1_line_le_of_logDeriv hx0 (by linarith : (1 : ℝ) ≤ T) hld
  have hxσ : (x : ℝ) ^ σ ≤ (x : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx hσ2
  have hxp : 0 ≤ (x : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hx0.le _
  have hd : (x : ℝ) ^ σ / T ≤ (x : ℝ) ^ (-(1 / 2) : ℝ) / T :=
    div_le_div_of_nonneg_right hxσ hT0.le
  have hle : C₁ * L ^ 3 + 1 ≤ (C₁ + 1) * L ^ 3 := by nlinarith [hC₁.le, hL3]
  calc ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖
      ≤ (C₁ * L ^ 3 + 1) * ((x : ℝ) ^ σ / T) := hp
    _ ≤ (C₁ + 1) * L ^ 3 * ((x : ℝ) ^ (-(1 / 2) : ℝ) / T) := by
        have h0 : 0 ≤ (x : ℝ) ^ σ / T := div_nonneg (Real.rpow_nonneg hx0.le σ) hT0.le
        calc (C₁ * L ^ 3 + 1) * ((x : ℝ) ^ σ / T)
            ≤ ((C₁ + 1) * L ^ 3) * ((x : ℝ) ^ (-(1 / 2) : ℝ) / T) :=
              mul_le_mul hle hd h0 (by positivity)
          _ = (C₁ + 1) * L ^ 3 * ((x : ℝ) ^ (-(1 / 2) : ℝ) / T) := by ring

/-- Pointwise kernel bound on `σ ∈ [1/8, 1/2]` at a good height, in `δ`-form. -/
theorem psiIntF1_leftmid_delta_pointwise (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T δ : ℝ, 1 ≤ x → 5 ≤ T → 0 < δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ∀ σ : ℝ, (1 / 8 : ℝ) ≤ σ → σ ≤ (1 / 2 : ℝ) →
        ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
          C * ((Real.log (T + 3) + 1) ^ 3 + (Real.log (T + 3) + 1) ^ 2 / δ) *
            ((x : ℝ) ^ (1 / 2 : ℝ) / T) := by
  obtain ⟨C₀, hC₀, h₀⟩ := zeta1_logDeriv_left_mid_delta h
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro x T δ hx hT hδ0 hgap σ hσ1 hσ2
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set L : ℝ := Real.log (T + 3) + 1 with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    simp only [hL]; linarith
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have hM1 : 1 ≤ L ^ 3 + L ^ 2 / δ := by
    have : 0 ≤ L ^ 2 / δ := div_nonneg (pow_nonneg (by linarith) 2) hδ0.le
    linarith
  have hld := h₀ T δ hT hδ0 hgap σ hσ1 hσ2
  have hld' : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
      C₀ * (L ^ 3 + L ^ 2 / δ) := by simpa only [hL] using hld
  have hp := psiIntF1_line_le_of_logDeriv hx0 (by linarith : (1 : ℝ) ≤ T) hld'
  have hxσ : (x : ℝ) ^ σ ≤ (x : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx hσ2
  have hxp : 0 ≤ (x : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hd : (x : ℝ) ^ σ / T ≤ (x : ℝ) ^ (1 / 2 : ℝ) / T :=
    div_le_div_of_nonneg_right hxσ hT0.le
  have hle : C₀ * (L ^ 3 + L ^ 2 / δ) + 1 ≤ (C₀ + 1) * (L ^ 3 + L ^ 2 / δ) := by
    nlinarith [hC₀.le, hM1]
  calc ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖
      ≤ (C₀ * (L ^ 3 + L ^ 2 / δ) + 1) * ((x : ℝ) ^ σ / T) := hp
    _ ≤ (C₀ + 1) * (L ^ 3 + L ^ 2 / δ) * ((x : ℝ) ^ (1 / 2 : ℝ) / T) := by
        have h0 : 0 ≤ (x : ℝ) ^ σ / T := div_nonneg (Real.rpow_nonneg hx0.le σ) hT0.le
        calc (C₀ * (L ^ 3 + L ^ 2 / δ) + 1) * ((x : ℝ) ^ σ / T)
            ≤ ((C₀ + 1) * (L ^ 3 + L ^ 2 / δ)) * ((x : ℝ) ^ (1 / 2 : ℝ) / T) :=
              mul_le_mul hle hd h0 (by positivity)
          _ = (C₀ + 1) * (L ^ 3 + L ^ 2 / δ) * ((x : ℝ) ^ (1 / 2 : ℝ) / T) := by ring

/-- Pointwise kernel bound on `σ ∈ [1/2, 5/8]` at a good height, in `δ`-form. -/
theorem psiIntF1_mid_delta_pointwise (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T δ : ℝ, 1 ≤ x → 5 ≤ T → 0 < δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → σ ≤ (5 / 8 : ℝ) →
        ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
          C * ((Real.log (T + 3) + 1) ^ 3 + (Real.log (T + 3) + 1) ^ 2 / δ) *
            ((x : ℝ) ^ (5 / 8 : ℝ) / T) := by
  obtain ⟨C₀, hC₀, h₀⟩ := zeta1_logDeriv_goodHeight_delta h
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro x T δ hx hT hδ0 hgap σ hσ1 hσ2
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set L : ℝ := Real.log (T + 3) + 1 with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    simp only [hL]; linarith
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have hM1 : 1 ≤ L ^ 3 + L ^ 2 / δ := by
    have : 0 ≤ L ^ 2 / δ := div_nonneg (pow_nonneg (by linarith) 2) hδ0.le
    linarith
  have hld := h₀ T δ hT hδ0 hgap σ hσ1 hσ2
  have hld' : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
      C₀ * (L ^ 3 + L ^ 2 / δ) := by simpa only [hL] using hld
  have hp := psiIntF1_line_le_of_logDeriv hx0 (by linarith : (1 : ℝ) ≤ T) hld'
  have hxσ : (x : ℝ) ^ σ ≤ (x : ℝ) ^ (5 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx hσ2
  have hxp : 0 ≤ (x : ℝ) ^ (5 / 8 : ℝ) := Real.rpow_nonneg hx0.le _
  have hd : (x : ℝ) ^ σ / T ≤ (x : ℝ) ^ (5 / 8 : ℝ) / T :=
    div_le_div_of_nonneg_right hxσ hT0.le
  have hle : C₀ * (L ^ 3 + L ^ 2 / δ) + 1 ≤ (C₀ + 1) * (L ^ 3 + L ^ 2 / δ) := by
    nlinarith [hC₀.le, hM1]
  calc ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖
      ≤ (C₀ * (L ^ 3 + L ^ 2 / δ) + 1) * ((x : ℝ) ^ σ / T) := hp
    _ ≤ (C₀ + 1) * (L ^ 3 + L ^ 2 / δ) * ((x : ℝ) ^ (5 / 8 : ℝ) / T) := by
        have h0 : 0 ≤ (x : ℝ) ^ σ / T := div_nonneg (Real.rpow_nonneg hx0.le σ) hT0.le
        calc (C₀ * (L ^ 3 + L ^ 2 / δ) + 1) * ((x : ℝ) ^ σ / T)
            ≤ ((C₀ + 1) * (L ^ 3 + L ^ 2 / δ)) * ((x : ℝ) ^ (5 / 8 : ℝ) / T) :=
              mul_le_mul hle hd h0 (by positivity)
          _ = (C₀ + 1) * (L ^ 3 + L ^ 2 / δ) * ((x : ℝ) ^ (5 / 8 : ℝ) / T) := by ring

/-- **Top/bottom edge bound for the far-left contour `Re ∈ [-3/2, 1/8]`.**

For `-3/2 ≤ a ≤ 1/8`, `5/8 ≤ b ≤ 2`, `T ≥ 5`, a good height with gap `δ`, and `K ≥ 1` with
`1 ≤ K·L·δ` (`L = log(T+3)+1`), the horizontal edge integral of the Perron kernel satisfies
`‖edgeT‖ ≤ C·K·L³·(x^b/T)`: the `K`-factor absorbs the `1/δ` of the middle-strip bound
(`L³ + L²/δ ≤ (K+1)L³`). -/
theorem edgeT_bound_neg (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x a b T δ K : ℝ), 1 ≤ x → -(3 / 2 : ℝ) ≤ a → a ≤ (1 / 8 : ℝ) →
      (5 / 8 : ℝ) ≤ b → b ≤ 2 → 5 ≤ T → 0 < δ → 1 ≤ K →
      1 ≤ K * (Real.log (T + 3) + 1) * δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ‖edgeT a b T (psiIntF1 x)‖ ≤
        C * K * ((Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ b / T)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := psiIntF1_negStrip_pointwise h
  obtain ⟨C₂, hC₂, h₂⟩ := psiIntF1_farleft_pointwise_fixed h
  obtain ⟨C₃, hC₃, h₃⟩ := psiIntF1_leftmid_delta_pointwise h
  obtain ⟨C₄, hC₄, h₄⟩ := psiIntF1_mid_delta_pointwise h
  obtain ⟨C₅, hC₅, h₅⟩ := edge_horiz_right_bound h
  set Cc : ℝ := (C₁ + (5/8)*C₂ + (3/8)*C₃ + (1/8)*C₄ + (11/8)*C₅) + ((3/8)*C₃ + (1/8)*C₄) + 1 with hCc
  refine ⟨Cc + C₁ + 1, by positivity, ?_⟩

  intro x a b T δ K hx ha ha8 hb1 hb2 hT hδ0 hK1 hKδ hgap
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set L : ℝ := Real.log (T + 3) + 1 with hL
  set X : ℝ := (x : ℝ) ^ b with hX
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    simp only [hL]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL0 3
  have hX0 : 0 ≤ X := by rw [hX]; exact Real.rpow_nonneg hx0.le b
  have hXt : 0 ≤ X / T := div_nonneg hX0 hT0.le
  have hP : 0 ≤ L ^ 3 * (X / T) := mul_nonneg hL3 hXt
  have hQ : 0 ≤ (L ^ 2 / δ) * (X / T) :=
    mul_nonneg (div_nonneg (pow_nonneg hL0 2) hδ0.le) hXt
  have hpowc : ∀ c : ℝ, c ≤ b → (x : ℝ) ^ c ≤ X := by
    intro c hc; rw [hX]; exact Real.rpow_le_rpow_of_exponent_le hx hc
  have key3 : ∀ c : ℝ, c ≤ b → ∀ C : ℝ, 0 ≤ C →
      C * L ^ 3 * ((x : ℝ) ^ c / T) ≤ C * (L ^ 3 * (X / T)) := by
    intro c hc C hC
    have h1 : L ^ 3 * ((x : ℝ) ^ c / T) ≤ L ^ 3 * (X / T) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hpowc c hc) hT0.le) hL3
    calc C * L ^ 3 * ((x : ℝ) ^ c / T) = C * (L ^ 3 * ((x : ℝ) ^ c / T)) := by ring
      _ ≤ C * (L ^ 3 * (X / T)) := mul_le_mul_of_nonneg_left h1 hC
  have key2 : ∀ c : ℝ, c ≤ b → ∀ C : ℝ, 0 ≤ C →
      C * (L ^ 2 / δ) * ((x : ℝ) ^ c / T) ≤ C * ((L ^ 2 / δ) * (X / T)) := by
    intro c hc C hC
    have h1 : (L ^ 2 / δ) * ((x : ℝ) ^ c / T) ≤ (L ^ 2 / δ) * (X / T) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hpowc c hc) hT0.le)
        (div_nonneg (pow_nonneg hL0 2) hδ0.le)
    calc C * (L ^ 2 / δ) * ((x : ℝ) ^ c / T)
        = C * ((L ^ 2 / δ) * ((x : ℝ) ^ c / T)) := by ring
      _ ≤ C * ((L ^ 2 / δ) * (X / T)) := mul_le_mul_of_nonneg_left h1 hC
  set F : ℝ → ℂ := fun σ => psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ)) with hF
  have hInt : ∀ p q : ℝ, IntervalIntegrable F volume p q := fun p q =>
    psiIntF1_intervalIntegrable_line hx0 hT hδ0 hgap p q
  have hEdge : edgeT a b T (psiIntF1 x) = ∫ σ in a..b, F σ := by
    rw [edgeT]
    apply intervalIntegral.integral_congr
    intro σ _
    show psiIntF1 x ((σ : ℂ) + ((wRect b T).im : ℂ) * Complex.I) = F σ
    rw [hF]
    congr 1
    rw [wRect_im, mul_comm]
  -- the part from `a' ≥ -1/2` up to `b`
  have hmid : ∀ a' : ℝ, -(1 / 2) ≤ a' → a' ≤ 1 / 8 →
      ‖∫ σ in a'..b, F σ‖ ≤
        (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) * (L ^ 3 * (X / T))
        + (C₃ * (3/8) + C₄ * (1/8)) * ((L ^ 2 / δ) * (X / T)) := by
    intro a' ha' ha'8
    have hpt1 : ∀ σ ∈ Set.uIoc a' (1/8),
        ‖F σ‖ ≤ C₂ * L ^ 3 * ((x : ℝ) ^ (1/8 : ℝ) / T) := by
      intro σ hσ
      rw [Set.uIoc_of_le ha'8] at hσ
      have hσ1 : -(1 / 2 : ℝ) ≤ σ := le_trans ha' (le_of_lt hσ.1)
      have hb := h₂ x T hx hT σ hσ1 hσ.2
      simpa only [hF, ← hL] using hb
    have hpt2 : ∀ σ ∈ Set.uIoc (1/8) (1/2),
        ‖F σ‖ ≤ C₃ * (L ^ 3 + L ^ 2 / δ) * ((x : ℝ) ^ (1/2 : ℝ) / T) := by
      intro σ hσ
      rw [Set.uIoc_of_le (by norm_num : (1/8 : ℝ) ≤ 1/2)] at hσ
      have hb := h₃ x T δ hx hT hδ0 hgap σ (le_of_lt hσ.1) hσ.2
      simpa only [hF, ← hL] using hb
    have hpt3 : ∀ σ ∈ Set.uIoc (1/2) (5/8),
        ‖F σ‖ ≤ C₄ * (L ^ 3 + L ^ 2 / δ) * ((x : ℝ) ^ (5/8 : ℝ) / T) := by
      intro σ hσ
      rw [Set.uIoc_of_le (by norm_num : (1/2 : ℝ) ≤ 5/8)] at hσ
      have hb := h₄ x T δ hx hT hδ0 hgap σ (le_of_lt hσ.1) hσ.2
      simpa only [hF, ← hL] using hb
    have hA1 := intervalIntegral.norm_integral_le_of_norm_le_const hpt1
    have hA2 := intervalIntegral.norm_integral_le_of_norm_le_const hpt2
    have hA3 := intervalIntegral.norm_integral_le_of_norm_le_const hpt3
    have hw1 : |(1/8 : ℝ) - a'| ≤ 5/8 := by rw [abs_le]; constructor <;> linarith
    have habs2 : |(1/2 : ℝ) - 1/8| = 3/8 := by norm_num
    have habs3 : |(5/8 : ℝ) - 1/2| = 1/8 := by norm_num
    have hB1 : ‖∫ σ in a'..(1/8), F σ‖ ≤ (5/8) * (C₂ * (L ^ 3 * (X / T))) := by
      have hC0 : 0 ≤ C₂ * L ^ 3 * ((x : ℝ) ^ (1/8 : ℝ) / T) :=
        mul_nonneg (mul_nonneg hC₂.le hL3) (div_nonneg (Real.rpow_nonneg hx0.le _) hT0.le)
      have hstep : C₂ * L ^ 3 * ((x : ℝ) ^ (1/8 : ℝ) / T) * |(1/8 : ℝ) - a'|
          ≤ C₂ * (L ^ 3 * (X / T)) * (5/8) :=
        mul_le_mul (key3 (1/8) (by linarith) C₂ hC₂.le) hw1 (abs_nonneg _)
          (mul_nonneg hC₂.le hP)
      calc ‖∫ σ in a'..(1/8), F σ‖
          ≤ C₂ * L ^ 3 * ((x : ℝ) ^ (1/8 : ℝ) / T) * |(1/8 : ℝ) - a'| := hA1
        _ ≤ C₂ * (L ^ 3 * (X / T)) * (5/8) := hstep
        _ = (5/8) * (C₂ * (L ^ 3 * (X / T))) := by ring
    have hB2 : ‖∫ σ in (1/8)..(1/2), F σ‖
        ≤ (3/8) * (C₃ * (L ^ 3 * (X / T))) + (3/8) * (C₃ * ((L ^ 2 / δ) * (X / T))) := by
      have hA2' : ‖∫ σ in (1/8)..(1/2), F σ‖
          ≤ C₃ * (L ^ 3 + L ^ 2 / δ) * ((x : ℝ) ^ (1/2 : ℝ) / T) * (3/8) := by
        have hh := hA2
        rwa [habs2] at hh
      have e1 : C₃ * (L ^ 3 + L ^ 2 / δ) * ((x : ℝ) ^ (1/2 : ℝ) / T) * (3/8)
          = (3/8) * (C₃ * L ^ 3 * ((x : ℝ) ^ (1/2 : ℝ) / T))
            + (3/8) * (C₃ * (L ^ 2 / δ) * ((x : ℝ) ^ (1/2 : ℝ) / T)) := by ring
      have h1 := key3 (1/2) (by linarith) C₃ hC₃.le
      have h2 := key2 (1/2) (by linarith) C₃ hC₃.le
      linarith [hA2', e1, h1, h2]
    have hB3 : ‖∫ σ in (1/2)..(5/8), F σ‖
        ≤ (1/8) * (C₄ * (L ^ 3 * (X / T))) + (1/8) * (C₄ * ((L ^ 2 / δ) * (X / T))) := by
      have hA3' : ‖∫ σ in (1/2)..(5/8), F σ‖
          ≤ C₄ * (L ^ 3 + L ^ 2 / δ) * ((x : ℝ) ^ (5/8 : ℝ) / T) * (1/8) := by
        have hh := hA3
        rwa [habs3] at hh
      have e1 : C₄ * (L ^ 3 + L ^ 2 / δ) * ((x : ℝ) ^ (5/8 : ℝ) / T) * (1/8)
          = (1/8) * (C₄ * L ^ 3 * ((x : ℝ) ^ (5/8 : ℝ) / T))
            + (1/8) * (C₄ * (L ^ 2 / δ) * ((x : ℝ) ^ (5/8 : ℝ) / T)) := by ring
      have h1 := key3 (5/8) hb1 C₄ hC₄.le
      have h2 := key2 (5/8) hb1 C₄ hC₄.le
      linarith [hA3', e1, h1, h2]
    have hB4 : ‖∫ σ in (5/8)..b, F σ‖ ≤ (11/8) * (C₅ * (L ^ 3 * (X / T))) := by
      have hTabs : |T| = T := abs_of_nonneg hT0.le
      have hm := h₅ x b T hx hb1 hb2 (by rw [hTabs]; linarith)
      rw [hTabs] at hm
      have hm' : ‖∫ σ in (5/8)..b, F σ‖ ≤ C₅ * L ^ 3 * ((x : ℝ) ^ b * (b - 5 / 8) / T) := by
        simpa only [hF, ← hL] using hm
      rw [← hX] at hm'
      have hstep : C₅ * L ^ 3 * (X * (b - 5 / 8) / T) ≤ (11/8) * (C₅ * (L ^ 3 * (X / T))) := by
        have hC0 : 0 ≤ C₅ * (L ^ 3 * (X / T)) :=
          mul_nonneg hC₅.le (mul_nonneg hL3 hXt)
        have e : C₅ * L ^ 3 * (X * (b - 5 / 8) / T)
            = (C₅ * (L ^ 3 * (X / T))) * (b - 5 / 8) := by ring
        rw [e]
        calc (C₅ * (L ^ 3 * (X / T))) * (b - 5 / 8)
            ≤ (C₅ * (L ^ 3 * (X / T))) * (11/8) :=
              mul_le_mul_of_nonneg_left (by linarith) hC0
          _ = (11/8) * (C₅ * (L ^ 3 * (X / T))) := by ring
      exact le_trans hm' hstep
    have hsplit1 : (∫ σ in a'..b, F σ) = (∫ σ in a'..(1/8), F σ) + ((∫ σ in (1/8)..(1/2), F σ)
        + ((∫ σ in (1/2)..(5/8), F σ) + (∫ σ in (5/8)..b, F σ))) := by
      have e1 := intervalIntegral.integral_add_adjacent_intervals (hInt a' (1/8)) (hInt (1/8) b)
      have e2 := intervalIntegral.integral_add_adjacent_intervals (hInt (1/8) (1/2)) (hInt (1/2) b)
      have e3 := intervalIntegral.integral_add_adjacent_intervals (hInt (1/2) (5/8)) (hInt (5/8) b)
      rw [← e1, ← e2, ← e3]
    rw [hsplit1]
    have hsum : ‖(∫ σ in a'..(1/8), F σ) + ((∫ σ in (1/8)..(1/2), F σ)
        + ((∫ σ in (1/2)..(5/8), F σ) + (∫ σ in (5/8)..b, F σ)))‖
        ≤ (5/8) * (C₂ * (L ^ 3 * (X / T))) + ((3/8) * (C₃ * (L ^ 3 * (X / T)))
            + (3/8) * (C₃ * ((L ^ 2 / δ) * (X / T))))
          + ((1/8) * (C₄ * (L ^ 3 * (X / T))) + (1/8) * (C₄ * ((L ^ 2 / δ) * (X / T))))
          + (11/8) * (C₅ * (L ^ 3 * (X / T))) := by
      have h1 := norm_add_le (∫ σ in a'..(1/8), F σ)
        ((∫ σ in (1/8)..(1/2), F σ) + ((∫ σ in (1/2)..(5/8), F σ) + (∫ σ in (5/8)..b, F σ)))
      have h2 := norm_add_le (∫ σ in (1/8)..(1/2), F σ)
        ((∫ σ in (1/2)..(5/8), F σ) + (∫ σ in (5/8)..b, F σ))
      have h3 := norm_add_le (∫ σ in (1/2)..(5/8), F σ) (∫ σ in (5/8)..b, F σ)
      linarith [h1, h2, h3, hB1, hB2, hB3, hB4]
    have htarget : (5/8) * (C₂ * (L ^ 3 * (X / T))) + ((3/8) * (C₃ * (L ^ 3 * (X / T)))
            + (3/8) * (C₃ * ((L ^ 2 / δ) * (X / T))))
          + ((1/8) * (C₄ * (L ^ 3 * (X / T))) + (1/8) * (C₄ * ((L ^ 2 / δ) * (X / T))))
          + (11/8) * (C₅ * (L ^ 3 * (X / T)))
        = (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) * (L ^ 3 * (X / T))
          + (C₃ * (3/8) + C₄ * (1/8)) * ((L ^ 2 / δ) * (X / T)) := by ring
    linarith [hsum, htarget]
  -- the final conversion
  have hQeq : (L ^ 2 / δ) * (X / T) = (1 / (L * δ)) * (L ^ 3 * (X / T)) := by
    field_simp
  have hLd : 0 < L * δ := mul_pos (by linarith) hδ0
  have hinv : 1 / (L * δ) ≤ K := by
    rw [div_le_iff₀ hLd]; linarith [hKδ]
  have hKP : (1 / (L * δ)) * (L ^ 3 * (X / T)) ≤ K * (L ^ 3 * (X / T)) :=
    mul_le_mul_of_nonneg_right hinv hP
  have hfin : ∀ Z : ℝ, Z ≤ (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) * (L ^ 3 * (X / T))
        + (C₃ * (3/8) + C₄ * (1/8)) * ((L ^ 2 / δ) * (X / T)) →
      Z ≤ Cc * K * (L ^ 3 * (X / T)) := by
    intro Z hZ
    rw [hQeq] at hZ
    have hcA : 0 ≤ C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8) := by
      linarith [hC₂.le, hC₃.le, hC₄.le, hC₅.le]
    have hcB : 0 ≤ C₃ * (3/8) + C₄ * (1/8) := by linarith [hC₃.le, hC₄.le]
    have hA : (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) * (L ^ 3 * (X / T))
        ≤ (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) * (K * (L ^ 3 * (X / T))) := by
      refine mul_le_mul_of_nonneg_left ?_ hcA
      nlinarith [hK1, hP]
    have hB : (C₃ * (3/8) + C₄ * (1/8)) * ((1 / (L * δ)) * (L ^ 3 * (X / T)))
        ≤ (C₃ * (3/8) + C₄ * (1/8)) * (K * (L ^ 3 * (X / T))) :=
      mul_le_mul_of_nonneg_left hKP hcB
    have hstep : (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) * (K * (L ^ 3 * (X / T)))
        + (C₃ * (3/8) + C₄ * (1/8)) * (K * (L ^ 3 * (X / T)))
        ≤ Cc * (K * (L ^ 3 * (X / T))) := by
      have hcoef : (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) + (C₃ * (3/8) + C₄ * (1/8))
          ≤ Cc := by rw [hCc]; linarith [hC₁.le]
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by linarith : (0:ℝ) ≤ K) hP)
    have hZ' : Z ≤ (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) * (K * (L ^ 3 * (X / T)))
        + (C₃ * (3/8) + C₄ * (1/8)) * (K * (L ^ 3 * (X / T))) := by
      have e : (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) * (L ^ 3 * (X / T))
          + (C₃ * (3/8) + C₄ * (1/8)) * ((1 / (L * δ)) * (L ^ 3 * (X / T)))
          = (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) * (L ^ 3 * (X / T))
          + (C₃ * (3/8) + C₄ * (1/8)) * ((1 / (L * δ)) * (L ^ 3 * (X / T))) := rfl
      calc Z ≤ (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) * (L ^ 3 * (X / T))
            + (C₃ * (3/8) + C₄ * (1/8)) * ((1 / (L * δ)) * (L ^ 3 * (X / T))) := hZ
        _ ≤ (C₂ * (5/8) + C₃ * (3/8) + C₄ * (1/8) + C₅ * (11/8)) * (K * (L ^ 3 * (X / T)))
            + (C₃ * (3/8) + C₄ * (1/8)) * (K * (L ^ 3 * (X / T))) := add_le_add hA hB
    calc Z ≤ _ := hZ'
      _ ≤ Cc * (K * (L ^ 3 * (X / T))) := hstep
      _ = Cc * K * (L ^ 3 * (X / T)) := by ring
  by_cases hcase : -(1 / 2 : ℝ) ≤ a
  · rw [hEdge]
    have hh := hfin _ (hmid a hcase ha8)
    have hKP : 0 ≤ K * (L ^ 3 * (X / T)) := mul_nonneg (by linarith : (0:ℝ) ≤ K) hP
    have hle : Cc ≤ Cc + C₁ + 1 := by linarith [hC₁.le]
    have hstep := mul_le_mul_of_nonneg_right hle hKP
    have hh' : ‖∫ σ in a..b, F σ‖ ≤ Cc * (K * (L ^ 3 * (X / T))) := by
      have := hh
      rwa [mul_assoc] at this
    have heq : (Cc + C₁ + 1) * K * (L ^ 3 * (X / T))
        = (Cc + C₁ + 1) * (K * (L ^ 3 * (X / T))) := by ring
    rw [heq]
    linarith [hh', hstep]
  · have hlt : a < -(1 / 2 : ℝ) := lt_of_not_ge hcase
    have hB0 : ‖∫ σ in a..(-(1/2)), F σ‖ ≤ C₁ * (L ^ 3 * (X / T)) := by
      have hpt : ∀ σ ∈ Set.uIoc a (-(1/2)),
          ‖F σ‖ ≤ C₁ * L ^ 3 * ((x : ℝ) ^ (-(1/2) : ℝ) / T) := by
        intro σ hσ
        rw [Set.uIoc_of_le (by linarith : a ≤ -(1/2))] at hσ
        have hσ1 : -(3 / 2 : ℝ) ≤ σ := le_trans ha (le_of_lt hσ.1)
        have hb := h₁ x T hx hT σ hσ1 hσ.2
        simpa only [hF, ← hL] using hb
      have hA := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      have hw : |(-(1/2) : ℝ) - a| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have hstep : C₁ * L ^ 3 * ((x : ℝ) ^ (-(1/2) : ℝ) / T) * |(-(1/2) : ℝ) - a|
          ≤ C₁ * (L ^ 3 * (X / T)) * 1 :=
        mul_le_mul (key3 (-(1/2)) (by linarith) C₁ hC₁.le) hw (abs_nonneg _)
          (mul_nonneg hC₁.le hP)
      calc ‖∫ σ in a..(-(1/2)), F σ‖
          ≤ C₁ * L ^ 3 * ((x : ℝ) ^ (-(1/2) : ℝ) / T) * |(-(1/2) : ℝ) - a| := hA
        _ ≤ C₁ * (L ^ 3 * (X / T)) * 1 := hstep
        _ = C₁ * (L ^ 3 * (X / T)) := by ring
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hInt a (-(1/2))) (hInt (-(1/2)) b)
    have hm := hmid (-(1/2)) (le_refl _) (by norm_num)
    rw [hEdge, ← hsplit]
    have hKP : 0 ≤ K * (L ^ 3 * (X / T)) := mul_nonneg (by linarith : (0:ℝ) ≤ K) hP
    have hB0' : ‖∫ σ in a..(-(1/2)), F σ‖ ≤ C₁ * (K * (L ^ 3 * (X / T))) := by
      refine le_trans hB0 ?_
      calc C₁ * (L ^ 3 * (X / T)) = C₁ * (1 * (L ^ 3 * (X / T))) := by ring
        _ ≤ C₁ * (K * (L ^ 3 * (X / T))) :=
            mul_le_mul_of_nonneg_left (by nlinarith [hK1, hP]) hC₁.le
    have hm' : ‖∫ σ in (-(1/2))..b, F σ‖ ≤ Cc * (K * (L ^ 3 * (X / T))) := by
      have := hfin _ hm
      rwa [mul_assoc] at this
    have h1 := norm_add_le (∫ σ in a..(-(1/2)), F σ) (∫ σ in (-(1/2))..b, F σ)
    have hsum2 : ‖(∫ σ in a..(-(1/2)), F σ) + (∫ σ in (-(1/2))..b, F σ)‖
        ≤ (C₁ + Cc) * (K * (L ^ 3 * (X / T))) := by
      have e : C₁ * (K * (L ^ 3 * (X / T))) + Cc * (K * (L ^ 3 * (X / T)))
          = (C₁ + Cc) * (K * (L ^ 3 * (X / T))) := by ring
      linarith [h1, hB0', hm', e.le, e.ge]
    have hCC : C₁ + Cc ≤ Cc + C₁ + 1 := by linarith
    have hfinal := mul_le_mul_of_nonneg_right hCC hKP
    have heq : (Cc + C₁ + 1) * K * (L ^ 3 * (X / T))
        = (Cc + C₁ + 1) * (K * (L ^ 3 * (X / T))) := by ring
    rw [heq]
    linarith [hsum2, hfinal]


end Commons.NumberTheory.Zeta
end


-- ==== begin p3_perronFarLeft ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# P4′ for the far-left contour: the truncated explicit formula with the `-log(2π)` constant

`rectInt_psiIntF1_engineSum_farLeft` (p3_farLeft) is the rectangle identity at the left edge
`Re = a ∈ [-1/2, 0)`; on the right edge (`Re = b > 1`) the ζ₁-form integrand coincides with
the von-Mangoldt `LSeries` integrand of `chebyshevPsi_truncatedPerron`.  Solving the
rectangle identity for the right edge gives the truncated explicit formula in the form used
by the *integrated* (Route B) argument: the pole at `s = 0` contributes the classical
constant `-log(2π)`, and the three other sides contribute the (norm-bounded) side integrals.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section
set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.Zeta

/-- **The algebra part of the truncated explicit formula at the far-left contour.** -/
theorem perron_raw_sub_zero_sum_bound_farLeft (h : RiemannHypothesis) {R a b Tp x : ℝ}
    (hR : 0 ≤ R) (hx : 0 < x) (ha : -(3 / 2 : ℝ) ≤ a) (ha0 : a < 0) (h1b : 1 < b)
    (hTp : 0 < Tp)
    (hrect : closedContourRect a b Tp ⊆ Metric.closedBall (0 : ℂ) R)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp) :
    ‖edgeR b Tp (psiIntF1 x) * ((2 : ℂ) * (Real.pi : ℂ))⁻¹ -
        ((x : ℂ) - Complex.log (2 * (Real.pi : ℂ)) -
          ∑ ρ ∈ zRectZeros hR a b Tp, (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ)‖ ≤
      (‖edgeB a b Tp (psiIntF1 x)‖ + ‖edgeT a b Tp (psiIntF1 x)‖ +
        ‖edgeL a Tp (psiIntF1 x)‖) * ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ := by
  have h4 := rectInt_psiIntF1_engineSum_farLeft h hR hx ha ha0 h1b hTp hrect hgood
  have hdec := rectInt_decompose a b Tp (psiIntF1 x)
  rw [hdec] at h4
  let K : ℂ := (2 : ℂ) * (Real.pi : ℂ) * Complex.I
  let c : ℂ := (x : ℂ) - Complex.log (2 * (Real.pi : ℂ)) -
      ∑ ρ ∈ zRectZeros hR a b Tp, (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  let Bv : ℂ := edgeB a b Tp (psiIntF1 x)
  let Tv : ℂ := edgeT a b Tp (psiIntF1 x)
  let Rv : ℂ := edgeR b Tp (psiIntF1 x)
  let Lv : ℂ := edgeL a Tp (psiIntF1 x)
  have h4' : Bv - Tv + Complex.I • Rv - Complex.I • Lv = c * K := by
    simpa [K, c, Bv, Tv, Rv, Lv] using h4
  have hRI : Complex.I • Rv = K * c - Bv + Tv + Complex.I • Lv := by
    calc
      Complex.I • Rv = (Bv - Tv + Complex.I • Rv - Complex.I • Lv) - (Bv - Tv - Complex.I • Lv) := by ring
      _ = K * c - Bv + Tv + Complex.I • Lv := by rw [h4']; ring
  have hRI'' : Rv * Complex.I = K * c - Bv + Tv + Complex.I • Lv := by
    calc
      Rv * Complex.I = Complex.I • Rv := by ring
      _ = K * c - Bv + Tv + Complex.I • Lv := hRI
  have hR : Rv = (K * c - Bv + Tv + Complex.I • Lv) / Complex.I := by
    have hI : Complex.I ≠ 0 := by simp
    calc
      Rv = (Rv * Complex.I) / Complex.I := by field_simp [hI]
      _ = (K * c - Bv + Tv + Complex.I • Lv) / Complex.I := by rw [hRI'']
  have hmain : ‖Rv * ((2 : ℂ) * (Real.pi : ℂ))⁻¹ - c‖ ≤
      (‖Bv‖ + ‖Tv‖ + ‖Lv‖) * ‖K⁻¹‖ := by
    have hI : Complex.I ≠ 0 := by simp
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    have hpi : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hK : K ≠ 0 := by
      dsimp [K]
      exact mul_ne_zero (mul_ne_zero htwo hpi) hI
    have hpi2 : ((2 : ℂ) * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero htwo hpi
    have hstep : Rv * ((2 : ℂ) * (Real.pi : ℂ))⁻¹ - c =
        (- Bv + Tv + Complex.I • Lv) * K⁻¹ := by
      rw [hR]
      dsimp [K, c]
      field_simp [hI, htwo, hpi]
      ring
    rw [hstep]
    calc
      ‖(- Bv + Tv + Complex.I • Lv) * K⁻¹‖
          = ‖- Bv + Tv + Complex.I • Lv‖ * ‖K⁻¹‖ := by rw [norm_mul]
      _ ≤ (‖Bv‖ + ‖Tv‖ + ‖Lv‖) * ‖K⁻¹‖ := by
            have h1 : ‖-Bv + Tv + Complex.I • Lv‖ ≤ ‖-Bv + Tv‖ + ‖Lv‖ := by
              have h1' : ‖-Bv + Tv + Complex.I • Lv‖ ≤ ‖-Bv + Tv‖ + ‖Complex.I • Lv‖ :=
                norm_add_le (-Bv + Tv) (Complex.I • Lv)
              have h2' : ‖Complex.I • Lv‖ = ‖Lv‖ := by simp
              linarith
            have h1a : ‖-Bv + Tv‖ ≤ ‖-Bv‖ + ‖Tv‖ := norm_add_le (-Bv) Tv
            have h1c : ‖-Bv‖ = ‖Bv‖ := by rw [norm_neg]
            have hS : ‖-Bv + Tv + Complex.I • Lv‖ ≤ ‖Bv‖ + ‖Tv‖ + ‖Lv‖ := by
              linarith
            have hm : 0 ≤ ‖K⁻¹‖ := norm_nonneg _
            nlinarith
  simpa [K, c, Bv, Tv, Rv, Lv] using hmain



end Commons.NumberTheory.Zeta
end


-- ==== begin p3_heightFarLeftNeg ====

-- PORT-CHECKLIST: before publishing a lemma from this file into commons, read
-- Submission/Work/NumberTheory/Zeta/PORT_SPEC.md and PORT_CHECKLIST.md and publish the
-- listed public API as well (children must expose these non-privately).

/-!
# The truncated explicit formula at the far-left contour `Re = -3/2`

This is the refined far-left formula of `p3_heightFarLeftRefined` with the left edge pushed
down to `Re = -3/2` (so that the left-edge contribution `x^{-3/2}·polylog(T)` is negligible
after integration against `k(t) = (log t+1)/(t²log²t)`), and with the top/bottom edge bound
`edgeT_bound_neg` carrying the multiplicative `K` (which absorbs the good-height gap `1/δ`).

The pointwise error is
`C·K·x·L³/T + C₂·L·G_T(x) + IND(x) + D·x^{−3/2}·L⁴`, with `L = log(T+3)+1`,
`G_T(x) = min 1 (2x/(T|x−⌊x⌋|)) + min 1 (2x/(T|x−⌊x⌋−1|))`, `IND` supported on `ℤ`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section
set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.Zeta

/-- Auxiliary form: the refined truncated Perron estimate is taken as a hypothesis. -/
theorem chebyshevPsi_at_height_farLeft_neg_aux (h : RiemannHypothesis) (Cp : ℝ)
    (hCppos : 0 < Cp)
    (hCp : ∀ x : ℝ, 4 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖(Chebyshev.psi x : ℂ) - (1 / (2 * Real.pi)) *
          (∫ (t : ℝ) in -T..T,
            (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) *
              (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
              (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        Cp * (x * (Real.log x) ^ 2 / T + Real.log x *
          (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
           min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)))) +
        (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0)) :
    ∃ C C₂ D : ℝ, 0 < C ∧ 0 < C₂ ∧ 0 < D ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ T δ K : ℝ,
      5 ≤ T → x ≤ T ^ 2 → 0 < δ → 1 ≤ K → 1 ≤ K * (Real.log (T + 3) + 1) * δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ T ∧ ρ.im ≠ -T) →
      ‖(Chebyshev.psi x : ℂ) - ((x : ℂ) - Complex.log (2 * (Real.pi : ℂ)) -
          ∑ ρ ∈ zRectZeros (R := 2 + |T|) (by positivity) (-(3 / 2)) (1 + 1 / Real.log x) T,
            (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ)‖ ≤
        C * (x * (Real.log (T + 3) + 1) ^ 3 / T) * K +
        C₂ * ((Real.log (T + 3) + 1) *
          (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
           min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)))) +
        (if (Nat.floor x : ℝ) = x then 4 * (Real.log (T + 3) + 1) else 0) +
        D * ((x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (T + 3) + 1) ^ 4) := by
  obtain ⟨CT, hCTpos, hCT⟩ := edgeT_bound_neg h
  obtain ⟨CL, hCLpos, hCL⟩ := edgeL_farleft_neg_three_halves_bound h
  refine ⟨Cp + 4 * CT / Real.pi + 1, 2 * Cp + 1, CL / (2 * Real.pi) + 1, ?_, ?_, ?_, ?_⟩
  · have : 0 < 4 * CT / Real.pi := div_pos (by linarith) Real.pi_pos
    linarith
  · linarith
  · have : 0 < CL / (2 * Real.pi) := div_pos hCLpos (by positivity)
    linarith
  · refine ⟨Real.exp 9 + 100, ?_⟩
    intro x hx0 T δ K hT hTx hδ0 hK1 hKδ hgap hgood
    have hexp9 : Real.exp 9 ≤ x := by linarith
    have hx1 : (1 : ℝ) ≤ x :=
      le_trans (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 9)) hexp9
    have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
    have hlog8 : (8 : ℝ) ≤ Real.log x := by
      have h1 : Real.log (Real.exp 9) ≤ Real.log x :=
        Real.log_le_log (Real.exp_pos 9) hexp9
      rw [Real.log_exp] at h1
      linarith
    have hT0 : 0 < T := by linarith
    set L : ℝ := Real.log (T + 3) + 1 with hL
    have hL0 : 0 ≤ L := by
      rw [hL]
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 3)
      linarith
    have hlogx_le : Real.log x ≤ 2 * L := by
      have h1 : Real.log x ≤ Real.log (T ^ 2) := Real.log_le_log hxpos hTx
      have h2 : Real.log (T ^ 2) = 2 * Real.log T := by
        rw [Real.log_pow]; push_cast; ring
      have h3 : Real.log T ≤ Real.log (T + 3) := Real.log_le_log hT0 (by linarith)
      rw [h2] at h1
      rw [hL]
      linarith
    have hLlogx : (Real.log x) ^ 2 ≤ L ^ 3 := by
      have h4 : (4 : ℝ) ≤ L := by linarith [hlogx_le, hlog8]
      have h5 : 0 ≤ L ^ 2 * (L - 4) := mul_nonneg (sq_nonneg L) (by linarith)
      nlinarith [hlogx_le, h4, hL0, h5, sq_nonneg (Real.log x)]
    set Gx : ℝ := min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
      min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)) with hGx
    have hG0 : 0 ≤ Gx := by
      rw [hGx]
      have h2x : 0 ≤ 2 * x := by linarith
      have h1 : 0 ≤ 2 * x / (T * |x - (Nat.floor x : ℝ)|) :=
        div_nonneg h2x (mul_nonneg hT0.le (abs_nonneg _))
      have h2 : 0 ≤ 2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|) :=
        div_nonneg h2x (mul_nonneg hT0.le (abs_nonneg _))
      exact add_nonneg (le_min (by norm_num) h1) (le_min (by norm_num) h2)
    have h1b : 1 < 1 + 1 / Real.log x := by
      have : 0 < 1 / Real.log x := by positivity
      linarith
    have hb2 : 1 + 1 / Real.log x ≤ 2 := by
      have hlog1 : (1 : ℝ) ≤ Real.log x := by linarith
      have h1 : 1 / Real.log x ≤ 1 := by rw [div_le_one (by linarith)]; exact hlog1
      linarith
    have hR : (0 : ℝ) ≤ 2 + |T| := by positivity
    have ha : -(3 / 2 : ℝ) ≤ -(3 / 2) := le_refl _
    have ha0 : (-(3 / 2) : ℝ) < 0 := by norm_num
    have hrect : closedContourRect (-(3 / 2)) (1 + 1 / Real.log x) T ⊆
        Metric.closedBall (0 : ℂ) (2 + |T|) := by
      intro z hz
      have hab : (-(3 / 2) : ℝ) ≤ 1 + 1 / Real.log x := by
        have : 0 < 1 / Real.log x := by positivity
        linarith
      have hTle : -T ≤ T := by linarith
      have hmem := (mem_closedContourRect hab hTle z).mp hz
      obtain ⟨h1, h2, h3, h4⟩ := hmem
      have hre : |z.re| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith
      have him : |z.im| ≤ T := by
        rw [abs_le]; constructor <;> linarith
      have hnorm : ‖z‖ ≤ 2 + |T| := by
        have h1' : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        have hTabs : |T| = T := abs_of_nonneg hT0.le
        rw [hTabs]
        linarith
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hnorm
    have hx4 : (4 : ℝ) ≤ x := by have := Real.exp_pos 9; linarith
    have hP := hCp x hx4 T (by linarith)
    have hE := edgeR_eq_perron_raw x (1 + 1 / Real.log x) T h1b
    rw [← hE] at hP
    have hScal : (1 / (2 * Real.pi)) * edgeR (1 + 1 / Real.log x) T (psiIntF1 x) =
        edgeR (1 + 1 / Real.log x) T (psiIntF1 x) * ((2 : ℂ) * (Real.pi : ℂ))⁻¹ := by
      field_simp [Real.pi_ne_zero]
    rw [hScal] at hP
    have hPR := perron_raw_sub_zero_sum_bound_farLeft h hR hxpos ha ha0 h1b hT0 hrect hgood
    let A : ℂ := (Chebyshev.psi x : ℂ)
    let B : ℂ := edgeR (1 + 1 / Real.log x) T (psiIntF1 x) * ((2 : ℂ) * (Real.pi : ℂ))⁻¹
    let Cc : ℂ := (x : ℂ) - Complex.log (2 * (Real.pi : ℂ)) -
        ∑ ρ ∈ zRectZeros (R := 2 + |T|) hR (-(3 / 2)) (1 + 1 / Real.log x) T,
          (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ
    have hP' : ‖A - B‖ ≤ Cp * (x * (Real.log x) ^ 2 / T + Real.log x * Gx) +
        (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0) := by
      simpa [A, B, hGx] using hP
    have hPR' : ‖B - Cc‖ ≤
        (‖edgeB (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ +
          ‖edgeT (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ +
          ‖edgeL (-(3 / 2)) T (psiIntF1 x)‖) * ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ := by
      simpa [B, Cc] using hPR
    have htri : ‖A - Cc‖ ≤ ‖A - B‖ + ‖B - Cc‖ := by
      calc ‖A - Cc‖ = ‖(A - B) + (B - Cc)‖ := by congr 1; abel
        _ ≤ ‖A - B‖ + ‖B - Cc‖ := norm_add_le (A - B) (B - Cc)
    have hBTn : ‖edgeB (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ =
        ‖edgeT (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ := by
      rw [edgeB_eq_conj_edgeT hxpos, Complex.norm_conj]
    have hsideT : ‖edgeT (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ ≤
        CT * K * (L ^ 3 * ((x : ℝ) ^ (1 + 1 / Real.log x) / T)) := by
      have hh := hCT x (-(3 / 2)) (1 + 1 / Real.log x) T δ K hx1 (by norm_num)
        (by linarith : (-(3 / 2) : ℝ) ≤ 1 / 8) (by linarith) hb2 hT hδ0 hK1 hKδ hgap
      simpa only [hL] using hh
    have hxpow : (x : ℝ) ^ (1 + 1 / Real.log x) ≤ 4 * x := by
      have hlog0 : Real.log x ≠ 0 := by linarith
      have hsplit : (x : ℝ) ^ (1 + 1 / Real.log x) =
          (x : ℝ) ^ (1 : ℝ) * (x : ℝ) ^ (1 / Real.log x) :=
        Real.rpow_add hxpos 1 (1 / Real.log x)
      have hone : (x : ℝ) ^ (1 : ℝ) = x := Real.rpow_one x
      have hexp : (x : ℝ) ^ (1 / Real.log x) = Real.exp 1 := by
        rw [Real.rpow_def_of_pos hxpos]
        congr 1
        field_simp
      rw [hsplit, hone, hexp]
      have h4 : Real.exp 1 ≤ 4 := by
        have := Real.exp_one_lt_d9
        linarith
      nlinarith [Real.exp_pos 1]
    have hsideL : ‖edgeL (-(3 / 2)) T (psiIntF1 x)‖ ≤
        CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (T + 3) + 1) ^ 4 := by
      have hh := hCL x (-(3 / 2)) T hx1 (by norm_num) (by norm_num) hT
      have hEq : edgeL (-(3 / 2)) T (psiIntF1 x) =
          (∫ (y : ℝ) in -T..T,
            (-(logDeriv riemannZeta₁ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ))) *
                ((x : ℂ) ^ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) /
                  ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ))) +
              (x : ℂ) ^ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) /
                (((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) *
                  (((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) - 1)))) := by
        rw [edgeL, zRect_re]
        apply intervalIntegral.integral_congr
        intro y _
        simp only [psiIntF1, mul_comm Complex.I]
      rw [hEq]
      simpa only [hL] using hh
    have h2pi : ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ = 1 / (2 * Real.pi) :=
      norm_inv_two_pi_I
    have hsum : ‖edgeB (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ +
        ‖edgeT (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ +
        ‖edgeL (-(3 / 2)) T (psiIntF1 x)‖ ≤
        2 * (CT * K * (L ^ 3 * (4 * x / T))) + CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4 := by
      have hT4 : CT * K * (L ^ 3 * ((x : ℝ) ^ (1 + 1 / Real.log x) / T)) ≤
          CT * K * (L ^ 3 * (4 * x / T)) := by
        have hdiv : (x : ℝ) ^ (1 + 1 / Real.log x) / T ≤ 4 * x / T :=
          div_le_div_of_nonneg_right (by linarith [hxpow]) hT0.le
        have h1 : L ^ 3 * ((x : ℝ) ^ (1 + 1 / Real.log x) / T) ≤ L ^ 3 * (4 * x / T) :=
          mul_le_mul_of_nonneg_left hdiv (pow_nonneg hL0 3)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hL4 : CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (T + 3) + 1) ^ 4 =
          CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4 := by rw [hL]
      rw [hBTn, hL4]
      linarith
    have hbase : ‖A - Cc‖ ≤ Cp * (x * (Real.log x) ^ 2 / T + Real.log x * Gx) +
        (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0) +
        (2 * (CT * K * (L ^ 3 * (4 * x / T))) + CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) *
          (1 / (2 * Real.pi)) := by
      have h1 := htri
      have h2 := hPR'
      rw [h2pi] at h2
      have h3 : ‖B - Cc‖ ≤ (2 * (CT * K * (L ^ 3 * (4 * x / T))) +
          CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) * (1 / (2 * Real.pi)) :=
        le_trans h2 (mul_le_mul_of_nonneg_right hsum (by positivity))
      linarith
    have hCp0 : 0 ≤ Cp := hCppos.le
    have hCT0 : 0 ≤ CT := hCTpos.le
    have hCL0 : 0 ≤ CL := hCLpos.le
    have hxlog : 0 ≤ (x : ℝ) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hxpos.le _
    have hlogx0 : 0 ≤ Real.log x := by linarith
    have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL0 3
    have hL4nn : 0 ≤ L ^ 4 := pow_nonneg hL0 4
    have hxT : 0 ≤ x / T := div_nonneg hxpos.le hT0.le
    have hxl3 : 0 ≤ x * L ^ 3 / T :=
      div_nonneg (mul_nonneg hxpos.le hL3) hT0.le
    have hxl4 : 0 ≤ (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4 :=
      mul_nonneg (Real.rpow_nonneg hxpos.le _) hL4nn
    have hCLpi : 0 ≤ CL / (2 * Real.pi) := div_nonneg hCL0 (by positivity)
    have hpi4 : 0 ≤ 4 * CT / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
    have hK0 : 0 ≤ K := by linarith
    have hind : (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0) ≤
        (if (Nat.floor x : ℝ) = x then 4 * L else 0) := by
      by_cases hh : (Nat.floor x : ℝ) = x
      · rw [if_pos hh, if_pos hh]; linarith [hlogx_le]
      · rw [if_neg hh, if_neg hh]
    have htermp : Cp * (x * (Real.log x) ^ 2 / T + Real.log x * Gx) ≤
        Cp * (x * L ^ 3 / T) + (2 * Cp) * (L * Gx) := by
      have h1 : x * (Real.log x) ^ 2 / T ≤ x * L ^ 3 / T :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLlogx hxpos.le) hT0.le
      have h2 : Real.log x * Gx ≤ (2 * L) * Gx :=
        mul_le_mul_of_nonneg_right hlogx_le hG0
      have h3 : Cp * (x * (Real.log x) ^ 2 / T + Real.log x * Gx) =
          Cp * (x * (Real.log x) ^ 2 / T) + Cp * (Real.log x * Gx) := by ring
      have h4 : Cp * (x * (Real.log x) ^ 2 / T) ≤ Cp * (x * L ^ 3 / T) :=
        mul_le_mul_of_nonneg_left h1 hCp0
      have h5 : Cp * (Real.log x * Gx) ≤ Cp * ((2 * L) * Gx) :=
        mul_le_mul_of_nonneg_left h2 hCp0
      have h6 : Cp * ((2 * L) * Gx) = (2 * Cp) * (L * Gx) := by ring
      linarith [h3, h4, h5, h6]
    have hP1 : 0 ≤ x * L ^ 3 / T := hxl3
    have hPK : Cp * (x * L ^ 3 / T) ≤ Cp * (x * L ^ 3 / T) * K := by
      have h1 : (x * L ^ 3 / T) ≤ K * (x * L ^ 3 / T) := by
        have := mul_le_mul_of_nonneg_right hK1 hP1
        simpa using this
      calc Cp * (x * L ^ 3 / T) ≤ Cp * (K * (x * L ^ 3 / T)) :=
            mul_le_mul_of_nonneg_left h1 hCp0
        _ = Cp * (x * L ^ 3 / T) * K := by ring
    have hterm2 : (2 * (CT * K * (L ^ 3 * (4 * x / T)))) * (1 / (2 * Real.pi)) ≤
        (4 * CT / Real.pi) * (x * L ^ 3 / T) * K := by
      apply le_of_eq
      field_simp [Real.pi_ne_zero, (by linarith : T ≠ 0)]
      try ring
    have hterm3 : (CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) * (1 / (2 * Real.pi)) ≤
        (CL / (2 * Real.pi)) * ((x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) := by
      apply le_of_eq
      field_simp [Real.pi_ne_zero] <;> ring
    have hfin : Cp * (x * (Real.log x) ^ 2 / T + Real.log x * Gx) +
        (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0) +
        (2 * (CT * K * (L ^ 3 * (4 * x / T))) + CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) *
          (1 / (2 * Real.pi)) ≤
        (Cp + 4 * CT / Real.pi + 1) * (x * L ^ 3 / T) * K + (2 * Cp + 1) * (L * Gx) +
        (if (Nat.floor x : ℝ) = x then 4 * L else 0) +
        (CL / (2 * Real.pi) + 1) * ((x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) := by
      have hsplit : (2 * (CT * K * (L ^ 3 * (4 * x / T))) + CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) *
          (1 / (2 * Real.pi)) =
          (2 * (CT * K * (L ^ 3 * (4 * x / T)))) * (1 / (2 * Real.pi)) +
          (CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) * (1 / (2 * Real.pi)) := by ring
      have hexp : (Cp + 4 * CT / Real.pi + 1) * (x * L ^ 3 / T) * K
          = Cp * (x * L ^ 3 / T) * K + (4 * CT / Real.pi) * (x * L ^ 3 / T) * K
            + (x * L ^ 3 / T) * K := by ring
      have hcomb : Cp * (x * L ^ 3 / T) + (4 * CT / Real.pi) * (x * L ^ 3 / T) * K
          ≤ Cp * (x * L ^ 3 / T) * K + (4 * CT / Real.pi) * (x * L ^ 3 / T) * K
            + (x * L ^ 3 / T) * K := by
        have h2 : 0 ≤ (x * L ^ 3 / T) * K := mul_nonneg hP1 hK0
        linarith [hPK, h2]
      have h2cp : (2 * Cp) * (L * Gx) ≤ (2 * Cp + 1) * (L * Gx) := by
        have h2 : 0 ≤ L * Gx := mul_nonneg hL0 hG0
        nlinarith [h2]
      have hcl : (CL / (2 * Real.pi)) * ((x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4)
          ≤ (CL / (2 * Real.pi) + 1) * ((x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) := by
        have h2 : 0 ≤ (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4 := hxl4
        nlinarith [h2]
      rw [hsplit, hexp]
      linarith [htermp, hterm2, hterm3, hind, hcomb, h2cp, hcl]
    linarith [hbase, hfin]



end Commons.NumberTheory.Zeta
end


namespace Commons.NumberTheory.Zeta


theorem chebyshevPsi_at_height_farLeft_neg (h : RiemannHypothesis) : ∃ C C₂ D : ℝ, 0 < C ∧ 0 < C₂ ∧ 0 < D ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ T δ K : ℝ, 5 ≤ T → x ≤ T ^ 2 → 0 < δ → 1 ≤ K → 1 ≤ K * (Real.log (T + 3) + 1) * δ → (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) → (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ T ∧ ρ.im ≠ -T) → ‖(Chebyshev.psi x : ℂ) - ((x : ℂ) - Complex.log (2 * (Real.pi : ℂ)) - ∑ ρ ∈ Commons.NumberTheory.Zeta.zRectZeros (R := 2 + |T|) (by positivity) (-(3 / 2)) (1 + 1 / Real.log x) T, (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ)‖ ≤ C * (x * (Real.log (T + 3) + 1) ^ 3 / T) * K + C₂ * ((Real.log (T + 3) + 1) * (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) + min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)))) + (if (Nat.floor x : ℝ) = x then 4 * (Real.log (T + 3) + 1) else 0) + D * ((x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (T + 3) + 1) ^ 4) := by
  obtain ⟨Cp, hCppos, hCp⟩ := chebyshevPsi_truncatedPerron_refined
  exact chebyshevPsi_at_height_farLeft_neg_aux h Cp hCppos hCp


end Commons.NumberTheory.Zeta
