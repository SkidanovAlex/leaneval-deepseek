import Mathlib
import Submission.Commons.Analysis.Complex.rectIntegral_sub_inv_inside
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_truncatedPerron
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.Analysis.Fourier.perronStep_deviation
import Submission.Commons.NumberTheory.Zeta.perronOne_bound
import Submission.Commons.NumberTheory.Zeta.mangoldt_perron_sum_eq
import Submission.Commons.Analysis.ExpLog.log_nat_add_rpow_div_summable_bound
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Port.LogDerivCompat
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_negStrip_bound
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Group.Basic
import Submission.Commons.NumberTheory.Zeta.zeta1_exists_good_radius
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth_neg
import Submission.Commons.NumberTheory.Zeta.zeta_lower_re_two
import Submission.Commons.Analysis.Complex.logDeriv_sub_divisor_le
import Submission.Commons.NumberTheory.Zeta.zetaZeroBall

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
  rw [Submission.Port.logDeriv_mul_fun 0 (by norm_num) (by rw [riemannZeta_zero]; norm_num)
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

end Commons.NumberTheory.Zeta
end


namespace Commons.NumberTheory.Zeta


end Commons.NumberTheory.Zeta
