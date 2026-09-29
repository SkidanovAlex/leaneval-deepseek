import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17b.xs_pos
import Submission.Work.C17b.deriv_Pfun_local
import Submission.Work.C17b.isPreconnected_slitBall
import Submission.Work.C17b.analyticOn_eqOn_zero_of_vanishing_Ioo
import Submission.Work.C17b.tendsto_log_neg_im_pos
import Submission.Work.C17b.tendsto_log_neg_im_neg

/-!
# Comparison of the coefficient of a logarithm (area C17, lemma `17functions`)

`acl_log_compare` is the analytic core (ACL-b) of the x-side route to the seventeen-function
independence: if `Pfun` agrees, near the origin, with `κ • y₁ • log (x_s - ·) + h` where `y₁ , h`
are holomorphic on a ball around the singularity `x_s`, and if a polynomial combination
`α·Pfun + β·Pfun'` is holomorphic there, then the *coefficient* `α·y₁ + β·y₁'` of the logarithm
vanishes identically on the ball.

The mathematical content is the elementary fact that `u ↦ log (-u)` has a branch cut along the
positive real axis: if `A , B` are holomorphic near `0` (`B` possibly with a pole at `0`) and
`A u * log (-u) = B u` on a nonempty open subset of the left half-plane, then `A ≡ 0`. Indeed the
identity propagates to the slit disc `{|u| < δ}\{u : u.re ≥ 0, u.im = 0}`, which is preconnected;
there both one-sided limits of `log (-u)` at a positive real point exist and differ by `2πi`, which
forces `A = 0` on `(0 , δ)` and hence everywhere.
-/

open Filter Metric
open scoped Topology

namespace Work.C17

theorem log_neg_compare {δ : ℝ} (hδ : 0 < δ) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (A B : ℂ → ℂ)
    (hA : DifferentiableOn ℂ A (Metric.ball (0 : ℂ) δ))
    (hB : DifferentiableOn ℂ B (Metric.ball (0 : ℂ) δ \ {0}))
    (hid : ∀ u ∈ Metric.ball (0 : ℂ) δ ∩ Metric.ball (-x₀ : ℂ) x₀,
      A u * Complex.log (-u) = B u) :
    ∀ u ∈ Metric.ball (0 : ℂ) δ, A u = 0 := by
  set Ω : Set ℂ := Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.re < 0 ∨ u.im ≠ 0} with hΩ
  have hslit_open : IsOpen {u : ℂ | u.re < 0 ∨ u.im ≠ 0} := by
    have hset : {u : ℂ | u.re < 0 ∨ u.im ≠ 0}
        = {u : ℂ | u.re < (0:ℝ)} ∪ ({u : ℂ | u.im < (0:ℝ)} ∪ {u : ℂ | (0:ℝ) < u.im}) := by
      ext u
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · rcases lt_or_gt_of_ne h with h' | h'
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr h')
      · rintro (h | (h | h))
        · exact Or.inl h
        · exact Or.inr (ne_of_lt h)
        · exact Or.inr (ne_of_gt h)
    rw [hset]
    exact (isOpen_lt Complex.continuous_re continuous_const).union
      ((isOpen_lt Complex.continuous_im continuous_const).union
        (isOpen_lt continuous_const Complex.continuous_im))
  have hΩopen : IsOpen Ω := by rw [hΩ]; exact isOpen_ball.inter hslit_open
  have hpunct_open : IsOpen (Metric.ball (0 : ℂ) δ \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hΩsub_ball : Ω ⊆ Metric.ball (0 : ℂ) δ := by rw [hΩ]; exact Set.inter_subset_left
  have hΩsub_punct : Ω ⊆ Metric.ball (0 : ℂ) δ \ {0} := by
    rw [hΩ]
    rintro u ⟨hu, hcond⟩
    refine ⟨hu, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h0
    rw [h0] at hcond
    simp at hcond
  have hAΩ : AnalyticOnNhd ℂ A Ω := (hA.analyticOnNhd isOpen_ball).mono hΩsub_ball
  have hBΩ : AnalyticOnNhd ℂ B Ω := (hB.analyticOnNhd hpunct_open).mono hΩsub_punct
  have hlogΩ : AnalyticOnNhd ℂ (fun u : ℂ => Complex.log (-u)) Ω := by
    refine DifferentiableOn.analyticOnNhd ?_ hΩopen
    intro u hu
    have hmem : -u ∈ Complex.slitPlane := by
      rw [hΩ] at hu
      rcases hu with ⟨hu1, hcond⟩
      rw [Complex.mem_slitPlane_iff]
      rcases hcond with h | h
      · left; simpa using (neg_pos.mpr h)
      · right; simpa using neg_ne_zero.mpr h
    exact ((Complex.differentiableAt_log hmem).comp u (hasDerivAt_neg u).differentiableAt).differentiableWithinAt
  have hf : AnalyticOnNhd ℂ (fun u : ℂ => A u * Complex.log (-u) - B u) Ω :=
    (hAΩ.mul hlogΩ).sub hBΩ
  set c : ℝ := min δ x₀ / 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcltδ : c < δ := by rw [hc]; nlinarith [min_le_left δ x₀]
  have hcltx : c < x₀ := by rw [hc]; nlinarith [min_le_right δ x₀]
  set z₀ : ℂ := ((-c : ℝ) : ℂ) with hz₀
  have hz₀_ball : z₀ ∈ Metric.ball (0 : ℂ) δ := by
    rw [mem_ball, Complex.dist_eq, sub_zero, hz₀]
    have : ((-c : ℝ) : ℂ) = -((c : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_neg, Complex.norm_of_nonneg hcpos.le]
    exact hcltδ
  have hz₀_ballx : z₀ ∈ Metric.ball (-x₀ : ℂ) x₀ := by
    rw [mem_ball, Complex.dist_eq, hz₀]
    have hdiff : ((-c : ℝ) : ℂ) - -(((x₀ : ℝ)) : ℂ) = (((x₀ - c) : ℝ) : ℂ) := by push_cast; ring
    rw [hdiff, Complex.norm_of_nonneg (by linarith)]
    linarith
  have hz₀_mem : z₀ ∈ Ω := by
    rw [hΩ]
    refine ⟨hz₀_ball, Or.inl ?_⟩
    rw [hz₀]
    simp only [Complex.ofReal_re]
    linarith
  have hnbhd : Metric.ball (0 : ℂ) δ ∩ Metric.ball (-x₀ : ℂ) x₀ ∈ nhds z₀ :=
    Filter.inter_mem (IsOpen.mem_nhds isOpen_ball hz₀_ball)
      (IsOpen.mem_nhds isOpen_ball hz₀_ballx)
  have hf0 : (fun u : ℂ => A u * Complex.log (-u) - B u) =ᶠ[nhds z₀] 0 := by
    filter_upwards [hnbhd] with u hu
    simp only [Pi.zero_apply]
    exact sub_eq_zero.mpr (hid u hu)
  have hfzero : ∀ u ∈ Ω, A u * Complex.log (-u) - B u = 0 :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero (by rw [hΩ]; exact Work.C17b.isPreconnected_slitBall hδ)
      hz₀_mem hf0
  -- accumulation at real points
  have hclos_pos : ∀ t : ℝ, (t:ℂ) ∈ closure {u : ℂ | 0 < u.im} := by
    intro t
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hpos : (0:ℝ) < min ε 1 / 2 := by have := lt_min hε one_pos; linarith
    refine ⟨(t:ℂ) + (((min ε 1 / 2 : ℝ)) : ℂ) * Complex.I, ?_, ?_⟩
    · show (0:ℝ) < ((t:ℂ) + (((min ε 1 / 2 : ℝ)) : ℂ) * Complex.I).im
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
      linarith
    · rw [Complex.dist_eq]
      have hdiff : (t:ℂ) - ((t:ℂ) + (((min ε 1 / 2 : ℝ)) : ℂ) * Complex.I)
          = -((((min ε 1 / 2 : ℝ)) : ℂ) * Complex.I) := by ring
      rw [hdiff, norm_neg, Complex.norm_mul, Complex.norm_I, mul_one,
        Complex.norm_of_nonneg (by positivity)]
      nlinarith [min_le_left ε 1, hε]
  have hclos_neg : ∀ t : ℝ, (t:ℂ) ∈ closure {u : ℂ | u.im < 0} := by
    intro t
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hpos : (0:ℝ) < min ε 1 / 2 := by have := lt_min hε one_pos; linarith
    refine ⟨(t:ℂ) - (((min ε 1 / 2 : ℝ)) : ℂ) * Complex.I, ?_, ?_⟩
    · show ((t:ℂ) - (((min ε 1 / 2 : ℝ)) : ℂ) * Complex.I).im < 0
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
      linarith
    · rw [Complex.dist_eq]
      have hdiff : (t:ℂ) - ((t:ℂ) - (((min ε 1 / 2 : ℝ)) : ℂ) * Complex.I)
          = (((min ε 1 / 2 : ℝ)) : ℂ) * Complex.I := by ring
      rw [hdiff, Complex.norm_mul, Complex.norm_I, mul_one,
        Complex.norm_of_nonneg (by positivity)]
      nlinarith [min_le_left ε 1, hε]
  have key : ∀ t : ℝ, 0 < t → t < δ → A (t:ℂ) = 0 := by
    intro t ht0 htd
    have htmem : (t:ℂ) ∈ Metric.ball (0:ℂ) δ := by
      rw [mem_ball, Complex.dist_eq, sub_zero, Complex.norm_of_nonneg ht0.le]; exact htd
    have htne : (t:ℂ) ≠ 0 := fun h => ht0.ne' (Complex.ofReal_eq_zero.mp h)
    have htmem_p : (t:ℂ) ∈ Metric.ball (0:ℂ) δ \ {0} := ⟨htmem, by simp [htne]⟩
    haveI hNBpos : (nhdsWithin (t:ℂ) {u : ℂ | 0 < u.im}).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (hclos_pos t)
    haveI hNBneg : (nhdsWithin (t:ℂ) {u : ℂ | u.im < 0}).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (hclos_neg t)
    -- upper side
    have hAc : Tendsto A (nhdsWithin (t:ℂ) {u : ℂ | 0 < u.im}) (nhds (A (t:ℂ))) :=
      ((hA.differentiableAt (IsOpen.mem_nhds isOpen_ball htmem)).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    have hBc : Tendsto B (nhdsWithin (t:ℂ) {u : ℂ | 0 < u.im}) (nhds (B (t:ℂ))) :=
      ((hB.differentiableAt (IsOpen.mem_nhds hpunct_open htmem_p)).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    have hlim1 : Tendsto (fun u : ℂ => A u * Complex.log (-u) - B u)
        (nhdsWithin (t:ℂ) {u : ℂ | 0 < u.im})
        (nhds (A (t:ℂ) * ((Real.log t : ℂ) - (Real.pi : ℂ) * Complex.I) - B (t:ℂ))) :=
      (hAc.mul (Work.C17b.tendsto_log_neg_im_pos ht0)).sub hBc
    have hev1 : (fun u : ℂ => A u * Complex.log (-u) - B u)
        =ᶠ[nhdsWithin (t:ℂ) {u : ℂ | 0 < u.im}] (0 : ℂ → ℂ) := by
      change ∀ᶠ u in nhdsWithin (t:ℂ) {u : ℂ | 0 < u.im}, A u * Complex.log (-u) - B u = 0
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (t:ℂ) (show (0:ℝ) < δ - t by linarith)] with u hu hpos
      have hmemΩ : u ∈ Ω := by
        rw [hΩ]
        refine ⟨?_, Or.inr (ne_of_gt hpos)⟩
        rw [mem_ball, Complex.dist_eq, sub_zero]
        have h1 : ‖u‖ ≤ ‖u - (t:ℂ)‖ + ‖(t:ℂ)‖ := by
          conv_lhs => rw [show u = (u - (t:ℂ)) + (t:ℂ) from by ring]
          exact norm_add_le _ _
        have h2 : ‖(t:ℂ)‖ = t := Complex.norm_of_nonneg ht0.le
        rw [h2] at h1
        have h3 : ‖u - (t:ℂ)‖ < δ - t := by
          have h4 := hu
          rwa [mem_ball, Complex.dist_eq] at h4
        linarith
      exact hfzero u hmemΩ
    have hfz1 : Tendsto (fun u : ℂ => A u * Complex.log (-u) - B u)
        (nhdsWithin (t:ℂ) {u : ℂ | 0 < u.im}) (nhds 0) :=
      Tendsto.congr' hev1.symm tendsto_const_nhds
    have e1 : A (t:ℂ) * ((Real.log t : ℂ) - (Real.pi : ℂ) * Complex.I) - B (t:ℂ) = 0 :=
      tendsto_nhds_unique hlim1 hfz1
    -- lower side
    have hAc' : Tendsto A (nhdsWithin (t:ℂ) {u : ℂ | u.im < 0}) (nhds (A (t:ℂ))) :=
      ((hA.differentiableAt (IsOpen.mem_nhds isOpen_ball htmem)).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    have hBc' : Tendsto B (nhdsWithin (t:ℂ) {u : ℂ | u.im < 0}) (nhds (B (t:ℂ))) :=
      ((hB.differentiableAt (IsOpen.mem_nhds hpunct_open htmem_p)).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun u : ℂ => A u * Complex.log (-u) - B u)
        (nhdsWithin (t:ℂ) {u : ℂ | u.im < 0})
        (nhds (A (t:ℂ) * ((Real.log t : ℂ) + (Real.pi : ℂ) * Complex.I) - B (t:ℂ))) :=
      (hAc'.mul (Work.C17b.tendsto_log_neg_im_neg ht0)).sub hBc'
    have hev2 : (fun u : ℂ => A u * Complex.log (-u) - B u)
        =ᶠ[nhdsWithin (t:ℂ) {u : ℂ | u.im < 0}] (0 : ℂ → ℂ) := by
      change ∀ᶠ u in nhdsWithin (t:ℂ) {u : ℂ | u.im < 0}, A u * Complex.log (-u) - B u = 0
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (t:ℂ) (show (0:ℝ) < δ - t by linarith)] with u hu hneg
      have hmemΩ : u ∈ Ω := by
        rw [hΩ]
        refine ⟨?_, Or.inr (ne_of_lt hneg)⟩
        rw [mem_ball, Complex.dist_eq, sub_zero]
        have h1 : ‖u‖ ≤ ‖u - (t:ℂ)‖ + ‖(t:ℂ)‖ := by
          conv_lhs => rw [show u = (u - (t:ℂ)) + (t:ℂ) from by ring]
          exact norm_add_le _ _
        have h2 : ‖(t:ℂ)‖ = t := Complex.norm_of_nonneg ht0.le
        rw [h2] at h1
        have h3 : ‖u - (t:ℂ)‖ < δ - t := by
          have h4 := hu
          rwa [mem_ball, Complex.dist_eq] at h4
        linarith
      exact hfzero u hmemΩ
    have hfz2 : Tendsto (fun u : ℂ => A u * Complex.log (-u) - B u)
        (nhdsWithin (t:ℂ) {u : ℂ | u.im < 0}) (nhds 0) :=
      Tendsto.congr' hev2.symm tendsto_const_nhds
    have e2 : A (t:ℂ) * ((Real.log t : ℂ) + (Real.pi : ℂ) * Complex.I) - B (t:ℂ) = 0 :=
      tendsto_nhds_unique hlim2 hfz2
    have hXY : A (t:ℂ) * ((Real.log t : ℂ) - (Real.pi : ℂ) * Complex.I)
        = A (t:ℂ) * ((Real.log t : ℂ) + (Real.pi : ℂ) * Complex.I) := by
      rw [sub_eq_zero.mp e1, sub_eq_zero.mp e2]
    have hmul : A (t:ℂ) * (((Real.log t : ℂ) - (Real.pi : ℂ) * Complex.I)
        - ((Real.log t : ℂ) + (Real.pi : ℂ) * Complex.I)) = 0 := by
      rw [mul_sub, hXY, sub_self]
    have hne : ((Real.log t : ℂ) - (Real.pi : ℂ) * Complex.I)
        - ((Real.log t : ℂ) + (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hform : ((Real.log t : ℂ) - (Real.pi : ℂ) * Complex.I)
          - ((Real.log t : ℂ) + (Real.pi : ℂ) * Complex.I)
          = -((2:ℂ) * (Real.pi : ℂ) * Complex.I) := by ring
      rw [hform]
      exact neg_ne_zero.mpr (by simpa using Complex.two_pi_I_ne_zero)
    exact (mul_eq_zero.mp hmul).resolve_right hne
  exact Work.C17b.analyticOn_eqOn_zero_of_vanishing_Ioo hδ (hA.analyticOnNhd isOpen_ball) key


open Polynomial

theorem acl_log_compare (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b)
    (ra rb rab r0 : ℤ) (κ : ℂ) (y1 hh : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ) (hκ : κ ≠ 0)
    (hy1 : DifferentiableOn ℂ y1 (Metric.ball (((xs a b : ℝ)) : ℂ) δ))
    (hhh : DifferentiableOn ℂ hh (Metric.ball (((xs a b : ℝ)) : ℂ) δ))
    (hloc : ∀ z ∈ Metric.ball (((xs a b : ℝ)) : ℂ) δ ∩ Metric.ball (0 : ℂ) (xs a b),
      Pfun a b ra rb rab r0 z = κ * y1 z * Complex.log (((xs a b : ℝ) : ℂ) - z) + hh z)
    (α β : Polynomial ℂ) (E : ℂ → ℂ)
    (hE : DifferentiableOn ℂ E (Metric.ball (((xs a b : ℝ)) : ℂ) δ))
    (heq : ∀ z ∈ Metric.ball (((xs a b : ℝ)) : ℂ) δ ∩ Metric.ball (0 : ℂ) (xs a b),
      α.eval z * Pfun a b ra rb rab r0 z + β.eval z * deriv (Pfun a b ra rb rab r0) z = E z) :
    ∀ z ∈ Metric.ball (((xs a b : ℝ)) : ℂ) δ, α.eval z * y1 z + β.eval z * deriv y1 z = 0 := by
  have hρ : 0 < xs a b := Work.C17b.xs_pos ha hb
  let x₀ : ℂ := ((xs a b : ℝ) : ℂ)
  have hx₀re : x₀.re = xs a b := Complex.ofReal_re _
  have hderiv : ∀ z ∈ Metric.ball x₀ δ ∩ Metric.ball (0 : ℂ) (xs a b),
      deriv (Pfun a b ra rb rab r0) z
        = κ * (deriv y1 z * Complex.log (x₀ - z) - y1 z * (x₀ - z)⁻¹) + deriv hh z :=
    Work.C17b.deriv_Pfun_local a b ra rb rab r0 κ y1 hh hy1 hhh hloc
  let W : ℂ → ℂ := fun z => α.eval z * y1 z + β.eval z * deriv y1 z
  let A : ℂ → ℂ := fun u => κ * W (x₀ + u)
  let B : ℂ → ℂ := fun u => E (x₀ + u) - α.eval (x₀ + u) * hh (x₀ + u)
      - β.eval (x₀ + u) * deriv hh (x₀ + u) + κ * (β.eval (x₀ + u) * y1 (x₀ + u)) * (-u)⁻¹
  have hlogid : ∀ u ∈ Metric.ball (0 : ℂ) δ ∩ Metric.ball (-x₀) (xs a b),
      A u * Complex.log (-u) = B u := by
    intro u hu
    have hu1 : u ∈ Metric.ball (0 : ℂ) δ := hu.1
    have hu2 : u ∈ Metric.ball (-x₀) (xs a b) := hu.2
    have hz_mem : x₀ + u ∈ Metric.ball x₀ δ ∩ Metric.ball (0 : ℂ) (xs a b) := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, Complex.dist_eq]
        have h : x₀ + u - x₀ = u := by ring
        rw [h]
        have h5 := hu1
        rwa [mem_ball, Complex.dist_eq, sub_zero] at h5
      · rw [mem_ball, Complex.dist_eq, sub_zero]
        have h2 : ‖u - (-x₀)‖ < xs a b := by
          have h6 := hu2
          rwa [mem_ball, Complex.dist_eq] at h6
        have h : u - (-x₀) = x₀ + u := by ring
        rwa [h] at h2
    have h3 := heq (x₀ + u) hz_mem
    have h1 := hloc (x₀ + u) hz_mem
    have h2 := hderiv (x₀ + u) hz_mem
    rw [h1, h2] at h3
    have hxz : x₀ - (x₀ + u) = -u := by ring
    rw [hxz] at h3
    dsimp only [A, B]
    rw [← h3]
    ring
  have hW : DifferentiableOn ℂ W (Metric.ball x₀ δ) := by
    dsimp only [W]
    exact ((Polynomial.differentiableOn (s := Metric.ball x₀ δ) α).mul hy1).add
      ((Polynomial.differentiableOn (s := Metric.ball x₀ δ) β).mul (hy1.deriv isOpen_ball))
  have hmaps : Set.MapsTo (fun u : ℂ => x₀ + u) (Metric.ball (0 : ℂ) δ) (Metric.ball x₀ δ) := by
    intro u hu
    rw [mem_ball, Complex.dist_eq]
    have h : x₀ + u - x₀ = u := by ring
    rw [h]
    have h5 := hu
    rwa [mem_ball, Complex.dist_eq, sub_zero] at h5
  have hshift : DifferentiableOn ℂ (fun u : ℂ => x₀ + u) (Metric.ball (0 : ℂ) δ) :=
    (differentiableOn_const x₀).add differentiableOn_id
  have hA : DifferentiableOn ℂ A (Metric.ball (0 : ℂ) δ) := by
    dsimp only [A]
    exact (hW.comp hshift hmaps).const_mul κ
  have hB : DifferentiableOn ℂ B (Metric.ball (0 : ℂ) δ \ {0}) := by
    dsimp only [B]
    have hshift' : DifferentiableOn ℂ (fun u : ℂ => x₀ + u) (Metric.ball (0 : ℂ) δ \ {0}) :=
      (differentiableOn_const x₀).add differentiableOn_id
    have hmaps' : Set.MapsTo (fun u : ℂ => x₀ + u) (Metric.ball (0 : ℂ) δ \ {0}) (Metric.ball x₀ δ) :=
      fun u hu => hmaps hu.1
    have h1 : DifferentiableOn ℂ (fun u : ℂ => E (x₀ + u)) (Metric.ball (0 : ℂ) δ \ {0}) :=
      hE.comp hshift' hmaps'
    have h2 : DifferentiableOn ℂ (fun u : ℂ => α.eval (x₀ + u) * hh (x₀ + u)) (Metric.ball (0 : ℂ) δ \ {0}) :=
      ((Polynomial.differentiableOn (s := Metric.ball x₀ δ) α).comp hshift' hmaps').mul
        (hhh.comp hshift' hmaps')
    have h3 : DifferentiableOn ℂ (fun u : ℂ => β.eval (x₀ + u) * deriv hh (x₀ + u)) (Metric.ball (0 : ℂ) δ \ {0}) :=
      ((Polynomial.differentiableOn (s := Metric.ball x₀ δ) β).comp hshift' hmaps').mul
        ((hhh.deriv isOpen_ball).comp hshift' hmaps')
    have h4 : DifferentiableOn ℂ (fun u : ℂ => κ * (β.eval (x₀ + u) * y1 (x₀ + u)) * (-u)⁻¹)
        (Metric.ball (0 : ℂ) δ \ {0}) := by
      have hinv : DifferentiableOn ℂ (fun u : ℂ => (-u)⁻¹) (Metric.ball (0 : ℂ) δ \ {0}) := by
        refine DifferentiableOn.inv differentiableOn_id.neg ?_
        intro u hu
        have hu0 : u ≠ 0 := fun h0 => hu.2 (by simpa using h0)
        simp [hu0]
      exact ((((Polynomial.differentiableOn (s := Metric.ball x₀ δ) β).comp hshift' hmaps').mul
        (hy1.comp hshift' hmaps')).const_mul κ).mul hinv
    exact ((h1.sub h2).sub h3).add h4
  have hmain := log_neg_compare hδ hρ A B hA hB hlogid
  intro z hz
  have hzmem : z - x₀ ∈ Metric.ball (0 : ℂ) δ := by
    rw [mem_ball, Complex.dist_eq, sub_zero]
    have h5 := hz
    rw [mem_ball, Complex.dist_eq] at h5
    exact h5
  have hA0 := hmain (z - x₀) hzmem
  have hfin : W z = 0 := by
    dsimp only [A] at hA0
    rw [show x₀ + (z - x₀) = z from by ring] at hA0
    exact (mul_eq_zero.mp hA0).resolve_left hκ
  dsimp only [W] at hfin
  exact hfin

end Work.C17
