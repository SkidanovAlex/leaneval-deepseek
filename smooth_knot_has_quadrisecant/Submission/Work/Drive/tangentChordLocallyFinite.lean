import Mathlib
import Submission.Work.Drive.genericFullDefs
import Submission.Work.Drive.tangentChordDefs
import Submission.Commons.Analysis.CrossProduct.cross3_ne_zero_iff_linearIndependent
import Submission.Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
import Submission.Commons.Analysis.CrossProduct.inner_cross3_self_left

/-!
# Local finiteness of the set of tangent chords

This module proves `Work.Drive.tangentChordLocallyFinite`: for a smooth knot `r` without inflection
points (`hinfl`) and in tangent-chord general position (`Work.Drive.TangentChordGP`), the set

  `{(a, h) | 0 < h < period, r (a+h) - r a parallel to r' a  or  to r' (a+h)}`

of *tangent chords* is locally finite.

**Mathematical content.**  A tangent chord at the first endpoint is the vanishing of
`cross3 (r (a + h) - r a) (deriv r a)`.  In the three-variable picture
`tangentLinePsi r (a, μ, h) = r (a + h) - r a - μ • deriv r a` this condition is the *graph* of the
zero set: `(a, h)` is a tangent chord with multiplier `μ` exactly when
`tangentLinePsi r (a, μ, h) = 0`.  At a genuine tangent chord `h ∈ (0, period)` the chord is non-zero
and parallel to the tangent, and the hypothesis `TangentChordGP` says precisely that the three
vectors `deriv r a`, `deriv (deriv r) a`, `deriv r (a + h)` are linearly independent — which is
exactly the invertibility of the derivative `tangentLinePsiD r p₀`
(`Work.Drive.tangentLinePsiD_injective`).  The inverse function theorem
(`Work.Drive.exists_injOn_nhds_tangentLinePsi`) therefore isolates the zero: tangent chords are
*locally* a single point.  Near the boundary lines `h = 0` and `h = period` the lemma
`Work.Drive.tangentChordBoundary_local` (a second-order expansion of the chord against the tangent,
using `hinfl`) shows that no tangent chord occurs at all.  Combining, the set of tangent chords is
locally finite; the second endpoint is handled by the involution `tcFlip (a, h) = (a + h, period - h)`
of the strip, which preserves the chord and exchanges the two endpoints
(`Work.Drive.tcFlip_mem_tcSetA_iff`).
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section


/-- The curvature vector `r'' (a) × r' (a)` of a smooth curve. -/
def curvatureVector (r : ℝ → Space) (a : ℝ) : Space := cross3 (deriv (deriv r) a) (deriv r a)

lemma inner_cross3_left (u v : Space) : inner ℝ (cross3 u v) u = 0 := by
  simpa [cross3] using Commons.Analysis.CrossProduct.inner_cross3_self_left u v

lemma inner_cross3_right (u v : Space) : inner ℝ (cross3 u v) v = 0 := by
  have h : cross3 u v = -cross3 v u := by rw [cross3_anticomm u v, neg_neg]
  rw [h, inner_neg_left, inner_cross3_left v u, neg_zero]

lemma inner_cross3_combination (x y z : Space) (c₁ c₂ c₃ : ℝ) :
    inner ℝ (cross3 x y) (c₁ • x + c₂ • y + c₃ • z) = c₃ * inner ℝ (cross3 x y) z := by
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, inner_cross3_left x y, inner_cross3_right x y,
    mul_zero, mul_zero, add_zero, zero_add]

lemma cross3_add_combination (x y : Space) (c₁ c₂ : ℝ) :
    cross3 (c₁ • x + c₂ • y) y = c₁ • cross3 x y := by
  rw [cross3_add_left, cross3_smul_left, cross3_smul_left, cross3_self, smul_zero, add_zero]

lemma linearIndependent_of_inner_cross3_ne_zero {x y z : Space}
    (h : inner ℝ (cross3 x y) z ≠ 0) : LinearIndependent ℝ ![x, y, z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hxy : cross3 x y ≠ 0 := fun h0 => h (by rw [h0, inner_zero_left])
  have hsum : g 0 • x + g 1 • y + g 2 • z = 0 := by simpa [Fin.sum_univ_three] using hg
  have h2 : g 2 = 0 := by
    have hc : g 2 * inner ℝ (cross3 x y) z = 0 := by
      have hcong := congrArg (fun w : Space => inner ℝ (cross3 x y) w) hsum
      rw [inner_cross3_combination, inner_zero_right] at hcong
      exact hcong
    exact (mul_eq_zero.mp hc).resolve_right h
  have hsum2 : g 0 • x + g 1 • y = 0 := by
    have hh := hsum
    rw [h2, zero_smul, add_zero] at hh
    exact hh
  have h1 : g 0 = 0 := by
    have hc : cross3 (g 0 • x + g 1 • y) y = cross3 (0 : Space) y := by rw [hsum2]
    rw [cross3_zero_left, cross3_add_combination] at hc
    exact (smul_eq_zero.mp hc).resolve_right hxy
  have h3 : g 1 = 0 := by
    have hy : y ≠ 0 := fun h0 => hxy (by rw [h0, cross3_zero_right])
    have hc : g 1 • y = 0 := by
      have hh := hsum2
      rw [h1, zero_smul, zero_add] at hh
      exact hh
    exact (smul_eq_zero.mp hc).resolve_right hy
  intro i
  fin_cases i
  · exact h1
  · exact h3
  · exact h2

lemma linearIndependent_swap_pair {x y : Space} (h : LinearIndependent ℝ ![x, y]) :
    LinearIndependent ℝ ![y, x] := by
  rw [Fintype.linearIndependent_iff] at h
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : (fun i => ![g 1, g 0] i) 0 • x + (fun i => ![g 1, g 0] i) 1 • y = 0 := by
    simpa [Fin.sum_univ_two, add_comm] using hg
  have h2 := h (fun i => ![g 1, g 0] i) (by simpa [Fin.sum_univ_two] using hg')
  intro i
  fin_cases i
  · exact h2 1
  · exact h2 0

lemma curvatureVector_ne_zero {r : ℝ → Space}
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) (a : ℝ) :
    curvatureVector r a ≠ 0 :=
  (Commons.Analysis.CrossProduct.cross3_ne_zero_iff_linearIndependent
    (deriv (deriv r) a) (deriv r a)).mpr (linearIndependent_swap_pair (hinfl a))

lemma curvatureVector_continuous {r : ℝ → Space} (hr : IsSmoothKnot r) (a₀ : ℝ) {c : ℝ}
    (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℝ × ℝ, dist q (a₀, a₀) < δ →
      dist (cross3 (deriv (deriv r) q.1) (deriv r q.2)) (curvatureVector r a₀) < c := by
  have hrcS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
  have hvcS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) :=
    (contDiff_infty_iff_deriv.mp hrcS).2
  have hv2S : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv r)) :=
    (contDiff_infty_iff_deriv.mp hvcS).2
  have hcrosscont : Continuous fun p : Space × Space => cross3 p.1 p.2 := by
    have h := Commons.Analysis.Calculus.ContDiff.crossProduct (s := Set.univ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (u := fun p : Space × Space => p.1)
      (v := fun p : Space × Space => p.2) (by fun_prop) (by fun_prop)
    rw [contDiffOn_univ] at h
    exact h.continuous
  have hGcont : Continuous fun q : ℝ × ℝ => cross3 (deriv (deriv r) q.1) (deriv r q.2) := by
    have h1 : Continuous fun q : ℝ × ℝ => deriv (deriv r) q.1 :=
      hv2S.continuous.comp continuous_fst
    have h2 : Continuous fun q : ℝ × ℝ => deriv r q.2 :=
      hvcS.continuous.comp continuous_snd
    exact hcrosscont.comp (h1.prodMk h2)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hGcont.continuousAt c hc
  refine ⟨δ, hδpos, fun q hq => ?_⟩
  have := hδ hq
  simpa [curvatureVector] using this

lemma norm_sub_sub_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' f'' : ℝ → E} {x y M : ℝ}
    (h1 : ∀ s ∈ Set.uIcc x y, HasDerivAt f (f' s) s)
    (h2 : ∀ s ∈ Set.uIcc x y, HasDerivAt f' (f'' s) s)
    (hM : ∀ s ∈ Set.uIcc x y, ‖f'' s‖ ≤ M) :
    ‖f y - f x - (y - x) • f' x‖ ≤ M * |y - x| ^ 2 := by
  set φ : ℝ → E := fun s => f y - f s - (y - s) • f' s with hφ
  have hφderiv : ∀ s ∈ Set.uIcc x y, HasDerivAt φ (-(y - s) • f'' s) s := by
    intro s hs
    have hA : HasDerivAt (fun t : ℝ => f y - f t) (-(f' s)) s := by
      have h := (hasDerivAt_const s (f y)).sub (h1 s hs)
      refine (h.congr_deriv (by simp)).congr_of_eventuallyEq ?_
      filter_upwards with t
      rfl
    have hB : HasDerivAt (fun t : ℝ => (y - t) • f' t) (y • f'' s - (f' s + s • f'' s)) s := by
      have hid := (hasDerivAt_id s).smul (h2 s hs)
      have hcst := (h2 s hs).const_smul y
      have hsub := hcst.sub hid
      refine (hsub.congr_deriv ?_).congr_of_eventuallyEq ?_
      · simp only [id_eq, one_smul, add_comm]
      · filter_upwards with t
        simp [sub_smul]
    have htot := hA.sub hB
    refine (htot.congr_deriv ?_).congr_of_eventuallyEq ?_
    · module
    · filter_upwards with t
      rfl
  have hφy : φ y = 0 := by simp [hφ]
  have hbd : ∀ s ∈ Set.uIcc x y, ‖deriv φ s‖ ≤ M * |y - x| := by
    intro s hs
    have hs' : |y - s| ≤ |y - x| := by
      rcases le_total x y with hxy | hyx
      · rw [Set.uIcc_of_le hxy, Set.mem_Icc] at hs
        rw [abs_of_nonneg (by linarith [hs.2] : 0 ≤ y - s),
          abs_of_nonneg (by linarith : 0 ≤ y - x)]
        linarith [hs.1]
      · rw [Set.uIcc_of_ge hyx, Set.mem_Icc] at hs
        rw [abs_of_nonpos (by linarith [hs.1] : y - s ≤ 0),
          abs_of_nonpos (by linarith : y - x ≤ 0)]
        linarith [hs.2]
    have hder : deriv φ s = -(y - s) • f'' s := (hφderiv s hs).deriv
    rw [hder, norm_smul, Real.norm_eq_abs, abs_neg]
    calc |y - s| * ‖f'' s‖ ≤ |y - x| * M :=
          (mul_le_mul_of_nonneg_right hs' (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (hM s hs) (abs_nonneg _))
      _ = M * |y - x| := by ring
  have hdiff : ∀ s ∈ Set.uIcc x y, DifferentiableAt ℝ φ s :=
    fun s hs => (hφderiv s hs).differentiableAt
  have hmvt := (convex_uIcc x y).norm_image_sub_le_of_norm_deriv_le hdiff hbd
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  rw [hφy, zero_sub, norm_neg] at hmvt
  calc ‖f y - f x - (y - x) • f' x‖ = ‖φ x‖ := by simp [hφ]
    _ ≤ (M * |y - x|) * ‖y - x‖ := hmvt
    _ = M * |y - x| ^ 2 := by rw [Real.norm_eq_abs]; ring

lemma abs_le_abs_of_mem_uIcc {h s : ℝ} (hs : s ∈ Set.uIcc (0:ℝ) h) : |s| ≤ |h| := by
  rcases le_total 0 h with hh | hh
  · rw [Set.uIcc_of_le hh, Set.mem_Icc] at hs
    rw [abs_of_nonneg hs.1, abs_of_nonneg hh]; exact hs.2
  · rw [Set.uIcc_of_ge hh, Set.mem_Icc] at hs
    rw [abs_of_nonpos hs.2, abs_of_nonpos hh]; linarith [hs.1]

lemma norm_cross3_chord_bound {r : ℝ → Space} (hr : IsSmoothKnot r)
    {a a₀ h δ₀ : ℝ} {g₀ : Space} (hδ₀pos : 0 < δ₀)
    (hδ₀ : ∀ q : ℝ × ℝ, dist q (a₀, a₀) < δ₀ →
      dist (cross3 (deriv (deriv r) q.1) (deriv r q.2)) g₀ < ‖g₀‖ / 4)
    (ha : |a - a₀| < δ₀ / 4) (hh : |h| < δ₀ / 4) :
    ‖cross3 (r (a + h) - r a) (deriv r a) - (h ^ 2 / 2) • g₀‖ ≤ (‖g₀‖ / 4) * |h| ^ 2 := by
  have hrc : ContDiff ℝ ⊤ r := hr.smooth
  have hrcS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hrc.of_le le_top
  have hvcS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) :=
    (contDiff_infty_iff_deriv.mp hrcS).2
  have hrd : Differentiable ℝ r := hrc.differentiable (by simp)
  have hvd : Differentiable ℝ (deriv r) := hvcS.differentiable (by simp)
  have hcomp1 : ∀ s : ℝ, HasDerivAt (fun t : ℝ => r (a + t)) (deriv r (a + s)) s := by
    intro s
    have houter : HasDerivAt r (deriv r (a + s)) (a + s) :=
      (hrd.differentiableAt (x := a + s)).hasDerivAt
    have hinner : HasDerivAt (fun t : ℝ => a + t) 1 s :=
      ((hasDerivAt_id s).const_add a).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => rfl)
    exact (houter.scomp s hinner).congr_deriv (by simp)
  have hcomp2 : ∀ s : ℝ, HasDerivAt (fun t : ℝ => deriv r (a + t)) (deriv (deriv r) (a + s)) s := by
    intro s
    have houter : HasDerivAt (deriv r) (deriv (deriv r) (a + s)) (a + s) :=
      (hvd.differentiableAt (x := a + s)).hasDerivAt
    have hinner : HasDerivAt (fun t : ℝ => a + t) 1 s :=
      ((hasDerivAt_id s).const_add a).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => rfl)
    exact (houter.scomp s hinner).congr_deriv (by simp)
  have hquad : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (t ^ 2 / 2) • g₀) (s • g₀) s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => t * t) (1 * s + s * 1) s :=
      (hasDerivAt_id s).mul (hasDerivAt_id s)
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) s s := by
      have h3 : HasDerivAt (fun t : ℝ => t * t / 2) ((1 * s + s * 1) / 2) s := h1.div_const 2
      have h4 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) ((1 * s + s * 1) / 2) s :=
        h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by simp [pow_two])
      exact h4.congr_deriv (by ring)
    exact (h2.smul_const g₀).congr_deriv (by ring)
  have h1 : ∀ s ∈ Set.uIcc (0:ℝ) h,
      HasDerivAt (fun s : ℝ => cross3 (r (a + s) - r a) (deriv r a) - (s ^ 2 / 2) • g₀)
        (cross3 (deriv r (a + s)) (deriv r a) - s • g₀) s := by
    intro s hs
    have hsub : HasDerivAt (fun t : ℝ => r (a + t) - r a) (deriv r (a + s)) s := by
      have h := (hcomp1 s).sub (hasDerivAt_const s (r a))
      refine (h.congr_deriv (by simp)).congr_of_eventuallyEq ?_
      filter_upwards with t
      rfl
    have hcr : HasDerivAt (fun t : ℝ => cross3 (r (a + t) - r a) (deriv r a))
        (cross3 (deriv r (a + s)) (deriv r a)) s := by
      have h := Commons.Analysis.CrossProduct.hasDerivAt_cross3
        (fun t : ℝ => r (a + t) - r a) (fun _ : ℝ => deriv r a) hsub
        (hasDerivAt_const s (deriv r a))
      refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
      · show cross3 (deriv r (a + s)) (deriv r a) + cross3 (r (a + s) - r a) (0 : Space)
            = cross3 (deriv r (a + s)) (deriv r a)
        rw [cross3_zero_right, add_zero]
      · filter_upwards with t
        rfl
    have htot := hcr.sub (hquad s)
    refine (htot.congr_deriv ?_).congr_of_eventuallyEq ?_
    · module
    · filter_upwards with t
      rfl
  have h2 : ∀ s ∈ Set.uIcc (0:ℝ) h,
      HasDerivAt (fun s : ℝ => cross3 (deriv r (a + s)) (deriv r a) - s • g₀)
        (cross3 (deriv (deriv r) (a + s)) (deriv r a) - g₀) s := by
    intro s hs
    have hcr : HasDerivAt (fun t : ℝ => cross3 (deriv r (a + t)) (deriv r a))
        (cross3 (deriv (deriv r) (a + s)) (deriv r a)) s := by
      have h := Commons.Analysis.CrossProduct.hasDerivAt_cross3
        (fun t : ℝ => deriv r (a + t)) (fun _ : ℝ => deriv r a) (hcomp2 s)
        (hasDerivAt_const s (deriv r a))
      refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
      · show cross3 (deriv (deriv r) (a + s)) (deriv r a) + cross3 (deriv r (a + s)) (0 : Space)
            = cross3 (deriv (deriv r) (a + s)) (deriv r a)
        rw [cross3_zero_right, add_zero]
      · filter_upwards with t
        rfl
    have hlin : HasDerivAt (fun t : ℝ => t • g₀) g₀ s := by
      refine ((hasDerivAt_id s).smul_const g₀).congr_deriv ?_
      simp
    exact (hcr.sub hlin).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)
  have h3 : ∀ s ∈ Set.uIcc (0:ℝ) h,
      ‖cross3 (deriv (deriv r) (a + s)) (deriv r a) - g₀‖ ≤ ‖g₀‖ / 4 := by
    intro s hs
    have hs' : |s| ≤ |h| := abs_le_abs_of_mem_uIcc hs
    have hdist : dist (a + s, a) (a₀, a₀) < δ₀ := by
      rw [Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Real.dist_eq]
        calc |a + s - a₀| ≤ |a - a₀| + |s| := by
              rw [show a + s - a₀ = (a - a₀) + s by ring]
              exact abs_add_le _ _
          _ ≤ δ₀ / 4 + δ₀ / 4 := by linarith
          _ < δ₀ := by linarith
      · rw [Real.dist_eq]; linarith
    have hlt := hδ₀ (a + s, a) hdist
    rw [dist_eq_norm] at hlt
    exact le_of_lt hlt
  have hmvt := norm_sub_sub_smul_le (x := 0) (y := h) h1 h2 h3
  simpa [cross3_zero_left, cross3_self, sub_zero] using hmvt

lemma tangentChordBoundary_local {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) (a₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, |a - a₀| < δ →
      ∀ h : ℝ, 0 < |h| → |h| < ε → cross3 (r (a + h) - r a) (deriv r a) ≠ 0 := by
  have hg0ne : curvatureVector r a₀ ≠ 0 := curvatureVector_ne_zero hinfl a₀
  have hg0pos : 0 < ‖curvatureVector r a₀‖ := norm_pos_iff.mpr hg0ne
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := curvatureVector_continuous hr a₀ (c := ‖curvatureVector r a₀‖ / 4) (by linarith)
  refine ⟨δ₀ / 4, by linarith, δ₀ / 4, by linarith, ?_⟩
  intro a ha h hh0 hh1 hzero
  have hbound := norm_cross3_chord_bound (g₀ := curvatureVector r a₀) hr hδ₀pos hδ₀ ha hh1
  have hsmul : ‖(h ^ 2 / 2) • curvatureVector r a₀‖ = (h ^ 2 / 2) * ‖curvatureVector r a₀‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ h ^ 2 / 2)]
  rw [hzero, zero_sub, norm_neg, hsmul, sq_abs] at hbound
  have hh2 : 0 < h ^ 2 := by
    have : h ≠ 0 := abs_pos.mp hh0
    positivity
  nlinarith [hg0pos, hh2, hbound]

/-! ## Chunk 4: the derivative, injectivity and the implicit function theorem -/

lemma cross3_neg_left (u v : Space) : cross3 (-u) v = -cross3 u v := by
  rw [show (-u : Space) = (-1 : ℝ) • u by rw [neg_one_smul]]
  rw [cross3_smul_left, neg_one_smul]

lemma continuous_cross3_pair : Continuous fun p : Space × Space => cross3 p.1 p.2 := by
  have h := Commons.Analysis.Calculus.ContDiff.crossProduct (s := Set.univ)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (u := fun p : Space × Space => p.1)
    (v := fun p : Space × Space => p.2) (by fun_prop) (by fun_prop)
  rw [contDiffOn_univ] at h
  exact h.continuous

lemma continuous_tangentChordCross {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Continuous fun p : ℝ × ℝ => cross3 (r (p.1 + p.2) - r p.1) (velocity r p.1) := by
  have hr1 : ContDiff ℝ 1 r := hr.smooth.of_le (by simp)
  have hv1 : ContDiff ℝ 1 (deriv r) :=
    ((contDiff_infty_iff_deriv.mp (hr.smooth.of_le le_top)).2).of_le (by simp)
  have h1 : Continuous fun p : ℝ × ℝ => r (p.1 + p.2) - r p.1 := by fun_prop
  have h2 : Continuous fun p : ℝ × ℝ => deriv r p.1 := hv1.continuous.comp continuous_fst
  exact continuous_cross3_pair.comp (h1.prodMk h2)

lemma tcF1_apply (q : tcParam) : tcF1 q = q.1.1 := rfl
lemma tcF2_apply (q : tcParam) : tcF2 q = q.2 := rfl
lemma tcF3_apply (q : tcParam) : tcF3 q = q.1.2 := rfl
lemma tcSum_apply (q : tcParam) : tcSum q = q.1.1 + q.2 := by
  simp [tcSum, tcF1, tcF2]

lemma tangentLinePsi_apply (r : ℝ → Space) (a μ h : ℝ) :
    tangentLinePsi r ((a, μ), h) = r (a + h) - r a - μ • deriv r a := by
  simp [tangentLinePsi, tcSum_apply, tcF1_apply, tcF3_apply]

lemma contDiff_tangentLinePsi {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) :
    ContDiff ℝ ⊤ (tangentLinePsi r) := by
  unfold tangentLinePsi
  fun_prop

lemma hasFDerivAt_tangentLinePsi {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (p : tcParam) :
    HasFDerivAt (tangentLinePsi r) (tangentLinePsiD r p) p := by
  have hdr : Differentiable ℝ r := hr.differentiable (by simp)
  have hrcS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.of_le le_top
  have hvcS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) :=
    (contDiff_infty_iff_deriv.mp hrcS).2
  have hvd : Differentiable ℝ (deriv r) := hvcS.differentiable (by simp)
  have h1 : HasFDerivAt (fun q : tcParam => r (tcSum q))
      (tcSum.smulRight (deriv r (tcSum p))) p := by
    have h := ((hdr.differentiableAt (x := tcSum p)).hasDerivAt.hasFDerivAt).comp p
      tcSum.hasFDerivAt
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smulRight_apply]
  have h2 : HasFDerivAt (fun q : tcParam => r (tcF1 q))
      (tcF1.smulRight (deriv r (tcF1 p))) p := by
    have h := ((hdr.differentiableAt (x := tcF1 p)).hasDerivAt.hasFDerivAt).comp p
      tcF1.hasFDerivAt
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smulRight_apply]
  have h3 : HasFDerivAt (fun q : tcParam => deriv r (tcF1 q))
      (tcF1.smulRight (deriv (deriv r) (tcF1 p))) p := by
    have h := ((hvd.differentiableAt (x := tcF1 p)).hasDerivAt.hasFDerivAt).comp p
      tcF1.hasFDerivAt
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smulRight_apply]
  have h4 : HasFDerivAt (fun q : tcParam => tcF3 q • deriv r (tcF1 q))
      (tcF3 p • tcF1.smulRight (deriv (deriv r) (tcF1 p)) +
        tcF3.smulRight (deriv r (tcF1 p))) p := by
    have h := tcF3.hasFDerivAt.smul h3
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with q
    rfl
  have htot := (h1.sub h2).sub h4
  refine htot.congr_of_eventuallyEq ?_
  filter_upwards with q
  rfl

lemma fderiv_tangentLinePsi {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (p : tcParam) :
    fderiv ℝ (tangentLinePsi r) p = tangentLinePsiD r p :=
  (hasFDerivAt_tangentLinePsi hr p).fderiv

lemma hasStrictFDerivAt_tangentLinePsi {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (p : tcParam) :
    HasStrictFDerivAt (tangentLinePsi r) (tangentLinePsiD r p) p := by
  rw [← fderiv_tangentLinePsi hr p]
  exact (contDiff_tangentLinePsi hr).contDiffAt.hasStrictFDerivAt (by simp)

lemma tangentLinePsiD_apply (r : ℝ → Space) (a μ h : ℝ) (v : tcParam) :
    tangentLinePsiD r ((a, μ), h) v
      = (v.1.1 + v.2) • deriv r (a + h) - (v.1.1 + v.1.2) • deriv r a
        - (μ * v.1.1) • deriv (deriv r) a := by
  simp only [tangentLinePsiD, tcSum_apply, tcF1_apply, tcF2_apply, tcF3_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  module

lemma tangentLinePsiD_injective {r : ℝ → Space} {a h μ : ℝ}
    (hli : LinearIndependent ℝ ![deriv r a, deriv (deriv r) a, deriv r (a + h)])
    (hμ : μ ≠ 0) : Function.Injective (tangentLinePsiD r ((a, μ), h)) := by
  set A : Space := deriv r (a + h) with hA
  set B : Space := deriv r a with hB
  set C : Space := deriv (deriv r) a with hC
  have hli' : LinearIndependent ℝ ![B, C, A] := hli
  have h1 : tangentLinePsiD r ((a, μ), h) ((1, 0), 0) = A - B - μ • C := by
    rw [tangentLinePsiD_apply]
    module
  have h2 : tangentLinePsiD r ((a, μ), h) ((0, 1), 0) = -B := by
    rw [tangentLinePsiD_apply]
    module
  have h3 : tangentLinePsiD r ((a, μ), h) ((0, 0), 1) = A := by
    rw [tangentLinePsiD_apply]
    module
  have himg : LinearIndependent ℝ ![A - B - μ • C, -B, A] := by
    rw [Fintype.linearIndependent_iff] at hli'
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • (A - B - μ • C) + g 1 • (-B) + g 2 • A = 0 := by
      simpa [Fin.sum_univ_three] using hg
    have key : g 0 • (A - B - μ • C) + g 1 • (-B) + g 2 • A
        = (-(g 0 + g 1)) • B + (-(μ * g 0)) • C + (g 0 + g 2) • A := by
      module
    rw [key] at hg'
    have h2' := hli' (fun i => ![-(g 0 + g 1), -(μ * g 0), g 0 + g 2] i)
      (by simpa [Fin.sum_univ_three] using hg')
    have hz0 : -(g 0 + g 1) = 0 := by simpa using h2' 0
    have hz1 : -(μ * g 0) = 0 := by simpa using h2' 1
    have hz2 : g 0 + g 2 = 0 := by simpa using h2' 2
    have hg0 : g 0 = 0 := (mul_eq_zero.mp (neg_eq_zero.mp hz1)).resolve_left hμ
    intro i
    fin_cases i
    · exact hg0
    · rw [hg0, zero_add] at hz0
      exact neg_eq_zero.mp hz0
    · rw [hg0, zero_add] at hz2
      exact hz2
  intro p q hpq
  have hker : tangentLinePsiD r ((a, μ), h) (p - q) = 0 := by rw [map_sub, hpq, sub_self]
  set v : tcParam := p - q with hv
  obtain ⟨⟨c1, c2⟩, c3⟩ := v
  have hker' : tangentLinePsiD r ((a, μ), h) ((c1, c2), c3) = 0 := hker
  have hdecomp : ((c1, c2), c3) = c1 • ((1, 0), 0) + c2 • ((0, 1), 0) + c3 • ((0, 0), 1) := by
    ext <;> simp
  rw [hdecomp, map_add, map_add, map_smul, map_smul, map_smul, h1, h2, h3] at hker'
  have hg := (Fintype.linearIndependent_iff.mp himg) (fun i => ![c1, c2, c3] i)
    (by simpa [Fin.sum_univ_three] using hker')
  have hc1 : c1 = 0 := hg 0
  have hc2 : c2 = 0 := hg 1
  have hc3 : c3 = 0 := hg 2
  have hzero : p - q = 0 := by
    rw [← hv, hdecomp, hc1, hc2, hc3]
    simp
  exact sub_eq_zero.mp hzero

lemma exists_injOn_nhds_tangentLinePsi {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {p₀ : tcParam}
    (hinj : Function.Injective (tangentLinePsiD r p₀)) :
    ∃ U : Set tcParam, IsOpen U ∧ p₀ ∈ U ∧ Set.InjOn (tangentLinePsi r) U := by
  have hfr : Module.finrank ℝ tcParam = 3 := by
    simp [tcParam, Module.finrank_prod, Module.finrank_self]
  have hfs : Module.finrank ℝ Space = 3 := by
    simp [Space]
  have hbij : Function.Bijective (tangentLinePsiD r p₀) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hfr, hfs])).mp hinj⟩
  let e : tcParam ≃ₗ[ℝ] Space := LinearEquiv.ofBijective (tangentLinePsiD r p₀).toLinearMap hbij
  have he : ((e.toContinuousLinearEquiv : tcParam →L[ℝ] Space)) = tangentLinePsiD r p₀ := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have hstrict : HasStrictFDerivAt (tangentLinePsi r)
      ((e.toContinuousLinearEquiv : tcParam →L[ℝ] Space)) p₀ := by
    rw [he]
    exact hasStrictFDerivAt_tangentLinePsi hr p₀
  set U := hstrict.toOpenPartialHomeomorph (tangentLinePsi r) with hU
  exact ⟨U.source, U.open_source, hstrict.mem_toOpenPartialHomeomorph_source, U.injOn⟩

/-! ## Chunk 5: local finiteness of the tangent chords -/

/-- A set is locally finite if every point has a neighbourhood meeting it finitely. -/
def LocallyFiniteSet (S : Set (ℝ × ℝ)) : Prop :=
  ∀ z : ℝ × ℝ, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ z ∈ U ∧ (S ∩ U).Finite

lemma sub_div_mul_self {Δ T : Space} (hT : T ≠ 0) (h : cross3 Δ T = 0) :
    Δ - (inner ℝ Δ T / ‖T‖ ^ 2) • T = 0 := by
  rcases (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul Δ T).mp h with h0 | ⟨t, ht⟩
  · rw [h0, inner_zero_left, zero_div, zero_smul, sub_zero]
  · have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ht
      exact hT ht
    have hΔ : Δ = t⁻¹ • T := by rw [ht, inv_smul_smul₀ ht0]
    have hT2 : (0:ℝ) < ‖T‖ ^ 2 := by
      have : 0 < ‖T‖ := norm_pos_iff.mpr hT
      positivity
    rw [hΔ, real_inner_smul_left, real_inner_self_eq_norm_sq, mul_div_assoc,
      div_self (ne_of_gt hT2), mul_one, sub_self]

lemma isolated_of_mem_tcSetA {r : ℝ → Space} (hr : IsSmoothKnot r) (htc : TangentChordGP r)
    {z : ℝ × ℝ} (hz : z ∈ tcSetA r) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ z ∈ U ∧ (tcSetA r ∩ U).Finite := by
  obtain ⟨hz1, hz2, htan⟩ := hz
  obtain ⟨hnotb, hin⟩ := (htc z.1 (z.1 + z.2) (by linarith) (by linarith)).1 htan
  have hΔne : r (z.1 + z.2) - r z.1 ≠ 0 := by
    intro h0
    rw [h0, cross3_zero_left] at hnotb
    exact hnotb rfl
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, r (z.1 + z.2) - r z.1 = lam • deriv r z.1 := by
    rcases (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul (r (z.1 + z.2) - r z.1)
      (deriv r z.1)).mp htan with h0 | ⟨t, ht⟩
    · exact absurd h0 hΔne
    · have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ht
        exact hr.regular z.1 ht
      exact ⟨t⁻¹, by rw [ht, inv_smul_smul₀ ht0]⟩
  have hlamne : lam ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hlam
    exact hΔne hlam
  have hli : LinearIndependent ℝ ![deriv r z.1, deriv (deriv r) z.1, deriv r (z.1 + z.2)] :=
    linearIndependent_of_inner_cross3_ne_zero hin
  obtain ⟨U₀, hU₀o, hU₀z, hU₀inj⟩ := exists_injOn_nhds_tangentLinePsi hr.smooth
    (tangentLinePsiD_injective (a := z.1) (h := z.2) (μ := lam) hli hlamne)
  have hvcS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) :=
    (contDiff_infty_iff_deriv.mp (hr.smooth.of_le le_top)).2
  set μfun : ℝ × ℝ → ℝ :=
    fun p => inner ℝ (r (p.1 + p.2) - r p.1) (deriv r p.1) / ‖deriv r p.1‖ ^ 2 with hμfun
  set U : Set (ℝ × ℝ) := {p | ((p.1, μfun p), p.2) ∈ U₀} with hU
  have hcont : Continuous fun p : ℝ × ℝ => ((p.1, μfun p), p.2) := by
    have hr1 : ContDiff ℝ 1 r := hr.smooth.of_le (by simp)
    have hv1 : ContDiff ℝ 1 (deriv r) := hvcS.of_le (by simp)
    have hnum : Continuous fun p : ℝ × ℝ => inner ℝ (r (p.1 + p.2) - r p.1) (deriv r p.1) := by
      fun_prop
    have hden : Continuous fun p : ℝ × ℝ => ‖deriv r p.1‖ ^ 2 := by fun_prop
    have hne : ∀ p : ℝ × ℝ, ‖deriv r p.1‖ ^ 2 ≠ 0 := by
      intro p
      have h := hr.regular p.1
      positivity
    have hdiv : Continuous fun p : ℝ × ℝ => μfun p := hnum.div hden hne
    exact (continuous_fst.prodMk hdiv).prodMk continuous_snd
  have hμz : μfun z = lam := by
    rw [hμfun]
    simp only []
    rw [hlam, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hT2 : (0:ℝ) < ‖deriv r z.1‖ ^ 2 := by
      have h := hr.regular z.1
      positivity
    rw [mul_div_assoc, div_self (ne_of_gt hT2), mul_one]
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hU]
    exact hU₀o.preimage hcont
  · rw [hU]
    show ((z.1, μfun z), z.2) ∈ U₀
    rw [hμz]
    exact hU₀z
  · refine Set.Finite.subset (Set.finite_singleton z) ?_
    rintro p ⟨hpA, hpU⟩
    obtain ⟨hp1, hp2, hptan⟩ := hpA
    rw [hU] at hpU
    have hkey : tangentLinePsi r ((p.1, μfun p), p.2) = 0 := by
      rw [tangentLinePsi_apply]
      show r (p.1 + p.2) - r p.1 - μfun p • deriv r p.1 = 0
      rw [hμfun]
      exact sub_div_mul_self (Δ := r (p.1 + p.2) - r p.1) (T := deriv r p.1)
        (hr.regular p.1) hptan
    have hkey0 : tangentLinePsi r ((z.1, lam), z.2) = 0 := by
      rw [tangentLinePsi_apply, hlam, sub_self]
    have huniq := hU₀inj hpU hU₀z (hkey.trans hkey0.symm)
    have h1 : p.1 = z.1 := by simpa using congrArg (fun q : tcParam => q.1.1) huniq
    have h2 : p.2 = z.2 := by simpa using congrArg (fun q : tcParam => q.2) huniq
    exact Prod.ext h1 h2

lemma not_mem_tcSetA_near_boundary {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) {z : ℝ × ℝ}
    (hz : z.2 ≤ 0 ∨ period ≤ z.2) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ z ∈ U ∧ ∀ p ∈ tcSetA r, p ∈ U → False := by
  obtain ⟨ε, hε, δ, hδ, hbnd⟩ := tangentChordBoundary_local hr hinfl z.1
  have hopen : IsOpen {p : ℝ × ℝ | |p.1 - z.1| < δ ∧ |p.2 - z.2| < ε} :=
    (isOpen_lt (by fun_prop : Continuous fun p : ℝ × ℝ => |p.1 - z.1|) continuous_const).inter
      (isOpen_lt (by fun_prop : Continuous fun p : ℝ × ℝ => |p.2 - z.2|) continuous_const)
  have hmem : z ∈ {p : ℝ × ℝ | |p.1 - z.1| < δ ∧ |p.2 - z.2| < ε} := by
    constructor <;> simp [hδ, hε]
  refine ⟨_, hopen, hmem, ?_⟩
  rintro p ⟨hp1, hp2, hptan⟩ ⟨h1, h2⟩
  rcases hz with hz0 | hzp
  · have hpos : 0 < p.2 := hp1
    have hlt : p.2 < ε := by
      have := (abs_lt.mp h2).2
      linarith
    exact hbnd p.1 h1 p.2 (by simpa [abs_of_pos hpos] using hpos)
      (by simpa [abs_of_pos hpos] using hlt) hptan
  · set η : ℝ := period - p.2 with hη
    have hηpos : 0 < η := by rw [hη]; linarith [hp2]
    have hηε : η < ε := by
      have := (abs_lt.mp h2).1
      rw [hη]
      linarith
    have harg : p.1 + p.2 = (p.1 - η) + period := by rw [hη]; ring
    have hper : r (p.1 + p.2) = r (p.1 - η) := by
      rw [harg]
      exact hr.periodic (p.1 - η)
    have htan' : cross3 (r (p.1 - η) - r p.1) (deriv r p.1) = 0 := by
      rw [← hper]
      exact hptan
    have := hbnd p.1 h1 (-η) (by simpa [abs_neg, abs_of_pos hηpos] using hηpos)
      (by simpa [abs_neg, abs_of_pos hηpos] using hηε) htan'
    exact this

lemma locallyFinite_tcSetA {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (htc : TangentChordGP r) : LocallyFiniteSet (tcSetA r) := by
  intro z
  by_cases hz : z ∈ tcSetA r
  · exact isolated_of_mem_tcSetA hr htc hz
  · by_cases hb : z.2 ≤ 0 ∨ period ≤ z.2
    · obtain ⟨U, hUo, hUz, hUe⟩ := not_mem_tcSetA_near_boundary hr hinfl hb
      refine ⟨U, hUo, hUz, ?_⟩
      refine Set.Finite.subset Set.finite_empty ?_
      rintro p ⟨hpA, hpU⟩
      exact hUe p hpA hpU
    · push_neg at hb
      obtain ⟨hb1, hb2⟩ := hb
      have hcross : cross3 (r (z.1 + z.2) - r z.1) (velocity r z.1) ≠ 0 := by
        intro h0
        exact hz ⟨hb1, hb2, h0⟩
      have hcont : Continuous fun p : ℝ × ℝ =>
          cross3 (r (p.1 + p.2) - r p.1) (velocity r p.1) :=
        continuous_tangentChordCross hr
      refine ⟨(fun p : ℝ × ℝ => cross3 (r (p.1 + p.2) - r p.1) (velocity r p.1)) ⁻¹' {0}ᶜ,
        hcont.isOpen_preimage _ isOpen_compl_singleton, hcross, ?_⟩
      refine Set.Finite.subset Set.finite_empty ?_
      rintro p ⟨hpA, hpU⟩
      exact hpU hpA.2.2

/-! ## Chunk 6: the second endpoint, and the theorem -/

/-- The involution swapping the two endpoints of a chord. -/
def tcFlip (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + p.2, period - p.2)

lemma tcFlip_injective : Function.Injective tcFlip := by
  intro p q h
  simp only [tcFlip, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h2' : p.2 = q.2 := by linarith
  exact Prod.ext (by linarith) h2'

lemma tcFlip_continuous : Continuous tcFlip := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_fst.add continuous_snd
  · exact continuous_const.sub continuous_snd

lemma tcFlip_mem_tcSetA_iff {r : ℝ → Space} (hr : IsSmoothKnot r) (p : ℝ × ℝ) :
    tcFlip p ∈ tcSetA r ↔ p ∈ tcSetB r := by
  have harg : p.1 + p.2 + (period - p.2) = p.1 + period := by ring
  have hcross : cross3 (r (p.1 + p.2 + (period - p.2)) - r (p.1 + p.2))
        (velocity r (p.1 + p.2))
      = -cross3 (r (p.1 + p.2) - r p.1) (velocity r (p.1 + p.2)) := by
    rw [harg, hr.periodic p.1]
    rw [show r p.1 - r (p.1 + p.2) = -(r (p.1 + p.2) - r p.1) by rw [neg_sub]]
    rw [cross3_neg_left]
  simp only [tcSetA, tcSetB, Set.mem_setOf_eq, tcFlip]
  rw [hcross]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith [period_pos], by linarith, by simpa using h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith [period_pos], by linarith, by simpa using h3⟩

lemma locallyFinite_tcSetB {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hA : LocallyFiniteSet (tcSetA r)) : LocallyFiniteSet (tcSetB r) := by
  intro z
  obtain ⟨U, hUo, hUz, hUf⟩ := hA (tcFlip z)
  refine ⟨tcFlip ⁻¹' U, hUo.preimage tcFlip_continuous, hUz, ?_⟩
  refine Set.Finite.subset (hUf.preimage (fun a _ b _ hab => tcFlip_injective hab)) ?_
  rintro p ⟨hpB, hpU⟩
  exact ⟨(tcFlip_mem_tcSetA_iff hr p).mpr hpB, hpU⟩

open LeanEval.KnotTheory.Quadrisecant in
theorem tangentChordLocallyFinite {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (htc : TangentChordGP r) :
    ∀ z : ℝ × ℝ, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ z ∈ U ∧
      (({p : ℝ × ℝ | 0 < p.2 ∧ p.2 < period ∧
          (cross3 (r (p.1 + p.2) - r p.1) (velocity r p.1) = 0 ∨
           cross3 (r (p.1 + p.2) - r p.1) (velocity r (p.1 + p.2)) = 0)} ∩ U).Finite) := by
  intro z
  obtain ⟨U₁, hU₁o, hU₁z, hU₁f⟩ := locallyFinite_tcSetA hr hinfl htc z
  obtain ⟨U₂, hU₂o, hU₂z, hU₂f⟩ := locallyFinite_tcSetB hr (locallyFinite_tcSetA hr hinfl htc) z
  refine ⟨U₁ ∩ U₂, hU₁o.inter hU₂o, ⟨hU₁z, hU₂z⟩, ?_⟩
  refine Set.Finite.subset (hU₁f.union hU₂f) ?_
  rintro p ⟨hp, hpU⟩
  obtain ⟨hp1, hp2, hpx⟩ := hp
  obtain ⟨hpU1, hpU2⟩ := hpU
  rcases hpx with h | h
  · exact Or.inl ⟨⟨hp1, hp2, h⟩, hpU1⟩
  · exact Or.inr ⟨⟨hp1, hp2, h⟩, hpU2⟩

end
end Work.Drive
