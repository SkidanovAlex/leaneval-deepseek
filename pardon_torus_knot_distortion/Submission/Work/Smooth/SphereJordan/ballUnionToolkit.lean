import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.loopSharedLemmas

/-!
# Toolkit: circles, arcs and frontiers of unions of equal closed discs

This module collects the geometric and index-theoretic toolkit shared by the proof of
`Work.Smooth.SphereJordan.existsLogPath` and by the (parallel) proof of the frontier-loop lemma
`loopInFrontierBallUnion` in its general form:

* the circle loop `circleLoop r`, the translated circle `sphereLoop w r`, and the computation
  `loopIndex_sphereLoop : ‖w‖ < r → loopIndex (sphereLoop w r) = 1`;
* `loopInFrontier_singleton`, `sphere_subset_frontier_union_pair`, `loopInFrontier_pair_disjoint`:
  the elementary cases of the frontier loop;
* the explicit junction points `circleIntersection a b κ` of two equal circles
  (`dist_circleIntersection`, `circleIntersection_mem_frontier`);
* the perpendicular-step estimates (`normSq_add_ofReal_mul_I_mul`, `dist_perp_step_gt`, ...) and the
  visible-arc criteria `frontier_of_sphere_point_of_dist_gt`, `frontier_of_sphere_point_of_dist_ge`,
  `sphere_sdiff_ball_subset_frontier`.

Everything here is `sorry`-free and axiom-clean; it is deliberately placed *upstream* of
`existsLogPath` so that it can be reused without an import cycle.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

theorem exp_two_pi_I : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
  rw [Complex.exp_eq_one_iff]
  refine ⟨1, ?_⟩
  push_cast
  ring

/-- The circle of radius `r` as a loop. -/
def circleLoop (r : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun s : unitInterval => (r : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℝ)),
    by fun_prop⟩

theorem circleLoop_apply (r : ℝ) (s : unitInterval) :
    circleLoop r s = (r : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℝ)) := rfl

theorem norm_exp_two_pi_I_mul (s : ℝ) : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * ((s : ℝ) : ℂ)).re = 0 := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((s : ℝ) : ℂ)
        = (((2 * Real.pi * s : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  rw [hre, Real.exp_zero]

theorem norm_circleLoop (r : ℝ) (hr : 0 < r) (s : unitInterval) : ‖circleLoop r s‖ = r := by
  rw [circleLoop_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    show (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ)) = 2 * (Real.pi : ℂ) * Complex.I * ((s : ℝ) : ℂ) from rfl,
    norm_exp_two_pi_I_mul, mul_one]

theorem loopIndex_circleLoop (r : ℝ) (hr : 0 < r) : loopIndex (circleLoop r) = 1 :=
  Work.Smooth.SphereJordan.loopIndex_circle r hr

theorem circleLoop_zero (r : ℝ) : circleLoop r 0 = (r : ℂ) := by
  rw [circleLoop_apply]
  show (r : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((0 : ℝ) : ℂ)) = (r : ℂ)
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

theorem circleLoop_one (r : ℝ) : circleLoop r 1 = (r : ℂ) := by
  rw [circleLoop_apply]
  show (r : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ)) = (r : ℂ)
  rw [Complex.ofReal_one, mul_one, exp_two_pi_I, mul_one]


/-- **Covering a compact plane set by finitely many small balls centred in it.**

This is the geometric input of the shell lemma: a compact `K` is the union of finitely many
balls of radius `ε/4` whose centres lie in `K`.  It is proved from compactness via
`IsCompact.elim_finite_subcover`. -/
theorem exists_ballUnion_cover {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : Finset ℂ), (∀ w ∈ P, w ∈ K) ∧ K ⊆ ⋃ w ∈ P, Metric.ball w (ε / 4) := by
  classical
  have hcov : K ⊆ ⋃ x : K, Metric.ball (x : ℂ) (ε / 4) := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, by rw [Metric.mem_ball, dist_self]; positivity⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball (x : ℂ) (ε / 4))
    (fun _ => Metric.isOpen_ball) hcov
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro w hw
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hw
    exact x.2
  · intro z hz
    obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.mp (ht hz)
    exact Set.mem_iUnion₂.mpr ⟨(x : ℂ), Finset.mem_image.mpr ⟨x, hxt, rfl⟩, hzx⟩

/-- **The frontier of the union of the balls of radius `ε/2` is disjoint from `K`, and each of its
points is within `ε` of `K`.**

Both halves are pure geometry: a point of `K` lies in some ball of radius `ε/4` around a centre in
`K`, hence in the *interior* of the union of the balls of radius `ε/2` and so cannot be on the
frontier; conversely a frontier point lies in the (closed) union, hence in some closed ball of
radius `ε/2` around a centre in `K`, and `ε/2 ≤ ε`. -/
theorem frontier_closedBall_union_spec {K : Set ℂ} {ε : ℝ} (hε : 0 < ε) {P : Finset ℂ}
    (hPK : ∀ w ∈ P, w ∈ K) (hcov : K ⊆ ⋃ w ∈ P, Metric.ball w (ε / 4)) :
    (∀ z ∈ frontier (⋃ w ∈ P, Metric.closedBall w (ε / 2)), z ∉ K) ∧
      (∀ z ∈ frontier (⋃ w ∈ P, Metric.closedBall w (ε / 2)), ∃ k ∈ K, dist z k ≤ ε) := by
  have hclosed : IsClosed (⋃ w ∈ P, Metric.closedBall w (ε / 2)) :=
    isClosed_biUnion_finset fun w _ => Metric.isClosed_closedBall
  constructor
  · intro z hz hzK
    obtain ⟨w, hwP, hw⟩ := Set.mem_iUnion₂.mp (hcov hzK)
    rw [Metric.mem_ball] at hw
    have hsub : Metric.ball w (ε / 2) ⊆ ⋃ w ∈ P, Metric.closedBall w (ε / 2) :=
      fun y hy => Set.mem_iUnion₂.mpr
        ⟨w, hwP, (Metric.mem_closedBall.mpr (le_of_lt ((Metric.mem_ball.mp hy).trans_le
          (by linarith))))⟩
    have hint : Metric.ball w (ε / 2) ⊆ interior (⋃ w ∈ P, Metric.closedBall w (ε / 2)) :=
      interior_maximal hsub Metric.isOpen_ball
    exact hz.2 (hint (by rw [Metric.mem_ball]; linarith))
  · intro z hz
    have hzmem : z ∈ ⋃ w ∈ P, Metric.closedBall w (ε / 2) := by
      have h := hz.1
      rwa [hclosed.closure_eq] at h
    obtain ⟨w, hwP, hw⟩ := Set.mem_iUnion₂.mp hzmem
    exact ⟨w, hPK w hwP, le_trans (Metric.mem_closedBall.mp hw) (by linarith)⟩

/-- **The shell lemma from the frontier loop.**

If for every finite union of equal closed balls whose interior contains `0` there is a loop in its
frontier of index `1` (with a choice of orientation, so the statement is the oriented one), then
the shell lemma `existsShellLoop` holds: take the finite cover of `K` by balls of radius `ε/4`,
apply the frontier loop to the union of the balls of radius `ε/2`, and use
`frontier_closedBall_union_spec` to see that this loop avoids `K` while staying within `ε` of it. -/
def sphereLoop (w : ℂ) (r : ℝ) : C(unitInterval, ℂ) :=
  ContinuousMap.const unitInterval w + circleLoop r

theorem sphereLoop_apply (w : ℂ) (r : ℝ) (t : unitInterval) :
    sphereLoop w r t = w + circleLoop r t := rfl

/-- **A translated circle has index `1` when it surrounds the origin.**

This is the mathematical content of the single-disc case of
`loopInFrontierOfBallUnion`: the loop `t ↦ w + r e^{2πit}` with `‖w‖ < r` winds once around `0`.
The index is transported from the standard circle `circleLoop r` (`loopIndex_circleLoop`) by
`loopIndex_eq_of_pointwise_div_mem_slitPlane`: the pointwise quotient is
`1 + w / (r e^{2πit})`, whose real part is `> 0` because `‖w / (r e^{2πit})‖ = ‖w‖/r < 1`. -/
theorem loopIndex_sphereLoop (w : ℂ) {r : ℝ} (hr : 0 < r) (hw : ‖w‖ < r) :
    Work.Smooth.SphereJordan.loopIndex (sphereLoop w r) = 1 := by
  have hv : ∀ t, circleLoop r t ≠ 0 := fun t => by
    rw [← norm_pos_iff, norm_circleLoop r hr t]
    exact hr
  have hu : ∀ t, sphereLoop w r t ≠ 0 := by
    intro t h
    have h0 : w + circleLoop r t = 0 := by rwa [sphereLoop_apply] at h
    have h3 : ‖(w + circleLoop r t) - w‖ ≤ ‖w + circleLoop r t‖ + ‖w‖ := norm_sub_le _ _
    rw [add_sub_cancel_left, h0, norm_zero, zero_add, norm_circleLoop r hr t] at h3
    linarith
  have hlu : sphereLoop w r 0 = sphereLoop w r 1 := by
    rw [sphereLoop_apply, sphereLoop_apply, circleLoop_zero, circleLoop_one]
  have hlv : circleLoop r 0 = circleLoop r 1 := by
    rw [circleLoop_zero, circleLoop_one]
  have hdiv : ∀ t, sphereLoop w r t / circleLoop r t ∈ Complex.slitPlane := by
    intro t
    rw [sphereLoop_apply, add_div, div_self (hv t), Complex.slitPlane]
    left
    rw [Complex.add_re, Complex.one_re]
    have hnorm : ‖w / circleLoop r t‖ < 1 := by
      rw [norm_div, norm_circleLoop r hr t, div_lt_one hr]
      exact hw
    have hre : -(‖w / circleLoop r t‖) ≤ (w / circleLoop r t).re := by
      have h := Complex.abs_re_le_norm (w / circleLoop r t)
      rw [abs_le] at h
      exact h.1
    linarith
  have h := Work.Smooth.SphereJordan.loopIndex_eq_of_pointwise_div_mem_slitPlane
    (sphereLoop w r) (circleLoop r) hu hv hlu hlv hdiv
  rw [h, loopIndex_circleLoop r hr]

/-- **The single-disc case of the frontier loop.**

For `P = {w}` the union is the closed ball `closedBall w r`, whose frontier is the sphere
`sphere w r` (`frontier_closedBall`); the loop `sphereLoop w r` runs in that sphere and has index
`1` by `loopIndex_sphereLoop`.  This is the `P = {w}` case of
`loopInFrontierOfBallUnion`, the first slab of the arc-tracing argument. -/
theorem loopInFrontier_singleton (w : ℂ) {r : ℝ} (hr : 0 < r) (hw : ‖w‖ < r) :
    ∃ c : C(unitInterval, ℂ),
      (∀ t, c t ∈ frontier (⋃ u ∈ ({w} : Finset ℂ), Metric.closedBall u r)) ∧
      c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c = 1 := by
  have hfront : (⋃ u ∈ ({w} : Finset ℂ), Metric.closedBall u r) = Metric.closedBall w r := by
    ext z
    simp only [Set.mem_iUnion, Finset.mem_singleton]
    constructor
    · rintro ⟨u, rfl, hz⟩
      exact hz
    · intro hz
      exact ⟨w, rfl, hz⟩
  refine ⟨sphereLoop w r, ?_, ?_, loopIndex_sphereLoop w hr hw⟩
  · intro t
    rw [hfront, frontier_closedBall w (ne_of_gt hr)]
    exact Metric.mem_sphere.mpr (by
      rw [dist_eq_norm, sphereLoop_apply, add_sub_cancel_left, norm_circleLoop r hr t])
  · rw [sphereLoop_apply, sphereLoop_apply, circleLoop_zero, circleLoop_one]

/-- **Two disjoint discs: the sphere of either disc lies in the frontier of the union.** -/
theorem sphere_subset_frontier_union_pair {a b : ℂ} {r : ℝ} (hr : 0 < r) (h : 2 * r < dist a b) :
    Metric.sphere a r ⊆ frontier (Metric.closedBall a r ∪ Metric.closedBall b r) := by
  intro x hx
  have hxa : dist x a = r := Metric.mem_sphere.mp hx
  have hxb : r < dist x b := by
    have h1 : dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
    rw [dist_comm a x, hxa] at h1
    linarith
  refine ⟨subset_closure (Or.inl (Metric.sphere_subset_closedBall hx)), ?_⟩
  intro hint
  have hnotmem : ¬ x ∈ closure ((Metric.closedBall a r ∪ Metric.closedBall b r)ᶜ) := by
    rw [closure_compl]
    simpa using hint
  refine hnotmem (Metric.mem_closure_iff.mpr ?_)
  intro ε hε
  set t : ℝ := min ε (dist x b - r) / 4 with ht
  have htε : t < ε := by
    rw [ht]
    have hle : min ε (dist x b - r) ≤ ε := min_le_left _ _
    linarith
  have htd : t < dist x b - r := by
    rw [ht]
    have hle : min ε (dist x b - r) ≤ dist x b - r := min_le_right _ _
    linarith
  have htpos : 0 < t := by
    rw [ht]
    exact div_pos (lt_min hε (by linarith)) (by norm_num)
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  set u : ℂ := (x - a) / (r : ℂ) with hu
  have hnormu : ‖u‖ = 1 := by
    rw [hu, norm_div, ← dist_eq_norm, hxa, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact div_self (ne_of_gt hr)
  have hxau : x - a = (r : ℂ) * u := by
    rw [hu]
    field_simp [hrne]
  set y : ℂ := x + (t : ℂ) * u with hy
  have hxy : dist x y = t := by
    have hsub : x - y = -((t : ℂ) * u) := by
      rw [hy]
      ring
    rw [dist_eq_norm, hsub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos, hnormu, mul_one]
  have hya : dist y a = r + t := by
    have hsub : y - a = (((r + t : ℝ)) : ℂ) * u := by
      rw [hy]
      have e : (x + (t : ℂ) * u) - a = (x - a) + (t : ℂ) * u := by ring
      rw [e, hxau]
      push_cast
      ring
    rw [dist_eq_norm, hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ r + t), hnormu, mul_one]
  refine ⟨y, ?_, ?_⟩
  · rw [Set.mem_compl_iff, Set.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, hya]
      linarith
    · rw [Metric.mem_closedBall]
      have h3 : dist x b ≤ dist x y + dist y b := dist_triangle _ _ _
      rw [hxy] at h3
      linarith
  · rw [hxy]
    exact htε

/-- **Disjoint two-disc case of the frontier loop.** -/
theorem loopInFrontier_pair_disjoint (a b : ℂ) {r : ℝ} (hr : 0 < r) (h : 2 * r < dist a b)
    (h0 : (0 : ℂ) ∈ Metric.ball a r) :
    ∃ c : C(unitInterval, ℂ),
      (∀ t, c t ∈ frontier (⋃ u ∈ ({a, b} : Finset ℂ), Metric.closedBall u r)) ∧
      c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c = 1 := by
  have hfront : (⋃ u ∈ ({a, b} : Finset ℂ), Metric.closedBall u r) =
      Metric.closedBall a r ∪ Metric.closedBall b r := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨u, rfl | rfl, hz⟩
      · exact Or.inl hz
      · exact Or.inr hz
    · rintro (hz | hz)
      · exact ⟨a, Or.inl rfl, hz⟩
      · exact ⟨b, Or.inr rfl, hz⟩
  have hwa : ‖a‖ < r := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at h0
    simpa using h0
  refine ⟨sphereLoop a r, ?_, ?_, loopIndex_sphereLoop a hr hwa⟩
  · intro t
    rw [hfront]
    refine sphere_subset_frontier_union_pair hr h ?_
    rw [Metric.mem_sphere, dist_eq_norm, sphereLoop_apply, add_sub_cancel_left,
      norm_circleLoop r hr t]
  · rw [sphereLoop_apply, sphereLoop_apply, circleLoop_zero, circleLoop_one]

/-- **The algebraic heart of the peanut (overlapping two-disc) case.**

Rotating `u` by `90°` and scaling by the real number `c` produces a displacement perpendicular to
`u`, so Pythagoras gives `normSq (u + c·(I·u)) = (1 + c²)·normSq u`.  The proof pulls the factor out,
`u + (c:ℂ)·(I·u) = u·(1 + (c:ℂ)·I)`, evaluates `normSq (1 + (c:ℂ)·I) = 1 + c²` from real and
imaginary parts, and derives multiplicativity of `normSq` from `norm_mul` and
`Complex.normSq_eq_norm_sq`. -/
theorem normSq_add_ofReal_mul_I_mul (u : ℂ) (c : ℝ) :
    Complex.normSq (u + (c : ℂ) * (Complex.I * u)) = (1 + c ^ 2) * Complex.normSq u := by
  have hfac : u + (c : ℂ) * (Complex.I * u) = u * (1 + (c : ℂ) * Complex.I) := by ring
  have hmul : Complex.normSq (u * (1 + (c : ℂ) * Complex.I)) =
      Complex.normSq u * Complex.normSq (1 + (c : ℂ) * Complex.I) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, norm_mul]
    ring
  have hone : Complex.normSq (1 + (c : ℂ) * Complex.I) = 1 + c ^ 2 := by
    simp [Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    ring
  rw [hfac, hmul, hone]
  ring

/-- **The intersection points of two equal circles.**  For `a ≠ b` the two circles
`sphere a r` and `sphere b r` meet at `(a + b)/2 ± κ · (I · (b - a)/‖b - a‖)`, where
`κ = ± Real.sqrt (r² - (‖b - a‖/2)²)`. -/
noncomputable def circleIntersection (a b : ℂ) (κ : ℝ) : ℂ :=
  (a + b) / 2 + (κ : ℂ) * (Complex.I * ((b - a) / ((‖b - a‖ : ℝ) : ℂ)))

/-- The radicand in the peanut construction is nonnegative when the circles overlap. -/
theorem peanut_sqrt_arg_nonneg (a b : ℂ) {r : ℝ} (hd : ‖b - a‖ < 2 * r) :
    0 ≤ r ^ 2 - (‖b - a‖ / 2) ^ 2 := by
  have h1 : ‖b - a‖ / 2 < r := by linarith
  have h2 : 0 ≤ ‖b - a‖ / 2 := by positivity
  nlinarith

/-- **The peanut intersection points lie on both spheres.**

If `a ≠ b` and `κ ^ 2 = r ^ 2 - (‖b - a‖ / 2) ^ 2` then `circleIntersection a b κ` is at distance `r`
from both `a` and `b`.  (For `0 < r` and `‖b - a‖ < 2 * r`, `κ := ±Real.sqrt (r^2 - (‖b-a‖/2)^2)`
gives the two genuine intersection points.) -/
theorem dist_circleIntersection (a b : ℂ) {r κ : ℝ} (hr : 0 < r) (hab : a ≠ b)
    (hκ : κ ^ 2 = r ^ 2 - (‖b - a‖ / 2) ^ 2) :
    dist (circleIntersection a b κ) a = r ∧ dist (circleIntersection a b κ) b = r := by
  set d : ℝ := ‖b - a‖ with hddef
  have hd0 : d ≠ 0 := by
    rw [hddef, norm_ne_zero_iff]
    exact sub_ne_zero.mpr (Ne.symm hab)
  have hdcast : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hrepr : circleIntersection a b κ =
      (a + b) / 2 + ((κ / d : ℝ) : ℂ) * (Complex.I * (b - a)) := by
    rw [circleIntersection, hddef]
    congr 1
    rw [div_eq_mul_inv, div_eq_mul_inv]
    push_cast
    ring
  have hu2 : Complex.normSq ((b - a) / 2) = (d / 2) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, norm_div, hddef]
    norm_num
  have h4 : (2 * (κ / d)) ^ 2 * (d / 2) ^ 2 = κ ^ 2 := by
    field_simp [hd0]
  constructor
  · rw [dist_eq_norm]
    have hsub : (a + b) / 2 + ((κ / d : ℝ) : ℂ) * (Complex.I * (b - a)) - a =
        (b - a) / 2 + ((2 * (κ / d) : ℝ) : ℂ) * (Complex.I * ((b - a) / 2)) := by
      push_cast
      ring
    have hs : Complex.normSq (circleIntersection a b κ - a) = r ^ 2 := by
      rw [hrepr, hsub, normSq_add_ofReal_mul_I_mul, hu2]
      nlinarith [h4, hκ]
    have hsq : ‖circleIntersection a b κ - a‖ ^ 2 = r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hs
    nlinarith [norm_nonneg (circleIntersection a b κ - a)]
  · rw [dist_eq_norm]
    have hsub : (a + b) / 2 + ((κ / d : ℝ) : ℂ) * (Complex.I * (b - a)) - b =
        (a - b) / 2 + ((-(2 * (κ / d)) : ℝ) : ℂ) * (Complex.I * ((a - b) / 2)) := by
      push_cast
      ring
    have hub : Complex.normSq ((a - b) / 2) = (d / 2) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, norm_div]
      have h1 : ‖a - b‖ = d := by rw [hddef, norm_sub_rev]
      rw [h1]
      norm_num
    have hs : Complex.normSq (circleIntersection a b κ - b) = r ^ 2 := by
      rw [hrepr, hsub, normSq_add_ofReal_mul_I_mul, hub]
      have h4' : (-(2 * (κ / d))) ^ 2 * (d / 2) ^ 2 = κ ^ 2 := by
        rw [neg_sq]; exact h4
      nlinarith [h4', hκ]
    have hsq : ‖circleIntersection a b κ - b‖ ^ 2 = r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hs
    nlinarith [norm_nonneg (circleIntersection a b κ - b)]

/-- **A point of `sphere a r` strictly outside `closedBall b r` lies in the frontier of the union.**

This is Case `r < dist z b` of `frontier_of_sphere_point_of_dist_ge`, proved by the radial-step
argument: a small step radially outward from `a` past `z` gives points arbitrarily close to `z` that
are outside both closed balls (the estimate on `b` uses `dist z b - t > r`). -/
theorem frontier_of_sphere_point_of_dist_gt {a b : ℂ} {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : dist z a = r) (hzb : r < dist z b) :
    z ∈ frontier (Metric.closedBall a r ∪ Metric.closedBall b r) := by
  refine ⟨subset_closure (Or.inl (Metric.mem_closedBall.mpr (le_of_eq hz))), ?_⟩
  intro hint
  have hnotmem : ¬ z ∈ closure ((Metric.closedBall a r ∪ Metric.closedBall b r)ᶜ) := by
    rw [closure_compl]
    simpa using hint
  refine hnotmem (Metric.mem_closure_iff.mpr ?_)
  intro ε hε
  set t : ℝ := min ε (dist z b - r) / 4 with ht
  have htε : t < ε := by
    rw [ht]
    have hle : min ε (dist z b - r) ≤ ε := min_le_left _ _
    linarith
  have htd : t < dist z b - r := by
    rw [ht]
    have hle : min ε (dist z b - r) ≤ dist z b - r := min_le_right _ _
    linarith
  have htpos : 0 < t := by
    rw [ht]
    exact div_pos (lt_min hε (by linarith)) (by norm_num)
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  set u : ℂ := (z - a) / (r : ℂ) with hu
  have hnormu : ‖u‖ = 1 := by
    rw [hu, norm_div, ← dist_eq_norm, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact div_self (ne_of_gt hr)
  have hzau : z - a = (r : ℂ) * u := by
    rw [hu]
    field_simp [hrne]
  set y : ℂ := z + (t : ℂ) * u with hy
  have hzy : dist z y = t := by
    have hsub : z - y = -((t : ℂ) * u) := by
      rw [hy]
      ring
    rw [dist_eq_norm, hsub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos, hnormu, mul_one]
  have hya : dist y a = r + t := by
    have hsub : y - a = (((r + t : ℝ)) : ℂ) * u := by
      rw [hy]
      have e : (z + (t : ℂ) * u) - a = (z - a) + (t : ℂ) * u := by ring
      rw [e, hzau]
      push_cast
      ring
    rw [dist_eq_norm, hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ r + t), hnormu, mul_one]
  refine ⟨y, ?_, ?_⟩
  · rw [Set.mem_compl_iff, Set.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, hya]
      linarith
    · rw [Metric.mem_closedBall]
      have h3 : dist z b ≤ dist z y + dist y b := dist_triangle _ _ _
      rw [hzy] at h3
      linarith
  · rw [hzy]
    exact htε

/-- **Case B, `a`-side of the arc sub-piece.**

Stepping perpendicular to `z - a` (by `(t/r)·(I·(z-a))`) strictly increases the squared distance to
`a`: `dist y a ^ 2 = (1 + (t/r)^2) * r^2` when `dist z a = r`.  The heart lemma
`normSq_add_ofReal_mul_I_mul` does the work; note the identity needs no hypothesis on `r` or `t`. -/
theorem dist_perp_step_sq (a z : ℂ) {r t : ℝ} (hz : dist z a = r) :
    dist (z + ((t / r : ℝ) : ℂ) * (Complex.I * (z - a))) a ^ 2 =
      (1 + (t / r) ^ 2) * r ^ 2 := by
  have hsub : z + ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - a =
      (z - a) + ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) := by ring
  have hnorm : Complex.normSq (z - a) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, ← dist_eq_norm, hz]
  rw [dist_eq_norm, hsub, ← Complex.normSq_eq_norm_sq, normSq_add_ofReal_mul_I_mul, hnorm]

/-- **The second-order expansion of `normSq` under a perpendicular step.**

    normSq (u + s·(I·v)) = normSq u + 2 s · Im (u * star v) + s² · normSq v

The `b`-side of the arc sub-piece instantiates this with `u := z - b`, `v := z - a`, `s := ±t/r`. -/
theorem normSq_add_ofReal_mul_I (u v : ℂ) (s : ℝ) :
    Complex.normSq (u + (s : ℂ) * (Complex.I * v)) =
      Complex.normSq u + 2 * s * (u * star v).im + s ^ 2 * Complex.normSq v := by
  have him : (star v).im = -v.im := by simp
  have hre : (star v).re = v.re := by simp
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, him, hre]
  ring

/-- **Case B, `b`-side: the perpendicular step increases the distance to `b` when the sign is right.**

If `dist z a = dist z b = r` and `Im ((z - b) * star (z - a)) ≥ 0`, then stepping perpendicular to
`z - a` by `(t/r)·(I·(z - a))` (for `0 < t`) gives a point at distance `> r` from `b` as well.  This
uses `normSq_add_ofReal_mul_I` for the expansion and `dist_perp_step_sq` for the `a`-side; the sign
split on `Im ((z - b) * star (z - a))` is the only branch of Case B. -/
theorem dist_perp_step_gt_of_im_nonneg {a b z : ℂ} {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hza : dist z a = r) (hzb : dist z b = r)
    (hsgn : 0 ≤ ((z - b) * star (z - a)).im) :
    r < dist (z + ((t / r : ℝ) : ℂ) * (Complex.I * (z - a))) b := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hsub : z + ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - b =
      (z - b) + ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) := by ring
  have hna : Complex.normSq (z - a) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, ← dist_eq_norm, hza]
  have hnb : Complex.normSq (z - b) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, ← dist_eq_norm, hzb]
  have hs : Complex.normSq (z + ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - b) =
      r ^ 2 + t ^ 2 + 2 * (t / r) * ((z - b) * star (z - a)).im := by
    rw [hsub, normSq_add_ofReal_mul_I, hna, hnb]
    field_simp
    ring
  have htr : 0 < t / r := div_pos ht hr
  have hnn : 0 ≤ 2 * (t / r) * ((z - b) * star (z - a)).im :=
    mul_nonneg (mul_nonneg (by norm_num) htr.le) hsgn
  have hgt : r ^ 2 < ‖z + ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - b‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hs]
    nlinarith [hnn, mul_pos ht ht]
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (z + ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - b)]

/-- **Case B, `b`-side, opposite sign: the reversed perpendicular step works when `Im ≤ 0`.** -/
theorem dist_perp_step_gt_of_im_nonpos {a b z : ℂ} {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hza : dist z a = r) (hzb : dist z b = r)
    (hsgn : ((z - b) * star (z - a)).im ≤ 0) :
    r < dist (z - ((t / r : ℝ) : ℂ) * (Complex.I * (z - a))) b := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hsub : z - ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - b =
      (z - b) + ((-(t / r) : ℝ) : ℂ) * (Complex.I * (z - a)) := by
    push_cast
    ring
  have hna : Complex.normSq (z - a) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, ← dist_eq_norm, hza]
  have hnb : Complex.normSq (z - b) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, ← dist_eq_norm, hzb]
  have hs : Complex.normSq (z - ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - b) =
      r ^ 2 + t ^ 2 + 2 * (t / r) * (-(((z - b) * star (z - a)).im)) := by
    rw [hsub, normSq_add_ofReal_mul_I, hna, hnb]
    field_simp [hr0]
    ring
  have htr : 0 < t / r := div_pos ht hr
  have hnn : 0 ≤ 2 * (t / r) * (-(((z - b) * star (z - a)).im)) :=
    mul_nonneg (mul_nonneg (by norm_num) htr.le) (neg_nonneg.mpr hsgn)
  have hgt : r ^ 2 < ‖z - ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - b‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hs]
    nlinarith [hnn, mul_pos ht ht]
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (z - ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - b)]

/-- **The perpendicular displacement has norm `t`.**

`‖(t/r)·(I·(z-a))‖ = |t/r| · ‖I‖ · ‖z-a‖ = (t/r) · 1 · r = t`.  The distance `dist z a = r` is
converted to `‖z - a‖ = r` *first* (a separate `have`), before the scalar rewrites, so the
`← dist_eq_norm` rewrite has the pattern it expects. -/
theorem norm_ofReal_div_mul_I_mul_sub (a z : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hz : dist z a = r) :
    ‖((t / r : ℝ) : ℂ) * (Complex.I * (z - a))‖ = t := by
  have htr : 0 < t / r := div_pos ht hr
  have hnorm : ‖z - a‖ = r := by rw [← dist_eq_norm, hz]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htr, norm_mul, Complex.norm_I,
    one_mul, hnorm]
  field_simp

/-- **The perpendicular step strictly increases the distance to `a`.**

From `dist_perp_step_sq` the squared distance is `(1 + (t/r)²)·r²`; restating it as `‖·‖²` first and
handing `nlinarith` the two positivity chains (`(t/r)² > 0` and `r² > 0`) together with
`norm_nonneg` gives `r < dist (z + (t/r)·(I·(z-a))) a`. -/
theorem dist_perp_step_gt (a z : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (hz : dist z a = r) :
    r < dist (z + ((t / r : ℝ) : ℂ) * (Complex.I * (z - a))) a := by
  have htr : 0 < t / r := div_pos ht hr
  have hs := dist_perp_step_sq (a := a) (z := z) (r := r) (t := t) hz
  rw [dist_eq_norm] at hs
  rw [dist_eq_norm]
  nlinarith [hs, mul_pos htr htr, mul_pos hr hr,
    norm_nonneg (z + ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - a)]

/-- **The reversed perpendicular step also strictly increases the distance to `a`.**

Same recipe as `dist_perp_step_gt`, but with the *negative* coefficient baked in from the start:
the heart lemma is instantiated with `c := -(t/r)`, so `(1 + (-(t/r))²)·r² = (1 + (t/r)²)·r²` is
normalised inside the lemma and no transport between sign spellings is ever needed. -/
theorem dist_perp_step_gt_neg (a z : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (hz : dist z a = r) :
    r < dist (z - ((t / r : ℝ) : ℂ) * (Complex.I * (z - a))) a := by
  have htr : 0 < t / r := div_pos ht hr
  have hna : Complex.normSq (z - a) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, ← dist_eq_norm, hz]
  have hsub : z - ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - a =
      (z - a) + ((-(t / r) : ℝ) : ℂ) * (Complex.I * (z - a)) := by
    push_cast
    ring
  have hs : Complex.normSq (z - ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - a) =
      (1 + (t / r) ^ 2) * r ^ 2 := by
    rw [hsub, normSq_add_ofReal_mul_I_mul, hna]
    ring
  have hsq : r ^ 2 < ‖z - ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - a‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hs]
    nlinarith [mul_pos htr htr, mul_pos hr hr]
  rw [dist_eq_norm]
  nlinarith [hsq, norm_nonneg (z - ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) - a)]

/-- **A point of `sphere a r` outside the open ball at `b` lies in the frontier of the union.**

`lt_or_eq_of_le hzb` dispatches; in the equality case step perpendicular to `z - a` in either
direction, the four distance facts being `dist_perp_step_gt`/`dist_perp_step_gt_neg` for the `a`-side
and `dist_perp_step_gt_of_im_nonneg`/`dist_perp_step_gt_of_im_nonpos` for the `b`-side, with
`norm_ofReal_div_mul_I_mul_sub` giving the step length `t`. -/
theorem frontier_of_sphere_point_of_dist_ge {a b : ℂ} {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : dist z a = r) (hzb : r ≤ dist z b) :
    z ∈ frontier (Metric.closedBall a r ∪ Metric.closedBall b r) := by
  rcases lt_or_eq_of_le hzb with hlt | heq
  · exact frontier_of_sphere_point_of_dist_gt hr hz hlt
  · refine ⟨subset_closure (Or.inl (Metric.mem_closedBall.mpr (le_of_eq hz))), ?_⟩
    intro hint
    have hnotmem : ¬ z ∈ closure ((Metric.closedBall a r ∪ Metric.closedBall b r)ᶜ) := by
      rw [closure_compl]
      simpa using hint
    refine hnotmem (Metric.mem_closure_iff.mpr ?_)
    intro ε hε
    set t : ℝ := ε / 2 with htdef
    have htpos : 0 < t := by rw [htdef]; linarith
    have htε : t < ε := by rw [htdef]; linarith
    set c : ℂ := ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) with hcdef
    have hct : dist z (z + c) = t := by
      have hneg : z - (z + c) = -c := by ring
      rw [dist_eq_norm, hneg, norm_neg, hcdef]
      exact norm_ofReal_div_mul_I_mul_sub a z hr htpos hz
    have hct' : dist z (z + -c) = t := by
      have hneg : z - (z + -c) = c := by ring
      rw [dist_eq_norm, hneg, hcdef]
      exact norm_ofReal_div_mul_I_mul_sub a z hr htpos hz
    have hAc : r < dist (z + c) a := by
      rw [hcdef]
      exact dist_perp_step_gt a z hr htpos hz
    have hAc' : r < dist (z + -c) a := by
      have hconv : z + -c = z - ((t / r : ℝ) : ℂ) * (Complex.I * (z - a)) := by
        rw [hcdef]
        ring
      rw [hconv]
      exact dist_perp_step_gt_neg a z hr htpos hz
    by_cases hsgn : 0 ≤ ((z - b) * star (z - a)).im
    · refine ⟨z + c, ?_, ?_⟩
      · rw [Set.mem_compl_iff, Set.mem_union, not_or]
        exact ⟨not_le.mpr hAc,
          not_le.mpr (dist_perp_step_gt_of_im_nonneg hr htpos hz heq.symm hsgn)⟩
      · rw [hct]
        exact htε
    · refine ⟨z + -c, ?_, ?_⟩
      · rw [Set.mem_compl_iff, Set.mem_union, not_or]
        exact ⟨not_le.mpr hAc',
          not_le.mpr (dist_perp_step_gt_of_im_nonpos hr htpos hz heq.symm (not_le.mp hsgn).le)⟩
      · rw [hct']
        exact htε

/-- **The two intersection points lie in the frontier of the union of the two closed balls.**

This is the endpoints of the outer arcs, and it is exactly the combination of
`dist_circleIntersection` (the point is at distance `r` from both centres) with
`frontier_of_sphere_point_of_dist_ge` (a point of `sphere a r` outside the open ball at `b` is on the
frontier). -/
theorem circleIntersection_mem_frontier {a b : ℂ} {r κ : ℝ} (hr : 0 < r) (hab : a ≠ b)
    (hκ : κ ^ 2 = r ^ 2 - (‖b - a‖ / 2) ^ 2) :
    circleIntersection a b κ ∈ frontier (Metric.closedBall a r ∪ Metric.closedBall b r) := by
  have h := dist_circleIntersection (a := a) (b := b) (r := r) (κ := κ) hr hab hκ
  exact frontier_of_sphere_point_of_dist_ge (a := a) (b := b) (r := r) hr h.1 (le_of_eq h.2.symm)

/-- **The part of `sphere a r` outside the open ball at `b` lies in the frontier.**

This is the pointwise engine of the arc body: any parametrisation of the outer arc only has to land
in `sphere a r` and outside `Metric.ball b r`, and this subset form applies
`frontier_of_sphere_point_of_dist_ge` along it. -/
theorem sphere_sdiff_ball_subset_frontier {a b : ℂ} {r : ℝ} (hr : 0 < r) :
    Metric.sphere a r \ Metric.ball b r ⊆
      frontier (Metric.closedBall a r ∪ Metric.closedBall b r) := by
  intro z hz
  exact frontier_of_sphere_point_of_dist_ge hr hz.1
    (not_lt.mp fun h => hz.2 (Metric.mem_ball.mpr h))

end

end Work.Smooth.SphereJordan
