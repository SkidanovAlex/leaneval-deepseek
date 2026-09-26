import ChallengeDeps
import Submission.Commons.Analysis.Normed.exists_not_mem_openSegment_of_isCompact

open LeanEval.KnotTheory.Quadrisecant

/-! Development notes for `smooth_knot_has_quadrisecant`
======================================================

Statement (Pannwitz 1933 / Kuperberg 1994): a smooth knot `r` that is not
unknotted has four collinear image points.

Roadmap (following Kuperberg, *Quadrisecants of knots and links*,
J. Knot Theory Ramif. 3 (1994); see also Denne's thesis arXiv:math/0510561):

  1. Secant space. For a knot, unordered pairs of distinct points form an
     open Möbius strip `M`. The subset `O ⊆ M` of pairs `(a,b)` for which a
     third point of the knot lies on the chord is the image of a smooth
     immersion of a 1-manifold; double points of that immersion are
     quadrisecants.
  2. Obstruction. A properly embedded *non-separating* arc of `M` avoiding
     `O` yields (by sweeping the chords along the arc) a spanning disk of the
     knot whose interior misses the knot; by the classical Dehn-lemma /
     Alexander-trick circle of ideas such a knot is isotopic through knots
     to the round circle, i.e. unknotted.
  3. If there is no quadrisecant then `O` is embedded and, because the knot
     is knotted (no disk as in (2)), `O` blocks every non-separating arc,
     forcing a circular component winding around the Möbius strip; that loop
     either forces a jump discontinuity in the middle point of the moving
     trisecant, or puts every point of the (compact) knot between two other
     points -- both impossible.
  Hence knotted ⇒ quadrisecant.

This file: elementary API only (unconditional facts about the trusted
definitions, the round circle, periodic calculus). -/

namespace LeanEval.KnotTheory.Quadrisecant

lemma period_pos : 0 < period := by
  unfold period
  positivity

lemma period_ne_zero : period ≠ 0 := ne_of_gt period_pos

lemma period_nonneg : 0 ≤ period := le_of_lt period_pos

/-- A `IsSmoothKnot` curve is continuous. -/
lemma IsSmoothKnot.continuous {r : ℝ → Space} (h : IsSmoothKnot r) : Continuous r :=
  h.smooth.continuous

/-- A `IsSmoothKnot` curve takes equal values at arguments separated by the period. -/
lemma IsSmoothKnot.periodic_eq {r : ℝ → Space} (h : IsSmoothKnot r) (t : ℝ) :
    r (t + period) = r t :=
  h.periodic t

/-- A `IsSmoothKnot` curve is injective on the defining half-open interval. -/
lemma IsSmoothKnot.injective_on_Ico {r : ℝ → Space} (h : IsSmoothKnot r) :
    Set.InjOn r (Set.Ico (0 : ℝ) period) :=
  h.injective_on_period

/-- Images of distinct parameters in one period are distinct points. -/
lemma IsSmoothKnot.image_ne {r : ℝ → Space} (h : IsSmoothKnot r) {t s : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) period) (hs : s ∈ Set.Ico (0 : ℝ) period)
    (hts : t ≠ s) : r t ≠ r s := by
  intro hts'
  exact hts (h.injective_on_period ht hs hts')

/-- The period of a differentiable periodic curve is also a period of its
velocity (tangent vector). -/
lemma periodic_velocity {r : ℝ → Space} (hr : Function.Periodic r period)
    (hdiff : Differentiable ℝ r) (t : ℝ) :
    velocity r (t + period) = velocity r t := by
  unfold velocity
  have hshift : deriv (fun x : ℝ => r (x + period)) t = deriv r (t + period) := by
    have htr : HasDerivAt (fun x : ℝ => x + period) 1 t := by
      simpa using (hasDerivAt_id t).add_const period
    have hmain : HasDerivAt r (deriv r (t + period)) (t + period) :=
      (hdiff (t + period)).hasDerivAt
    have hc : HasDerivAt (fun x : ℝ => r (x + period)) (1 • deriv r (t + period)) t := by
      simpa [Function.comp_def] using (hmain.scomp t htr)
    simpa using hc.deriv
  have heq : (fun x : ℝ => r (x + period)) = r := by
    funext x
    exact hr x
  rw [← hshift, heq]

/-- For a smooth knot the velocity is periodic. -/
lemma IsSmoothKnot.velocity_periodic {r : ℝ → Space} (h : IsSmoothKnot r) (t : ℝ) :
    velocity r (t + period) = velocity r t :=
  periodic_velocity h.periodic (ContDiff.differentiable h.smooth (by simp)) t

/-! ### The round circle ------------------------------------------------ -/

lemma standardCircle_contDiff : ContDiff ℝ ⊤ standardCircle := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp [standardCircle] <;> fun_prop

lemma standardCircle_periodic : Function.Periodic standardCircle period := by
  intro t
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [standardCircle, period, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The standard parametrization of the circle is injective on `[0, period)`. -/
lemma standardCircle_injective : Set.InjOn standardCircle (Set.Ico (0 : ℝ) period) := by
  intro t ht s hs hts
  -- the squared distance between the two image points vanishes
  have hn0 : ‖standardCircle t - standardCircle s‖ ^ 2 = 0 := by simp [hts]
  have hn2 : ‖standardCircle t - standardCircle s‖ ^ 2 =
      (Real.cos t - Real.cos s) ^ 2 + (Real.sin t - Real.sin s) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [standardCircle, PiLp.sub_apply, Fin.sum_univ_three]
  have htrig : (Real.cos t - Real.cos s) ^ 2 + (Real.sin t - Real.sin s) ^ 2 =
      2 - 2 * Real.cos (t - s) := by
    rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq s]
  have hcos1 : Real.cos (t - s) = 1 := by
    nlinarith [hn0, hn2, htrig]
  have ht2 : t < 2 * Real.pi := by simpa [period] using ht.2
  have hs2 : s < 2 * Real.pi := by simpa [period] using hs.2
  have hb1 : -(2 * Real.pi) < t - s := by
    nlinarith [ht.1, hs2]
  have hb2 : t - s < 2 * Real.pi := by
    nlinarith [ht2, hs.1]
  have hts0 : t - s = 0 := (Real.cos_eq_one_iff_of_lt_of_lt hb1 hb2).mp hcos1
  linarith


/-- Derivative in a coordinate of a differentiable curve into `Space`. -/
lemma deriv_ofLp {f : ℝ → Space} {t : ℝ} (hd : DifferentiableAt ℝ f t) (i : Fin 3) :
    (deriv f t).ofLp i = deriv (fun x : ℝ => (f x).ofLp i) t := by
  let P : Space →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
  have hP : ∀ z : Space, P z = z.ofLp i := by
    intro z
    change (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i) z = z.ofLp i
    rfl
  have hc : DifferentiableAt ℝ (fun _ : ℝ => P) t := by
    have hD : Differentiable ℝ (fun _ : ℝ => P) := by
      exact (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => P)).differentiable (by simp)
    exact hD.differentiableAt
  have hd' := deriv_clm_apply (c := (fun _ : ℝ => P)) (u := f) hc hd
  have hc0 : deriv (fun _ : ℝ => P) t = 0 := deriv_const t P
  rw [hc0, zero_apply, zero_add] at hd'
  rw [← hP (deriv f t)]
  rw [← hd']
  rfl

/-- The velocity of the standard circle is a unit tangent vector. -/
lemma standardCircle_velocity (t : ℝ) :
    velocity standardCircle t = !₂[-Real.sin t, Real.cos t, 0] := by
  unfold velocity
  have hd : DifferentiableAt ℝ standardCircle t :=
    (standardCircle_contDiff.differentiable (by simp)).differentiableAt
  apply PiLp.ext
  intro i
  rw [deriv_ofLp hd i]
  fin_cases i <;> simp [standardCircle]

/-- The standard circle is everywhere regular. -/
lemma standardCircle_regular : ∀ t : ℝ, velocity standardCircle t ≠ 0 := by
  intro t
  rw [standardCircle_velocity t]
  intro h
  have hnorm : ‖(!₂[-Real.sin t, Real.cos t, 0] : Space)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three, Real.sin_sq_add_cos_sq t]
  have hz : ‖(!₂[-Real.sin t, Real.cos t, 0] : Space)‖ ^ 2 = 0 := by simp [h]
  linarith

/-- The standard circle is a smooth knot. -/
lemma standardCircle_isSmoothKnot : IsSmoothKnot standardCircle :=
  { smooth := standardCircle_contDiff
    periodic := standardCircle_periodic
    injective_on_period := standardCircle_injective
    regular := standardCircle_regular }

/-- Joint smoothness of the constant isotopy `(t, s) ↦ standardCircle t`. -/
lemma standardCircle_constIsotopy_contDiff :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => standardCircle p.1) := by
  rw [show (fun p : ℝ × ℝ => standardCircle p.1) = standardCircle ∘ Prod.fst by rfl]
  exact standardCircle_contDiff.comp contDiff_fst

/-- The round circle is an unknot: the constant homotopy is an isotopy
through knots from `standardCircle` to itself. -/
lemma standardCircle_isUnknotted : IsUnknotted standardCircle := by
  refine ⟨fun t _ => standardCircle t, ?_, ?_, ?_, ?_⟩
  · exact standardCircle_constIsotopy_contDiff
  · intro t
    rfl
  · intro t
    rfl
  · intro s hs
    simpa using standardCircle_isSmoothKnot


/-- The image of the defining half-open period is nonempty. -/
lemma IsSmoothKnot.image_Ico_nonempty {r : ℝ → Space} (_h : IsSmoothKnot r) :
    (r '' Set.Ico (0 : ℝ) period).Nonempty := by
  refine ⟨r 0, 0, ⟨le_rfl, period_pos⟩, rfl⟩

lemma IsSmoothKnot.image_compact {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsCompact (r '' Set.Icc (0 : ℝ) period) := by
  exact IsCompact.image isCompact_Icc h.continuous

/-- The image of a knot over the closed period equals its image over the
half-open period (the endpoints are identified). -/
lemma IsSmoothKnot.image_Icc_eq_image_Ico {r : ℝ → Space} (h : IsSmoothKnot r) :
    r '' Set.Icc (0 : ℝ) period = r '' Set.Ico (0 : ℝ) period := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩
    by_cases htp : t < period
    · exact ⟨t, ⟨ht.1, htp⟩, rfl⟩
    · have hte : t = period := le_antisymm ht.2 (le_of_not_gt htp)
      subst t
      exact ⟨0, ⟨le_rfl, period_pos⟩, by simpa using (h.periodic_eq 0).symm⟩
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩
    exact ⟨t, ⟨ht.1, le_of_lt ht.2⟩, rfl⟩

/-- The image of a smooth knot is a bounded set. -/
lemma IsSmoothKnot.image_bounded {r : ℝ → Space} (h : IsSmoothKnot r) :
    Bornology.IsBounded (r '' Set.Icc (0 : ℝ) period) :=
  h.image_compact.isBounded


/-- Extremal-point lemma used in the Kuperberg argument (step 3): some point
`q` of the image of a smooth knot is not strictly between two other image
points.  (Take a point of the compact image farthest from the origin.) -/
lemma IsSmoothKnot.exists_point_not_strictly_between {r : ℝ → Space} (h : IsSmoothKnot r) :
    ∃ q : Space, q ∈ r '' Set.Ico (0 : ℝ) period ∧
      ∀ x y : Space, x ∈ r '' Set.Ico (0 : ℝ) period → y ∈ r '' Set.Ico (0 : ℝ) period →
        x ≠ y → q ∉ openSegment ℝ x y := by
  have hC : IsCompact (r '' Set.Ico (0 : ℝ) period) := by
    simpa [h.image_Icc_eq_image_Ico] using h.image_compact
  rcases Commons.Analysis.Normed.exists_not_mem_openSegment_of_isCompact
      (r '' Set.Ico (0 : ℝ) period) hC h.image_Ico_nonempty with ⟨q, hq, hqprop⟩
  exact ⟨q, hq, hqprop⟩


end LeanEval.KnotTheory.Quadrisecant

