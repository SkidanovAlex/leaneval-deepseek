import Mathlib
import Submission.Work.Drive.cappingProjCoords

/-!
# The cap side of a sphere lift, and why a *pointwise* patching of the lift cannot work

This file settles the vocabulary used by every attempt to build the capped-plane chart
`∃ Q, Work.Drive.IsPlaneChart γ hγne Q` (`Submission/Work/Drive/planeChartDefs.lean`).

The capping space is `(0,∞) × ℝP³` transported along `Work.Drive.cappingSpaceHomeoProj`, and the two
solid tori of `ℝP³` are

* the **configuration side** `{|c₁| ≥ |c₂|}`, image of `ConfigPiece`
  (`confProjVecOf u d = (u√(1-‖d‖²/2), ūd/√2)` has `|c₁| = √(1-‖d‖²/2)`, `|c₂| = ‖d‖/√2`, so
  `|c₁| ≥ |c₂| ⟺ ‖d‖ ≤ 1`);
* the **cap side** `{|c₁| ≤ |c₂|}`, image of `CapPiece`
  (`capProjVecOf w d = (d·w/√2, w̄√(1-‖d‖²/2))` has `|c₁| = ‖d‖/√2`, `|c₂| = √(1-‖d‖²/2)`).

`Work.Drive.IsCapVec v := ‖c₁ v‖ < ‖c₂ v‖` is the *cap side*, and the lemmas below record

* its invariance under positive scalings (`IsCapVec` is a conical condition — but **not** convex: see
  `Work.Drive.not_forall_convex_isCapVec`, which exhibits two cap-side lifts whose midpoint is not
  cap-side; this is why the `muX`-blend of `Submission/Work/Drive/Neutral/StripDiskAux.lean` cannot be
  used to force the cap side, and why the correct blend has to be done in the *cap coordinates*
  `(θ, d)` of `CapPiece`, whose disk coordinate `d` is genuinely convex);
* its preservation when the second coordinate is scaled by `1 + λ`, `λ ≥ 0`
  (`isCapVec_ofComplex_snd_mul`), and the "large anchor" criterion
  (`isCapVec_of_large`): adding a vector of norm `> 2` to `c₂` always lands on the cap side.  Both are
  the local ingredients any construction has to use.
* the two chart criteria `isCapVec_capProjVecOf` / `isCapVec_confProjVecOf`, which identify the sides
  with the ranges of the two piece presentations — the form in which the piece of a capping point is
  decided.

**The obstruction (for the next session).**  A chart `Q` satisfies the cap clause iff its lift `V` is
cap-side (or on the torus) on the inner disk.  The cap coordinate of the corresponding capping point is
`(conj (c₂ V) / ‖c₂ V‖)²`, so the *mark* `z ↦ conj (c₂ (V z))² / max(‖c₁ (V z)‖², ‖c₂ (V z)‖²)` of
`Submission/Work/Drive/wrapData_of_planeChart.lean` is a *nowhere-zero* continuous function on the
closed inner disk; a nowhere-zero continuous function on a disk has boundary winding `0`
(`Work.Drive.degree_circle_boundary_eq_zero`), while the boundary values of the mark are forced by the
strip clause to be `circleOf (tanLoop - posLoop)`, of winding `2ε - 2m`.  Hence `2ε = 2m`
(`Work.Drive.wrapData_of_planeChart`, proved) — and, sharply, the *only* way a pointwise patching of
the lift can fail is that the class `[c₁ : 0]` of the **configuration pole** (a chord whose midpoint is
the origin, i.e. `d = 0`) is attained on the inner disk: there the mark vanishes
(`Work.Drive.isCapVec_of_c₂_eq_zero`).  A construction may therefore only use perturbations that
provably keep `c₂ ≠ 0`; any additive anchor whose cancellation is not excluded will, in general, be hit
— the winding computation shows that it *must* be hit whenever `m ≠ ε`.
-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

/-! ## 1. The predicate and its elementary algebra -/

/-- **The cap side of a lift** `v : ℂ² ≅ ℝ⁴`: its second complex coordinate dominates the first.  The
class `[v] ∈ ℝP³` is then in the cap solid torus (with equality on the gluing torus). -/
def IsCapVec (v : Eucl 3) : Prop := ‖c₁ v‖ < ‖c₂ v‖

lemma isCapVec_iff {v : Eucl 3} : IsCapVec v ↔ ‖c₁ v‖ < ‖c₂ v‖ := Iff.rfl

lemma complex_norm_eq_sqrt_normSq (z : ℂ) : ‖z‖ = Real.sqrt (Complex.normSq z) := by
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]

/-- The norm of a non-negative real, as a complex number. -/
lemma complex_norm_ofReal_nonneg {t : ℝ} (ht : 0 ≤ t) : ‖(t : ℂ)‖ = t := by
  have h : ‖(t : ℂ)‖ = |t| := by simp
  rw [h, abs_of_nonneg ht]

lemma isCapVec_iff_normSq {v : Eucl 3} :
    IsCapVec v ↔ Complex.normSq (c₁ v) < Complex.normSq (c₂ v) := by
  rw [isCapVec_iff, complex_norm_eq_sqrt_normSq, complex_norm_eq_sqrt_normSq]
  exact Real.sqrt_lt_sqrt_iff (Complex.normSq_nonneg _)

lemma isCapVec.ne {v : Eucl 3} (h : IsCapVec v) : v ≠ 0 := by
  intro h0
  rw [h0, isCapVec_iff] at h
  simp [c₁, c₂] at h

/-- The configuration pole `[c₁ : 0]` (a chord with midpoint at the origin) is never cap side. -/
lemma isCapVec_of_c₂_eq_zero {v : Eucl 3} (h : c₂ v = 0) : ¬ IsCapVec v := by
  rw [isCapVec_iff, h, norm_zero]
  exact not_lt.mpr (norm_nonneg (c₁ v))

@[simp] lemma c₁_add (v w : Eucl 3) : c₁ (v + w) = c₁ v + c₁ w := by
  simp only [c₁, PiLp.add_apply]
  rw [Complex.ofReal_add, Complex.ofReal_add]
  ring

@[simp] lemma c₂_add (v w : Eucl 3) : c₂ (v + w) = c₂ v + c₂ w := by
  simp only [c₂, PiLp.add_apply]
  rw [Complex.ofReal_add, Complex.ofReal_add]
  ring

@[simp] lemma c₁_real_smul (t : ℝ) (v : Eucl 3) : c₁ (t • v) = (t : ℂ) * c₁ v := by
  simp only [c₁, PiLp.smul_apply]
  rw [smul_eq_mul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_mul]
  ring

@[simp] lemma c₂_real_smul (t : ℝ) (v : Eucl 3) : c₂ (t • v) = (t : ℂ) * c₂ v := by
  simp only [c₂, PiLp.smul_apply]
  rw [smul_eq_mul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_mul]
  ring

/-- The cap side is invariant under positive scalings (it is a conical condition). -/
lemma isCapVec_smul {v : Eucl 3} {t : ℝ} (ht : 0 < t) : IsCapVec (t • v) ↔ IsCapVec v := by
  have ht' : (0:ℝ) < ‖(t : ℂ)‖ := by
    rw [complex_norm_ofReal_nonneg ht.le]; exact ht
  rw [isCapVec_iff, isCapVec_iff, c₁_real_smul, c₂_real_smul, norm_mul, norm_mul]
  constructor
  · intro h; exact lt_of_mul_lt_mul_left h (norm_nonneg _)
  · intro h; exact mul_lt_mul_of_pos_left h ht' 

/-- Scaling the second coordinate by `1 + l`, `l ≥ 0`, preserves the cap side (and turns a lifting
failure into a lifting success once `l` is large enough). -/
lemma isCapVec_ofComplex_snd_mul {v : Eucl 3} {l : ℝ} (hl : 0 ≤ l) (h : IsCapVec v) :
    IsCapVec (ofComplex (c₁ v) ((1 + l) * c₂ v)) := by
  have hl1 : (0:ℝ) < 1 + l := by linarith
  have hcast : (1 : ℂ) + (l : ℂ) = (((1 + l : ℝ)) : ℂ) := by push_cast; ring
  have hnorm : ‖(((1 + l : ℝ)) : ℂ)‖ = 1 + l := complex_norm_ofReal_nonneg hl1.le
  rw [isCapVec_iff, c₁_ofComplex, c₂_ofComplex, hcast, norm_mul, hnorm]
  have h2 : (1 : ℝ) * ‖c₂ v‖ ≤ (1 + l) * ‖c₂ v‖ := by
    nlinarith [norm_nonneg (c₂ v)]
  calc ‖c₁ v‖ < ‖c₂ v‖ := h
    _ = 1 * ‖c₂ v‖ := (one_mul _).symm
    _ ≤ (1 + l) * ‖c₂ v‖ := h2

/-- **The large-anchor criterion**: adding a vector of norm `> 2` to the second coordinate always lands
strictly on the cap side.  (`|c₂ + w| ≥ ‖w‖ - ‖c₂‖ > 2 - 1 ≥ ‖c₁‖`.) -/
lemma isCapVec_of_large {v : Eucl 3} (h₁ : ‖c₁ v‖ ≤ 1) (h₂ : ‖c₂ v‖ ≤ 1)
    {w : ℂ} (hw : 2 < ‖w‖) : IsCapVec (ofComplex (c₁ v) (c₂ v + w)) := by
  rw [isCapVec_iff, c₁_ofComplex, c₂_ofComplex]
  have h : ‖w‖ - ‖c₂ v‖ ≤ ‖c₂ v + w‖ := by
    have h1 := norm_sub_le (w + c₂ v) (c₂ v)
    have h2 : w + c₂ v - c₂ v = w := by abel
    have h3 : w + c₂ v = c₂ v + w := add_comm _ _
    rw [h2, h3] at h1
    linarith
  linarith

/-! ## 2. The cap side is not convex -/

/-- The cap-side condition is conical but **not convex**: the lifts `(1, 1001/1000)` and
`(9/10, -1)` are both cap side, while their midpoint `(19/20, 1/2000)` is not.  Consequently a
*linear* blend of the honest chord data with a fixed anchor (the `muX`-blend of the strip lane) cannot
be used to force the cap side; the blending has to be done in the cap coordinates, whose disk
coordinate is convex. -/
theorem not_forall_convex_isCapVec :
    ∃ v w : Eucl 3, IsCapVec v ∧ IsCapVec w ∧ ¬ IsCapVec ((1 / 2 : ℝ) • (v + w)) := by
  refine ⟨ofComplex 1 (3 / 2), ofComplex (9 / 10) (-1), ?_, ?_, ?_⟩
  · rw [isCapVec_iff_normSq, c₁_ofComplex, c₂_ofComplex]
    norm_num [Complex.normSq_apply]
  · rw [isCapVec_iff_normSq, c₁_ofComplex, c₂_ofComplex]
    norm_num [Complex.normSq_apply]
  · rw [isCapVec_iff_normSq, c₁_real_smul, c₂_real_smul, c₁_add, c₂_add, c₁_ofComplex,
      c₂_ofComplex, c₁_ofComplex, c₂_ofComplex]
    norm_num [Complex.normSq_apply]

/-! ## 3. The two chart criteria -/

/-- The cap chart `(w, d) ↦ [capProjVecOf w d]` (`‖w‖ = 1`, `‖d‖ ≤ 1`) is cap side exactly in the
*interior* `‖d‖ < 1` of the cap disk. -/
lemma isCapVec_capProjVecOf {w d : ℂ} (hw : ‖w‖ = 1) (hd : ‖d‖ ≤ 1) :
    IsCapVec (capProjVecOf w d) ↔ ‖d‖ < 1 := by
  have hd2 : ‖d‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg d]
  have hX : 0 ≤ 1 - ‖d‖ ^ 2 / 2 := by linarith
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsX : (Real.sqrt (1 - ‖d‖ ^ 2 / 2)) ^ 2 = 1 - ‖d‖ ^ 2 / 2 := Real.sq_sqrt hX
  have hdiv : (‖d‖ / Real.sqrt 2) ^ 2 = ‖d‖ ^ 2 / 2 := by rw [div_pow, hs2]
  have ha : 0 ≤ Real.sqrt (1 - ‖d‖ ^ 2 / 2) := Real.sqrt_nonneg _
  have hb : 0 ≤ ‖d‖ / Real.sqrt 2 := by positivity
  have hc1 : ‖c₁ (capProjVecOf w d)‖ = ‖d‖ / Real.sqrt 2 := by
    simp only [c₁_capProjVecOf, norm_div, norm_mul, hw, mul_one,
      complex_norm_ofReal_nonneg (Real.sqrt_nonneg 2)]
  have hc2 : ‖c₂ (capProjVecOf w d)‖ = Real.sqrt (1 - ‖d‖ ^ 2 / 2) := by
    simp only [c₂_capProjVecOf, norm_mul, norm_star, hw, one_mul,
      complex_norm_ofReal_nonneg (Real.sqrt_nonneg _)]
  rw [isCapVec_iff, hc1, hc2]
  constructor
  · intro h
    have h3 : (‖d‖ / Real.sqrt 2) ^ 2 < (Real.sqrt (1 - ‖d‖ ^ 2 / 2)) ^ 2 := by
      rw [sq_lt_sq, abs_of_nonneg hb, abs_of_nonneg ha]
      exact h
    rw [hdiv, hsX] at h3
    nlinarith [norm_nonneg d]
  · intro h
    have h3 : (‖d‖ / Real.sqrt 2) ^ 2 < (Real.sqrt (1 - ‖d‖ ^ 2 / 2)) ^ 2 := by
      rw [hdiv, hsX]; nlinarith [norm_nonneg d]
    rw [sq_lt_sq, abs_of_nonneg hb, abs_of_nonneg ha] at h3
    exact h3

/-- The configuration chart `(u, d) ↦ [confProjVecOf u d]` (`‖u‖ = 1`, `‖d‖ ≤ √2`) is cap side exactly
when `‖d‖ > 1`: this is the reflection identity `Work.Drive.capLift_reflect` seen from the side, and it
is why `Work.Drive.planePt u r d` with `1 < ‖d‖ ≤ √2` presents a *cap* point. -/
lemma isCapVec_confProjVecOf {u d : ℂ} (hu : ‖u‖ = 1) (hd : ‖d‖ ≤ Real.sqrt 2) :
    IsCapVec (confProjVecOf u d) ↔ 1 < ‖d‖ := by
  have hd2 : ‖d‖ ^ 2 ≤ 2 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith [norm_nonneg d, hd]
  have hX : 0 ≤ 1 - ‖d‖ ^ 2 / 2 := by linarith
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsX : (Real.sqrt (1 - ‖d‖ ^ 2 / 2)) ^ 2 = 1 - ‖d‖ ^ 2 / 2 := Real.sq_sqrt hX
  have hdiv : (‖d‖ / Real.sqrt 2) ^ 2 = ‖d‖ ^ 2 / 2 := by rw [div_pow, hs2]
  have ha : 0 ≤ Real.sqrt (1 - ‖d‖ ^ 2 / 2) := Real.sqrt_nonneg _
  have hb : 0 ≤ ‖d‖ / Real.sqrt 2 := by positivity
  have hc1 : ‖c₁ (confProjVecOf u d)‖ = Real.sqrt (1 - ‖d‖ ^ 2 / 2) := by
    simp only [c₁_confProjVecOf, norm_mul, hu, one_mul,
      complex_norm_ofReal_nonneg (Real.sqrt_nonneg _)]
  have hc2 : ‖c₂ (confProjVecOf u d)‖ = ‖d‖ / Real.sqrt 2 := by
    simp only [c₂_confProjVecOf, norm_div, norm_mul, norm_star, hu, one_mul,
      complex_norm_ofReal_nonneg (Real.sqrt_nonneg 2)]
  rw [isCapVec_iff, hc1, hc2]
  constructor
  · intro h
    have h3 : (Real.sqrt (1 - ‖d‖ ^ 2 / 2)) ^ 2 < (‖d‖ / Real.sqrt 2) ^ 2 := by
      rw [sq_lt_sq, abs_of_nonneg ha, abs_of_nonneg hb]
      exact h
    rw [hdiv, hsX] at h3
    nlinarith [norm_nonneg d]
  · intro h
    have h3 : (Real.sqrt (1 - ‖d‖ ^ 2 / 2)) ^ 2 < (‖d‖ / Real.sqrt 2) ^ 2 := by
      rw [hdiv, hsX]; nlinarith [norm_nonneg d]
    rw [sq_lt_sq, abs_of_nonneg ha, abs_of_nonneg hb] at h3
    exact h3

/-- The configuration pole `d = 0` is the point at which the mark of
`Submission/Work/Drive/wrapData_of_planeChart.lean` vanishes (`[c₁ : 0]` is the only class of `ℝP³`
whose mark is zero), and it is never cap side: this is the sharp form of the obstruction that forces
`Work.Drive.WrapData`. -/
lemma confProjVecOf_zero_not_isCapVec {u : ℂ} (hu : ‖u‖ = 1) :
    ¬ IsCapVec (confProjVecOf u 0) := by
  rw [isCapVec_confProjVecOf hu (by simp)]
  simp

end

end Work.Drive
