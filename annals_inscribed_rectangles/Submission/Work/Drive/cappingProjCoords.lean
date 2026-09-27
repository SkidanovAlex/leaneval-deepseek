import Mathlib
import Submission.Work.Drive.LensSpaceGlue
import Submission.Work.Drive.ProjectiveChartDefs
import Submission.Work.Drive.exists_cappingModel_projectivization

/-!
# Sphere lifts of the two solid tori of the capping

`Work.Drive.lensToProj : LensSpace → ℝP³` (`Submission/Work/Drive/exists_cappingModel_projectivization`)
is defined *abstractly*, as the descent of `projOfUnitSphere` through the quotient map
`phi : S³ → LensSpace` (`Work.Drive.lensToProj_phi : lensToProj (phi v) = projOfUnitSphere v`), and its
definition goes through `Function.surjInv`, so nothing about it can be unfolded.  For the chain route
of the total-order chapter (`Submission/Work/Drive/CHAIN_ROUTE_REDUCTION.md`,
`Submission/Work/Drive/SMOOTHNESS_LANE_STATUS.md`) the *coordinate formula* of `lensToProj` on each of
the two solid tori `S¹ × D²` and `D² × S¹` whose boundary gluing is `LensSpace = L(2,1) = ℝP³` is
needed, and the formula necessarily involves a **square root** of the `S¹`-coordinate: the cap
coordinate of `LensSpace` is `(‖z₂‖/z₂)²`, the *square* of a unit complex number, so recovering the
sphere point from the torus coordinates requires choosing a square root.  (The two choices differ by
`z ↦ -z`, which is exactly the antipodal identification of the sphere, so the projective class is
independent of the choice — but no *continuous* choice exists, which is why the smoothness of the
concrete charts has to be proved with the square root taken from the curve data.)

This file supplies, for each torus coordinate and each chosen square root, the explicit **unit vector**
of `ℂ² ≅ ℝ⁴ = Eucl 3` whose projective class is the image point:

* a cap point `(θ, d) ∈ S¹ × D²` (`CapTorus`) with a square root `w` of `circleOf θ`
  (`w ^ 2 = circleOf θ`) has sphere point `(d · w / √2, w̄ · √(1 - ‖d‖²/2))`, i.e.
  `Work.Drive.capProjVecOf w d`;
* a configuration point `(d, η) ∈ D² × S¹` (`ConfTorus`) with a square root `u` of `circleOf η`
  (`u ^ 2 = circleOf η`) has sphere point `(u · √(1 - ‖d‖²/2), ū · d / √2)`, i.e.
  `Work.Drive.confProjVecOf u d`.

Both are unit vectors (the two squared norms sum to `1`, since `‖w‖ = ‖u‖ = 1`) and neither vanishes
(`Work.Drive.capProjVecOf_ne_zero`, `Work.Drive.confProjVecOf_ne_zero`), so each is the `√2`-multiple
of nothing but a genuine point of the unit sphere; the identifications
`Work.Drive.lensToProj_capTorus` and `Work.Drive.lensToProj_confTorus` are stated in the files that
accompany this one.  The dictionary with the usual coordinates of `ℂ² = ℝ⁴` is
`Work.Drive.c₁`/`Work.Drive.c₂` (`c₁ v = v 0 + v 1 · i`, `c₂ v = v 2 + v 3 · i`), and
`Work.Drive.ofComplex z z'` is the inverse dictionary.
-/

namespace Work.Drive

noncomputable section

/-- The vector of `ℂ² ≅ ℝ⁴ = Eucl 3` with complex coordinates `z₁ = z`, `z₂ = z'`. -/
def ofComplex (z z' : ℂ) : Eucl 3 :=
  WithLp.toLp 2 (![z.re, z.im, z'.re, z'.im] : Fin 4 → ℝ)

@[simp] lemma c₁_ofComplex (z z' : ℂ) : c₁ (ofComplex z z') = z := by
  unfold c₁ ofComplex
  rw [WithLp.ofLp_toLp]
  simp

@[simp] lemma c₂_ofComplex (z z' : ℂ) : c₂ (ofComplex z z') = z' := by
  unfold c₂ ofComplex
  rw [WithLp.ofLp_toLp]
  simp

/-- The dictionary `ofComplex` is inverse to the complex coordinates `c₁`, `c₂`. -/
lemma ofComplex_c₁_c₂ (v : Eucl 3) : ofComplex (c₁ v) (c₂ v) = v := by
  have h₁ : (ofComplex (c₁ v) (c₂ v)).ofLp 0 = v.ofLp 0 := by
    have := congrArg Complex.re (c₁_ofComplex (c₁ v) (c₂ v))
    simpa [c₁, ofComplex, WithLp.ofLp_toLp] using this
  have h₂ : (ofComplex (c₁ v) (c₂ v)).ofLp 1 = v.ofLp 1 := by
    have := congrArg Complex.im (c₁_ofComplex (c₁ v) (c₂ v))
    simpa [c₁, ofComplex, WithLp.ofLp_toLp] using this
  have h₃ : (ofComplex (c₁ v) (c₂ v)).ofLp 2 = v.ofLp 2 := by
    have := congrArg Complex.re (c₂_ofComplex (c₁ v) (c₂ v))
    simpa [c₂, ofComplex, WithLp.ofLp_toLp] using this
  have h₄ : (ofComplex (c₁ v) (c₂ v)).ofLp 3 = v.ofLp 3 := by
    have := congrArg Complex.im (c₂_ofComplex (c₁ v) (c₂ v))
    simpa [c₂, ofComplex, WithLp.ofLp_toLp] using this
  refine WithLp.ofLp_injective _ ?_
  ext i
  fin_cases i
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

/-- An element of the closed unit disk of `ℂ` has norm at most `1`. -/
lemma norm_coe_closedBall_le_one (d : Metric.closedBall (0 : ℂ) 1) : ‖(d : ℂ)‖ ≤ 1 := by
  have h := d.2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  exact h

/-- A square root of a point of the unit circle is a unit complex number. -/
lemma norm_eq_one_of_sq_eq_circleOf {w : ℂ} {θ : UnitAddCircle} (hw : w ^ 2 = circleOf θ) :
    ‖w‖ = 1 := by
  have h : ‖w‖ ^ 2 = 1 := by rw [← norm_pow, hw, norm_circleOf]
  nlinarith [norm_nonneg w]

/-- The vector `√(1 - ‖d‖²/2)` is positive for `d` in the closed unit disk. -/
lemma sqrt_one_sub_pos {d : ℂ} (hd : ‖d‖ ≤ 1) : 0 < Real.sqrt (1 - ‖d‖ ^ 2 / 2) :=
  Real.sqrt_pos.mpr (by nlinarith [norm_nonneg d, sq_nonneg ‖d‖, hd])

/-- **The sphere point of a cap point** `(θ, d) ∈ S¹ × D²` with a chosen square root
`w` of `circleOf θ`: the pair `(d · w / √2, w̄ · √(1 - ‖d‖²/2))`. -/
def capProjVecOf (w : ℂ) (d : ℂ) : Eucl 3 :=
  ofComplex (d * w / ((Real.sqrt 2 : ℝ) : ℂ))
    (star w * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ))

/-- **The sphere point of a configuration point** `(d, η) ∈ D² × S¹` with a chosen square root
`u` of `circleOf η`: the pair `(u · √(1 - ‖d‖²/2), ū · d / √2)`. -/
def confProjVecOf (u : ℂ) (d : ℂ) : Eucl 3 :=
  ofComplex (u * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ))
    (star u * d / ((Real.sqrt 2 : ℝ) : ℂ))

@[simp] lemma c₁_capProjVecOf (w : ℂ) (d : ℂ) :
    c₁ (capProjVecOf w d) = d * w / ((Real.sqrt 2 : ℝ) : ℂ) := by simp [capProjVecOf]

@[simp] lemma c₂_capProjVecOf (w : ℂ) (d : ℂ) :
    c₂ (capProjVecOf w d) = star w * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ) := by
  simp [capProjVecOf]

@[simp] lemma c₁_confProjVecOf (u : ℂ) (d : ℂ) :
    c₁ (confProjVecOf u d) = u * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ) := by
  simp [confProjVecOf]

@[simp] lemma c₂_confProjVecOf (u : ℂ) (d : ℂ) :
    c₂ (confProjVecOf u d) = star u * d / ((Real.sqrt 2 : ℝ) : ℂ) := by
  simp [confProjVecOf]

/-- The cap sphere point never vanishes. -/
lemma capProjVecOf_ne_zero {w : ℂ} (hw : ‖w‖ = 1) {d : ℂ} (hd : ‖d‖ ≤ 1) :
    capProjVecOf w d ≠ 0 := by
  intro h
  have h2 : c₂ (capProjVecOf w d) = 0 := by rw [h]; simp [c₂]
  rw [c₂_capProjVecOf] at h2
  have hw0 : star w ≠ 0 := by
    intro hw'
    have : ‖w‖ = 0 := by rw [← norm_star, hw', norm_zero]
    rw [hw] at this; norm_num at this
  have hpos : ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (sqrt_one_sub_pos hd))
  exact (mul_ne_zero hw0 hpos) h2

/-- The configuration sphere point never vanishes. -/
lemma confProjVecOf_ne_zero {u : ℂ} (hu : ‖u‖ = 1) {d : ℂ} (hd : ‖d‖ ≤ 1) :
    confProjVecOf u d ≠ 0 := by
  intro h
  have h2 : c₁ (confProjVecOf u d) = 0 := by rw [h]; simp [c₁]
  rw [c₁_confProjVecOf] at h2
  have hu0 : u ≠ 0 := by
    intro hu'
    have : ‖u‖ = 0 := by rw [hu', norm_zero]
    rw [hu] at this; norm_num at this
  have hpos : ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (sqrt_one_sub_pos hd))
  exact (mul_ne_zero hu0 hpos) h2

/-- The cap sphere point is a unit vector. -/
lemma norm_capProjVecOf {w : ℂ} (hw : ‖w‖ = 1) {d : ℂ} (hd : ‖d‖ ≤ 1) :
    ‖capProjVecOf w d‖ = 1 := by
  have h := norm_sq_c₁_c₂ (capProjVecOf w d)
  rw [c₁_capProjVecOf, c₂_capProjVecOf] at h
  have h1 : ‖d * w / ((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = ‖d‖ ^ 2 / 2 := by
    rw [norm_div, norm_mul, hw, mul_one, div_pow]
    have h2 : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 2 := by
      rw [Complex.norm_of_nonneg (Real.sqrt_nonneg 2), Real.sq_sqrt (by norm_num)]
    rw [h2]
  have h3 : ‖star w * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ)‖ ^ 2
      = 1 - ‖d‖ ^ 2 / 2 := by
    rw [norm_mul, norm_star, hw, one_mul, Complex.norm_of_nonneg (le_of_lt (sqrt_one_sub_pos hd)),
      Real.sq_sqrt (by nlinarith [norm_nonneg d, sq_nonneg ‖d‖, hd])]
  rw [h1, h3] at h
  have h4 : ‖capProjVecOf w d‖ ^ 2 = 1 := by rw [h]; ring
  rw [← Real.sqrt_sq (norm_nonneg _), h4, Real.sqrt_one]

/-- The configuration sphere point is a unit vector. -/
lemma norm_confProjVecOf {u : ℂ} (hu : ‖u‖ = 1) {d : ℂ} (hd : ‖d‖ ≤ 1) :
    ‖confProjVecOf u d‖ = 1 := by
  have h := norm_sq_c₁_c₂ (confProjVecOf u d)
  rw [c₁_confProjVecOf, c₂_confProjVecOf] at h
  have h1 : ‖u * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ)‖ ^ 2 = 1 - ‖d‖ ^ 2 / 2 := by
    rw [norm_mul, hu, one_mul, Complex.norm_of_nonneg (le_of_lt (sqrt_one_sub_pos hd)),
      Real.sq_sqrt (by nlinarith [norm_nonneg d, sq_nonneg ‖d‖, hd])]
  have h3 : ‖star u * d / ((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = ‖d‖ ^ 2 / 2 := by
    rw [norm_div, norm_mul, norm_star, hu, one_mul, div_pow]
    have h2 : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 2 := by
      rw [Complex.norm_of_nonneg (Real.sqrt_nonneg 2), Real.sq_sqrt (by norm_num)]
    rw [h2]
  rw [h1, h3] at h
  have h4 : ‖confProjVecOf u d‖ ^ 2 = 1 := by rw [h]; ring
  rw [← Real.sqrt_sq (norm_nonneg _), h4, Real.sqrt_one]

end

end Work.Drive
