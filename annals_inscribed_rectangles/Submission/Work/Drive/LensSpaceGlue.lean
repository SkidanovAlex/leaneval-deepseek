import Mathlib
import Submission.Work.Drive.CappingSpace
import Submission.Work.Drive.ProjectiveTopology
import Submission.Work.Drive.sphere_quotient_projective

/-!
# The glueing map `S³ → LensSpace` realizing `L(2,1) ≅ ℝP³`

This file fixes the *formulas* that identify the Heegaard presentation `Work.Drive.LensSpace` of the
capping (two solid tori glued along their boundary tori by the `(2,1)` identification `lensRel`,
`Submission/Work/Drive/CappingSpace`) with the unit sphere modulo antipodes, i.e. with `ℝP³`.

Write a point of the sphere `S³ ⊆ ℂ² = ℝ⁴` as `(z₁, z₂)` and split it along the Clifford torus
`|z₁| = |z₂| = 1/√2` into the two solid tori `capHemi = {|z₁| ≤ |z₂|}` and
`confHemi = {|z₂| ≤ |z₁|}`.  The antipodal map `v ↦ -v` preserves each of them, so
`ℝP³ = S³/{±1}` is the glueing of the quotients `capHemi/{±1} ≅ S¹ × D²` and
`confHemi/{±1} ≅ D² × S¹` along their common boundary torus.

Concretely, for `(z₁, z₂)` with `|z₁| ≤ |z₂|` (so `z₂ ≠ 0`),

`capPt (z₁,z₂) = ( (‖z₂‖/z₂)² , √2 z₁z₂/‖z₂‖ )  ∈  S¹ × D² = CapTorus`,

and for `(z₁,z₂)` with `|z₂| ≤ |z₁|` (so `z₁ ≠ 0`),

`confPt (z₁,z₂) = ( √2 z₂z₁/‖z₁‖ , (z₁/‖z₁‖)² )  ∈  D² × S¹ = ConfTorus`.

Both branches are `{±1}`-invariant and injective on the quotient by `{±1}`; on the common boundary
`|z₁| = |z₂| = 1/√2`, writing `z₁ = e^{iα}/√2`, `z₂ = e^{iβ}/√2`, they give
`capPt = (e^{-2iβ}, e^{i(α+β)})` and `confPt = (e^{i(α+β)}, e^{2iα})`, and the cap boundary point
`(θ, w) = (e^{-2iβ}, e^{i(α+β)})` is identified by `lensRel` with the configuration boundary point
`(w, θ w²) = (e^{i(α+β)}, e^{2iα})`.  This *is* the `(2,1)`-glueing: the meridian of the cap torus
becomes the `(2,1)`-curve of the configuration torus.
-/

namespace Work.Drive

noncomputable section

open scoped Topology

/-- The first complex coordinate `z₁` of a point of `ℝ⁴ ≅ ℂ²`. -/
def c₁ (v : Eucl 3) : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I

/-- The second complex coordinate `z₂` of a point of `ℝ⁴ ≅ ℂ²`. -/
def c₂ (v : Eucl 3) : ℂ := (v 2 : ℂ) + (v 3 : ℂ) * Complex.I

lemma continuous_c₁ : Continuous c₁ := by unfold c₁; fun_prop

lemma continuous_c₂ : Continuous c₂ := by unfold c₂; fun_prop

lemma norm_sq_c₁_c₂ (v : Eucl 3) : ‖v‖ ^ 2 = ‖c₁ v‖ ^ 2 + ‖c₂ v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp [c₁, c₂, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

/-- On the unit sphere the two complex coordinates satisfy `‖z₁‖² + ‖z₂‖² = 1`. -/
lemma sq_norm_eq_one (v : unitSphere 3) : ‖c₁ v.1‖ ^ 2 + ‖c₂ v.1‖ ^ 2 = 1 := by
  rw [← norm_sq_c₁_c₂, norm_coe_unitSphere]
  norm_num

/-- Variant of `sq_norm_eq_one` with the summands exchanged. -/
lemma sq_norm_eq_one_comm (v : unitSphere 3) : ‖c₂ v.1‖ ^ 2 + ‖c₁ v.1‖ ^ 2 = 1 := by
  rw [add_comm]; exact sq_norm_eq_one v

/-- Arithmetic: if `‖a‖ ≤ ‖b‖` and `‖a‖² + ‖b‖² = 1` then `‖a‖ ≤ 1/√2`. -/
lemma norm_le_inv_sqrt_two {a b : ℂ} (h1 : ‖a‖ ≤ ‖b‖) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ‖a‖ ≤ 1 / Real.sqrt 2 := by
  have hsq : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [sq_le_sq]
    rwa [abs_of_nonneg (norm_nonneg a), abs_of_nonneg (le_trans (norm_nonneg a) h1)]
  have h2 : 2 * ‖a‖ ^ 2 ≤ 1 := by nlinarith [h, hsq]
  have h4 : ‖a‖ ^ 2 ≤ (1 / Real.sqrt 2) ^ 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [h2]
  rw [sq_le_sq] at h4
  rwa [abs_of_nonneg (norm_nonneg a), abs_of_nonneg (by positivity)] at h4

/-- Arithmetic: if `‖a‖ ≤ ‖b‖` and `‖a‖² + ‖b‖² = 1` then `b ≠ 0`. -/
lemma ne_zero_of_norm_le {a b : ℂ} (h1 : ‖a‖ ≤ ‖b‖) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : b ≠ 0 := by
  have hsq : (1 : ℝ) / 2 ≤ ‖b‖ ^ 2 := by
    nlinarith [h, h1, sq_nonneg (‖a‖), sq_nonneg (‖b‖), norm_nonneg a]
  intro hb
  rw [hb, norm_zero] at hsq
  norm_num at hsq

/-- Arithmetic: `(‖z‖/z)²` has norm `1` for `z ≠ 0`. -/
lemma norm_sq_self_div (z : ℂ) (hz : z ≠ 0) : ‖(((‖z‖ : ℝ) : ℂ) / z) ^ 2‖ = 1 := by
  rw [norm_pow, norm_div]
  have h : ‖(((‖z‖ : ℝ) : ℂ))‖ = ‖z‖ := by simp
  rw [h, div_self (norm_ne_zero_iff.mpr hz)]
  norm_num

/-- Arithmetic: `(z/‖z‖)²` has norm `1` for `z ≠ 0`. -/
lemma norm_sq_div_self (z : ℂ) (hz : z ≠ 0) : ‖(z / ((‖z‖ : ℝ) : ℂ)) ^ 2‖ = 1 := by
  rw [norm_pow, norm_div]
  have h : ‖(((‖z‖ : ℝ) : ℂ))‖ = ‖z‖ := by simp
  rw [h, div_self (norm_ne_zero_iff.mpr hz)]
  norm_num

/-- Arithmetic: `√2 · a · b/‖b‖` lies in the unit disk when `‖a‖ ≤ 1/√2` and `b ≠ 0`. -/
lemma norm_sqrt_two_mul_div_le (a b : ℂ) (hb : b ≠ 0) (ha : ‖a‖ ≤ 1 / Real.sqrt 2) :
    ‖(Real.sqrt 2 : ℂ) * a * b / ((‖b‖ : ℝ) : ℂ)‖ ≤ 1 := by
  have hb' : ‖(((‖b‖ : ℝ) : ℂ))‖ = ‖b‖ := by simp
  have h2 : ‖(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 := by simp
  rw [norm_div, norm_mul, norm_mul, hb', h2]
  rw [mul_div_assoc, div_self (norm_ne_zero_iff.mpr hb), mul_one]
  calc Real.sqrt 2 * ‖a‖ ≤ Real.sqrt 2 * (1 / Real.sqrt 2) :=
        mul_le_mul_of_nonneg_left ha (Real.sqrt_nonneg 2)
    _ = 1 := by
        rw [mul_one_div]
        exact div_self (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-- Membership of a complex number of norm `1` in the unit sphere submonoid, i.e. in the circle. -/
lemma mem_unitSphere_of_norm {z : ℂ} (hz : ‖z‖ = 1) : z ∈ Submonoid.unitSphere ℂ := by
  change z ∈ (Submonoid.unitSphere ℂ : Set ℂ)
  rw [Submonoid.coe_unitSphere]
  simpa [Metric.mem_sphere, dist_eq_norm] using hz

/-- The circle element corresponding to a complex number of norm `1`. -/
def circOf (z : ℂ) (hz : ‖z‖ = 1) : UnitAddCircle :=
  (AddCircle.homeomorphCircle (T := 1) one_ne_zero).symm ⟨z, by
    change z ∈ (Submonoid.unitSphere ℂ : Set ℂ)
    rw [Submonoid.coe_unitSphere]
    simpa [Metric.mem_sphere, dist_eq_norm] using hz⟩

@[simp] lemma circleOf_circOf (z : ℂ) (hz : ‖z‖ = 1) : circleOf (circOf z hz) = z := by
  have h := Homeomorph.apply_symm_apply (AddCircle.homeomorphCircle (T := 1) one_ne_zero)
    (⟨z, by
      change z ∈ (Submonoid.unitSphere ℂ : Set ℂ)
      rw [Submonoid.coe_unitSphere]
      simpa [Metric.mem_sphere, dist_eq_norm] using hz⟩ : Circle)
  simp only [circleOf, circOf]
  exact congrArg (fun x : Circle => (x : ℂ)) h

lemma circleOf_add (a b : UnitAddCircle) : circleOf (a + b) = circleOf a * circleOf b := by
  simp only [circleOf]
  rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply,
    AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add, Circle.coe_mul]

lemma circleOf_nsmul (n : ℕ) (a : UnitAddCircle) : circleOf (n • a) = circleOf a ^ n := by
  induction n with
  | zero =>
      simp only [zero_nsmul, circleOf, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zero]
      rfl
  | succ k ih => rw [succ_nsmul, circleOf_add, ih, pow_succ]

/-- The cap hemisphere `{|z₁| ≤ |z₂|}` of the unit sphere: a closed solid torus. -/
def capHemi : Set (unitSphere 3) := {v | ‖c₁ v.1‖ ≤ ‖c₂ v.1‖}

/-- The configuration hemisphere `{|z₂| ≤ |z₁|}` of the unit sphere: a closed solid torus. -/
def confHemi : Set (unitSphere 3) := {v | ‖c₂ v.1‖ ≤ ‖c₁ v.1‖}

lemma isClosed_capHemi : IsClosed capHemi :=
  isClosed_le (continuous_norm.comp (continuous_c₁.comp continuous_subtype_val))
    (continuous_norm.comp (continuous_c₂.comp continuous_subtype_val))

lemma isClosed_confHemi : IsClosed confHemi :=
  isClosed_le (continuous_norm.comp (continuous_c₂.comp continuous_subtype_val))
    (continuous_norm.comp (continuous_c₁.comp continuous_subtype_val))

lemma capHemi_union_confHemi : capHemi ∪ confHemi = Set.univ := by
  ext v
  simp only [Set.mem_union, Set.mem_univ, iff_true, capHemi, confHemi, Set.mem_setOf_eq]
  exact le_total _ _

lemma capHemi_inter_confHemi : capHemi ∩ confHemi = {v | ‖c₁ v.1‖ = ‖c₂ v.1‖} := by
  ext v
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, capHemi, confHemi]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- The cap point of the sphere, as a point of `CapTorus = S¹ × D²`: the first coordinate is
`(‖z₂‖/z₂)² = e^{-2iβ}` and the disk coordinate is `√2 z₁z₂/‖z₂‖ = √2 z₁ e^{iβ}`. -/
def capPt (v : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖}) : CapTorus :=
  (circOf ((((‖c₂ v.1.1‖ : ℝ) : ℂ) / c₂ v.1.1) ^ 2)
      (norm_sq_self_div _ (ne_zero_of_norm_le v.2 (sq_norm_eq_one v.1))),
   ⟨(Real.sqrt 2 : ℂ) * c₁ v.1.1 * c₂ v.1.1 / ((‖c₂ v.1.1‖ : ℝ) : ℂ), by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact norm_sqrt_two_mul_div_le _ _
        (ne_zero_of_norm_le v.2 (sq_norm_eq_one v.1))
        (norm_le_inv_sqrt_two v.2 (sq_norm_eq_one v.1))⟩)

/-- The configuration point of the sphere, as a point of `ConfTorus = D² × S¹`: the disk coordinate
is `√2 z₂z₁/‖z₁‖ = √2 z₂ e^{iα}` and the second coordinate is `(z₁/‖z₁‖)² = e^{2iα}`. -/
def confPt (v : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖}) : ConfTorus :=
  (⟨(Real.sqrt 2 : ℂ) * c₂ v.1.1 * c₁ v.1.1 / ((‖c₁ v.1.1‖ : ℝ) : ℂ), by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact norm_sqrt_two_mul_div_le _ _
        (ne_zero_of_norm_le v.2 (sq_norm_eq_one_comm v.1))
        (norm_le_inv_sqrt_two v.2 (sq_norm_eq_one_comm v.1))⟩,
   circOf ((c₁ v.1.1 / ((‖c₁ v.1.1‖ : ℝ) : ℂ)) ^ 2)
      (norm_sq_div_self _ (ne_zero_of_norm_le v.2 (sq_norm_eq_one_comm v.1))))

/-- The cap branch of the glueing map `S³ → LensSpace`, as a total function (with an arbitrary value
off the cap hemisphere). -/
def phiCap (v : unitSphere 3) : LensSpace :=
  if h : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖ then Quotient.mk'' (Sum.inl (capPt ⟨v, h⟩))
  else Quotient.mk'' (Sum.inl ((0 : UnitAddCircle), ⟨0, by simp⟩))

/-- The configuration branch of the glueing map `S³ → LensSpace`, as a total function (with an
arbitrary value off the configuration hemisphere). -/
def phiConf (v : unitSphere 3) : LensSpace :=
  if h : ‖c₂ v.1‖ ≤ ‖c₁ v.1‖ then Quotient.mk'' (Sum.inr (confPt ⟨v, h⟩))
  else Quotient.mk'' (Sum.inr ((⟨0, by simp⟩ : Metric.closedBall (0 : ℂ) 1), 0))

/-- **The glueing map `S³ → LensSpace`**: `capPt` on the cap hemisphere, `confPt` on the
configuration hemisphere; the two branches agree on the common boundary. -/
def phi (v : unitSphere 3) : LensSpace :=
  if h : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖ then Quotient.mk'' (Sum.inl (capPt ⟨v, h⟩))
  else Quotient.mk'' (Sum.inr (confPt ⟨v, le_of_not_ge h⟩))

end

end Work.Drive
