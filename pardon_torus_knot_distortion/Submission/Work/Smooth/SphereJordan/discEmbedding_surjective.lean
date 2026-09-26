import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.CoreTopology.circle_lift_eq_of_extends_disk

/-!
# An injective self-map of the disc fixing the boundary circle is surjective

Let `𝔻 = {z : ℂ | ‖z‖ ≤ 1}` be the closed unit disc and let `F : 𝔻 → 𝔻` be a continuous
injective map which fixes the boundary circle pointwise and maps the open disc into itself.
Then `F` is surjective.  This file proves that statement
(`Work.Smooth.SphereJordan.discEmbedding_surjective`); the hypothesis that the open disc is
mapped into itself is not actually needed, and is kept because the caller states it.

## The mathematical argument

Surjectivity is classically equivalent to the non-existence of a continuous retraction of the
closed disc onto its boundary circle (Brouwer's theorem), and it is the latter that is proved
here, using the covering space `Circle.exp : ℝ → Circle` of the unit circle:

* if a point `y` of the disc were missed by `F`, then `y` would lie in the **open** disc
  (the boundary is fixed), and the radial projection `ρ_y` of the disc away from `y` onto the
  unit circle (the point where the ray from `y` through `x` meets the circle) would be a
  continuous **retraction** `r` of `𝔻` onto `S¹` fixing the boundary;
* a retraction `r` gives a continuous map `G : 𝔻 → Circle` which extends the loop
  `θ ↦ exp (iθ)`: the loop has the lift `θ ↦ θ` with `Λ (2π) ≠ Λ 0`, while a loop extending
  over the disc has every lift a *loop*, `Λ (2π) = Λ 0`
  (`Work.CoreTopology.circle_lift_eq_of_extends_disk`).  Contradiction.

The radial projection is written down explicitly: for `x ≠ y` let `u = (x - y)/‖x - y‖` (a unit
vector) and let `s = -⟪y,u⟫_ℝ + √(⟪y,u⟫_ℝ² + 1 - ‖y‖²)` be the positive root of
`‖y + s u‖² = 1`; then `radialProj y x = y + s • u` lies on the unit circle, and for `‖x‖ = 1`
one has `s = ‖x - y‖`, so that `radialProj y x = x`: the boundary is fixed.
-/

open Set
open scoped InnerProductSpace

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## The radial projection of the disc away from an interior point -/

/-- The direction of the ray from `y` through `x`, normalised to a unit vector.  This is a total
function of `x` (at `x = y` the value is the junk value `0/0 = 0`); all the lemmas below carry the
hypothesis `x ≠ y`. -/
def rayDir (y x : ℂ) : ℂ := (x - y) / ((‖x - y‖ : ℝ) : ℂ)

/-- The direction of a ray is a unit vector. -/
theorem norm_rayDir {y x : ℂ} (hx : x ≠ y) : ‖rayDir y x‖ = 1 := by
  have hxy : x - y ≠ 0 := sub_ne_zero.mpr hx
  rw [rayDir, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hxy)]

/-- Multiplying the direction of the ray by the distance recovers the difference `x - y`. -/
theorem rayDir_smul {y x : ℂ} (hx : x ≠ y) : (‖x - y‖ : ℝ) • rayDir y x = x - y := by
  have hne : ((‖x - y‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  rw [Complex.real_smul, rayDir, ← mul_div_assoc, mul_div_cancel_left₀ _ hne]

/-- The direction of a ray depends continuously on `x`, away from the base point `y`. -/
theorem continuousAt_rayDir (y x : ℂ) (hx : x ≠ y) : ContinuousAt (rayDir y) x := by
  have hnum : ContinuousAt (fun z : ℂ => z - y) x := continuousAt_id.sub continuousAt_const
  have hden : ContinuousAt (fun z : ℂ => ((‖z - y‖ : ℝ) : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp ((continuousAt_id.sub continuousAt_const).norm)
  have hne : ((‖x - y‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  exact hnum.div hden hne

/-- The distance from `y` to the unit circle along the ray in the direction `u`
(`‖u‖ = 1`): the positive root `s` of `‖y + s • u‖ = 1`, in closed form. -/
def radialParam (y u : ℂ) : ℝ :=
  -⟪y, u⟫_ℝ + Real.sqrt (⟪y, u⟫_ℝ ^ 2 + 1 - ‖y‖ ^ 2)

/-- The **radial projection** of the disc away from the point `y`: the point of the unit circle
met by the ray starting at `y` and passing through `x`. -/
def radialProj (y x : ℂ) : ℂ := y + radialParam y (rayDir y x) • rayDir y x

/-- Cauchy–Schwarz for a unit vector `u`. -/
theorem inner_sq_le_norm_sq (y u : ℂ) (hu : ‖u‖ = 1) : ⟪y, u⟫_ℝ ^ 2 ≤ ‖y‖ ^ 2 := by
  have h := abs_real_inner_le_norm y u
  rw [hu, mul_one] at h
  rw [sq_le_sq, abs_of_nonneg (norm_nonneg y)]
  exact h

/-- The argument of the square root in `radialParam` is nonnegative for `‖y‖ ≤ 1`. -/
theorem sqrt_arg_nonneg (y u : ℂ) (hy : ‖y‖ ≤ 1) (hu : ‖u‖ = 1) :
    0 ≤ ⟪y, u⟫_ℝ ^ 2 + 1 - ‖y‖ ^ 2 := by
  have hβ := inner_sq_le_norm_sq y u hu
  nlinarith [sq_nonneg ⟪y, u⟫_ℝ, norm_nonneg y]

/-- `radialParam` is a root of the quadratic `s² + 2⟪y,u⟫_ℝ s + (‖y‖² - 1) = 0`. -/
theorem radialParam_eq (y u : ℂ) (hy : ‖y‖ ≤ 1) (hu : ‖u‖ = 1) :
    radialParam y u ^ 2 + 2 * ⟪y, u⟫_ℝ * radialParam y u = 1 - ‖y‖ ^ 2 := by
  have hβ := inner_sq_le_norm_sq y u hu
  have hd : Real.sqrt (⟪y, u⟫_ℝ ^ 2 + 1 - ‖y‖ ^ 2) ^ 2 = ⟪y, u⟫_ℝ ^ 2 + 1 - ‖y‖ ^ 2 :=
    Real.sq_sqrt (sqrt_arg_nonneg y u hy hu)
  simp only [radialParam]
  nlinarith [hd]

/-- Expanding `‖y + r • u‖²` for a unit vector `u`. -/
theorem norm_add_smul_sq (y u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) :
    ‖y + r • u‖ ^ 2 = ‖y‖ ^ 2 + 2 * r * ⟪y, u⟫_ℝ + r ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
  ring

/-- For `‖y‖ < 1` and a unit vector `u`, the square root occurring in `radialParam` dominates
`|⟪y,u⟫_ℝ|`: the ray from `y` in the direction `u` does meet the unit circle. -/
theorem abs_inner_lt_sqrt (y u : ℂ) (hy : ‖y‖ < 1) (hu : ‖u‖ = 1) :
    |⟪y, u⟫_ℝ| < Real.sqrt (⟪y, u⟫_ℝ ^ 2 + 1 - ‖y‖ ^ 2) := by
  have hd : Real.sqrt (⟪y, u⟫_ℝ ^ 2 + 1 - ‖y‖ ^ 2) ^ 2 = ⟪y, u⟫_ℝ ^ 2 + 1 - ‖y‖ ^ 2 :=
    Real.sq_sqrt (sqrt_arg_nonneg y u hy.le hu)
  have hs : 0 ≤ Real.sqrt (⟪y, u⟫_ℝ ^ 2 + 1 - ‖y‖ ^ 2) := Real.sqrt_nonneg _
  have hsq : ⟪y, u⟫_ℝ ^ 2 < Real.sqrt (⟪y, u⟫_ℝ ^ 2 + 1 - ‖y‖ ^ 2) ^ 2 := by
    rw [hd]
    have hylt : ‖y‖ ^ 2 < 1 := by nlinarith [norm_nonneg y, hy]
    linarith
  have h2 := sq_lt_sq.mp hsq
  rwa [abs_of_nonneg hs] at h2

/-- The parameter `radialParam` is positive: it is the length at which the ray meets the circle. -/
theorem radialParam_pos (y u : ℂ) (hy : ‖y‖ < 1) (hu : ‖u‖ = 1) : 0 < radialParam y u := by
  have h := abs_inner_lt_sqrt y u hy hu
  simp only [radialParam]
  linarith [le_abs_self ⟪y, u⟫_ℝ]

/-- The radial projection lands on the unit circle. -/
theorem norm_radialProj (y : ℂ) (hy : ‖y‖ < 1) {x : ℂ} (hx : x ≠ y) :
    ‖radialProj y x‖ = 1 := by
  have hu : ‖rayDir y x‖ = 1 := norm_rayDir hx
  have hkey : ‖radialProj y x‖ ^ 2 = 1 := by
    have h := norm_add_smul_sq y (rayDir y x) hu (radialParam y (rayDir y x))
    have hs := radialParam_eq y (rayDir y x) hy.le hu
    show ‖y + radialParam y (rayDir y x) • rayDir y x‖ ^ 2 = 1
    linarith [h, hs]
  have hsq : (‖radialProj y x‖ - 1) * (‖radialProj y x‖ + 1) = 0 := by nlinarith [hkey]
  rcases mul_eq_zero.mp hsq with h | h
  · linarith
  · have := norm_nonneg (radialProj y x); linarith

/-- The radial projection fixes the unit circle: the positive root of `‖y + s u‖ = 1` is
`‖x - y‖` when `‖x‖ = 1`. -/
theorem radialProj_eq_self (y : ℂ) (hy : ‖y‖ < 1) {x : ℂ} (hx : x ≠ y) (hx1 : ‖x‖ = 1) :
    radialProj y x = x := by
  have hu : ‖rayDir y x‖ = 1 := norm_rayDir hx
  have hdecomp : y + (‖x - y‖ : ℝ) • rayDir y x = x := by
    rw [rayDir_smul hx]; abel
  have ht : ‖x - y‖ ^ 2 + 2 * ⟪y, rayDir y x⟫_ℝ * ‖x - y‖ = 1 - ‖y‖ ^ 2 := by
    have h := norm_add_smul_sq y (rayDir y x) hu (‖x - y‖)
    rw [hdecomp, hx1] at h
    linarith
  have hs := radialParam_eq y (rayDir y x) hy.le hu
  have hfac : (‖x - y‖ - radialParam y (rayDir y x)) *
      (‖x - y‖ + radialParam y (rayDir y x) + 2 * ⟪y, rayDir y x⟫_ℝ) = 0 := by
    nlinarith [hs, ht]
  have hpos : 0 < ‖x - y‖ + radialParam y (rayDir y x) + 2 * ⟪y, rayDir y x⟫_ℝ := by
    have hlt := abs_inner_lt_sqrt y (rayDir y x) hy hu
    have ht_pos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    simp only [radialParam]
    linarith [neg_abs_le ⟪y, rayDir y x⟫_ℝ]
  have hts : ‖x - y‖ = radialParam y (rayDir y x) := by
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · linarith
  rw [show radialProj y x = y + radialParam y (rayDir y x) • rayDir y x from rfl, ← hts]
  exact hdecomp

/-- The radial projection is continuous away from its base point. -/
theorem continuousAt_radialProj (y x : ℂ) (hx : x ≠ y) : ContinuousAt (radialProj y) x := by
  have hu : ContinuousAt (rayDir y) x := continuousAt_rayDir y x hx
  have hβ : Continuous fun u : ℂ => ⟪y, u⟫_ℝ := continuous_const.inner continuous_id
  have hs : Continuous fun u : ℂ => radialParam y u := by
    simp only [radialParam]
    exact (hβ.neg).add
      (Real.continuous_sqrt.comp (((hβ.pow 2).add continuous_const).sub continuous_const))
  have hcomp : ContinuousAt (fun z : ℂ => radialParam y (rayDir y z)) x := hs.continuousAt.comp hu
  exact continuousAt_const.add (hcomp.smul hu)

/-! ## No retraction of the disc onto its boundary -/

/-- The two parametrisations of the boundary circle of the disc (that of the sphere/Jordan
chapter and that of the topological core) agree. -/
theorem circlePoint_core (θ : ℝ) :
    Work.CoreTopology.circlePoint θ = circlePoint θ := Subtype.ext rfl

/-- **A continuous retraction of the closed disc onto its boundary circle is impossible.**

This is the form of Brouwer's theorem needed for `discEmbedding_surjective`: it is deduced from
the covering space `Circle.exp : ℝ → Circle` of the circle, via the fact that a loop which
extends over the disc has a lift which is a loop
(`Work.CoreTopology.circle_lift_eq_of_extends_disk`), while the standard loop
`θ ↦ exp (iθ)` has the lift `θ ↦ θ`, which is not a loop. -/
theorem no_retraction_disc_aux (r : C(Disc, Disc))
    (hr : ∀ z : Disc, ‖((r z : Disc) : ℂ)‖ = 1)
    (hf : ∀ θ : ℝ, r (circlePoint θ) = circlePoint θ) : False := by
  -- the retraction, as a map into the circle
  let G : C(Disc, Circle) :=
    ⟨fun z => ⟨((r z : Disc) : ℂ), mem_sphere_zero_iff_norm.mpr (hr z)⟩,
      Continuous.subtype_mk (continuous_subtype_val.comp r.continuous)
        (fun z => mem_sphere_zero_iff_norm.mpr (hr z))⟩
  -- the standard loop of the circle, with its lift `θ ↦ θ`
  have hexp2pi : Circle.exp (2 * Real.pi) = 1 := by
    simpa using Circle.exp_int_mul_two_pi 1
  have hper : ∀ θ : ℝ, Circle.exp (θ + 2 * Real.pi) = Circle.exp θ := by
    intro θ
    rw [Circle.exp_add, hexp2pi, mul_one]
  have hG : ∀ θ : ℝ, G (Work.CoreTopology.circlePoint θ) = Circle.exp θ := by
    intro θ
    apply Subtype.ext
    show ((r (Work.CoreTopology.circlePoint θ) : Disc) : ℂ) = (Circle.exp θ : ℂ)
    rw [circlePoint_core θ, hf θ, Work.Smooth.Jordan.circlePoint_coe, Circle.coe_exp]
  have h := Work.CoreTopology.circle_lift_eq_of_extends_disk Circle.exp Circle.exp.continuous hper
    G hG (fun θ : ℝ => θ) continuous_id (fun θ => rfl)
  have hzero : (2 : ℝ) * Real.pi = 0 := h
  have := Real.pi_pos
  linarith

/-! ## The main theorem -/

/-- **An injective continuous self-map of the closed disc which fixes the boundary circle pointwise
is surjective.**

If a point `y` of the disc were missed by `F`, then `y` would be an interior point (all boundary
points are fixed by `F`), and radially projecting the disc away from `y` onto the boundary circle
would give a continuous retraction of the disc onto its boundary, contradicting
`no_retraction_disc_aux` (Brouwer).  The assumption that `F` maps the open disc into itself is not
used. -/
theorem discEmbedding_surjective {F : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc)}
    (hinj : Function.Injective F)
    (hbd : ∀ θ : ℝ, F (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ)
    (hint : ∀ z : Work.Smooth.SphereJordan.Disc,
      ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 → ‖((F z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1) :
    Function.Surjective F := by
  by_contra hsurj
  obtain ⟨y, hy⟩ := by
    simpa only [Function.Surjective, not_forall, not_exists] using hsurj
  have hyF : ∀ z : Disc, ((F z : Disc) : ℂ) ≠ ((y : Disc) : ℂ) :=
    fun z h => hy z (Subtype.ext h)
  -- the missed point is an interior point
  have hy_lt : ‖((y : Disc) : ℂ)‖ < 1 := by
    by_contra hlt
    have hle : ‖((y : Disc) : ℂ)‖ ≤ 1 := by
      have h := y.2
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      exact h
    have h1 : ‖((y : Disc) : ℂ)‖ = 1 := le_antisymm hle (not_lt.mp hlt)
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq y h1
    refine hy (circlePoint θ) ?_
    rw [hbd θ]
    exact hθ
  -- the radial projection of `F` away from `y`
  have hsub : Continuous fun z : Disc => ((F z : Disc) : ℂ) :=
    continuous_subtype_val.comp F.continuous
  have hcont : Continuous fun z : Disc => radialProj ((y : Disc) : ℂ) ((F z : Disc) : ℂ) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact ContinuousAt.comp (f := fun z : Disc => ((F z : Disc) : ℂ)) (x := z)
      (continuousAt_radialProj ((y : Disc) : ℂ) ((F z : Disc) : ℂ) (hyF z))
      hsub.continuousAt
  have hmem : ∀ z : Disc,
      radialProj ((y : Disc) : ℂ) ((F z : Disc) : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (norm_radialProj ((y : Disc) : ℂ) hy_lt (hyF z))
  let r : C(Disc, Disc) :=
    ⟨fun z => ⟨radialProj ((y : Disc) : ℂ) ((F z : Disc) : ℂ), hmem z⟩,
      hcont.subtype_mk hmem⟩
  have hr : ∀ z : Disc, ‖((r z : Disc) : ℂ)‖ = 1 :=
    fun z => norm_radialProj ((y : Disc) : ℂ) hy_lt (hyF z)
  have hrbd : ∀ θ : ℝ, r (circlePoint θ) = circlePoint θ := by
    intro θ
    have hne : ((circlePoint θ : Disc) : ℂ) ≠ ((y : Disc) : ℂ) :=
      fun h => hyF (circlePoint θ) (by rw [hbd θ]; exact h)
    refine Subtype.ext ?_
    show radialProj ((y : Disc) : ℂ) (F (circlePoint θ)) = ((circlePoint θ : Disc) : ℂ)
    rw [hbd θ]
    exact radialProj_eq_self _ hy_lt hne
      (by rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I])
  exact no_retraction_disc_aux r hr hrbd

end

end Work.Smooth.SphereJordan
