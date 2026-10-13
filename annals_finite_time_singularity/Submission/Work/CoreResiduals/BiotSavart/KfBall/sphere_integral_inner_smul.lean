/-
# The second moment of the unit sphere in `ℝ³`

This file proves

`∫_{S²} ⟪z, ω⟫ • ω dσ(ω) = (4π/3) • z`

for the surface measure `σ = volume.toSphere` on the unit sphere of `ℝ³`
(`Work.LWP.R3 = EuclideanSpace ℝ (Fin 3)`), i.e. the classical identity
`∫_{S²} ⟪z,ω⟫ ω dσ = (4π/3) z` used in the Biot–Savart far-field computation.

The route is elementary and self-contained:

* the *tensor* second moment `∫_{S²} ⟪u,h⟫⟪u,w⟫ dσ = (4π/3) ⟪h,w⟫` is obtained from the
  ball second moment via the spherical decomposition `sphere_ball_polar`;
* the ball second moment `∫_{B} ⟪x,h⟫⟪x,w⟫ = (4π/15)⟪h,w⟫` is obtained by expanding in
  coordinates and using that the coordinate moments of the ball are
  `∫_B x_i x_j = (4π/15) δ_ij`; the latter follow from the radial integral
  `∫_B ‖x‖² = 4π/5` (`radial_rpow_integral`) together with the invariance of Lebesgue
  measure under coordinate permutations (`swapCoord`) and sign flips (`flipCoord`);
* the vector-valued identity is recovered by testing against all `w` (`ext_inner_left`).
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.LWP.Defs
import Submission.Work.CoreResiduals.BiotSavart.sphere_ball_polar
import Submission.Work.CoreResiduals.BiotSavart.radial_rpow_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.KfBall

open MeasureTheory Set
open scoped Topology

noncomputable section

/-! ## Elementary coordinates facts for `ℝ³` -/

/-- `⟪x, y⟫ = ∑ i, y i * x i` in `ℝ³`. -/
lemma inner_eq_sum (x y : Work.LWP.R3) : inner ℝ x y = ∑ i, y i * x i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [RCLike.inner_apply]; simp

/-- `⟪x, y⟫ = ∑ i, x i * y i` in `ℝ³`. -/
lemma inner_eq_sum' (x y : Work.LWP.R3) : inner ℝ x y = ∑ i, x i * y i := by
  rw [inner_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => mul_comm (y i) (x i))

/-- `‖x‖² = ∑ i, (x i)²` in `ℝ³`. -/
lemma norm_sq_eq_sum (x : Work.LWP.R3) : ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-! ## Invariance of the ball integral under isometries -/

/-- Change of variables in the unit-ball integral under a linear isometry of `ℝ³`. -/
lemma ball_integral_comp_isometry (f : Work.LWP.R3 ≃ₗᵢ[ℝ] Work.LWP.R3)
    (g : Work.LWP.R3 → ℝ) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, g (f x)
      = ∫ x in Metric.ball (0 : Work.LWP.R3) 1, g x := by
  classical
  have hpre : f ⁻¹' Metric.ball (0 : Work.LWP.R3) 1 = Metric.ball 0 1 := by
    rw [LinearIsometryEquiv.preimage_ball]; simp
  have hiff : ∀ x, (f x ∈ Metric.ball (0 : Work.LWP.R3) 1) ↔ (x ∈ Metric.ball 0 1) :=
    fun x => by rw [← Set.mem_preimage, hpre]
  have hfun : (fun x => (Metric.ball (0 : Work.LWP.R3) 1).indicator (fun x => g (f x)) x)
      = (fun x => (Metric.ball (0 : Work.LWP.R3) 1).indicator g (f x)) := by
    funext x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : x ∈ Metric.ball (0 : Work.LWP.R3) 1
    · rw [if_pos h, if_pos ((hiff x).mpr h)]
    · rw [if_neg h, if_neg (fun hf => h ((hiff x).mp hf))]
  conv_lhs => rw [← integral_indicator measurableSet_ball]
  conv_rhs => rw [← integral_indicator measurableSet_ball]
  rw [hfun]
  exact MeasureTheory.integral_comp f ((Metric.ball (0 : Work.LWP.R3) 1).indicator g)

/-- Any continuous function on `ℝ³` is integrable on the unit ball. -/
lemma integrable_of_continuous_ball {f : Work.LWP.R3 → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict (Metric.ball (0 : Work.LWP.R3) 1)) :=
  (ContinuousOn.integrableOn_compact (μ := volume) (isCompact_closedBall (0 : Work.LWP.R3) 1)
    hf.continuousOn).mono_set Metric.ball_subset_closedBall

/-- The isometry of `ℝ³` negating the `i`-th coordinate. -/
def flipCoord (i : Fin 3) : Work.LWP.R3 ≃ₗᵢ[ℝ] Work.LWP.R3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j : Fin 3 => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma flipCoord_apply (i k : Fin 3) (x : Work.LWP.R3) :
    (flipCoord i x) k = if k = i then -x k else x k := by
  show (LinearIsometryEquiv.piLpCongrRight 2 _ x) k = _
  rw [LinearIsometryEquiv.piLpCongrRight_apply]
  split <;> simp_all

/-- The isometry of `ℝ³` swapping the `i`-th and `j`-th coordinates. -/
def swapCoord (i j : Fin 3) : Work.LWP.R3 ≃ₗᵢ[ℝ] Work.LWP.R3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

lemma swapCoord_apply (i j k : Fin 3) (x : Work.LWP.R3) :
    (swapCoord i j x) k = x (Equiv.swap i j k) := by
  show (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j) x) k = _
  rw [show (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j) x) k
        = ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j) x).ofLp) k from rfl]
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  simp [Equiv.piCongrLeft']

/-! ## Coordinate moments of the unit ball -/

/-- The off-diagonal coordinate moments of the unit ball vanish. -/
lemma moment_off (i j : Fin 3) (hij : i ≠ j) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j) = 0 := by
  have h1 : ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j)
      = ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
          ((flipCoord j x) i) * ((flipCoord j x) j) := by
    rw [ball_integral_comp_isometry (flipCoord j) (fun x => (x i) * (x j))]
  have h2 : ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
          ((flipCoord j x) i) * ((flipCoord j x) j)
      = - ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    rw [flipCoord_apply, flipCoord_apply, if_neg hij, if_pos rfl]
    ring
  linarith [h1, h2]

/-- The diagonal coordinate moments of the unit ball are all equal. -/
lemma moment_sq_eq (i j : Fin 3) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) ^ 2
      = ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x j) ^ 2 := by
  have h1 : ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x j) ^ 2
      = ∫ x in Metric.ball (0 : Work.LWP.R3) 1, ((swapCoord i j x) j) ^ 2 := by
    rw [ball_integral_comp_isometry (swapCoord i j) (fun x => (x j) ^ 2)]
  rw [h1]
  apply integral_congr_ae
  filter_upwards with x
  rw [swapCoord_apply, Equiv.swap_apply_right]

/-- `∫_{B} ‖x‖² = 4π/5`. -/
lemma norm_sq_ball_integral :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, ‖x‖ ^ 2 = 4 * Real.pi / 5 := by
  have h := radial_rpow_integral 2 (by norm_num) 1 (by norm_num)
  norm_num at h
  exact h

/-- Every diagonal coordinate moment of the unit ball equals `4π/15`. -/
lemma moment_sq (i : Fin 3) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) ^ 2 = 4 * Real.pi / 15 := by
  have hsplit : ∫ x in Metric.ball (0 : Work.LWP.R3) 1, ‖x‖ ^ 2
      = (∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x 0) ^ 2)
        + (∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x 1) ^ 2)
        + (∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x 2) ^ 2) := by
    rw [show (fun x : Work.LWP.R3 => ‖x‖ ^ 2)
        = (fun x => (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2) from
          funext (fun x => by rw [norm_sq_eq_sum, Fin.sum_univ_three])]
    have ha : Integrable (fun x : Work.LWP.R3 => (x 0) ^ 2 + (x 1) ^ 2)
        (volume.restrict (Metric.ball (0 : Work.LWP.R3) 1)) :=
      (integrable_of_continuous_ball (by fun_prop)).add (integrable_of_continuous_ball (by fun_prop))
    rw [integral_add ha (integrable_of_continuous_ball (by fun_prop)),
        integral_add (integrable_of_continuous_ball (by fun_prop))
          (integrable_of_continuous_ball (by fun_prop))]
  rw [norm_sq_ball_integral] at hsplit
  rw [moment_sq_eq 0 i, moment_sq_eq 1 i, moment_sq_eq 2 i] at hsplit
  have h3 : (4 : ℝ) * Real.pi / 5 = 3 * (4 * Real.pi / 15) := by ring_nf
  linarith [hsplit, h3]

/-- All coordinate moments of the unit ball: `∫_B x_i x_j = (4π/15) δ_ij`. -/
lemma moment_ij (i j : Fin 3) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j)
      = (4 * Real.pi / 15) * (if i = j then 1 else 0) := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, mul_one]
    simpa [pow_two] using moment_sq i
  · rw [if_neg hij, mul_zero]
    exact moment_off i j hij

/-! ## The second moment of the ball and of the sphere -/

/-- Second moment of the unit ball: `∫_B ⟪x,h⟫⟪x,w⟫ = (4π/15) ⟪h,w⟫`. -/
lemma ball_moment (h w : Work.LWP.R3) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (inner ℝ x h) * (inner ℝ x w)
      = (4 * Real.pi / 15) * inner ℝ h w := by
  have hpoint : (fun x : Work.LWP.R3 => (inner ℝ x h) * (inner ℝ x w))
      = fun x => ∑ i : Fin 3, ∑ j : Fin 3, (h i * w j) * ((x i) * (x j)) := by
    funext x
    rw [inner_eq_sum x h, inner_eq_sum x w, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [hpoint]
  have step1 : ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
        (∑ i : Fin 3, ∑ j : Fin 3, (h i * w j) * ((x i) * (x j)))
      = ∑ i : Fin 3, ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
          (∑ j : Fin 3, (h i * w j) * ((x i) * (x j))) :=
    integral_finset_sum (μ := volume.restrict (Metric.ball (0 : Work.LWP.R3) 1)) Finset.univ
      (f := fun i x => ∑ j : Fin 3, (h i * w j) * ((x i) * (x j)))
      (fun i _ => integrable_of_continuous_ball (by fun_prop))
  rw [step1]
  have step2 : ∀ i : Fin 3, ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
        (∑ j : Fin 3, (h i * w j) * ((x i) * (x j)))
      = ∑ j : Fin 3, (h i * w j)
          * ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j) := by
    intro i
    rw [integral_finset_sum (μ := volume.restrict (Metric.ball (0 : Work.LWP.R3) 1)) Finset.univ
      (f := fun j x => (h i * w j) * ((x i) * (x j)))
      (fun j _ => integrable_of_continuous_ball (by fun_prop))]
    exact Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)
  rw [Finset.sum_congr rfl (fun i _ => step2 i)]
  have step3 : ∑ i : Fin 3, ∑ j : Fin 3,
        (h i * w j) * ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j)
      = ∑ i : Fin 3, ∑ j : Fin 3,
          (h i * w j) * ((4 * Real.pi / 15) * (if i = j then 1 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [moment_ij]
  rw [step3]
  have hinner : ∀ i : Fin 3,
        ∑ j : Fin 3, (h i * w j) * ((4 * Real.pi / 15) * (if i = j then 1 else 0))
      = (4 * Real.pi / 15) * (h i * w i) := by
    intro i
    rw [Finset.sum_congr rfl (fun j _ => show
        (h i * w j) * ((4 * Real.pi / 15) * (if i = j then 1 else 0))
          = (4 * Real.pi / 15) * ((h i * w j) * (if i = j then 1 else 0)) by ring)]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl (fun j _ => show (h i * w j) * (if i = j then 1 else 0)
        = if i = j then h i * w j else 0 by split <;> ring)]
    rw [Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [← Finset.mul_sum, ← inner_eq_sum' h w]

/-- Second moment of the unit sphere: `∫_{S²} ⟪u,h⟫⟪u,w⟫ dσ = (4π/3) ⟪h,w⟫`. -/
lemma sphere_moment (h w : Work.LWP.R3) :
    ∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
        (inner ℝ (u : Work.LWP.R3) h) * (inner ℝ (u : Work.LWP.R3) w)
        ∂(volume : Measure Work.LWP.R3).toSphere = (4 * Real.pi / 3) * inner ℝ h w := by
  rw [sphere_ball_polar h w, ball_moment h w]
  ring_nf

/-! ## The vector-valued second moment -/

theorem sphere_integral_inner_smul (z : Work.LWP.R3) :
    ∫ ω, inner ℝ z (ω : Work.LWP.R3) • (ω : Work.LWP.R3)
      ∂(MeasureTheory.Measure.toSphere (MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3))
      = (4 * Real.pi / 3) • z := by
  apply ext_inner_left ℝ
  intro w
  have hint : Integrable (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
      inner ℝ z (ω : Work.LWP.R3) • (ω : Work.LWP.R3))
      (MeasureTheory.Measure.toSphere (volume : Measure (Work.LWP.R3))) := by
    refine Integrable.of_bound ?_ ‖z‖ ?_
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with ω
      rw [norm_smul, mem_sphere_zero_iff_norm.mp ω.2, mul_one, Real.norm_eq_abs]
      simpa using abs_real_inner_le_norm z (ω : Work.LWP.R3)
  have hconv : (∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
        (inner ℝ z (u : Work.LWP.R3)) * (inner ℝ w (u : Work.LWP.R3))
        ∂(volume : Measure Work.LWP.R3).toSphere) = (4 * Real.pi / 3) * inner ℝ z w := by
    rw [show (∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
          (inner ℝ z (u : Work.LWP.R3)) * (inner ℝ w (u : Work.LWP.R3))
          ∂(volume : Measure Work.LWP.R3).toSphere)
        = (∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
          (inner ℝ (u : Work.LWP.R3) z) * (inner ℝ (u : Work.LWP.R3) w)
          ∂(volume : Measure Work.LWP.R3).toSphere) from by
          apply integral_congr_ae; filter_upwards with u
          rw [real_inner_comm (u : Work.LWP.R3) z, real_inner_comm (u : Work.LWP.R3) w]]
    exact sphere_moment z w
  rw [← innerSL_apply_apply ℝ w, ← ContinuousLinearMap.integral_comp_comm (innerSL ℝ w) hint]
  simp only [innerSL_apply_apply, real_inner_smul_right]
  rw [hconv, real_inner_comm z w]

end

end Work.CoreResiduals.BiotSavart.KfBall
