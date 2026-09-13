/-
# The measure estimate for sliding paraboloids (Savin's Lemma 2.1)

Savin's Lemma 2.1 ([S], CPDE 32 (2007)) is the measure-theoretic core of the Harnack inequality:
if `B` is a closed set of vertices, and one slides the concave paraboloids
`x ↦ -(a/2)‖x - y‖² + c` with vertex `y ∈ B` upwards from below until they touch the graph of a
solution `φ` of the equation, then the set `A` of contact points satisfies `|A| ≥ c |B|` with a
constant `c` which does not depend on `a` (for `a` small).

Savin's proof assumes first that `φ` is uniformly semiconcave (so that `Dφ` is Lipschitz on `A`)
and then removes this assumption by an inf-convolution regularisation.  In our situation `φ` is a
classical solution, and we can argue directly: at a contact point `x` the vertex `y` is determined
by `x` through `y = x + Dφ(x)/a`, and the *equation* together with the touching condition bounds
the Hessian at contact points (`Submission.contact_bound`).  Hence the change of variables formula
(the "≤" direction of the area formula, which does not require injectivity) gives

  `|B| ≤ |{x + Dφ(x)/a : x ∈ A}| ≤ ∫_A |det (1 + D²φ(x)/a)| ≤ K⁴ |A|`,

which is the desired estimate.  This avoids both the semiconcavity assumption and the
inf-convolution regularisation.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Operator
import Submission.Commons.Analysis.Calculus.Gradient.hasFDerivAt_toDual_fderiv
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_add_quadratic
import Submission.Commons.Analysis.Calculus.FDeriv.isSymmetric_hessian
import Submission.Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin
import Submission.Commons.Analysis.Calculus.FDeriv.hasFDerivAt_paraboloid
import Submission.Commons.Analysis.Calculus.FDeriv.quadform_neg_le_of_localMin_paraboloid
import Submission.Commons.Analysis.InnerProductSpace.abs_det_le_pow_of_quadform_bounds

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- The gradient (Riesz representative of the derivative) of a function on `ℝ⁴`, as a vector. -/
noncomputable def gradVec (φ : ℝ⁴ → ℝ) (x : ℝ⁴) : ℝ⁴ :=
  (InnerProductSpace.toDual ℝ ℝ⁴).symm (fderiv ℝ φ x)

/-- The Hessian of `φ` at `x` as a self-adjoint operator (the Fréchet derivative of the gradient);
it agrees with `H φ s x` whenever `s` is a neighbourhood of `x`. -/
noncomputable def hessOp (φ : ℝ⁴ → ℝ) (x : ℝ⁴) : ℝ⁴ →L[ℝ] ℝ⁴ :=
  InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ φ) x)

/-- The map of the sliding paraboloid argument: `x ↦ x + ∇φ(x)/a`.  A paraboloid of opening `a`
which touches the graph of `φ` from below at `x` has vertex `slideMap a φ x`. -/
noncomputable def slideMap (a : ℝ) (φ : ℝ⁴ → ℝ) (x : ℝ⁴) : ℝ⁴ :=
  x + a⁻¹ • gradVec φ x

@[simp] theorem slideMap_apply (a : ℝ) (φ : ℝ⁴ → ℝ) (x : ℝ⁴) :
    slideMap a φ x = x + a⁻¹ • gradVec φ x := rfl

/-- The set of contact points of concave paraboloids of opening `a` whose vertex lies in `B`:
the paraboloid with vertex `y = slideMap a φ x` lies below the graph of `φ` on `closedBall 0 1`
and touches it at `x`. -/
def contactSet (a : ℝ) (φ : ℝ⁴ → ℝ) (B : Set ℝ⁴) : Set ℝ⁴ :=
  {x ∈ closedBall 0 (1 / 2) |
    slideMap a φ x ∈ B ∧
      ∀ z ∈ closedBall 0 1,
        φ x + a / 2 * ‖x - slideMap a φ x‖ ^ 2 ≤ φ z + a / 2 * ‖z - slideMap a φ x‖ ^ 2}

theorem mem_contactSet {a : ℝ} {φ : ℝ⁴ → ℝ} {B : Set ℝ⁴} {x : ℝ⁴} :
    x ∈ contactSet a φ B ↔
      x ∈ closedBall 0 (1 / 2) ∧ slideMap a φ x ∈ B ∧
        ∀ z ∈ closedBall 0 1,
          φ x + a / 2 * ‖x - slideMap a φ x‖ ^ 2 ≤ φ z + a / 2 * ‖z - slideMap a φ x‖ ^ 2 :=
  Iff.rfl

theorem contactSet_subset_closedBall {a : ℝ} {φ : ℝ⁴ → ℝ} {B : Set ℝ⁴} :
    contactSet a φ B ⊆ closedBall 0 (1 / 2) := fun _ hx => hx.1

/-- The contact points of paraboloids of opening `a` whose *vertex lies in the closed unit ball*;
this is Savin's and Fan's `T_a`.  The restriction on the vertex is essential for the passage from
measure estimates on `T_a` to pointwise estimates on `u`: it is what makes the *values* of `φ` at
contact points comparable with the opening (`contactPt_le_value`), and it is preserved both by
enlarging the opening (the new vertex is a convex combination of the old vertex and the contact
point, `contactPt_mono`) and by the perturbation of the vertex in the growth lemma. -/
noncomputable def contactPt (a : ℝ) (φ : ℝ⁴ → ℝ) : Set ℝ⁴ := contactSet a φ (closedBall 0 1)

theorem mem_contactPt {a : ℝ} {φ : ℝ⁴ → ℝ} {x : ℝ⁴} :
    x ∈ contactPt a φ ↔
      x ∈ closedBall 0 (1 / 2) ∧ slideMap a φ x ∈ closedBall 0 1 ∧
        ∀ z ∈ closedBall 0 1,
          φ x + a / 2 * ‖x - slideMap a φ x‖ ^ 2 ≤ φ z + a / 2 * ‖z - slideMap a φ x‖ ^ 2 := by
  rw [contactPt, mem_contactSet]

theorem contactPt_subset_closedBall {a : ℝ} {φ : ℝ⁴ → ℝ} :
    contactPt a φ ⊆ closedBall 0 (1 / 2) := fun _ hx => (mem_contactPt.mp hx).1

/-- Monotonicity of the contact sets in the vertex set. -/
theorem contactSet_mono_vertex {a : ℝ} {φ : ℝ⁴ → ℝ} {B B' : Set ℝ⁴} (h : B ⊆ B') :
    contactSet a φ B ⊆ contactSet a φ B' := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := mem_contactSet.mp hx
  exact mem_contactSet.mpr ⟨h1, h h2, h3⟩

theorem contactSet_subset_contactPt {a : ℝ} {φ : ℝ⁴ → ℝ} {B : Set ℝ⁴}
    (hB : B ⊆ closedBall 0 1) : contactSet a φ B ⊆ contactPt a φ :=
  contactSet_mono_vertex hB


/-- Quadratic identity behind the monotonicity of the contact sets in the opening. -/
theorem slide_quad_key {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (g w : ℝ⁴) :
    (a / 2) * ‖-(a⁻¹ • g)‖ ^ 2 - (a / 2) * ‖w - a⁻¹ • g‖ ^ 2
      + (b / 2) * ‖w - b⁻¹ • g‖ ^ 2 - (b / 2) * ‖-(b⁻¹ • g)‖ ^ 2
      = ((b - a) / 2) * ‖w‖ ^ 2 := by
  rw [norm_neg, norm_neg, norm_sub_sq_real w (a⁻¹ • g), norm_sub_sq_real w (b⁻¹ • g),
    real_inner_smul_right, real_inner_smul_right, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  field_simp
  ring

/-- **Monotonicity of the contact sets in the opening.**  Touching a function from below with a
paraboloid of opening `a` also touches it with any larger opening, with the new vertex
`(a/b) • slideMap a φ x + (1 - a/b) • x`: the first-order condition at the contact point makes the
difference of the two paraboloids vanish on the unit ball, and the new vertex is a convex
combination of the old vertex and the contact point, hence lies in the unit ball. -/
theorem contactPt_mono {φ : ℝ⁴ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    contactPt a φ ⊆ contactPt b φ := by
  intro x hx
  obtain ⟨hx1, hxv, hmin⟩ := mem_contactPt.mp hx
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt (lt_trans ha hab)
  have e1 : x - slideMap a φ x = -(a⁻¹ • gradVec φ x) := by
    rw [slideMap_apply]; abel
  have e2 : x - slideMap b φ x = -(b⁻¹ • gradVec φ x) := by
    rw [slideMap_apply]; abel
  have e3 : ∀ z : ℝ⁴, z - slideMap a φ x = (z - x) - a⁻¹ • gradVec φ x := by
    intro z; rw [slideMap_apply]; abel
  have e4 : ∀ z : ℝ⁴, z - slideMap b φ x = (z - x) - b⁻¹ • gradVec φ x := by
    intro z; rw [slideMap_apply]; abel
  have hbw : 0 ≤ a / b := div_nonneg ha.le (lt_trans ha hab).le
  have hbw' : 0 ≤ 1 - a / b := by
    have h1 : a / b ≤ 1 := (div_le_one (lt_trans ha hab)).mpr hab.le
    linarith
  have hws : a / b + (1 - a / b) = 1 := by ring
  have hcoef : (a / b) * a⁻¹ = b⁻¹ := by field_simp
  have hconv : slideMap b φ x = (a / b) • slideMap a φ x + (1 - a / b) • x := by
    calc slideMap b φ x = x + b⁻¹ • gradVec φ x := by rw [slideMap_apply]
      _ = ((a / b) + (1 - a / b)) • x + ((a / b) * a⁻¹) • gradVec φ x := by
            rw [hws, one_smul, hcoef]
      _ = (a / b) • x + ((a / b) * a⁻¹) • gradVec φ x + (1 - a / b) • x := by
            rw [add_smul]; abel
      _ = (a / b) • (x + a⁻¹ • gradVec φ x) + (1 - a / b) • x := by
            rw [smul_add, smul_smul]
      _ = (a / b) • slideMap a φ x + (1 - a / b) • x := by rw [slideMap_apply]
  have hxv' : slideMap b φ x ∈ closedBall 0 1 := by
    rw [hconv]
    exact convex_closedBall (0 : ℝ⁴) 1 hxv (closedBall_subset_closedBall (by norm_num) hx1)
      hbw hbw' hws
  rw [mem_contactPt]
  refine ⟨hx1, hxv', fun z hz => ?_⟩
  have h := hmin z hz
  have hkey := slide_quad_key (a := a) (b := b) ha' hb' (gradVec φ x) (z - x)
  rw [e1, e3 z] at h
  rw [e2, e4 z]
  nlinarith [hkey, h, sq_nonneg ‖z - x‖, hab]

/-- **The values at contact points are controlled by the opening.**  If `φ x₁ ≤ 1` at some point
`x₁` of the unit ball, then `φ x ≤ 1 + 2a` at every contact point of opening `a`: the vertex of a
contact paraboloid of opening `a` lies in the unit ball, so the touching condition tested at `x₁`
gives `φ x ≤ φ x₁ + (a/2)‖x₁ - y‖² ≤ 1 + 2a`. -/
theorem contactPt_le_value {a : ℝ} (ha : 0 < a) {φ : ℝ⁴ → ℝ} {x₁ x : ℝ⁴}
    (hx₁ : x₁ ∈ closedBall 0 1) (hle : φ x₁ ≤ 1) (hx : x ∈ contactPt a φ) :
    φ x ≤ 1 + 2 * a := by
  obtain ⟨-, hxv, hmin⟩ := mem_contactPt.mp hx
  have hy : ‖slideMap a φ x‖ ≤ 1 := by
    have h := mem_closedBall.mp hxv; rwa [dist_zero_right] at h
  have hx₁n : ‖x₁‖ ≤ 1 := by
    have h := mem_closedBall.mp hx₁; rwa [dist_zero_right] at h
  have h := hmin x₁ hx₁
  have hd : ‖x₁ - slideMap a φ x‖ ^ 2 ≤ 4 := by
    have h1 : ‖x₁ - slideMap a φ x‖ ≤ 2 := by
      calc ‖x₁ - slideMap a φ x‖ ≤ ‖x₁‖ + ‖slideMap a φ x‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith
    nlinarith [h1, norm_nonneg (x₁ - slideMap a φ x)]
  nlinarith [h, hle, hd, ha, sq_nonneg ‖x - slideMap a φ x‖]

theorem mem_ball_of_mem_closedBall_half {x : ℝ⁴} (hx : x ∈ closedBall 0 (1 / 2)) :
    x ∈ ball 0 1 := by
  rw [mem_closedBall, dist_zero_right] at hx
  rw [mem_ball, dist_zero_right]
  linarith

/-- `contactSet` is closed for `φ` of class `C¹` near the unit ball and `B` closed. -/
theorem isClosed_contactSet {a : ℝ} {φ : ℝ⁴ → ℝ} {B : Set ℝ⁴} (hB : IsClosed B)
    (hφ : ContDiffOn ℝ 1 φ (ball 0 1)) : IsClosed (contactSet a φ B) := by
  have hKball : closedBall (0 : ℝ⁴) (1 / 2) ⊆ ball 0 1 := fun x hx =>
    mem_ball_of_mem_closedBall_half hx
  have hφcont : ContinuousOn φ (closedBall (0 : ℝ⁴) (1 / 2)) := (hφ.continuousOn).mono hKball
  have hfd : ContinuousOn (fderiv ℝ φ) (closedBall (0 : ℝ⁴) (1 / 2)) :=
    (Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv isOpen_ball hφ).mono hKball
  have hgrad : ContinuousOn (gradVec φ) (closedBall (0 : ℝ⁴) (1 / 2)) :=
    (InnerProductSpace.toDual ℝ ℝ⁴).symm.continuous.comp_continuousOn hfd
  have hsm : ContinuousOn (slideMap a φ) (closedBall (0 : ℝ⁴) (1 / 2)) := by
    have h2 : ContinuousOn (fun x : ℝ⁴ => x + a⁻¹ • gradVec φ x)
        (closedBall (0 : ℝ⁴) (1 / 2)) := continuousOn_id.add (hgrad.const_smul a⁻¹)
    exact h2
  have haux : ∀ z : ℝ⁴, IsClosed (closedBall (0 : ℝ⁴) (1 / 2) ∩
      {x : ℝ⁴ | φ x + a / 2 * ‖x - slideMap a φ x‖ ^ 2
        ≤ φ z + a / 2 * ‖z - slideMap a φ x‖ ^ 2}) := by
    intro z
    have hfun : ContinuousOn (fun x : ℝ⁴ => (φ z + a / 2 * ‖z - slideMap a φ x‖ ^ 2)
        - (φ x + a / 2 * ‖x - slideMap a φ x‖ ^ 2)) (closedBall (0 : ℝ⁴) (1 / 2)) := by
      have h1 : ContinuousOn (fun x : ℝ⁴ => ‖z - slideMap a φ x‖)
          (closedBall (0 : ℝ⁴) (1 / 2)) := (continuousOn_const.sub hsm).norm
      have h2 : ContinuousOn (fun x : ℝ⁴ => ‖x - slideMap a φ x‖)
          (closedBall (0 : ℝ⁴) (1 / 2)) := (continuousOn_id.sub hsm).norm
      exact (continuousOn_const.add ((h1.pow 2).const_mul (a / 2))).sub
        (hφcont.add ((h2.pow 2).const_mul (a / 2)))
    have h4 := hfun.preimage_isClosed_of_isClosed isClosed_closedBall (isClosed_Ici (a := (0 : ℝ)))
    have hEq : (fun x : ℝ⁴ => (φ z + a / 2 * ‖z - slideMap a φ x‖ ^ 2)
        - (φ x + a / 2 * ‖x - slideMap a φ x‖ ^ 2)) ⁻¹' Set.Ici (0 : ℝ)
        = {x : ℝ⁴ | φ x + a / 2 * ‖x - slideMap a φ x‖ ^ 2
            ≤ φ z + a / 2 * ‖z - slideMap a φ x‖ ^ 2} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_setOf_eq]
      constructor <;> intro h <;> linarith
    rw [hEq] at h4
    exact h4
  have hset : contactSet a φ B = (closedBall (0 : ℝ⁴) (1 / 2) ∩ slideMap a φ ⁻¹' B) ∩
      ⋂ z ∈ closedBall (0 : ℝ⁴) 1, closedBall (0 : ℝ⁴) (1 / 2) ∩
        {x : ℝ⁴ | φ x + a / 2 * ‖x - slideMap a φ x‖ ^ 2
          ≤ φ z + a / 2 * ‖z - slideMap a φ x‖ ^ 2} := by
    ext x
    simp only [mem_contactSet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun z hz => ⟨h1, h3 z hz⟩⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, fun z hz => (h3 z hz).2⟩
  rw [hset]
  exact IsClosed.inter (hsm.preimage_isClosed_of_isClosed isClosed_closedBall hB)
    (isClosed_biInter fun z _ => haux z)

/-- At an interior minimiser of `z ↦ φ z + (a/2)‖z - y‖²` the vertex of the paraboloid is the
image of the minimiser under the sliding map. -/
theorem slideMap_eq_of_isMin {a : ℝ} (ha : a ≠ 0) {φ : ℝ⁴ → ℝ} {x y : ℝ⁴}
    (hx : x ∈ ball 0 1) (hφx : ContDiffAt ℝ 1 φ x)
    (hmin : ∀ z ∈ closedBall 0 1,
      φ x + a / 2 * ‖x - y‖ ^ 2 ≤ φ z + a / 2 * ‖z - y‖ ^ 2) :
    slideMap a φ x = y := by
  have hxcl : x ∈ closedBall 0 1 := ball_subset_closedBall hx
  have hloc : IsLocalMin (fun z : ℝ⁴ => φ z + a / 2 * ‖z - y‖ ^ 2) x := by
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    exact hmin z (ball_subset_closedBall hz)
  have h0 : fderiv ℝ (fun z : ℝ⁴ => φ z + a / 2 * ‖z - y‖ ^ 2) x = 0 := hloc.fderiv_eq_zero
  have hpar : HasFDerivAt (fun z : ℝ⁴ => a / 2 * ‖z - y‖ ^ 2) (a • innerSL ℝ (x - y)) x :=
    Commons.Analysis.Calculus.FDeriv.hasFDerivAt_paraboloid a y x
  have hsum : fderiv ℝ (fun z : ℝ⁴ => φ z + a / 2 * ‖z - y‖ ^ 2) x
      = fderiv ℝ φ x + a • innerSL ℝ (x - y) := by
    have hsplit : (fun z : ℝ⁴ => φ z + a / 2 * ‖z - y‖ ^ 2)
        = (φ + fun z : ℝ⁴ => a / 2 * ‖z - y‖ ^ 2) := rfl
    rw [hsplit, fderiv_add (hφx.differentiableAt (by norm_num)) hpar.differentiableAt,
      hpar.fderiv]
  rw [hsum] at h0
  have hfφ : fderiv ℝ φ x = -a • innerSL ℝ (x - y) := by
    rw [eq_neg_of_add_eq_zero_left h0, neg_smul]
  have hgrad : gradVec φ x = -a • (x - y) := by
    rw [gradVec, hfφ, map_smul,
      show (InnerProductSpace.toDual ℝ ℝ⁴).symm (innerSL ℝ (x - y)) = (x - y) from by
        apply (InnerProductSpace.toDual ℝ ℝ⁴).injective
        rw [LinearIsometryEquiv.apply_symm_apply]
        ext w
        rw [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]]
  rw [slideMap_apply, hgrad, smul_smul]
  have hc : a⁻¹ * -a = -1 := by field_simp
  rw [hc, neg_one_smul]
  abel

/-- Every vertex in `B` occurs as the image of a contact point. -/
theorem subset_image_contactSet {a : ℝ} (ha : a ≠ 0) {φ : ℝ⁴ → ℝ} {B : Set ℝ⁴}
    (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)))
    (hcontact : ∀ y ∈ B, ∃ x ∈ closedBall 0 (1 / 2),
      ∀ z ∈ closedBall 0 1, φ x + a / 2 * ‖x - y‖ ^ 2 ≤ φ z + a / 2 * ‖z - y‖ ^ 2) :
    B ⊆ slideMap a φ '' contactSet a φ B := by
  intro y hy
  obtain ⟨x, hx, hmin⟩ := hcontact y hy
  have hxball : x ∈ ball 0 1 := mem_ball_of_mem_closedBall_half hx
  have hφx : ContDiffAt ℝ 1 φ x := by
    have hx3 : x ∈ ball 0 (3 / 2) := by
      rw [mem_ball] at hxball ⊢
      linarith
    exact (hφ.contDiffAt (isOpen_ball.mem_nhds hx3)).of_le (m := 1) (by norm_num)
  have hsl : slideMap a φ x = y := slideMap_eq_of_isMin ha hxball hφx hmin
  refine ⟨x, ?_, hsl⟩
  refine mem_contactSet.mpr ⟨hx, ?_, ?_⟩
  · rw [hsl]; exact hy
  · rw [hsl]; exact hmin

/-- The sliding map is differentiable, with derivative `1 + D²φ(x)/a`. -/
theorem hasFDerivAt_slideMap {a : ℝ} {φ : ℝ⁴ → ℝ} {x : ℝ⁴} (hφ : ContDiffAt ℝ 2 φ x) :
    HasFDerivAt (slideMap a φ) ((1 : ℝ⁴ →L[ℝ] ℝ⁴) + a⁻¹ • hessOp φ x) x := by
  have h1 : HasFDerivAt (gradVec φ) (hessOp φ x) x :=
    Commons.Analysis.Calculus.Gradient.hasFDerivAt_toDual_fderiv hφ
  have h2 : HasFDerivAt (fun z : ℝ⁴ => z + a⁻¹ • gradVec φ z)
      ((1 : ℝ⁴ →L[ℝ] ℝ⁴) + a⁻¹ • hessOp φ x) x :=
    (hasFDerivAt_id x).add (h1.const_smul a⁻¹)
  exact h2

theorem hessOp_symm {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2))) {x : ℝ⁴}
    (hx : x ∈ ball 0 (3 / 2)) : (hessOp φ x).IsSymmetric :=
  Commons.Analysis.Calculus.FDeriv.isSymmetric_hessian isOpen_ball hx hφ

/-- At a contact point the function `z ↦ φ z + (a/2)‖z - y‖²` has a local minimum. -/
theorem isLocalMin_of_mem_contactSet {a : ℝ} {φ : ℝ⁴ → ℝ} {B : Set ℝ⁴} {x : ℝ⁴}
    (hx : x ∈ contactSet a φ B) :
    IsLocalMin (fun z : ℝ⁴ => φ z + a / 2 * ‖z - slideMap a φ x‖ ^ 2) x := by
  have hxball : x ∈ ball 0 1 := mem_ball_of_mem_closedBall_half (contactSet_subset_closedBall hx)
  have hmin := hx.2.2
  filter_upwards [isOpen_ball.mem_nhds hxball] with z hz
  exact hmin z (ball_subset_closedBall hz)

/-- At a contact point the Hessian of `φ` dominates `-a` in the quadratic form sense. -/
theorem quadform_lower_of_mem_contactSet {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)))
    {a : ℝ} {B : Set ℝ⁴} {x : ℝ⁴} (hx : x ∈ contactSet a φ B) (v : ℝ⁴) :
    -a * ‖v‖ ^ 2 ≤ ⟪hessOp φ x v, v⟫ := by
  have hxball : x ∈ ball 0 1 := mem_ball_of_mem_closedBall_half (contactSet_subset_closedBall hx)
  have hx3 : x ∈ ball 0 (3 / 2) := by
    rw [mem_ball] at hxball ⊢; linarith
  have hφx : ContDiffAt ℝ 2 φ x := hφ.contDiffAt (isOpen_ball.mem_nhds hx3)
  have h := Commons.Analysis.Calculus.FDeriv.quadform_neg_le_of_localMin_paraboloid hφx
    (isLocalMin_of_mem_contactSet hx) v
  rw [show ⟪hessOp φ x v, v⟫ = (fderiv ℝ (fderiv ℝ φ) x) v v from
    InnerProductSpace.continuousLinearMapOfBilin_apply (B := fderiv ℝ (fderiv ℝ φ) x) v v]
  exact h

/-- At a contact point the Hessian of `φ` is bounded above by `K a` with `K` independent of `a`. -/
theorem quadform_upper_of_mem_contactSet {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)))
    {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (haε : 3 * ε * a ≤ c / 2) (heq : ∀ x ∈ ball 0 (3 / 2), Fop C ε (hessOp φ x) = 0)
    {B : Set ℝ⁴} {x : ℝ⁴} (hx : x ∈ contactSet a φ B) (v : ℝ⁴) :
    ⟪hessOp φ x v, v⟫ ≤ (2 * trOp C / c + 3) * a * ‖v‖ ^ 2 := by
  have hxball : x ∈ ball 0 1 := mem_ball_of_mem_closedBall_half (contactSet_subset_closedBall hx)
  have hx3 : x ∈ ball 0 (3 / 2) := by
    rw [mem_ball] at hxball ⊢; linarith
  have hsymm : (hessOp φ x).IsSymmetric := hessOp_symm hφ hx3
  exact contact_bound hC hc hcq hε ha haε hsymm
    (fun w => quadform_lower_of_mem_contactSet hφ hx w) (heq x hx3) v

/-- **The measure estimate for the contact set of sliding paraboloids** (Savin's Lemma 2.1, in the
classical case and for the concrete operator `Fop`).

If `φ` is a classical solution of `Fop C ε (D²φ) = 0` on a neighbourhood of the unit ball, if `B` is
a closed set inside `closedBall 0 (1/2)` all of whose points occur as vertices of contact
paraboloids of opening `a` (with contact point inside `closedBall 0 (1/2)`), then the contact set
`A = contactSet a φ B` satisfies `|B| ≤ K⁴ |A|` with `K = 2 tr C / c + 3`, where `c > 0` is an
ellipticity constant of `C`. -/
theorem contactSet_measure {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)))
    {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (haε : 3 * ε * a ≤ c / 2) (heq : ∀ x ∈ ball 0 (3 / 2), Fop C ε (hessOp φ x) = 0)
    {B : Set ℝ⁴} (hB : IsClosed B)
    (hcontact : ∀ y ∈ B, ∃ x ∈ closedBall 0 (1 / 2),
      ∀ z ∈ closedBall 0 1, φ x + a / 2 * ‖x - y‖ ^ 2 ≤ φ z + a / 2 * ‖z - y‖ ^ 2) :
    volume B ≤ ENNReal.ofReal ((1 + (2 * trOp C / c + 3)) ^ 4) * volume (contactSet a φ B) := by
  set K : ℝ := 2 * trOp C / c + 3 with hKdef
  have htrC : 0 ≤ trOp C := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h2 := hcq (stdB4 i)
    have h3 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h3] at h2
    nlinarith [h2]
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  -- (i) every vertex is hit by a contact point
  have hsub : B ⊆ slideMap a φ '' contactSet a φ B :=
    subset_image_contactSet (ne_of_gt ha) hφ hcontact
  -- (ii) the area formula
  have hφ1 : ContDiffOn ℝ 1 φ (ball 0 1) :=
    (hφ.of_le (m := 1) (by norm_num)).mono (ball_subset_ball (by norm_num))
  have hmeas : MeasurableSet (contactSet a φ B) := (isClosed_contactSet hB hφ1).measurableSet
  have hf' : ∀ x ∈ contactSet a φ B, HasFDerivWithinAt (slideMap a φ)
      ((1 : ℝ⁴ →L[ℝ] ℝ⁴) + a⁻¹ • hessOp φ x) (contactSet a φ B) x := by
    intro x hx
    have hxball : x ∈ ball 0 1 := mem_ball_of_mem_closedBall_half (contactSet_subset_closedBall hx)
    have hx3 : x ∈ ball 0 (3 / 2) := by
      rw [mem_ball] at hxball ⊢; linarith
    exact (hasFDerivAt_slideMap (hφ.contDiffAt (isOpen_ball.mem_nhds hx3))).hasFDerivWithinAt
  have harea := MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv
    (μ := (volume : Measure ℝ⁴)) (f := slideMap a φ)
    (f' := fun x : ℝ⁴ => (1 : ℝ⁴ →L[ℝ] ℝ⁴) + a⁻¹ • hessOp φ x) hmeas hf'
  -- (iii) the integrand is bounded
  have hbdd : ∀ x ∈ contactSet a φ B,
      ENNReal.ofReal |((1 : ℝ⁴ →L[ℝ] ℝ⁴) + a⁻¹ • hessOp φ x).det|
        ≤ ENNReal.ofReal ((1 + K) ^ 4) := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal ?_
    have hxball : x ∈ ball 0 1 := mem_ball_of_mem_closedBall_half (contactSet_subset_closedBall hx)
    have hx3 : x ∈ ball 0 (3 / 2) := by
      rw [mem_ball] at hxball ⊢; linarith
    have hsymm : (hessOp φ x).IsSymmetric := hessOp_symm hφ hx3
    have hlo := quadform_lower_of_mem_contactSet hφ hx
    have hup := quadform_upper_of_mem_contactSet hφ hC hc hcq hε ha haε heq hx
    set S : ℝ⁴ →L[ℝ] ℝ⁴ := (1 : ℝ⁴ →L[ℝ] ℝ⁴) + a⁻¹ • hessOp φ x with hSdef
    have hSsym : S.IsSymmetric := by
      rw [hSdef]
      exact LinearMap.IsSymmetric.add LinearMap.IsSymmetric.one
        (LinearMap.IsSymmetric.smul (c := a⁻¹) (by simp) hsymm)
    have hS1 : ∀ v : ℝ⁴, 0 ≤ ⟪S v, v⟫ := by
      intro v
      have h := hlo v
      rw [hSdef]
      simp only [add_apply, smul_apply, one_apply_eq_self, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      have h' : -‖v‖ ^ 2 ≤ a⁻¹ * ⟪hessOp φ x v, v⟫ := by
        have := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr ha))
        have h2 : a⁻¹ * (-a * ‖v‖ ^ 2) = -‖v‖ ^ 2 := by
          field_simp
        linarith [h2]
      linarith
    have hS2 : ∀ v : ℝ⁴, ⟪S v, v⟫ ≤ (1 + K) * ‖v‖ ^ 2 := by
      intro v
      have h := hup v
      rw [hSdef]
      simp only [add_apply, smul_apply, one_apply_eq_self, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      have h' : a⁻¹ * ⟪hessOp φ x v, v⟫ ≤ K * ‖v‖ ^ 2 := by
        have hh : ⟪hessOp φ x v, v⟫ ≤ K * a * ‖v‖ ^ 2 := by
          rw [hKdef]; exact h
        have := mul_le_mul_of_nonneg_left hh (le_of_lt (inv_pos.mpr ha))
        have h2 : a⁻¹ * (K * a * ‖v‖ ^ 2) = K * ‖v‖ ^ 2 := by
          field_simp
        linarith [h2]
      linarith
    have hdet := Commons.Analysis.InnerProductSpace.abs_det_le_pow_of_quadform_bounds hSsym
      (by linarith : (0 : ℝ) ≤ 1 + K) hS1 hS2
    rwa [show Module.finrank ℝ ℝ⁴ = 4 from by simp] at hdet
  calc volume B ≤ volume (slideMap a φ '' contactSet a φ B) := measure_mono hsub
    _ ≤ ∫⁻ x in contactSet a φ B,
          ENNReal.ofReal |((1 : ℝ⁴ →L[ℝ] ℝ⁴) + a⁻¹ • hessOp φ x).det| := harea
    _ ≤ ∫⁻ _x in contactSet a φ B, ENNReal.ofReal ((1 + K) ^ 4) :=
          setLIntegral_mono' hmeas hbdd
    _ = ENNReal.ofReal ((1 + K) ^ 4) * volume (contactSet a φ B) := setLIntegral_const _ _


/-- `contactPt` is closed (and hence measurable) for `φ` of class `C¹` near the unit ball. -/
theorem isClosed_contactPt {a : ℝ} {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 1 φ (ball 0 1)) :
    IsClosed (contactPt a φ) :=
  isClosed_contactSet isClosed_closedBall hφ

theorem measurableSet_contactPt {a : ℝ} {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 1 φ (ball 0 1)) :
    MeasurableSet (contactPt a φ) :=
  (isClosed_contactPt hφ).measurableSet

end

end Submission