/-
# The measure estimate for paraboloids sliding **from above** (positive branch)

This is the mirror image of `Submission.Savin.Measure.contactSet_measure`, needed for the
*propagation* step of the Harnack argument: if the perturbation `w = u - Q` is large somewhere, then
it is large on a set of definite measure.

The function being slid is `w` (a classical solution of
`s2 (A + D²w) = 1` with `trOp (A + D²w) > 0`, where `A = D²Q` is the fixed quadratic solution).
At a contact point of a paraboloid of opening `b` touching from **above** one has
`D²w ⪯ b • 1`; the required lower bound `D²w ⪰ -K b • 1` is
`Submission.contact_bound_above_sigma2` (SESSION 27 -- it uses the concavity of
`M ↦ trM - √(2 + tr(M∘M))` and the *positive branch* hypothesis `trOp (A + M) > 0`).

The sliding map is `Ψ̃ x = x - b⁻¹ ∇w(x)`, whose derivative at a contact point is
`1 - b⁻¹ D²w(x)`, an operator with eigenvalues in `[0, 1 + K]`.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Operator
import Submission.Savin.ContactAbove
import Submission.Savin.Measure
import Submission.Commons.Analysis.Calculus.Gradient.hasFDerivAt_toDual_fderiv
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian
import Submission.Commons.Analysis.Calculus.FDeriv.isSymmetric_hessian
import Submission.Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin
import Submission.Commons.Analysis.Calculus.FDeriv.quadform_neg_le_of_localMin_paraboloid
import Submission.Commons.Analysis.Calculus.FDeriv.hasFDerivAt_paraboloid
import Submission.Commons.Analysis.InnerProductSpace.abs_det_le_pow_of_quadform_bounds

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- The vertex of the paraboloid of opening `b` touching the graph of `w` **from above** at `x`:
`x ↦ x - b⁻¹ ∇w(x)`. -/
noncomputable def slideMapAbove (b : ℝ) (w : ℝ⁴ → ℝ) (x : ℝ⁴) : ℝ⁴ :=
  x - b⁻¹ • gradVec w x

@[simp] theorem slideMapAbove_apply (b : ℝ) (w : ℝ⁴ → ℝ) (x : ℝ⁴) :
    slideMapAbove b w x = x - b⁻¹ • gradVec w x := rfl

/-- The set of contact points of paraboloids of opening `b` touching the graph of `w` from above,
whose vertex lies in `B`. -/
def contactSetAbove (b : ℝ) (w : ℝ⁴ → ℝ) (B : Set ℝ⁴) : Set ℝ⁴ :=
  {x ∈ closedBall 0 (1 / 2) |
    slideMapAbove b w x ∈ B ∧
      ∀ z ∈ closedBall 0 1,
        -w x + b / 2 * ‖x - slideMapAbove b w x‖ ^ 2
          ≤ -w z + b / 2 * ‖z - slideMapAbove b w x‖ ^ 2}

theorem mem_contactSetAbove {b : ℝ} {w : ℝ⁴ → ℝ} {B : Set ℝ⁴} {x : ℝ⁴} :
    x ∈ contactSetAbove b w B ↔
      x ∈ closedBall 0 (1 / 2) ∧ slideMapAbove b w x ∈ B ∧
        ∀ z ∈ closedBall 0 1,
          -w x + b / 2 * ‖x - slideMapAbove b w x‖ ^ 2
            ≤ -w z + b / 2 * ‖z - slideMapAbove b w x‖ ^ 2 :=
  Iff.rfl

theorem contactSetAbove_subset_closedBall {b : ℝ} {w : ℝ⁴ → ℝ} {B : Set ℝ⁴} :
    contactSetAbove b w B ⊆ closedBall 0 (1 / 2) := fun _ hx => hx.1

/-- `contactSetAbove` is closed for `w` of class `C¹` near the unit ball and `B` closed. -/
theorem isClosed_contactSetAbove {b : ℝ} {w : ℝ⁴ → ℝ} {B : Set ℝ⁴} (hB : IsClosed B)
    (hw : ContDiffOn ℝ 1 w (ball 0 1)) : IsClosed (contactSetAbove b w B) := by
  have hKball : closedBall (0 : ℝ⁴) (1 / 2) ⊆ ball 0 1 := fun x hx =>
    mem_ball_of_mem_closedBall_half hx
  have hwcont : ContinuousOn w (closedBall (0 : ℝ⁴) (1 / 2)) := (hw.continuousOn).mono hKball
  have hfd : ContinuousOn (fderiv ℝ w) (closedBall (0 : ℝ⁴) (1 / 2)) :=
    (Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv isOpen_ball hw).mono hKball
  have hgrad : ContinuousOn (gradVec w) (closedBall (0 : ℝ⁴) (1 / 2)) :=
    (InnerProductSpace.toDual ℝ ℝ⁴).symm.continuous.comp_continuousOn hfd
  have hsm : ContinuousOn (slideMapAbove b w) (closedBall (0 : ℝ⁴) (1 / 2)) := by
    have h2 : ContinuousOn (fun x : ℝ⁴ => x - b⁻¹ • gradVec w x)
        (closedBall (0 : ℝ⁴) (1 / 2)) := continuousOn_id.sub (hgrad.const_smul b⁻¹)
    exact h2
  have haux : ∀ z : ℝ⁴, IsClosed (closedBall (0 : ℝ⁴) (1 / 2) ∩
      {x : ℝ⁴ | -w x + b / 2 * ‖x - slideMapAbove b w x‖ ^ 2
        ≤ -w z + b / 2 * ‖z - slideMapAbove b w x‖ ^ 2}) := by
    intro z
    have hfun : ContinuousOn (fun x : ℝ⁴ => (-w z + b / 2 * ‖z - slideMapAbove b w x‖ ^ 2)
        - (-w x + b / 2 * ‖x - slideMapAbove b w x‖ ^ 2)) (closedBall (0 : ℝ⁴) (1 / 2)) := by
      have h1 : ContinuousOn (fun x : ℝ⁴ => ‖z - slideMapAbove b w x‖)
          (closedBall (0 : ℝ⁴) (1 / 2)) := (continuousOn_const.sub hsm).norm
      have h2 : ContinuousOn (fun x : ℝ⁴ => ‖x - slideMapAbove b w x‖)
          (closedBall (0 : ℝ⁴) (1 / 2)) := (continuousOn_id.sub hsm).norm
      exact (continuousOn_const.add ((h1.pow 2).const_mul (b / 2))).sub
        ((hwcont.neg.add ((h2.pow 2).const_mul (b / 2))))
    have h4 := hfun.preimage_isClosed_of_isClosed isClosed_closedBall (isClosed_Ici (a := (0 : ℝ)))
    have hEq : (fun x : ℝ⁴ => (-w z + b / 2 * ‖z - slideMapAbove b w x‖ ^ 2)
        - (-w x + b / 2 * ‖x - slideMapAbove b w x‖ ^ 2)) ⁻¹' Set.Ici (0 : ℝ)
        = {x : ℝ⁴ | -w x + b / 2 * ‖x - slideMapAbove b w x‖ ^ 2
            ≤ -w z + b / 2 * ‖z - slideMapAbove b w x‖ ^ 2} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_setOf_eq]
      constructor <;> intro h <;> linarith
    rw [hEq] at h4
    exact h4
  have hset : contactSetAbove b w B = (closedBall (0 : ℝ⁴) (1 / 2) ∩ slideMapAbove b w ⁻¹' B) ∩
      ⋂ z ∈ closedBall (0 : ℝ⁴) 1, closedBall (0 : ℝ⁴) (1 / 2) ∩
        {x : ℝ⁴ | -w x + b / 2 * ‖x - slideMapAbove b w x‖ ^ 2
          ≤ -w z + b / 2 * ‖z - slideMapAbove b w x‖ ^ 2} := by
    ext x
    simp only [mem_contactSetAbove, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun z hz => ⟨h1, h3 z hz⟩⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, fun z hz => (h3 z hz).2⟩
  rw [hset]
  exact IsClosed.inter (hsm.preimage_isClosed_of_isClosed isClosed_closedBall hB)
    (isClosed_biInter fun z _ => haux z)

/-- At an interior minimiser of `z ↦ -w z + (b/2)‖z - y‖²` the vertex of the paraboloid is the
image of the minimiser under `slideMapAbove`. -/
theorem slideMapAbove_eq_of_isMin {b : ℝ} (hb : b ≠ 0) {w : ℝ⁴ → ℝ} {x y : ℝ⁴}
    (hx : x ∈ ball 0 1) (hw : ContDiffAt ℝ 1 w x)
    (hmin : ∀ z ∈ closedBall 0 1,
      -w x + b / 2 * ‖x - y‖ ^ 2 ≤ -w z + b / 2 * ‖z - y‖ ^ 2) :
    slideMapAbove b w x = y := by
  have hxcl : x ∈ closedBall 0 1 := ball_subset_closedBall hx
  have hloc : IsLocalMin (fun z : ℝ⁴ => -w z + b / 2 * ‖z - y‖ ^ 2) x := by
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    exact hmin z (ball_subset_closedBall hz)
  have h0 : fderiv ℝ (fun z : ℝ⁴ => -w z + b / 2 * ‖z - y‖ ^ 2) x = 0 := hloc.fderiv_eq_zero
  have hpar : HasFDerivAt (fun z : ℝ⁴ => b / 2 * ‖z - y‖ ^ 2) (b • innerSL ℝ (x - y)) x :=
    Commons.Analysis.Calculus.FDeriv.hasFDerivAt_paraboloid b y x
  have hneg : HasFDerivAt (fun z : ℝ⁴ => -w z) (-(fderiv ℝ w x)) x :=
    ((hw.differentiableAt (by norm_num)).hasFDerivAt).neg
  have hsum : fderiv ℝ (fun z : ℝ⁴ => -w z + b / 2 * ‖z - y‖ ^ 2) x
      = -(fderiv ℝ w x) + b • innerSL ℝ (x - y) := by
    have hsplit : (fun z : ℝ⁴ => -w z + b / 2 * ‖z - y‖ ^ 2)
        = ((fun z : ℝ⁴ => -w z) + fun z : ℝ⁴ => b / 2 * ‖z - y‖ ^ 2) := rfl
    rw [hsplit, fderiv_add hneg.differentiableAt hpar.differentiableAt, hneg.fderiv, hpar.fderiv]
  rw [hsum] at h0
  have hfw : fderiv ℝ w x = b • innerSL ℝ (x - y) := by
    rw [neg_add_eq_zero] at h0
    exact h0
  have hgrad : gradVec w x = b • (x - y) := by
    rw [gradVec, hfw, map_smul,
      show (InnerProductSpace.toDual ℝ ℝ⁴).symm (innerSL ℝ (x - y)) = (x - y) from by
        apply (InnerProductSpace.toDual ℝ ℝ⁴).injective
        rw [LinearIsometryEquiv.apply_symm_apply]
        ext v
        rw [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]]
  rw [slideMapAbove_apply, hgrad, smul_smul]
  have hc : b⁻¹ * b = 1 := by field_simp
  rw [hc, one_smul]
  abel

/-- Every vertex of a from-above touching family in `B` occurs as the image of a contact point. -/
theorem subset_image_contactSetAbove {b : ℝ} (hb : b ≠ 0) {w : ℝ⁴ → ℝ} {B : Set ℝ⁴}
    (hw : ContDiffOn ℝ 2 w (ball 0 (3 / 2)))
    (hcontact : ∀ y ∈ B, ∃ x ∈ closedBall 0 (1 / 2),
      ∀ z ∈ closedBall 0 1,
        -w x + b / 2 * ‖x - y‖ ^ 2 ≤ -w z + b / 2 * ‖z - y‖ ^ 2) :
    B ⊆ slideMapAbove b w '' contactSetAbove b w B := by
  intro y hy
  obtain ⟨x, hx, hmin⟩ := hcontact y hy
  have hxball : x ∈ ball 0 1 := mem_ball_of_mem_closedBall_half hx
  have hwx : ContDiffAt ℝ 1 w x := by
    have hx3 : x ∈ ball 0 (3 / 2) := by
      rw [mem_ball] at hxball ⊢
      linarith
    exact (hw.contDiffAt (isOpen_ball.mem_nhds hx3)).of_le (m := 1) (by norm_num)
  have hsl : slideMapAbove b w x = y := slideMapAbove_eq_of_isMin hb hxball hwx hmin
  refine ⟨x, ?_, hsl⟩
  refine mem_contactSetAbove.mpr ⟨hx, ?_, ?_⟩
  · rw [hsl]; exact hy
  · rw [hsl]; exact hmin

/-- The from-above sliding map is differentiable, with derivative `1 - D²w(x)/b`. -/
theorem hasFDerivAt_slideMapAbove {b : ℝ} {w : ℝ⁴ → ℝ} {x : ℝ⁴} (hw : ContDiffAt ℝ 2 w x) :
    HasFDerivAt (slideMapAbove b w) ((1 : ℝ⁴ →L[ℝ] ℝ⁴) - b⁻¹ • hessOp w x) x := by
  have h1 : HasFDerivAt (gradVec w) (hessOp w x) x :=
    Commons.Analysis.Calculus.Gradient.hasFDerivAt_toDual_fderiv hw
  have h2 : HasFDerivAt (fun z : ℝ⁴ => z - b⁻¹ • gradVec w z)
      ((1 : ℝ⁴ →L[ℝ] ℝ⁴) - b⁻¹ • hessOp w x) x :=
    (hasFDerivAt_id x).sub (h1.const_smul b⁻¹)
  exact h2

/-- At a from-above contact point the function `z ↦ -w z + (b/2)‖z - y‖²` has a local minimum. -/
theorem isLocalMin_of_mem_contactSetAbove {b : ℝ} {w : ℝ⁴ → ℝ} {B : Set ℝ⁴} {x : ℝ⁴}
    (hx : x ∈ contactSetAbove b w B) :
    IsLocalMin (fun z : ℝ⁴ => -w z + b / 2 * ‖z - slideMapAbove b w x‖ ^ 2) x := by
  have hxball : x ∈ ball 0 1 :=
    mem_ball_of_mem_closedBall_half (contactSetAbove_subset_closedBall hx)
  have hmin := hx.2.2
  filter_upwards [isOpen_ball.mem_nhds hxball] with z hz
  exact hmin z (ball_subset_closedBall hz)

/-- At a from-above contact point the Hessian of `w` is bounded above by `b`. -/
theorem quadform_upper_of_mem_contactSetAbove {w : ℝ⁴ → ℝ} (hw : ContDiffOn ℝ 2 w (ball 0 (3 / 2)))
    {b : ℝ} {B : Set ℝ⁴} {x : ℝ⁴} (hx : x ∈ contactSetAbove b w B) (v : ℝ⁴) :
    ⟪hessOp w x v, v⟫ ≤ b * ‖v‖ ^ 2 := by
  have hxball : x ∈ ball 0 1 :=
    mem_ball_of_mem_closedBall_half (contactSetAbove_subset_closedBall hx)
  have hx3 : x ∈ ball 0 (3 / 2) := by
    rw [mem_ball] at hxball ⊢; linarith
  have hwx : ContDiffAt ℝ 2 (-w) x := (hw.contDiffAt (isOpen_ball.mem_nhds hx3)).neg
  have h := Commons.Analysis.Calculus.FDeriv.quadform_neg_le_of_localMin_paraboloid hwx
    (isLocalMin_of_mem_contactSetAbove hx) v
  have hderiv : (fderiv ℝ (fderiv ℝ (-w)) x) = -(fderiv ℝ (fderiv ℝ w) x) := by
    have h1 : fderiv ℝ (-w) = (fun z : ℝ⁴ => -(fderiv ℝ w z)) := by
      funext z
      exact fderiv_fun_neg
    rw [h1, fderiv_fun_neg]
  rw [hderiv] at h
  have h2 : ((fderiv ℝ (fderiv ℝ w) x)) v v = ⟪hessOp w x v, v⟫ :=
    (InnerProductSpace.continuousLinearMapOfBilin_apply (B := fderiv ℝ (fderiv ℝ w) x) v v).symm
  simp only [neg_apply, ContinuousLinearMap.neg_apply] at h
  linarith [h, h2.symm.le, h2.le]

/-- At a from-above contact point the Hessian of `w` is bounded below by `-(4 c'/c) b`:
`Submission.contact_bound_above_sigma2` applied to the perturbation. -/
theorem quadform_lower_of_mem_contactSetAbove {w : ℝ⁴ → ℝ} (hw : ContDiffOn ℝ 2 w (ball 0 (3 / 2)))
    {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hA1 : s2 A = 1) (htrA : 0 < trOp A)
    (heq : ∀ x ∈ ball 0 (3 / 2), s2 (A + hessOp w x) = 1)
    (hpos : ∀ x ∈ ball 0 (3 / 2), 0 < trOp (A + hessOp w x))
    {c c' b : ℝ} (hc : 0 < c) (hb : 0 ≤ b)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {B : Set ℝ⁴} {x : ℝ⁴} (hx : x ∈ contactSetAbove b w B) (v : ℝ⁴) :
    -(4 * c' / c) * b * ‖v‖ ^ 2 ≤ ⟪hessOp w x v, v⟫ := by
  have hxball : x ∈ ball 0 1 :=
    mem_ball_of_mem_closedBall_half (contactSetAbove_subset_closedBall hx)
  have hx3 : x ∈ ball 0 (3 / 2) := by
    rw [mem_ball] at hxball ⊢; linarith
  have hsymm : (hessOp w x).IsSymmetric :=
    Commons.Analysis.Calculus.FDeriv.isSymmetric_hessian isOpen_ball hx3 hw
  have hMle : ∀ v : ℝ⁴, ⟪hessOp w x v, v⟫ ≤ b * ‖v‖ ^ 2 :=
    fun v => quadform_upper_of_mem_contactSetAbove hw hx v
  exact contact_bound_above_sigma2 hA hsymm hA1 (heq x hx3) htrA (hpos x hx3) hc hb
    hcq hcq' hMle v

/-- **The measure estimate for the contact set of paraboloids sliding from above.**

If `w` is `C²` on a neighbourhood of the unit ball, `A` is a fixed symmetric operator with
`s2 A = 1`, `trOp A > 0`, and `s2 (A + D²w) = 1` with `trOp (A + D²w) > 0` on `ball 0 (3/2)`, and if
`B` is a closed set inside `closedBall 0 (1/2)` all of whose points occur as vertices of from-above
contact paraboloids of opening `b` (with contact point inside `closedBall 0 (1/2)`), then the
contact set `A_b = contactSetAbove b w B` satisfies `|B| ≤ (1 + 4 c'/c)^4 |A_b|`, where
`c ≤ cofOp A ≤ c'` in the quadratic form sense. -/
theorem contactSetAbove_measure {w : ℝ⁴ → ℝ} (hw : ContDiffOn ℝ 2 w (ball 0 (3 / 2)))
    {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hA1 : s2 A = 1) (htrA : 0 < trOp A)
    (heq : ∀ x ∈ ball 0 (3 / 2), s2 (A + hessOp w x) = 1)
    (hpos : ∀ x ∈ ball 0 (3 / 2), 0 < trOp (A + hessOp w x))
    {c c' b : ℝ} (hc : 0 < c) (hb : 0 < b)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {B : Set ℝ⁴} (hB : IsClosed B)
    (hcontact : ∀ y ∈ B, ∃ x ∈ closedBall 0 (1 / 2),
      ∀ z ∈ closedBall 0 1,
        -w x + b / 2 * ‖x - y‖ ^ 2 ≤ -w z + b / 2 * ‖z - y‖ ^ 2) :
    volume B ≤ ENNReal.ofReal ((1 + 4 * c' / c) ^ 4) * volume (contactSetAbove b w B) := by
  set K : ℝ := 4 * c' / c with hKdef
  have hc'pos : 0 < c' := by
    have h1 := hcq (stdB4 0)
    have h2 := hcq' (stdB4 0)
    have h3 : ‖stdB4 0‖ = 1 := stdB4.orthonormal.1 0
    simp only [h3, one_pow, mul_one] at h1 h2
    linarith
  have hK : 0 ≤ K := by rw [hKdef]; exact div_nonneg (by linarith) hc.le
  have hsub : B ⊆ slideMapAbove b w '' contactSetAbove b w B :=
    subset_image_contactSetAbove (ne_of_gt hb) hw hcontact
  have hw1 : ContDiffOn ℝ 1 w (ball 0 1) :=
    (hw.of_le (m := 1) (by norm_num)).mono (ball_subset_ball (by norm_num))
  have hmeas : MeasurableSet (contactSetAbove b w B) := (isClosed_contactSetAbove hB hw1).measurableSet
  have hf' : ∀ x ∈ contactSetAbove b w B, HasFDerivWithinAt (slideMapAbove b w)
      ((1 : ℝ⁴ →L[ℝ] ℝ⁴) - b⁻¹ • hessOp w x) (contactSetAbove b w B) x := by
    intro x hx
    have hxball : x ∈ ball 0 1 :=
      mem_ball_of_mem_closedBall_half (contactSetAbove_subset_closedBall hx)
    have hx3 : x ∈ ball 0 (3 / 2) := by
      rw [mem_ball] at hxball ⊢; linarith
    exact (hasFDerivAt_slideMapAbove (hw.contDiffAt (isOpen_ball.mem_nhds hx3))).hasFDerivWithinAt
  have harea := MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv
    (μ := (volume : Measure ℝ⁴)) (f := slideMapAbove b w)
    (f' := fun x : ℝ⁴ => (1 : ℝ⁴ →L[ℝ] ℝ⁴) - b⁻¹ • hessOp w x) hmeas hf'
  have hbdd : ∀ x ∈ contactSetAbove b w B,
      ENNReal.ofReal |((1 : ℝ⁴ →L[ℝ] ℝ⁴) - b⁻¹ • hessOp w x).det|
        ≤ ENNReal.ofReal ((1 + K) ^ 4) := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal ?_
    have hxball : x ∈ ball 0 1 :=
      mem_ball_of_mem_closedBall_half (contactSetAbove_subset_closedBall hx)
    have hx3 : x ∈ ball 0 (3 / 2) := by
      rw [mem_ball] at hxball ⊢; linarith
    have hsymm : (hessOp w x).IsSymmetric :=
      Commons.Analysis.Calculus.FDeriv.isSymmetric_hessian isOpen_ball hx3 hw
    have hup := quadform_upper_of_mem_contactSetAbove hw hx
    have hlo := quadform_lower_of_mem_contactSetAbove hw hA hA1 htrA heq hpos hc hb.le hcq hcq' hx
    set S : ℝ⁴ →L[ℝ] ℝ⁴ := (1 : ℝ⁴ →L[ℝ] ℝ⁴) - b⁻¹ • hessOp w x with hSdef
    have hSsym : S.IsSymmetric := by
      rw [hSdef]
      exact LinearMap.IsSymmetric.sub LinearMap.IsSymmetric.one
        (LinearMap.IsSymmetric.smul (c := b⁻¹) (by simp) hsymm)
    have hS1 : ∀ v : ℝ⁴, 0 ≤ ⟪S v, v⟫ := by
      intro v
      have h := hup v
      rw [hSdef]
      simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      have h' : b⁻¹ * ⟪hessOp w x v, v⟫ ≤ ‖v‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hb))
        have h2 : b⁻¹ * (b * ‖v‖ ^ 2) = ‖v‖ ^ 2 := by field_simp
        linarith [h2]
      linarith
    have hS2 : ∀ v : ℝ⁴, ⟪S v, v⟫ ≤ (1 + K) * ‖v‖ ^ 2 := by
      intro v
      have h := hlo v
      rw [hSdef]
      simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      have h' : -(4 * c' / c * ‖v‖ ^ 2) ≤ b⁻¹ * ⟪hessOp w x v, v⟫ := by
        have hh : -(4 * c' / c * b * ‖v‖ ^ 2) ≤ ⟪hessOp w x v, v⟫ := by linarith [h]
        have hh2 := mul_le_mul_of_nonneg_left hh (le_of_lt (inv_pos.mpr hb))
        have h2 : b⁻¹ * (-(4 * c' / c * b * ‖v‖ ^ 2)) = -(4 * c' / c * ‖v‖ ^ 2) := by
          field_simp
        linarith [h2]
      linarith
    have hdet := Commons.Analysis.InnerProductSpace.abs_det_le_pow_of_quadform_bounds hSsym
      (by linarith : (0 : ℝ) ≤ 1 + K) hS1 hS2
    rwa [show Module.finrank ℝ ℝ⁴ = 4 from by simp] at hdet
  calc volume B ≤ volume (slideMapAbove b w '' contactSetAbove b w B) := measure_mono hsub
    _ ≤ ∫⁻ x in contactSetAbove b w B,
          ENNReal.ofReal |((1 : ℝ⁴ →L[ℝ] ℝ⁴) - b⁻¹ • hessOp w x).det| := harea
    _ ≤ ∫⁻ _x in contactSetAbove b w B, ENNReal.ofReal ((1 + K) ^ 4) :=
          setLIntegral_mono' hmeas hbdd
    _ = ENNReal.ofReal ((1 + K) ^ 4) * volume (contactSetAbove b w B) := setLIntegral_const _ _

end

end Submission
