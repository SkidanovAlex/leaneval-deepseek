import Mathlib
import Submission.Work.Drive.rot90

/-!
# The manifold bridge: injective + `C^∞` in the `Circle.exp` parametrisation + non-vanishing
tangent implies smooth embedding

For `γ : Circle → ℝ × ℝ` which is continuous and injective, whose `Circle.exp`-parametrisation
`g t = γ (Circle.exp t)` is `C^∞` with nowhere vanishing derivative, we produce the two charts
needed to exhibit `γ` as a smooth embedding:

* on the source, the "angle" chart `y ↦ Im log (y / x)` (a local inverse of `Circle.exp`, written
  with `Complex.log` so that no smoothness of `Complex.arg` is needed);
* on the target, the straightening of the curve `z ↦ g (t₀ + z.1) + z.2 • rot90 (deriv g t₀)`
  (a local diffeomorphism of the plane, from the inverse function theorem).

Composed suitably, `γ` reads as the linear inclusion `u ↦ (u, 0)` in these charts.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Manifold

namespace Work.Drive.PolarTwist

noncomputable section

open scoped Classical

/-- The canonical linear isometry `ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1)`. -/
def eucOne : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-! ### Two logarithmic identities -/

/-- `exp (Im (log w)) = w / ‖w‖` for `w ≠ 0`. -/
lemma exp_im_log (w : ℂ) (hw : w ≠ 0) :
    Complex.exp ((Complex.log w).im * Complex.I) = w / (‖w‖ : ℂ) := by
  have h1 : Complex.exp ((Complex.log w).im * Complex.I)
      = Complex.exp (w.arg * Complex.I) := by rw [Complex.log_im]
  have hnorm : (↑‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
  rw [h1]
  rw [eq_div_iff hnorm, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I w

/-- A complex version of "multiplying `x` by the exponential of the angle of `y/x` gives `y`". -/
lemma mul_exp_im_log (x y : ℂ) (hx : x ≠ 0) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) :
    x * Complex.exp ((Complex.log (y / x)).im * Complex.I) = y := by
  have hy : y ≠ 0 := by
    intro h; rw [h] at hy1; norm_num at hy1
  have hw : y / x ≠ 0 := div_ne_zero hy hx
  rw [exp_im_log (y / x) hw]
  have hnorm : ‖y / x‖ = 1 := by rw [norm_div, hx1, hy1, div_one]
  simp only [hnorm, Complex.ofReal_one, div_one]
  exact mul_div_cancel₀ y hx

/-- The circle version: `x * Circle.exp (Im log (y/x)) = y`. -/
lemma mul_circleExp_im_log (x y : Circle) :
    x * Circle.exp ((Complex.log ((y : ℂ) / (x : ℂ))).im) = y := by
  refine Subtype.ext ?_
  rw [Circle.coe_mul, Circle.coe_exp]
  exact mul_exp_im_log (x : ℂ) (y : ℂ) (Circle.coe_ne_zero x) (Circle.norm_coe x)
    (Circle.norm_coe y)

/-- The angle of `Circle.exp t` relative to `Circle.exp t₀` is `t - t₀`, as long as
`|t - t₀| < π`. -/
lemma im_log_div_circleExp {t t₀ : ℝ} (h : |t - t₀| < Real.pi) :
    (Complex.log (((Circle.exp t : Circle) : ℂ) / ((Circle.exp t₀ : Circle) : ℂ))).im = t - t₀ := by
  have hquot : ((Circle.exp t : Circle) : ℂ) / ((Circle.exp t₀ : Circle) : ℂ)
      = Complex.exp ((↑(t - t₀) : ℂ) * Complex.I) := by
    rw [Circle.coe_exp, Circle.coe_exp, ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  rw [hquot, Complex.log_exp]
  · simp
  · have h1 : -(Real.pi) < t - t₀ := by
      have := neg_lt_of_abs_lt h; linarith
    simpa using h1
  · have h1 : t - t₀ ≤ Real.pi := by
      have := le_of_abs_le (le_of_lt h); linarith
    simpa using h1

/-! ### The angle chart of the circle -/

/-- The source arc `exp '' (t₀ - ε, t₀ + ε)` of the angle chart. -/
def expArc (t₀ ε : ℝ) : Set Circle := Circle.exp '' Set.Ioo (t₀ - ε) (t₀ + ε)

/-- The target `eucOne ⁻¹' (-ε, ε)` of the angle chart. -/
def expArcTarget (ε : ℝ) : Set (EuclideanSpace ℝ (Fin 1)) := eucOne.symm ⁻¹' Set.Ioo (-ε) ε

/-- The angle function `y ↦ Im log (y / exp t₀)` read in `ℝ¹ = EuclideanSpace ℝ (Fin 1)`. -/
def expAngle (t₀ : ℝ) : Circle → EuclideanSpace ℝ (Fin 1) :=
  fun y => eucOne ((Complex.log ((y : ℂ) / ((Circle.exp t₀ : Circle) : ℂ))).im)

/-- The inverse of the angle chart: `u ↦ exp (t₀ + u)`. -/
def expAngleInv (t₀ : ℝ) : EuclideanSpace ℝ (Fin 1) → Circle :=
  fun u => Circle.exp (t₀ + eucOne.symm u)

lemma expAngleInv_apply (t₀ : ℝ) (u : EuclideanSpace ℝ (Fin 1)) :
    expAngleInv t₀ u = Circle.exp (t₀ + eucOne.symm u) := rfl

/-- The arc `exp '' (t₀ - ε, t₀ + ε)` is open. -/
lemma isOpen_expArc (t₀ ε : ℝ) : IsOpen (expArc t₀ ε) :=
  isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo

/-- The target interval is open. -/
lemma isOpen_expArcTarget (ε : ℝ) : IsOpen (expArcTarget ε) :=
  isOpen_Ioo.preimage eucOne.symm.continuous

/-- Points of the source arc avoid the slitting of the plane: their `log` is smooth. -/
lemma expAngle_mem_slitPlane (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) {y : Circle}
    (hy : y ∈ expArc t₀ ε) :
    ((y : ℂ) / ((Circle.exp t₀ : Circle) : ℂ)) ∈ Complex.slitPlane := by
  obtain ⟨t, ht, rfl⟩ := hy
  have hlt : |t - t₀| < ε := by
    rw [abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hquot : ((Circle.exp t : Circle) : ℂ) / ((Circle.exp t₀ : Circle) : ℂ)
      = Complex.exp ((↑(t - t₀) : ℂ) * Complex.I) := by
    rw [Circle.coe_exp, Circle.coe_exp, ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  have hcos : 0 < Real.cos (t - t₀) := by
    have h2 : |t - t₀| < Real.pi / 2 := by
      have hpi : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
      linarith
    rw [abs_lt] at h2
    exact Real.cos_pos_of_mem_Ioo ⟨h2.1, h2.2⟩
  have hre : (Complex.exp ((↑(t - t₀) : ℂ) * Complex.I)).re = Real.cos (t - t₀) := by
    rw [Complex.exp_re]; simp
  rw [hquot]
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (hre ▸ hcos))

/-- The angle function is smooth on the source arc. -/
lemma contMDiffOn_expAngle (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ContMDiffOn (𝓡 1) (𝓡 1) ∞ (expAngle t₀) (expArc t₀ ε) := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) :=
    ⟨by simpa using Complex.finrank_real_complex⟩
  have hcoe : ContMDiffOn (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (fun y : Circle => (y : ℂ)) (expArc t₀ ε) :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞)).contMDiffOn
  have hdiv0 : ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞
      (fun z : ℂ => z / ((Circle.exp t₀ : Circle) : ℂ)) Set.univ :=
    contMDiffOn_iff_contDiffOn.mpr ((contDiff_id.div_const _).contDiffOn)
  have hdiv : ContMDiffOn (𝓡 1) (𝓘(ℝ, ℂ)) ∞
      (fun y : Circle => (y : ℂ) / ((Circle.exp t₀ : Circle) : ℂ)) (expArc t₀ ε) :=
    hdiv0.comp hcoe (fun y _ => Set.mem_univ _)
  have hlog : ContDiffOn ℝ ∞ Complex.log Complex.slitPlane :=
    Complex.isOpen_slitPlane.contDiffOn_iff.2
      (fun x hx => (Complex.contDiffAt_log hx).restrict_scalars ℝ)
  have hlogMD : ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ Complex.log Complex.slitPlane :=
    contMDiffOn_iff_contDiffOn.mpr hlog
  have hcomp := hlogMD.comp hdiv
    (fun y hy => expAngle_mem_slitPlane t₀ ε hε hε1 hy)
  have him : ContMDiffOn (𝓡 1) (𝓘(ℝ)) ∞
      (fun y : Circle => (Complex.log ((y : ℂ) / ((Circle.exp t₀ : Circle) : ℂ))).im)
      (expArc t₀ ε) :=
    (Complex.imCLM.contMDiff (n := ∞)).comp_contMDiffOn hcomp
  exact ((eucOne : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).contMDiff (n := ∞)).comp_contMDiffOn him

/-- The inverse of the angle chart is smooth (it is `Circle.exp` composed with an affine map). -/
lemma contMDiff_expAngleInv (t₀ : ℝ) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (expAngleInv t₀) := by
  have h1 : ContMDiff (𝓡 1) (𝓘(ℝ)) ∞ (fun u : EuclideanSpace ℝ (Fin 1) => eucOne.symm u) :=
    (eucOne.symm : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contMDiff (n := ∞)
  have h2 : ContMDiff (𝓡 1) (𝓘(ℝ)) ∞ (fun u : EuclideanSpace ℝ (Fin 1) => t₀ + eucOne.symm u) :=
    contMDiff_const.add h1
  exact (contMDiff_circleExp (m := ∞)).comp h2

/-- The angle function maps the source arc into the target interval. -/
lemma expAngle_mapsTo (t₀ ε : ℝ) (_hε : 0 < ε) (hε1 : ε ≤ 1) :
    Set.MapsTo (expAngle t₀) (expArc t₀ ε) (expArcTarget ε) := by
  rintro y ⟨t, ht, rfl⟩
  have hlt : |t - t₀| < ε := by
    rw [abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  simp only [expArcTarget, Set.mem_preimage, expAngle, Set.mem_Ioo]
  rw [ContinuousLinearEquiv.symm_apply_apply, im_log_div_circleExp (by linarith)]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The inverse of the angle function maps the target interval into the source arc. -/
lemma expAngleInv_mapsTo (t₀ ε : ℝ) :
    Set.MapsTo (expAngleInv t₀) (expArcTarget ε) (expArc t₀ ε) := by
  rintro u hu
  simp only [expArcTarget, Set.mem_preimage, Set.mem_Ioo] at hu
  exact ⟨t₀ + eucOne.symm u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, expAngleInv_apply t₀ u⟩

/-- `expAngleInv` is a left inverse of `expAngle` on the source arc. -/
lemma expAngle_leftInvOn (t₀ ε : ℝ) :
    Set.LeftInvOn (expAngleInv t₀) (expAngle t₀) (expArc t₀ ε) := by
  rintro y ⟨t, ht, rfl⟩
  simp only [expAngle, expAngleInv, ContinuousLinearEquiv.symm_apply_apply, Circle.exp_add]
  exact mul_circleExp_im_log (Circle.exp t₀) (Circle.exp t)

/-- `expAngleInv` is a right inverse of `expAngle` on the target interval. -/
lemma expAngle_rightInvOn (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Set.RightInvOn (expAngleInv t₀) (expAngle t₀) (expArcTarget ε) := by
  rintro u hu
  simp only [expArcTarget, Set.mem_preimage, Set.mem_Ioo] at hu
  have hlt : |eucOne.symm u| < Real.pi := by
    have h1 : |eucOne.symm u| < ε := by
      rw [abs_lt]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    linarith
  simp only [expAngle, expAngleInv]
  rw [im_log_div_circleExp (t := t₀ + eucOne.symm u) (t₀ := t₀) (by
    rw [add_sub_cancel_left]; exact hlt)]
  rw [show t₀ + eucOne.symm u - t₀ = eucOne.symm u by ring,
    ContinuousLinearEquiv.apply_symm_apply]

/-- **The angle chart of the circle.**  Around `Circle.exp t₀` it is the local inverse of
`Circle.exp`, rescaled to the interval `(-ε, ε)`. -/
def expChart (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    OpenPartialHomeomorph Circle (EuclideanSpace ℝ (Fin 1)) where
  toFun := expAngle t₀
  invFun := expAngleInv t₀
  source := expArc t₀ ε
  target := expArcTarget ε
  map_source' := expAngle_mapsTo t₀ ε hε hε1

  map_target' := expAngleInv_mapsTo t₀ ε
  left_inv' := expAngle_leftInvOn t₀ ε
  right_inv' := expAngle_rightInvOn t₀ ε hε hε1
  continuousOn_toFun := (contMDiffOn_expAngle t₀ ε hε hε1).continuousOn
  continuousOn_invFun := (contMDiff_expAngleInv t₀).contMDiffOn.continuousOn
  open_source := isOpen_expArc t₀ ε
  open_target := isOpen_expArcTarget ε

lemma expChart_coe (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ⇑(expChart t₀ ε hε hε1) = expAngle t₀ := rfl

lemma expChart_symm_coe (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ⇑(expChart t₀ ε hε hε1).symm = expAngleInv t₀ := rfl

lemma expChart_source (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (expChart t₀ ε hε hε1).source = expArc t₀ ε := rfl

lemma expChart_target (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (expChart t₀ ε hε hε1).target = expArcTarget ε := rfl

lemma expChart_symm_apply (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (u : EuclideanSpace ℝ (Fin 1)) :
    (expChart t₀ ε hε hε1).symm u = Circle.exp (t₀ + eucOne.symm u) := rfl

/-- The angle chart lies in the maximal atlas of the circle. -/
lemma expChart_mem_maximalAtlas (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    expChart t₀ ε hε hε1 ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle :=
  OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _
    (contMDiffOn_expAngle t₀ ε hε hε1)
    ((contMDiff_expAngleInv t₀).contMDiffOn)

/-- The base point of the angle chart. -/
lemma expChart_base_mem (t₀ ε : ℝ) (hε : 0 < ε) :
    Circle.exp t₀ ∈ expArc t₀ ε :=
  ⟨t₀, ⟨by linarith, by linarith⟩, rfl⟩

/-! ### The straightening chart of the plane -/

/-- The straightening map of the plane along the curve `g` at `t₀`: it sends the horizontal axis to
the curve and translates along the fixed normal direction `rot90 (g' t₀)`. -/
def straightenMap (g : ℝ → ℝ × ℝ) (t₀ : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun z => g (t₀ + z.1) + z.2 • rot90 (deriv g t₀)

/-- The derivative of the straightening map at `z`. -/
def straightenDeriv (g : ℝ → ℝ × ℝ) (t₀ : ℝ) (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.toSpanSingleton ℝ (deriv g (t₀ + z.1))).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (rot90 (deriv g t₀))

lemma straightenMap_fst_zero (g : ℝ → ℝ × ℝ) (t₀ s : ℝ) :
    straightenMap g t₀ (s, 0) = g (t₀ + s) := by
  simp [straightenMap]

lemma straightenMap_zero (g : ℝ → ℝ × ℝ) (t₀ : ℝ) :
    straightenMap g t₀ (0 : ℝ × ℝ) = g t₀ := by
  simp [straightenMap]

lemma straightenDeriv_apply (g : ℝ → ℝ × ℝ) (t₀ : ℝ) (z w : ℝ × ℝ) :
    straightenDeriv g t₀ z w = w.1 • deriv g (t₀ + z.1) + w.2 • rot90 (deriv g t₀) := by
  simp [straightenDeriv, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- The set of points where the derivative of the straightening map is invertible. -/
def straightenGood (g : ℝ → ℝ × ℝ) (t₀ : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 < (deriv g (t₀ + z.1)).1 * (deriv g t₀).1 + (deriv g (t₀ + z.1)).2 * (deriv g t₀).2}

lemma straightenGood_zero_mem {g : ℝ → ℝ × ℝ} {t₀ : ℝ} (hdg : deriv g t₀ ≠ 0) :
    (0 : ℝ × ℝ) ∈ straightenGood g t₀ := by
  rw [straightenGood, Set.mem_setOf_eq, show t₀ + (0 : ℝ × ℝ).1 = t₀ from by simp]
  have hne : (deriv g t₀).1 ≠ 0 ∨ (deriv g t₀).2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hdg (Prod.ext h.1 h.2)
  rcases hne with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (deriv g t₀).2]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (deriv g t₀).1]

lemma isOpen_straightenGood (g : ℝ → ℝ × ℝ) (t₀ : ℝ) (hg : ContDiff ℝ ∞ g) :
    IsOpen (straightenGood g t₀) := by
  have hd : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hcont : Continuous fun z : ℝ × ℝ =>
      (deriv g (t₀ + z.1)).1 * (deriv g t₀).1 + (deriv g (t₀ + z.1)).2 * (deriv g t₀).2 := by
    have h1 : Continuous fun z : ℝ × ℝ => deriv g (t₀ + z.1) :=
      hd.comp (continuous_const.add continuous_fst)
    exact (h1.fst.mul continuous_const).add (h1.snd.mul continuous_const)
  exact isOpen_lt continuous_const hcont

lemma contDiff_straightenMap (g : ℝ → ℝ × ℝ) (t₀ : ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (straightenMap g t₀) := by
  rw [show straightenMap g t₀ = fun z : ℝ × ℝ => g (t₀ + z.1) + z.2 • rot90 (deriv g t₀) from rfl]
  fun_prop

lemma hasFDerivAt_straightenMap_aux (g : ℝ → ℝ × ℝ) (t₀ : ℝ) (hg : ContDiff ℝ ∞ g)
    (z : ℝ × ℝ) :
    HasFDerivAt ((fun z : ℝ × ℝ => g (t₀ + z.1)) + fun z => z.2 • rot90 (deriv g t₀))
      (straightenDeriv g t₀ z) z := by
  have hgd : DifferentiableAt ℝ g (t₀ + z.1) := (hg.differentiable (by simp)).differentiableAt
  have hg' : HasFDerivAt g (ContinuousLinearMap.toSpanSingleton ℝ (deriv g (t₀ + z.1)))
      (t₀ + z.1) := hgd.hasDerivAt.hasFDerivAt
  have hfst : HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := z)
  have hinner : HasFDerivAt (fun z : ℝ × ℝ => t₀ + z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
    hfst.const_add t₀
  have h1 := hg'.comp z hinner
  have h2 : HasFDerivAt (fun z : ℝ × ℝ => z.2 • rot90 (deriv g t₀))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (rot90 (deriv g t₀))) z :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)
      (rot90 (deriv g t₀))).hasFDerivAt
  have h := h1.add h2
  simpa only [Function.comp_def, straightenDeriv] using h

lemma hasFDerivAt_straightenMap (g : ℝ → ℝ × ℝ) (t₀ : ℝ) (hg : ContDiff ℝ ∞ g)
    (z : ℝ × ℝ) : HasFDerivAt (straightenMap g t₀) (straightenDeriv g t₀ z) z := by
  have h := hasFDerivAt_straightenMap_aux g t₀ hg z
  change HasFDerivAt ((fun z : ℝ × ℝ => g (t₀ + z.1)) + fun z => z.2 • rot90 (deriv g t₀))
    (straightenDeriv g t₀ z) z
  exact h

lemma straightenDeriv_injective (g : ℝ → ℝ × ℝ) (t₀ : ℝ) (z : ℝ × ℝ)
    (h : (deriv g (t₀ + z.1)).1 * (deriv g t₀).1 + (deriv g (t₀ + z.1)).2 * (deriv g t₀).2 ≠ 0) :
    Function.Injective (straightenDeriv g t₀ z) := by
  intro u v huv
  have hzero : straightenDeriv g t₀ z (u - v) = 0 := by rw [map_sub, huv, sub_self]
  rw [straightenDeriv_apply] at hzero
  have h1 : (u - v).1 * (deriv g (t₀ + z.1)).1 + -((u - v).2 * (deriv g t₀).2) = 0 := by
    have := congrArg Prod.fst hzero
    simpa [Prod.smul_fst, Prod.smul_snd, rot90_fst, rot90_snd] using this
  have h2 : (u - v).1 * (deriv g (t₀ + z.1)).2 + (u - v).2 * (deriv g t₀).1 = 0 := by
    have := congrArg Prod.snd hzero
    simpa [Prod.smul_fst, Prod.smul_snd, rot90_fst, rot90_snd] using this
  have hc : (u - v).1 = 0 := by
    have key : (u - v).1 * ((deriv g (t₀ + z.1)).1 * (deriv g t₀).1 +
        (deriv g (t₀ + z.1)).2 * (deriv g t₀).2) = 0 := by
      linear_combination (deriv g t₀).1 * h1 + (deriv g t₀).2 * h2
    exact (mul_eq_zero.mp key).resolve_right h
  have hd : (u - v).2 = 0 := by
    have key : (u - v).2 * ((deriv g (t₀ + z.1)).1 * (deriv g t₀).1 +
        (deriv g (t₀ + z.1)).2 * (deriv g t₀).2) = 0 := by
      linear_combination (deriv g (t₀ + z.1)).1 * h2 + (-(deriv g (t₀ + z.1)).2) * h1
    exact (mul_eq_zero.mp key).resolve_right h
  have huv' : u - v = 0 := Prod.ext hc hd
  exact sub_eq_zero.mp huv'

/-- On the good set, the derivative of the straightening map is a linear equivalence. -/
noncomputable def straightenEquiv (g : ℝ → ℝ × ℝ) (t₀ : ℝ) (z : ℝ × ℝ)
    (h : (deriv g (t₀ + z.1)).1 * (deriv g t₀).1 + (deriv g (t₀ + z.1)).2 * (deriv g t₀).2 ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  have hinj : Function.Injective (straightenDeriv g t₀ z) := straightenDeriv_injective g t₀ z h
  have hker : (straightenDeriv g t₀ z).toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hsurj : Function.Surjective (straightenDeriv g t₀ z) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℝ) (V := ℝ × ℝ) (V₂ := ℝ × ℝ) rfl).mp hinj
  have hrange : (straightenDeriv g t₀ z).toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  ContinuousLinearEquiv.ofBijective (straightenDeriv g t₀ z) hker hrange

lemma straightenEquiv_coe (g : ℝ → ℝ × ℝ) (t₀ : ℝ) (z : ℝ × ℝ) (h) :
    ((straightenEquiv g t₀ z h : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) = straightenDeriv g t₀ z := rfl

/-- **The straightening chart.**  There is a chart of the plane at `g t₀` in which the curve becomes
the horizontal axis. -/
lemma exists_straightenChart (g : ℝ → ℝ × ℝ) (t₀ : ℝ) (hg : ContDiff ℝ ∞ g)
    (hdg : deriv g t₀ ≠ 0) :
    ∃ (ψ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (δ : ℝ), 0 < δ ∧
      ψ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℝ × ℝ)) ∞ (ℝ × ℝ) ∧
      g t₀ ∈ ψ.source ∧
      (∀ s : ℝ, |s| < δ → ψ (g (t₀ + s)) = (s, 0)) := by
  have hgood : IsOpen (straightenGood g t₀) := isOpen_straightenGood g t₀ hg
  have h0good : (0 : ℝ × ℝ) ∈ straightenGood g t₀ := straightenGood_zero_mem hdg
  have hcont : ContDiff ℝ ∞ (straightenMap g t₀) := contDiff_straightenMap g t₀ hg
  have hderiv0 : HasFDerivAt (straightenMap g t₀)
      ((straightenEquiv g t₀ 0 (ne_of_gt h0good) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) 0 :=
    hasFDerivAt_straightenMap g t₀ hg 0
  let Ψ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    ContDiffAt.toOpenPartialHomeomorph (straightenMap g t₀) hcont.contDiffAt hderiv0 (by simp)
  have hΨcoe : (Ψ : ℝ × ℝ → ℝ × ℝ) = straightenMap g t₀ :=
    ContDiffAt.toOpenPartialHomeomorph_coe _ _ _
  have hΨsrc : (0 : ℝ × ℝ) ∈ Ψ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _
  let Ψ' : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) := Ψ.restrOpen (straightenGood g t₀) hgood
  have hΨ'src : Ψ'.source = Ψ.source ∩ straightenGood g t₀ :=
    OpenPartialHomeomorph.restrOpen_source Ψ (straightenGood g t₀) hgood
  have hΨ'coe : (Ψ' : ℝ × ℝ → ℝ × ℝ) = straightenMap g t₀ := by
    rw [OpenPartialHomeomorph.coe_restrOpen, hΨcoe]
  have hΨ'tgt : Ψ'.target = Ψ.target ∩ Ψ.symm ⁻¹' straightenGood g t₀ := by
    have h1 : Ψ'.toPartialEquiv = Ψ.toPartialEquiv.restr (straightenGood g t₀) :=
      OpenPartialHomeomorph.restrOpen_toPartialEquiv Ψ (straightenGood g t₀) hgood
    calc Ψ'.target = (Ψ'.toPartialEquiv).target := rfl
      _ = (Ψ.toPartialEquiv.restr (straightenGood g t₀)).target := by rw [h1]
      _ = Ψ.target ∩ Ψ.symm ⁻¹' straightenGood g t₀ := PartialEquiv.restr_target _ _
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp (Ψ.open_source.mem_nhds hΨsrc)
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.mp (hgood.mem_nhds h0good)
  have hnorm : ∀ s : ℝ, ‖((s, 0) : ℝ × ℝ)‖ = |s| := by
    intro s
    simp
  refine ⟨Ψ'.symm, min r₁ r₂, lt_min hr₁ hr₂, ?_, ?_, ?_⟩
  · -- the chart lies in the maximal atlas
    refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
    · -- smoothness of `Ψ'.symm` on `Ψ'.target`
      rw [contMDiffOn_iff_contDiffOn]
      intro a ha
      have ha' : a ∈ Ψ'.target := ha
      rw [show (Ψ'.symm).source = Ψ'.target from rfl,
        contDiffWithinAt_iff_contDiffAt (Ψ'.open_target.mem_nhds ha')]
      have hmem : Ψ'.symm a ∈ straightenGood g t₀ :=
        (hΨ'tgt ▸ (show a ∈ Ψ'.target from ha)).2
      have hderiv : HasFDerivAt (Ψ' : ℝ × ℝ → ℝ × ℝ)
          ((straightenEquiv g t₀ (Ψ'.symm a) (ne_of_gt hmem) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
          (Ψ'.symm a) := by
        rw [hΨ'coe]
        exact hasFDerivAt_straightenMap g t₀ hg (Ψ'.symm a)
      exact Ψ'.contDiffAt_symm ha' hderiv (hcont.contDiffAt)
    · -- smoothness of the inverse of `Ψ'.symm`, which is `straightenMap g t₀`
      have hcoe : (⇑(Ψ'.symm).symm : ℝ × ℝ → ℝ × ℝ) = straightenMap g t₀ := by
        rw [show ((Ψ'.symm).symm : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) = Ψ' from
          OpenPartialHomeomorph.symm_symm _, hΨ'coe]
      rw [contMDiffOn_iff_contDiffOn, hcoe]
      exact hcont.contDiffOn
  · -- the base point lies in the source
    have h0mem : (0 : ℝ × ℝ) ∈ Ψ'.source := by
      rw [hΨ'src]; exact ⟨hΨsrc, h0good⟩
    have hmap : (Ψ' : ℝ × ℝ → ℝ × ℝ) 0 = g t₀ := by
      rw [hΨ'coe, straightenMap_zero]
    rw [show (Ψ'.symm).source = Ψ'.target from rfl, ← hmap]
    exact Ψ'.map_source h0mem
  · -- the curve is straightened
    intro s hs
    have hs1 : (s, 0) ∈ Ψ.source :=
      hball₁ (by
        rw [Metric.mem_ball, dist_zero_right, hnorm]
        exact lt_of_lt_of_le hs (min_le_left _ _))
    have hs2 : (s, 0) ∈ straightenGood g t₀ :=
      hball₂ (by
        rw [Metric.mem_ball, dist_zero_right, hnorm]
        exact lt_of_lt_of_le hs (min_le_right _ _))
    have hs' : (s, 0) ∈ Ψ'.source := by rw [hΨ'src]; exact ⟨hs1, hs2⟩
    show Ψ'.symm (g (t₀ + s)) = (s, 0)
    rw [← straightenMap_fst_zero g t₀ s, ← hΨ'coe]
    exact Ψ'.left_inv hs'

/-! ### Two bookkeeping lemmas for the extended angle chart -/

lemma expChart_extend_target (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((expChart t₀ ε hε hε1).extend (𝓡 1)).target = expArcTarget ε := by
  rw [OpenPartialHomeomorph.extend_target, expChart_target]
  simp only [modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe, Set.range_id,
    Set.preimage_id, Set.univ_inter, Set.inter_univ]

lemma expChart_extend_symm_apply (t₀ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (u : EuclideanSpace ℝ (Fin 1)) :
    ((expChart t₀ ε hε hε1).extend (𝓡 1)).symm u = Circle.exp (t₀ + eucOne.symm u) := by
  rw [OpenPartialHomeomorph.extend]
  rfl

/-- **The bridge.**  A continuous injective map `γ : Circle → ℝ × ℝ` whose `Circle.exp`-parametrisation
is `C^∞` with nowhere vanishing derivative is a smooth embedding. -/
theorem isSmoothEmbedding_of_injective_deriv_ne_zero (gamma : Circle → ℝ × ℝ)
    (hcont : Continuous gamma) (hinj : Function.Injective gamma)
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => gamma (Circle.exp t)))
    (hderiv : ∀ t : ℝ, deriv (fun u : ℝ => gamma (Circle.exp u)) t ≠ 0) :
    Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) gamma := by
  have hg : ContDiff ℝ ∞ (fun t : ℝ => gamma (Circle.exp t)) := hsmooth
  refine ⟨?_, ?_⟩
  · refine IsImmersionOfComplement.isImmersion (F := EuclideanSpace ℝ (Fin 1)) fun x => ?_
    obtain ⟨t₀, ht₀⟩ := Circle.exp_surjective x
    obtain ⟨ψ, δ, hδ, hψmem, hψbase, hψcurve⟩ :=
      exists_straightenChart (fun t : ℝ => gamma (Circle.exp t)) t₀ hg (hderiv t₀)
    have hε : 0 < min 1 δ := lt_min one_pos hδ
    have hε1 : min 1 δ ≤ 1 := min_le_left _ _
    refine IsImmersionAtOfComplement.mk_of_continuousAt (f := gamma) (x := x) hcont.continuousAt
      (eucOne.symm.prodCongr eucOne.symm) (expChart t₀ (min 1 δ) hε hε1) ψ ?_ ?_
      (expChart_mem_maximalAtlas t₀ (min 1 δ) hε hε1) hψmem ?_
    · exact ht₀ ▸ expChart_base_mem t₀ (min 1 δ) hε
    · exact congrArg gamma ht₀ ▸ hψbase
    · intro u hu
      have hu' : eucOne.symm u ∈ Set.Ioo (-(min 1 δ)) (min 1 δ) := by
        have hu'' := hu
        rw [expChart_extend_target t₀ (min 1 δ) hε hε1, expArcTarget,
          Set.mem_preimage] at hu''
        exact hu''
      have hs : |eucOne.symm u| < min 1 δ := abs_lt.mpr ⟨hu'.1, hu'.2⟩
      have hsd : |eucOne.symm u| < δ := lt_of_lt_of_le hs (min_le_right _ _)
      rw [Function.comp_apply, Function.comp_apply,
        expChart_extend_symm_apply t₀ (min 1 δ) hε hε1 u,
        OpenPartialHomeomorph.extend_coe]
      simp only [Function.comp_apply, modelWithCornersSelf_coe, id_eq]
      rw [hψcurve _ hsd]
      simp [ContinuousLinearEquiv.prodCongr_apply]
  · exact Topology.IsClosedEmbedding.isEmbedding
      (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont hinj
        (fun U hU => (hU.isCompact.image hcont).isClosed))

end

end Work.Drive.PolarTwist
