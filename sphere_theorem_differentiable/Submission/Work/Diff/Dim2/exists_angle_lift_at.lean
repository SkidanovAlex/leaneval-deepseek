import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.Azim
import Submission.Work.Diff.Dim2.azimuth
import Submission.Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn_vec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

/-!
## A local smooth angle lift of a unit vector field

`Work.Diff.Dim2.exists_angle_lift_at`: if `u : M → ℝ²` is `C^∞` on an open set `N`, takes values in
the unit circle there, and has non-zero derivative at `x₀ ∈ N`, then near `x₀` it is the
`circPt`-image of a globally `C^∞` function `ϑ : M → ℝ` whose derivative at `x₀` is non-zero.

The route is:

* **globalise `u`.**  `Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn_vec` produces a
  *globally* `C^∞` `u'` agreeing with `u` near `x₀`.  (This is needed because `ContMDiffOn ∞`
  only gives `C^k` on a neighbourhood for each `k`, not `C^∞` on one neighbourhood.)
* **write down the lift on a neighbourhood of `x₀`.**  With `z₀ := toC (u' x₀) ≠ 0`,
  `ϑloc y := Im (log z₀) + Im (log (toC (u' y) / z₀))` is smooth wherever `toC (u' y)/z₀` lies
  in the slit plane, an open neighbourhood of `x₀`; and on the unit circle it is a lift:
  `circPt (ϑloc y) = u' y`.  The latter is `circPt_log_div` below (for a unit complex number `ζ`,
  `exp (Im (log ζ) * I) = ζ`).
* **globalise the lift** with `Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn`, and
  **compute the derivative** from the chain rule `mvfderiv_circPt_comp_apply`
  (`d (circPt ∘ ϑ) = (dϑ) • rot90 (circPt ∘ ϑ)` with `rot90 (circPt ·) ≠ 0`).
-/

/-- `mvfderiv` respects eventual equality (vector-valued version). -/
lemma mvfderiv_congr_of_eventuallyEq_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g₁ g₂ : M → F} {x : M} (h : g₁ =ᶠ[𝓝 x] g₂) :
    mvfderiv I g₁ x = mvfderiv I g₂ x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  ext v
  rfl

/-- A vanishing `mvfderiv` forces the corresponding `mfderiv` to vanish. -/
lemma mfderiv_eq_zero_of_mvfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → F} {x : M} (h : mvfderiv I f x = 0) :
    mfderiv I 𝓘(ℝ, F) f x = 0 := by
  ext v
  have h1 : mvfderiv I f x v = 0 := by rw [h]; rfl
  have h2 : (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)) (mfderiv I 𝓘(ℝ, F) f x v) = 0 := h1
  have h3 := congrArg (fun z => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).symm z) h2
  simpa using h3

/-- For a non-zero complex number of modulus one, `exp (i * Im (log z)) = z`. -/
lemma exp_im_log_mul_I {z : ℂ} (h : z ≠ 0) (h1 : ‖z‖ = 1) :
    Complex.exp (((Complex.log z).im : ℂ) * Complex.I) = z := by
  have hre : (Complex.log z).re = 0 := by rw [Complex.log_re, h1, Real.log_one]
  conv_rhs => rw [← Complex.exp_log h]
  congr 1
  conv_rhs => rw [← Complex.re_add_im (Complex.log z)]
  rw [hre, Complex.ofReal_zero, zero_add]

/-- **An angle lift of the unit complex number `z`, normalised by the unit number `z₀`.**

If `‖z₀‖ = ‖z‖ = 1`, then `Im (log z₀) + Im (log (z / z₀))` is an angle of `z`. -/
lemma circPt_log_div {z₀ z : ℂ} (hz₀ : ‖z₀‖ = 1) (hz : ‖z‖ = 1) :
    circPt ((Complex.log z₀).im + (Complex.log (z / z₀)).im) = ofC z := by
  have hz0 : z₀ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hz₀
    norm_num at hz₀
  have hz' : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hz
    norm_num at hz
  have hdiv : z / z₀ ≠ 0 := div_ne_zero hz' hz0
  have hdiv1 : ‖z / z₀‖ = 1 := by rw [norm_div, hz, hz₀, div_one]
  rw [← ofC_exp_I ((Complex.log z₀).im + (Complex.log (z / z₀)).im)]
  congr 1
  rw [show (((Complex.log z₀).im + (Complex.log (z / z₀)).im : ℝ) : ℂ) * Complex.I
      = ((Complex.log z₀).im : ℂ) * Complex.I + ((Complex.log (z / z₀)).im : ℂ) * Complex.I by
        push_cast; ring,
    Complex.exp_add, exp_im_log_mul_I hz0 hz₀, exp_im_log_mul_I hdiv hdiv1]
  exact mul_div_cancel₀ z hz0

theorem exists_angle_lift_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    {N : Set M} {u : M → EuclideanSpace ℝ (Fin 2)}
    (hN : IsOpen N)
    (hu : ContMDiffOn I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞ u N)
    (hu1 : ∀ x ∈ N, ‖u x‖ = 1)
    (huinj : ∀ x ∈ N, mfderiv I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) u x ≠ 0)
    {x₀ : M} (hx₀ : x₀ ∈ N) :
    ∃ ϑ : M → ℝ,
      ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ ϑ ∧
      (u =ᶠ[𝓝 x₀] fun y => Work.Diff.Dim2.circPt (ϑ y)) ∧
      mvfderiv I ϑ x₀ ≠ 0 := by
  classical
  -- ## 1.  A globally `C^∞` representative `u'` of `u` near `x₀`.
  obtain ⟨u', hu'sm, hu'eq⟩ :=
    Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn_vec
      (I := I) (U := N) (x := x₀) (Φ := u) (hN.mem_nhds hx₀) hu
  have hu'x : u' x₀ = u x₀ := hu'eq.eq_of_nhds
  have hu'x1 : ‖u' x₀‖ = 1 := by rw [hu'x]; exact hu1 x₀ hx₀
  -- ## 2.  The normalising unit complex number `z₀` and the constant `θ₀`
  set z₀ : ℂ := toC (u' x₀) with hz₀def
  have hz₀ : ‖z₀‖ = 1 := by rw [hz₀def, norm_toC]; exact hu'x1
  have hz₀ne : z₀ ≠ 0 := by
    rintro h
    rw [h, norm_zero] at hz₀
    norm_num at hz₀
  set θ₀ : ℝ := (Complex.log z₀).im with hθ₀def
  -- ## 3.  The open set on which the local formula is smooth
  have hToC : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun y : M => toC (u' y)) :=
    contDiff_toC.comp_contMDiff hu'sm
  have hdivg : ContDiff ℝ ∞ (fun w : ℂ => w / z₀) := by
    have h : ContDiff ℝ ∞ (fun w : ℂ => z₀⁻¹ * w) := contDiff_const.mul contDiff_id
    simpa [div_eq_mul_inv, mul_comm] using h
  have hdiv : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun y : M => toC (u' y) / z₀) :=
    hdivg.comp_contMDiff hToC
  have hVcont : Continuous (fun y : M => toC (u' y) / z₀) := hdiv.continuous
  set V : Set M := {y : M | toC (u' y) / z₀ ∈ Complex.slitPlane} with hVdef
  have hVopen : IsOpen V := Complex.isOpen_slitPlane.preimage hVcont
  have hx₀V : x₀ ∈ V := by
    show toC (u' x₀) / z₀ ∈ Complex.slitPlane
    rw [hz₀def, div_self hz₀ne]
    exact Complex.one_mem_slitPlane
  -- ## 4.  The local lift is `C^∞` on `V`
  have hlogOn : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ Complex.log Complex.slitPlane :=
    fun z hz => (((Complex.contDiffAt_log hz).restrict_scalars ℝ).contMDiffAt).contMDiffWithinAt
  have hlog : ContMDiffOn I 𝓘(ℝ, ℂ) ∞
      (fun y : M => Complex.log (toC (u' y) / z₀)) V :=
    hlogOn.comp hdiv.contMDiffOn (fun y hy => hy)
  have himCLM : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun z : ℂ => z.im) Set.univ :=
    fun z _ => ((Complex.imCLM.contDiff.contDiffAt).contMDiffAt).contMDiffWithinAt
  have him : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y : M => (Complex.log (toC (u' y) / z₀)).im) V :=
    himCLM.comp hlog (fun y _ => Set.mem_univ _)
  have hϑloc : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y : M => θ₀ + (Complex.log (toC (u' y) / z₀)).im) V :=
    contMDiffOn_const.add him
  -- ## 5.  Globalise the lift
  obtain ⟨ϑ, hϑsm, hϑeq⟩ :=
    Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn
      (I := I) (U := V) (x := x₀)
      (F := fun y : M => θ₀ + (Complex.log (toC (u' y) / z₀)).im)
      (hVopen.mem_nhds hx₀V) hϑloc
  -- ## 6.  `u =ᶠ circPt ∘ ϑ` near `x₀`
  have hW1 : ∀ᶠ y in 𝓝 x₀, ‖u' y‖ = 1 := by
    filter_upwards [hu'eq, hN.mem_nhds hx₀] with y hy hNy
    rw [hy]
    exact hu1 y hNy
  have hucirc : u =ᶠ[𝓝 x₀] fun y => Work.Diff.Dim2.circPt (ϑ y) := by
    have hkey : ∀ᶠ y in 𝓝 x₀, Work.Diff.Dim2.circPt (ϑ y) = u y := by
      filter_upwards [hϑeq, hW1, hu'eq] with y hy hy1 hz
      rw [hy, ← hz]
      have h := circPt_log_div (z₀ := z₀) (z := toC (u' y)) hz₀
        (by rw [norm_toC]; exact hy1)
      simpa [hθ₀def, ofC_toC] using h
    filter_upwards [hkey] with y hy
    exact hy.symm
  refine ⟨ϑ, hϑsm, hucirc, ?_⟩
  -- ## 7.  Non-vanishing of the derivative
  intro hzero
  have hcomp0 : mvfderiv I (fun y : M => Work.Diff.Dim2.circPt (ϑ y)) x₀ = 0 := by
    ext v
    rw [Work.Diff.Dim2.mvfderiv_circPt_comp_apply (I := I) (M := M) (f := ϑ) (x := x₀)
      (hϑsm.mdifferentiableAt (by simp)) v]
    have hv : (NormedSpace.fromTangentSpace (𝕜 := ℝ) (ϑ x₀))
        (mfderiv I 𝓘(ℝ, ℝ) ϑ x₀ v) = mvfderiv I ϑ x₀ v := rfl
    rw [hv, hzero]
    simp
  have huzero : mvfderiv I u x₀ = 0 := by
    rw [mvfderiv_congr_of_eventuallyEq_aux (I := I) hucirc]
    exact hcomp0
  exact huinj x₀ hx₀ (mfderiv_eq_zero_of_mvfderiv_eq_zero (I := I) huzero)

end Work.Diff.Dim2
