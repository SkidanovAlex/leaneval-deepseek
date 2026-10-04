import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.mvfderiv_contMDiffAt
import Submission.Work.Diff.GE.smooth_onframe
import Submission.Work.Diff.L.Defs
import Submission.Work.OddBound.polygonValue.balancing.Instances
import Submission.ChartConnection
import Submission.ChartCurv
import Submission.GExpSmooth
import Submission.GExpRayIdent
import Submission.GExpTwoSided
import Submission.GExpVelocity
import Submission.CornerCut

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Gram pairing of two almost-`-f g` functions is `2ε`-Lipschitz along a geodesic ray

`Work.Diff.C.gram_along`: if two functions `f₁ f₂` satisfy `|Hess fᵢ + fᵢ·g| ≤ ε·g` at every point
of the unit-speed ray `t ↦ GExp q (t • u)`, if `|∇fᵢ| ≤ 1` along the ray, and if `0 ≤ s`, then

`|gp f₁ f₂ (GExp q (s • u)) − gp f₁ f₂ q| ≤ 2εs`,

where `gp F G x = ⟪∇F, ∇G⟫ + F·G`.  This is the "Gram matrix is almost constant" estimate of the
classical high-pinching sphere theorem (Step 3 of the classical endgame).

The proof is the computation

`d/dt gp(f₁,f₂)(γ t) = [rhess f₁ γ' ∇f₂ + f₁⟪γ',∇f₂⟫] + [rhess f₂ γ' ∇f₁ + f₂⟪γ',∇f₁⟫]`

(the first bracket is `⟨∇_{γ'}∇f₁, ∇f₂⟩ + f₁·(f₂∘γ)'` and the second is its mirror image), each
bracket being `≤ ε‖γ'‖·max ‖∇fᵢ‖ ≤ ε` by the Hessian hypothesis, together with the mean value
inequality.  The derivative computation is carried out in the chart at `γ t` using the chart form
of metric compatibility (`Submission.ChartConnection.hasDerivAt_chartGram`) and the chart formula
for `∇` of a section that is smooth at a point (`cov_eq_frameVector_coordFun_at`).  The one point
that is *not* a formal triviality is that `rgrad f` is a section that is `C^∞` at `x` as soon as
`f` is `C^∞` at `x` (`rgrad_contMDiffAt`), which is what makes the chart formula applicable to
`W = rgrad f`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic Submission.ChartCurv Submission.ChartConnection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The frame vector of the coordinates of a tangent vector is that tangent vector. -/
lemma frameVector_continuousLinearMapAt_of_mem {x₀ p : M} (hp : p ∈ (chartAt H x₀).source)
    (w : TangentSpace I p) :
    frameVector (I := I) x₀ p
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p w) = w := by
  show (trivializationAt E (TangentSpace I) x₀).symmL ℝ p
    ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p w) = w
  exact Trivialization.symmL_continuousLinearMapAt _ (R := ℝ)
    (by rwa [TangentBundle.trivializationAt_baseSet]) w

/-! ## Auxiliary: the Parseval expansion of a vector in an orthonormal frame -/

/-- In a finite-dimensional real inner product space, a vector is the sum of its coordinates in an
orthonormal basis. -/
lemma sum_inner_smul_eq_self_of_orthonormal {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] {f : ι → V}
    (hf : Orthonormal ℝ f) (hcard : Fintype.card ι = Module.finrank ℝ V) (v : V) :
    ∑ i, Inner.inner ℝ v (f i) • f i = v := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    have hfin : Module.finrank ℝ V = 0 := by
      rw [← hcard]
      exact Fintype.card_eq_zero
    have hsub : Subsingleton V := Module.finrank_zero_iff.mp hfin
    simp [Subsingleton.elim v 0]
  · haveI := hι
    let b : Module.Basis ι ℝ V := basisOfLinearIndependentOfCardEqFinrank hf.linearIndependent hcard
    have hb : (b : ι → V) = f := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    have hcoeff : ∀ i, Inner.inner ℝ v (f i) = b.repr v i := by
      intro i
      rw [← hb]
      conv_lhs => rw [← b.sum_repr v]
      rw [sum_inner, Finset.sum_eq_single i]
      · rw [inner_smul_left, hb, real_inner_self_eq_norm_sq, hf.1 i]
        simp
      · intro j _ hj
        rw [inner_smul_left, hb, hf.2 hj, mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    calc ∑ i, Inner.inner ℝ v (f i) • f i = ∑ i, b.repr v i • b i := by simp [hcoeff, hb]
      _ = v := b.sum_repr v

/-- An orthonormal frame of the ambient metric (in the sense of `IsONFrame` for the `SMet` of the
ambient instance) is an orthonormal family for the instance inner product. -/
lemma orthonormal_of_initSMet_frame {x : M}
    {f : Fin (Module.finrank ℝ E) → TangentSpace I x}
    (h : ∀ i j, Work.Diff.L.initSMet.inner x (f i) (f j) = if i = j then (1 : ℝ) else 0) :
    Orthonormal ℝ f := by
  constructor
  · intro i
    have h1 : Inner.inner ℝ (f i) (f i) = 1 := by
      rw [← Work.Diff.L.initSMet_inner, h i i, if_pos rfl]
    rw [norm_eq_sqrt_real_inner, h1, Real.sqrt_one]
  · intro i j hij
    rw [← Work.Diff.L.initSMet_inner, h i j, if_neg hij]

/-- The defining property of the gradient, read in the direction of a vector. -/
lemma inner_rgrad_eq_mvfderiv (F : M → ℝ) (x : M) (v : TangentSpace I x) :
    Inner.inner ℝ (rgrad (I := I) F x) v = mvfderiv I F x v := by
  rw [inner_rgrad]
  simp only [mvfderiv]
  rfl

/-! ## The gradient of a function that is smooth at a point is a smooth section there -/

/-- **Smoothness of the gradient section at a point.**  If `F` is `C^∞` at `x` in the pointwise
sense (`∀ m`, `F` is `C^m` on some neighbourhood of `x`), then `rgrad F` is a section that is
`C^∞` at `x` in the same pointwise sense.  (This is the pointwise form of
`Work.Diff.C.grad_smooth_of_smooth`; the *strong* form -- a globally smooth section agreeing with
`rgrad F` on a neighbourhood -- is false, see `Work.Diff.C.grad_smooth`.) -/
theorem rgrad_contMDiffAt {F : M → ℝ} {x : M} (hF : CMDiffAt ∞ F x) :
    CMDiffAt ∞ (T% (rgrad (I := I) F)) x := by
  obtain ⟨f, hON, hfsm⟩ := Work.Diff.GE.smooth_onframe (I := I) (M := M) Work.Diff.L.initSMet x
  have hscalar : ∀ i, CMDiffAt ∞ (fun y : M ↦ mvfderiv I F y (f y i)) x := fun i =>
    mvfderiv_contMDiffAt (I := I) (F := F) (X := fun y : M => f y i) (x := x) hF (hfsm i)
  have hterm : ∀ i, CMDiffAt ∞ (T% (fun y : M ↦ mvfderiv I F y (f y i) • f y i)) x := fun i =>
    (hscalar i).smul_section (hfsm i)
  have hsum : CMDiffAt ∞ (T% (fun y : M ↦ ∑ i, mvfderiv I F y (f y i) • f y i)) x :=
    ContMDiffAt.sum_section (fun i _ => hterm i)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hON] with y hy
  have horth : Orthonormal ℝ (fun i => f y i) :=
    orthonormal_of_initSMet_frame (fun i j => hy i j)
  have hvec : rgrad (I := I) F y = ∑ i, mvfderiv I F y (f y i) • f y i := by
    rw [← sum_inner_smul_eq_self_of_orthonormal horth (by rw [Fintype.card_fin]; rfl)
      (rgrad (I := I) F y)]
    exact Finset.sum_congr rfl (fun i _ => by rw [inner_rgrad_eq_mvfderiv])
  show (⟨y, rgrad (I := I) F y⟩ : TotalSpace E (TangentSpace I))
      = ⟨y, ∑ i, mvfderiv I F y (f y i) • f y i⟩
  rw [hvec]

/-! ## The coordinate function of a section that is smooth at a point -/

/-- **The coordinate function of a section that is `C^∞` at a point is `C^∞` there.** -/
theorem coordFun_contMDiffAt_of_section {W : Π x : M, TangentSpace I x} {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) (hW : CMDiffAt ∞ (T% W) x) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (coordFun x₀ W) x := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have h1 : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun q => ((trivializationAt E (TangentSpace I) x₀) ⟨q, W q⟩).2) x :=
    (Trivialization.contMDiffWithinAt_section (s := W) Set.univ hbase).1 hW
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hbase] with q hq
  rw [coordFun_apply]
  exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ (by simpa using hq) (W q)

/-! ## The chart formula for `∇` of a section that is smooth at a point -/

/-- **The chart formula for `∇` of a section that is `C^∞` at the base point.**  Local form of
`Submission.ChartCurv.cov_eq_frameVector_chartCoord`: the section `W` only needs to be smooth
*at* `p`, and the direction is an arbitrary tangent vector `w ∈ T_pM` (whose coordinates are the
chart coordinates of `w`). -/
theorem cov_eq_frameVector_coordFun_at
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    {W : Π x : M, TangentSpace I x} {c : M → E} {x₀ p : M}
    (hp : p ∈ (chartAt H x₀).source) (hW : CMDiffAt ∞ (T% W) p)
    (hc : ContMDiffAt I 𝓘(ℝ, E) ∞ c p)
    (heq : W =ᶠ[𝓝 p] fun q => frameVector (I := I) x₀ q (c q)) (w : TangentSpace I p) :
    cov W p w = frameVector (I := I) x₀ p
      (mvfderiv I c p w
        + chrB cov x₀ p (c p) ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p w)) := by
  classical
  have hframe : frameVector (I := I) x₀ p
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p w) = w :=
    frameVector_continuousLinearMapAt_of_mem hp w
  have hfr : (fun q : M => frameVector (I := I) x₀ q (c q))
      = (fun q : M => ∑ i, (Module.finBasis ℝ E).coord i (c q) •
          frameSection (I := I) x₀ (Module.finBasis ℝ E i) q) := by
    funext q
    show frameVector (I := I) x₀ q (c q)
      = ∑ i, (Module.finBasis ℝ E).coord i (c q) •
          frameSection (I := I) x₀ (Module.finBasis ℝ E i) q
    conv_lhs => rw [← sum_coord_smul_eq (E := E) (c q)]
    rw [frameVector_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (Module.finBasis ℝ E).coord i (c q) • frameVector (I := I) x₀ q (Module.finBasis ℝ E i)
      = (Module.finBasis ℝ E).coord i (c q) • frameSection (I := I) x₀ (Module.finBasis ℝ E i) q
    rw [show frameSection (I := I) x₀ (Module.finBasis ℝ E i) q
        = frameVector (I := I) x₀ q (Module.finBasis ℝ E i) from rfl]
  have hkey :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
    (cov := cov) Finset.univ
    (fun i (q : M) => (Module.finBasis ℝ E).coord i (c q))
    (fun i (q : M) => frameSection (I := I) x₀ (Module.finBasis ℝ E i) q)
    (Z := W) (x := p) (v := w) hW
    (fun i => contMDiffAt_frameSection (I := I) x₀ (Module.finBasis ℝ E i) hp)
    (fun i => (((Module.finBasis ℝ E).coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap).contMDiffAt.comp p hc)
    (heq.trans (Filter.Eventually.of_forall (fun q => congrFun hfr q)))
  rw [hkey]
  have hsum1 : (∑ i, (Module.finBasis ℝ E).coord i (c p) •
        cov (frameSection (I := I) x₀ (Module.finBasis ℝ E i)) p w)
      = frameVector (I := I) x₀ p (chrB cov x₀ p (c p)
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p w)) := by
    have h1 : ∀ i, cov (frameSection (I := I) x₀ (Module.finBasis ℝ E i)) p w
        = frameVector (I := I) x₀ p (christoffelEval cov x₀ p (Module.finBasis ℝ E i) w) :=
      fun i => cov_frameSection_eq cov x₀ p (Module.finBasis ℝ E i) w hp
    simp only [h1]
    rw [← frameVector_sum, ← christoffelEval_sum_left Finset.univ cov x₀ p
      (fun i => (Module.finBasis ℝ E).coord i (c p)) (fun i => Module.finBasis ℝ E i) w hp]
    congr 1
    rw [chrB_apply, hframe, sum_coord_smul_eq]
  have hsum2 : (∑ i, mvfderiv I (fun q : M => (Module.finBasis ℝ E).coord i (c q)) p w •
        frameSection (I := I) x₀ (Module.finBasis ℝ E i) p)
      = frameVector (I := I) x₀ p (mvfderiv I c p w) := by
    simp only [show ∀ i : Fin (Module.finrank ℝ E),
        frameSection (I := I) x₀ (Module.finBasis ℝ E i)
          = fun q => frameVector (I := I) x₀ q (Module.finBasis ℝ E i) from fun i => rfl]
    rw [← frameVector_sum, mvfderiv_eq_sum_coord (I := I) (hc.mdifferentiableAt (by simp))]
  rw [hsum1, hsum2, ← frameVector_add, add_comm]

/-! ## The chain rule along a curve, for real-valued functions -/

/-- The chain rule along a curve for a real-valued function. -/
lemma hasDerivAt_comp_curve_real {g : M → ℝ} {γ : ℝ → M} {t : ℝ}
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g (γ t)) (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    HasDerivAt (fun s => g (γ s)) (mvfderiv I g (γ t) (curveVelocity (I := I) γ t)) t := by
  have hcomp : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ℝ) (fun s => g (γ s)) t := hg.comp t hγ
  rw [mdifferentiableAt_iff_differentiableAt] at hcomp
  refine hcomp.hasDerivAt.congr_deriv ?_
  show deriv ((fun y : M => g y) ∘ γ) t = _
  rw [← Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) hg hγ]
  rfl

/-! ## The derivative of the Gram pairing along a curve -/

/-- Sum rule for `HasDerivAt`, stated with the pointwise sum as an explicit lambda (the pointwise
sum of functions is not the lambda; same issue as in `Submission.ChartConnection.hasDerivAt_mul_fun`). -/
theorem hasDerivAt_add_fun' {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun s => f s + g s) (f' + g') x := by
  have h := hf.add hg
  rwa [show (f + g) = fun s => f s + g s from by funext s; exact Pi.add_apply f g s] at h

/-- The derivative value of `t ↦ gp f₁ f₂ (γ t)`: the two "Hessian plus `f·g`" pieces. -/
noncomputable def gval (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (f₁ f₂ : M → ℝ) (γ : ℝ → M) (t : ℝ) : ℝ :=
  (rhess cov f₁ (γ t) (curveVelocity (I := I) γ t) (rgrad (I := I) f₂ (γ t))
      + f₁ (γ t) * Inner.inner ℝ (curveVelocity (I := I) γ t) (rgrad (I := I) f₂ (γ t)))
    + (rhess cov f₂ (γ t) (curveVelocity (I := I) γ t) (rgrad (I := I) f₁ (γ t))
      + f₂ (γ t) * Inner.inner ℝ (curveVelocity (I := I) γ t) (rgrad (I := I) f₁ (γ t)))

/-- **The derivative of the Gram pairing along a curve.**  If `γ` is differentiable at `t`,
`‖γ'(t)‖ = 1`, both `fᵢ` are `C^∞` at `γ t`, the Hessian bounds and the gradient bounds of the
statement `Work.Diff.C.gram_along` hold at the point `γ t`, then
`t ↦ gp f₁ f₂ (γ t)` has derivative `gval cov f₁ f₂ γ t`. -/
theorem gram_deriv_along
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    {hmet : IsMetricCompatible cov} {f₁ f₂ : M → ℝ} {ε : ℝ} {γ : ℝ → M} {t : ℝ}
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hvel : ‖curveVelocity (I := I) γ t‖ = 1)
    (hsm₁ : CMDiffAt ∞ f₁ (γ t)) (hsm₂ : CMDiffAt ∞ f₂ (γ t))
    (hH₁ : ∀ V W : TangentSpace I (γ t),
      |rhess cov f₁ (γ t) V W + f₁ (γ t) * Inner.inner ℝ V W| ≤ ε * ‖V‖ * ‖W‖)
    (hH₂ : ∀ V W : TangentSpace I (γ t),
      |rhess cov f₂ (γ t) V W + f₂ (γ t) * Inner.inner ℝ V W| ≤ ε * ‖V‖ * ‖W‖) :
    HasDerivAt (fun τ => gp (I := I) (M := M) f₁ f₂ (γ τ)) (gval cov f₁ f₂ γ t) t := by
  classical
  have hsrc : γ t ∈ (chartAt H (γ t)).source := mem_chart_source H (γ t)
  -- the gradient sections are smooth at `γ t`, and so are their coordinate functions
  have hW₁ : CMDiffAt ∞ (T% (rgrad (I := I) f₁)) (γ t) := rgrad_contMDiffAt hsm₁
  have hW₂ : CMDiffAt ∞ (T% (rgrad (I := I) f₂)) (γ t) := rgrad_contMDiffAt hsm₂
  have hc₁ : ContMDiffAt I 𝓘(ℝ, E) ∞ (coordFun (γ t) (rgrad (I := I) f₁)) (γ t) :=
    coordFun_contMDiffAt_of_section hsrc hW₁
  have hc₂ : ContMDiffAt I 𝓘(ℝ, E) ∞ (coordFun (γ t) (rgrad (I := I) f₂)) (γ t) :=
    coordFun_contMDiffAt_of_section hsrc hW₂
  have heq₁ : rgrad (I := I) f₁ =ᶠ[𝓝 (γ t)]
      fun q => frameVector (I := I) (γ t) q (coordFun (γ t) (rgrad (I := I) f₁) q) := by
    filter_upwards [(chartAt H (γ t)).open_source.mem_nhds hsrc] with q hq
    exact (frameVector_coordFun_eq (I := I) (x₀ := γ t) hq).symm
  have heq₂ : rgrad (I := I) f₂ =ᶠ[𝓝 (γ t)]
      fun q => frameVector (I := I) (γ t) q (coordFun (γ t) (rgrad (I := I) f₂) q) := by
    filter_upwards [(chartAt H (γ t)).open_source.mem_nhds hsrc] with q hq
    exact (frameVector_coordFun_eq (I := I) (x₀ := γ t) hq).symm
  -- the chart formula for `∇` of the two gradient sections, in the direction `γ'(t)`
  have hcov₁ : cov (rgrad (I := I) f₁) (γ t) (curveVelocity (I := I) γ t)
      = frameVector (I := I) (γ t) (γ t)
          (mvfderiv I (coordFun (γ t) (rgrad (I := I) f₁)) (γ t) (curveVelocity (I := I) γ t)
            + christoffelEval cov (γ t) (γ t) (coordFun (γ t) (rgrad (I := I) f₁) (γ t))
                (curveVelocity (I := I) γ t)) := by
    rw [cov_eq_frameVector_coordFun_at (cov := cov) (x₀ := γ t) (p := γ t) hsrc hW₁ hc₁ heq₁
      (curveVelocity (I := I) γ t), chrB_apply, frameVector_continuousLinearMapAt_of_mem hsrc]
  have hcov₂ : cov (rgrad (I := I) f₂) (γ t) (curveVelocity (I := I) γ t)
      = frameVector (I := I) (γ t) (γ t)
          (mvfderiv I (coordFun (γ t) (rgrad (I := I) f₂)) (γ t) (curveVelocity (I := I) γ t)
            + christoffelEval cov (γ t) (γ t) (coordFun (γ t) (rgrad (I := I) f₂) (γ t))
                (curveVelocity (I := I) γ t)) := by
    rw [cov_eq_frameVector_coordFun_at (cov := cov) (x₀ := γ t) (p := γ t) hsrc hW₂ hc₂ heq₂
      (curveVelocity (I := I) γ t), chrB_apply, frameVector_continuousLinearMapAt_of_mem hsrc]
  -- the coordinate curves along `γ`
  have ha₁ : HasDerivAt (fun τ => coordFun (γ t) (rgrad (I := I) f₁) (γ τ))
      (mvfderiv I (coordFun (γ t) (rgrad (I := I) f₁)) (γ t) (curveVelocity (I := I) γ t)) t :=
    hasDerivAt_comp_curve (g := coordFun (γ t) (rgrad (I := I) f₁))
      (hc₁.mdifferentiableAt (by simp)) hγmd
  have ha₂ : HasDerivAt (fun τ => coordFun (γ t) (rgrad (I := I) f₂) (γ τ))
      (mvfderiv I (coordFun (γ t) (rgrad (I := I) f₂)) (γ t) (curveVelocity (I := I) γ t)) t :=
    hasDerivAt_comp_curve (g := coordFun (γ t) (rgrad (I := I) f₂))
      (hc₂.mdifferentiableAt (by simp)) hγmd
  -- metric compatibility in the chart
  have hchart := hasDerivAt_chartGram (cov := cov) hmet (γ t) hγmd hsrc ha₁ ha₂
  -- its value is that of `d/dt ⟪∇f₁,∇f₂⟫`
  have hC₁ : chartGram (I := I) (γ t) (γ t)
        (mvfderiv I (coordFun (γ t) (rgrad (I := I) f₁)) (γ t) (curveVelocity (I := I) γ t)
          + christoffelEval cov (γ t) (γ t) (coordFun (γ t) (rgrad (I := I) f₁) (γ t))
              (curveVelocity (I := I) γ t))
        (coordFun (γ t) (rgrad (I := I) f₂) (γ t))
      = Inner.inner ℝ (cov (rgrad (I := I) f₁) (γ t) (curveVelocity (I := I) γ t))
          (rgrad (I := I) f₂ (γ t)) := by
    rw [chartGram_apply, ← hcov₁, frameVector_coordFun_eq (I := I) (x₀ := γ t) hsrc]
  have hC₂ : chartGram (I := I) (γ t) (γ t) (coordFun (γ t) (rgrad (I := I) f₁) (γ t))
        (mvfderiv I (coordFun (γ t) (rgrad (I := I) f₂)) (γ t) (curveVelocity (I := I) γ t)
          + christoffelEval cov (γ t) (γ t) (coordFun (γ t) (rgrad (I := I) f₂) (γ t))
              (curveVelocity (I := I) γ t))
      = Inner.inner ℝ (rgrad (I := I) f₁ (γ t))
          (cov (rgrad (I := I) f₂) (γ t) (curveVelocity (I := I) γ t)) := by
    rw [chartGram_apply, ← hcov₂, frameVector_coordFun_eq (I := I) (x₀ := γ t) hsrc]
  have hpair : HasDerivAt
      (fun τ => Inner.inner ℝ (rgrad (I := I) f₁ (γ τ)) (rgrad (I := I) f₂ (γ τ)))
      (Inner.inner ℝ (cov (rgrad (I := I) f₁) (γ t) (curveVelocity (I := I) γ t))
          (rgrad (I := I) f₂ (γ t))
        + Inner.inner ℝ (rgrad (I := I) f₁ (γ t))
            (cov (rgrad (I := I) f₂) (γ t) (curveVelocity (I := I) γ t))) t := by
    have h1 : HasDerivAt
        (fun s => chartGram (I := I) (γ t) (γ s)
          (coordFun (γ t) (rgrad (I := I) f₁) (γ s))
          (coordFun (γ t) (rgrad (I := I) f₂) (γ s)))
        (Inner.inner ℝ (cov (rgrad (I := I) f₁) (γ t) (curveVelocity (I := I) γ t))
            (rgrad (I := I) f₂ (γ t))
          + Inner.inner ℝ (rgrad (I := I) f₁ (γ t))
              (cov (rgrad (I := I) f₂) (γ t) (curveVelocity (I := I) γ t))) t :=
      hchart.congr_deriv (by rw [hC₁, hC₂])
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hγmd.continuousAt.preimage_mem_nhds
      ((chartAt H (γ t)).open_source.mem_nhds hsrc)] with τ hτ
    rw [chartGram_apply]
    simp only [frameVector_coordFun_eq (I := I) (x₀ := γ t) (W := rgrad (I := I) f₂) hτ,
      frameVector_coordFun_eq (I := I) (x₀ := γ t) (W := rgrad (I := I) f₁) hτ]
  -- the product term
  have hp₁ : HasDerivAt (fun τ => f₁ (γ τ))
      (Inner.inner ℝ (rgrad (I := I) f₁ (γ t)) (curveVelocity (I := I) γ t)) t :=
    (hasDerivAt_comp_curve_real (hsm₁.mdifferentiableAt (by simp)) hγmd).congr_deriv
      (inner_rgrad (I := I) f₁ (γ t) (curveVelocity (I := I) γ t)).symm
  have hp₂ : HasDerivAt (fun τ => f₂ (γ τ))
      (Inner.inner ℝ (rgrad (I := I) f₂ (γ t)) (curveVelocity (I := I) γ t)) t :=
    (hasDerivAt_comp_curve_real (hsm₂.mdifferentiableAt (by simp)) hγmd).congr_deriv
      (inner_rgrad (I := I) f₂ (γ t) (curveVelocity (I := I) γ t)).symm
  have hprod' : HasDerivAt (fun τ => f₁ (γ τ) * f₂ (γ τ))
      (Inner.inner ℝ (rgrad (I := I) f₁ (γ t)) (curveVelocity (I := I) γ t) * f₂ (γ t)
        + f₁ (γ t) * Inner.inner ℝ (rgrad (I := I) f₂ (γ t)) (curveVelocity (I := I) γ t)) t :=
    hasDerivAt_mul_fun hp₁ hp₂
  -- assemble
  have hsum := hasDerivAt_add_fun' hpair hprod'
  have hval : (Inner.inner ℝ (cov (rgrad (I := I) f₁) (γ t) (curveVelocity (I := I) γ t))
          (rgrad (I := I) f₂ (γ t))
        + Inner.inner ℝ (rgrad (I := I) f₁ (γ t))
            (cov (rgrad (I := I) f₂) (γ t) (curveVelocity (I := I) γ t)))
      + (Inner.inner ℝ (rgrad (I := I) f₁ (γ t)) (curveVelocity (I := I) γ t) * f₂ (γ t)
        + f₁ (γ t) * Inner.inner ℝ (rgrad (I := I) f₂ (γ t)) (curveVelocity (I := I) γ t))
      = gval cov f₁ f₂ γ t := by
    simp only [gval, rhess]
    rw [real_inner_comm (rgrad (I := I) f₁ (γ t)) (curveVelocity (I := I) γ t),
      real_inner_comm (rgrad (I := I) f₂ (γ t)) (curveVelocity (I := I) γ t),
      real_inner_comm (rgrad (I := I) f₁ (γ t))
        (cov (rgrad (I := I) f₂) (γ t) (curveVelocity (I := I) γ t))]
    ring
  rw [hval] at hsum
  simpa only [gp] using hsum

/-- **The bound on the derivative value.**  With `‖γ'(t)‖ = 1`, `|∇fᵢ| ≤ 1` and the Hessian
bounds at `γ t`, the derivative `gval cov f₁ f₂ γ t` is bounded by `2ε`. -/
theorem gram_deriv_bound
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {f₁ f₂ : M → ℝ} {ε : ℝ} {γ : ℝ → M} {t : ℝ}
    (hε : 0 ≤ ε) (hvel : ‖curveVelocity (I := I) γ t‖ = 1)
    (hH₁ : ∀ V W : TangentSpace I (γ t),
      |rhess cov f₁ (γ t) V W + f₁ (γ t) * Inner.inner ℝ V W| ≤ ε * ‖V‖ * ‖W‖)
    (hH₂ : ∀ V W : TangentSpace I (γ t),
      |rhess cov f₂ (γ t) V W + f₂ (γ t) * Inner.inner ℝ V W| ≤ ε * ‖V‖ * ‖W‖)
    (hg₁ : Inner.inner ℝ (rgrad (I := I) f₁ (γ t)) (rgrad (I := I) f₁ (γ t)) ≤ 1)
    (hg₂ : Inner.inner ℝ (rgrad (I := I) f₂ (γ t)) (rgrad (I := I) f₂ (γ t)) ≤ 1) :
    ‖gval cov f₁ f₂ γ t‖ ≤ 2 * ε := by
  have hn₁ : ‖rgrad (I := I) f₁ (γ t)‖ ≤ 1 := by
    have h2 : ‖rgrad (I := I) f₁ (γ t)‖ ^ 2 ≤ 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hg₁
    nlinarith [norm_nonneg (rgrad (I := I) f₁ (γ t))]
  have hn₂ : ‖rgrad (I := I) f₂ (γ t)‖ ≤ 1 := by
    have h2 : ‖rgrad (I := I) f₂ (γ t)‖ ^ 2 ≤ 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hg₂
    nlinarith [norm_nonneg (rgrad (I := I) f₂ (γ t))]
  have hA : |rhess cov f₁ (γ t) (curveVelocity (I := I) γ t) (rgrad (I := I) f₂ (γ t))
      + f₁ (γ t) * Inner.inner ℝ (curveVelocity (I := I) γ t) (rgrad (I := I) f₂ (γ t))| ≤ ε := by
    have h := hH₁ (curveVelocity (I := I) γ t) (rgrad (I := I) f₂ (γ t))
    rw [hvel, mul_one] at h
    exact le_trans h (by
      calc ε * ‖rgrad (I := I) f₂ (γ t)‖ ≤ ε * 1 := mul_le_mul_of_nonneg_left hn₂ hε
        _ = ε := mul_one ε)
  have hB : |rhess cov f₂ (γ t) (curveVelocity (I := I) γ t) (rgrad (I := I) f₁ (γ t))
      + f₂ (γ t) * Inner.inner ℝ (curveVelocity (I := I) γ t) (rgrad (I := I) f₁ (γ t))| ≤ ε := by
    have h := hH₂ (curveVelocity (I := I) γ t) (rgrad (I := I) f₁ (γ t))
    rw [hvel, mul_one] at h
    exact le_trans h (by
      calc ε * ‖rgrad (I := I) f₁ (γ t)‖ ≤ ε * 1 := mul_le_mul_of_nonneg_left hn₁ hε
        _ = ε := mul_one ε)
  rw [Real.norm_eq_abs, gval]
  exact le_trans (abs_add_le _ _) (by linarith [hA, hB])

theorem gram_along
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {f₁ f₂ : M → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    {u : TangentSpace I q} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hsm₁ : ∀ t ∈ Set.Icc (0 : ℝ) s,
      CMDiffAt ∞ f₁ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)))
    (hsm₂ : ∀ t ∈ Set.Icc (0 : ℝ) s,
      CMDiffAt ∞ f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)))
    (hH₁ : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ∀ V W : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)),
        |rhess cov f₁ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) V W
          + f₁ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))
            * Inner.inner ℝ V W| ≤ ε * ‖V‖ * ‖W‖)
    (hH₂ : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ∀ V W : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)),
        |rhess cov f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) V W
          + f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))
            * Inner.inner ℝ V W| ≤ ε * ‖V‖ * ‖W‖)
    (hg₁ : ∀ t ∈ Set.Icc (0 : ℝ) s,
      Inner.inner ℝ (rgrad (I := I) (M := M) f₁ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)))
        (rgrad (I := I) (M := M) f₁ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))) ≤ 1)
    (hg₂ : ∀ t ∈ Set.Icc (0 : ℝ) s,
      Inner.inner ℝ (rgrad (I := I) (M := M) f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)))
        (rgrad (I := I) (M := M) f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))) ≤ 1) :
    |gp (I := I) (M := M) f₁ f₂ (Submission.GlobalExp.GExp (cov := cov) hmet q (s • u))
        - gp (I := I) (M := M) f₁ f₂ q| ≤ 2 * ε * s  := by
  classical
  let γ : ℝ → M := fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (τ • u)
  have hu_ne : u ≠ 0 := by
    intro h0
    have h1 : (0 : ℝ) = 1 := by
      rw [h0] at hu
      simpa using hu
    exact one_ne_zero h1.symm
  have hu_norm : ‖u‖ = 1 := by
    have h2 : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hu]
    nlinarith [norm_nonneg u]
  have hγ0 : γ 0 = q := by
    show Submission.GlobalExp.GExp (cov := cov) hmet q ((0 : ℝ) • u) = q
    rw [zero_smul]
    exact Submission.GlobalExp.GExp_zero hmet q
  have hmd_pos : ∀ t : ℝ, 0 < t → MDifferentiableAt 𝓘(ℝ) I γ t := fun t ht =>
    Submission.GExpTwoSided.mdifferentiableAt_GExp_smul (cov := cov) hmet q hu_ne ht
  have hmd_zero : MDifferentiableAt 𝓘(ℝ) I γ 0 := by
    have hG : ContMDiffAt 𝓘(ℝ, E) I ∞
        (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet q (show TangentSpace I q from w))
        (0 : E) := Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet q 0
    have hlin : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun τ : ℝ => τ • (show E from u)) 0 :=
      (ContinuousLinearMap.toSpanSingleton ℝ (show E from u)).contMDiffAt
    have hG' : ContMDiffAt 𝓘(ℝ, E) I ∞
        (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet q (show TangentSpace I q from w))
        ((0 : ℝ) • (show E from u)) := by
      rw [zero_smul]
      exact hG
    have hcomp := ContMDiffAt.comp 0 hG' hlin
    simpa only [Function.comp_def] using hcomp.mdifferentiableAt (by simp)
  have hvel_pos : ∀ t : ℝ, 0 < t → ‖curveVelocity (I := I) γ t‖ = 1 := fun t ht => by
    have h1 : ‖curveVelocity (I := I)
        (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (τ • u)) t‖ = ‖u‖ :=
      Submission.GlobalExp.norm_curveVelocity_GExp_smul (cov := cov) hmet q hu_ne ht
    exact h1.trans hu_norm
  have hvel_zero : ‖curveVelocity (I := I) γ 0‖ = 1 := by
    rw [hγ0]
    have h2 : curveVelocity (I := I) γ 0 = u :=
      Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet q hu_ne
    rw [h2, hu_norm]
  have hderiv : ∀ t ∈ Set.Ico (0 : ℝ) s,
      HasDerivWithinAt (fun τ => gp (I := I) (M := M) f₁ f₂ (γ τ)) (gval cov f₁ f₂ γ t)
        (Set.Ici t) t := by
    intro t ht
    have hts : t ∈ Set.Icc (0 : ℝ) s := ⟨ht.1, le_of_lt ht.2⟩
    have hmd : MDifferentiableAt 𝓘(ℝ) I γ t := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h; exact hmd_zero
      · exact hmd_pos t h
    have hvel : ‖curveVelocity (I := I) γ t‖ = 1 := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h; exact hvel_zero
      · exact hvel_pos t h
    exact (gram_deriv_along (cov := cov) (hmet := hmet) (f₁ := f₁) (f₂ := f₂) (ε := ε)
      (γ := γ) (t := t) hmd hvel (hsm₁ t hts) (hsm₂ t hts) (hH₁ t hts) (hH₂ t hts)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) s, ‖gval cov f₁ f₂ γ t‖ ≤ 2 * ε := by
    intro t ht
    have hts : t ∈ Set.Icc (0 : ℝ) s := ⟨ht.1, le_of_lt ht.2⟩
    have hvel : ‖curveVelocity (I := I) γ t‖ = 1 := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h; exact hvel_zero
      · exact hvel_pos t h
    exact gram_deriv_bound (cov := cov) hε hvel
      (hH₁ t hts) (hH₂ t hts) (hg₁ t hts) (hg₂ t hts)
  have hcont : ContinuousOn (fun τ => gp (I := I) (M := M) f₁ f₂ (γ τ))
      (Set.Icc (0 : ℝ) s) := by
    intro t ht
    have hγc : ContinuousAt γ t := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h; exact hmd_zero.continuousAt
      · exact (hmd_pos t h).continuousAt
    have hW₁ : CMDiffAt ∞ (T% (rgrad (I := I) f₁)) (γ t) := rgrad_contMDiffAt (hsm₁ t ht)
    have hW₂ : CMDiffAt ∞ (T% (rgrad (I := I) f₂)) (γ t) := rgrad_contMDiffAt (hsm₂ t ht)
    have hinner : CMDiffAt ∞
        (fun y : M => Inner.inner ℝ (rgrad (I := I) f₁ y) (rgrad (I := I) f₂ y)) (γ t) :=
      ContMDiffAt.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hW₁ hW₂
    have hprod : CMDiffAt ∞ (fun y : M => f₁ y * f₂ y) (γ t) := (hsm₁ t ht).mul (hsm₂ t ht)
    have hgp : ContinuousAt (fun x : M => gp (I := I) (M := M) f₁ f₂ x) (γ t) := by
      have h : ContinuousAt
          ((fun y : M => Inner.inner ℝ (rgrad (I := I) f₁ y) (rgrad (I := I) f₂ y))
            + fun y : M => f₁ y * f₂ y) (γ t) := (hinner.add hprod).continuousAt
      refine h.congr ?_
      filter_upwards with y
      simp only [Pi.add_apply, gp]
    exact (hgp.comp hγc).continuousWithinAt
  have key := norm_image_sub_le_of_norm_deriv_right_le_segment
    (f := fun τ => gp (I := I) (M := M) f₁ f₂ (γ τ))
    (f' := fun t => gval cov f₁ f₂ γ t) (C := 2 * ε) hcont hderiv hbound s
    (right_mem_Icc.mpr hs0)
  rw [hγ0, sub_zero, Real.norm_eq_abs] at key
  exact key

end Work.Diff.C
