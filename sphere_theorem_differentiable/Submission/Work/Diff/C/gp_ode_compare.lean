import Mathlib
import Submission.Work.Diff.C.Lib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.mvfderiv_contMDiffAt
import Submission.Work.Diff.GE.smooth_onframe
import Submission.Work.Diff.L.Defs
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A port of `Work.Diff.C.ray_cos_compare` with no `Work.Diff.C.inner_rgrad_mvfderiv`

This module reproduces the Sturm comparison `Work.Diff.C.ray_cos_compare` for a smooth function `f`
along the geodesic ray `t ↦ exp_q (t • u)` (the target `Work.Diff.C.gp_ode_compare`), but RESTRICTS
the imports to modules that do not declare `Work.Diff.C.inner_rgrad_mvfderiv`.

`Work.Diff.C.inner_rgrad_mvfderiv` is declared (identically) in BOTH `Submission/Work/Diff/C/
grad_smooth.lean` (imported by `gram_along`) and `Submission/Work/Diff/C/grad_smoothAt.lean`
(imported by `ray_cos_compare`), so no module can import both, and `ray_cos_compare` cannot be
imported next to `gram_along` / `init_data`, which the target `Work.Diff.C.gram_pointwise2` needs.

Every auxiliary declaration is therefore re-proved here under a fresh `gpOde_` name:

* `gpOde_inner_rgrad_mvfderiv` -- the one-line Riesz fact `⟨∇F, v⟩ = dF(v)`;
* `gpOde_sum_inner_smul_eq_of_orthonormal`, `gpOde_orthonormal_of_initSMet_isONFrame`,
  `gpOde_grad_smoothAt` -- smoothness of the gradient (ports of the three lemmas and the main
  theorem of `Diff/C/grad_smoothAt.lean`);
* `gpOde_ode_compare` -- the scalar Sturm comparison `|φ'' + φ| ≤ ε ⇒ |φ - (φ₀ cos + φ'₀ sin)| ≤ εs`;
* `gpOde_mvfderiv_inner_local` -- the product rule for the metric pairing at a point, from
  metric compatibility (the pointwise strengthening of the frozen contract);
* `gpOde_hasDerivAt_secondDeriv_along_geodesic` -- the Hessian of `f` along a geodesic is the second
  derivative of the restriction;
* `gp_ode_compare` -- the assembly.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.GlobalExp Submission.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ## Ports of `Diff/C/grad_smoothAt.lean` (smoothness of the gradient) -/

/-- In a finite-dimensional real inner product space, an orthonormal family whose index type has
cardinality `finrank` expands every vector. -/
lemma gpOde_sum_inner_smul_eq_of_orthonormal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] {f : ι → V}
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

/-- The defining property of `rgrad`, in terms of `mvfderiv`. -/
lemma gpOde_inner_rgrad_mvfderiv (F : M → ℝ) (x : M) (v : TangentSpace I x) :
    Inner.inner ℝ (rgrad (I := I) F x) v = mvfderiv I F x v := by
  rw [inner_rgrad]
  simp only [mvfderiv]
  rfl

/-- `IsONFrame` for the ambient metric (`Work.Diff.L.initSMet`), read with the instance inner
product, is Mathlib's `Orthonormal`. -/
lemma gpOde_orthonormal_of_initSMet_isONFrame {x : M}
    {f : Fin (Module.finrank ℝ E) → TangentSpace I x}
    (h : IsONFrame (Work.Diff.L.initSMet (I := I) (M := M)) x f) :
    Orthonormal ℝ f := by
  constructor
  · intro i
    have h1 : Inner.inner ℝ (f i) (f i) = 1 := by
      rw [← Work.Diff.L.initSMet_inner, h i i, if_pos rfl]
    rw [norm_eq_sqrt_real_inner, h1, Real.sqrt_one]
  · intro i j hij
    rw [← Work.Diff.L.initSMet_inner, h i j, if_neg hij]

/-! ## The main theorem -/

open scoped Manifold ContDiff Bundle Topology in
theorem gpOde_grad_smoothAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {F : M → ℝ} {x : M} (hF : CMDiffAt ∞ F x) :
    CMDiffAt ∞ (T% (Work.Diff.C.rgrad (I := I) F)) x := by
  obtain ⟨f, hON, hfsm⟩ :=
    Work.Diff.GE.smooth_onframe (I := I) (M := M) (Work.Diff.L.initSMet (I := I) (M := M)) x
  -- the scalar coefficients `y ↦ dF_y (eᵢ(y))` are smooth at `x`, from the weak hypothesis
  have hscalar : ∀ i, CMDiffAt ∞ (fun y : M ↦ mvfderiv I F y (f y i)) x := fun i =>
    mvfderiv_contMDiffAt hF (hfsm i)
  have hterm : ∀ i, CMDiffAt ∞ (T% (fun y : M ↦ mvfderiv I F y (f y i) • f y i)) x := fun i =>
    (hscalar i).smul_section (hfsm i)
  have hsum : CMDiffAt ∞ (T% (fun y : M ↦ ∑ i, mvfderiv I F y (f y i) • f y i)) x :=
    ContMDiffAt.sum_section (fun i _ => hterm i)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hON] with y hy
  have horth : Orthonormal ℝ (fun i => f y i) := gpOde_orthonormal_of_initSMet_isONFrame hy
  have hvec : rgrad (I := I) F y = ∑ i, mvfderiv I F y (f y i) • f y i := by
    rw [← gpOde_sum_inner_smul_eq_of_orthonormal horth (by rw [Fintype.card_fin]; rfl)
      (rgrad (I := I) F y)]
    exact Finset.sum_congr rfl (fun i _ => by rw [gpOde_inner_rgrad_mvfderiv])
  show (⟨y, rgrad (I := I) F y⟩ : TotalSpace E (TangentSpace I))
      = ⟨y, ∑ i, mvfderiv I F y (f y i) • f y i⟩
  rw [hvec]


/-! ## The scalar oscillator comparison (Sturm) -/

/-- **Scalar model estimate.**  If `φ` is twice differentiable on `[0,s]` with second derivative
`φ''` satisfying `|φ'' + φ| ≤ ε`, then `φ` is within `ε·s` of the solution of `y'' + y = 0` with
the same initial data.  This is the Sturm comparison estimate used along a geodesic. -/
theorem gpOde_ode_compare {φ φ' φ'' : ℝ → ℝ} {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ (φ' t) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ' (φ'' t) t)
    (h3 : ∀ t ∈ Set.Icc (0 : ℝ) s, |φ'' t + φ t| ≤ ε) :
    |φ s - (φ 0 * Real.cos s + φ' 0 * Real.sin s)| ≤ ε * s := by
  set z : ℝ → ℝ := fun t => φ t - (φ 0 * Real.cos t + φ' 0 * Real.sin t) with hzdef
  set z' : ℝ → ℝ := fun t => φ' t + (φ 0 * Real.sin t - φ' 0 * Real.cos t) with hz'def
  set hh : ℝ → ℝ := fun t => φ'' t + φ t with hhdef
  have hz0 : z 0 = 0 := by simp [hzdef]
  have hz'0 : z' 0 = 0 := by simp [hz'def]
  have hdz : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt z (z' t) t := by
    intro t ht
    have hc : HasDerivAt (fun u : ℝ => φ 0 * Real.cos u + φ' 0 * Real.sin u)
        (φ 0 * (-Real.sin t) + φ' 0 * Real.cos t) t :=
      ((Real.hasDerivAt_cos t).const_mul (φ 0)).add ((Real.hasDerivAt_sin t).const_mul (φ' 0))
    have h := (h1 t ht).sub hc
    have heq : φ' t - (φ 0 * (-Real.sin t) + φ' 0 * Real.cos t) = z' t := by
      rw [hz'def]; ring
    rw [heq] at h
    exact h
  have hdz' : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt z' (hh t - z t) t := by
    intro t ht
    have hc : HasDerivAt (fun u : ℝ => φ 0 * Real.sin u - φ' 0 * Real.cos u)
        (φ 0 * Real.cos t - φ' 0 * (-Real.sin t)) t :=
      ((Real.hasDerivAt_sin t).const_mul (φ 0)).sub ((Real.hasDerivAt_cos t).const_mul (φ' 0))
    have h := (h2 t ht).add hc
    have heq : φ'' t + (φ 0 * Real.cos t - φ' 0 * (-Real.sin t)) = hh t - z t := by
      rw [hhdef, hzdef]; ring
    rw [heq] at h
    exact h
  set ζ : ℝ → ℂ := fun t => (z' t : ℂ) + Complex.I * (z t : ℂ) with hζdef
  set ξ : ℝ → ℂ := fun t => Complex.exp (-(t : ℂ) * Complex.I) * ζ t with hξdef
  have hdζ : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt ζ (Complex.I * ζ t + (hh t : ℂ)) t := by
    intro t ht
    have ha : HasDerivAt (fun u : ℝ => (z' u : ℂ)) ((hh t - z t : ℝ) : ℂ) t :=
      (hdz' t ht).ofReal_comp
    have hb : HasDerivAt (fun u : ℝ => (z u : ℂ)) ((z' t : ℝ) : ℂ) t := (hdz t ht).ofReal_comp
    have h := ha.add (hb.const_mul Complex.I)
    have heq : ((hh t - z t : ℝ) : ℂ) + Complex.I * ((z' t : ℝ) : ℂ)
        = Complex.I * ζ t + (hh t : ℂ) := by
      rw [hζdef]
      push_cast
      rw [mul_add, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [heq] at h
    exact h
  have hdξ : ∀ t ∈ Set.Icc (0 : ℝ) s,
      HasDerivAt ξ (Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ)) t := by
    intro t ht
    have hu : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have hlin : HasDerivAt (fun u : ℝ => -(u : ℂ) * Complex.I) (-Complex.I) t := by
      have h := (hu.neg).mul_const Complex.I
      simpa using h
    have hexp : HasDerivAt (fun u : ℝ => Complex.exp (-(u : ℂ) * Complex.I))
        (Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I)) t := hlin.cexp
    have h := hexp.mul (hdζ t ht)
    have heq : Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I) * ζ t
        + Complex.exp (-(t : ℂ) * Complex.I) * (Complex.I * ζ t + (hh t : ℂ))
        = Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ) := by
      ring
    rw [heq] at h
    exact h
  have hξ0 : ξ 0 = 0 := by
    simp [hξdef, hζdef, hz0, hz'0]
  have hbnd : ∀ t ∈ Set.Ico (0 : ℝ) s,
      ‖Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ)‖ ≤ ε := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) s := ⟨ht.1, le_of_lt ht.2⟩
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(t : ℂ) * Complex.I).re = 0 := by simp
    rw [hre, Real.exp_zero, one_mul]
    have h5 : ‖((hh t : ℝ) : ℂ)‖ = |hh t| := by simp
    rw [h5]
    exact h3 t ht'
  have hMVT : ‖ξ s - ξ 0‖ ≤ ε * (s - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := ξ)
      (f' := fun t => Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ))
      (fun t ht => (hdξ t ht).hasDerivWithinAt) hbnd s ⟨hs, le_rfl⟩
  rw [hξ0, sub_zero, sub_zero] at hMVT
  have hn1 : ‖ξ s‖ = ‖ζ s‖ := by
    rw [hξdef, norm_mul]
    have hn : ‖Complex.exp (-(s : ℂ) * Complex.I)‖ = 1 := by
      have hcast : (-(s : ℂ) * Complex.I) = ((-s : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hcast, Complex.norm_exp_ofReal_mul_I]
    rw [hn, one_mul]
  have hn2 : ‖(z s : ℂ)‖ ≤ ‖ζ s‖ := by
    have him : (ζ s).im = z s := by simp [hζdef]
    calc ‖(z s : ℂ)‖ = |z s| := by simp
      _ = |(ζ s).im| := by rw [him]
      _ ≤ ‖ζ s‖ := Complex.abs_im_le_norm _
  have hfin : |z s| ≤ ε * s := by
    rw [show |z s| = ‖(z s : ℂ)‖ by simp]
    linarith [hn2, hn1, hMVT]
  have hzval : z s = φ s - (φ 0 * Real.cos s + φ' 0 * Real.sin s) := rfl
  rwa [hzval] at hfin


/-! ## The product rule for the metric pairing at a point -/

theorem gpOde_mvfderiv_inner_local
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : IsMetricCompatible cov)
    {x : M} (X : Π x : M, TangentSpace I x)
    {σ τ : Π x : M, TangentSpace I x} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    mvfderiv I (fun y : M => Inner.inner ℝ (σ y) (τ y)) x (X x)
      = Inner.inner ℝ (cov σ x (X x)) (τ x) + Inner.inner ℝ (σ x) (cov τ x (X x)) := by
  have hinner : ∀ {σ τ : Π y : M, TangentSpace I y}, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y : M => Inner.inner ℝ (σ y) (τ y)) x :=
    fun hσ hτ => MDifferentiableAt.inner_bundle (F := E)
      (E := fun x : M => TangentSpace I x) (b := id) hσ hτ
  have hmul : ∀ {f g : M → ℝ}, MDiffAt f x → MDiffAt g x →
      mvfderiv I (fun y : M => f y * g y) x (X x)
        = f x * mvfderiv I g x (X x) + g x * mvfderiv I f x (X x) := by
    intro f g hf hg
    have h := mvfderiv_mul (I := I) (x := x) hf hg
    exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (X x)) h
  have hadd : ∀ {g g' : M → ℝ}, MDiffAt g x → MDiffAt g' x →
      mvfderiv I (fun y : M => g y + g' y) x (X x)
        = mvfderiv I g x (X x) + mvfderiv I g' x (X x) := by
    intro g g' hg hg'
    have h := mvfderiv_add (I := I) (x := x) hg hg'
    exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (X x)) h
  have hΦ₁ : ∀ τ : Π y : M, TangentSpace I y, MDiffAt (T% τ) x →
      TensorialAt I E (fun σ : Π y : M, TangentSpace I y =>
        mvfderiv I (fun y : M => Inner.inner ℝ (σ y) (τ y)) x (X x)
          - Inner.inner ℝ (cov σ x (X x)) (τ x)
          - Inner.inner ℝ (σ x) (cov τ x (X x))) x := by
    intro τ hτ
    constructor
    · intro f σ hf hσ
      have hfσ : MDiffAt (fun y : M => Inner.inner ℝ (σ y) (τ y)) x := hinner hσ hτ
      have hfun : (fun y : M => Inner.inner ℝ ((f • σ) y) (τ y))
          = (fun y : M => f y * Inner.inner ℝ (σ y) (τ y)) := by
        funext y; simp [inner_smul_left]
      have hcov : cov (f • σ) x (X x)
          = f x • cov σ x (X x) + (mvfderiv I f x (X x)) • σ x := by
        have h := cov.isCovariantDerivativeOn.leibniz (σ := σ) (g := f) hσ hf
        exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (X x)) h
      change mvfderiv I (fun y : M => Inner.inner ℝ ((f • σ) y) (τ y)) x (X x)
          - Inner.inner ℝ (cov (f • σ) x (X x)) (τ x)
          - Inner.inner ℝ ((f • σ) x) (cov τ x (X x))
        = f x * (mvfderiv I (fun y : M => Inner.inner ℝ (σ y) (τ y)) x (X x)
          - Inner.inner ℝ (cov σ x (X x)) (τ x)
          - Inner.inner ℝ (σ x) (cov τ x (X x)))
      rw [hfun, hmul hf hfσ, hcov, show (f • σ) x = f x • σ x from rfl]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, smul_eq_mul]
      ring
    · intro σ σ' hσ hσ'
      have h1 : MDiffAt (fun y : M => Inner.inner ℝ (σ y) (τ y)) x := hinner hσ hτ
      have h2 : MDiffAt (fun y : M => Inner.inner ℝ (σ' y) (τ y)) x := hinner hσ' hτ
      have hfun : (fun y : M => Inner.inner ℝ ((σ + σ') y) (τ y))
          = (fun y : M => Inner.inner ℝ (σ y) (τ y) + Inner.inner ℝ (σ' y) (τ y)) := by
        funext y; simp [inner_add_left]
      change mvfderiv I (fun y : M => Inner.inner ℝ ((σ + σ') y) (τ y)) x (X x)
          - Inner.inner ℝ (cov (σ + σ') x (X x)) (τ x)
          - Inner.inner ℝ ((σ + σ') x) (cov τ x (X x))
        = (mvfderiv I (fun y : M => Inner.inner ℝ (σ y) (τ y)) x (X x)
            - Inner.inner ℝ (cov σ x (X x)) (τ x)
            - Inner.inner ℝ (σ x) (cov τ x (X x)))
          + (mvfderiv I (fun y : M => Inner.inner ℝ (σ' y) (τ y)) x (X x)
            - Inner.inner ℝ (cov σ' x (X x)) (τ x)
            - Inner.inner ℝ (σ' x) (cov τ x (X x)))
      rw [hfun, hadd h1 h2, cov.isCovariantDerivativeOn.add hσ hσ']
      simp only [ContinuousLinearMap.add_apply, Pi.add_apply, inner_add_left, inner_add_right]
      ring
  have hΦ₂ : ∀ σ : Π y : M, TangentSpace I y, MDiffAt (T% σ) x →
      TensorialAt I E (fun τ : Π y : M, TangentSpace I y =>
        mvfderiv I (fun y : M => Inner.inner ℝ (σ y) (τ y)) x (X x)
          - Inner.inner ℝ (cov σ x (X x)) (τ x)
          - Inner.inner ℝ (σ x) (cov τ x (X x))) x := by
    intro σ hσ
    constructor
    · intro f τ hf hτ
      have hfτ : MDiffAt (fun y : M => Inner.inner ℝ (σ y) (τ y)) x := hinner hσ hτ
      have hfun : (fun y : M => Inner.inner ℝ (σ y) ((f • τ) y))
          = (fun y : M => f y * Inner.inner ℝ (σ y) (τ y)) := by
        funext y; simp [inner_smul_right]
      have hcov : cov (f • τ) x (X x)
          = f x • cov τ x (X x) + (mvfderiv I f x (X x)) • τ x := by
        have h := cov.isCovariantDerivativeOn.leibniz (σ := τ) (g := f) hτ hf
        exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (X x)) h
      change mvfderiv I (fun y : M => Inner.inner ℝ (σ y) ((f • τ) y)) x (X x)
          - Inner.inner ℝ (cov σ x (X x)) ((f • τ) x)
          - Inner.inner ℝ (σ x) (cov (f • τ) x (X x))
        = f x * (mvfderiv I (fun y : M => Inner.inner ℝ (σ y) (τ y)) x (X x)
          - Inner.inner ℝ (cov σ x (X x)) (τ x)
          - Inner.inner ℝ (σ x) (cov τ x (X x)))
      rw [hfun, hmul hf hfτ, hcov, show (f • τ) x = f x • τ x from rfl]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, smul_eq_mul]
      ring
    · intro τ τ' hτ hτ'
      have h1 : MDiffAt (fun y : M => Inner.inner ℝ (σ y) (τ y)) x := hinner hσ hτ
      have h2 : MDiffAt (fun y : M => Inner.inner ℝ (σ y) (τ' y)) x := hinner hσ hτ'
      have hfun : (fun y : M => Inner.inner ℝ (σ y) ((τ + τ') y))
          = (fun y : M => Inner.inner ℝ (σ y) (τ y) + Inner.inner ℝ (σ y) (τ' y)) := by
        funext y; simp [inner_add_right]
      change mvfderiv I (fun y : M => Inner.inner ℝ (σ y) ((τ + τ') y)) x (X x)
          - Inner.inner ℝ (cov σ x (X x)) ((τ + τ') x)
          - Inner.inner ℝ (σ x) (cov (τ + τ') x (X x))
        = (mvfderiv I (fun y : M => Inner.inner ℝ (σ y) (τ y)) x (X x)
            - Inner.inner ℝ (cov σ x (X x)) (τ x)
            - Inner.inner ℝ (σ x) (cov τ x (X x)))
          + (mvfderiv I (fun y : M => Inner.inner ℝ (σ y) (τ' y)) x (X x)
            - Inner.inner ℝ (cov σ x (X x)) (τ' x)
            - Inner.inner ℝ (σ x) (cov τ' x (X x)))
      rw [hfun, hadd h1 h2, cov.isCovariantDerivativeOn.add hτ hτ']
      simp only [ContinuousLinearMap.add_apply, Pi.add_apply, inner_add_left, inner_add_right]
      ring
  obtain ⟨s1, hs1sm, hs1x⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (σ x)
  obtain ⟨t1, ht1sm, ht1x⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (τ x)
  have hs1d : MDiffAt (T% s1) x := hs1sm.contMDiffAt.mdifferentiableAt (by simp)
  have ht1d : MDiffAt (T% t1) x := ht1sm.contMDiffAt.mdifferentiableAt (by simp)
  have e1 : mvfderiv I (fun y : M => Inner.inner ℝ (σ y) (τ y)) x (X x)
      - Inner.inner ℝ (cov σ x (X x)) (τ x) - Inner.inner ℝ (σ x) (cov τ x (X x))
      = mvfderiv I (fun y : M => Inner.inner ℝ (s1 y) (τ y)) x (X x)
      - Inner.inner ℝ (cov s1 x (X x)) (τ x) - Inner.inner ℝ (s1 x) (cov τ x (X x)) :=
    (hΦ₁ τ hτ).pointwise hσ hs1d hs1x.symm
  have e2 : mvfderiv I (fun y : M => Inner.inner ℝ (s1 y) (τ y)) x (X x)
      - Inner.inner ℝ (cov s1 x (X x)) (τ x) - Inner.inner ℝ (s1 x) (cov τ x (X x))
      = mvfderiv I (fun y : M => Inner.inner ℝ (s1 y) (t1 y)) x (X x)
      - Inner.inner ℝ (cov s1 x (X x)) (t1 x) - Inner.inner ℝ (s1 x) (cov t1 x (X x)) :=
    (hΦ₂ s1 hs1d).pointwise hτ ht1d ht1x.symm
  have e3 : mvfderiv I (fun y : M => Inner.inner ℝ (s1 y) (t1 y)) x (X x)
      - Inner.inner ℝ (cov s1 x (X x)) (t1 x) - Inner.inner ℝ (s1 x) (cov t1 x (X x)) = 0 := by
    have h := hmet s1 t1 hs1sm ht1sm x (X x)
    linarith [h]
  linarith [e1, e2, e3]




/-! ## The defining property of the gradient, in `mvfderiv` form -/

/-- The gradient is the Riesz representative of `mfderiv`: `⟨∇F, v⟩ = dF(v)`. -/
lemma gpOde_inner_rgrad_mvfderiv' (F : M → ℝ) (x : M) (v : TangentSpace I x) :
    Inner.inner ℝ (rgrad (I := I) F x) v = mvfderiv I F x v := by
  rw [inner_rgrad]
  rfl


/-! ## The Hessian along a geodesic is the second derivative of the restriction -/

/-- **The second derivative of `f ∘ γ` along a geodesic `γ`.**  If `γ` is `C^∞` on an open set `V`,
is a geodesic there with non-vanishing velocity at `t ∈ V`, and the gradient of `f` is
differentiable at `γ t`, then the function `τ ↦ d(f ∘ γ)(τ) = mvfderiv f (γ τ) (γ' τ)` has
derivative `rhess cov f (γ t) (γ' t) (γ' t) = ⟨∇_{γ'}∇f, γ'⟩` at `t`.

The proof chooses a globally smooth field `W` agreeing with the velocity of `γ` near `t`
(`Submission.CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity`) and differentiates the
pairing `⟨∇f, W⟩` with `gpOde_mvfderiv_inner_local`; the term `⟨∇f, ∇_{γ'}W⟩` drops out by the geodesic
equation. -/
theorem gpOde_hasDerivAt_secondDeriv_along_geodesic
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : IsMetricCompatible cov)
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t : ℝ} (ht : t ∈ V)
    (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hgeo : ∀ τ ∈ V, IsGeodesicAt cov γ τ)
    (hne : curveVelocity (I := I) γ t ≠ 0)
    {f : M → ℝ} (hfd : MDiffAt (T% (rgrad (I := I) f)) (γ t)) :
    HasDerivAt (fun τ : ℝ => mvfderiv I f (γ τ) (curveVelocity (I := I) γ τ))
      (rhess cov f (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) t := by
  obtain ⟨W, hWsm, hWev⟩ :=
    Submission.CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity hV ht hγsm hne
  have hWt : W (γ t) = curveVelocity (I := I) γ t := hWev.self_of_nhds
  have hτ : MDiffAt (T% W) (γ t) := hWsm.contMDiffAt.mdifferentiableAt (by simp)
  have hgeoW : cov W (γ t) (curveVelocity (I := I) γ t) = 0 := hgeo t ht W hWsm hWev
  have hmain : mvfderiv I (fun y : M => Inner.inner ℝ (rgrad (I := I) f y) (W y)) (γ t)
      (curveVelocity (I := I) γ t)
      = rhess cov f (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
    rw [rhess]
    have hkey := gpOde_mvfderiv_inner_local (cov := cov) hmet (X := W) hfd hτ
    rw [hWt] at hkey
    rw [hgeoW, inner_zero_right, add_zero] at hkey
    exact hkey
  -- the chain rule
  have hcomp : HasDerivAt (fun τ : ℝ => Inner.inner ℝ (rgrad (I := I) f (γ τ)) (W (γ τ)))
      (rhess cov f (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) t := by
    have hu : MDifferentiableAt I (𝓘(ℝ, ℝ))
        (fun y : M => Inner.inner ℝ (rgrad (I := I) f y) (W y)) (γ t) :=
      MDifferentiableAt.inner_bundle (F := E) (E := fun x : M => TangentSpace I x) (b := id)
        hfd hτ
    have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t :=
      (hγsm.contMDiffAt (hV.mem_nhds ht)).mdifferentiableAt (by simp)
    have hstep := hu.hasMFDerivAt.comp t hγmd.hasMFDerivAt
    have hkey2 := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := fun y : M => Inner.inner ℝ (rgrad (I := I) f y) (W y)) (γ := γ) (t := t) hu hγmd
    rw [← hmain]
    rw [show mvfderiv I (fun y : M => Inner.inner ℝ (rgrad (I := I) f y) (W y)) (γ t)
        (curveVelocity (I := I) γ t)
      = deriv ((fun y : M => Inner.inner ℝ (rgrad (I := I) f y) (W y)) ∘ γ) t from hkey2]
    exact hstep.hasFDerivAt.differentiableAt.hasDerivAt
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hWev] with τ hτ1
  rw [hτ1]
  exact (gpOde_inner_rgrad_mvfderiv' (I := I) f (γ τ) (curveVelocity (I := I) γ τ)).symm


/-! ## The main comparison -/

open Bundle in
/-- A *port* of the already-proven `Submission.Work.Diff.C.ray_cos_compare` (module
`Diff/C/ray_cos_compare`): the same claim, but this module must be importable together with
`Submission.Work.Diff.C.gram_along` / `Submission.Work.Diff.C.init_data`.

WHY A PORT IS NEEDED: `Work.Diff.C.inner_rgrad_mvfderiv` is declared (identically) in both
`Submission/Work/Diff/C/grad_smooth.lean` and `Submission/Work/Diff/C/grad_smoothAt.lean`.
`ray_cos_compare` imports `grad_smoothAt`, while `gram_along_pair`/`init_data` (needed by the target
`Submission.Work.Diff.C.gram_pointwise2`) pull in the other copy; importing both makes Lean report
"environment already contains 'Work.Diff.C.inner_rgrad_mvfderiv'".  So the target cannot import
`ray_cos_compare` as it stands.

TASK: reproduce the proof of `Submission/Work/Diff/C/ray_cos_compare.lean` in a new module, with
1. **imports restricted to modules that do not declare `Work.Diff.C.inner_rgrad_mvfderiv`**, i.e.
   do NOT import `Submission.Work.Diff.C.grad_smooth` or `...grad_smoothAt`;
   `Submission.Work.Diff.C.Setup`, `Submission.Work.Diff.C.Defs`, `Submission.CurveField` and
   Mathlib are fine;
2. every auxiliary fact you need from those files **re-proved here under a fresh name** (suggested
   prefix `gpOde_`), so that nothing collides -- in particular the one-line fact
   `⟪rgrad F x, v⟫ = mvfderiv I F x v` (proof: `rw [inner_rgrad]; rfl`, using
   `Work.Diff.C.inner_rgrad` from `Diff/C/Defs`) should be re-proved as
   `gpOde_inner_rgrad_mvfderiv`.  Rename *everything* you introduce.

The mathematical content is the standard Sturm comparison: with `γ t = GExp q (t • u)` and
`φ t = f (γ t)`, metric compatibility and `⟪u,u⟫ = 1` give `φ'' t = rhess cov f (γ t) γ'(t) γ'(t)`,
so `hHess` (at `V = γ'(t)`) gives `|φ'' + φ| ≤ ε`, and the integral representation
`φ s = φ 0 cos s + φ' 0 sin s + ∫₀^s e τ sin (s - τ) dτ` with `|e| ≤ ε` yields the bound. -/
theorem gp_ode_compare
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {f : M → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    {u : TangentSpace I q} (hu : Inner.inner ℝ u u = 1)
    {s : ℝ} (hs0 : 0 ≤ s)
    (hsm : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) f (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)))
    (hHess : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ∀ V : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)),
        |rhess cov f (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) V V
          + f (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))
            * Inner.inner ℝ V V| ≤ ε * Inner.inner ℝ V V) :
    |f (Submission.GlobalExp.GExp (cov := cov) hmet q (s • u))
      - (f q * Real.cos s + Inner.inner ℝ (rgrad (I := I) (M := M) f q) u * Real.sin s)| ≤ ε * s := by
  have hu_ne : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have hunorm : ‖u‖ = 1 := by
    have h : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq u]; exact hu
    nlinarith [norm_nonneg u]
  have huξ : unitOf (I := I) u hu_ne = u := by
    rw [unitOf, hunorm]; simp
  set T : ℝ := max 1 s with hTdef
  have hT0 : 0 ≤ T := hTdef ▸ le_trans zero_le_one (le_max_left 1 s)
  have hsT : s ≤ T := hTdef ▸ le_max_right 1 s
  set γ : ℝ → M := geodCurve (cov := cov) hmet T hT0 q (unitOf u hu_ne)
    (unitOf_norm u hu_ne) with hγdef
  obtain ⟨hγ0, hγv0, hγsm, hγgeo, hγsp⟩ :=
    geodCurve_spec (cov := cov) hmet T hT0 q (unitOf u hu_ne) (unitOf_norm u hu_ne)
  set dl : ℝ := geodDelta (cov := cov) hmet with hdldef
  have hdlpos : 0 < dl := geodDelta_pos hmet
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) s, t ∈ Set.Ioo (-dl) (T + dl) := by
    intro t ht
    exact Set.mem_Ioo.mpr ⟨by linarith [hdlpos, ht.1], by linarith [ht.2, hsT, hdlpos]⟩
  have hGExp : ∀ t ∈ Set.Icc (0 : ℝ) s, GExp (cov := cov) hmet q (t • u) = γ t := by
    intro t ht
    have hmul : t * ‖u‖ = t := by rw [hunorm, mul_one]
    have hl : (0 : ℝ) ≤ max ‖u‖ (t * ‖u‖) := le_trans (norm_nonneg u) (le_max_left _ _)
    have hle : max ‖u‖ (t * ‖u‖) ≤ T := by
      refine max_le ?_ ?_
      · rw [hunorm, hTdef]; exact le_max_left 1 s
      · rw [hunorm, mul_one]; exact le_trans ht.2 hsT
    have hmemt : t * ‖u‖ ∈ Set.Ioo (-dl) (max ‖u‖ (t * ‖u‖) + dl) := by
      refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
      · rw [hunorm, mul_one]; linarith [hdlpos, ht.1]
      · have h2 := le_max_right ‖u‖ (t * ‖u‖); linarith [hdlpos, h2]
    have hagree := geodCurve_agree (cov := cov) hmet hl hT0 hle q
      (unitOf u hu_ne) (unitOf_norm u hu_ne)
    have h2 : (geodCurve (cov := cov) hmet (max ‖u‖ (t * ‖u‖)) hl q
        (unitOf u hu_ne) (unitOf_norm u hu_ne)) (t * ‖u‖) = γ t := by
      rw [show (geodCurve (cov := cov) hmet (max ‖u‖ (t * ‖u‖)) hl q
            (unitOf u hu_ne) (unitOf_norm u hu_ne)) (t * ‖u‖)
          = (geodCurve (cov := cov) hmet T hT0 q (unitOf u hu_ne) (unitOf_norm u hu_ne))
              (t * ‖u‖) from hagree hmemt]
      rw [hmul]
    rw [GExp_smul (cov := cov) hmet q hu_ne ht.1]
    exact h2
  have hft : ∀ t ∈ Set.Icc (0 : ℝ) s, CMDiffAt ∞ f (γ t) := by
    intro t ht
    have h := hsm t ht
    rwa [hGExp t ht] at h
  have hγmd : ∀ t ∈ Set.Icc (0 : ℝ) s, MDifferentiableAt 𝓘(ℝ) I γ t := fun t ht =>
    (hγsm.contMDiffAt (isOpen_Ioo.mem_nhds (hmem t ht))).mdifferentiableAt (by simp)
  set φ : ℝ → ℝ := fun τ => f (γ τ) with hφdef
  set φ' : ℝ → ℝ := fun τ => mvfderiv I f (γ τ) (curveVelocity (I := I) γ τ) with hφ'def
  set φ'' : ℝ → ℝ := fun τ =>
    rhess cov f (γ τ) (curveVelocity (I := I) γ τ) (curveVelocity (I := I) γ τ) with hφ''def
  have h1 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ (φ' t) t := by
    intro t ht
    have hfmd : MDifferentiableAt I (𝓘(ℝ, ℝ)) f (γ t) := (hft t ht).mdifferentiableAt (by simp)
    have hcomp := hfmd.hasMFDerivAt.comp t (hγmd t ht).hasMFDerivAt
    have hkey := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := f)
      (γ := γ) (t := t) hfmd (hγmd t ht)
    have hval : φ' t = deriv (f ∘ γ) t := by
      change mvfderiv I f (γ t) (curveVelocity (I := I) γ t) = deriv (f ∘ γ) t
      exact hkey
    rw [hval]
    exact hcomp.hasFDerivAt.differentiableAt.hasDerivAt
  have h2 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ' (φ'' t) t := by
    intro t ht
    have hfd : MDiffAt (T% (rgrad (I := I) f)) (γ t) :=
      (gpOde_grad_smoothAt (I := I) (F := f) (x := γ t) (hft t ht)).mdifferentiableAt (by simp)
    have hne : curveVelocity (I := I) γ t ≠ 0 := by
      intro h0
      have h := hγsp t (hmem t ht)
      rw [h0, norm_zero] at h
      norm_num at h
    exact gpOde_hasDerivAt_secondDeriv_along_geodesic (cov := cov) hmet isOpen_Ioo (hmem t ht) hγsm
      (fun τ hτ => hγgeo τ hτ) hne hfd
  have h3 : ∀ t ∈ Set.Icc (0 : ℝ) s, |φ'' t + φ t| ≤ ε := by
    intro t ht
    have hV : Inner.inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) = 1 := by
      rw [real_inner_self_eq_norm_sq, hγsp t (hmem t ht)]
      norm_num
    have hh := hHess t ht
    rw [hGExp t ht] at hh
    have hres := hh (curveVelocity (I := I) γ t)
    simp only [hV, mul_one] at hres
    change |rhess cov f (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
      + f (γ t)| ≤ ε
    exact hres
  have hfin := gpOde_ode_compare (φ := φ) (φ' := φ') (φ'' := φ'') hε hs0 h1 h2 h3
  have hφs : φ s = f (GExp (cov := cov) hmet q (s • u)) := by
    change f (γ s) = f (GExp (cov := cov) hmet q (s • u))
    rw [← hGExp s ⟨hs0, le_rfl⟩]
  have hφ0 : φ 0 = f q := by
    change f (γ 0) = f q
    rw [hγdef, hγ0]
  have hφ'0 : φ' 0 = Inner.inner ℝ (rgrad (I := I) (M := M) f q) u := by
    change mvfderiv I f (γ 0) (curveVelocity (I := I) γ 0)
      = Inner.inner ℝ (rgrad (I := I) (M := M) f q) u
    rw [hγdef, hγ0, hγv0, huξ]
    exact (gpOde_inner_rgrad_mvfderiv' (I := I) f q u).symm
  rw [hφs, hφ0, hφ'0] at hfin
  exact hfin


end Work.Diff.C
