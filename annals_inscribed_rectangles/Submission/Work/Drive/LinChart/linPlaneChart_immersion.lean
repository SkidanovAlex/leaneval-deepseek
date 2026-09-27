import Mathlib
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.diskPlane_mfderiv
import Submission.Work.Drive.projImmersion

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


namespace Work.Drive.LinChart

open Manifold
open scoped Manifold ContDiff

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## 1. The complex coordinate of `ℝ²`, as a linear isometry equivalence

The criterion `Work.Drive.injective_mfderiv_projMk_iff` lives on the model space
`Eucl 2 = EuclideanSpace ℝ (Fin 2)`, while the concrete disk charts live on `ℂ`.  The dictionary
`Work.Drive.cplxOf : ℝ² ≅ ℂ` (`cplxOf x = x 0 + x 1 · i`) is a *linear isometry equivalence*, which
is what lets the injectivity of a manifold derivative be transported between the two disks. -/

/-- The identification `ℝ² ≅ ℂ` as a linear isometry equivalence. -/
def cplxOfLIE : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ where
  toFun := Work.Drive.cplxOf
  invFun := Work.Drive.cplxOfInv
  left_inv := Work.Drive.cplxOfInv_cplxOf
  right_inv := Work.Drive.cplxOf_cplxOfInv
  map_add' := fun x y => by
    apply Complex.ext <;> simp [Work.Drive.cplxOf, PiLp.add_apply, Complex.add_re, Complex.add_im]
  map_smul' := fun a x => by
    apply Complex.ext <;> simp [Work.Drive.cplxOf, PiLp.smul_apply]
  norm_map' := fun x => by
    change ‖Work.Drive.cplxOf x‖ = ‖x‖
    have h : ‖Work.Drive.cplxOf x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Work.Drive.cplxOf]
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp
      ring
    nlinarith [norm_nonneg (Work.Drive.cplxOf x), norm_nonneg x]

@[simp] lemma cplxOfLIE_apply (y : EuclideanSpace ℝ (Fin 2)) :
    cplxOfLIE y = Work.Drive.cplxOf y := rfl

@[simp] lemma cplxOfLIE_clm_apply (y : EuclideanSpace ℝ (Fin 2)) :
    ((cplxOfLIE : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ)) y = Work.Drive.cplxOf y := rfl

/-! ## 2. The class lift of the linear plane chart

`Work.Drive.linPlaneChart φ c hc z` has class `[φ (linVecC z)]` on the level `c`
(`Work.Drive.cappingSpaceHomeoProj_linPlaneChart`), so its class map is the projectivisation of the
nowhere-vanishing lift `z ↦ φ (linVecC z)`.  Composing with `cplxOf` puts it on the model space of
the criterion. -/

/-- The lift `y ↦ φ (linVecC (cplxOf y))` of the class map of the linear plane chart, on the model
space `ℝ²` of the projective criterion. -/
def linLift (φ : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3)
    (y : EuclideanSpace ℝ (Fin 2)) : Work.Drive.Eucl 3 :=
  φ (Work.Drive.linVecC (Work.Drive.cplxOf y))

lemma linLift_ne_zero (φ : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3)
    (y : EuclideanSpace ℝ (Fin 2)) : linLift φ y ≠ 0 :=
  Work.Drive.phi_linVecC_ne_zero φ (Work.Drive.cplxOf y)

lemma linLift_contDiff (φ : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (linLift φ) :=
  φ.contDiff.comp (Work.Drive.linVecC_contDiff.comp contDiff_cplxOf)

lemma linLift_cplxOfInv (φ : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (z : ℂ) :
    linLift φ (Work.Drive.cplxOfInv z) = φ (Work.Drive.linVecC z) := by
  simp [linLift]

/-- The Fréchet derivative of the linear isometry equivalence `cplxOf` is itself. -/
lemma fderiv_cplxOf (y : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ Work.Drive.cplxOf y = (↑↑cplxOfLIE : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ) := by
  have h := (LinearIsometryEquiv.hasFDerivAt cplxOfLIE (x := y)).fderiv
  rw [show (⇑cplxOfLIE : EuclideanSpace ℝ (Fin 2) → ℂ) = Work.Drive.cplxOf from rfl] at h
  exact h

/-- **The differential of the lift `linLift φ`**: it is `φ ∘ d(linVecC) ∘ cplxOf`, the chain rule of
`φ (z ↦ linVecC z) (ℝ² ≅ ℂ)`. -/
lemma hasFDerivAt_linLift (φ : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (z : ℂ) :
    HasFDerivAt (linLift φ)
      ((φ : Work.Drive.Eucl 3 →L[ℝ] Work.Drive.Eucl 3).comp
        ((fderiv ℝ Work.Drive.linVecC z).comp
          (cplxOfLIE : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ)))
      (Work.Drive.cplxOfInv z) := by
  have hC : HasFDerivAt (⇑cplxOfLIE) ((cplxOfLIE : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ))
      (Work.Drive.cplxOfInv z) := LinearIsometryEquiv.hasFDerivAt cplxOfLIE
  have hL : HasFDerivAt Work.Drive.linVecC
      (fderiv ℝ Work.Drive.linVecC (Work.Drive.cplxOf (Work.Drive.cplxOfInv z)))
      (Work.Drive.cplxOf (Work.Drive.cplxOfInv z)) :=
    (Work.Drive.linVecC_contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := hL.comp (Work.Drive.cplxOfInv z) hC
  have hcomp2 := (φ : Work.Drive.Eucl 3 →L[ℝ] Work.Drive.Eucl 3).hasFDerivAt.comp
    (Work.Drive.cplxOfInv z) hcomp
  rw [show (⇑(φ : Work.Drive.Eucl 3 →L[ℝ] Work.Drive.Eucl 3) ∘
      (Work.Drive.linVecC ∘ Work.Drive.cplxOf)) = linLift φ from rfl] at hcomp2
  simpa only [Work.Drive.cplxOf_cplxOfInv] using hcomp2

/-- The differential of the lift, evaluated: `d(linLift φ)(y₀) w = φ (d(linVecC)(z) (cplxOf w))`
where `z = cplxOf y₀`. -/
lemma fderiv_linLift_apply (φ : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (z : ℂ)
    (w : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (linLift φ) (Work.Drive.cplxOfInv z) w
      = φ ((fderiv ℝ Work.Drive.linVecC z) (Work.Drive.cplxOf w)) := by
  rw [(hasFDerivAt_linLift φ z).fderiv]
  simp only [ContinuousLinearMap.comp_apply, cplxOfLIE_clm_apply]
  rfl

/-! ## 3. The differential of `linVecC`

`linVecC z = (z, 1 - ‖z‖²)`, so its differential is `χ ↦ (χ, -2·⟪z, χ⟫)`.  This section proves the
two ingredients of the key computation: the four coordinates of the differential (from the chain rule
applied to the coordinate projections `projImmCoordL i`), and the consequence that a direction whose
differential is *radial* must vanish. -/

/-- Coordinate `0` of the differential of `linVecC`. -/
lemma fderiv_linVecC_coord0 (z χ : ℂ) :
    (fderiv ℝ Work.Drive.linVecC z χ).ofLp 0 = χ.re := by
  have hdiff : DifferentiableAt ℝ Work.Drive.linVecC z :=
    (Work.Drive.linVecC_contDiff.differentiable (by simp)).differentiableAt
  have hcomp := (Work.Drive.projImmCoordL (n := 3) 0).hasFDerivAt.comp z hdiff.hasFDerivAt
  have h1 : fderiv ℝ (fun w : ℂ => (Work.Drive.linVecC w).ofLp 0) z χ
      = (fderiv ℝ Work.Drive.linVecC z χ).ofLp 0 := by
    have h4 : fderiv ℝ (fun w : ℂ => (Work.Drive.linVecC w).ofLp 0) z
        = (Work.Drive.projImmCoordL (n := 3) 0).comp (fderiv ℝ Work.Drive.linVecC z) :=
      hcomp.fderiv
    rw [h4, ContinuousLinearMap.comp_apply, Work.Drive.projImmCoordL_apply]
  have hfun : (fun w : ℂ => (Work.Drive.linVecC w).ofLp 0) = fun w : ℂ => w.re := by
    funext w
    simp [Work.Drive.linVecC, Work.Drive.ofComplex]
  rw [← h1, hfun]
  have hre : fderiv ℝ (fun w : ℂ => w.re) z = Complex.reCLM :=
    (Complex.reCLM.hasFDerivAt (x := z)).fderiv
  exact congrArg (fun L : ℂ →L[ℝ] ℝ => L χ) hre

/-- Coordinate `1` of the differential of `linVecC`. -/
lemma fderiv_linVecC_coord1 (z χ : ℂ) :
    (fderiv ℝ Work.Drive.linVecC z χ).ofLp 1 = χ.im := by
  have hdiff : DifferentiableAt ℝ Work.Drive.linVecC z :=
    (Work.Drive.linVecC_contDiff.differentiable (by simp)).differentiableAt
  have hcomp := (Work.Drive.projImmCoordL (n := 3) 1).hasFDerivAt.comp z hdiff.hasFDerivAt
  have h1 : fderiv ℝ (fun w : ℂ => (Work.Drive.linVecC w).ofLp 1) z χ
      = (fderiv ℝ Work.Drive.linVecC z χ).ofLp 1 := by
    have h4 : fderiv ℝ (fun w : ℂ => (Work.Drive.linVecC w).ofLp 1) z
        = (Work.Drive.projImmCoordL (n := 3) 1).comp (fderiv ℝ Work.Drive.linVecC z) :=
      hcomp.fderiv
    rw [h4, ContinuousLinearMap.comp_apply, Work.Drive.projImmCoordL_apply]
  have hfun : (fun w : ℂ => (Work.Drive.linVecC w).ofLp 1) = fun w : ℂ => w.im := by
    funext w
    simp [Work.Drive.linVecC, Work.Drive.ofComplex]
  rw [← h1, hfun]
  have him : fderiv ℝ (fun w : ℂ => w.im) z = Complex.imCLM :=
    (Complex.imCLM.hasFDerivAt (x := z)).fderiv
  exact congrArg (fun L : ℂ →L[ℝ] ℝ => L χ) him

/-- Coordinate `2` of the differential of `linVecC`: `χ ↦ -2·⟪z, χ⟫`. -/
lemma fderiv_linVecC_coord2 (z χ : ℂ) :
    (fderiv ℝ Work.Drive.linVecC z χ).ofLp 2 = -2 * inner ℝ z χ := by
  have hdiff : DifferentiableAt ℝ Work.Drive.linVecC z :=
    (Work.Drive.linVecC_contDiff.differentiable (by simp)).differentiableAt
  have hcomp := (Work.Drive.projImmCoordL (n := 3) 2).hasFDerivAt.comp z hdiff.hasFDerivAt
  have h1 : fderiv ℝ (fun w : ℂ => (Work.Drive.linVecC w).ofLp 2) z χ
      = (fderiv ℝ Work.Drive.linVecC z χ).ofLp 2 := by
    have h4 : fderiv ℝ (fun w : ℂ => (Work.Drive.linVecC w).ofLp 2) z
        = (Work.Drive.projImmCoordL (n := 3) 2).comp (fderiv ℝ Work.Drive.linVecC z) :=
      hcomp.fderiv
    rw [h4, ContinuousLinearMap.comp_apply, Work.Drive.projImmCoordL_apply]
  have hfun : (fun w : ℂ => (Work.Drive.linVecC w).ofLp 2) = fun w : ℂ => 1 - ‖w‖ ^ 2 := by
    funext w
    simp only [Work.Drive.linVecC, Work.Drive.ofComplex, WithLp.ofLp_toLp, Matrix.cons_val,
      Complex.ofReal_re]
  rw [← h1, hfun]
  have hh : HasFDerivAt (fun z : ℂ => ‖z‖ ^ 2) ((2 : ℕ) • innerSL ℝ z) z := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) z).norm_sq
  have h2' : HasFDerivAt (fun z : ℂ => 1 - ‖z‖ ^ 2) ((0 : ℂ →L[ℝ] ℝ) - (2 : ℕ) • innerSL ℝ z) z :=
    (hasFDerivAt_const (1 : ℝ) z).sub hh
  rw [h2'.fderiv]
  simp only [sub_apply, zero_apply, smul_apply, innerSL_apply_apply]
  rw [two_nsmul]
  ring

/-- Coordinate `3` of the differential of `linVecC`. -/
lemma fderiv_linVecC_coord3 (z χ : ℂ) :
    (fderiv ℝ Work.Drive.linVecC z χ).ofLp 3 = 0 := by
  have hdiff : DifferentiableAt ℝ Work.Drive.linVecC z :=
    (Work.Drive.linVecC_contDiff.differentiable (by simp)).differentiableAt
  have hcomp := (Work.Drive.projImmCoordL (n := 3) 3).hasFDerivAt.comp z hdiff.hasFDerivAt
  have h1 : fderiv ℝ (fun w : ℂ => (Work.Drive.linVecC w).ofLp 3) z χ
      = (fderiv ℝ Work.Drive.linVecC z χ).ofLp 3 := by
    have h4 : fderiv ℝ (fun w : ℂ => (Work.Drive.linVecC w).ofLp 3) z
        = (Work.Drive.projImmCoordL (n := 3) 3).comp (fderiv ℝ Work.Drive.linVecC z) :=
      hcomp.fderiv
    rw [h4, ContinuousLinearMap.comp_apply, Work.Drive.projImmCoordL_apply]
  have hfun : (fun w : ℂ => (Work.Drive.linVecC w).ofLp 3) = fun _ : ℂ => (0 : ℝ) := by
    funext w
    simp only [Work.Drive.linVecC, Work.Drive.ofComplex, WithLp.ofLp_toLp, Matrix.cons_val,
      Complex.ofReal_im]
  rw [← h1, hfun]
  simp

/-- The coordinates of `linVecC` itself. -/
lemma linVecC_coord0 (z : ℂ) : (Work.Drive.linVecC z).ofLp 0 = z.re := by
  simp [Work.Drive.linVecC, Work.Drive.ofComplex]

lemma linVecC_coord1 (z : ℂ) : (Work.Drive.linVecC z).ofLp 1 = z.im := by
  simp [Work.Drive.linVecC, Work.Drive.ofComplex]

lemma linVecC_coord2 (z : ℂ) : (Work.Drive.linVecC z).ofLp 2 = 1 - ‖z‖ ^ 2 := by
  simp only [Work.Drive.linVecC, Work.Drive.ofComplex, WithLp.ofLp_toLp, Matrix.cons_val,
    Complex.ofReal_re]

/-- **The key linear computation.**  The only direction in which the differential of `linVecC` at `z`
is a *real multiple* of the value `linVecC z` is the zero direction.

Indeed `fderiv linVecC z χ = λ • linVecC z` unpacks (coordinates `0`, `1`, `2`) to `χ = λ • z` and
`-2·⟪z, χ⟫ = λ·(1 - ‖z‖²)`; substituting the first in the second gives `λ·(1 + ‖z‖²) = 0`, so
`λ = 0` and `χ = 0`.  (Note that `linVecC` never vanishes, so no side condition on `z` is needed:
the computation is uniform on all of `ℂ`.) -/
lemma linVecC_fderiv_span_eq_zero {z χ : ℂ} {lam : ℝ}
    (h : fderiv ℝ Work.Drive.linVecC z χ = lam • Work.Drive.linVecC z) : χ = 0 := by
  have e0 : χ.re = lam * z.re := by
    have hh := congrArg (fun v : Work.Drive.Eucl 3 => v.ofLp 0) h
    rw [fderiv_linVecC_coord0, PiLp.smul_apply, smul_eq_mul, linVecC_coord0] at hh
    exact hh
  have e1 : χ.im = lam * z.im := by
    have hh := congrArg (fun v : Work.Drive.Eucl 3 => v.ofLp 1) h
    rw [fderiv_linVecC_coord1, PiLp.smul_apply, smul_eq_mul, linVecC_coord1] at hh
    exact hh
  have e2 : -2 * inner ℝ z χ = lam * (1 - ‖z‖ ^ 2) := by
    have hh := congrArg (fun v : Work.Drive.Eucl 3 => v.ofLp 2) h
    rw [fderiv_linVecC_coord2, PiLp.smul_apply, smul_eq_mul, linVecC_coord2] at hh
    exact hh
  have hchi : χ = lam • z := by
    refine Complex.ext ?_ ?_
    · rw [Complex.smul_re, smul_eq_mul]; exact e0
    · rw [Complex.smul_im, smul_eq_mul]; exact e1
  have hlam : lam = 0 := by
    have h2 := e2
    rw [hchi, real_inner_smul_right, real_inner_self_eq_norm_sq] at h2
    have hpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
    have hmul : lam * (1 + ‖z‖ ^ 2) = 0 := by linarith [h2]
    exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hpos)
  rw [hchi, hlam, zero_smul]

/-! ## 4. Transporting the injectivity of `mfderiv` along a linear isometry equivalence

The criterion of `Work.Drive.projImmersion` is stated for the domain `Eucl 2`, whereas the disk
presentation is a map on `ℂ`.  The following is the same statement as
`Work.Drive.injective_mfderiv_comp_linearIsometryEquiv`, but with the model space of the target
manifold *free* (that file's version forces the domain's model space to be the target's), which is
what is needed here: the target `ℝP³` is modelled on `Eucl 3`, while the domain must stay `ℂ` (or
`Eucl 2`). -/

/-- **Injectivity of the manifold derivative is invariant under precomposition with a linear isometry
equivalence.**  Let `I` be a model with corners on the model space `E`, `M` an `I`-manifold,
`f : F → M` a map from a normed space `F` (regarded as a manifold with the self model) and
`e : E' ≃ₗᵢ[ℝ] F` a linear isometry equivalence.  Then `mfderiv f` at `e x` is injective iff
`mfderiv (f ∘ e)` at `x` is. -/
theorem injective_mfderiv_comp_linearIsometryEquiv_self {F E E' H : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    (e : E' ≃ₗᵢ[ℝ] F) (f : F → M) (x : E') :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ F) I f (e x)) ↔
      Function.Injective (mfderiv (modelWithCornersSelf ℝ E') I (f ∘ ⇑e) x) := by
  have hmfde : mfderiv (modelWithCornersSelf ℝ E') (modelWithCornersSelf ℝ F) (⇑e) x
      = (↑e.toContinuousLinearEquiv : E' →L[ℝ] F) :=
    (ContinuousLinearMap.hasMFDerivAt (↑e.toContinuousLinearEquiv : E' →L[ℝ] F)).mfderiv
  have hmain : mfderiv (modelWithCornersSelf ℝ E') I (f ∘ ⇑e) x =
      (mfderiv (modelWithCornersSelf ℝ F) I f (e x)).comp
        (↑e.toContinuousLinearEquiv : E' →L[ℝ] F) := by
    by_cases hd : MDifferentiableAt (modelWithCornersSelf ℝ F) I f (e x)
    · have he : MDifferentiableAt (modelWithCornersSelf ℝ E') (modelWithCornersSelf ℝ F) (⇑e) x :=
        (ContinuousLinearMap.hasMFDerivAt (↑e.toContinuousLinearEquiv : E' →L[ℝ] F)).mdifferentiableAt
      rw [mfderiv_comp (I := modelWithCornersSelf ℝ E') (I' := modelWithCornersSelf ℝ F)
        (I'' := I) x hd he, hmfde]
    · have hne : ¬ MDifferentiableAt (modelWithCornersSelf ℝ E') I (f ∘ ⇑e) x := by
        intro hc
        have he' : MDifferentiableAt (modelWithCornersSelf ℝ F) (modelWithCornersSelf ℝ E')
            (⇑e.symm) (e x) :=
          (ContinuousLinearMap.hasMFDerivAt (↑e.symm.toContinuousLinearEquiv : F →L[ℝ] E')).mdifferentiableAt
        have h2 : MDifferentiableAt (modelWithCornersSelf ℝ F) I ((f ∘ ⇑e) ∘ ⇑e.symm) (e x) :=
          MDifferentiableAt.comp (e x) (f := ⇑e.symm) (by simpa using hc) he'
        have h3 : ((f ∘ ⇑e) ∘ ⇑e.symm) = f := by
          funext y
          simp [Function.comp_apply]
        rw [h3] at h2
        exact hd h2
      have h1 : mfderiv (modelWithCornersSelf ℝ E') I (f ∘ ⇑e) x = 0 := by
        simp [mfderiv, hne]
      have h2 : mfderiv (modelWithCornersSelf ℝ F) I f (e x) = 0 := by
        simp [mfderiv, hd]
      rw [h1, h2, ContinuousLinearMap.zero_comp]
  have hkey : ∀ v : TangentSpace (modelWithCornersSelf ℝ E') x,
      mfderiv (modelWithCornersSelf ℝ E') I (f ∘ ⇑e) x v
      = mfderiv (modelWithCornersSelf ℝ F) I f (e x) (e v) := by
    intro v
    have h := congrArg (fun L : TangentSpace (modelWithCornersSelf ℝ E') x →L[ℝ]
        TangentSpace I ((f ∘ ⇑e) x) => L v) hmain
    exact h.trans (ContinuousLinearMap.comp_apply (mfderiv (modelWithCornersSelf ℝ F) I f (e x))
      (↑e.toContinuousLinearEquiv : E' →L[ℝ] F) v)
  constructor
  · intro h v w hvw
    have h2 : mfderiv (modelWithCornersSelf ℝ F) I f (e x) (e v)
        = mfderiv (modelWithCornersSelf ℝ F) I f (e x) (e w) := by
      rw [← hkey v, ← hkey w]
      exact hvw
    exact e.injective (h h2)
  · intro h u w huw
    obtain ⟨a, ha⟩ := e.surjective u
    obtain ⟨b, hb⟩ := e.surjective w
    have h2 : mfderiv (modelWithCornersSelf ℝ E') I (f ∘ ⇑e) x a
        = mfderiv (modelWithCornersSelf ℝ E') I (f ∘ ⇑e) x b := by
      rw [hkey a, hkey b, ha, hb]
      exact huw
    rw [← ha, ← hb, h h2]

/-! ## 5. The immersion of the linear plane chart -/

/-- **The linear plane chart is an immersion** (the hypothesis `hc` of the genericity lane,
`Submission/Work/Drive/COUNTING_HALF_REMAINING.md` §2, `PROJ_IMMERSION_STATUS.md`), *everywhere* on the
disk — including the boundary circle and the centre.  With `linPlaneChart φ c hc z =
[φ (z, 1 - ‖z‖²)]` (the disk model of the projective plane `φ(linStd)` on the level `c`,
`Submission/Work/Drive/linearPlaneChart.lean`), the class map is
`z ↦ [φ (linVecC z)]`, `linVecC z = (z, 1 - ‖z‖²)`, `d(linVecC)(z) w = (w, -2 Re (z̄ w))`, and
`(w, -2 Re (z̄ w)) = λ (z, 1 - ‖z‖²)` forces `λ(1 + ‖z‖²) = 0`, so `λ = 0`, `w = 0`: the criterion
`Work.Drive.injective_mfderiv_projMk_iff` applies.  (Note that `linVecC` never vanishes, and `φ` is a
linear equivalence, so the lift `z ↦ φ (linVecC z)` is nowhere zero.) -/
theorem linPlaneChart_immersion (φ : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (c : ℝ)
    (hc : 0 < c) (z : ℂ) :
    Function.Injective (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun w : ℂ => (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.linPlaneChart φ c hc w)).2) z) := by
  -- the class map of the chart is the projectivisation of `φ ∘ linVecC`
  have hfun : (fun w : ℂ => (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.linPlaneChart φ c hc w)).2)
      = fun w : ℂ => Projectivization.mk ℝ (φ (Work.Drive.linVecC w))
          (Work.Drive.phi_linVecC_ne_zero φ w) := by
    funext w
    rw [Work.Drive.cappingSpaceHomeoProj_linPlaneChart]
  rw [hfun]
  -- the smooth manifold structure of `ℝP³`
  haveI hM : IsManifold (𝓡 3) 1 (Projectivization ℝ (Work.Drive.Eucl 3)) := by
    haveI : IsManifold (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Projectivization ℝ (Work.Drive.Eucl 3)) :=
      Work.Drive.isManifold_projCharted 3
    infer_instance
  -- the criterion applies to the lift on the model space `ℝ²`
  have hVs : ContMDiffAt (𝓡 2) (𝓘(ℝ, Work.Drive.Eucl 3)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (linLift φ) (Work.Drive.cplxOfInv z) :=
    contMDiffAt_iff_contDiffAt.mpr (linLift_contDiff φ).contDiffAt
  have key : ∀ w : EuclideanSpace ℝ (Fin 2),
      fderiv ℝ (linLift φ) (Work.Drive.cplxOfInv z) w ∈
        Submodule.span ℝ ({linLift φ (Work.Drive.cplxOfInv z)} : Set (Work.Drive.Eucl 3)) →
        w = 0 := by
    intro w hw
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hw
    rw [fderiv_linLift_apply] at hlam
    rw [linLift_cplxOfInv] at hlam
    -- `hlam : lam • φ (linVecC z) = φ (d linVecC (z) (cplxOf w))`
    have hder : (fderiv ℝ Work.Drive.linVecC z) (Work.Drive.cplxOf w)
        = lam • Work.Drive.linVecC z := by
      apply φ.injective
      rw [← hlam]
      exact (map_smul (φ : Work.Drive.Eucl 3 →L[ℝ] Work.Drive.Eucl 3) lam
        (Work.Drive.linVecC z)).symm
    have hcw : Work.Drive.cplxOf w = 0 := linVecC_fderiv_span_eq_zero hder
    exact Work.Drive.cplxOf_injective (by rw [hcw]; simp [Work.Drive.cplxOf])
  have hcrit : Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun x : EuclideanSpace ℝ (Fin 2) => Projectivization.mk ℝ (linLift φ x)
        (linLift_ne_zero φ x)) (Work.Drive.cplxOfInv z)) :=
    (Work.Drive.injective_mfderiv_projMk_iff (linLift φ) (linLift_ne_zero φ)
      (Work.Drive.cplxOfInv z) hVs).mpr key
  -- transport along `ℝ² ≅ ℂ`
  have hB : Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      ((fun w : ℂ => Projectivization.mk ℝ (φ (Work.Drive.linVecC w))
        (Work.Drive.phi_linVecC_ne_zero φ w)) ∘ ⇑cplxOfLIE)
      (Work.Drive.cplxOfInv z)) := by
    have hfun_eq : ((fun w : ℂ => Projectivization.mk ℝ (φ (Work.Drive.linVecC w))
        (Work.Drive.phi_linVecC_ne_zero φ w)) ∘ ⇑cplxOfLIE)
        = (fun x : EuclideanSpace ℝ (Fin 2) => Projectivization.mk ℝ (linLift φ x)
          (linLift_ne_zero φ x)) := by
      funext y
      rfl
    rw [hfun_eq]
    exact hcrit
  have hA : Function.Injective (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun w : ℂ => Projectivization.mk ℝ (φ (Work.Drive.linVecC w))
        (Work.Drive.phi_linVecC_ne_zero φ w)) (cplxOfLIE (Work.Drive.cplxOfInv z))) :=
    (injective_mfderiv_comp_linearIsometryEquiv_self (I := 𝓡 3) cplxOfLIE
      (fun w : ℂ => Projectivization.mk ℝ (φ (Work.Drive.linVecC w))
        (Work.Drive.phi_linVecC_ne_zero φ w)) (Work.Drive.cplxOfInv z)).mpr hB
  have hz : cplxOfLIE (Work.Drive.cplxOfInv z) = z := Work.Drive.cplxOf_cplxOfInv z
  rw [hz] at hA
  exact hA

end

end Work.Drive.LinChart
