import Mathlib
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.frame_deps
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second covariant derivative of the curvature, on vector fields

`cov2RmExt g x u V A B C D` (frozen in `Submission.Work.Diff.GE.NablaRm`) is the differentiation
formula for `∇∇Rm` written with five *smooth fields* `V A B C D` instead of the five tangent vectors
of the frozen `cov2Rm`: it is `mvfderiv (y ↦ covRm g y (V y) … (D y)) x u` minus the five Leibniz
corrections.  This file collects the auxiliary facts needed to prove that it really is the `(0,6)`
tensor `∇∇Rm` evaluated on the values `V x, …, D x` (the target lemma
`Work.Diff.GE.kato_cov2RmExt_field` in `kato_cov2RmExt_field.lean`).

Contents:

* the fourth field-slot facts of `dRmPhi` (linearity, value-dependence, germ), obtained from the
  third slot (`covRm_linear_fth`) and the skew-symmetry `rmP_skew`;
* `dRmPhi_fields_smooth`: `y ↦ dRmPhi g y (𝔳 y) A B C D` is smooth for smooth `𝔳, A, B, C, D`;
* `covRm_fields_eq_dRmPhi`, `covRm_fields_smooth`: the field form and the smoothness of `covRm`;
* the pointwise `ℝ`-linearity of `covRm` in its first and fifth arguments;
* a general "value dependence" machine: a function of one vector field which is `C^∞(M)`-linear in
  that field and germ-invariant depends only on the value of the field at the base point.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable {g : SMet I M} {x : M} {v : TangentSpace I x}

/-! ## The fourth field slot of `dRmPhi` -/

/-- `dRmPhi` is skew in its last two field slots (the skew-adjointness `rmP_skew` of the frozen
curvature form, propagated through the four connection corrections). -/
theorem dRmPhi_skew_thd_fth (hLC : LCSmooth I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    dRmPhi g x v A B C D = - dRmPhi g x v A B D C := by
  have hfun : (fun y : M => rmP g y (A y) (B y) (D y) (C y))
      = -(fun y : M => rmP g y (A y) (B y) (C y) (D y)) :=
    funext fun y => rmP_skew hLC g y (A y) (B y) (D y) (C y)
  have h1 : mvfderiv I (fun y : M => rmP g y (A y) (B y) (D y) (C y)) x v
      = - mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x v := by
    rw [hfun, mvfderiv_neg]
    simp
  have c1 : rmP g x ((lcOf g) A x v) (B x) (D x) (C x)
      = - rmP g x ((lcOf g) A x v) (B x) (C x) (D x) :=
    rmP_skew hLC g x ((lcOf g) A x v) (B x) (D x) (C x)
  have c2 : rmP g x (A x) ((lcOf g) B x v) (D x) (C x)
      = - rmP g x (A x) ((lcOf g) B x v) (C x) (D x) :=
    rmP_skew hLC g x (A x) ((lcOf g) B x v) (D x) (C x)
  have c3 : rmP g x (A x) (B x) ((lcOf g) D x v) (C x)
      = - rmP g x (A x) (B x) (C x) ((lcOf g) D x v) :=
    rmP_skew hLC g x (A x) (B x) ((lcOf g) D x v) (C x)
  have c4 : rmP g x (A x) (B x) (D x) ((lcOf g) C x v)
      = - rmP g x (A x) (B x) ((lcOf g) C x v) (D x) :=
    rmP_skew hLC g x (A x) (B x) (D x) ((lcOf g) C x v)
  simp only [dRmPhi]
  rw [h1, c1, c2, c3, c4]
  ring

/-- `dRmPhi` is `ℝ`-linear in its fourth field slot. -/
theorem dRmPhi_linear_fif (hLC : LCSmooth I M)
    {A B C D₁ D₂ : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (hD₁ : CMDiff ∞ (T% D₁)) (hD₂ : CMDiff ∞ (T% D₂))
    {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    dRmPhi g x v A B C (f₁ • D₁ + f₂ • D₂)
      = f₁ x * dRmPhi g x v A B C D₁ + f₂ x * dRmPhi g x v A B C D₂ := by
  have hD : CMDiff ∞ (T% (f₁ • D₁ + f₂ • D₂)) :=
    (hf₁.smul_section hD₁).add_section (hf₂.smul_section hD₂)
  have hskew₁ := dRmPhi_skew_thd_fth (g := g) (x := x) (v := v) hLC hA hB hC hD
  have hskew₂ := dRmPhi_skew_thd_fth (g := g) (x := x) (v := v) hLC hA hB hC hD₁
  have hskew₃ := dRmPhi_skew_thd_fth (g := g) (x := x) (v := v) hLC hA hB hC hD₂
  have hlin := fth_dRmPhi_linear (g := g) (x := x) (v := v) hLC hA hB hD₁ hD₂ hC hf₁ hf₂
  rw [hskew₁, hlin, hskew₂, hskew₃]
  ring

/-- `dRmPhi` depends on its fourth field only through its value at `x`. -/
theorem dRmPhi_bind_fif (hLC : LCSmooth I M)
    {A B C D D' : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (hD : CMDiff ∞ (T% D)) (hD' : CMDiff ∞ (T% D')) (h : D x = D' x) :
    dRmPhi g x v A B C D = dRmPhi g x v A B C D' := by
  have hskew₁ := dRmPhi_skew_thd_fth (g := g) (x := x) (v := v) hLC hA hB hC hD
  have hskew₂ := dRmPhi_skew_thd_fth (g := g) (x := x) (v := v) hLC hA hB hC hD'
  have hbind := fth_dRmPhi_bind (g := g) (x := x) (v := v) hLC hA hB hD hD' hC h
  rw [hskew₁, hbind, hskew₂]

/-! ## Smoothness of `dRmPhi` on smooth fields -/

/-- `y ↦ dRmPhi g y (𝔳 y) A B C D` is smooth whenever `𝔳, A, B, C, D` are smooth sections. -/
theorem dRmPhi_fields_smooth (hLC : LCSmooth I M)
    {𝔳 A B C D : Π y : M, TangentSpace I y}
    (h𝔳 : CMDiff ∞ (T% 𝔳)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (fun y : M => dRmPhi g y (𝔳 y) A B C D) := by
  obtain ⟨hcov⟩ := (hLC g).1
  have h0 : CMDiff ∞ (fun z : M => rmP g z (A z) (B z) (C z) (D z)) :=
    rmP_fields_smooth hLC g hA hB hC hD
  have h1 : CMDiff ∞ (fun y : M =>
      mvfderiv I (fun z : M => rmP g z (A z) (B z) (C z) (D z)) y (𝔳 y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff h0 h𝔳
  have h2 : CMDiff ∞ (fun y : M => rmP g y ((lcOf g) A y (𝔳 y)) (B y) (C y) (D y)) :=
    rmP_fields_smooth hLC g
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hA h𝔳) hB hC hD
  have h3 : CMDiff ∞ (fun y : M => rmP g y (A y) ((lcOf g) B y (𝔳 y)) (C y) (D y)) :=
    rmP_fields_smooth hLC g hA
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hB h𝔳) hC hD
  have h4 : CMDiff ∞ (fun y : M => rmP g y (A y) (B y) ((lcOf g) C y (𝔳 y)) (D y)) :=
    rmP_fields_smooth hLC g hA hB
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hC h𝔳) hD
  have h5 : CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (C y) ((lcOf g) D y (𝔳 y))) :=
    rmP_fields_smooth hLC g hA hB hC
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hD h𝔳)
  have hgoal : (fun y : M => dRmPhi g y (𝔳 y) A B C D)
      = fun y : M =>
          mvfderiv I (fun z : M => rmP g z (A z) (B z) (C z) (D z)) y (𝔳 y)
            - rmP g y ((lcOf g) A y (𝔳 y)) (B y) (C y) (D y)
            - rmP g y (A y) ((lcOf g) B y (𝔳 y)) (C y) (D y)
            - rmP g y (A y) (B y) ((lcOf g) C y (𝔳 y)) (D y)
            - rmP g y (A y) (B y) (C y) ((lcOf g) D y (𝔳 y)) := by
    funext y
    simp only [dRmPhi]
  rw [hgoal]
  exact (((h1.sub h2).sub h3).sub h4).sub h5

/-! ## The field form and smoothness of `covRm` -/

/-- `covRm` evaluated on smooth fields is `dRmPhi` evaluated on those fields. -/
theorem covRm_fields_eq_dRmPhi (hLC : LCSmooth I M)
    {V A B C D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) (y : M) :
    covRm g y (V y) (A y) (B y) (C y) (D y) = dRmPhi g y (V y) A B C D := by
  rw [covRm_eq_dRmPhi]
  rw [dRmPhi_bind_fst (g := g) (x := y) (v := V y) hLC (smoothExt_cmdiff y (A y)) hA
      (smoothExt_cmdiff y (B y)) (smoothExt_cmdiff y (C y)) (smoothExt_cmdiff y (D y))
      (smoothExt_apply y (A y))]
  rw [dRmPhi_bind_slotB (g := g) (x := y) (v := V y) hLC hA (smoothExt_cmdiff y (B y)) hB
      (smoothExt_cmdiff y (C y)) (smoothExt_cmdiff y (D y)) (smoothExt_apply y (B y))]
  rw [fth_dRmPhi_bind (g := g) (x := y) (v := V y) hLC hA hB (smoothExt_cmdiff y (C y)) hC
      (smoothExt_cmdiff y (D y)) (smoothExt_apply y (C y))]
  rw [dRmPhi_bind_fif (g := g) (x := y) (v := V y) hLC hA hB hC (smoothExt_cmdiff y (D y)) hD
      (smoothExt_apply y (D y))]

/-- `y ↦ covRm g y (V y) (A y) (B y) (C y) (D y)` is smooth for smooth sections. -/
theorem covRm_fields_smooth (hLC : LCSmooth I M)
    {V A B C D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)) := by
  have hgoal : (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y))
      = fun y : M => dRmPhi g y (V y) A B C D :=
    funext fun y => covRm_fields_eq_dRmPhi (g := g) hLC hV hA hB hC hD y
  rw [hgoal]
  exact dRmPhi_fields_smooth (g := g) hLC hV hA hB hC hD

/-! ## Pointwise `ℝ`-linearity of `covRm` in its first and last arguments -/

/-- `covRm` is `ℝ`-linear in its first argument `v` (the direction). -/
theorem covRm_linear_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (r s : ℝ) (v₁ v₂ : TangentSpace I x) (a b c d : TangentSpace I x),
      covRm g x (r • v₁ + s • v₂) a b c d
        = r * covRm g x v₁ a b c d + s * covRm g x v₂ a b c d := by
  intro r s v₁ v₂ a b c d
  have hd : mvfderiv I (fun y : M => rmP g y (smoothExt x a y) (smoothExt x b y)
        (smoothExt x c y) (smoothExt x d y)) x (r • v₁ + s • v₂)
      = r * mvfderiv I (fun y : M => rmP g y (smoothExt x a y) (smoothExt x b y)
          (smoothExt x c y) (smoothExt x d y)) x v₁
        + s * mvfderiv I (fun y : M => rmP g y (smoothExt x a y) (smoothExt x b y)
          (smoothExt x c y) (smoothExt x d y)) x v₂ := by
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
  have c1 : rmP g x ((lcOf g) (smoothExt x a) x (r • v₁ + s • v₂)) b c d
      = r * rmP g x ((lcOf g) (smoothExt x a) x v₁) b c d
        + s * rmP g x ((lcOf g) (smoothExt x a) x v₂) b c d := by
    rw [map_add, map_smul, map_smul]
    simp only [rmP_add_fst g hLC, rmP_smul_fst g hLC, smul_eq_mul]
  have c2 : rmP g x a ((lcOf g) (smoothExt x b) x (r • v₁ + s • v₂)) c d
      = r * rmP g x a ((lcOf g) (smoothExt x b) x v₁) c d
        + s * rmP g x a ((lcOf g) (smoothExt x b) x v₂) c d := by
    rw [map_add, map_smul, map_smul]
    simp only [rmP_add_snd g hLC, rmP_smul_snd g hLC, smul_eq_mul]
  have c3 : rmP g x a b ((lcOf g) (smoothExt x c) x (r • v₁ + s • v₂)) d
      = r * rmP g x a b ((lcOf g) (smoothExt x c) x v₁) d
        + s * rmP g x a b ((lcOf g) (smoothExt x c) x v₂) d := by
    rw [map_add, map_smul, map_smul]
    simp only [rmP_add_thd g hLC, rmP_smul_thd g hLC, smul_eq_mul]
  have c4 : rmP g x a b c ((lcOf g) (smoothExt x d) x (r • v₁ + s • v₂))
      = r * rmP g x a b c ((lcOf g) (smoothExt x d) x v₁)
        + s * rmP g x a b c ((lcOf g) (smoothExt x d) x v₂) := by
    rw [map_add, map_smul, map_smul]
    simp only [rmP_add_fth g hLC, rmP_smul_fth g hLC, smul_eq_mul]
  simp only [covRm]
  rw [hd, c1, c2, c3, c4]
  ring

/-- `covRm` is `ℝ`-linear in its fifth argument `d`. -/
theorem covRm_linear_fif (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (v a b c : TangentSpace I x) (r s : ℝ) (d₁ d₂ : TangentSpace I x),
      covRm g x v a b c (r • d₁ + s • d₂)
        = r * covRm g x v a b c d₁ + s * covRm g x v a b c d₂ := by
  intro v a b c r s d₁ d₂
  have h1 : CMDiff ∞ (T% (smoothExt x d₁)) := smoothExt_cmdiff x d₁
  have h2 : CMDiff ∞ (T% (smoothExt x d₂)) := smoothExt_cmdiff x d₂
  have h3 : CMDiff ∞ (T% (smoothExt x a)) := smoothExt_cmdiff x a
  have h4 : CMDiff ∞ (T% (smoothExt x b)) := smoothExt_cmdiff x b
  have h5 : CMDiff ∞ (T% (smoothExt x c)) := smoothExt_cmdiff x c
  have h6 : CMDiff ∞ (T% ((fun _ : M => r) • smoothExt x d₁
      + (fun _ : M => s) • smoothExt x d₂)) :=
    ((contMDiff_const (c := r)).smul_section h1).add_section
      ((contMDiff_const (c := s)).smul_section h2)
  have hsum : smoothExt x (r • d₁ + s • d₂) x
      = ((fun _ : M => r) • smoothExt x d₁ + (fun _ : M => s) • smoothExt x d₂) x := by
    rw [show ((fun _ : M => r) • smoothExt x d₁ + (fun _ : M => s) • smoothExt x d₂) x
        = r • smoothExt x d₁ x + s • smoothExt x d₂ x from rfl,
      smoothExt_apply x (r • d₁ + s • d₂), smoothExt_apply x d₁, smoothExt_apply x d₂]
  have hbind := dRmPhi_bind_fif (g := g) (x := x) (v := v) hLC h3 h4 h5
    (smoothExt_cmdiff x (r • d₁ + s • d₂)) h6 hsum
  have hlin := dRmPhi_linear_fif (g := g) (x := x) (v := v) hLC h3 h4 h5 h1 h2
    (contMDiff_const (c := r)) (contMDiff_const (c := s))
  have hcov1 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a) (b := b) (c := c)
    (d := r • d₁ + s • d₂)
  have hcov2 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a) (b := b) (c := c) (d := d₁)
  have hcov3 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a) (b := b) (c := c) (d := d₂)
  rw [hcov1, hbind, hlin, hcov2, hcov3]

/-! ## The value-dependence machine -/

/-- **Value dependence machine.**  A function `F` of one tangent vector field which is
`C^∞(M)`-linear in that field and invariant under a change of the field away from `x` depends only
on the value of the field at `x`: the field is written as a `C^∞` combination of globally defined
smooth fields near `x` with vanishing coefficients
(`Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero`). -/
theorem field_value_dep_of_linear (x : M)
    {F : (Π y : M, TangentSpace I y) → ℝ}
    (hlin : ∀ (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      CMDiff ∞ (T% X₁) → CMDiff ∞ (T% X₂) → CMDiff ∞ f₁ → CMDiff ∞ f₂ →
      F (f₁ • X₁ + f₂ • X₂) = f₁ x * F X₁ + f₂ x * F X₂)
    (hgerm : ∀ (X X' : Π y : M, TangentSpace I y), CMDiff ∞ (T% X) → CMDiff ∞ (T% X') →
      X =ᶠ[𝓝 x] X' → F X = F X')
    {X X' : Π y : M, TangentSpace I y} (hX : CMDiff ∞ (T% X)) (hX' : CMDiff ∞ (T% X'))
    (h : X x = X' x) : F X = F X' := by
  have hzero0 : F (0 : Π y : M, TangentSpace I y) = 0 := by
    have h0 := hlin (0 : Π y : M, TangentSpace I y) (0 : Π y : M, TangentSpace I y)
      (fun _ : M => (0 : ℝ)) (fun _ : M => (0 : ℝ))
      cmDiff_zeroField cmDiff_zeroField (contMDiff_const (c := (0 : ℝ)))
      (contMDiff_const (c := (0 : ℝ)))
    simpa using h0
  have hsmul : ∀ (f : M → ℝ) (X : Π y : M, TangentSpace I y), CMDiff ∞ f →
      CMDiff ∞ (T% X) → F (f • X) = f x * F X := by
    intro f X hf hX
    have h0 := hlin X (0 : Π y : M, TangentSpace I y) f (fun _ : M => (0 : ℝ)) hX
      cmDiff_zeroField hf (contMDiff_const (c := (0 : ℝ)))
    have hz : (fun _ : M => (0 : ℝ)) • (0 : Π y : M, TangentSpace I y) = 0 := by
      funext y; simp
    rw [hz, add_zero] at h0
    simpa using h0
  have hadd : ∀ (X Y : Π y : M, TangentSpace I y), CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) →
      F (X + Y) = F X + F Y := by
    intro X Y hX hY
    have h1 := hlin X Y (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ)) hX hY
      (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
    have hx : (fun _ : M => (1 : ℝ)) • X = X := by funext y; simp
    have hy : (fun _ : M => (1 : ℝ)) • Y = Y := by funext y; simp
    rw [hx, hy] at h1
    simpa using h1
  have hfin : ∀ (s : Finset (Fin (Module.finrank ℝ E)))
      (f : Fin (Module.finrank ℝ E) → M → ℝ)
      (Y : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
      (hf : ∀ i, CMDiff ∞ (f i)) (hY : ∀ i, CMDiff ∞ (T% (Y i))),
      F (∑ i ∈ s, f i • Y i) = ∑ i ∈ s, f i x * F (Y i) := by
    intro s f Y hf hY
    induction s using Finset.induction_on with
    | empty =>
        have h0 : (∑ i ∈ (∅ : Finset (Fin (Module.finrank ℝ E))), f i • Y i)
            = (0 : Π y : M, TangentSpace I y) := by simp
        rw [h0, Finset.sum_empty, hzero0]
    | insert i s hi ih =>
        have hs : CMDiff ∞ (T% (∑ j ∈ s, f j • Y j)) :=
          cmDiff_sum_smul (I := I) s f Y hf hY
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          hadd _ _ ((hf i).smul_section (hY i)) hs, hsmul (f i) (Y i) (hf i) (hY i), ih]
  have hzero : ∀ X : Π y : M, TangentSpace I y, CMDiff ∞ (T% X) → X x = 0 → F X = 0 := by
    intro X hX hXx
    obtain ⟨f, Y, hf, hY, hfx, hdecomp⟩ :=
      Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
        (I := I) hX hXx
    have hsum : CMDiff ∞ (T% (∑ i, f i • Y i)) :=
      cmDiff_sum_smul (I := I) Finset.univ f Y hf hY
    have h1 : F X = F (∑ i, f i • Y i) := hgerm X _ hX hsum hdecomp
    have h2 : F (∑ i, f i • Y i) = ∑ i, f i x * F (Y i) := hfin Finset.univ f Y hf hY
    have h3 : (∑ i, f i x * F (Y i)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hfx i, zero_mul]
    exact h1.trans (h2.trans h3)
  have hsub : CMDiff ∞ (T% (X - X')) := hX.sub_section hX'
  have h0 : (X - X') x = 0 := by rw [Pi.sub_apply, h, sub_self]
  have hz : F (X - X') = 0 := hzero (X - X') hsub h0
  have hsplit : X = (X - X') + X' := by funext y; simp
  rw [hsplit, hadd _ _ hsub hX', hz, zero_add]

/-! ## `C^∞(M)`-linearity of `cov2RmExt` in its field arguments -/

/-- `cov2RmExt g x u · A B C D` is `C^∞(M)`-linear in its second field argument `A`. -/
theorem cov2RmExt_linear_A (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A₁ A₂ B C D : Π y : M, TangentSpace I y} {f₁ f₂ : M → ℝ}
    (hV : CMDiff ∞ (T% V)) (hA₁ : CMDiff ∞ (T% A₁)) (hA₂ : CMDiff ∞ (T% A₂))
    (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    cov2RmExt g x u V (f₁ • A₁ + f₂ • A₂) B C D
      = f₁ x * cov2RmExt g x u V A₁ B C D
        + f₂ x * cov2RmExt g x u V A₂ B C D := by
  have hA : CMDiff ∞ (T% (f₁ • A₁ + f₂ • A₂)) :=
    (hf₁.smul_section hA₁).add_section (hf₂.smul_section hA₂)
  have hfA₁ : CMDiff ∞ (T% (f₁ • A₁)) := hf₁.smul_section hA₁
  have hfA₂ : CMDiff ∞ (T% (f₂ • A₂)) := hf₂.smul_section hA₂
  have hΦ₁ : CMDiff ∞ (fun y : M => covRm g y (V y) (A₁ y) (B y) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA₁ hB hC hD
  have hΦ₂ : CMDiff ∞ (fun y : M => covRm g y (V y) (A₂ y) (B y) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA₂ hB hC hD
  have hΦ : CMDiff ∞ (fun y : M => covRm g y (V y) ((f₁ • A₁ + f₂ • A₂) y) (B y) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hC hD
  have hF₁d : MDiffAt (fun y : M => covRm g y (V y) (A₁ y) (B y) (C y) (D y)) x :=
    hΦ₁.mdifferentiableAt (by simp)
  have hF₂d : MDiffAt (fun y : M => covRm g y (V y) (A₂ y) (B y) (C y) (D y)) x :=
    hΦ₂.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  -- pointwise linearity of the integrand
  have hpt : ∀ y : M, covRm g y (V y) ((f₁ • A₁ + f₂ • A₂) y) (B y) (C y) (D y)
      = f₁ y * covRm g y (V y) (A₁ y) (B y) (C y) (D y)
        + f₂ y * covRm g y (V y) (A₂ y) (B y) (C y) (D y) := by
    intro y
    rw [show (f₁ • A₁ + f₂ • A₂) y = f₁ y • A₁ y + f₂ y • A₂ y from rfl]
    exact covRm_linear_snd hLC g y (V y) (f₁ y) (f₂ y) (A₁ y) (A₂ y) (B y) (C y) (D y)
  -- the derivative part
  have hT : mvfderiv I (fun y : M => covRm g y (V y) ((f₁ • A₁ + f₂ • A₂) y)
        (B y) (C y) (D y)) x u
      = (f₁ x * mvfderiv I (fun y : M => covRm g y (V y) (A₁ y) (B y) (C y) (D y)) x u
          + mvfderiv I f₁ x u * covRm g x (V x) (A₁ x) (B x) (C x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => covRm g y (V y) (A₂ y) (B y) (C y) (D y)) x u
          + mvfderiv I f₂ x u * covRm g x (V x) (A₂ x) (B x) (C x) (D x)) := by
    have hfun : (fun y : M => covRm g y (V y) ((f₁ • A₁ + f₂ • A₂) y) (B y) (C y) (D y))
        = f₁ * (fun y : M => covRm g y (V y) (A₁ y) (B y) (C y) (D y))
          + f₂ * (fun y : M => covRm g y (V y) (A₂ y) (B y) (C y) (D y)) := by
      funext y
      exact hpt y
    rw [hfun, mvfderiv_add (hf₁d.mul hF₁d) (hf₂d.mul hF₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => covRm g y (V y) (A₁ y) (B y) (C y) (D y))
        hf₁d hF₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => covRm g y (V y) (A₂ y) (B y) (C y) (D y))
        hf₂d hF₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- the corrections
  have hlc : (lcOf g) (f₁ • A₁ + f₂ • A₂) x u
      = (lcOf g) (f₁ • A₁) x u + (lcOf g) (f₂ • A₂) x u := by
    have h := (lcOf g).isCovariantDerivativeOn.add (hfA₁.mdifferentiableAt (by simp))
      (hfA₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply]
  have hle₁ : (lcOf g) (f₁ • A₁) x u = f₁ x • (lcOf g) A₁ x u + mvfderiv I f₁ x u • A₁ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := A₁) (g := f₁)
      (hA₁.mdifferentiableAt (by simp)) (hf₁.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hle₂ : (lcOf g) (f₂ • A₂) x u = f₂ x • (lcOf g) A₂ x u + mvfderiv I f₂ x u • A₂ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := A₂) (g := f₂)
      (hA₂.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hcx : (f₁ • A₁ + f₂ • A₂) x = f₁ x • A₁ x + f₂ x • A₂ x := rfl
  have hc1 : covRm g x ((lcOf g) V x u) ((f₁ • A₁ + f₂ • A₂) x) (B x) (C x) (D x)
      = f₁ x * covRm g x ((lcOf g) V x u) (A₁ x) (B x) (C x) (D x)
        + f₂ x * covRm g x ((lcOf g) V x u) (A₂ x) (B x) (C x) (D x) := by
    rw [hcx]
    exact covRm_linear_snd hLC g x ((lcOf g) V x u) (f₁ x) (f₂ x) (A₁ x) (A₂ x) (B x) (C x) (D x)
  have hc2 : covRm g x (V x) ((lcOf g) (f₁ • A₁ + f₂ • A₂) x u) (B x) (C x) (D x)
      = (f₁ x * covRm g x (V x) ((lcOf g) A₁ x u) (B x) (C x) (D x)
          + mvfderiv I f₁ x u * covRm g x (V x) (A₁ x) (B x) (C x) (D x))
        + (f₂ x * covRm g x (V x) ((lcOf g) A₂ x u) (B x) (C x) (D x)
          + mvfderiv I f₂ x u * covRm g x (V x) (A₂ x) (B x) (C x) (D x)) := by
    have hadd2 : ∀ (X Y : TangentSpace I x),
        covRm g x (V x) (X + Y) (B x) (C x) (D x)
          = covRm g x (V x) X (B x) (C x) (D x) + covRm g x (V x) Y (B x) (C x) (D x) := by
      intro X Y
      have h := covRm_linear_snd hLC g x (V x) 1 1 X Y (B x) (C x) (D x)
      simpa using h
    rw [hlc, hle₁, hle₂]
    rw [hadd2 (f₁ x • (lcOf g) A₁ x u + mvfderiv I f₁ x u • A₁ x)
        (f₂ x • (lcOf g) A₂ x u + mvfderiv I f₂ x u • A₂ x)]
    rw [covRm_linear_snd hLC g x (V x) (f₁ x) (mvfderiv I f₁ x u)
        ((lcOf g) A₁ x u) (A₁ x) (B x) (C x) (D x)]
    rw [covRm_linear_snd hLC g x (V x) (f₂ x) (mvfderiv I f₂ x u)
        ((lcOf g) A₂ x u) (A₂ x) (B x) (C x) (D x)]
  have hc3 : covRm g x (V x) ((f₁ • A₁ + f₂ • A₂) x) ((lcOf g) B x u) (C x) (D x)
      = f₁ x * covRm g x (V x) (A₁ x) ((lcOf g) B x u) (C x) (D x)
        + f₂ x * covRm g x (V x) (A₂ x) ((lcOf g) B x u) (C x) (D x) := by
    rw [hcx]
    exact covRm_linear_snd hLC g x (V x) (f₁ x) (f₂ x) (A₁ x) (A₂ x) ((lcOf g) B x u) (C x) (D x)
  have hc4 : covRm g x (V x) ((f₁ • A₁ + f₂ • A₂) x) (B x) ((lcOf g) C x u) (D x)
      = f₁ x * covRm g x (V x) (A₁ x) (B x) ((lcOf g) C x u) (D x)
        + f₂ x * covRm g x (V x) (A₂ x) (B x) ((lcOf g) C x u) (D x) := by
    rw [hcx]
    exact covRm_linear_snd hLC g x (V x) (f₁ x) (f₂ x) (A₁ x) (A₂ x) (B x) ((lcOf g) C x u) (D x)
  have hc5 : covRm g x (V x) ((f₁ • A₁ + f₂ • A₂) x) (B x) (C x) ((lcOf g) D x u)
      = f₁ x * covRm g x (V x) (A₁ x) (B x) (C x) ((lcOf g) D x u)
        + f₂ x * covRm g x (V x) (A₂ x) (B x) (C x) ((lcOf g) D x u) := by
    rw [hcx]
    exact covRm_linear_snd hLC g x (V x) (f₁ x) (f₂ x) (A₁ x) (A₂ x) (B x) (C x) ((lcOf g) D x u)
  simp only [cov2RmExt]
  rw [hT, hc1, hc2, hc3, hc4, hc5]
  ring

/-- `cov2RmExt g x u V · B C D` is `C^∞(M)`-linear in its first field argument `V`
(the direction field). -/
theorem cov2RmExt_linear_V (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V₁ V₂ A B C D : Π y : M, TangentSpace I y} {f₁ f₂ : M → ℝ}
    (hV₁ : CMDiff ∞ (T% V₁)) (hV₂ : CMDiff ∞ (T% V₂))
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    cov2RmExt g x u (f₁ • V₁ + f₂ • V₂) A B C D
      = f₁ x * cov2RmExt g x u V₁ A B C D
        + f₂ x * cov2RmExt g x u V₂ A B C D := by
  have hV : CMDiff ∞ (T% (f₁ • V₁ + f₂ • V₂)) :=
    (hf₁.smul_section hV₁).add_section (hf₂.smul_section hV₂)
  have hfV₁ : CMDiff ∞ (T% (f₁ • V₁)) := hf₁.smul_section hV₁
  have hfV₂ : CMDiff ∞ (T% (f₂ • V₂)) := hf₂.smul_section hV₂
  have hΦ₁ : CMDiff ∞ (fun y : M => covRm g y (V₁ y) (A y) (B y) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV₁ hA hB hC hD
  have hΦ₂ : CMDiff ∞ (fun y : M => covRm g y (V₂ y) (A y) (B y) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV₂ hA hB hC hD
  have hΦ : CMDiff ∞ (fun y : M => covRm g y ((f₁ • V₁ + f₂ • V₂) y) (A y) (B y) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hC hD
  have hF₁d : MDiffAt (fun y : M => covRm g y (V₁ y) (A y) (B y) (C y) (D y)) x :=
    hΦ₁.mdifferentiableAt (by simp)
  have hF₂d : MDiffAt (fun y : M => covRm g y (V₂ y) (A y) (B y) (C y) (D y)) x :=
    hΦ₂.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  have hpt : ∀ y : M, covRm g y ((f₁ • V₁ + f₂ • V₂) y) (A y) (B y) (C y) (D y)
      = f₁ y * covRm g y (V₁ y) (A y) (B y) (C y) (D y)
        + f₂ y * covRm g y (V₂ y) (A y) (B y) (C y) (D y) := by
    intro y
    rw [show (f₁ • V₁ + f₂ • V₂) y = f₁ y • V₁ y + f₂ y • V₂ y from rfl]
    exact covRm_linear_fst hLC g y (f₁ y) (f₂ y) (V₁ y) (V₂ y) (A y) (B y) (C y) (D y)
  have hT : mvfderiv I (fun y : M => covRm g y ((f₁ • V₁ + f₂ • V₂) y)
        (A y) (B y) (C y) (D y)) x u
      = (f₁ x * mvfderiv I (fun y : M => covRm g y (V₁ y) (A y) (B y) (C y) (D y)) x u
          + mvfderiv I f₁ x u * covRm g x (V₁ x) (A x) (B x) (C x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => covRm g y (V₂ y) (A y) (B y) (C y) (D y)) x u
          + mvfderiv I f₂ x u * covRm g x (V₂ x) (A x) (B x) (C x) (D x)) := by
    have hfun : (fun y : M => covRm g y ((f₁ • V₁ + f₂ • V₂) y) (A y) (B y) (C y) (D y))
        = f₁ * (fun y : M => covRm g y (V₁ y) (A y) (B y) (C y) (D y))
          + f₂ * (fun y : M => covRm g y (V₂ y) (A y) (B y) (C y) (D y)) := by
      funext y
      exact hpt y
    rw [hfun, mvfderiv_add (hf₁d.mul hF₁d) (hf₂d.mul hF₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => covRm g y (V₁ y) (A y) (B y) (C y) (D y))
        hf₁d hF₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => covRm g y (V₂ y) (A y) (B y) (C y) (D y))
        hf₂d hF₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hlc : (lcOf g) (f₁ • V₁ + f₂ • V₂) x u
      = (lcOf g) (f₁ • V₁) x u + (lcOf g) (f₂ • V₂) x u := by
    have h := (lcOf g).isCovariantDerivativeOn.add (hfV₁.mdifferentiableAt (by simp))
      (hfV₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply]
  have hle₁ : (lcOf g) (f₁ • V₁) x u = f₁ x • (lcOf g) V₁ x u + mvfderiv I f₁ x u • V₁ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := V₁) (g := f₁)
      (hV₁.mdifferentiableAt (by simp)) (hf₁.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hle₂ : (lcOf g) (f₂ • V₂) x u = f₂ x • (lcOf g) V₂ x u + mvfderiv I f₂ x u • V₂ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := V₂) (g := f₂)
      (hV₂.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hcx : (f₁ • V₁ + f₂ • V₂) x = f₁ x • V₁ x + f₂ x • V₂ x := rfl
  have hadd1 : ∀ (Z W : TangentSpace I x),
      covRm g x (Z + W) (A x) (B x) (C x) (D x)
        = covRm g x Z (A x) (B x) (C x) (D x) + covRm g x W (A x) (B x) (C x) (D x) := by
    intro Z W
    have h := covRm_linear_fst hLC g x 1 1 Z W (A x) (B x) (C x) (D x)
    simpa using h
  have hc1 : covRm g x ((lcOf g) (f₁ • V₁ + f₂ • V₂) x u) (A x) (B x) (C x) (D x)
      = (f₁ x * covRm g x ((lcOf g) V₁ x u) (A x) (B x) (C x) (D x)
          + mvfderiv I f₁ x u * covRm g x (V₁ x) (A x) (B x) (C x) (D x))
        + (f₂ x * covRm g x ((lcOf g) V₂ x u) (A x) (B x) (C x) (D x)
          + mvfderiv I f₂ x u * covRm g x (V₂ x) (A x) (B x) (C x) (D x)) := by
    rw [hlc, hle₁, hle₂]
    rw [hadd1 (f₁ x • (lcOf g) V₁ x u + mvfderiv I f₁ x u • V₁ x)
        (f₂ x • (lcOf g) V₂ x u + mvfderiv I f₂ x u • V₂ x)]
    rw [covRm_linear_fst hLC g x (f₁ x) (mvfderiv I f₁ x u)
        ((lcOf g) V₁ x u) (V₁ x) (A x) (B x) (C x) (D x)]
    rw [covRm_linear_fst hLC g x (f₂ x) (mvfderiv I f₂ x u)
        ((lcOf g) V₂ x u) (V₂ x) (A x) (B x) (C x) (D x)]
  have hc2 : covRm g x ((f₁ • V₁ + f₂ • V₂) x) ((lcOf g) A x u) (B x) (C x) (D x)
      = f₁ x * covRm g x (V₁ x) ((lcOf g) A x u) (B x) (C x) (D x)
        + f₂ x * covRm g x (V₂ x) ((lcOf g) A x u) (B x) (C x) (D x) := by
    rw [hcx]
    exact covRm_linear_fst hLC g x (f₁ x) (f₂ x) (V₁ x) (V₂ x) ((lcOf g) A x u) (B x) (C x) (D x)
  have hc3 : covRm g x ((f₁ • V₁ + f₂ • V₂) x) (A x) ((lcOf g) B x u) (C x) (D x)
      = f₁ x * covRm g x (V₁ x) (A x) ((lcOf g) B x u) (C x) (D x)
        + f₂ x * covRm g x (V₂ x) (A x) ((lcOf g) B x u) (C x) (D x) := by
    rw [hcx]
    exact covRm_linear_fst hLC g x (f₁ x) (f₂ x) (V₁ x) (V₂ x) (A x) ((lcOf g) B x u) (C x) (D x)
  have hc4 : covRm g x ((f₁ • V₁ + f₂ • V₂) x) (A x) (B x) ((lcOf g) C x u) (D x)
      = f₁ x * covRm g x (V₁ x) (A x) (B x) ((lcOf g) C x u) (D x)
        + f₂ x * covRm g x (V₂ x) (A x) (B x) ((lcOf g) C x u) (D x) := by
    rw [hcx]
    exact covRm_linear_fst hLC g x (f₁ x) (f₂ x) (V₁ x) (V₂ x) (A x) (B x) ((lcOf g) C x u) (D x)
  have hc5 : covRm g x ((f₁ • V₁ + f₂ • V₂) x) (A x) (B x) (C x) ((lcOf g) D x u)
      = f₁ x * covRm g x (V₁ x) (A x) (B x) (C x) ((lcOf g) D x u)
        + f₂ x * covRm g x (V₂ x) (A x) (B x) (C x) ((lcOf g) D x u) := by
    rw [hcx]
    exact covRm_linear_fst hLC g x (f₁ x) (f₂ x) (V₁ x) (V₂ x) (A x) (B x) (C x) ((lcOf g) D x u)
  simp only [cov2RmExt]
  rw [hT, hc1, hc2, hc3, hc4, hc5]
  ring

/-- `cov2RmExt g x u V A · C D` is `C^∞(M)`-linear in its fourth field argument `B`. -/
theorem cov2RmExt_linear_B (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A B₁ B₂ C D : Π y : M, TangentSpace I y} {f₁ f₂ : M → ℝ}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A))
    (hB₁ : CMDiff ∞ (T% B₁)) (hB₂ : CMDiff ∞ (T% B₂))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    cov2RmExt g x u V A (f₁ • B₁ + f₂ • B₂) C D
      = f₁ x * cov2RmExt g x u V A B₁ C D
        + f₂ x * cov2RmExt g x u V A B₂ C D := by
  have hB : CMDiff ∞ (T% (f₁ • B₁ + f₂ • B₂)) :=
    (hf₁.smul_section hB₁).add_section (hf₂.smul_section hB₂)
  have hfB₁ : CMDiff ∞ (T% (f₁ • B₁)) := hf₁.smul_section hB₁
  have hfB₂ : CMDiff ∞ (T% (f₂ • B₂)) := hf₂.smul_section hB₂
  have hΦ₁ : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B₁ y) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB₁ hC hD
  have hΦ₂ : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B₂ y) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB₂ hC hD
  have hΦ : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) ((f₁ • B₁ + f₂ • B₂) y) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hC hD
  have hF₁d : MDiffAt (fun y : M => covRm g y (V y) (A y) (B₁ y) (C y) (D y)) x :=
    hΦ₁.mdifferentiableAt (by simp)
  have hF₂d : MDiffAt (fun y : M => covRm g y (V y) (A y) (B₂ y) (C y) (D y)) x :=
    hΦ₂.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  have hpt : ∀ y : M, covRm g y (V y) (A y) ((f₁ • B₁ + f₂ • B₂) y) (C y) (D y)
      = f₁ y * covRm g y (V y) (A y) (B₁ y) (C y) (D y)
        + f₂ y * covRm g y (V y) (A y) (B₂ y) (C y) (D y) := by
    intro y
    rw [show (f₁ • B₁ + f₂ • B₂) y = f₁ y • B₁ y + f₂ y • B₂ y from rfl]
    exact covRm_linear_thd hLC g y (V y) (A y) (f₁ y) (f₂ y) (B₁ y) (B₂ y) (C y) (D y)
  have hT : mvfderiv I (fun y : M => covRm g y (V y) (A y) ((f₁ • B₁ + f₂ • B₂) y)
        (C y) (D y)) x u
      = (f₁ x * mvfderiv I (fun y : M => covRm g y (V y) (A y) (B₁ y) (C y) (D y)) x u
          + mvfderiv I f₁ x u * covRm g x (V x) (A x) (B₁ x) (C x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => covRm g y (V y) (A y) (B₂ y) (C y) (D y)) x u
          + mvfderiv I f₂ x u * covRm g x (V x) (A x) (B₂ x) (C x) (D x)) := by
    have hfun : (fun y : M => covRm g y (V y) (A y) ((f₁ • B₁ + f₂ • B₂) y) (C y) (D y))
        = f₁ * (fun y : M => covRm g y (V y) (A y) (B₁ y) (C y) (D y))
          + f₂ * (fun y : M => covRm g y (V y) (A y) (B₂ y) (C y) (D y)) := by
      funext y
      exact hpt y
    rw [hfun, mvfderiv_add (hf₁d.mul hF₁d) (hf₂d.mul hF₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => covRm g y (V y) (A y) (B₁ y) (C y) (D y))
        hf₁d hF₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => covRm g y (V y) (A y) (B₂ y) (C y) (D y))
        hf₂d hF₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hlc : (lcOf g) (f₁ • B₁ + f₂ • B₂) x u
      = (lcOf g) (f₁ • B₁) x u + (lcOf g) (f₂ • B₂) x u := by
    have h := (lcOf g).isCovariantDerivativeOn.add (hfB₁.mdifferentiableAt (by simp))
      (hfB₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply]
  have hle₁ : (lcOf g) (f₁ • B₁) x u = f₁ x • (lcOf g) B₁ x u + mvfderiv I f₁ x u • B₁ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := B₁) (g := f₁)
      (hB₁.mdifferentiableAt (by simp)) (hf₁.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hle₂ : (lcOf g) (f₂ • B₂) x u = f₂ x • (lcOf g) B₂ x u + mvfderiv I f₂ x u • B₂ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := B₂) (g := f₂)
      (hB₂.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hcx : (f₁ • B₁ + f₂ • B₂) x = f₁ x • B₁ x + f₂ x • B₂ x := rfl
  have hadd3 : ∀ (Z W : TangentSpace I x),
      covRm g x (V x) (A x) (Z + W) (C x) (D x)
        = covRm g x (V x) (A x) Z (C x) (D x) + covRm g x (V x) (A x) W (C x) (D x) := by
    intro Z W
    have h := covRm_linear_thd hLC g x (V x) (A x) 1 1 Z W (C x) (D x)
    simpa using h
  have hc1 : covRm g x ((lcOf g) V x u) (A x) ((f₁ • B₁ + f₂ • B₂) x) (C x) (D x)
      = f₁ x * covRm g x ((lcOf g) V x u) (A x) (B₁ x) (C x) (D x)
        + f₂ x * covRm g x ((lcOf g) V x u) (A x) (B₂ x) (C x) (D x) := by
    rw [hcx]
    exact covRm_linear_thd hLC g x ((lcOf g) V x u) (A x) (f₁ x) (f₂ x) (B₁ x) (B₂ x) (C x) (D x)
  have hc2 : covRm g x (V x) ((lcOf g) A x u) ((f₁ • B₁ + f₂ • B₂) x) (C x) (D x)
      = f₁ x * covRm g x (V x) ((lcOf g) A x u) (B₁ x) (C x) (D x)
        + f₂ x * covRm g x (V x) ((lcOf g) A x u) (B₂ x) (C x) (D x) := by
    rw [hcx]
    exact covRm_linear_thd hLC g x (V x) ((lcOf g) A x u) (f₁ x) (f₂ x) (B₁ x) (B₂ x) (C x) (D x)
  have hc3 : covRm g x (V x) (A x) ((lcOf g) (f₁ • B₁ + f₂ • B₂) x u) (C x) (D x)
      = (f₁ x * covRm g x (V x) (A x) ((lcOf g) B₁ x u) (C x) (D x)
          + mvfderiv I f₁ x u * covRm g x (V x) (A x) (B₁ x) (C x) (D x))
        + (f₂ x * covRm g x (V x) (A x) ((lcOf g) B₂ x u) (C x) (D x)
          + mvfderiv I f₂ x u * covRm g x (V x) (A x) (B₂ x) (C x) (D x)) := by
    rw [hlc, hle₁, hle₂]
    rw [hadd3 (f₁ x • (lcOf g) B₁ x u + mvfderiv I f₁ x u • B₁ x)
        (f₂ x • (lcOf g) B₂ x u + mvfderiv I f₂ x u • B₂ x)]
    rw [covRm_linear_thd hLC g x (V x) (A x) (f₁ x) (mvfderiv I f₁ x u)
        ((lcOf g) B₁ x u) (B₁ x) (C x) (D x)]
    rw [covRm_linear_thd hLC g x (V x) (A x) (f₂ x) (mvfderiv I f₂ x u)
        ((lcOf g) B₂ x u) (B₂ x) (C x) (D x)]
  have hc4 : covRm g x (V x) (A x) ((f₁ • B₁ + f₂ • B₂) x) ((lcOf g) C x u) (D x)
      = f₁ x * covRm g x (V x) (A x) (B₁ x) ((lcOf g) C x u) (D x)
        + f₂ x * covRm g x (V x) (A x) (B₂ x) ((lcOf g) C x u) (D x) := by
    rw [hcx]
    exact covRm_linear_thd hLC g x (V x) (A x) (f₁ x) (f₂ x) (B₁ x) (B₂ x) ((lcOf g) C x u) (D x)
  have hc5 : covRm g x (V x) (A x) ((f₁ • B₁ + f₂ • B₂) x) (C x) ((lcOf g) D x u)
      = f₁ x * covRm g x (V x) (A x) (B₁ x) (C x) ((lcOf g) D x u)
        + f₂ x * covRm g x (V x) (A x) (B₂ x) (C x) ((lcOf g) D x u) := by
    rw [hcx]
    exact covRm_linear_thd hLC g x (V x) (A x) (f₁ x) (f₂ x) (B₁ x) (B₂ x) (C x) ((lcOf g) D x u)
  simp only [cov2RmExt]
  rw [hT, hc1, hc2, hc3, hc4, hc5]
  ring

/-- `cov2RmExt g x u V A B · D` is `C^∞(M)`-linear in its fifth field argument `C`. -/
theorem cov2RmExt_linear_C (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A B C₁ C₂ D : Π y : M, TangentSpace I y} {f₁ f₂ : M → ℝ}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC₁ : CMDiff ∞ (T% C₁)) (hC₂ : CMDiff ∞ (T% C₂))
    (hD : CMDiff ∞ (T% D))
    (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    cov2RmExt g x u V A B (f₁ • C₁ + f₂ • C₂) D
      = f₁ x * cov2RmExt g x u V A B C₁ D
        + f₂ x * cov2RmExt g x u V A B C₂ D := by
  have hC : CMDiff ∞ (T% (f₁ • C₁ + f₂ • C₂)) :=
    (hf₁.smul_section hC₁).add_section (hf₂.smul_section hC₂)
  have hfC₁ : CMDiff ∞ (T% (f₁ • C₁)) := hf₁.smul_section hC₁
  have hfC₂ : CMDiff ∞ (T% (f₂ • C₂)) := hf₂.smul_section hC₂
  have hΦ₁ : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B y) (C₁ y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hC₁ hD
  have hΦ₂ : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B y) (C₂ y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hC₂ hD
  have hΦ : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B y) ((f₁ • C₁ + f₂ • C₂) y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hC hD
  have hF₁d : MDiffAt (fun y : M => covRm g y (V y) (A y) (B y) (C₁ y) (D y)) x :=
    hΦ₁.mdifferentiableAt (by simp)
  have hF₂d : MDiffAt (fun y : M => covRm g y (V y) (A y) (B y) (C₂ y) (D y)) x :=
    hΦ₂.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  have hpt : ∀ y : M, covRm g y (V y) (A y) (B y) ((f₁ • C₁ + f₂ • C₂) y) (D y)
      = f₁ y * covRm g y (V y) (A y) (B y) (C₁ y) (D y)
        + f₂ y * covRm g y (V y) (A y) (B y) (C₂ y) (D y) := by
    intro y
    rw [show (f₁ • C₁ + f₂ • C₂) y = f₁ y • C₁ y + f₂ y • C₂ y from rfl]
    exact covRm_linear_fth hLC g y (V y) (A y) (B y) (f₁ y) (f₂ y) (C₁ y) (C₂ y) (D y)
  have hT : mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) ((f₁ • C₁ + f₂ • C₂) y)
        (D y)) x u
      = (f₁ x * mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C₁ y) (D y)) x u
          + mvfderiv I f₁ x u * covRm g x (V x) (A x) (B x) (C₁ x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C₂ y) (D y)) x u
          + mvfderiv I f₂ x u * covRm g x (V x) (A x) (B x) (C₂ x) (D x)) := by
    have hfun : (fun y : M => covRm g y (V y) (A y) (B y) ((f₁ • C₁ + f₂ • C₂) y) (D y))
        = f₁ * (fun y : M => covRm g y (V y) (A y) (B y) (C₁ y) (D y))
          + f₂ * (fun y : M => covRm g y (V y) (A y) (B y) (C₂ y) (D y)) := by
      funext y
      exact hpt y
    rw [hfun, mvfderiv_add (hf₁d.mul hF₁d) (hf₂d.mul hF₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => covRm g y (V y) (A y) (B y) (C₁ y) (D y))
        hf₁d hF₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => covRm g y (V y) (A y) (B y) (C₂ y) (D y))
        hf₂d hF₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hlc : (lcOf g) (f₁ • C₁ + f₂ • C₂) x u
      = (lcOf g) (f₁ • C₁) x u + (lcOf g) (f₂ • C₂) x u := by
    have h := (lcOf g).isCovariantDerivativeOn.add (hfC₁.mdifferentiableAt (by simp))
      (hfC₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply]
  have hle₁ : (lcOf g) (f₁ • C₁) x u = f₁ x • (lcOf g) C₁ x u + mvfderiv I f₁ x u • C₁ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := C₁) (g := f₁)
      (hC₁.mdifferentiableAt (by simp)) (hf₁.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hle₂ : (lcOf g) (f₂ • C₂) x u = f₂ x • (lcOf g) C₂ x u + mvfderiv I f₂ x u • C₂ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := C₂) (g := f₂)
      (hC₂.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hcx : (f₁ • C₁ + f₂ • C₂) x = f₁ x • C₁ x + f₂ x • C₂ x := rfl
  have hadd4 : ∀ (Z W : TangentSpace I x),
      covRm g x (V x) (A x) (B x) (Z + W) (D x)
        = covRm g x (V x) (A x) (B x) Z (D x) + covRm g x (V x) (A x) (B x) W (D x) := by
    intro Z W
    have h := covRm_linear_fth hLC g x (V x) (A x) (B x) 1 1 Z W (D x)
    simpa using h
  have hc1 : covRm g x ((lcOf g) V x u) (A x) (B x) ((f₁ • C₁ + f₂ • C₂) x) (D x)
      = f₁ x * covRm g x ((lcOf g) V x u) (A x) (B x) (C₁ x) (D x)
        + f₂ x * covRm g x ((lcOf g) V x u) (A x) (B x) (C₂ x) (D x) := by
    rw [hcx]
    exact covRm_linear_fth hLC g x ((lcOf g) V x u) (A x) (B x) (f₁ x) (f₂ x) (C₁ x) (C₂ x) (D x)
  have hc2 : covRm g x (V x) ((lcOf g) A x u) (B x) ((f₁ • C₁ + f₂ • C₂) x) (D x)
      = f₁ x * covRm g x (V x) ((lcOf g) A x u) (B x) (C₁ x) (D x)
        + f₂ x * covRm g x (V x) ((lcOf g) A x u) (B x) (C₂ x) (D x) := by
    rw [hcx]
    exact covRm_linear_fth hLC g x (V x) ((lcOf g) A x u) (B x) (f₁ x) (f₂ x) (C₁ x) (C₂ x) (D x)
  have hc3 : covRm g x (V x) (A x) ((lcOf g) B x u) ((f₁ • C₁ + f₂ • C₂) x) (D x)
      = f₁ x * covRm g x (V x) (A x) ((lcOf g) B x u) (C₁ x) (D x)
        + f₂ x * covRm g x (V x) (A x) ((lcOf g) B x u) (C₂ x) (D x) := by
    rw [hcx]
    exact covRm_linear_fth hLC g x (V x) (A x) ((lcOf g) B x u) (f₁ x) (f₂ x) (C₁ x) (C₂ x) (D x)
  have hc4 : covRm g x (V x) (A x) (B x) ((lcOf g) (f₁ • C₁ + f₂ • C₂) x u) (D x)
      = (f₁ x * covRm g x (V x) (A x) (B x) ((lcOf g) C₁ x u) (D x)
          + mvfderiv I f₁ x u * covRm g x (V x) (A x) (B x) (C₁ x) (D x))
        + (f₂ x * covRm g x (V x) (A x) (B x) ((lcOf g) C₂ x u) (D x)
          + mvfderiv I f₂ x u * covRm g x (V x) (A x) (B x) (C₂ x) (D x)) := by
    rw [hlc, hle₁, hle₂]
    rw [hadd4 (f₁ x • (lcOf g) C₁ x u + mvfderiv I f₁ x u • C₁ x)
        (f₂ x • (lcOf g) C₂ x u + mvfderiv I f₂ x u • C₂ x)]
    rw [covRm_linear_fth hLC g x (V x) (A x) (B x) (f₁ x) (mvfderiv I f₁ x u)
        ((lcOf g) C₁ x u) (C₁ x) (D x)]
    rw [covRm_linear_fth hLC g x (V x) (A x) (B x) (f₂ x) (mvfderiv I f₂ x u)
        ((lcOf g) C₂ x u) (C₂ x) (D x)]
  have hc5 : covRm g x (V x) (A x) (B x) ((f₁ • C₁ + f₂ • C₂) x) ((lcOf g) D x u)
      = f₁ x * covRm g x (V x) (A x) (B x) (C₁ x) ((lcOf g) D x u)
        + f₂ x * covRm g x (V x) (A x) (B x) (C₂ x) ((lcOf g) D x u) := by
    rw [hcx]
    exact covRm_linear_fth hLC g x (V x) (A x) (B x) (f₁ x) (f₂ x) (C₁ x) (C₂ x) ((lcOf g) D x u)
  simp only [cov2RmExt]
  rw [hT, hc1, hc2, hc3, hc4, hc5]
  ring

/-- `cov2RmExt g x u V A B C ·` is `C^∞(M)`-linear in its sixth field argument `D`. -/
theorem cov2RmExt_linear_D (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A B C D₁ D₂ : Π y : M, TangentSpace I y} {f₁ f₂ : M → ℝ}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD₁ : CMDiff ∞ (T% D₁)) (hD₂ : CMDiff ∞ (T% D₂))
    (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    cov2RmExt g x u V A B C (f₁ • D₁ + f₂ • D₂)
      = f₁ x * cov2RmExt g x u V A B C D₁
        + f₂ x * cov2RmExt g x u V A B C D₂ := by
  have hD : CMDiff ∞ (T% (f₁ • D₁ + f₂ • D₂)) :=
    (hf₁.smul_section hD₁).add_section (hf₂.smul_section hD₂)
  have hfD₁ : CMDiff ∞ (T% (f₁ • D₁)) := hf₁.smul_section hD₁
  have hfD₂ : CMDiff ∞ (T% (f₂ • D₂)) := hf₂.smul_section hD₂
  have hΦ₁ : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D₁ y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hC hD₁
  have hΦ₂ : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D₂ y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hC hD₂
  have hΦ : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B y) (C y) ((f₁ • D₁ + f₂ • D₂) y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hC hD
  have hF₁d : MDiffAt (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D₁ y)) x :=
    hΦ₁.mdifferentiableAt (by simp)
  have hF₂d : MDiffAt (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D₂ y)) x :=
    hΦ₂.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  have hpt : ∀ y : M, covRm g y (V y) (A y) (B y) (C y) ((f₁ • D₁ + f₂ • D₂) y)
      = f₁ y * covRm g y (V y) (A y) (B y) (C y) (D₁ y)
        + f₂ y * covRm g y (V y) (A y) (B y) (C y) (D₂ y) := by
    intro y
    rw [show (f₁ • D₁ + f₂ • D₂) y = f₁ y • D₁ y + f₂ y • D₂ y from rfl]
    exact covRm_linear_fif hLC g y (V y) (A y) (B y) (C y) (f₁ y) (f₂ y) (D₁ y) (D₂ y)
  have hT : mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y)
        ((f₁ • D₁ + f₂ • D₂) y)) x u
      = (f₁ x * mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D₁ y)) x u
          + mvfderiv I f₁ x u * covRm g x (V x) (A x) (B x) (C x) (D₁ x))
        + (f₂ x * mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D₂ y)) x u
          + mvfderiv I f₂ x u * covRm g x (V x) (A x) (B x) (C x) (D₂ x)) := by
    have hfun : (fun y : M => covRm g y (V y) (A y) (B y) (C y) ((f₁ • D₁ + f₂ • D₂) y))
        = f₁ * (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D₁ y))
          + f₂ * (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D₂ y)) := by
      funext y
      exact hpt y
    rw [hfun, mvfderiv_add (hf₁d.mul hF₁d) (hf₂d.mul hF₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => covRm g y (V y) (A y) (B y) (C y) (D₁ y))
        hf₁d hF₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => covRm g y (V y) (A y) (B y) (C y) (D₂ y))
        hf₂d hF₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hlc : (lcOf g) (f₁ • D₁ + f₂ • D₂) x u
      = (lcOf g) (f₁ • D₁) x u + (lcOf g) (f₂ • D₂) x u := by
    have h := (lcOf g).isCovariantDerivativeOn.add (hfD₁.mdifferentiableAt (by simp))
      (hfD₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply]
  have hle₁ : (lcOf g) (f₁ • D₁) x u = f₁ x • (lcOf g) D₁ x u + mvfderiv I f₁ x u • D₁ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := D₁) (g := f₁)
      (hD₁.mdifferentiableAt (by simp)) (hf₁.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hle₂ : (lcOf g) (f₂ • D₂) x u = f₂ x • (lcOf g) D₂ x u + mvfderiv I f₂ x u • D₂ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := D₂) (g := f₂)
      (hD₂.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L u) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hcx : (f₁ • D₁ + f₂ • D₂) x = f₁ x • D₁ x + f₂ x • D₂ x := rfl
  have hadd5 : ∀ (Z W : TangentSpace I x),
      covRm g x (V x) (A x) (B x) (C x) (Z + W)
        = covRm g x (V x) (A x) (B x) (C x) Z + covRm g x (V x) (A x) (B x) (C x) W := by
    intro Z W
    have h := covRm_linear_fif hLC g x (V x) (A x) (B x) (C x) 1 1 Z W
    simpa using h
  have hc1 : covRm g x ((lcOf g) V x u) (A x) (B x) (C x) ((f₁ • D₁ + f₂ • D₂) x)
      = f₁ x * covRm g x ((lcOf g) V x u) (A x) (B x) (C x) (D₁ x)
        + f₂ x * covRm g x ((lcOf g) V x u) (A x) (B x) (C x) (D₂ x) := by
    rw [hcx]
    exact covRm_linear_fif hLC g x ((lcOf g) V x u) (A x) (B x) (C x) (f₁ x) (f₂ x) (D₁ x) (D₂ x)
  have hc2 : covRm g x (V x) ((lcOf g) A x u) (B x) (C x) ((f₁ • D₁ + f₂ • D₂) x)
      = f₁ x * covRm g x (V x) ((lcOf g) A x u) (B x) (C x) (D₁ x)
        + f₂ x * covRm g x (V x) ((lcOf g) A x u) (B x) (C x) (D₂ x) := by
    rw [hcx]
    exact covRm_linear_fif hLC g x (V x) ((lcOf g) A x u) (B x) (C x) (f₁ x) (f₂ x) (D₁ x) (D₂ x)
  have hc3 : covRm g x (V x) (A x) ((lcOf g) B x u) (C x) ((f₁ • D₁ + f₂ • D₂) x)
      = f₁ x * covRm g x (V x) (A x) ((lcOf g) B x u) (C x) (D₁ x)
        + f₂ x * covRm g x (V x) (A x) ((lcOf g) B x u) (C x) (D₂ x) := by
    rw [hcx]
    exact covRm_linear_fif hLC g x (V x) (A x) ((lcOf g) B x u) (C x) (f₁ x) (f₂ x) (D₁ x) (D₂ x)
  have hc4 : covRm g x (V x) (A x) (B x) ((lcOf g) C x u) ((f₁ • D₁ + f₂ • D₂) x)
      = f₁ x * covRm g x (V x) (A x) (B x) ((lcOf g) C x u) (D₁ x)
        + f₂ x * covRm g x (V x) (A x) (B x) ((lcOf g) C x u) (D₂ x) := by
    rw [hcx]
    exact covRm_linear_fif hLC g x (V x) (A x) (B x) ((lcOf g) C x u) (f₁ x) (f₂ x) (D₁ x) (D₂ x)
  have hc5 : covRm g x (V x) (A x) (B x) (C x) ((lcOf g) (f₁ • D₁ + f₂ • D₂) x u)
      = (f₁ x * covRm g x (V x) (A x) (B x) (C x) ((lcOf g) D₁ x u)
          + mvfderiv I f₁ x u * covRm g x (V x) (A x) (B x) (C x) (D₁ x))
        + (f₂ x * covRm g x (V x) (A x) (B x) (C x) ((lcOf g) D₂ x u)
          + mvfderiv I f₂ x u * covRm g x (V x) (A x) (B x) (C x) (D₂ x)) := by
    rw [hlc, hle₁, hle₂]
    rw [hadd5 (f₁ x • (lcOf g) D₁ x u + mvfderiv I f₁ x u • D₁ x)
        (f₂ x • (lcOf g) D₂ x u + mvfderiv I f₂ x u • D₂ x)]
    rw [covRm_linear_fif hLC g x (V x) (A x) (B x) (C x) (f₁ x) (mvfderiv I f₁ x u)
        ((lcOf g) D₁ x u) (D₁ x)]
    rw [covRm_linear_fif hLC g x (V x) (A x) (B x) (C x) (f₂ x) (mvfderiv I f₂ x u)
        ((lcOf g) D₂ x u) (D₂ x)]
  simp only [cov2RmExt]
  rw [hT, hc1, hc2, hc3, hc4, hc5]
  ring

/-- `cov2RmExt g x u · A B C D` is unchanged by changing its first (direction) field away from `x`. -/
theorem cov2RmExt_germ_V (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V V' A B C D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hV' : CMDiff ∞ (T% V')) (hA : CMDiff ∞ (T% A))
    (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (h : V =ᶠ[𝓝 x] V') :
    cov2RmExt g x u V A B C D = cov2RmExt g x u V' A B C D := by
  have h1 : mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)) x
      = mvfderiv I (fun y : M => covRm g y (V' y) (A y) (B y) (C y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) (by
      filter_upwards [h] with y hy
      rw [hy])
  have h2 : (lcOf g) V x = (lcOf g) V' x :=
    (lcOf g).isCovariantDerivativeOn.congr_of_eventuallyEq (hV.mdifferentiableAt (by simp))
      (hV'.mdifferentiableAt (by simp)) Filter.univ_mem h
  have h3 : V x = V' x := h.self_of_nhds
  simp only [cov2RmExt]
  rw [h1, h2, h3]

/-- `cov2RmExt g x u V · B C D` is unchanged by changing its second field away from `x`. -/
theorem cov2RmExt_germ_A (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A A' B C D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hA' : CMDiff ∞ (T% A'))
    (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (h : A =ᶠ[𝓝 x] A') :
    cov2RmExt g x u V A B C D = cov2RmExt g x u V A' B C D := by
  have h1 : mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)) x
      = mvfderiv I (fun y : M => covRm g y (V y) (A' y) (B y) (C y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) (by
      filter_upwards [h] with y hy
      rw [hy])
  have h2 : (lcOf g) A x = (lcOf g) A' x :=
    (lcOf g).isCovariantDerivativeOn.congr_of_eventuallyEq (hA.mdifferentiableAt (by simp))
      (hA'.mdifferentiableAt (by simp)) Filter.univ_mem h
  have h3 : A x = A' x := h.self_of_nhds
  simp only [cov2RmExt]
  rw [h1, h2, h3]

/-- `cov2RmExt g x u V A · C D` is unchanged by changing its fourth field away from `x`. -/
theorem cov2RmExt_germ_B (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A B B' C D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hB' : CMDiff ∞ (T% B')) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (h : B =ᶠ[𝓝 x] B') :
    cov2RmExt g x u V A B C D = cov2RmExt g x u V A B' C D := by
  have h1 : mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)) x
      = mvfderiv I (fun y : M => covRm g y (V y) (A y) (B' y) (C y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) (by
      filter_upwards [h] with y hy
      rw [hy])
  have h2 : (lcOf g) B x = (lcOf g) B' x :=
    (lcOf g).isCovariantDerivativeOn.congr_of_eventuallyEq (hB.mdifferentiableAt (by simp))
      (hB'.mdifferentiableAt (by simp)) Filter.univ_mem h
  have h3 : B x = B' x := h.self_of_nhds
  simp only [cov2RmExt]
  rw [h1, h2, h3]

/-- `cov2RmExt g x u V A B · D` is unchanged by changing its fifth field away from `x`. -/
theorem cov2RmExt_germ_C (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A B C C' D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hC' : CMDiff ∞ (T% C')) (hD : CMDiff ∞ (T% D))
    (h : C =ᶠ[𝓝 x] C') :
    cov2RmExt g x u V A B C D = cov2RmExt g x u V A B C' D := by
  have h1 : mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)) x
      = mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C' y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) (by
      filter_upwards [h] with y hy
      rw [hy])
  have h2 : (lcOf g) C x = (lcOf g) C' x :=
    (lcOf g).isCovariantDerivativeOn.congr_of_eventuallyEq (hC.mdifferentiableAt (by simp))
      (hC'.mdifferentiableAt (by simp)) Filter.univ_mem h
  have h3 : C x = C' x := h.self_of_nhds
  simp only [cov2RmExt]
  rw [h1, h2, h3]

/-- `cov2RmExt g x u V A B C ·` is unchanged by changing its sixth field away from `x`. -/
theorem cov2RmExt_germ_D (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A B C D D' : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) (hD' : CMDiff ∞ (T% D'))
    (h : D =ᶠ[𝓝 x] D') :
    cov2RmExt g x u V A B C D = cov2RmExt g x u V A B C D' := by
  have h1 : mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)) x
      = mvfderiv I (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D' y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) (by
      filter_upwards [h] with y hy
      rw [hy])
  have h2 : (lcOf g) D x = (lcOf g) D' x :=
    (lcOf g).isCovariantDerivativeOn.congr_of_eventuallyEq (hD.mdifferentiableAt (by simp))
      (hD'.mdifferentiableAt (by simp)) Filter.univ_mem h
  have h3 : D x = D' x := h.self_of_nhds
  simp only [cov2RmExt]
  rw [h1, h2, h3]

/-! ## The value dependence of `cov2RmExt` in each of its five fields -/

/-- `cov2RmExt g x u` depends on its first (direction) field only through the value at `x`. -/
theorem cov2RmExt_bind_V (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V V' A B C D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hV' : CMDiff ∞ (T% V')) (hA : CMDiff ∞ (T% A))
    (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (h : V x = V' x) :
    cov2RmExt g x u V A B C D = cov2RmExt g x u V' A B C D :=
  field_value_dep_of_linear x (F := fun X : Π y : M, TangentSpace I y =>
      cov2RmExt g x u X A B C D)
    (fun X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂ =>
      cov2RmExt_linear_V (g := g) hLC x u hX₁ hX₂ hA hB hC hD hf₁ hf₂)
    (fun X X' hX hX' heq => cov2RmExt_germ_V (g := g) hLC x u hX hX' hA hB hC hD heq)
    hV hV' h

/-- `cov2RmExt g x u V` depends on its second field only through the value at `x`. -/
theorem cov2RmExt_bind_A (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A A' B C D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hA' : CMDiff ∞ (T% A'))
    (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (h : A x = A' x) :
    cov2RmExt g x u V A B C D = cov2RmExt g x u V A' B C D :=
  field_value_dep_of_linear x (F := fun X : Π y : M, TangentSpace I y =>
      cov2RmExt g x u V X B C D)
    (fun X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂ =>
      cov2RmExt_linear_A (g := g) hLC x u hV hX₁ hX₂ hB hC hD hf₁ hf₂)
    (fun X X' hX hX' heq => cov2RmExt_germ_A (g := g) hLC x u hV hX hX' hB hC hD heq)
    hA hA' h

/-- `cov2RmExt g x u V A` depends on its fourth field only through the value at `x`. -/
theorem cov2RmExt_bind_B (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A B B' C D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hB' : CMDiff ∞ (T% B')) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (h : B x = B' x) :
    cov2RmExt g x u V A B C D = cov2RmExt g x u V A B' C D :=
  field_value_dep_of_linear x (F := fun X : Π y : M, TangentSpace I y =>
      cov2RmExt g x u V A X C D)
    (fun X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂ =>
      cov2RmExt_linear_B (g := g) hLC x u hV hA hX₁ hX₂ hC hD hf₁ hf₂)
    (fun X X' hX hX' heq => cov2RmExt_germ_B (g := g) hLC x u hV hA hX hX' hC hD heq)
    hB hB' h

/-- `cov2RmExt g x u V A B` depends on its fifth field only through the value at `x`. -/
theorem cov2RmExt_bind_C (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A B C C' D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hC' : CMDiff ∞ (T% C')) (hD : CMDiff ∞ (T% D))
    (h : C x = C' x) :
    cov2RmExt g x u V A B C D = cov2RmExt g x u V A B C' D :=
  field_value_dep_of_linear x (F := fun X : Π y : M, TangentSpace I y =>
      cov2RmExt g x u V A B X D)
    (fun X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂ =>
      cov2RmExt_linear_C (g := g) hLC x u hV hA hB hX₁ hX₂ hD hf₁ hf₂)
    (fun X X' hX hX' heq => cov2RmExt_germ_C (g := g) hLC x u hV hA hB hX hX' hD heq)
    hC hC' h

/-- `cov2RmExt g x u V A B C` depends on its sixth field only through the value at `x`. -/
theorem cov2RmExt_bind_D (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u : TangentSpace I x)
    {V A B C D D' : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) (hD' : CMDiff ∞ (T% D'))
    (h : D x = D' x) :
    cov2RmExt g x u V A B C D = cov2RmExt g x u V A B C D' :=
  field_value_dep_of_linear x (F := fun X : Π y : M, TangentSpace I y =>
      cov2RmExt g x u V A B C X)
    (fun X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂ =>
      cov2RmExt_linear_D (g := g) hLC x u hV hA hB hC hX₁ hX₂ hf₁ hf₂)
    (fun X X' hX hX' heq => cov2RmExt_germ_D (g := g) hLC x u hV hA hB hC hX hX' heq)
    hD hD' h

end Work.Diff.GE
