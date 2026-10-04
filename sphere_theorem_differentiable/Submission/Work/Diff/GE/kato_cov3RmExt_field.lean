import Mathlib
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.NablaRm
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The field form of `cov3RmExt` (`∇∇∇Rm` on smooth fields)

`Work.Diff.GE.cov3RmExt g x w U V A B C D` is `mvfderiv (y ↦ cov2Rm g y (U y) … (D y)) x w` minus
the six Leibniz corrections; it is the component `(∇_w∇∇Rm)(U,V,A,B,C,D)` of the third covariant
derivative of the curvature, i.e. a `(0,7)`-tensor, and so depends only on the *values* of the six
fields at `x`.  This file proves that (`kato_cov3RmExt_field`), one slot at a time, using the
value-dependence machine `Work.Diff.GE.field_value_dep_of_linear` of `cov2RmExt_prelim.lean`:

* `cov2RmExt_field_smooth`, `cov2Rm_field_form`, `cov2Rm_field_smooth`: smoothness of `∇²Rm` on
  smooth fields and its field form (via the `cov2RmExt_bind_*` lemmas);
* `cov2Rm_lin_*`, `cov2Rm_linear_slots_self`: `∇²Rm` is `ℝ`-multilinear in its six arguments
  (pointwise; obtained from the `C^∞(M)`-linearity of `cov2RmExt` in its five field arguments and
  the value dependence of the latter);
* `cov3RmExt_linear_{fst,snd,thd,fth,fif,sixth}`: `cov3RmExt` is `C^∞(M)`-linear in each of its six
  field arguments (the Leibniz computation for the differentiated term, using the pointwise
  multilinearity of `∇²Rm`, plus the identity of the connection corrections — `lcOf`);
* `cov3RmExt_germ_*`: `cov3RmExt` is unchanged by changing one field away from `x`;
* `cov3RmExt_bind_*`: the resulting value dependence in each slot;
* `kato_cov3RmExt_field`: all six slots at once.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.GE.Kato3

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Smoothness of `cov2Rm` on smooth fields -/

/-- Smoothness of `y ↦ cov2RmExt g y (W y) V A B C D` on smooth fields. -/
theorem cov2RmExt_field_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {W V A B C D : Π y : M, TangentSpace I y}
    (hW : CMDiff ∞ (T% W)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A))
    (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (fun y : M => cov2RmExt g y (W y) V A B C D) := by
  obtain ⟨hcov⟩ := (hLC g).1
  have hF : CMDiff ∞ (fun z : M => covRm g z (V z) (A z) (B z) (C z) (D z)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hC hD
  have t1 : CMDiff ∞ (fun y : M =>
      mvfderiv I (fun z : M => covRm g z (V z) (A z) (B z) (C z) (D z)) y (W y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hF hW
  have hlcV : CMDiff ∞ (T% (fun y : M => lcOf g V y (W y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hV hW
  have hlcA : CMDiff ∞ (T% (fun y : M => lcOf g A y (W y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hA hW
  have hlcB : CMDiff ∞ (T% (fun y : M => lcOf g B y (W y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hB hW
  have hlcC : CMDiff ∞ (T% (fun y : M => lcOf g C y (W y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hC hW
  have hlcD : CMDiff ∞ (T% (fun y : M => lcOf g D y (W y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hD hW
  have t2 : CMDiff ∞ (fun y : M => covRm g y (lcOf g V y (W y)) (A y) (B y) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hlcV hA hB hC hD
  have t3 : CMDiff ∞ (fun y : M => covRm g y (V y) (lcOf g A y (W y)) (B y) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hlcA hB hC hD
  have t4 : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (lcOf g B y (W y)) (C y) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hlcB hC hD
  have t5 : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B y) (lcOf g C y (W y)) (D y)) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hlcC hD
  have t6 : CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B y) (C y) (lcOf g D y (W y))) :=
    covRm_fields_smooth (g := g) hLC hV hA hB hC hlcD
  simp only [cov2RmExt]
  exact ((((t1.sub t2).sub t3).sub t4).sub t5).sub t6

/-- The field form of the frozen `cov2Rm`. -/
theorem cov2Rm_field_form (hLC : LCSmooth I M) (g : SMet I M) (y : M)
    {X₁ X₂ X₃ X₄ X₅ X₆ : Π y : M, TangentSpace I y}
    (h₁ : CMDiff ∞ (T% X₁)) (h₂ : CMDiff ∞ (T% X₂)) (h₃ : CMDiff ∞ (T% X₃))
    (h₄ : CMDiff ∞ (T% X₄)) (h₅ : CMDiff ∞ (T% X₅)) (h₆ : CMDiff ∞ (T% X₆)) :
    cov2Rm g y (X₁ y) (X₂ y) (X₃ y) (X₄ y) (X₅ y) (X₆ y)
      = cov2RmExt g y (X₁ y) X₂ X₃ X₄ X₅ X₆ := by
  rw [show cov2Rm g y (X₁ y) (X₂ y) (X₃ y) (X₄ y) (X₅ y) (X₆ y)
      = cov2RmExt g y (X₁ y) (smoothExt y (X₂ y)) (smoothExt y (X₃ y))
          (smoothExt y (X₄ y)) (smoothExt y (X₅ y)) (smoothExt y (X₆ y)) from rfl]
  rw [cov2RmExt_bind_V (g := g) hLC y (X₁ y) (smoothExt_cmdiff y (X₂ y)) h₂
      (smoothExt_cmdiff y (X₃ y)) (smoothExt_cmdiff y (X₄ y)) (smoothExt_cmdiff y (X₅ y))
      (smoothExt_cmdiff y (X₆ y)) (smoothExt_apply y (X₂ y))]
  rw [cov2RmExt_bind_A (g := g) hLC y (X₁ y) h₂ (smoothExt_cmdiff y (X₃ y)) h₃
      (smoothExt_cmdiff y (X₄ y)) (smoothExt_cmdiff y (X₅ y)) (smoothExt_cmdiff y (X₆ y))
      (smoothExt_apply y (X₃ y))]
  rw [cov2RmExt_bind_B (g := g) hLC y (X₁ y) h₂ h₃ (smoothExt_cmdiff y (X₄ y)) h₄
      (smoothExt_cmdiff y (X₅ y)) (smoothExt_cmdiff y (X₆ y)) (smoothExt_apply y (X₄ y))]
  rw [cov2RmExt_bind_C (g := g) hLC y (X₁ y) h₂ h₃ h₄ (smoothExt_cmdiff y (X₅ y)) h₅
      (smoothExt_cmdiff y (X₆ y)) (smoothExt_apply y (X₅ y))]
  rw [cov2RmExt_bind_D (g := g) hLC y (X₁ y) h₂ h₃ h₄ h₅ (smoothExt_cmdiff y (X₆ y)) h₆
      (smoothExt_apply y (X₆ y))]

/-- Smoothness of `y ↦ cov2Rm g y (fields)` for smooth fields. -/
theorem cov2Rm_field_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {X₁ X₂ X₃ X₄ X₅ X₆ : Π y : M, TangentSpace I y}
    (h₁ : CMDiff ∞ (T% X₁)) (h₂ : CMDiff ∞ (T% X₂)) (h₃ : CMDiff ∞ (T% X₃))
    (h₄ : CMDiff ∞ (T% X₄)) (h₅ : CMDiff ∞ (T% X₅)) (h₆ : CMDiff ∞ (T% X₆)) :
    CMDiff ∞ (fun y : M => cov2Rm g y (X₁ y) (X₂ y) (X₃ y) (X₄ y) (X₅ y) (X₆ y)) := by
  have hfun : (fun y : M => cov2Rm g y (X₁ y) (X₂ y) (X₃ y) (X₄ y) (X₅ y) (X₆ y))
      = fun y : M => cov2RmExt g y (X₁ y) X₂ X₃ X₄ X₅ X₆ :=
    funext fun y => cov2Rm_field_form hLC g y h₁ h₂ h₃ h₄ h₅ h₆
  rw [hfun]
  exact cov2RmExt_field_smooth hLC g h₁ h₂ h₃ h₄ h₅ h₆



/-- Pointwise linearity of `cov2Rm` in its first (direction) argument. -/
theorem cov2Rm_lin_first (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (r s : ℝ) (v₁ v₂ w a b c d : TangentSpace I x) :
    cov2Rm g x (r • v₁ + s • v₂) w a b c d
      = r * cov2Rm g x v₁ w a b c d + s * cov2Rm g x v₂ w a b c d := by
  have h1 : CMDiff ∞ (T% (smoothExt x w)) := smoothExt_cmdiff x w
  have h2 : CMDiff ∞ (T% (smoothExt x a)) := smoothExt_cmdiff x a
  have h3 : CMDiff ∞ (T% (smoothExt x b)) := smoothExt_cmdiff x b
  have h4 : CMDiff ∞ (T% (smoothExt x c)) := smoothExt_cmdiff x c
  have h5 : CMDiff ∞ (T% (smoothExt x d)) := smoothExt_cmdiff x d
  show cov2RmExt g x (r • v₁ + s • v₂) (smoothExt x w) (smoothExt x a) (smoothExt x b)
      (smoothExt x c) (smoothExt x d)
    = r * cov2RmExt g x v₁ (smoothExt x w) (smoothExt x a) (smoothExt x b) (smoothExt x c)
        (smoothExt x d)
      + s * cov2RmExt g x v₂ (smoothExt x w) (smoothExt x a) (smoothExt x b) (smoothExt x c)
        (smoothExt x d)
  have hd : mvfderiv I (fun y : M => covRm g y (smoothExt x w y) (smoothExt x a y)
        (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x (r • v₁ + s • v₂)
      = r * mvfderiv I (fun y : M => covRm g y (smoothExt x w y) (smoothExt x a y)
          (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v₁
        + s * mvfderiv I (fun y : M => covRm g y (smoothExt x w y) (smoothExt x a y)
          (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v₂ := by
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
  have c1 : covRm g x ((lcOf g) (smoothExt x w) x (r • v₁ + s • v₂))
        (smoothExt x a x) (smoothExt x b x) (smoothExt x c x) (smoothExt x d x)
      = r * covRm g x ((lcOf g) (smoothExt x w) x v₁) (smoothExt x a x) (smoothExt x b x)
          (smoothExt x c x) (smoothExt x d x)
        + s * covRm g x ((lcOf g) (smoothExt x w) x v₂) (smoothExt x a x) (smoothExt x b x)
          (smoothExt x c x) (smoothExt x d x) := by
    rw [map_add, map_smul, map_smul]
    rw [covRm_linear_fst hLC g x r s ((lcOf g) (smoothExt x w) x v₁)
        ((lcOf g) (smoothExt x w) x v₂) (smoothExt x a x) (smoothExt x b x)
        (smoothExt x c x) (smoothExt x d x)]
  have c2 : covRm g x (smoothExt x w x) ((lcOf g) (smoothExt x a) x (r • v₁ + s • v₂))
        (smoothExt x b x) (smoothExt x c x) (smoothExt x d x)
      = r * covRm g x (smoothExt x w x) ((lcOf g) (smoothExt x a) x v₁) (smoothExt x b x)
          (smoothExt x c x) (smoothExt x d x)
        + s * covRm g x (smoothExt x w x) ((lcOf g) (smoothExt x a) x v₂) (smoothExt x b x)
          (smoothExt x c x) (smoothExt x d x) := by
    rw [map_add, map_smul, map_smul]
    rw [covRm_linear_snd hLC g x (smoothExt x w x) r s ((lcOf g) (smoothExt x a) x v₁)
        ((lcOf g) (smoothExt x a) x v₂) (smoothExt x b x) (smoothExt x c x)
        (smoothExt x d x)]
  have c3 : covRm g x (smoothExt x w x) (smoothExt x a x)
        ((lcOf g) (smoothExt x b) x (r • v₁ + s • v₂)) (smoothExt x c x) (smoothExt x d x)
      = r * covRm g x (smoothExt x w x) (smoothExt x a x) ((lcOf g) (smoothExt x b) x v₁)
          (smoothExt x c x) (smoothExt x d x)
        + s * covRm g x (smoothExt x w x) (smoothExt x a x) ((lcOf g) (smoothExt x b) x v₂)
          (smoothExt x c x) (smoothExt x d x) := by
    rw [map_add, map_smul, map_smul]
    rw [covRm_linear_thd hLC g x (smoothExt x w x) (smoothExt x a x) r s
        ((lcOf g) (smoothExt x b) x v₁) ((lcOf g) (smoothExt x b) x v₂) (smoothExt x c x)
        (smoothExt x d x)]
  have c4 : covRm g x (smoothExt x w x) (smoothExt x a x) (smoothExt x b x)
        ((lcOf g) (smoothExt x c) x (r • v₁ + s • v₂)) (smoothExt x d x)
      = r * covRm g x (smoothExt x w x) (smoothExt x a x) (smoothExt x b x)
          ((lcOf g) (smoothExt x c) x v₁) (smoothExt x d x)
        + s * covRm g x (smoothExt x w x) (smoothExt x a x) (smoothExt x b x)
          ((lcOf g) (smoothExt x c) x v₂) (smoothExt x d x) := by
    rw [map_add, map_smul, map_smul]
    rw [covRm_linear_fth hLC g x (smoothExt x w x) (smoothExt x a x) (smoothExt x b x) r s
        ((lcOf g) (smoothExt x c) x v₁) ((lcOf g) (smoothExt x c) x v₂) (smoothExt x d x)]
  have c5 : covRm g x (smoothExt x w x) (smoothExt x a x) (smoothExt x b x) (smoothExt x c x)
        ((lcOf g) (smoothExt x d) x (r • v₁ + s • v₂))
      = r * covRm g x (smoothExt x w x) (smoothExt x a x) (smoothExt x b x) (smoothExt x c x)
          ((lcOf g) (smoothExt x d) x v₁)
        + s * covRm g x (smoothExt x w x) (smoothExt x a x) (smoothExt x b x) (smoothExt x c x)
          ((lcOf g) (smoothExt x d) x v₂) := by
    rw [map_add, map_smul, map_smul]
    rw [covRm_linear_fif hLC g x (smoothExt x w x) (smoothExt x a x) (smoothExt x b x)
        (smoothExt x c x) r s ((lcOf g) (smoothExt x d) x v₁) ((lcOf g) (smoothExt x d) x v₂)]
  simp only [cov2RmExt]
  rw [hd, c1, c2, c3, c4, c5]
  ring


/-- Pointwise linearity of `cov2Rm` in its second argument (via binding in the first field). -/
theorem cov2Rm_lin_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (r s : ℝ) (v w₁ w₂ a b c d : TangentSpace I x) :
    cov2Rm g x v (r • w₁ + s • w₂) a b c d
      = r * cov2Rm g x v w₁ a b c d + s * cov2Rm g x v w₂ a b c d := by
  have hW : CMDiff ∞ (T% (smoothExt x (r • w₁ + s • w₂))) := smoothExt_cmdiff x (r • w₁ + s • w₂)
  have hW' : CMDiff ∞ (T% ((fun _ : M => r) • smoothExt x w₁ + (fun _ : M => s) • smoothExt x w₂)) :=
    ((contMDiff_const (c := r)).smul_section (smoothExt_cmdiff x w₁)).add_section
      ((contMDiff_const (c := s)).smul_section (smoothExt_cmdiff x w₂))
  have hval : smoothExt x (r • w₁ + s • w₂) x
      = ((fun _ : M => r) • smoothExt x w₁ + (fun _ : M => s) • smoothExt x w₂) x := by
    rw [show ((fun _ : M => r) • smoothExt x w₁ + (fun _ : M => s) • smoothExt x w₂) x
        = r • smoothExt x w₁ x + s • smoothExt x w₂ x from rfl,
      smoothExt_apply x (r • w₁ + s • w₂), smoothExt_apply x w₁, smoothExt_apply x w₂]
  show cov2RmExt g x v (smoothExt x (r • w₁ + s • w₂)) (smoothExt x a) (smoothExt x b)
      (smoothExt x c) (smoothExt x d) = _
  rw [cov2RmExt_bind_V (g := g) hLC x v hW hW' (smoothExt_cmdiff x a) (smoothExt_cmdiff x b)
      (smoothExt_cmdiff x c) (smoothExt_cmdiff x d) hval]
  rw [cov2RmExt_linear_V (g := g) hLC x v (smoothExt_cmdiff x w₁) (smoothExt_cmdiff x w₂)
      (smoothExt_cmdiff x a) (smoothExt_cmdiff x b) (smoothExt_cmdiff x c) (smoothExt_cmdiff x d)
      (contMDiff_const (c := r)) (contMDiff_const (c := s))]
  rfl

/-- Pointwise linearity of `cov2Rm` in its third argument (via binding in the second field). -/
theorem cov2Rm_lin_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (r s : ℝ) (v w a₁ a₂ b c d : TangentSpace I x) :
    cov2Rm g x v w (r • a₁ + s • a₂) b c d
      = r * cov2Rm g x v w a₁ b c d + s * cov2Rm g x v w a₂ b c d := by
  have hA : CMDiff ∞ (T% (smoothExt x (r • a₁ + s • a₂))) := smoothExt_cmdiff x (r • a₁ + s • a₂)
  have hA' : CMDiff ∞ (T% ((fun _ : M => r) • smoothExt x a₁ + (fun _ : M => s) • smoothExt x a₂)) :=
    ((contMDiff_const (c := r)).smul_section (smoothExt_cmdiff x a₁)).add_section
      ((contMDiff_const (c := s)).smul_section (smoothExt_cmdiff x a₂))
  have hval : smoothExt x (r • a₁ + s • a₂) x
      = ((fun _ : M => r) • smoothExt x a₁ + (fun _ : M => s) • smoothExt x a₂) x := by
    rw [show ((fun _ : M => r) • smoothExt x a₁ + (fun _ : M => s) • smoothExt x a₂) x
        = r • smoothExt x a₁ x + s • smoothExt x a₂ x from rfl,
      smoothExt_apply x (r • a₁ + s • a₂), smoothExt_apply x a₁, smoothExt_apply x a₂]
  show cov2RmExt g x v (smoothExt x w) (smoothExt x (r • a₁ + s • a₂)) (smoothExt x b)
      (smoothExt x c) (smoothExt x d) = _
  rw [cov2RmExt_bind_A (g := g) hLC x v (smoothExt_cmdiff x w) hA hA' (smoothExt_cmdiff x b)
      (smoothExt_cmdiff x c) (smoothExt_cmdiff x d) hval]
  rw [cov2RmExt_linear_A (g := g) hLC x v (smoothExt_cmdiff x w) (smoothExt_cmdiff x a₁)
      (smoothExt_cmdiff x a₂) (smoothExt_cmdiff x b) (smoothExt_cmdiff x c) (smoothExt_cmdiff x d)
      (contMDiff_const (c := r)) (contMDiff_const (c := s))]
  rfl

/-- Pointwise linearity of `cov2Rm` in its fourth argument (via binding in the third field). -/
theorem cov2Rm_lin_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (r s : ℝ) (v w a b₁ b₂ c d : TangentSpace I x) :
    cov2Rm g x v w a (r • b₁ + s • b₂) c d
      = r * cov2Rm g x v w a b₁ c d + s * cov2Rm g x v w a b₂ c d := by
  have hB : CMDiff ∞ (T% (smoothExt x (r • b₁ + s • b₂))) := smoothExt_cmdiff x (r • b₁ + s • b₂)
  have hB' : CMDiff ∞ (T% ((fun _ : M => r) • smoothExt x b₁ + (fun _ : M => s) • smoothExt x b₂)) :=
    ((contMDiff_const (c := r)).smul_section (smoothExt_cmdiff x b₁)).add_section
      ((contMDiff_const (c := s)).smul_section (smoothExt_cmdiff x b₂))
  have hval : smoothExt x (r • b₁ + s • b₂) x
      = ((fun _ : M => r) • smoothExt x b₁ + (fun _ : M => s) • smoothExt x b₂) x := by
    rw [show ((fun _ : M => r) • smoothExt x b₁ + (fun _ : M => s) • smoothExt x b₂) x
        = r • smoothExt x b₁ x + s • smoothExt x b₂ x from rfl,
      smoothExt_apply x (r • b₁ + s • b₂), smoothExt_apply x b₁, smoothExt_apply x b₂]
  show cov2RmExt g x v (smoothExt x w) (smoothExt x a) (smoothExt x (r • b₁ + s • b₂))
      (smoothExt x c) (smoothExt x d) = _
  rw [cov2RmExt_bind_B (g := g) hLC x v (smoothExt_cmdiff x w) (smoothExt_cmdiff x a) hB hB'
      (smoothExt_cmdiff x c) (smoothExt_cmdiff x d) hval]
  rw [cov2RmExt_linear_B (g := g) hLC x v (smoothExt_cmdiff x w) (smoothExt_cmdiff x a)
      (smoothExt_cmdiff x b₁) (smoothExt_cmdiff x b₂) (smoothExt_cmdiff x c) (smoothExt_cmdiff x d)
      (contMDiff_const (c := r)) (contMDiff_const (c := s))]
  rfl

/-- Pointwise linearity of `cov2Rm` in its fifth argument (via binding in the fourth field). -/
theorem cov2Rm_lin_fif (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (r s : ℝ) (v w a b c₁ c₂ d : TangentSpace I x) :
    cov2Rm g x v w a b (r • c₁ + s • c₂) d
      = r * cov2Rm g x v w a b c₁ d + s * cov2Rm g x v w a b c₂ d := by
  have hC : CMDiff ∞ (T% (smoothExt x (r • c₁ + s • c₂))) := smoothExt_cmdiff x (r • c₁ + s • c₂)
  have hC' : CMDiff ∞ (T% ((fun _ : M => r) • smoothExt x c₁ + (fun _ : M => s) • smoothExt x c₂)) :=
    ((contMDiff_const (c := r)).smul_section (smoothExt_cmdiff x c₁)).add_section
      ((contMDiff_const (c := s)).smul_section (smoothExt_cmdiff x c₂))
  have hval : smoothExt x (r • c₁ + s • c₂) x
      = ((fun _ : M => r) • smoothExt x c₁ + (fun _ : M => s) • smoothExt x c₂) x := by
    rw [show ((fun _ : M => r) • smoothExt x c₁ + (fun _ : M => s) • smoothExt x c₂) x
        = r • smoothExt x c₁ x + s • smoothExt x c₂ x from rfl,
      smoothExt_apply x (r • c₁ + s • c₂), smoothExt_apply x c₁, smoothExt_apply x c₂]
  show cov2RmExt g x v (smoothExt x w) (smoothExt x a) (smoothExt x b)
      (smoothExt x (r • c₁ + s • c₂)) (smoothExt x d) = _
  rw [cov2RmExt_bind_C (g := g) hLC x v (smoothExt_cmdiff x w) (smoothExt_cmdiff x a)
      (smoothExt_cmdiff x b) hC hC' (smoothExt_cmdiff x d) hval]
  rw [cov2RmExt_linear_C (g := g) hLC x v (smoothExt_cmdiff x w) (smoothExt_cmdiff x a)
      (smoothExt_cmdiff x b) (smoothExt_cmdiff x c₁) (smoothExt_cmdiff x c₂) (smoothExt_cmdiff x d)
      (contMDiff_const (c := r)) (contMDiff_const (c := s))]
  rfl

/-- Pointwise linearity of `cov2Rm` in its sixth argument (via binding in the fifth field). -/
theorem cov2Rm_lin_sixth (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (r s : ℝ) (v w a b c d₁ d₂ : TangentSpace I x) :
    cov2Rm g x v w a b c (r • d₁ + s • d₂)
      = r * cov2Rm g x v w a b c d₁ + s * cov2Rm g x v w a b c d₂ := by
  have hD : CMDiff ∞ (T% (smoothExt x (r • d₁ + s • d₂))) := smoothExt_cmdiff x (r • d₁ + s • d₂)
  have hD' : CMDiff ∞ (T% ((fun _ : M => r) • smoothExt x d₁ + (fun _ : M => s) • smoothExt x d₂)) :=
    ((contMDiff_const (c := r)).smul_section (smoothExt_cmdiff x d₁)).add_section
      ((contMDiff_const (c := s)).smul_section (smoothExt_cmdiff x d₂))
  have hval : smoothExt x (r • d₁ + s • d₂) x
      = ((fun _ : M => r) • smoothExt x d₁ + (fun _ : M => s) • smoothExt x d₂) x := by
    rw [show ((fun _ : M => r) • smoothExt x d₁ + (fun _ : M => s) • smoothExt x d₂) x
        = r • smoothExt x d₁ x + s • smoothExt x d₂ x from rfl,
      smoothExt_apply x (r • d₁ + s • d₂), smoothExt_apply x d₁, smoothExt_apply x d₂]
  show cov2RmExt g x v (smoothExt x w) (smoothExt x a) (smoothExt x b) (smoothExt x c)
      (smoothExt x (r • d₁ + s • d₂)) = _
  rw [cov2RmExt_bind_D (g := g) hLC x v (smoothExt_cmdiff x w) (smoothExt_cmdiff x a)
      (smoothExt_cmdiff x b) (smoothExt_cmdiff x c) hD hD' hval]
  rw [cov2RmExt_linear_D (g := g) hLC x v (smoothExt_cmdiff x w) (smoothExt_cmdiff x a)
      (smoothExt_cmdiff x b) (smoothExt_cmdiff x c) (smoothExt_cmdiff x d₁)
      (smoothExt_cmdiff x d₂) (contMDiff_const (c := r)) (contMDiff_const (c := s))]
  rfl

/-- The six pointwise multilinearities of `∇²Rm`, packaged as one statement. -/
theorem cov2Rm_linear_slots_self (hLC : LCSmooth I M) (g : SMet I M) :
    (∀ (x : M) (r s : ℝ) (v₁ v₂ w a b c d : TangentSpace I x),
        cov2Rm g x (r • v₁ + s • v₂) w a b c d
          = r * cov2Rm g x v₁ w a b c d + s * cov2Rm g x v₂ w a b c d)
    ∧ (∀ (x : M) (r s : ℝ) (v w₁ w₂ a b c d : TangentSpace I x),
        cov2Rm g x v (r • w₁ + s • w₂) a b c d
          = r * cov2Rm g x v w₁ a b c d + s * cov2Rm g x v w₂ a b c d)
    ∧ (∀ (x : M) (r s : ℝ) (v w a₁ a₂ b c d : TangentSpace I x),
        cov2Rm g x v w (r • a₁ + s • a₂) b c d
          = r * cov2Rm g x v w a₁ b c d + s * cov2Rm g x v w a₂ b c d)
    ∧ (∀ (x : M) (r s : ℝ) (v w a b₁ b₂ c d : TangentSpace I x),
        cov2Rm g x v w a (r • b₁ + s • b₂) c d
          = r * cov2Rm g x v w a b₁ c d + s * cov2Rm g x v w a b₂ c d)
    ∧ (∀ (x : M) (r s : ℝ) (v w a b c₁ c₂ d : TangentSpace I x),
        cov2Rm g x v w a b (r • c₁ + s • c₂) d
          = r * cov2Rm g x v w a b c₁ d + s * cov2Rm g x v w a b c₂ d)
    ∧ (∀ (x : M) (r s : ℝ) (v w a b c d₁ d₂ : TangentSpace I x),
        cov2Rm g x v w a b c (r • d₁ + s • d₂)
          = r * cov2Rm g x v w a b c d₁ + s * cov2Rm g x v w a b c d₂) :=
  ⟨cov2Rm_lin_first hLC g, cov2Rm_lin_snd hLC g, cov2Rm_lin_thd hLC g, cov2Rm_lin_fth hLC g,
    cov2Rm_lin_fif hLC g, cov2Rm_lin_sixth hLC g⟩


theorem cov3RmExt_linear_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U₁ U₂ V A B C D : Π y : M, TangentSpace I y}
    (hU₁ : CMDiff ∞ (T% U₁)) (hU₂ : CMDiff ∞ (T% U₂)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    cov3RmExt g x w (f₁ • U₁ + f₂ • U₂) V A B C D
      = f₁ x * cov3RmExt g x w U₁ V A B C D + f₂ x * cov3RmExt g x w U₂ V A B C D := by
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6⟩ := cov2Rm_linear_slots_self hLC g
  have hX : CMDiff ∞ (T% (f₁ • U₁ + f₂ • U₂)) :=
    (hf₁.smul_section hU₁).add_section (hf₂.smul_section hU₂)
  have hΦ₁ : CMDiff ∞ (fun y : M => cov2Rm g y (U₁ y) (V y) (A y) (B y) (C y) (D y)) :=
    cov2Rm_field_smooth hLC g hU₁ hV hA hB hC hD
  have hΦ₂ : CMDiff ∞ (fun y : M => cov2Rm g y (U₂ y) (V y) (A y) (B y) (C y) (D y)) :=
    cov2Rm_field_smooth hLC g hU₂ hV hA hB hC hD
  have hΦ₁d : MDiffAt (fun y : M => cov2Rm g y (U₁ y) (V y) (A y) (B y) (C y) (D y)) x := hΦ₁.mdifferentiableAt (by simp)
  have hΦ₂d : MDiffAt (fun y : M => cov2Rm g y (U₂ y) (V y) (A y) (B y) (C y) (D y)) x := hΦ₂.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  have hpt : ∀ y : M, cov2Rm g y ((f₁ • U₁ + f₂ • U₂) y) (V y) (A y) (B y) (C y) (D y) = f₁ y * cov2Rm g y (U₁ y) (V y) (A y) (B y) (C y) (D y) + f₂ y * cov2Rm g y (U₂ y) (V y) (A y) (B y) (C y) (D y) := by
    intro y
    rw [show (f₁ • U₁ + f₂ • U₂) y = f₁ y • U₁ y + f₂ y • U₂ y from rfl]
    exact hL1 y (f₁ y) (f₂ y) (U₁ y) (U₂ y) (V y) (A y) (B y) (C y) (D y)
  have hT : mvfderiv I (fun y : M => cov2Rm g y ((f₁ • U₁ + f₂ • U₂) y) (V y) (A y) (B y) (C y) (D y)) x w
      = (f₁ x * mvfderiv I (fun y : M => cov2Rm g y (U₁ y) (V y) (A y) (B y) (C y) (D y)) x w
          + mvfderiv I f₁ x w * cov2Rm g x (U₁ x) (V x) (A x) (B x) (C x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => cov2Rm g y (U₂ y) (V y) (A y) (B y) (C y) (D y)) x w
          + mvfderiv I f₂ x w * cov2Rm g x (U₂ x) (V x) (A x) (B x) (C x) (D x)) := by
    have hfun : (fun y : M => cov2Rm g y ((f₁ • U₁ + f₂ • U₂) y) (V y) (A y) (B y) (C y) (D y))
        = f₁ * (fun y : M => cov2Rm g y (U₁ y) (V y) (A y) (B y) (C y) (D y)) + f₂ * (fun y : M => cov2Rm g y (U₂ y) (V y) (A y) (B y) (C y) (D y)) := by
      funext y
      exact hpt y
    rw [hfun, mvfderiv_add (hf₁d.mul hΦ₁d) (hf₂d.mul hΦ₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => cov2Rm g y (U₁ y) (V y) (A y) (B y) (C y) (D y)) hf₁d hΦ₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => cov2Rm g y (U₂ y) (V y) (A y) (B y) (C y) (D y)) hf₂d hΦ₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hcx : (f₁ • U₁ + f₂ • U₂) x = f₁ x • U₁ x + f₂ x • U₂ x := rfl
  have hc1 : cov2Rm g x ((lcOf g (f₁ • U₁ + f₂ • U₂) x) w) (V x) (A x) (B x) (C x) (D x)
      = (f₁ x * cov2Rm g x ((lcOf g (U₁) x) w) (V x) (A x) (B x) (C x) (D x) + mvfderiv I f₁ x w * cov2Rm g x (U₁ x) (V x) (A x) (B x) (C x) (D x))
        + (f₂ x * cov2Rm g x ((lcOf g (U₂) x) w) (V x) (A x) (B x) (C x) (D x) + mvfderiv I f₂ x w * cov2Rm g x (U₂ x) (V x) (A x) (B x) (C x) (D x)) := by
    have h1d : MDiffAt (T% (f₁ • U₁)) x := (hf₁.smul_section hU₁).mdifferentiableAt (by simp)
    have h2d : MDiffAt (T% (f₂ • U₂)) x := (hf₂.smul_section hU₂).mdifferentiableAt (by simp)
    have hU₁d : MDiffAt (T% U₁) x := hU₁.mdifferentiableAt (by simp)
    have hU₂d : MDiffAt (T% U₂) x := hU₂.mdifferentiableAt (by simp)
    have hlc := (lcOf g).isCovariantDerivativeOn.add (s := Set.univ) (σ := f₁ • U₁)
      (σ' := f₂ • U₂) h1d h2d
    have hle₁ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := U₁) (g := f₁)
      hU₁d hf₁d
    have hle₂ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := U₂) (g := f₂)
      hU₂d hf₂d
    have hadd1 : ∀ (Z W : TangentSpace I x),
        cov2Rm g x (Z + W) (V x) (A x) (B x) (C x) (D x)
          = cov2Rm g x (Z) (V x) (A x) (B x) (C x) (D x) + cov2Rm g x (W) (V x) (A x) (B x) (C x) (D x) := by
      intro Z W
      simpa using hL1 x 1 1 Z W (V x) (A x) (B x) (C x) (D x)
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, add_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₁, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₂, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [hadd1 (f₁ x • (lcOf g U₁ x) w + mvfderiv I f₁ x w • U₁ x)
        (f₂ x • (lcOf g U₂ x) w + mvfderiv I f₂ x w • U₂ x)]
    rw [hL1 x (f₁ x) (mvfderiv I f₁ x w) ((lcOf g U₁ x) w) (U₁ x) (V x) (A x) (B x) (C x) (D x)]
    rw [hL1 x (f₂ x) (mvfderiv I f₂ x w) ((lcOf g U₂ x) w) (U₂ x) (V x) (A x) (B x) (C x) (D x)]
  have hc2 : cov2Rm g x ((f₁ • U₁ + f₂ • U₂) x) ((lcOf g (V) x) w) (A x) (B x) (C x) (D x)
      = f₁ x * cov2Rm g x (U₁ x) ((lcOf g (V) x) w) (A x) (B x) (C x) (D x) + f₂ x * cov2Rm g x (U₂ x) ((lcOf g (V) x) w) (A x) (B x) (C x) (D x) := by
    rw [hcx]
    exact hL1 x (f₁ x) (f₂ x) (U₁ x) (U₂ x) ((lcOf g V x) w) (A x) (B x) (C x) (D x)
  have hc3 : cov2Rm g x ((f₁ • U₁ + f₂ • U₂) x) (V x) ((lcOf g (A) x) w) (B x) (C x) (D x)
      = f₁ x * cov2Rm g x (U₁ x) (V x) ((lcOf g (A) x) w) (B x) (C x) (D x) + f₂ x * cov2Rm g x (U₂ x) (V x) ((lcOf g (A) x) w) (B x) (C x) (D x) := by
    rw [hcx]
    exact hL1 x (f₁ x) (f₂ x) (U₁ x) (U₂ x) (V x) ((lcOf g A x) w) (B x) (C x) (D x)
  have hc4 : cov2Rm g x ((f₁ • U₁ + f₂ • U₂) x) (V x) (A x) ((lcOf g (B) x) w) (C x) (D x)
      = f₁ x * cov2Rm g x (U₁ x) (V x) (A x) ((lcOf g (B) x) w) (C x) (D x) + f₂ x * cov2Rm g x (U₂ x) (V x) (A x) ((lcOf g (B) x) w) (C x) (D x) := by
    rw [hcx]
    exact hL1 x (f₁ x) (f₂ x) (U₁ x) (U₂ x) (V x) (A x) ((lcOf g B x) w) (C x) (D x)
  have hc5 : cov2Rm g x ((f₁ • U₁ + f₂ • U₂) x) (V x) (A x) (B x) ((lcOf g (C) x) w) (D x)
      = f₁ x * cov2Rm g x (U₁ x) (V x) (A x) (B x) ((lcOf g (C) x) w) (D x) + f₂ x * cov2Rm g x (U₂ x) (V x) (A x) (B x) ((lcOf g (C) x) w) (D x) := by
    rw [hcx]
    exact hL1 x (f₁ x) (f₂ x) (U₁ x) (U₂ x) (V x) (A x) (B x) ((lcOf g C x) w) (D x)
  have hc6 : cov2Rm g x ((f₁ • U₁ + f₂ • U₂) x) (V x) (A x) (B x) (C x) ((lcOf g (D) x) w)
      = f₁ x * cov2Rm g x (U₁ x) (V x) (A x) (B x) (C x) ((lcOf g (D) x) w) + f₂ x * cov2Rm g x (U₂ x) (V x) (A x) (B x) (C x) ((lcOf g (D) x) w) := by
    rw [hcx]
    exact hL1 x (f₁ x) (f₂ x) (U₁ x) (U₂ x) (V x) (A x) (B x) (C x) ((lcOf g D x) w)
  simp only [cov3RmExt]
  rw [hT, hc1, hc2, hc3, hc4, hc5, hc6]
  ring

theorem cov3RmExt_linear_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V₁ V₂ A B C D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV₁ : CMDiff ∞ (T% V₁)) (hV₂ : CMDiff ∞ (T% V₂)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    cov3RmExt g x w U (f₁ • V₁ + f₂ • V₂) A B C D
      = f₁ x * cov3RmExt g x w U V₁ A B C D + f₂ x * cov3RmExt g x w U V₂ A B C D := by
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6⟩ := cov2Rm_linear_slots_self hLC g
  have hX : CMDiff ∞ (T% (f₁ • V₁ + f₂ • V₂)) :=
    (hf₁.smul_section hV₁).add_section (hf₂.smul_section hV₂)
  have hΦ₁ : CMDiff ∞ (fun y : M => cov2Rm g y (U y) (V₁ y) (A y) (B y) (C y) (D y)) :=
    cov2Rm_field_smooth hLC g hU hV₁ hA hB hC hD
  have hΦ₂ : CMDiff ∞ (fun y : M => cov2Rm g y (U y) (V₂ y) (A y) (B y) (C y) (D y)) :=
    cov2Rm_field_smooth hLC g hU hV₂ hA hB hC hD
  have hΦ₁d : MDiffAt (fun y : M => cov2Rm g y (U y) (V₁ y) (A y) (B y) (C y) (D y)) x := hΦ₁.mdifferentiableAt (by simp)
  have hΦ₂d : MDiffAt (fun y : M => cov2Rm g y (U y) (V₂ y) (A y) (B y) (C y) (D y)) x := hΦ₂.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  have hpt : ∀ y : M, cov2Rm g y (U y) ((f₁ • V₁ + f₂ • V₂) y) (A y) (B y) (C y) (D y) = f₁ y * cov2Rm g y (U y) (V₁ y) (A y) (B y) (C y) (D y) + f₂ y * cov2Rm g y (U y) (V₂ y) (A y) (B y) (C y) (D y) := by
    intro y
    rw [show (f₁ • V₁ + f₂ • V₂) y = f₁ y • V₁ y + f₂ y • V₂ y from rfl]
    exact hL2 y (f₁ y) (f₂ y) (U y) (V₁ y) (V₂ y) (A y) (B y) (C y) (D y)
  have hT : mvfderiv I (fun y : M => cov2Rm g y (U y) ((f₁ • V₁ + f₂ • V₂) y) (A y) (B y) (C y) (D y)) x w
      = (f₁ x * mvfderiv I (fun y : M => cov2Rm g y (U y) (V₁ y) (A y) (B y) (C y) (D y)) x w
          + mvfderiv I f₁ x w * cov2Rm g x (U x) (V₁ x) (A x) (B x) (C x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => cov2Rm g y (U y) (V₂ y) (A y) (B y) (C y) (D y)) x w
          + mvfderiv I f₂ x w * cov2Rm g x (U x) (V₂ x) (A x) (B x) (C x) (D x)) := by
    have hfun : (fun y : M => cov2Rm g y (U y) ((f₁ • V₁ + f₂ • V₂) y) (A y) (B y) (C y) (D y))
        = f₁ * (fun y : M => cov2Rm g y (U y) (V₁ y) (A y) (B y) (C y) (D y)) + f₂ * (fun y : M => cov2Rm g y (U y) (V₂ y) (A y) (B y) (C y) (D y)) := by
      funext y
      exact hpt y
    rw [hfun, mvfderiv_add (hf₁d.mul hΦ₁d) (hf₂d.mul hΦ₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => cov2Rm g y (U y) (V₁ y) (A y) (B y) (C y) (D y)) hf₁d hΦ₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => cov2Rm g y (U y) (V₂ y) (A y) (B y) (C y) (D y)) hf₂d hΦ₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hcx : (f₁ • V₁ + f₂ • V₂) x = f₁ x • V₁ x + f₂ x • V₂ x := rfl
  have hc1 : cov2Rm g x ((lcOf g (U) x) w) ((f₁ • V₁ + f₂ • V₂) x) (A x) (B x) (C x) (D x)
      = f₁ x * cov2Rm g x ((lcOf g (U) x) w) (V₁ x) (A x) (B x) (C x) (D x) + f₂ x * cov2Rm g x ((lcOf g (U) x) w) (V₂ x) (A x) (B x) (C x) (D x) := by
    rw [hcx]
    exact hL2 x (f₁ x) (f₂ x) ((lcOf g U x) w) (V₁ x) (V₂ x) (A x) (B x) (C x) (D x)
  have hc2 : cov2Rm g x (U x) ((lcOf g (f₁ • V₁ + f₂ • V₂) x) w) (A x) (B x) (C x) (D x)
      = (f₁ x * cov2Rm g x (U x) ((lcOf g (V₁) x) w) (A x) (B x) (C x) (D x) + mvfderiv I f₁ x w * cov2Rm g x (U x) (V₁ x) (A x) (B x) (C x) (D x))
        + (f₂ x * cov2Rm g x (U x) ((lcOf g (V₂) x) w) (A x) (B x) (C x) (D x) + mvfderiv I f₂ x w * cov2Rm g x (U x) (V₂ x) (A x) (B x) (C x) (D x)) := by
    have h1d : MDiffAt (T% (f₁ • V₁)) x := (hf₁.smul_section hV₁).mdifferentiableAt (by simp)
    have h2d : MDiffAt (T% (f₂ • V₂)) x := (hf₂.smul_section hV₂).mdifferentiableAt (by simp)
    have hV₁d : MDiffAt (T% V₁) x := hV₁.mdifferentiableAt (by simp)
    have hV₂d : MDiffAt (T% V₂) x := hV₂.mdifferentiableAt (by simp)
    have hlc := (lcOf g).isCovariantDerivativeOn.add (s := Set.univ) (σ := f₁ • V₁)
      (σ' := f₂ • V₂) h1d h2d
    have hle₁ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := V₁) (g := f₁)
      hV₁d hf₁d
    have hle₂ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := V₂) (g := f₂)
      hV₂d hf₂d
    have hadd2 : ∀ (Z W : TangentSpace I x),
        cov2Rm g x (U x) (Z + W) (A x) (B x) (C x) (D x)
          = cov2Rm g x (U x) (Z) (A x) (B x) (C x) (D x) + cov2Rm g x (U x) (W) (A x) (B x) (C x) (D x) := by
      intro Z W
      simpa using hL2 x 1 1 (U x) Z W (A x) (B x) (C x) (D x)
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, add_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₁, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₂, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [hadd2 (f₁ x • (lcOf g V₁ x) w + mvfderiv I f₁ x w • V₁ x)
        (f₂ x • (lcOf g V₂ x) w + mvfderiv I f₂ x w • V₂ x)]
    rw [hL2 x (f₁ x) (mvfderiv I f₁ x w) (U x) ((lcOf g V₁ x) w) (V₁ x) (A x) (B x) (C x) (D x)]
    rw [hL2 x (f₂ x) (mvfderiv I f₂ x w) (U x) ((lcOf g V₂ x) w) (V₂ x) (A x) (B x) (C x) (D x)]
  have hc3 : cov2Rm g x (U x) ((f₁ • V₁ + f₂ • V₂) x) ((lcOf g (A) x) w) (B x) (C x) (D x)
      = f₁ x * cov2Rm g x (U x) (V₁ x) ((lcOf g (A) x) w) (B x) (C x) (D x) + f₂ x * cov2Rm g x (U x) (V₂ x) ((lcOf g (A) x) w) (B x) (C x) (D x) := by
    rw [hcx]
    exact hL2 x (f₁ x) (f₂ x) (U x) (V₁ x) (V₂ x) ((lcOf g A x) w) (B x) (C x) (D x)
  have hc4 : cov2Rm g x (U x) ((f₁ • V₁ + f₂ • V₂) x) (A x) ((lcOf g (B) x) w) (C x) (D x)
      = f₁ x * cov2Rm g x (U x) (V₁ x) (A x) ((lcOf g (B) x) w) (C x) (D x) + f₂ x * cov2Rm g x (U x) (V₂ x) (A x) ((lcOf g (B) x) w) (C x) (D x) := by
    rw [hcx]
    exact hL2 x (f₁ x) (f₂ x) (U x) (V₁ x) (V₂ x) (A x) ((lcOf g B x) w) (C x) (D x)
  have hc5 : cov2Rm g x (U x) ((f₁ • V₁ + f₂ • V₂) x) (A x) (B x) ((lcOf g (C) x) w) (D x)
      = f₁ x * cov2Rm g x (U x) (V₁ x) (A x) (B x) ((lcOf g (C) x) w) (D x) + f₂ x * cov2Rm g x (U x) (V₂ x) (A x) (B x) ((lcOf g (C) x) w) (D x) := by
    rw [hcx]
    exact hL2 x (f₁ x) (f₂ x) (U x) (V₁ x) (V₂ x) (A x) (B x) ((lcOf g C x) w) (D x)
  have hc6 : cov2Rm g x (U x) ((f₁ • V₁ + f₂ • V₂) x) (A x) (B x) (C x) ((lcOf g (D) x) w)
      = f₁ x * cov2Rm g x (U x) (V₁ x) (A x) (B x) (C x) ((lcOf g (D) x) w) + f₂ x * cov2Rm g x (U x) (V₂ x) (A x) (B x) (C x) ((lcOf g (D) x) w) := by
    rw [hcx]
    exact hL2 x (f₁ x) (f₂ x) (U x) (V₁ x) (V₂ x) (A x) (B x) (C x) ((lcOf g D x) w)
  simp only [cov3RmExt]
  rw [hT, hc1, hc2, hc3, hc4, hc5, hc6]
  ring

theorem cov3RmExt_linear_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A₁ A₂ B C D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA₁ : CMDiff ∞ (T% A₁)) (hA₂ : CMDiff ∞ (T% A₂)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    cov3RmExt g x w U V (f₁ • A₁ + f₂ • A₂) B C D
      = f₁ x * cov3RmExt g x w U V A₁ B C D + f₂ x * cov3RmExt g x w U V A₂ B C D := by
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6⟩ := cov2Rm_linear_slots_self hLC g
  have hX : CMDiff ∞ (T% (f₁ • A₁ + f₂ • A₂)) :=
    (hf₁.smul_section hA₁).add_section (hf₂.smul_section hA₂)
  have hΦ₁ : CMDiff ∞ (fun y : M => cov2Rm g y (U y) (V y) (A₁ y) (B y) (C y) (D y)) :=
    cov2Rm_field_smooth hLC g hU hV hA₁ hB hC hD
  have hΦ₂ : CMDiff ∞ (fun y : M => cov2Rm g y (U y) (V y) (A₂ y) (B y) (C y) (D y)) :=
    cov2Rm_field_smooth hLC g hU hV hA₂ hB hC hD
  have hΦ₁d : MDiffAt (fun y : M => cov2Rm g y (U y) (V y) (A₁ y) (B y) (C y) (D y)) x := hΦ₁.mdifferentiableAt (by simp)
  have hΦ₂d : MDiffAt (fun y : M => cov2Rm g y (U y) (V y) (A₂ y) (B y) (C y) (D y)) x := hΦ₂.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  have hpt : ∀ y : M, cov2Rm g y (U y) (V y) ((f₁ • A₁ + f₂ • A₂) y) (B y) (C y) (D y) = f₁ y * cov2Rm g y (U y) (V y) (A₁ y) (B y) (C y) (D y) + f₂ y * cov2Rm g y (U y) (V y) (A₂ y) (B y) (C y) (D y) := by
    intro y
    rw [show (f₁ • A₁ + f₂ • A₂) y = f₁ y • A₁ y + f₂ y • A₂ y from rfl]
    exact hL3 y (f₁ y) (f₂ y) (U y) (V y) (A₁ y) (A₂ y) (B y) (C y) (D y)
  have hT : mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) ((f₁ • A₁ + f₂ • A₂) y) (B y) (C y) (D y)) x w
      = (f₁ x * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A₁ y) (B y) (C y) (D y)) x w
          + mvfderiv I f₁ x w * cov2Rm g x (U x) (V x) (A₁ x) (B x) (C x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A₂ y) (B y) (C y) (D y)) x w
          + mvfderiv I f₂ x w * cov2Rm g x (U x) (V x) (A₂ x) (B x) (C x) (D x)) := by
    have hfun : (fun y : M => cov2Rm g y (U y) (V y) ((f₁ • A₁ + f₂ • A₂) y) (B y) (C y) (D y))
        = f₁ * (fun y : M => cov2Rm g y (U y) (V y) (A₁ y) (B y) (C y) (D y)) + f₂ * (fun y : M => cov2Rm g y (U y) (V y) (A₂ y) (B y) (C y) (D y)) := by
      funext y
      exact hpt y
    rw [hfun, mvfderiv_add (hf₁d.mul hΦ₁d) (hf₂d.mul hΦ₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => cov2Rm g y (U y) (V y) (A₁ y) (B y) (C y) (D y)) hf₁d hΦ₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => cov2Rm g y (U y) (V y) (A₂ y) (B y) (C y) (D y)) hf₂d hΦ₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hcx : (f₁ • A₁ + f₂ • A₂) x = f₁ x • A₁ x + f₂ x • A₂ x := rfl
  have hc1 : cov2Rm g x ((lcOf g (U) x) w) (V x) ((f₁ • A₁ + f₂ • A₂) x) (B x) (C x) (D x)
      = f₁ x * cov2Rm g x ((lcOf g (U) x) w) (V x) (A₁ x) (B x) (C x) (D x) + f₂ x * cov2Rm g x ((lcOf g (U) x) w) (V x) (A₂ x) (B x) (C x) (D x) := by
    rw [hcx]
    exact hL3 x (f₁ x) (f₂ x) ((lcOf g U x) w) (V x) (A₁ x) (A₂ x) (B x) (C x) (D x)
  have hc2 : cov2Rm g x (U x) ((lcOf g (V) x) w) ((f₁ • A₁ + f₂ • A₂) x) (B x) (C x) (D x)
      = f₁ x * cov2Rm g x (U x) ((lcOf g (V) x) w) (A₁ x) (B x) (C x) (D x) + f₂ x * cov2Rm g x (U x) ((lcOf g (V) x) w) (A₂ x) (B x) (C x) (D x) := by
    rw [hcx]
    exact hL3 x (f₁ x) (f₂ x) (U x) ((lcOf g V x) w) (A₁ x) (A₂ x) (B x) (C x) (D x)
  have hc3 : cov2Rm g x (U x) (V x) ((lcOf g (f₁ • A₁ + f₂ • A₂) x) w) (B x) (C x) (D x)
      = (f₁ x * cov2Rm g x (U x) (V x) ((lcOf g (A₁) x) w) (B x) (C x) (D x) + mvfderiv I f₁ x w * cov2Rm g x (U x) (V x) (A₁ x) (B x) (C x) (D x))
        + (f₂ x * cov2Rm g x (U x) (V x) ((lcOf g (A₂) x) w) (B x) (C x) (D x) + mvfderiv I f₂ x w * cov2Rm g x (U x) (V x) (A₂ x) (B x) (C x) (D x)) := by
    have h1d : MDiffAt (T% (f₁ • A₁)) x := (hf₁.smul_section hA₁).mdifferentiableAt (by simp)
    have h2d : MDiffAt (T% (f₂ • A₂)) x := (hf₂.smul_section hA₂).mdifferentiableAt (by simp)
    have hA₁d : MDiffAt (T% A₁) x := hA₁.mdifferentiableAt (by simp)
    have hA₂d : MDiffAt (T% A₂) x := hA₂.mdifferentiableAt (by simp)
    have hlc := (lcOf g).isCovariantDerivativeOn.add (s := Set.univ) (σ := f₁ • A₁)
      (σ' := f₂ • A₂) h1d h2d
    have hle₁ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := A₁) (g := f₁)
      hA₁d hf₁d
    have hle₂ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := A₂) (g := f₂)
      hA₂d hf₂d
    have hadd3 : ∀ (Z W : TangentSpace I x),
        cov2Rm g x (U x) (V x) (Z + W) (B x) (C x) (D x)
          = cov2Rm g x (U x) (V x) (Z) (B x) (C x) (D x) + cov2Rm g x (U x) (V x) (W) (B x) (C x) (D x) := by
      intro Z W
      simpa using hL3 x 1 1 (U x) (V x) Z W (B x) (C x) (D x)
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, add_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₁, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₂, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [hadd3 (f₁ x • (lcOf g A₁ x) w + mvfderiv I f₁ x w • A₁ x)
        (f₂ x • (lcOf g A₂ x) w + mvfderiv I f₂ x w • A₂ x)]
    rw [hL3 x (f₁ x) (mvfderiv I f₁ x w) (U x) (V x) ((lcOf g A₁ x) w) (A₁ x) (B x) (C x) (D x)]
    rw [hL3 x (f₂ x) (mvfderiv I f₂ x w) (U x) (V x) ((lcOf g A₂ x) w) (A₂ x) (B x) (C x) (D x)]
  have hc4 : cov2Rm g x (U x) (V x) ((f₁ • A₁ + f₂ • A₂) x) ((lcOf g (B) x) w) (C x) (D x)
      = f₁ x * cov2Rm g x (U x) (V x) (A₁ x) ((lcOf g (B) x) w) (C x) (D x) + f₂ x * cov2Rm g x (U x) (V x) (A₂ x) ((lcOf g (B) x) w) (C x) (D x) := by
    rw [hcx]
    exact hL3 x (f₁ x) (f₂ x) (U x) (V x) (A₁ x) (A₂ x) ((lcOf g B x) w) (C x) (D x)
  have hc5 : cov2Rm g x (U x) (V x) ((f₁ • A₁ + f₂ • A₂) x) (B x) ((lcOf g (C) x) w) (D x)
      = f₁ x * cov2Rm g x (U x) (V x) (A₁ x) (B x) ((lcOf g (C) x) w) (D x) + f₂ x * cov2Rm g x (U x) (V x) (A₂ x) (B x) ((lcOf g (C) x) w) (D x) := by
    rw [hcx]
    exact hL3 x (f₁ x) (f₂ x) (U x) (V x) (A₁ x) (A₂ x) (B x) ((lcOf g C x) w) (D x)
  have hc6 : cov2Rm g x (U x) (V x) ((f₁ • A₁ + f₂ • A₂) x) (B x) (C x) ((lcOf g (D) x) w)
      = f₁ x * cov2Rm g x (U x) (V x) (A₁ x) (B x) (C x) ((lcOf g (D) x) w) + f₂ x * cov2Rm g x (U x) (V x) (A₂ x) (B x) (C x) ((lcOf g (D) x) w) := by
    rw [hcx]
    exact hL3 x (f₁ x) (f₂ x) (U x) (V x) (A₁ x) (A₂ x) (B x) (C x) ((lcOf g D x) w)
  simp only [cov3RmExt]
  rw [hT, hc1, hc2, hc3, hc4, hc5, hc6]
  ring

theorem cov3RmExt_linear_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A B₁ B₂ C D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB₁ : CMDiff ∞ (T% B₁)) (hB₂ : CMDiff ∞ (T% B₂)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    cov3RmExt g x w U V A (f₁ • B₁ + f₂ • B₂) C D
      = f₁ x * cov3RmExt g x w U V A B₁ C D + f₂ x * cov3RmExt g x w U V A B₂ C D := by
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6⟩ := cov2Rm_linear_slots_self hLC g
  have hX : CMDiff ∞ (T% (f₁ • B₁ + f₂ • B₂)) :=
    (hf₁.smul_section hB₁).add_section (hf₂.smul_section hB₂)
  have hΦ₁ : CMDiff ∞ (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₁ y) (C y) (D y)) :=
    cov2Rm_field_smooth hLC g hU hV hA hB₁ hC hD
  have hΦ₂ : CMDiff ∞ (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₂ y) (C y) (D y)) :=
    cov2Rm_field_smooth hLC g hU hV hA hB₂ hC hD
  have hΦ₁d : MDiffAt (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₁ y) (C y) (D y)) x := hΦ₁.mdifferentiableAt (by simp)
  have hΦ₂d : MDiffAt (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₂ y) (C y) (D y)) x := hΦ₂.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  have hpt : ∀ y : M, cov2Rm g y (U y) (V y) (A y) ((f₁ • B₁ + f₂ • B₂) y) (C y) (D y) = f₁ y * cov2Rm g y (U y) (V y) (A y) (B₁ y) (C y) (D y) + f₂ y * cov2Rm g y (U y) (V y) (A y) (B₂ y) (C y) (D y) := by
    intro y
    rw [show (f₁ • B₁ + f₂ • B₂) y = f₁ y • B₁ y + f₂ y • B₂ y from rfl]
    exact hL4 y (f₁ y) (f₂ y) (U y) (V y) (A y) (B₁ y) (B₂ y) (C y) (D y)
  have hT : mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) ((f₁ • B₁ + f₂ • B₂) y) (C y) (D y)) x w
      = (f₁ x * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₁ y) (C y) (D y)) x w
          + mvfderiv I f₁ x w * cov2Rm g x (U x) (V x) (A x) (B₁ x) (C x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₂ y) (C y) (D y)) x w
          + mvfderiv I f₂ x w * cov2Rm g x (U x) (V x) (A x) (B₂ x) (C x) (D x)) := by
    have hfun : (fun y : M => cov2Rm g y (U y) (V y) (A y) ((f₁ • B₁ + f₂ • B₂) y) (C y) (D y))
        = f₁ * (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₁ y) (C y) (D y)) + f₂ * (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₂ y) (C y) (D y)) := by
      funext y
      exact hpt y
    rw [hfun, mvfderiv_add (hf₁d.mul hΦ₁d) (hf₂d.mul hΦ₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => cov2Rm g y (U y) (V y) (A y) (B₁ y) (C y) (D y)) hf₁d hΦ₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => cov2Rm g y (U y) (V y) (A y) (B₂ y) (C y) (D y)) hf₂d hΦ₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hcx : (f₁ • B₁ + f₂ • B₂) x = f₁ x • B₁ x + f₂ x • B₂ x := rfl
  have hc1 : cov2Rm g x ((lcOf g (U) x) w) (V x) (A x) ((f₁ • B₁ + f₂ • B₂) x) (C x) (D x)
      = f₁ x * cov2Rm g x ((lcOf g (U) x) w) (V x) (A x) (B₁ x) (C x) (D x) + f₂ x * cov2Rm g x ((lcOf g (U) x) w) (V x) (A x) (B₂ x) (C x) (D x) := by
    rw [hcx]
    exact hL4 x (f₁ x) (f₂ x) ((lcOf g U x) w) (V x) (A x) (B₁ x) (B₂ x) (C x) (D x)
  have hc2 : cov2Rm g x (U x) ((lcOf g (V) x) w) (A x) ((f₁ • B₁ + f₂ • B₂) x) (C x) (D x)
      = f₁ x * cov2Rm g x (U x) ((lcOf g (V) x) w) (A x) (B₁ x) (C x) (D x) + f₂ x * cov2Rm g x (U x) ((lcOf g (V) x) w) (A x) (B₂ x) (C x) (D x) := by
    rw [hcx]
    exact hL4 x (f₁ x) (f₂ x) (U x) ((lcOf g V x) w) (A x) (B₁ x) (B₂ x) (C x) (D x)
  have hc3 : cov2Rm g x (U x) (V x) ((lcOf g (A) x) w) ((f₁ • B₁ + f₂ • B₂) x) (C x) (D x)
      = f₁ x * cov2Rm g x (U x) (V x) ((lcOf g (A) x) w) (B₁ x) (C x) (D x) + f₂ x * cov2Rm g x (U x) (V x) ((lcOf g (A) x) w) (B₂ x) (C x) (D x) := by
    rw [hcx]
    exact hL4 x (f₁ x) (f₂ x) (U x) (V x) ((lcOf g A x) w) (B₁ x) (B₂ x) (C x) (D x)
  have hc4 : cov2Rm g x (U x) (V x) (A x) ((lcOf g (f₁ • B₁ + f₂ • B₂) x) w) (C x) (D x)
      = (f₁ x * cov2Rm g x (U x) (V x) (A x) ((lcOf g (B₁) x) w) (C x) (D x) + mvfderiv I f₁ x w * cov2Rm g x (U x) (V x) (A x) (B₁ x) (C x) (D x))
        + (f₂ x * cov2Rm g x (U x) (V x) (A x) ((lcOf g (B₂) x) w) (C x) (D x) + mvfderiv I f₂ x w * cov2Rm g x (U x) (V x) (A x) (B₂ x) (C x) (D x)) := by
    have h1d : MDiffAt (T% (f₁ • B₁)) x := (hf₁.smul_section hB₁).mdifferentiableAt (by simp)
    have h2d : MDiffAt (T% (f₂ • B₂)) x := (hf₂.smul_section hB₂).mdifferentiableAt (by simp)
    have hB₁d : MDiffAt (T% B₁) x := hB₁.mdifferentiableAt (by simp)
    have hB₂d : MDiffAt (T% B₂) x := hB₂.mdifferentiableAt (by simp)
    have hlc := (lcOf g).isCovariantDerivativeOn.add (s := Set.univ) (σ := f₁ • B₁)
      (σ' := f₂ • B₂) h1d h2d
    have hle₁ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := B₁) (g := f₁)
      hB₁d hf₁d
    have hle₂ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := B₂) (g := f₂)
      hB₂d hf₂d
    have hadd4 : ∀ (Z W : TangentSpace I x),
        cov2Rm g x (U x) (V x) (A x) (Z + W) (C x) (D x)
          = cov2Rm g x (U x) (V x) (A x) (Z) (C x) (D x) + cov2Rm g x (U x) (V x) (A x) (W) (C x) (D x) := by
      intro Z W
      simpa using hL4 x 1 1 (U x) (V x) (A x) Z W (C x) (D x)
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, add_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₁, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₂, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [hadd4 (f₁ x • (lcOf g B₁ x) w + mvfderiv I f₁ x w • B₁ x)
        (f₂ x • (lcOf g B₂ x) w + mvfderiv I f₂ x w • B₂ x)]
    rw [hL4 x (f₁ x) (mvfderiv I f₁ x w) (U x) (V x) (A x) ((lcOf g B₁ x) w) (B₁ x) (C x) (D x)]
    rw [hL4 x (f₂ x) (mvfderiv I f₂ x w) (U x) (V x) (A x) ((lcOf g B₂ x) w) (B₂ x) (C x) (D x)]
  have hc5 : cov2Rm g x (U x) (V x) (A x) ((f₁ • B₁ + f₂ • B₂) x) ((lcOf g (C) x) w) (D x)
      = f₁ x * cov2Rm g x (U x) (V x) (A x) (B₁ x) ((lcOf g (C) x) w) (D x) + f₂ x * cov2Rm g x (U x) (V x) (A x) (B₂ x) ((lcOf g (C) x) w) (D x) := by
    rw [hcx]
    exact hL4 x (f₁ x) (f₂ x) (U x) (V x) (A x) (B₁ x) (B₂ x) ((lcOf g C x) w) (D x)
  have hc6 : cov2Rm g x (U x) (V x) (A x) ((f₁ • B₁ + f₂ • B₂) x) (C x) ((lcOf g (D) x) w)
      = f₁ x * cov2Rm g x (U x) (V x) (A x) (B₁ x) (C x) ((lcOf g (D) x) w) + f₂ x * cov2Rm g x (U x) (V x) (A x) (B₂ x) (C x) ((lcOf g (D) x) w) := by
    rw [hcx]
    exact hL4 x (f₁ x) (f₂ x) (U x) (V x) (A x) (B₁ x) (B₂ x) (C x) ((lcOf g D x) w)
  simp only [cov3RmExt]
  rw [hT, hc1, hc2, hc3, hc4, hc5, hc6]
  ring

theorem cov3RmExt_linear_fif (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A B C₁ C₂ D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC₁ : CMDiff ∞ (T% C₁)) (hC₂ : CMDiff ∞ (T% C₂)) (hD : CMDiff ∞ (T% D)) {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    cov3RmExt g x w U V A B (f₁ • C₁ + f₂ • C₂) D
      = f₁ x * cov3RmExt g x w U V A B C₁ D + f₂ x * cov3RmExt g x w U V A B C₂ D := by
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6⟩ := cov2Rm_linear_slots_self hLC g
  have hX : CMDiff ∞ (T% (f₁ • C₁ + f₂ • C₂)) :=
    (hf₁.smul_section hC₁).add_section (hf₂.smul_section hC₂)
  have hΦ₁ : CMDiff ∞ (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₁ y) (D y)) :=
    cov2Rm_field_smooth hLC g hU hV hA hB hC₁ hD
  have hΦ₂ : CMDiff ∞ (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₂ y) (D y)) :=
    cov2Rm_field_smooth hLC g hU hV hA hB hC₂ hD
  have hΦ₁d : MDiffAt (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₁ y) (D y)) x := hΦ₁.mdifferentiableAt (by simp)
  have hΦ₂d : MDiffAt (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₂ y) (D y)) x := hΦ₂.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  have hpt : ∀ y : M, cov2Rm g y (U y) (V y) (A y) (B y) ((f₁ • C₁ + f₂ • C₂) y) (D y) = f₁ y * cov2Rm g y (U y) (V y) (A y) (B y) (C₁ y) (D y) + f₂ y * cov2Rm g y (U y) (V y) (A y) (B y) (C₂ y) (D y) := by
    intro y
    rw [show (f₁ • C₁ + f₂ • C₂) y = f₁ y • C₁ y + f₂ y • C₂ y from rfl]
    exact hL5 y (f₁ y) (f₂ y) (U y) (V y) (A y) (B y) (C₁ y) (C₂ y) (D y)
  have hT : mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) ((f₁ • C₁ + f₂ • C₂) y) (D y)) x w
      = (f₁ x * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₁ y) (D y)) x w
          + mvfderiv I f₁ x w * cov2Rm g x (U x) (V x) (A x) (B x) (C₁ x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₂ y) (D y)) x w
          + mvfderiv I f₂ x w * cov2Rm g x (U x) (V x) (A x) (B x) (C₂ x) (D x)) := by
    have hfun : (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) ((f₁ • C₁ + f₂ • C₂) y) (D y))
        = f₁ * (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₁ y) (D y)) + f₂ * (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₂ y) (D y)) := by
      funext y
      exact hpt y
    rw [hfun, mvfderiv_add (hf₁d.mul hΦ₁d) (hf₂d.mul hΦ₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₁ y) (D y)) hf₁d hΦ₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₂ y) (D y)) hf₂d hΦ₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hcx : (f₁ • C₁ + f₂ • C₂) x = f₁ x • C₁ x + f₂ x • C₂ x := rfl
  have hc1 : cov2Rm g x ((lcOf g (U) x) w) (V x) (A x) (B x) ((f₁ • C₁ + f₂ • C₂) x) (D x)
      = f₁ x * cov2Rm g x ((lcOf g (U) x) w) (V x) (A x) (B x) (C₁ x) (D x) + f₂ x * cov2Rm g x ((lcOf g (U) x) w) (V x) (A x) (B x) (C₂ x) (D x) := by
    rw [hcx]
    exact hL5 x (f₁ x) (f₂ x) ((lcOf g U x) w) (V x) (A x) (B x) (C₁ x) (C₂ x) (D x)
  have hc2 : cov2Rm g x (U x) ((lcOf g (V) x) w) (A x) (B x) ((f₁ • C₁ + f₂ • C₂) x) (D x)
      = f₁ x * cov2Rm g x (U x) ((lcOf g (V) x) w) (A x) (B x) (C₁ x) (D x) + f₂ x * cov2Rm g x (U x) ((lcOf g (V) x) w) (A x) (B x) (C₂ x) (D x) := by
    rw [hcx]
    exact hL5 x (f₁ x) (f₂ x) (U x) ((lcOf g V x) w) (A x) (B x) (C₁ x) (C₂ x) (D x)
  have hc3 : cov2Rm g x (U x) (V x) ((lcOf g (A) x) w) (B x) ((f₁ • C₁ + f₂ • C₂) x) (D x)
      = f₁ x * cov2Rm g x (U x) (V x) ((lcOf g (A) x) w) (B x) (C₁ x) (D x) + f₂ x * cov2Rm g x (U x) (V x) ((lcOf g (A) x) w) (B x) (C₂ x) (D x) := by
    rw [hcx]
    exact hL5 x (f₁ x) (f₂ x) (U x) (V x) ((lcOf g A x) w) (B x) (C₁ x) (C₂ x) (D x)
  have hc4 : cov2Rm g x (U x) (V x) (A x) ((lcOf g (B) x) w) ((f₁ • C₁ + f₂ • C₂) x) (D x)
      = f₁ x * cov2Rm g x (U x) (V x) (A x) ((lcOf g (B) x) w) (C₁ x) (D x) + f₂ x * cov2Rm g x (U x) (V x) (A x) ((lcOf g (B) x) w) (C₂ x) (D x) := by
    rw [hcx]
    exact hL5 x (f₁ x) (f₂ x) (U x) (V x) (A x) ((lcOf g B x) w) (C₁ x) (C₂ x) (D x)
  have hc5 : cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g (f₁ • C₁ + f₂ • C₂) x) w) (D x)
      = (f₁ x * cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g (C₁) x) w) (D x) + mvfderiv I f₁ x w * cov2Rm g x (U x) (V x) (A x) (B x) (C₁ x) (D x))
        + (f₂ x * cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g (C₂) x) w) (D x) + mvfderiv I f₂ x w * cov2Rm g x (U x) (V x) (A x) (B x) (C₂ x) (D x)) := by
    have h1d : MDiffAt (T% (f₁ • C₁)) x := (hf₁.smul_section hC₁).mdifferentiableAt (by simp)
    have h2d : MDiffAt (T% (f₂ • C₂)) x := (hf₂.smul_section hC₂).mdifferentiableAt (by simp)
    have hC₁d : MDiffAt (T% C₁) x := hC₁.mdifferentiableAt (by simp)
    have hC₂d : MDiffAt (T% C₂) x := hC₂.mdifferentiableAt (by simp)
    have hlc := (lcOf g).isCovariantDerivativeOn.add (s := Set.univ) (σ := f₁ • C₁)
      (σ' := f₂ • C₂) h1d h2d
    have hle₁ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := C₁) (g := f₁)
      hC₁d hf₁d
    have hle₂ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := C₂) (g := f₂)
      hC₂d hf₂d
    have hadd5 : ∀ (Z W : TangentSpace I x),
        cov2Rm g x (U x) (V x) (A x) (B x) (Z + W) (D x)
          = cov2Rm g x (U x) (V x) (A x) (B x) (Z) (D x) + cov2Rm g x (U x) (V x) (A x) (B x) (W) (D x) := by
      intro Z W
      simpa using hL5 x 1 1 (U x) (V x) (A x) (B x) Z W (D x)
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, add_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₁, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₂, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [hadd5 (f₁ x • (lcOf g C₁ x) w + mvfderiv I f₁ x w • C₁ x)
        (f₂ x • (lcOf g C₂ x) w + mvfderiv I f₂ x w • C₂ x)]
    rw [hL5 x (f₁ x) (mvfderiv I f₁ x w) (U x) (V x) (A x) (B x) ((lcOf g C₁ x) w) (C₁ x) (D x)]
    rw [hL5 x (f₂ x) (mvfderiv I f₂ x w) (U x) (V x) (A x) (B x) ((lcOf g C₂ x) w) (C₂ x) (D x)]
  have hc6 : cov2Rm g x (U x) (V x) (A x) (B x) ((f₁ • C₁ + f₂ • C₂) x) ((lcOf g (D) x) w)
      = f₁ x * cov2Rm g x (U x) (V x) (A x) (B x) (C₁ x) ((lcOf g (D) x) w) + f₂ x * cov2Rm g x (U x) (V x) (A x) (B x) (C₂ x) ((lcOf g (D) x) w) := by
    rw [hcx]
    exact hL5 x (f₁ x) (f₂ x) (U x) (V x) (A x) (B x) (C₁ x) (C₂ x) ((lcOf g D x) w)
  simp only [cov3RmExt]
  rw [hT, hc1, hc2, hc3, hc4, hc5, hc6]
  ring

theorem cov3RmExt_linear_sixth (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A B C D₁ D₂ : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD₁ : CMDiff ∞ (T% D₁)) (hD₂ : CMDiff ∞ (T% D₂)) {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    cov3RmExt g x w U V A B C (f₁ • D₁ + f₂ • D₂)
      = f₁ x * cov3RmExt g x w U V A B C D₁ + f₂ x * cov3RmExt g x w U V A B C D₂ := by
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6⟩ := cov2Rm_linear_slots_self hLC g
  have hX : CMDiff ∞ (T% (f₁ • D₁ + f₂ • D₂)) :=
    (hf₁.smul_section hD₁).add_section (hf₂.smul_section hD₂)
  have hΦ₁ : CMDiff ∞ (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₁ y)) :=
    cov2Rm_field_smooth hLC g hU hV hA hB hC hD₁
  have hΦ₂ : CMDiff ∞ (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₂ y)) :=
    cov2Rm_field_smooth hLC g hU hV hA hB hC hD₂
  have hΦ₁d : MDiffAt (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₁ y)) x := hΦ₁.mdifferentiableAt (by simp)
  have hΦ₂d : MDiffAt (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₂ y)) x := hΦ₂.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  have hpt : ∀ y : M, cov2Rm g y (U y) (V y) (A y) (B y) (C y) ((f₁ • D₁ + f₂ • D₂) y) = f₁ y * cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₁ y) + f₂ y * cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₂ y) := by
    intro y
    rw [show (f₁ • D₁ + f₂ • D₂) y = f₁ y • D₁ y + f₂ y • D₂ y from rfl]
    exact hL6 y (f₁ y) (f₂ y) (U y) (V y) (A y) (B y) (C y) (D₁ y) (D₂ y)
  have hT : mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) ((f₁ • D₁ + f₂ • D₂) y)) x w
      = (f₁ x * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₁ y)) x w
          + mvfderiv I f₁ x w * cov2Rm g x (U x) (V x) (A x) (B x) (C x) (D₁ x))
        + (f₂ x * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₂ y)) x w
          + mvfderiv I f₂ x w * cov2Rm g x (U x) (V x) (A x) (B x) (C x) (D₂ x)) := by
    have hfun : (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) ((f₁ • D₁ + f₂ • D₂) y))
        = f₁ * (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₁ y)) + f₂ * (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₂ y)) := by
      funext y
      exact hpt y
    rw [hfun, mvfderiv_add (hf₁d.mul hΦ₁d) (hf₂d.mul hΦ₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₁ y)) hf₁d hΦ₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₂ y)) hf₂d hΦ₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hcx : (f₁ • D₁ + f₂ • D₂) x = f₁ x • D₁ x + f₂ x • D₂ x := rfl
  have hc1 : cov2Rm g x ((lcOf g (U) x) w) (V x) (A x) (B x) (C x) ((f₁ • D₁ + f₂ • D₂) x)
      = f₁ x * cov2Rm g x ((lcOf g (U) x) w) (V x) (A x) (B x) (C x) (D₁ x) + f₂ x * cov2Rm g x ((lcOf g (U) x) w) (V x) (A x) (B x) (C x) (D₂ x) := by
    rw [hcx]
    exact hL6 x (f₁ x) (f₂ x) ((lcOf g U x) w) (V x) (A x) (B x) (C x) (D₁ x) (D₂ x)
  have hc2 : cov2Rm g x (U x) ((lcOf g (V) x) w) (A x) (B x) (C x) ((f₁ • D₁ + f₂ • D₂) x)
      = f₁ x * cov2Rm g x (U x) ((lcOf g (V) x) w) (A x) (B x) (C x) (D₁ x) + f₂ x * cov2Rm g x (U x) ((lcOf g (V) x) w) (A x) (B x) (C x) (D₂ x) := by
    rw [hcx]
    exact hL6 x (f₁ x) (f₂ x) (U x) ((lcOf g V x) w) (A x) (B x) (C x) (D₁ x) (D₂ x)
  have hc3 : cov2Rm g x (U x) (V x) ((lcOf g (A) x) w) (B x) (C x) ((f₁ • D₁ + f₂ • D₂) x)
      = f₁ x * cov2Rm g x (U x) (V x) ((lcOf g (A) x) w) (B x) (C x) (D₁ x) + f₂ x * cov2Rm g x (U x) (V x) ((lcOf g (A) x) w) (B x) (C x) (D₂ x) := by
    rw [hcx]
    exact hL6 x (f₁ x) (f₂ x) (U x) (V x) ((lcOf g A x) w) (B x) (C x) (D₁ x) (D₂ x)
  have hc4 : cov2Rm g x (U x) (V x) (A x) ((lcOf g (B) x) w) (C x) ((f₁ • D₁ + f₂ • D₂) x)
      = f₁ x * cov2Rm g x (U x) (V x) (A x) ((lcOf g (B) x) w) (C x) (D₁ x) + f₂ x * cov2Rm g x (U x) (V x) (A x) ((lcOf g (B) x) w) (C x) (D₂ x) := by
    rw [hcx]
    exact hL6 x (f₁ x) (f₂ x) (U x) (V x) (A x) ((lcOf g B x) w) (C x) (D₁ x) (D₂ x)
  have hc5 : cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g (C) x) w) ((f₁ • D₁ + f₂ • D₂) x)
      = f₁ x * cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g (C) x) w) (D₁ x) + f₂ x * cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g (C) x) w) (D₂ x) := by
    rw [hcx]
    exact hL6 x (f₁ x) (f₂ x) (U x) (V x) (A x) (B x) ((lcOf g C x) w) (D₁ x) (D₂ x)
  have hc6 : cov2Rm g x (U x) (V x) (A x) (B x) (C x) ((lcOf g (f₁ • D₁ + f₂ • D₂) x) w)
      = (f₁ x * cov2Rm g x (U x) (V x) (A x) (B x) (C x) ((lcOf g (D₁) x) w) + mvfderiv I f₁ x w * cov2Rm g x (U x) (V x) (A x) (B x) (C x) (D₁ x))
        + (f₂ x * cov2Rm g x (U x) (V x) (A x) (B x) (C x) ((lcOf g (D₂) x) w) + mvfderiv I f₂ x w * cov2Rm g x (U x) (V x) (A x) (B x) (C x) (D₂ x)) := by
    have h1d : MDiffAt (T% (f₁ • D₁)) x := (hf₁.smul_section hD₁).mdifferentiableAt (by simp)
    have h2d : MDiffAt (T% (f₂ • D₂)) x := (hf₂.smul_section hD₂).mdifferentiableAt (by simp)
    have hD₁d : MDiffAt (T% D₁) x := hD₁.mdifferentiableAt (by simp)
    have hD₂d : MDiffAt (T% D₂) x := hD₂.mdifferentiableAt (by simp)
    have hlc := (lcOf g).isCovariantDerivativeOn.add (s := Set.univ) (σ := f₁ • D₁)
      (σ' := f₂ • D₂) h1d h2d
    have hle₁ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := D₁) (g := f₁)
      hD₁d hf₁d
    have hle₂ := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := D₂) (g := f₂)
      hD₂d hf₂d
    have hadd6 : ∀ (Z W : TangentSpace I x),
        cov2Rm g x (U x) (V x) (A x) (B x) (C x) (Z + W)
          = cov2Rm g x (U x) (V x) (A x) (B x) (C x) (Z) + cov2Rm g x (U x) (V x) (A x) (B x) (C x) (W) := by
      intro Z W
      simpa using hL6 x 1 1 (U x) (V x) (A x) (B x) (C x) Z W
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, add_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₁, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hle₂, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [hadd6 (f₁ x • (lcOf g D₁ x) w + mvfderiv I f₁ x w • D₁ x)
        (f₂ x • (lcOf g D₂ x) w + mvfderiv I f₂ x w • D₂ x)]
    rw [hL6 x (f₁ x) (mvfderiv I f₁ x w) (U x) (V x) (A x) (B x) (C x) ((lcOf g D₁ x) w) (D₁ x)]
    rw [hL6 x (f₂ x) (mvfderiv I f₂ x w) (U x) (V x) (A x) (B x) (C x) ((lcOf g D₂ x) w) (D₂ x)]
  simp only [cov3RmExt]
  rw [hT, hc1, hc2, hc3, hc4, hc5, hc6]
  ring

theorem cov3RmExt_germ_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U₁ U₂ V A B C D : Π y : M, TangentSpace I y}
    (hU₁ : CMDiff ∞ (T% U₁)) (hU₂ : CMDiff ∞ (T% U₂)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) (h : U₁ =ᶠ[𝓝 x] U₂) :
    cov3RmExt g x w U₁ V A B C D = cov3RmExt g x w U₂ V A B C D := by
  have hfun : (fun y : M => cov2Rm g y (U₁ y) (V y) (A y) (B y) (C y) (D y))
      =ᶠ[𝓝 x] (fun y : M => cov2Rm g y (U₂ y) (V y) (A y) (B y) (C y) (D y)) := by
    filter_upwards [h] with y hy
    rw [hy]
  have hlc : (lcOf g U₁ x) = (lcOf g U₂ x) :=
    lcOf_congr_eventuallyEq g (hU₁.mdifferentiableAt (by simp)) (hU₂.mdifferentiableAt (by simp)) h
  have hXx : U₁ x = U₂ x := h.self_of_nhds
  have hmv : mvfderiv I (fun y : M => cov2Rm g y (U₁ y) (V y) (A y) (B y) (C y) (D y)) x
      = mvfderiv I (fun y : M => cov2Rm g y (U₂ y) (V y) (A y) (B y) (C y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) hfun
  simp only [cov3RmExt]
  rw [congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L w) hmv,
    congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, hXx]

theorem cov3RmExt_germ_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V₁ V₂ A B C D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV₁ : CMDiff ∞ (T% V₁)) (hV₂ : CMDiff ∞ (T% V₂)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) (h : V₁ =ᶠ[𝓝 x] V₂) :
    cov3RmExt g x w U V₁ A B C D = cov3RmExt g x w U V₂ A B C D := by
  have hfun : (fun y : M => cov2Rm g y (U y) (V₁ y) (A y) (B y) (C y) (D y))
      =ᶠ[𝓝 x] (fun y : M => cov2Rm g y (U y) (V₂ y) (A y) (B y) (C y) (D y)) := by
    filter_upwards [h] with y hy
    rw [hy]
  have hlc : (lcOf g V₁ x) = (lcOf g V₂ x) :=
    lcOf_congr_eventuallyEq g (hV₁.mdifferentiableAt (by simp)) (hV₂.mdifferentiableAt (by simp)) h
  have hXx : V₁ x = V₂ x := h.self_of_nhds
  have hmv : mvfderiv I (fun y : M => cov2Rm g y (U y) (V₁ y) (A y) (B y) (C y) (D y)) x
      = mvfderiv I (fun y : M => cov2Rm g y (U y) (V₂ y) (A y) (B y) (C y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) hfun
  simp only [cov3RmExt]
  rw [congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L w) hmv,
    congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, hXx]

theorem cov3RmExt_germ_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A₁ A₂ B C D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA₁ : CMDiff ∞ (T% A₁)) (hA₂ : CMDiff ∞ (T% A₂)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) (h : A₁ =ᶠ[𝓝 x] A₂) :
    cov3RmExt g x w U V A₁ B C D = cov3RmExt g x w U V A₂ B C D := by
  have hfun : (fun y : M => cov2Rm g y (U y) (V y) (A₁ y) (B y) (C y) (D y))
      =ᶠ[𝓝 x] (fun y : M => cov2Rm g y (U y) (V y) (A₂ y) (B y) (C y) (D y)) := by
    filter_upwards [h] with y hy
    rw [hy]
  have hlc : (lcOf g A₁ x) = (lcOf g A₂ x) :=
    lcOf_congr_eventuallyEq g (hA₁.mdifferentiableAt (by simp)) (hA₂.mdifferentiableAt (by simp)) h
  have hXx : A₁ x = A₂ x := h.self_of_nhds
  have hmv : mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A₁ y) (B y) (C y) (D y)) x
      = mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A₂ y) (B y) (C y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) hfun
  simp only [cov3RmExt]
  rw [congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L w) hmv,
    congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, hXx]

theorem cov3RmExt_germ_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A B₁ B₂ C D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB₁ : CMDiff ∞ (T% B₁)) (hB₂ : CMDiff ∞ (T% B₂)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) (h : B₁ =ᶠ[𝓝 x] B₂) :
    cov3RmExt g x w U V A B₁ C D = cov3RmExt g x w U V A B₂ C D := by
  have hfun : (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₁ y) (C y) (D y))
      =ᶠ[𝓝 x] (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₂ y) (C y) (D y)) := by
    filter_upwards [h] with y hy
    rw [hy]
  have hlc : (lcOf g B₁ x) = (lcOf g B₂ x) :=
    lcOf_congr_eventuallyEq g (hB₁.mdifferentiableAt (by simp)) (hB₂.mdifferentiableAt (by simp)) h
  have hXx : B₁ x = B₂ x := h.self_of_nhds
  have hmv : mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₁ y) (C y) (D y)) x
      = mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B₂ y) (C y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) hfun
  simp only [cov3RmExt]
  rw [congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L w) hmv,
    congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, hXx]

theorem cov3RmExt_germ_fif (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A B C₁ C₂ D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC₁ : CMDiff ∞ (T% C₁)) (hC₂ : CMDiff ∞ (T% C₂)) (hD : CMDiff ∞ (T% D)) (h : C₁ =ᶠ[𝓝 x] C₂) :
    cov3RmExt g x w U V A B C₁ D = cov3RmExt g x w U V A B C₂ D := by
  have hfun : (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₁ y) (D y))
      =ᶠ[𝓝 x] (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₂ y) (D y)) := by
    filter_upwards [h] with y hy
    rw [hy]
  have hlc : (lcOf g C₁ x) = (lcOf g C₂ x) :=
    lcOf_congr_eventuallyEq g (hC₁.mdifferentiableAt (by simp)) (hC₂.mdifferentiableAt (by simp)) h
  have hXx : C₁ x = C₂ x := h.self_of_nhds
  have hmv : mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₁ y) (D y)) x
      = mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C₂ y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) hfun
  simp only [cov3RmExt]
  rw [congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L w) hmv,
    congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, hXx]

theorem cov3RmExt_germ_sixth (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A B C D₁ D₂ : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD₁ : CMDiff ∞ (T% D₁)) (hD₂ : CMDiff ∞ (T% D₂)) (h : D₁ =ᶠ[𝓝 x] D₂) :
    cov3RmExt g x w U V A B C D₁ = cov3RmExt g x w U V A B C D₂ := by
  have hfun : (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₁ y))
      =ᶠ[𝓝 x] (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₂ y)) := by
    filter_upwards [h] with y hy
    rw [hy]
  have hlc : (lcOf g D₁ x) = (lcOf g D₂ x) :=
    lcOf_congr_eventuallyEq g (hD₁.mdifferentiableAt (by simp)) (hD₂.mdifferentiableAt (by simp)) h
  have hXx : D₁ x = D₂ x := h.self_of_nhds
  have hmv : mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₁ y)) x
      = mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D₂ y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) hfun
  simp only [cov3RmExt]
  rw [congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L w) hmv,
    congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L w) hlc, hXx]

theorem cov3RmExt_bind_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U₁ U₂ V A B C D : Π y : M, TangentSpace I y}
    (hU₁ : CMDiff ∞ (T% U₁)) (hU₂ : CMDiff ∞ (T% U₂)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) (h : U₁ x = U₂ x) :
    cov3RmExt g x w U₁ V A B C D = cov3RmExt g x w U₂ V A B C D :=
  field_value_dep_of_linear x
    (F := fun X : Π y : M, TangentSpace I y => cov3RmExt g x w X V A B C D)
    (fun X₁ X₂ f₁ f₂ h₁ h₂ hf₁ hf₂ =>
      cov3RmExt_linear_fst hLC g x w h₁ h₂ hV hA hB hC hD hf₁ hf₂)
    (fun X X' h₁ h₂ heq =>
      cov3RmExt_germ_fst hLC g x w h₁ h₂ hV hA hB hC hD heq)
    hU₁ hU₂ h

theorem cov3RmExt_bind_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V₁ V₂ A B C D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV₁ : CMDiff ∞ (T% V₁)) (hV₂ : CMDiff ∞ (T% V₂)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) (h : V₁ x = V₂ x) :
    cov3RmExt g x w U V₁ A B C D = cov3RmExt g x w U V₂ A B C D :=
  field_value_dep_of_linear x
    (F := fun X : Π y : M, TangentSpace I y => cov3RmExt g x w U X A B C D)
    (fun X₁ X₂ f₁ f₂ h₁ h₂ hf₁ hf₂ =>
      cov3RmExt_linear_snd hLC g x w hU h₁ h₂ hA hB hC hD hf₁ hf₂)
    (fun X X' h₁ h₂ heq =>
      cov3RmExt_germ_snd hLC g x w hU h₁ h₂ hA hB hC hD heq)
    hV₁ hV₂ h

theorem cov3RmExt_bind_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A₁ A₂ B C D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA₁ : CMDiff ∞ (T% A₁)) (hA₂ : CMDiff ∞ (T% A₂)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) (h : A₁ x = A₂ x) :
    cov3RmExt g x w U V A₁ B C D = cov3RmExt g x w U V A₂ B C D :=
  field_value_dep_of_linear x
    (F := fun X : Π y : M, TangentSpace I y => cov3RmExt g x w U V X B C D)
    (fun X₁ X₂ f₁ f₂ h₁ h₂ hf₁ hf₂ =>
      cov3RmExt_linear_thd hLC g x w hU hV h₁ h₂ hB hC hD hf₁ hf₂)
    (fun X X' h₁ h₂ heq =>
      cov3RmExt_germ_thd hLC g x w hU hV h₁ h₂ hB hC hD heq)
    hA₁ hA₂ h

theorem cov3RmExt_bind_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A B₁ B₂ C D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB₁ : CMDiff ∞ (T% B₁)) (hB₂ : CMDiff ∞ (T% B₂)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) (h : B₁ x = B₂ x) :
    cov3RmExt g x w U V A B₁ C D = cov3RmExt g x w U V A B₂ C D :=
  field_value_dep_of_linear x
    (F := fun X : Π y : M, TangentSpace I y => cov3RmExt g x w U V A X C D)
    (fun X₁ X₂ f₁ f₂ h₁ h₂ hf₁ hf₂ =>
      cov3RmExt_linear_fth hLC g x w hU hV hA h₁ h₂ hC hD hf₁ hf₂)
    (fun X X' h₁ h₂ heq =>
      cov3RmExt_germ_fth hLC g x w hU hV hA h₁ h₂ hC hD heq)
    hB₁ hB₂ h

theorem cov3RmExt_bind_fif (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A B C₁ C₂ D : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC₁ : CMDiff ∞ (T% C₁)) (hC₂ : CMDiff ∞ (T% C₂)) (hD : CMDiff ∞ (T% D)) (h : C₁ x = C₂ x) :
    cov3RmExt g x w U V A B C₁ D = cov3RmExt g x w U V A B C₂ D :=
  field_value_dep_of_linear x
    (F := fun X : Π y : M, TangentSpace I y => cov3RmExt g x w U V A B X D)
    (fun X₁ X₂ f₁ f₂ h₁ h₂ hf₁ hf₂ =>
      cov3RmExt_linear_fif hLC g x w hU hV hA hB h₁ h₂ hD hf₁ hf₂)
    (fun X X' h₁ h₂ heq =>
      cov3RmExt_germ_fif hLC g x w hU hV hA hB h₁ h₂ hD heq)
    hC₁ hC₂ h

theorem cov3RmExt_bind_sixth (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {U V A B C D₁ D₂ : Π y : M, TangentSpace I y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD₁ : CMDiff ∞ (T% D₁)) (hD₂ : CMDiff ∞ (T% D₂)) (h : D₁ x = D₂ x) :
    cov3RmExt g x w U V A B C D₁ = cov3RmExt g x w U V A B C D₂ :=
  field_value_dep_of_linear x
    (F := fun X : Π y : M, TangentSpace I y => cov3RmExt g x w U V A B C X)
    (fun X₁ X₂ f₁ f₂ h₁ h₂ hf₁ hf₂ =>
      cov3RmExt_linear_sixth hLC g x w hU hV hA hB hC h₁ h₂ hf₁ hf₂)
    (fun X X' h₁ h₂ heq =>
      cov3RmExt_germ_sixth hLC g x w hU hV hA hB hC h₁ h₂ heq)
    hD₁ hD₂ h


end Work.Diff.GE.Kato3

namespace Work.Diff.GE

open Work.Diff.GE.Kato3

/-- **The field form of `cov3RmExt`.**  `cov3RmExt g x u U V A B C D` is `mvfderiv` of
`y ↦ cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D y)` at `x` in the direction `u`, minus the six Leibniz
corrections; it is the second covariant derivative `(∇_u∇∇Rm)(U,V,A,B,C,D)` of the `(0,5)`-tensor `∇Rm`,
hence depends only on the *values* of its six field arguments at `x`.  Proof route: as for
`kato_cov2RmExt_field`, but with the field form `cov2Rm = cov2RmExt` supplied by that statement in place
of the field form of `covRm` (the same decomposition/Leibniz argument one level up); add the import of
the corresponding module if needed. -/
theorem kato_cov3RmExt_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (U V A B C D U' V' A' B' C' D' : Π y : M, TangentSpace I y)
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (hU' : CMDiff ∞ (T% U')) (hV' : CMDiff ∞ (T% V')) (hA' : CMDiff ∞ (T% A'))
    (hB' : CMDiff ∞ (T% B')) (hC' : CMDiff ∞ (T% C')) (hD' : CMDiff ∞ (T% D'))
    (hUx : U x = U' x) (hVx : V x = V' x) (hAx : A x = A' x) (hBx : B x = B' x)
    (hCx : C x = C' x) (hDx : D x = D' x) :
    ∀ u : TangentSpace I x, cov3RmExt g x u U V A B C D = cov3RmExt g x u U' V' A' B' C' D' := by
  intro u
  rw [cov3RmExt_bind_fst hLC g x u hU hU' hV hA hB hC hD hUx,
      cov3RmExt_bind_snd hLC g x u hU' hV hV' hA hB hC hD hVx,
      cov3RmExt_bind_thd hLC g x u hU' hV' hA hA' hB hC hD hAx,
      cov3RmExt_bind_fth hLC g x u hU' hV' hA' hB hB' hC hD hBx,
      cov3RmExt_bind_fif hLC g x u hU' hV' hA' hB' hC hC' hD hCx,
      cov3RmExt_bind_sixth hLC g x u hU' hV' hA' hB' hC' hD hD' hDx]

end Work.Diff.GE
