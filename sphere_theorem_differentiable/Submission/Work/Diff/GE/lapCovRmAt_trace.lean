import Mathlib
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.onFrame_orthogonal_change

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Frame independence of the trace defining `lapCovRmAt`

The frozen file `Submission/Work/Diff/GE/NablaRm.lean` defines the third covariant derivative of the
curvature as an `Ext`-pattern expression

`cov3Rm g x w u v a b c d = mvfderiv (y ↦ cov2Rm g y (smoothExt x u y) … (smoothExt x d y)) x w −`
six Leibniz corrections,

and the rough Laplacian `lapCovRmAt g x v a b c d = ∑ m, cov3Rm g x (onFrame g x m) (onFrame g x m)
v a b c d` as its trace over the `Classical.epsilon`-chosen frame `onFrame g x`.  The point of this
file is that this trace is the trace of a `(0,7)`-tensor, hence frame independent; here it is
compared with the trace over an arbitrary `g`-orthonormal frame `e`.

Ingredients, all already available in the workspace:

* `Kato3.cov2Rm_lin_{first,snd,thd,fth,fif,sixth}` (`Submission/Work/Diff/GE/kato_cov3RmExt_field.lean`):
  `cov2Rm` is `ℝ`-linear in each of its six arguments.  These give the `ℝ`-linearity of `cov3RmExt`
  in its *direction* argument `w` (`cov3RmExt_linear_dir` below), i.e. the `ℝ`-linearity of `cov3Rm`
  in its first argument;
* `Kato3.cov3RmExt_{linear,bind}_fst`: `cov3RmExt` is `C^∞(M)`-linear in its first *field* and only
  sees the value of that field, which gives the `ℝ`-linearity of `cov3Rm` in its second argument;
* `Work.Diff.GE.onFrame_orthogonal_change`: two `g`-orthonormal frames differ by an orthogonal
  matrix, and `Work.Diff.GE.sum_trace_bilinear_orthogonal` (the abstract trace identity, copied
  below as a private lemma while the delegated module is being proved).
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## `ℝ`-linearity of `cov3Rm` in its first two arguments -/

/-- **`cov3RmExt` is `ℝ`-linear in its direction argument.**  The direction `w` occurs in
`cov3RmExt g x w U V A B C D` only as the direction of the `mvfderiv` (linear in that argument) and in
the six corrections, where it is fed into `lcOf g · x w` (linear, being a continuous linear map) and
thence into one of the six arguments of `cov2Rm`; so the whole expression is linear in `w`
(cf. `Kato3.cov2Rm_lin_first` for the same computation one level down).  No smoothness of the fields
is needed. -/
private theorem cov3RmExt_linear_dir (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (r s : ℝ) (w₁ w₂ : TangentSpace I x) (U V A B C D : Π y : M, TangentSpace I y) :
    cov3RmExt g x (r • w₁ + s • w₂) U V A B C D
      = r * cov3RmExt g x w₁ U V A B C D + s * cov3RmExt g x w₂ U V A B C D := by
  have hd : mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D y)) x
        (r • w₁ + s • w₂)
      = r * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D y)) x w₁
        + s * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D y)) x w₂ := by
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
  have c1 : cov2Rm g x ((lcOf g) U x (r • w₁ + s • w₂)) (V x) (A x) (B x) (C x) (D x)
      = r * cov2Rm g x ((lcOf g) U x w₁) (V x) (A x) (B x) (C x) (D x)
        + s * cov2Rm g x ((lcOf g) U x w₂) (V x) (A x) (B x) (C x) (D x) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_first hLC g x r s ((lcOf g) U x w₁) ((lcOf g) U x w₂) (V x) (A x)
      (B x) (C x) (D x)]
  have c2 : cov2Rm g x (U x) ((lcOf g) V x (r • w₁ + s • w₂)) (A x) (B x) (C x) (D x)
      = r * cov2Rm g x (U x) ((lcOf g) V x w₁) (A x) (B x) (C x) (D x)
        + s * cov2Rm g x (U x) ((lcOf g) V x w₂) (A x) (B x) (C x) (D x) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_snd hLC g x r s (U x) ((lcOf g) V x w₁) ((lcOf g) V x w₂) (A x)
      (B x) (C x) (D x)]
  have c3 : cov2Rm g x (U x) (V x) ((lcOf g) A x (r • w₁ + s • w₂)) (B x) (C x) (D x)
      = r * cov2Rm g x (U x) (V x) ((lcOf g) A x w₁) (B x) (C x) (D x)
        + s * cov2Rm g x (U x) (V x) ((lcOf g) A x w₂) (B x) (C x) (D x) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_thd hLC g x r s (U x) (V x) ((lcOf g) A x w₁) ((lcOf g) A x w₂)
      (B x) (C x) (D x)]
  have c4 : cov2Rm g x (U x) (V x) (A x) ((lcOf g) B x (r • w₁ + s • w₂)) (C x) (D x)
      = r * cov2Rm g x (U x) (V x) (A x) ((lcOf g) B x w₁) (C x) (D x)
        + s * cov2Rm g x (U x) (V x) (A x) ((lcOf g) B x w₂) (C x) (D x) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_fth hLC g x r s (U x) (V x) (A x) ((lcOf g) B x w₁)
      ((lcOf g) B x w₂) (C x) (D x)]
  have c5 : cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g) C x (r • w₁ + s • w₂)) (D x)
      = r * cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g) C x w₁) (D x)
        + s * cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g) C x w₂) (D x) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_fif hLC g x r s (U x) (V x) (A x) (B x) ((lcOf g) C x w₁)
      ((lcOf g) C x w₂) (D x)]
  have c6 : cov2Rm g x (U x) (V x) (A x) (B x) (C x) ((lcOf g) D x (r • w₁ + s • w₂))
      = r * cov2Rm g x (U x) (V x) (A x) (B x) (C x) ((lcOf g) D x w₁)
        + s * cov2Rm g x (U x) (V x) (A x) (B x) (C x) ((lcOf g) D x w₂) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_sixth hLC g x r s (U x) (V x) (A x) (B x) (C x) ((lcOf g) D x w₁)
      ((lcOf g) D x w₂)]
  simp only [cov3RmExt]
  rw [hd, c1, c2, c3, c4, c5, c6]
  ring

/-- **`cov3Rm` is `ℝ`-linear in its first argument** (the first differentiation direction). -/
private theorem cov3Rm_linear_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (r s : ℝ) (w₁ w₂ u v a b c d : TangentSpace I x),
      cov3Rm g x (r • w₁ + s • w₂) u v a b c d
        = r * cov3Rm g x w₁ u v a b c d + s * cov3Rm g x w₂ u v a b c d := by
  intro r s w₁ w₂ u v a b c d
  simp only [cov3Rm]
  rw [cov3RmExt_linear_dir hLC g x r s w₁ w₂ (smoothExt x u) (smoothExt x v) (smoothExt x a)
    (smoothExt x b) (smoothExt x c) (smoothExt x d)]

/-- **`cov3Rm` is `ℝ`-linear in its second argument.**  By `Kato3.cov3RmExt_bind_fst` (a smooth field
entering the first field slot only contributes its value at `x`), the second argument of `cov3Rm`
behaves like the *first field* of `cov3RmExt`, so this reduces to
`Kato3.cov3RmExt_linear_fst` — as in `Kato3.cov2Rm_lin_snd`, one level down. -/
private theorem cov3Rm_linear_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (r s : ℝ) (w u₁ u₂ v a b c d : TangentSpace I x),
      cov3Rm g x w (r • u₁ + s • u₂) v a b c d
        = r * cov3Rm g x w u₁ v a b c d + s * cov3Rm g x w u₂ v a b c d := by
  intro r s w u₁ u₂ v a b c d
  have hU : CMDiff ∞ (T% (smoothExt x (r • u₁ + s • u₂))) :=
    smoothExt_cmdiff x (r • u₁ + s • u₂)
  have hU' : CMDiff ∞ (T% ((fun _ : M => r) • smoothExt x u₁ + (fun _ : M => s) • smoothExt x u₂)) :=
    ((contMDiff_const (c := r)).smul_section (smoothExt_cmdiff x u₁)).add_section
      ((contMDiff_const (c := s)).smul_section (smoothExt_cmdiff x u₂))
  have hval : smoothExt x (r • u₁ + s • u₂) x
      = ((fun _ : M => r) • smoothExt x u₁ + (fun _ : M => s) • smoothExt x u₂) x := by
    rw [show ((fun _ : M => r) • smoothExt x u₁ + (fun _ : M => s) • smoothExt x u₂) x
        = r • smoothExt x u₁ x + s • smoothExt x u₂ x from rfl,
      smoothExt_apply x (r • u₁ + s • u₂), smoothExt_apply x u₁, smoothExt_apply x u₂]
  have hbind := Kato3.cov3RmExt_bind_fst hLC g x w hU hU' (smoothExt_cmdiff x v)
    (smoothExt_cmdiff x a) (smoothExt_cmdiff x b) (smoothExt_cmdiff x c) (smoothExt_cmdiff x d) hval
  have hlin := Kato3.cov3RmExt_linear_fst hLC g x w (smoothExt_cmdiff x u₁)
    (smoothExt_cmdiff x u₂) (smoothExt_cmdiff x v) (smoothExt_cmdiff x a) (smoothExt_cmdiff x b)
    (smoothExt_cmdiff x c) (smoothExt_cmdiff x d) (contMDiff_const (c := r))
    (contMDiff_const (c := s))
  simp only [cov3Rm]
  rw [hbind, hlin]

/-! ## The abstract orthogonal change-of-frame identity -/

-- **Local copy** of the delegated lemma `Work.Diff.GE.sum_trace_bilinear_orthogonal` (the abstract
-- orthogonal-trace identity), inserted here so that this file is self-contained; the same copy is
-- used in `Submission/Work/Diff/GE/lapRmAt_trace.lean`.
private theorem sum_trace_bilinear_aux
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [AddCommMonoid X] [Module ℝ X]
    (β : X → X → ℝ)
    (h₁ : ∀ (r s : ℝ) (u₁ u₂ w : X), β (r • u₁ + s • u₂) w = r * β u₁ w + s * β u₂ w)
    (h₂ : ∀ (r s : ℝ) (u v₁ v₂ : X), β u (r • v₁ + s • v₂) = r * β u v₁ + s * β u v₂)
    (A : ι → ι → ℝ) (e₀ : ι → X)
    (hA : ∀ j k, ∑ m, A m j * A m k = if j = k then 1 else 0) :
    ∑ m, β (∑ j, A m j • e₀ j) (∑ k, A m k • e₀ k) = ∑ j, β (e₀ j) (e₀ j) := by
  have hβ0 : ∀ w : X, β 0 w = 0 := by
    intro w
    have h := h₁ 0 0 (0 : X) (0 : X) w
    simpa using h
  have h0β : ∀ u : X, β u 0 = 0 := by
    intro u
    have h := h₂ 0 0 u (0 : X) (0 : X)
    simpa using h
  -- bilinearity in finite-sum form
  have hsum₁ : ∀ (s : Finset ι) (c : ι → ℝ) (v : ι → X) (w : X),
      β (∑ i ∈ s, c i • v i) w = ∑ i ∈ s, c i * β (v i) w := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro c v w; rw [Finset.sum_empty, Finset.sum_empty]; exact hβ0 w
    | insert k s hk ih =>
        intro c v w
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        have h := h₁ (c k) 1 (v k) (∑ i ∈ s, c i • v i) w
        simp only [one_smul, one_mul] at h
        rw [h, ih c v w]
  have hsum₂ : ∀ (s : Finset ι) (c : ι → ℝ) (v : ι → X) (w : X),
      β w (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * β w (v i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro c v w; rw [Finset.sum_empty, Finset.sum_empty]; exact h0β w
    | insert k s hk ih =>
        intro c v w
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        have h := h₂ (c k) 1 w (v k) (∑ i ∈ s, c i • v i)
        simp only [one_smul, one_mul] at h
        rw [h, ih c v w]
  calc ∑ m, β (∑ j, A m j • e₀ j) (∑ k, A m k • e₀ k)
      = ∑ m, ∑ j, A m j * β (e₀ j) (∑ k, A m k • e₀ k) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        exact hsum₁ Finset.univ (fun j => A m j) e₀ (∑ k, A m k • e₀ k)
    _ = ∑ m, ∑ j, A m j * (∑ k, A m k * β (e₀ j) (e₀ k)) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hsum₂ Finset.univ (fun k => A m k) e₀ (e₀ j)]
    _ = ∑ m, ∑ j, ∑ k, A m j * A m k * β (e₀ j) (e₀ k) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
    _ = ∑ j, ∑ k, (∑ m, A m j * A m k) * β (e₀ j) (e₀ k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_mul]
    _ = ∑ j, ∑ k, (if j = k then 1 else 0) * β (e₀ j) (e₀ k) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hA j k]
    _ = ∑ j, β (e₀ j) (e₀ j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
          ite_true]

/-- **Frame independence of the trace defining `lapCovRmAt`.**  `lapCovRmAt g x v a b c d` is the
trace `∑ m, ∇³Rm(e_m,e_m,v,a,b,c,d)` of the third covariant derivative of the curvature over the
`Classical.epsilon`-chosen frame `onFrame g x`; since `∇³Rm` is a `(0,7)`-tensor and the frame is
orthonormal, the value does not depend on the frame, and may be computed in any `g`-orthonormal
frame `e`.

Route: `ℝ`-bilinearity of `cov3Rm g x` in its first two arguments (from the value-dependence
`Work.Diff.GE.kato_cov3RmExt_field` — or a private helper if that module is still `sorry` — plus the
linearity of `mvfderiv` in its vector argument and of `lcOf g V x ·`), then the same orthogonal
change-of-frame computation as for `Work.Diff.GE.lapRmAt_trace`. -/
theorem lapCovRmAt_trace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (v a b c d : TangentSpace I x) :
    Work.Diff.GE.lapCovRmAt g x v a b c d
      = ∑ m, Work.Diff.GE.cov3Rm g x (e m) (e m) v a b c d := by
  classical
  -- the two orthonormal frames differ by an orthogonal matrix
  obtain ⟨A, hAorth, hAe⟩ :=
    onFrame_orthogonal_change g x (onFrame g x) e (isONFrame_onFrame g x) he
  have hAA : ∀ j k : Fin (Module.finrank ℝ E), ∑ m, A m j * A m k = if j = k then 1 else 0 := by
    intro j k
    have hAtA := (Matrix.mem_orthogonalGroup_iff' (Fin (Module.finrank ℝ E)) ℝ).mp hAorth
    have h := congrFun (congrFun hAtA j) k
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  -- the two-fold trace of a bilinear form is invariant under an orthogonal change of frame
  have htr := sum_trace_bilinear_aux
      (β := fun u w : TangentSpace I x => cov3Rm g x u w v a b c d)
      (fun r s u₁ u₂ w => cov3Rm_linear_fst hLC g x r s u₁ u₂ w v a b c d)
      (fun r s u w₁ w₂ => cov3Rm_linear_snd hLC g x r s u w₁ w₂ v a b c d)
      A (onFrame g x) hAA
  rw [show lapCovRmAt g x v a b c d
        = ∑ m, cov3Rm g x (onFrame g x m) (onFrame g x m) v a b c d from rfl]
  rw [show (∑ m, cov3Rm g x (e m) (e m) v a b c d)
        = ∑ m, cov3Rm g x (∑ j, A m j • onFrame g x j) (∑ k, A m k • onFrame g x k) v a b c d from
      Finset.sum_congr rfl (fun m _ => by simp only [hAe m])]
  exact htr.symm

end Work.Diff.GE
