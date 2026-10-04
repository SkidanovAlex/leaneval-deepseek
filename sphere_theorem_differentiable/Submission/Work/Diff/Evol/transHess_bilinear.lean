import Mathlib
import Submission.Work.Diff.Evol.Vocab
import Submission.Work.Diff.Evol.FrameData
import Submission.Work.Diff.Evol.lcOf_second_congr_value
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.EXT.contMDiffCovariantDerivative_lcOf
import Submission.Work.EXT.lcSmooth_noBoundary
import Submission.Work.Diff.GE.smp_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bilinearity of the symmetrised second frame derivative `transHess`

`Work.Diff.Evol.transHess g x F v w p i` is the pairing, with `F p x`, of the symmetrisation in
`(v,w)` of the *field-form* second covariant derivative
`∇_v ∇_{smoothExt x w} (F i) = lcOf g (fun y => lcOf g (F i) y (smoothExt x w y)) x v`.

If the family `F` is smooth and *parallel at `x`* (`∇(F i)(x) = 0` for all `i`), then `transHess`
is bilinear in `(v, w)`: linear in the outer direction `v` (or `w`) because `lcOf g A x` is linear
in the direction, and linear in the "field" direction because, by tensoriality of the second
covariant derivative in its field slot (`tensorialAt_lcOf_second`), the value
`∇_v ∇_W (F i)` at `x` depends only on `W x`, and linearly so.

The two distinct helpers are

* `lcOf_second_congr_dir`: the value `∇_v∇_W(F i)` is unchanged when `W` is replaced by another
  smooth field with the same value at `x`;
* `lcOf_second_linear_combo`: that value is linear in the field.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]

/-- **Tensoriality of the second covariant derivative in its field slot.**

If `X` is a smooth field which is parallel at `x` (i.e. `∇X = 0` at `x`), then the operation
`σ ↦ ∇_·(∇_·X(σ))` at `x` is tensorial at `x`: it respects addition of sections and multiplication
by germs of smooth functions.  (The Leibniz rule produces the correction term
`(df) ⊗ ∇X(x)`, which vanishes precisely because `∇X = 0` at `x`.)

In particular (by `TensorialAt.pointwise`) the value `∇_v(∇_{W}X)` at `x` depends on a smooth field
`W` only through `W x`, and is linear in `W x`. -/
theorem tensorialAt_lcOf_second
    (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M)
    (X : Π y : M, TangentSpace I y) (hX : Work.Diff.Evol.SmoothField I M X)
    (hX0 : ∀ v : TangentSpace I x, Submission.Diff.lcOf g X x v = 0) :
    TensorialAt I E (fun W : Π y : M, TangentSpace I y =>
      Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (W y)) x) x := by
  haveI : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ := (hLC g).1.some
  have hHom : MDifferentiableAt I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E)))
      (fun y : M => (⟨y, Submission.Diff.lcOf g X y⟩ : TotalSpace (E →L[ℝ] E)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))) x :=
    Work.Diff.Evol.mdifferentiableAt_cov_self hX x
  refine ⟨?_, ?_⟩
  · intro f σ hf hσ
    have hS : MDiffAt (T% (fun y : M => Submission.Diff.lcOf g X y (σ y))) x :=
      hHom.clm_bundle_apply hσ
    change Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y ((f • σ) y)) x
      = f x • Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (σ y)) x
    have h₁ : (fun y : M => Submission.Diff.lcOf g X y ((f • σ) y))
        = fun y : M => f y • Submission.Diff.lcOf g X y (σ y) := by
      funext y; exact map_smul (Submission.Diff.lcOf g X y) (f y) (σ y)
    have h₂ : (fun y : M => f y • Submission.Diff.lcOf g X y (σ y))
        = f • (fun y : M => Submission.Diff.lcOf g X y (σ y)) := rfl
    have h₃ := (Submission.Diff.lcOf g).isCovariantDerivativeOn.leibniz
      (σ := fun y : M => Submission.Diff.lcOf g X y (σ y)) hS hf
    rw [h₁, h₂, h₃, hX0 (σ x), ContinuousLinearMap.smulRight_zero, add_zero]
  · intro σ σ' hσ hσ'
    have hS : MDiffAt (T% (fun y : M => Submission.Diff.lcOf g X y (σ y))) x :=
      hHom.clm_bundle_apply hσ
    have hS' : MDiffAt (T% (fun y : M => Submission.Diff.lcOf g X y (σ' y))) x :=
      hHom.clm_bundle_apply hσ'
    change Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y ((σ + σ') y)) x
      = Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (σ y)) x
        + Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (σ' y)) x
    have h₁ : (fun y : M => Submission.Diff.lcOf g X y ((σ + σ') y))
        = (fun y : M => Submission.Diff.lcOf g X y (σ y))
          + (fun y : M => Submission.Diff.lcOf g X y (σ' y)) := by
      funext y; exact map_add (Submission.Diff.lcOf g X y) (σ y) (σ' y)
    rw [h₁, (Submission.Diff.lcOf g).isCovariantDerivativeOn.add hS hS']

/-- **The pairing `∇_a ∇_W (X)` at `x` depends on the field `W` only through `W x`.** -/
theorem lcOf_second_congr_dir
    (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M)
    (X : Π y : M, TangentSpace I y) (hX : Work.Diff.Evol.SmoothField I M X)
    (hX0 : ∀ v : TangentSpace I x, Submission.Diff.lcOf g X x v = 0)
    (W W' : Π y : M, TangentSpace I y) (hW : Work.Diff.Evol.SmoothField I M W)
    (hW' : Work.Diff.Evol.SmoothField I M W') (hWW' : W x = W' x) (a : TangentSpace I x) :
    Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (W y)) x a
      = Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (W' y)) x a :=
  congrArg (fun L => L a)
    ((tensorialAt_lcOf_second hLC g x X hX hX0).pointwise
      (hW.contMDiffAt.mdifferentiableAt (by simp))
      (hW'.contMDiffAt.mdifferentiableAt (by simp)) hWW')

/-- **Linearity of `∇_a ∇_W (X)` in the field `W`.**

For smooth fields `W₁`, `W₂` and reals `c`, `d`, the field-form second derivative at `x` of `X` in
the directions `(a, c • W₁ + d • W₂)` is the corresponding combination. -/
theorem lcOf_second_linear_combo
    (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M)
    (X : Π y : M, TangentSpace I y) (hX : Work.Diff.Evol.SmoothField I M X)
    (hX0 : ∀ v : TangentSpace I x, Submission.Diff.lcOf g X x v = 0)
    (W₁ W₂ : Π y : M, TangentSpace I y)
    (hW₁ : Work.Diff.Evol.SmoothField I M W₁) (hW₂ : Work.Diff.Evol.SmoothField I M W₂)
    (c d : ℝ) (a : TangentSpace I x) :
    Submission.Diff.lcOf g
        (fun y : M => Submission.Diff.lcOf g X y ((c • W₁ + d • W₂) y)) x a
      = c • (Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (W₁ y)) x a)
        + d • (Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (W₂ y)) x a) := by
  have hΦ := tensorialAt_lcOf_second hLC g x X hX hX0
  have h1 : MDiffAt (T% (c • W₁)) x :=
    (hW₁.const_smul_section (a := c)).contMDiffAt.mdifferentiableAt (by simp)
  have h2 : MDiffAt (T% (d • W₂)) x :=
    (hW₂.const_smul_section (a := d)).contMDiffAt.mdifferentiableAt (by simp)
  have hs1 : Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y ((c • W₁) y)) x
      = c • (Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (W₁ y)) x) :=
    hΦ.smul (f := fun _ : M => c) mdifferentiableAt_const
      (hW₁.contMDiffAt.mdifferentiableAt (by simp))
  have hs2 : Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y ((d • W₂) y)) x
      = d • (Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (W₂ y)) x) :=
    hΦ.smul (f := fun _ : M => d) mdifferentiableAt_const
      (hW₂.contMDiffAt.mdifferentiableAt (by simp))
  have hadd := hΦ.add h1 h2
  have key : Submission.Diff.lcOf g
        (fun y : M => Submission.Diff.lcOf g X y ((c • W₁ + d • W₂) y)) x
      = c • (Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (W₁ y)) x)
        + d • (Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (W₂ y)) x) := by
    rw [hadd, hs1, hs2]
  have key2 := congrArg (fun L => L a) key
  simpa only [add_apply, smul_apply]
    using key2

theorem transHess_bilinear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless]
    (g : Submission.Diff.SMet I M) (x : M) {n : ℕ} (F : Fin n → Π y : M, TangentSpace I y)
    (hF : ∀ i, Work.Diff.Evol.SmoothField I M (F i))
    (hF0 : ∀ (i : Fin n) (v : TangentSpace I x), Submission.Diff.lcOf g (F i) x v = 0) :
    (∀ (r s : ℝ) (v₁ v₂ : TangentSpace I x) (w : TangentSpace I x) (p i : Fin n),
        Work.Diff.Evol.transHess g x F (r • v₁ + s • v₂) w p i
          = r * Work.Diff.Evol.transHess g x F v₁ w p i
            + s * Work.Diff.Evol.transHess g x F v₂ w p i) ∧
    (∀ (r s : ℝ) (v : TangentSpace I x) (w₁ w₂ : TangentSpace I x) (p i : Fin n),
        Work.Diff.Evol.transHess g x F v (r • w₁ + s • w₂) p i
          = r * Work.Diff.Evol.transHess g x F v w₁ p i
            + s * Work.Diff.Evol.transHess g x F v w₂ p i) := by
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  constructor
  · intro r s v₁ v₂ w p i
    have hW₁ : CMDiff ∞ (T% (r • smoothExt x v₁)) :=
      ContMDiff.const_smul_section (a := r) (Work.Diff.GE.smoothExt_spec x v₁).1
    have hW₂ : CMDiff ∞ (T% (s • smoothExt x v₂)) :=
      ContMDiff.const_smul_section (a := s) (Work.Diff.GE.smoothExt_spec x v₂).1
    have hW : CMDiff ∞ (T% (r • smoothExt x v₁ + s • smoothExt x v₂)) := hW₁.add_section hW₂
    have hs₀ : smoothExt x (r • v₁ + s • v₂) x = r • v₁ + s • v₂ :=
      (Work.Diff.GE.smoothExt_spec x (r • v₁ + s • v₂)).2
    have hs₁ : smoothExt x v₁ x = v₁ := (Work.Diff.GE.smoothExt_spec x v₁).2
    have hs₂ : smoothExt x v₂ x = v₂ := (Work.Diff.GE.smoothExt_spec x v₂).2
    have hval : smoothExt x (r • v₁ + s • v₂) x
        = (r • smoothExt x v₁ + s • smoothExt x v₂) x := by
      simp only [Pi.add_apply, Pi.smul_apply, hs₀, hs₁, hs₂]
    have hΦ2 : Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g (F i) y
          (smoothExt x (r • v₁ + s • v₂) y)) x
        = Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g (F i) y
          ((r • smoothExt x v₁ + s • smoothExt x v₂) y)) x := by
      ext a
      exact lcOf_second_congr_dir hLC g x (F i) (hF i) (hF0 i)
        (smoothExt x (r • v₁ + s • v₂)) (r • smoothExt x v₁ + s • smoothExt x v₂)
        ((Work.Diff.GE.smoothExt_spec x (r • v₁ + s • v₂)).1) hW hval a
    have hΦ3 : Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g (F i) y
          ((r • smoothExt x v₁ + s • smoothExt x v₂) y)) x
        = r • Submission.Diff.lcOf g
              (fun y : M => Submission.Diff.lcOf g (F i) y (smoothExt x v₁ y)) x
          + s • Submission.Diff.lcOf g
              (fun y : M => Submission.Diff.lcOf g (F i) y (smoothExt x v₂ y)) x := by
      ext a
      have h := lcOf_second_linear_combo hLC g x (F i) (hF i) (hF0 i)
        (smoothExt x v₁) (smoothExt x v₂)
        ((Work.Diff.GE.smoothExt_spec x v₁).1) ((Work.Diff.GE.smoothExt_spec x v₂).1) r s a
      simpa only [add_apply, smul_apply] using h
    simp only [transHess, hΦ2, hΦ3, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  · intro r s v w₁ w₂ p i
    have hW₁ : CMDiff ∞ (T% (r • smoothExt x w₁)) :=
      ContMDiff.const_smul_section (a := r) (Work.Diff.GE.smoothExt_spec x w₁).1
    have hW₂ : CMDiff ∞ (T% (s • smoothExt x w₂)) :=
      ContMDiff.const_smul_section (a := s) (Work.Diff.GE.smoothExt_spec x w₂).1
    have hW : CMDiff ∞ (T% (r • smoothExt x w₁ + s • smoothExt x w₂)) := hW₁.add_section hW₂
    have hs₀ : smoothExt x (r • w₁ + s • w₂) x = r • w₁ + s • w₂ :=
      (Work.Diff.GE.smoothExt_spec x (r • w₁ + s • w₂)).2
    have hs₁ : smoothExt x w₁ x = w₁ := (Work.Diff.GE.smoothExt_spec x w₁).2
    have hs₂ : smoothExt x w₂ x = w₂ := (Work.Diff.GE.smoothExt_spec x w₂).2
    have hval : smoothExt x (r • w₁ + s • w₂) x
        = (r • smoothExt x w₁ + s • smoothExt x w₂) x := by
      simp only [Pi.add_apply, Pi.smul_apply, hs₀, hs₁, hs₂]
    have hΦ2 : Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g (F i) y
          (smoothExt x (r • w₁ + s • w₂) y)) x
        = Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g (F i) y
          ((r • smoothExt x w₁ + s • smoothExt x w₂) y)) x := by
      ext a
      exact lcOf_second_congr_dir hLC g x (F i) (hF i) (hF0 i)
        (smoothExt x (r • w₁ + s • w₂)) (r • smoothExt x w₁ + s • smoothExt x w₂)
        ((Work.Diff.GE.smoothExt_spec x (r • w₁ + s • w₂)).1) hW hval a
    have hΦ3 : Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g (F i) y
          ((r • smoothExt x w₁ + s • smoothExt x w₂) y)) x
        = r • Submission.Diff.lcOf g
              (fun y : M => Submission.Diff.lcOf g (F i) y (smoothExt x w₁ y)) x
          + s • Submission.Diff.lcOf g
              (fun y : M => Submission.Diff.lcOf g (F i) y (smoothExt x w₂ y)) x := by
      ext a
      have h := lcOf_second_linear_combo hLC g x (F i) (hF i) (hF0 i)
        (smoothExt x w₁) (smoothExt x w₂)
        ((Work.Diff.GE.smoothExt_spec x w₁).1) ((Work.Diff.GE.smoothExt_spec x w₂).1) r s a
      simpa only [add_apply, smul_apply] using h
    simp only [transHess, hΦ2, hΦ3, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring

end Work.Diff.Evol
