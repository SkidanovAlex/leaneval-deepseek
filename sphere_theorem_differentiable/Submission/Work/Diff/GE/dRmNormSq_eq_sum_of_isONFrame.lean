import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.frobSq5_frameIndep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `dRmNormSq` does not depend on the orthonormal frame

`dRmNormSq g x` is defined (in the frozen `Submission/Diff/Grad.lean`) as the sum of the squares of
the components of `∇Rm` in the `Classical.epsilon`-chosen frame `onFrame g x`.  This module proves
that the same sum is obtained from *any* `g`-orthonormal frame of `TₓM`:

* `covRm` (the frozen `(∇_v Rm)(a,b,c,d)`) is `ℝ`-linear in each of its five arguments — the
  second slot is `Work.Diff.GE.covRm_linear_snd` (from `dRmPhi_slotA.lean`), the third and fourth
  are `Work.Diff.GE.covRm_linear_thd`/`_fth`, the fifth is `Work.Diff.GE.Kato3.covRm_linear_fith`,
  and the first is `covRm_linear_fst` below;
* hence `covRm` gives a nested `LinearMap` `mkLin5`, and the sum of squares of a `5`-multilinear
  form in an orthonormal frame is frame independent (`Work.Diff.GE.frobSq5_frameIndep`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## The nested `LinearMap` attached to a five-fold "linear in each slot" function -/

/-- Package a function of five variables that is additive and homogeneous in each slot into the
nested `LinearMap` `V →ₗ V →ₗ V →ₗ V →ₗ V →ₗ ℝ`. -/
noncomputable def mkLin5 {V : Type*} [AddCommGroup V] [Module ℝ V] (F : V → V → V → V → V → ℝ)
    (h1a : ∀ (a₁ a₂ b c d e : V), F (a₁ + a₂) b c d e = F a₁ b c d e + F a₂ b c d e)
    (h1s : ∀ (r : ℝ) (a b c d e : V), F (r • a) b c d e = r * F a b c d e)
    (h2a : ∀ (a b₁ b₂ c d e : V), F a (b₁ + b₂) c d e = F a b₁ c d e + F a b₂ c d e)
    (h2s : ∀ (a : V) (r : ℝ) (b c d e : V), F a (r • b) c d e = r * F a b c d e)
    (h3a : ∀ (a b c₁ c₂ d e : V), F a b (c₁ + c₂) d e = F a b c₁ d e + F a b c₂ d e)
    (h3s : ∀ (a b : V) (r : ℝ) (c d e : V), F a b (r • c) d e = r * F a b c d e)
    (h4a : ∀ (a b c d₁ d₂ e : V), F a b c (d₁ + d₂) e = F a b c d₁ e + F a b c d₂ e)
    (h4s : ∀ (a b c : V) (r : ℝ) (d e : V), F a b c (r • d) e = r * F a b c d e)
    (h5a : ∀ (a b c d e₁ e₂ : V), F a b c d (e₁ + e₂) = F a b c d e₁ + F a b c d e₂)
    (h5s : ∀ (a b c d : V) (r : ℝ) (e : V), F a b c d (r • e) = r * F a b c d e) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  { toFun := fun a =>
      { toFun := fun b =>
          { toFun := fun c =>
              { toFun := fun d =>
                  { toFun := fun e => F a b c d e
                    map_add' := h5a a b c d
                    map_smul' := h5s a b c d }
                map_add' := fun d₁ d₂ => by ext e; exact h4a a b c d₁ d₂ e
                map_smul' := fun r d => by ext e; exact h4s a b c r d e }
            map_add' := fun c₁ c₂ => by ext d e; exact h3a a b c₁ c₂ d e
            map_smul' := fun r c => by ext d e; exact h3s a b r c d e }
        map_add' := fun b₁ b₂ => by ext c d e; exact h2a a b₁ b₂ c d e
        map_smul' := fun r b => by ext c d e; exact h2s a r b c d e }
    map_add' := fun a₁ a₂ => by ext b c d e; exact h1a a₁ a₂ b c d e
    map_smul' := fun r a => by ext b c d e; exact h1s r a b c d e }

@[simp] theorem mkLin5_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (F : V → V → V → V → V → ℝ) (h1a h1s h2a h2s h3a h3s h4a h4s h5a h5s) (a b c d e : V) :
    mkLin5 F h1a h1s h2a h2s h3a h3s h4a h4s h5a h5s a b c d e = F a b c d e := rfl

/-! ## Linearity of `covRm` in its first argument -/

/-- `covRm` is `ℝ`-linear in its first argument `v` (the direction of differentiation). -/
theorem covRm_linear_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (r s : ℝ) (v₁ v₂ a b c d : TangentSpace I x),
      covRm g x (r • v₁ + s • v₂) a b c d
        = r * covRm g x v₁ a b c d + s * covRm g x v₂ a b c d := by
  intro r s v₁ v₂ a b c d
  simp only [covRm, map_add, map_smul, smul_eq_mul,
    rmP_add_fst g hLC, rmP_smul_fst g hLC, rmP_add_snd g hLC, rmP_smul_snd g hLC,
    rmP_add_thd g hLC, rmP_smul_thd g hLC, rmP_add_fth g hLC, rmP_smul_fth g hLC]
  ring

/-! ## The target theorem -/

/-- The squared norm of `∇Rm` (as defined by `dRmNormSq` through the chosen orthonormal frame
`onFrame`) is independent of the orthonormal frame used to compute it: for *any* frame `e` that is
orthonormal for `g` at `x`, the sum of the squares of the components of `∇Rm` in `e` is the same. -/
theorem dRmNormSq_eq_sum_of_isONFrame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) {g : SMet I M} (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    dRmNormSq g x
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (covRm g x (e m) (e i) (e j) (e k) (e l)) ^ 2 := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- the two frames are orthonormal for the instance inner product (which is `g.inner`)
  have hon : Orthonormal ℝ (onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show Inner.inner ℝ (onFrame g x i) (onFrame g x j)
        = g.inner x (onFrame g x i) (onFrame g x j) from rfl]
    exact isONFrame_onFrame g x i j
  have he' : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show Inner.inner ℝ (e i) (e j) = g.inner x (e i) (e j) from rfl]
    exact he i j
  -- `covRm` in the five slots
  have h1a : ∀ (a₁ a₂ b c d ee : TangentSpace I x),
      covRm g x (a₁ + a₂) b c d ee = covRm g x a₁ b c d ee + covRm g x a₂ b c d ee := by
    intro a₁ a₂ b c d ee
    have h := covRm_linear_fst hLC g x 1 1 a₁ a₂ b c d ee
    simpa using h
  have h1s : ∀ (r : ℝ) (a b c d ee : TangentSpace I x),
      covRm g x (r • a) b c d ee = r * covRm g x a b c d ee := by
    intro r a b c d ee
    have h := covRm_linear_fst hLC g x r 0 a 0 b c d ee
    simpa using h
  have h2a : ∀ (a b₁ b₂ c d ee : TangentSpace I x),
      covRm g x a (b₁ + b₂) c d ee = covRm g x a b₁ c d ee + covRm g x a b₂ c d ee := by
    intro a b₁ b₂ c d ee
    have h := covRm_linear_snd hLC g x a 1 1 b₁ b₂ c d ee
    simpa using h
  have h2s : ∀ (a : TangentSpace I x) (r : ℝ) (b c d ee : TangentSpace I x),
      covRm g x a (r • b) c d ee = r * covRm g x a b c d ee := by
    intro a r b c d ee
    have h := covRm_linear_snd hLC g x a r 0 b 0 c d ee
    simpa using h
  have h3a : ∀ (a b c₁ c₂ d ee : TangentSpace I x),
      covRm g x a b (c₁ + c₂) d ee = covRm g x a b c₁ d ee + covRm g x a b c₂ d ee := by
    intro a b c₁ c₂ d ee
    have h := covRm_linear_thd hLC g x a b 1 1 c₁ c₂ d ee
    simpa using h
  have h3s : ∀ (a b : TangentSpace I x) (r : ℝ) (c d ee : TangentSpace I x),
      covRm g x a b (r • c) d ee = r * covRm g x a b c d ee := by
    intro a b r c d ee
    have h := covRm_linear_thd hLC g x a b r 0 c 0 d ee
    simpa using h
  have h4a : ∀ (a b c d₁ d₂ ee : TangentSpace I x),
      covRm g x a b c (d₁ + d₂) ee = covRm g x a b c d₁ ee + covRm g x a b c d₂ ee := by
    intro a b c d₁ d₂ ee
    have h := covRm_linear_fth hLC g x a b c 1 1 d₁ d₂ ee
    simpa using h
  have h4s : ∀ (a b c : TangentSpace I x) (r : ℝ) (d ee : TangentSpace I x),
      covRm g x a b c (r • d) ee = r * covRm g x a b c d ee := by
    intro a b c r d ee
    have h := covRm_linear_fth hLC g x a b c r 0 d 0 ee
    simpa using h
  have h5a : ∀ (a b c d ee₁ ee₂ : TangentSpace I x),
      covRm g x a b c d (ee₁ + ee₂) = covRm g x a b c d ee₁ + covRm g x a b c d ee₂ := by
    intro a b c d ee₁ ee₂
    have h := Kato3.covRm_linear_fith hLC g x a b c d 1 1 ee₁ ee₂
    simpa using h
  have h5s : ∀ (a b c d : TangentSpace I x) (r : ℝ) (ee : TangentSpace I x),
      covRm g x a b c d (r • ee) = r * covRm g x a b c d ee := by
    intro a b c d r ee
    have h := Kato3.covRm_linear_fith hLC g x a b c d r 0 ee 0
    simpa using h
  -- the algebra lemma
  have hmain := frobSq5_frameIndep
    (mkLin5 (fun a b c d ee => covRm g x a b c d ee) h1a h1s h2a h2s h3a h3s h4a h4s h5a h5s)
    (onFrame g x) e hon he'
  simp only [mkLin5_apply] at hmain
  rw [dRmNormSq]
  exact hmain

end Work.Diff.GE
