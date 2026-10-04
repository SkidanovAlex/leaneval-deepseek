import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.ATower.LinDefs
import Submission.Work.Diff.EXT.ATower.tower_slotAdd_smF

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linearity of the recursion `step` in its operator argument

`Work.Diff.EXT.ATower.step cov τ` is one recursion step of the tower of iterated covariant
derivatives (`Work.Diff.EXT.ATower.Defs`): the derivative `mvfderiv I (τ …) x (v 0 x)` of the
operator applied to the tail of the direction tuple, corrected by the connection terms in each of
the `k + 3` slots.

The lemma proved here, `Work.Diff.EXT.ConnCov.step_linear_ext`, says that `step cov` is `ℝ`-linear
in `τ` (pointwise in the values): for a pointwise linear combination `c₁ · τ₁ + c₂ · τ₂` of two
operators the recursion step is the same linear combination of the two recursion steps.  The
hypotheses `h₁`, `h₂` (smoothness of `τᵢ` applied to smooth fields) provide exactly the
differentiability needed to apply additivity of `mvfderiv` to the derivative term; all the
connection corrections are pointwise linear.

This is a tool of the *conversion* programme between the `∇^{G 0}`- and the `∇^{G t}`-towers of the
connection difference (`Submission/Work/Diff/EXT/ConnCov/`): the base of the `dAOfBase`-tower is a
fixed linear combination of index permutations of the Ricci/S₀ tensors, so the recursion has to be
pushed through that combination.

The statement is deliberately *parameterized* (no `[I.Boundaryless]`, no `[T2Space M]`, no
smoothness of the connection), so that it can be imported by any of the files of the conversion
chain without dragging in the rest of the development.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

/-- **The applied form of additivity of `mvfderiv`** for real-valued functions, stated without the
extra structural hypotheses (`[I.Boundaryless]`, `[T2Space M]`) that the `ATower` version
`Work.Diff.EXT.ATower.mvfderiv_add_ka` carries in its section variables. -/
lemma connCov_mvfderiv_add_val
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {f g : M → ℝ} {x : M} {v : TangentSpace I x}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) :
    mvfderiv I (f + g) x v = mvfderiv I f x v + mvfderiv I g x v := by
  rw [mvfderiv_add hf hg, add_apply]

/-- **The constant-multiple rule for `mvfderiv` of a real-valued function**, in applied form.
Immediate from the Leibniz rule `mvfderiv_smul` applied to the constant scalar field
`fun _ ↦ c`, whose derivative vanishes (`mvfderiv_const`). -/
lemma connCov_mvfderiv_const_mul_val
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {c : ℝ} {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => c * f y) x v = c * mvfderiv I f x v := by
  have hzero : mvfderiv I (fun _ : M => c) x = 0 := mvfderiv_const c
  have hsmul := mvfderiv_smul (I := I) (x := x) (a := fun _ : M => c) (g := f)
      (mdifferentiableAt_const (c := c)) hf
  have hfun : (fun y : M => c * f y) = (fun _ : M => c) • f := rfl
  rw [hfun, hsmul, hzero]
  simp

/-- **Linearity of `mvfderiv` in the function, for a two-term linear combination with constant
coefficients.**  This is the derivative half of the linearity of the recursion `step`. -/
lemma connCov_mvfderiv_add_const_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {f₁ f₂ : M → ℝ} {x : M} {v : TangentSpace I x}
    (hf₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) f₁ x) (hf₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) f₂ x)
    (c₁ c₂ : ℝ) :
    mvfderiv I (fun y : M => c₁ * f₁ y + c₂ * f₂ y) x v
      = c₁ * mvfderiv I f₁ x v + c₂ * mvfderiv I f₂ x v := by
  have h₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => c₁ * f₁ y) x :=
    (mdifferentiableAt_const (c := c₁)).mul hf₁
  have h₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => c₂ * f₂ y) x :=
    (mdifferentiableAt_const (c := c₂)).mul hf₂
  have hsplit : (fun y : M => c₁ * f₁ y + c₂ * f₂ y)
      = (fun y : M => c₁ * f₁ y) + (fun y : M => c₂ * f₂ y) := rfl
  rw [hsplit, connCov_mvfderiv_add_val h₁ h₂,
    connCov_mvfderiv_const_mul_val hf₁ v, connCov_mvfderiv_const_mul_val hf₂ v]

theorem step_linear_ext
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (c₁ c₂ : ℝ) (τ₁ τ₂ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k)
    (h₁ : ∀ (w : Fin k → (Π y : M, TangentSpace I y)) (X Y Z : Π y : M, TangentSpace I y),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (w i)) → Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmF I M (τ₁ w X Y Z))
    (h₂ : ∀ (w : Fin k → (Π y : M, TangentSpace I y)) (X Y Z : Π y : M, TangentSpace I y),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (w i)) → Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmF I M (τ₂ w X Y Z))
    (v : Fin (k + 1) → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y)
    (hv : ∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) (hA : Work.Diff.EXT.ATower.SmE I M A)
    (hB : Work.Diff.EXT.ATower.SmE I M B) (hC : Work.Diff.EXT.ATower.SmE I M C) (x : M) :
    Work.Diff.EXT.ATower.step cov
        (fun w X Y Z y => c₁ * τ₁ w X Y Z y + c₂ * τ₂ w X Y Z y) v A B C x
      = c₁ * Work.Diff.EXT.ATower.step cov τ₁ v A B C x
        + c₂ * Work.Diff.EXT.ATower.step cov τ₂ v A B C x := by
  -- The tail of the direction tuple is the tuple on which both operators are evaluated; its
  -- smoothness is inherited from `hv`.
  have hw : ∀ j : Fin k, Work.Diff.EXT.ATower.SmE I M ((fun i : Fin k => v i.succ) j) :=
    fun j => hv j.succ
  -- Smoothness (hence differentiability) of the two functions whose `mvfderiv` occurs in `step`.
  have hf₁ : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (τ₁ (fun i : Fin k => v i.succ) A B C) x := by
    have h := h₁ (fun i : Fin k => v i.succ) A B C hw hA hB hC
    exact h.mdifferentiableAt (by simp)
  have hf₂ : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (τ₂ (fun i : Fin k => v i.succ) A B C) x := by
    have h := h₂ (fun i : Fin k => v i.succ) A B C hw hA hB hC
    exact h.mdifferentiableAt (by simp)
  -- Unfold the recursion on both sides: the derivative term is handled by linearity of `mvfderiv`,
  -- the four families of connection corrections are pointwise linear.
  simp only [Work.Diff.EXT.ATower.step]
  rw [connCov_mvfderiv_add_const_mul hf₁ hf₂]
  simp only [Finset.sum_add_distrib, mul_sub]
  rw [Finset.mul_sum, Finset.mul_sum]
  ring

end Work.Diff.EXT.ConnCov
