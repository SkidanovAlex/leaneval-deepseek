import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ATower.connDiff_flip_input
import Submission.Work.Diff.C.mvfderiv_contMDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Slot-additivity and smoothness of the `A`-tower (`Work.Diff.EXT.ATower.tower_slotAdd_smF`)

The tower `tower cov base k` (`Work.Diff.EXT.ATower.Defs`) is the `k`-th iterated covariant
derivative of a base operator `base : Op3 0`.  This file proves, for every `k`, that
`tower cov base k` is

* **additive in each of its `k + 3` slots**, on smooth fields (`SlotAdd`), and
* **sends smooth fields to smooth functions** (`SmF`),

by induction on `k`.

The induction step is the *only* mathematical content: from the same two properties of `τ` one has
to obtain them for `step cov τ`.  The point of the auxiliary operator `stepAux` below is that the
recursion `step` splits the direction tuple `v : Fin (k+1) → TF` into its head `v 0` (the
differentiation direction) and its tail `fun i ↦ v i.succ`; `stepAux` is `step` with that split
made explicit, which makes the five additivity statements (`w`-, `u`-, `A`-, `B`-, `C`-slot)
uniform.  The only ingredients used are

* `SlotAdd τ` itself (to commute `τ` with sums of *fields*),
* `mvfderiv_add` (together with the smoothness of `τ` applied to smooth fields, which gives the
  `MDiffAt` hypotheses), and
* `map_add` for the continuous linear maps `mvfderiv I F x`, `cov σ x` (no smoothness needed).

-/

namespace Work.Diff.EXT.ATower

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- `step cov τ` with the direction tuple split into its head `w` and its tail `u`. -/
noncomputable def stepAux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op3 (I := I) (M := M) k) (w : TF (I := I) (M := M))
    (u : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) : M → ℝ :=
  fun x =>
    mvfderiv I (τ u A B C) x (w x)
      - ∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y))) A B C x
      - τ u (fun y => cov A y (w y)) B C x
      - τ u A (fun y => cov B y (w y)) C x
      - τ u A B (fun y => cov C y (w y)) x

/-- `step` is `stepAux` on the head and the tail of the direction tuple. -/
theorem step_eq_stepAux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op3 (I := I) (M := M) k) (v : Fin (k + 1) → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) :
    step cov τ v A B C = stepAux cov τ (v 0) (fun i : Fin k => v i.succ) A B C := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Additivity of `stepAux` in each of its `k + 4` slots -/

/-- Additivity of `stepAux` in the differentiation direction. -/
theorem stepAux_add_w (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op3 (I := I) (M := M) k) (hτ : SlotAdd τ)
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {w w' : TF (I := I) (M := M)} (hw : SmE I M w) (hw' : SmE I M w')
    {u : Fin k → TF (I := I) (M := M)} (hu : ∀ j, SmE I M (u j))
    {A B C : TF (I := I) (M := M)} (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    stepAux cov τ (w + w') u A B C = stepAux cov τ w u A B C + stepAux cov τ w' u A B C := by
  funext x
  have h1 : mvfderiv I (τ u A B C) x (w x + w' x)
      = mvfderiv I (τ u A B C) x (w x) + mvfderiv I (τ u A B C) x (w' x) :=
    map_add _ _ _
  have hsum : (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y + w' y))) A B C x)
      = (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y))) A B C x)
        + (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w' y))) A B C x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfield : (fun y : M => cov (u i) y (w y + w' y))
        = (fun y : M => cov (u i) y (w y)) + (fun y : M => cov (u i) y (w' y)) := by
      funext y
      simp only [Pi.add_apply]
      exact map_add _ _ _
    rw [hfield]
    exact congrFun (hτ.1 i u (fun y => cov (u i) y (w y)) (fun y => cov (u i) y (w' y))
      A B C hu (hcov (u i) w (hu i) hw) (hcov (u i) w' (hu i) hw') hA hB hC) x
  have hA' : τ u (fun y => cov A y (w y + w' y)) B C x
      = τ u (fun y => cov A y (w y)) B C x + τ u (fun y => cov A y (w' y)) B C x := by
    have hfield : (fun y : M => cov A y (w y + w' y))
        = (fun y : M => cov A y (w y)) + (fun y : M => cov A y (w' y)) := by
      funext y; simp only [Pi.add_apply]; exact map_add _ _ _
    rw [hfield]
    exact congrFun (hτ.2.1 u (fun y => cov A y (w y)) (fun y => cov A y (w' y)) B C hu
      (hcov A w hA hw) (hcov A w' hA hw') hB hC) x
  have hB' : τ u A (fun y => cov B y (w y + w' y)) C x
      = τ u A (fun y => cov B y (w y)) C x + τ u A (fun y => cov B y (w' y)) C x := by
    have hfield : (fun y : M => cov B y (w y + w' y))
        = (fun y : M => cov B y (w y)) + (fun y : M => cov B y (w' y)) := by
      funext y; simp only [Pi.add_apply]; exact map_add _ _ _
    rw [hfield]
    exact congrFun (hτ.2.2.1 u A (fun y => cov B y (w y)) (fun y => cov B y (w' y)) C hu hA
      (hcov B w hB hw) (hcov B w' hB hw') hC) x
  have hC' : τ u A B (fun y => cov C y (w y + w' y)) x
      = τ u A B (fun y => cov C y (w y)) x + τ u A B (fun y => cov C y (w' y)) x := by
    have hfield : (fun y : M => cov C y (w y + w' y))
        = (fun y : M => cov C y (w y)) + (fun y : M => cov C y (w' y)) := by
      funext y; simp only [Pi.add_apply]; exact map_add _ _ _
    rw [hfield]
    exact congrFun (hτ.2.2.2 u A B (fun y => cov C y (w y)) (fun y => cov C y (w' y)) hu hA hB
      (hcov C w hC hw) (hcov C w' hC hw')) x
  simp only [stepAux, Pi.add_apply]
  rw [h1, hsum, hA', hB', hC']
  ring

/-- Additivity of `stepAux` in the first value slot. -/
theorem stepAux_add_A (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op3 (I := I) (M := M) k) (hτ : SlotAdd τ)
    (hτsm : ∀ (u : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ j, SmE I M (u j)) → SmE I M A → SmE I M B → SmE I M C → SmF I M (τ u A B C))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {w : TF (I := I) (M := M)} (hw : SmE I M w)
    {u : Fin k → TF (I := I) (M := M)} (hu : ∀ j, SmE I M (u j))
    {A A' B C : TF (I := I) (M := M)} (hA : SmE I M A) (hA' : SmE I M A')
    (hB : SmE I M B) (hC : SmE I M C) :
    stepAux cov τ w u (A + A') B C = stepAux cov τ w u A B C + stepAux cov τ w u A' B C := by
  funext x
  have hmd : ∀ (X : TF (I := I) (M := M)), SmE I M X → MDiffAt (τ u X B C) x := fun X hX =>
    (hτsm u X B C hu hX hB hC x).mdifferentiableAt (by simp)
  have huF : ∀ i : Fin k, ∀ j,
      SmE I M ((Function.update u i (fun y => cov (u i) y (w y))) j) := by
    intro i j
    by_cases hji : j = i
    · rw [hji, Function.update_self]; exact hcov (u i) w (hu i) hw
    · rw [Function.update_of_ne hji]; exact hu j
  have h1 : mvfderiv I (τ u (A + A') B C) x (w x)
      = mvfderiv I (τ u A B C) x (w x) + mvfderiv I (τ u A' B C) x (w x) := by
    rw [hτ.2.1 u A A' B C hu hA hA' hB hC, mvfderiv_add (hmd A hA) (hmd A' hA')]
    rfl
  have h2 : (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y))) (A + A') B C x)
      = (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y))) A B C x)
        + (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y))) A' B C x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      congrFun (hτ.2.1 (Function.update u i (fun y => cov (u i) y (w y))) A A' B C (huF i)
        hA hA' hB hC) x
  have hfA : (fun y : M => cov (A + A') y (w y))
      = (fun y : M => cov A y (w y)) + (fun y : M => cov A' y (w y)) := by
    funext y
    have haddA : cov (A + A') y = cov A y + cov A' y :=
      cov.isCovariantDerivativeOn.add (σ := A) (σ' := A')
        (hA.mdifferentiableAt (by simp)) (hA'.mdifferentiableAt (by simp))
    simp only [Pi.add_apply]
    rw [haddA]
    rfl
  have h3 : τ u (fun y => cov (A + A') y (w y)) B C x
      = τ u (fun y => cov A y (w y)) B C x + τ u (fun y => cov A' y (w y)) B C x := by
    rw [hfA]
    exact congrFun (hτ.2.1 u (fun y => cov A y (w y)) (fun y => cov A' y (w y)) B C hu
      (hcov A w hA hw) (hcov A' w hA' hw) hB hC) x
  have h4 : τ u (A + A') (fun y => cov B y (w y)) C x
      = τ u A (fun y => cov B y (w y)) C x + τ u A' (fun y => cov B y (w y)) C x :=
    congrFun (hτ.2.1 u A A' (fun y => cov B y (w y)) C hu hA hA'
      (hcov B w hB hw) hC) x
  have h5 : τ u (A + A') B (fun y => cov C y (w y)) x
      = τ u A B (fun y => cov C y (w y)) x + τ u A' B (fun y => cov C y (w y)) x :=
    congrFun (hτ.2.1 u A A' B (fun y => cov C y (w y)) hu hA hA' hB
      (hcov C w hC hw)) x
  simp only [stepAux, Pi.add_apply]
  rw [h1, h2, h3, h4, h5]
  ring

/-- Additivity of `stepAux` in the second value slot. -/
theorem stepAux_add_B (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op3 (I := I) (M := M) k) (hτ : SlotAdd τ)
    (hτsm : ∀ (u : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ j, SmE I M (u j)) → SmE I M A → SmE I M B → SmE I M C → SmF I M (τ u A B C))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {w : TF (I := I) (M := M)} (hw : SmE I M w)
    {u : Fin k → TF (I := I) (M := M)} (hu : ∀ j, SmE I M (u j))
    {A B B' C : TF (I := I) (M := M)} (hA : SmE I M A) (hB : SmE I M B) (hB' : SmE I M B')
    (hC : SmE I M C) :
    stepAux cov τ w u A (B + B') C = stepAux cov τ w u A B C + stepAux cov τ w u A B' C := by
  funext x
  have hmd : ∀ (X : TF (I := I) (M := M)), SmE I M X → MDiffAt (τ u A X C) x := fun X hX =>
    (hτsm u A X C hu hA hX hC x).mdifferentiableAt (by simp)
  have huF : ∀ i : Fin k, ∀ j,
      SmE I M ((Function.update u i (fun y => cov (u i) y (w y))) j) := by
    intro i j
    by_cases hji : j = i
    · rw [hji, Function.update_self]; exact hcov (u i) w (hu i) hw
    · rw [Function.update_of_ne hji]; exact hu j
  have h1 : mvfderiv I (τ u A (B + B') C) x (w x)
      = mvfderiv I (τ u A B C) x (w x) + mvfderiv I (τ u A B' C) x (w x) := by
    rw [hτ.2.2.1 u A B B' C hu hA hB hB' hC, mvfderiv_add (hmd B hB) (hmd B' hB')]
    rfl
  have h2 : (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y))) A (B + B') C x)
      = (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y))) A B C x)
        + (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y))) A B' C x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      congrFun (hτ.2.2.1 (Function.update u i (fun y => cov (u i) y (w y))) A B B' C (huF i)
        hA hB hB' hC) x
  have h3 : τ u (fun y => cov A y (w y)) (B + B') C x
      = τ u (fun y => cov A y (w y)) B C x + τ u (fun y => cov A y (w y)) B' C x :=
    congrFun (hτ.2.2.1 u (fun y => cov A y (w y)) B B' C hu (hcov A w hA hw) hB hB' hC) x
  have hfB : (fun y : M => cov (B + B') y (w y))
      = (fun y : M => cov B y (w y)) + (fun y : M => cov B' y (w y)) := by
    funext y
    have haddB : cov (B + B') y = cov B y + cov B' y :=
      cov.isCovariantDerivativeOn.add (σ := B) (σ' := B')
        (hB.mdifferentiableAt (by simp)) (hB'.mdifferentiableAt (by simp))
    simp only [Pi.add_apply]
    rw [haddB]
    rfl
  have h4 : τ u A (fun y => cov (B + B') y (w y)) C x
      = τ u A (fun y => cov B y (w y)) C x + τ u A (fun y => cov B' y (w y)) C x := by
    rw [hfB]
    exact congrFun (hτ.2.2.1 u A (fun y => cov B y (w y)) (fun y => cov B' y (w y)) C hu hA
      (hcov B w hB hw) (hcov B' w hB' hw) hC) x
  have h5 : τ u A (B + B') (fun y => cov C y (w y)) x
      = τ u A B (fun y => cov C y (w y)) x + τ u A B' (fun y => cov C y (w y)) x :=
    congrFun (hτ.2.2.1 u A B B' (fun y => cov C y (w y)) hu hA hB hB'
      (hcov C w hC hw)) x
  simp only [stepAux, Pi.add_apply]
  rw [h1, h2, h3, h4, h5]
  ring

/-- Additivity of `stepAux` in the third value slot. -/
theorem stepAux_add_C (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op3 (I := I) (M := M) k) (hτ : SlotAdd τ)
    (hτsm : ∀ (u : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ j, SmE I M (u j)) → SmE I M A → SmE I M B → SmE I M C → SmF I M (τ u A B C))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {w : TF (I := I) (M := M)} (hw : SmE I M w)
    {u : Fin k → TF (I := I) (M := M)} (hu : ∀ j, SmE I M (u j))
    {A B C C' : TF (I := I) (M := M)} (hA : SmE I M A) (hB : SmE I M B)
    (hC : SmE I M C) (hC' : SmE I M C') :
    stepAux cov τ w u A B (C + C') = stepAux cov τ w u A B C + stepAux cov τ w u A B C' := by
  funext x
  have hmd : ∀ (X : TF (I := I) (M := M)), SmE I M X → MDiffAt (τ u A B X) x := fun X hX =>
    (hτsm u A B X hu hA hB hX x).mdifferentiableAt (by simp)
  have huF : ∀ i : Fin k, ∀ j,
      SmE I M ((Function.update u i (fun y => cov (u i) y (w y))) j) := by
    intro i j
    by_cases hji : j = i
    · rw [hji, Function.update_self]; exact hcov (u i) w (hu i) hw
    · rw [Function.update_of_ne hji]; exact hu j
  have h1 : mvfderiv I (τ u A B (C + C')) x (w x)
      = mvfderiv I (τ u A B C) x (w x) + mvfderiv I (τ u A B C') x (w x) := by
    rw [hτ.2.2.2 u A B C C' hu hA hB hC hC', mvfderiv_add (hmd C hC) (hmd C' hC')]
    rfl
  have h2 : (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y))) A B (C + C') x)
      = (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y))) A B C x)
        + (∑ i : Fin k, τ (Function.update u i (fun y => cov (u i) y (w y))) A B C' x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      congrFun (hτ.2.2.2 (Function.update u i (fun y => cov (u i) y (w y))) A B C C' (huF i)
        hA hB hC hC') x
  have h3 : τ u (fun y => cov A y (w y)) B (C + C') x
      = τ u (fun y => cov A y (w y)) B C x + τ u (fun y => cov A y (w y)) B C' x :=
    congrFun (hτ.2.2.2 u (fun y => cov A y (w y)) B C C' hu (hcov A w hA hw) hB hC hC') x
  have h4 : τ u A (fun y => cov B y (w y)) (C + C') x
      = τ u A (fun y => cov B y (w y)) C x + τ u A (fun y => cov B y (w y)) C' x :=
    congrFun (hτ.2.2.2 u A (fun y => cov B y (w y)) C C' hu hA (hcov B w hB hw) hC hC') x
  have hfC : (fun y : M => cov (C + C') y (w y))
      = (fun y : M => cov C y (w y)) + (fun y : M => cov C' y (w y)) := by
    funext y
    have haddC : cov (C + C') y = cov C y + cov C' y :=
      cov.isCovariantDerivativeOn.add (σ := C) (σ' := C')
        (hC.mdifferentiableAt (by simp)) (hC'.mdifferentiableAt (by simp))
    simp only [Pi.add_apply]
    rw [haddC]
    rfl
  have h5 : τ u A B (fun y => cov (C + C') y (w y)) x
      = τ u A B (fun y => cov C y (w y)) x + τ u A B (fun y => cov C' y (w y)) x := by
    rw [hfC]
    exact congrFun (hτ.2.2.2 u A B (fun y => cov C y (w y)) (fun y => cov C' y (w y)) hu hA hB
      (hcov C w hC hw) (hcov C' w hC' hw)) x
  simp only [stepAux, Pi.add_apply]
  rw [h1, h2, h3, h4, h5]
  ring

/-- Additivity of `stepAux` in the `j`-th slot of the tail of the direction tuple. -/
theorem stepAux_add_u (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op3 (I := I) (M := M) k) (hτ : SlotAdd τ)
    (hτsm : ∀ (u : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ j, SmE I M (u j)) → SmE I M A → SmE I M B → SmE I M C → SmF I M (τ u A B C))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {w : TF (I := I) (M := M)} (hw : SmE I M w)
    {u : Fin k → TF (I := I) (M := M)} (hu : ∀ j, SmE I M (u j))
    (j : Fin k) {X X' : TF (I := I) (M := M)} (hX : SmE I M X) (hX' : SmE I M X')
    {A B C : TF (I := I) (M := M)} (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    stepAux cov τ w (Function.update u j (X + X')) A B C
      = stepAux cov τ w (Function.update u j X) A B C
        + stepAux cov τ w (Function.update u j X') A B C := by
  funext x
  have hup : ∀ (S : TF (I := I) (M := M)), SmE I M S → ∀ l,
      SmE I M (Function.update u j S l) := by
    intro S hS l
    by_cases hl : l = j
    · rw [hl, Function.update_self]; exact hS
    · rw [Function.update_of_ne hl]; exact hu l
  have hmd : ∀ (S : TF (I := I) (M := M)) (hS : SmE I M S),
      MDiffAt (τ (Function.update u j S) A B C) x := fun S hS =>
    (hτsm (Function.update u j S) A B C (hup S hS) hA hB hC x).mdifferentiableAt (by simp)
  have h1 : mvfderiv I (τ (Function.update u j (X + X')) A B C) x (w x)
      = mvfderiv I (τ (Function.update u j X) A B C) x (w x)
        + mvfderiv I (τ (Function.update u j X') A B C) x (w x) := by
    rw [hτ.1 j u X X' A B C hu hX hX' hA hB hC, mvfderiv_add (hmd X hX) (hmd X' hX')]
    rfl
  have h2 : (∑ i : Fin k, τ (Function.update (Function.update u j (X + X')) i
        (fun y => cov ((Function.update u j (X + X')) i) y (w y))) A B C x)
      = (∑ i : Fin k, τ (Function.update (Function.update u j X) i
          (fun y => cov ((Function.update u j X) i) y (w y))) A B C x)
        + (∑ i : Fin k, τ (Function.update (Function.update u j X') i
          (fun y => cov ((Function.update u j X') i) y (w y))) A B C x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : i = j
    · rw [hij]
      have hFS : (fun y : M => cov (X + X') y (w y))
          = (fun y : M => cov X y (w y)) + (fun y : M => cov X' y (w y)) := by
        funext y
        have hc : cov (X + X') y = cov X y + cov X' y :=
          cov.isCovariantDerivativeOn.add (σ := X) (σ' := X')
            (hX.mdifferentiableAt (by simp)) (hX'.mdifferentiableAt (by simp))
        simp only [Pi.add_apply]
        rw [hc]
        rfl
      simp only [Function.update_idem, Function.update_self]
      rw [hFS]
      exact congrFun (hτ.1 j u (fun y => cov X y (w y)) (fun y => cov X' y (w y)) A B C hu
        (hcov X w hX hw) (hcov X' w hX' hw) hA hB hC) x
    · have hji : i ≠ j := hij
      have hFi : ∀ (S : TF (I := I) (M := M)),
          (fun y : M => cov ((Function.update u j S) i) y (w y))
            = fun y : M => cov (u i) y (w y) := by
        intro S; rw [Function.update_of_ne hji]
      have hGi : ∀ l, SmE I M (Function.update u i (fun y => cov (u i) y (w y)) l) := by
        intro l
        by_cases hli : l = i
        · rw [hli, Function.update_self]; exact hcov (u i) w (hu i) hw
        · rw [Function.update_of_ne hli]; exact hu l
      rw [hFi (X + X'), hFi X, hFi X',
        ← Function.update_comm hji (fun y => cov (u i) y (w y)) (X + X') u,
        ← Function.update_comm hji (fun y => cov (u i) y (w y)) X u,
        ← Function.update_comm hji (fun y => cov (u i) y (w y)) X' u]
      exact congrFun (hτ.1 j (Function.update u i (fun y => cov (u i) y (w y))) X X' A B C
        hGi hX hX' hA hB hC) x
  have h3 : τ (Function.update u j (X + X')) (fun y => cov A y (w y)) B C x
      = τ (Function.update u j X) (fun y => cov A y (w y)) B C x
        + τ (Function.update u j X') (fun y => cov A y (w y)) B C x :=
    congrFun (hτ.1 j u X X' (fun y => cov A y (w y)) B C hu hX hX'
      (hcov A w hA hw) hB hC) x
  have h4 : τ (Function.update u j (X + X')) A (fun y => cov B y (w y)) C x
      = τ (Function.update u j X) A (fun y => cov B y (w y)) C x
        + τ (Function.update u j X') A (fun y => cov B y (w y)) C x :=
    congrFun (hτ.1 j u X X' A (fun y => cov B y (w y)) C hu hX hX' hA
      (hcov B w hB hw) hC) x
  have h5 : τ (Function.update u j (X + X')) A B (fun y => cov C y (w y)) x
      = τ (Function.update u j X) A B (fun y => cov C y (w y)) x
        + τ (Function.update u j X') A B (fun y => cov C y (w y)) x :=
    congrFun (hτ.1 j u X X' A B (fun y => cov C y (w y)) hu hX hX' hA hB
      (hcov C w hC hw)) x
  simp only [stepAux, Pi.add_apply]
  rw [h1, h2, h3, h4, h5]
  ring

/-- Smoothness of `stepAux` on smooth fields. -/
theorem stepAux_smF (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op3 (I := I) (M := M) k)
    (hτsm : ∀ (u : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ j, SmE I M (u j)) → SmE I M A → SmE I M B → SmE I M C → SmF I M (τ u A B C))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {w : TF (I := I) (M := M)} (hw : SmE I M w)
    {u : Fin k → TF (I := I) (M := M)} (hu : ∀ j, SmE I M (u j))
    {A B C : TF (I := I) (M := M)} (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    SmF I M (stepAux cov τ w u A B C) := by
  intro x
  have huF : ∀ i : Fin k, ∀ l,
      SmE I M ((Function.update u i (fun y => cov (u i) y (w y))) l) := by
    intro i l
    by_cases hli : l = i
    · rw [hli, Function.update_self]; exact hcov (u i) w (hu i) hw
    · rw [Function.update_of_ne hli]; exact hu l
  have h1 : CMDiffAt ∞ (fun y : M => mvfderiv I (τ u A B C) y (w y)) x :=
    Work.Diff.C.mvfderiv_contMDiffAt (hτsm u A B C hu hA hB hC x) (hw x)
  have h2 : CMDiffAt ∞ (fun y : M =>
      ∑ i : Fin k, τ (Function.update u i (fun z => cov (u i) z (w z))) A B C y) x :=
    ContMDiffAt.sum (t := Finset.univ)
      (f := fun i : Fin k => τ (Function.update u i (fun z => cov (u i) z (w z))) A B C)
      (fun i _ => hτsm _ A B C (huF i) hA hB hC x)
  have h3 : CMDiffAt ∞ (fun y : M => τ u (fun z => cov A z (w z)) B C y) x :=
    hτsm u (fun z => cov A z (w z)) B C hu (hcov A w hA hw) hB hC x
  have h4 : CMDiffAt ∞ (fun y : M => τ u A (fun z => cov B z (w z)) C y) x :=
    hτsm u A (fun z => cov B z (w z)) C hu hA (hcov B w hB hw) hC x
  have h5 : CMDiffAt ∞ (fun y : M => τ u A B (fun z => cov C z (w z)) y) x :=
    hτsm u A B (fun z => cov C z (w z)) hu hA hB (hcov C w hC hw) x
  exact (((h1.sub h2).sub h3).sub h4).sub h5

/-! ## The induction step and the main theorem -/

/-- The two properties of an operator that the induction carries: additivity in every slot on
smooth fields, and smoothness on smooth fields. -/
def GoodOp {k : ℕ} (τ : Op3 (I := I) (M := M) k) : Prop :=
  SlotAdd τ ∧ ∀ (u : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
    (∀ j, SmE I M (u j)) → SmE I M A → SmE I M B → SmE I M C → SmF I M (τ u A B C)

/-- The recursion step preserves `GoodOp`. -/
theorem goodOp_step (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {k : ℕ} {τ : Op3 (I := I) (M := M) k} (h : GoodOp τ) : GoodOp (step cov τ) := by
  obtain ⟨hτ, hτsm⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- additivity in the differentiation (`Fin (k+1)`) slots
    intro i v W W' A B C hv hW hW' hA hB hC
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
    · rw [hi]
      have key : ∀ S : TF (I := I) (M := M),
          step cov τ (Function.update v (0 : Fin (k + 1)) S) A B C
            = stepAux cov τ S (fun i : Fin k => v i.succ) A B C := by
        intro S
        have h1 : (Function.update v (0 : Fin (k + 1)) S) 0 = S := Function.update_self ..
        have h2 : (fun i : Fin k => (Function.update v (0 : Fin (k + 1)) S) i.succ)
            = fun i : Fin k => v i.succ := by
          funext i
          exact Function.update_of_ne (Fin.succ_ne_zero i) S v
        rw [step_eq_stepAux, h1, h2]
      rw [key (W + W'), key W, key W']
      exact stepAux_add_w cov τ hτ hcov hW hW' (fun i => hv i.succ) hA hB hC
    · rw [hj]
      have key : ∀ S : TF (I := I) (M := M),
          step cov τ (Function.update v j.succ S) A B C
            = stepAux cov τ (v 0) (Function.update (fun i : Fin k => v i.succ) j S) A B C := by
        intro S
        have h1 : (Function.update v j.succ S) 0 = v 0 :=
          Function.update_of_ne (Fin.succ_ne_zero j).symm S v
        have h2 : (fun i : Fin k => (Function.update v j.succ S) i.succ)
            = Function.update (fun i : Fin k => v i.succ) j S := by
          funext i
          simp only [Function.update_apply, Fin.succ_inj]
        rw [step_eq_stepAux, h1, h2]
      rw [key (W + W'), key W, key W']
      exact stepAux_add_u cov τ hτ hτsm hcov (hv 0) (fun i => hv i.succ) j hW hW' hA hB hC
  · -- additivity in the first value slot
    intro v A A' B C hv hA hA' hB hC
    exact stepAux_add_A cov τ hτ hτsm hcov (hv 0) (fun i => hv i.succ) hA hA' hB hC
  · -- additivity in the second value slot
    intro v A B B' C hv hA hB hB' hC
    exact stepAux_add_B cov τ hτ hτsm hcov (hv 0) (fun i => hv i.succ) hA hB hB' hC
  · -- additivity in the third value slot
    intro v A B C C' hv hA hB hC hC'
    exact stepAux_add_C cov τ hτ hτsm hcov (hv 0) (fun i => hv i.succ) hA hB hC hC'
  · -- smoothness
    intro v A B C hv hA hB hC
    exact stepAux_smF cov τ hτsm hcov (hv 0) (fun i => hv i.succ) hA hB hC

theorem tower_slotAdd_smF
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0}
    (hadd : Work.Diff.EXT.ATower.SlotAdd base)
    (hsm : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmF I M (base v A B C)) :
    ∀ k : ℕ,
      Work.Diff.EXT.ATower.SlotAdd (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k) ∧
      ∀ (v : Fin k → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
        (∀ j, Work.Diff.EXT.ATower.SmE I M (v j)) → Work.Diff.EXT.ATower.SmE I M A →
        Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M C →
        Work.Diff.EXT.ATower.SmF I M
          (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v A B C) := by
  have hcov : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (fun y => Submission.Diff.lcOf g Y y (Z y)) :=
    fun Y Z hY hZ => lcOf_apply_smE hLC g Y Z hY hZ
  intro k
  induction k with
  | zero => exact ⟨hadd, fun v A B C _ hA hB hC => hsm v A B C hA hB hC⟩
  | succ k ih => exact goodOp_step (Submission.Diff.lcOf g) hcov ih

end Work.Diff.EXT.ATower
