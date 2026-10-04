import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ConnCov.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The *honest* tower of `baseRic` and the shift identity

`Work.Diff.EXT.ATower.tower (lcOf g) (baseRic g) k` is the `k`-th covariant derivative of the
`(0,3)`-tensor `baseRic g = (A,B,C) ↦ Ric(A,B)`.  Because `baseRic` **ignores its third value
slot**, the recursion `step` produces, besides the honest derivatives, the *shift* corrections coming
from the unused slot: at level `1`,

`tower (lcOf g) (baseRic g) 1 v A B C = (∇_v Ric)(A,B) − Ric(A,B)`.

The present module isolates the recursion without the third-slot correction (`hstep`, the *honest*
step), the resulting *honest* tower `htower`, and records the relation
`step cov τ = hstep cov τ − drop τ` (definitional, for `hstep := step + drop`).

The main target is the **shift identity**: the tower of `baseRic` is a fixed ℤ-combination of the
honest towers evaluated on selections of the direction slots,

`tower (lcOf g) (baseRic g) m v A B C
   = Σ_{j≤m} (-1)^{m+j} (m-j)! · Σ_{f : Fin j ↪o Fin m} (htower (lcOf g) (baseRic g) j)
       (fun l => v (f l)) A B C`,

with the coefficients `c(m,j) = (-1)^{m+j}(m-j)!` determined by the recursion
`c(m+1,j+1) = c(m,j)`, `c(m+1,j) = -(m-j+1)·c(m,j)`.

The proof is an induction on `m`: on a "selection object" `(σ_j on f)` the honest step acts as
`hstep (σ_j on f) = (σ_{j+1} on f^{+0}) - (arity - j)·(σ_j on f^{+1})`, where `f^{+0}` inserts `0`
at the front and `f^{+1} l = f l + 1`, and `drop` acts as `drop (σ_j on f) = (σ_j on f^{+1})`.

## Contents

* `drop`, `hstep`, `htower`, `CIndep` (the third-slot independence);
* `step_eq_hstep_sub_drop`;
* `hstep_apply` — the honest recursion formula on third-slot-independent objects;
* `cIndep_baseRic`, `cIndep_hstep`, `cIndep_htower`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- `drop τ` is `τ` with the first direction slot discarded: it is the "shift" correction produced
by the (unused) third value slot in one application of `step`. -/
noncomputable def drop {k : ℕ} (τ : Op3 (I := I) (M := M) k) : Op3 (I := I) (M := M) (k + 1) :=
  fun v A B C x => τ (fun i : Fin k => v i.succ) A B C x

/-- **The honest recursion step**: `step` *without* the correction in the third value slot.
It is defined as `step cov τ + drop τ`, so that the relation `step = hstep - drop` is definitional. -/
noncomputable def hstep (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op3 (I := I) (M := M) k) : Op3 (I := I) (M := M) (k + 1) :=
  step cov τ + drop τ

/-- **The honest tower**: the iterated `hstep` of a base. -/
noncomputable def htower (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Op3 (I := I) (M := M) 0) : ∀ k : ℕ, Op3 (I := I) (M := M) k
  | 0 => base
  | k + 1 => hstep cov (htower cov base k)

@[simp] theorem htower_zero (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Op3 (I := I) (M := M) 0) : htower cov base 0 = base := rfl

theorem htower_succ (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Op3 (I := I) (M := M) 0) (k : ℕ) :
    htower cov base (k + 1) = hstep cov (htower cov base k) := rfl

/-- **Third-slot independence** of an operator. -/
def CIndep {k : ℕ} (τ : Op3 (I := I) (M := M) k) : Prop :=
  ∀ (v : Fin k → TF (I := I) (M := M)) (A B C C' : TF (I := I) (M := M)) (x : M),
    τ v A B C x = τ v A B C' x

/-- **The value bound used for the honest towers**: the same shape as the conclusion of
`Work.Diff.EXT.ConnCov.ricTowerBound_fixed_par` — one `(1 + √⟪vᵢ,vᵢ⟫)` factor per direction slot
and `√⟪a,a⟫ √⟪b,b⟫` for the first two value slots, and **no** factor for the third value slot
(the honest towers and `baseRic` ignore it). -/
def ValBoundNoC (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ)
    (τ : Op3 (I := I) (M := M) k) (C : ℝ) : Prop :=
  ∀ (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
    |valOp τ x v a b c|
      ≤ C * (Finset.univ.prod (fun i : Fin k => (1 + Real.sqrt ((G t).inner x (v i) (v i)))))
          * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)

/-- The relation between the two recursion steps (definitional). -/
theorem step_eq_hstep_sub_drop (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op3 (I := I) (M := M) k) :
    step cov τ = hstep cov τ - drop τ := by
  funext v A B C x
  simp only [hstep, Pi.add_apply, Pi.sub_apply]
  ring

/-- **The honest recursion formula**, on third-slot-independent objects: the third-slot correction
of `step` is exactly cancelled by `drop`. -/
theorem hstep_apply (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    {τ : Op3 (I := I) (M := M) k} (hτ : CIndep τ)
    (v : Fin (k + 1) → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (x : M) :
    hstep cov τ v A B C x
      = mvfderiv I (τ (fun i : Fin k => v i.succ) A B C) x (v 0 x)
        - (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => cov (v i.succ) y (v 0 y))) A B C x)
        - τ (fun i : Fin k => v i.succ) (fun y => cov A y (v 0 y)) B C x
        - τ (fun i : Fin k => v i.succ) A (fun y => cov B y (v 0 y)) C x := by
  have hC : τ (fun i : Fin k => v i.succ) A B (fun y => cov C y (v 0 y)) x
      = τ (fun i : Fin k => v i.succ) A B C x := hτ _ A B _ C x
  simp only [hstep, step, drop, Pi.add_apply]
  rw [hC]
  ring

/-- `baseRic` is independent of its third value slot. -/
theorem cIndep_baseRic (g : Submission.Diff.SMet I M) : CIndep (baseRic g) := by
  intro v A B C C' x
  rfl

/-- `step` preserves third-slot independence: the only place where the third argument slot enters
`step` is through `τ` itself. -/
theorem cIndep_step (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    {τ : Op3 (I := I) (M := M) k} (hτ : CIndep τ) : CIndep (step cov τ) := by
  intro v A B C C' x
  have h1 : (fun y : M => τ (fun i : Fin k => v i.succ) A B C y)
      = fun y : M => τ (fun i : Fin k => v i.succ) A B C' y := funext fun y => hτ _ A B C C' y
  have h1' : mvfderiv I (τ (fun i : Fin k => v i.succ) A B C) x (v 0 x)
      = mvfderiv I (τ (fun i : Fin k => v i.succ) A B C') x (v 0 x) :=
    congrArg (fun F : M → ℝ => mvfderiv I F x (v 0 x)) (funext fun y => hτ _ A B C C' y)
  have h2 : (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
        (fun y => cov (v i.succ) y (v 0 y))) A B C x)
      = (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
        (fun y => cov (v i.succ) y (v 0 y))) A B C' x) :=
    Finset.sum_congr rfl fun i _ => hτ _ A B C C' x
  have h3 : τ (fun i : Fin k => v i.succ) (fun y => cov A y (v 0 y)) B C x
      = τ (fun i : Fin k => v i.succ) (fun y => cov A y (v 0 y)) B C' x := hτ _ _ B C C' x
  have h4 : τ (fun i : Fin k => v i.succ) A (fun y => cov B y (v 0 y)) C x
      = τ (fun i : Fin k => v i.succ) A (fun y => cov B y (v 0 y)) C' x := hτ _ _ _ C C' x
  have h5 : τ (fun i : Fin k => v i.succ) A B (fun y => cov C y (v 0 y)) x
      = τ (fun i : Fin k => v i.succ) A B (fun y => cov C' y (v 0 y)) x := by
    rw [hτ _ A B (fun y => cov C y (v 0 y)) C x,
        hτ _ A B (fun y => cov C' y (v 0 y)) C' x]
    exact hτ _ A B C C' x
  simp only [step]
  rw [h1', h2, h3, h4, h5]

/-- `drop` preserves third-slot independence (it does not touch the slots). -/
theorem cIndep_drop {k : ℕ} {τ : Op3 (I := I) (M := M) k} (hτ : CIndep τ) :
    CIndep (drop τ) := by
  intro v A B C C' x
  exact hτ _ A B C C' x

/-- `hstep` preserves third-slot independence. -/
theorem cIndep_hstep (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    {τ : Op3 (I := I) (M := M) k} (hτ : CIndep τ) : CIndep (hstep cov τ) := by
  intro v A B C C' x
  have h1 : step cov τ v A B C x = step cov τ v A B C' x := cIndep_step cov hτ v A B C C' x
  have h2 : drop τ v A B C x = drop τ v A B C' x := cIndep_drop hτ v A B C C' x
  simp only [hstep, Pi.add_apply]
  rw [h1, h2]

/-- The honest tower of a third-slot-independent base is third-slot independent. -/
theorem cIndep_htower (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {base : Op3 (I := I) (M := M) 0} (h : CIndep base) :
    ∀ k : ℕ, CIndep (htower cov base k) := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact cIndep_hstep cov ih

/-- The tower of `baseRic` is third-slot independent. -/
theorem cIndep_tower_baseRic (g : Submission.Diff.SMet I M) (k : ℕ) :
    CIndep (tower (lcOf g) (baseRic g) k) := by
  induction k with
  | zero => exact cIndep_baseRic g
  | succ k ih => exact cIndep_step (lcOf g) ih

end Work.Diff.EXT.ConnCov
