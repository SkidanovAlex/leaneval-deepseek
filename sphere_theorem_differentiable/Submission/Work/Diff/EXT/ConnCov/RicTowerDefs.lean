import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.EXT.covK_linear
import Submission.Work.Diff.EXT.ATower.tower_slotAdd_smF

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The *honest* `(0,2)`-tensor tower of the Ricci tensor

`Work.Diff.EXT.ATower.tower` is the iterated covariant derivative of an `Op3` (an operator with
three value slots and `k` derivative slots).  Feeding it the base
`baseRic g = fun _ A B C y => ricAt (lcOf g) y (A y) (B y)` produces the tower of the *pullback* of
`Ric` along `(A,B,C) ↦ (A,B)`, i.e. the recursion pays a spurious correction for the dummy third
slot (`tower (lcOf g) (baseRic g) 1 v A B C = ∇_v Ric(A,B) − Ric(A,B)`).

This module introduces the *honest* `(0,2)`-tensor recursion, with two value slots only:

* `Op2 k` — an operator with `k` derivative slots and two value slots;
* `step2 cov τ` — the recursion step (the covariant derivative of a `(0,2)`-tensor-valued tower);
* `tower2 cov base k` — the `k`-th iterated covariant derivative of the base `(0,2)`-tensor;
* `baseRic2 g` — the Ricci tensor as an `Op2 0`;
* `lift23 β` — the lift of an `Op2 0` to an `Op3 0` with a dummy third slot, so that
  `lift23 (baseRic2 g) = baseRic g` (definitionally);
* `prefOf v h` — the prefix `(v 0, …, v (i-1))` of a tuple, used to state the **shift identity**
  `tower cov (lift23 β) m = ∑ i, (-1)^(m-i) C(m,i) • (tower2 cov β i ∘ prefOf · i)`;
* `gramMat`, `gramInv`, `Bc` — the Gram matrix of the canonical basis of the model space and its
  inverse, used for the **contraction identity**
  `tower2 (lcOf g) (baseRic2 g) m v A B x = ∑ p q, (gramInv g x) p q * covKRmExt g m v (Bc p) A B (Bc q) x`.

Nothing here is proved beyond the definitional unfoldings; the two identities above are the targets
of the chapter.
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

/-! ## The honest `(0,2)`-tensor tower -/

/-- A field-level operator with `k` derivative slots and **two** value slots. -/
abbrev Op2 (k : ℕ) : Type _ := (Fin k → TF (I := I) (M := M)) → TF (I := I) (M := M) →
  TF (I := I) (M := M) → M → ℝ

/-- **The recursion step for a `(0,2)`-tensor tower**: the covariant derivative of `τ` with
connection `cov` (the tensor-valued analogue of `ATower.step` with two value slots). -/
noncomputable def step2 (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op2 (I := I) (M := M) k) : Op2 (I := I) (M := M) (k + 1) :=
  fun v A B x =>
    mvfderiv I (τ (fun i : Fin k => v i.succ) A B) x (v 0 x)
      - ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
          (fun y => cov (v i.succ) y (v 0 y))) A B x
      - τ (fun i : Fin k => v i.succ) (fun y => cov A y (v 0 y)) B x
      - τ (fun i : Fin k => v i.succ) A (fun y => cov B y (v 0 y)) x

/-- **The honest tower of a `(0,2)`-tensor base**: its `k`-th iterated covariant derivative. -/
noncomputable def tower2 (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Op2 (I := I) (M := M) 0) :
    ∀ k : ℕ, Op2 (I := I) (M := M) k
  | 0, v, A, B => base v A B
  | k + 1, v, A, B => step2 cov (tower2 cov base k) v A B

/-- The Ricci tensor of `g` as an `Op2 0` (the honest `(0,2)`-tensor). -/
noncomputable def baseRic2 (g : SMet I M) : Op2 (I := I) (M := M) 0 :=
  fun _ A B y => ricAt (lcOf g) y (A y) (B y)

/-- The lift of an `Op2 0` to an `Op3 0` with a dummy third value slot. -/
noncomputable def lift23 (β : Op2 (I := I) (M := M) 0) : Op3 (I := I) (M := M) 0 :=
  fun v A B _ y => β v A B y

/-- `lift23 (baseRic2 g)` is `baseRic g` definitionally. -/
theorem lift23_baseRic2 (g : SMet I M) : lift23 (baseRic2 (I := I) (M := M) g) = baseRic g := rfl

/-- The prefix `(v 0, …, v (i-1))` of a tuple `v : Fin m → TF`, as a tuple of length `i`. -/
def prefOf {m : ℕ} (v : Fin m → TF (I := I) (M := M)) {i : ℕ} (h : i ≤ m) :
    Fin i → TF (I := I) (M := M) :=
  fun j => v (Fin.castLE h j)

/-- `step2` written out at level `k+1` (definitional). -/
theorem step2_apply {k : ℕ} (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (τ : Op2 (I := I) (M := M) k) (v : Fin (k + 1) → TF (I := I) (M := M))
    (A B : TF (I := I) (M := M)) (x : M) :
    step2 cov τ v A B x
      = mvfderiv I (τ (fun i : Fin k => v i.succ) A B) x (v 0 x)
        - ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => cov (v i.succ) y (v 0 y))) A B x
        - τ (fun i : Fin k => v i.succ) (fun y => cov A y (v 0 y)) B x
        - τ (fun i : Fin k => v i.succ) A (fun y => cov B y (v 0 y)) x := rfl

/-- The tower at level `0` (definitional). -/
theorem tower2_zero (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Op2 (I := I) (M := M) 0) (v : Fin 0 → TF (I := I) (M := M))
    (A B : TF (I := I) (M := M)) (x : M) :
    tower2 cov base 0 v A B x = base v A B x := rfl

/-- The tower at level `k+1` (definitional). -/
theorem tower2_succ (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Op2 (I := I) (M := M) 0) (k : ℕ) (v : Fin (k + 1) → TF (I := I) (M := M))
    (A B : TF (I := I) (M := M)) (x : M) :
    tower2 cov base (k + 1) v A B x = step2 cov (tower2 cov base k) v A B x := rfl

/-! ## The Gram matrix of the canonical basis and its inverse

`Bc p` is the `p`-th vector of the canonical basis of the model space, viewed as a constant tangent
field; `gramMat g x` is the Gram matrix of `(Bc p x) p` and `gramInv g x` its inverse.  These are the
coefficients of the *metric contraction* `Ric(A,B) = ∑ p q, gramInv p q * R (Bc p, A, B, Bc q)`. -/

/-- The `p`-th canonical basis vector of the model space, viewed as a constant tangent field. -/
noncomputable def Bc (p : Fin (Module.finrank ℝ E)) : TF (I := I) (M := M) :=
  fun y => ((Module.finBasis ℝ E) p : E)

/-- The Gram matrix of the canonical basis of the model space in the metric `g` at `x`. -/
noncomputable def gramMat (g : SMet I M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of (fun p q => g.inner x ((Module.finBasis ℝ E) p : E) ((Module.finBasis ℝ E) q : E))

/-- The inverse Gram matrix. -/
noncomputable def gramInv (g : SMet I M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (gramMat (I := I) (M := M) g x)⁻¹

/-- **The Christoffel symbol in the canonical basis**: the coefficient of `Bc a` in `∇_v (Bc r)`,
computed for the Levi-Civita connection of `g`. -/
noncomputable def Gam (g : SMet I M) (x : M) (v : TangentSpace I x)
    (r : Fin (Module.finrank ℝ E)) (a : Fin (Module.finrank ℝ E)) : ℝ :=
  (Module.finBasis ℝ E).coord a ((lcOf g) (Bc (I := I) (M := M) r) x v)

/-! ## The "drop the head" shift and the shifted tower of a lifted base

`dropHead σ` is `σ` with the direction slots shifted by one (`(dropHead σ) v = σ v_{>0}`), i.e. the
operator that appears as the spurious third-slot correction of `ATower.step` when the base ignores
its third value slot.  `sigmaTower cov β` is defined by the recursion

`σ_0 = β`, `σ_{k+1} = step2 cov σ_k - dropHead σ_k`,

and it is the object whose `Op3`-lift is `tower cov (lift23 β) k` (see `RicTower_lift_eq_sigmaTower`).
Its expansion into the honest towers `tower2 cov β i` on *sub-tuples* of the slots
(`RicTower_lift_span`) is what turns the shifted tower into a bounded number of honest towers. -/

/-- **Drop the head**: the direction slots of `σ` shifted by one. -/
noncomputable def dropHead {k : ℕ} (σ : Op2 (I := I) (M := M) k) :
    Op2 (I := I) (M := M) (k + 1) :=
  fun v A B x => σ (fun i : Fin k => v i.succ) A B x

/-- The tower of the *shift*: `σ_{k+1} = step2 σ_k - dropHead σ_k`. -/
noncomputable def sigmaTower (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (β : Op2 (I := I) (M := M) 0) :
    ∀ k : ℕ, Op2 (I := I) (M := M) k
  | 0, v, A, B => β v A B
  | k + 1, v, A, B =>
      step2 cov (sigmaTower cov β k) v A B - dropHead (sigmaTower cov β k) v A B

/-- The recursion of `sigmaTower` (definitional). -/
theorem sigmaTower_succ (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (β : Op2 (I := I) (M := M) 0) (k : ℕ) (v : Fin (k + 1) → TF (I := I) (M := M))
    (A B : TF (I := I) (M := M)) (x : M) :
    sigmaTower cov β (k + 1) v A B x
      = step2 cov (sigmaTower cov β k) v A B x - dropHead (sigmaTower cov β k) v A B x := rfl

/-- `sigmaTower` at level `0` (definitional). -/
theorem sigmaTower_zero (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (β : Op2 (I := I) (M := M) 0) (v : Fin 0 → TF (I := I) (M := M))
    (A B : TF (I := I) (M := M)) (x : M) :
    sigmaTower cov β 0 v A B x = β v A B x := rfl

end Work.Diff.EXT.ConnCov
