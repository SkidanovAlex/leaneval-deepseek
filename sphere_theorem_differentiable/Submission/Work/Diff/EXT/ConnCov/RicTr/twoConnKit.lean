import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs
import Submission.Work.Diff.EXT.ATower.tower_slotAdd_smF
import Submission.Work.Diff.EXT.ATower.connDiff_flip_input
import Submission.Work.Diff.EXT.ATower.KaLinD_holds

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Kit for `Work.Diff.EXT.ConnCov.RicTr.deltaTower_bound_of_hA`

Auxiliary definitions and lemmas for
`Submission/Work/Diff/EXT/ConnCov/RicTr/deltaTower_bound_of_hA.lean`.

## The target

* `hA` bounds the `∇^{G 0}`-tower of the *lowered* connection difference
  `aOf G t = g_t(δ ·,·)`;
* the conclusion bounds the `∇^{G 0}`-tower **and** the `∇^{G t}`-tower of the connection difference
  `δ := deltaOf (G 0) (G t)` itself, in the `dvVal`/`oneAddSqrtProd` shape.

## Import land (the main practical difficulty of this target)

The workspace contains **two mutually exclusive chains of duplicates**:

* the `deltaTower` chain (`Op2`, `vstep`, `vtower`, `deltaTower`, `gtTower`, `pairOp`,
  `bndVKit`'s `selTerm`/`Wterm`/`Good`, …, and the proved fixed-`δ`-tower bound
  `Work.Diff.EXT.ConnCov.bndV_deltaTower`), and
* the `RicTowerKit` chain (`VOpM`, `vstep`, `vtower`, `dvVal`, `deltaOf`, `oneAddSqrtProd`, …),

and **no module may import both** (they declare `Work.Diff.EXT.ConnCov.vstep`/`vtower`/`VOpM`).
The *statement* of the target uses the `RicTowerKit` vocabulary (`dvVal`, `deltaOf`,
`oneAddSqrtProd`), so this file lives in the `RicTowerKit` chain; the `deltaTower` chain — and
therefore the *proved* `bndV_deltaTower` — is not importable here, and the corresponding mathematics
must be redone with the definitions below.  (The proofs in the `deltaTower` chain can be *read* and
adapted, which is how the pieces delegated from this kit are meant to be produced.)

## The objects defined here

* `dVp G t c` — the `δ`-tower `∇^{G 0,c}δ`, and `dVpM G t c` — the same for `∇^{G t}`
  (both in the `RicTowerKit` vocabulary: `dVp` is definitionally the object of the first conjunct);
* `Op2p`, `gstepP`, `gtowP`, `gtBaseP`, `gtTowerP` — the `(0,2)`-tensor (metric) tower;
* `pairT`, `Wterm` — the pairing of the metric tower with the `δ`-tower (the twisted pairing of the
  Leibniz expansion) and its `i = 0` (lowering) term.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.RicTr

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The `δ`-tower in the `RicTowerKit` vocabulary -/

/-- The `δ`-tower `∇^{G 0,c}(deltaOf (G 0) (G t))`, in the vocabulary of the target statement. -/
noncomputable def dVp (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) :
    Work.Diff.EXT.ConnCov.VOpM (I := I) (M := M) c :=
  Work.Diff.EXT.ConnCov.vtower (G 0)
    (fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y) c

/-- The `∇^{G t}`-tower of the connection difference. -/
noncomputable def dVpM (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) :
    Work.Diff.EXT.ConnCov.VOpM (I := I) (M := M) c :=
  Work.Diff.EXT.ConnCov.vtower (G t)
    (fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y) c

theorem dVp_zero (G : ℝ → SMet I M) (t : ℝ) :
    dVp (I := I) (M := M) G t 0
      = fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y := rfl

theorem dVp_succ (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) :
    dVp (I := I) (M := M) G t (c + 1)
      = Work.Diff.EXT.ConnCov.vstep (G 0) (dVp (I := I) (M := M) G t c) := rfl

theorem dVpM_zero (G : ℝ → SMet I M) (t : ℝ) :
    dVpM (I := I) (M := M) G t 0
      = fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y := rfl

theorem dVpM_succ (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) :
    dVpM (I := I) (M := M) G t (c + 1)
      = Work.Diff.EXT.ConnCov.vstep (G t) (dVpM (I := I) (M := M) G t c) := rfl

/-- The `dvVal` of the fixed `δ`-tower is the `G t`-norm of its value at the canonical
`smoothExt`-tuple — which is literally the left-hand side of the target statement. -/
theorem dvVal_dVp (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) (x : M)
    (v : Fin c → TangentSpace I x) (X Y : TangentSpace I x) :
    Work.Diff.EXT.ConnCov.dvVal (G t) (dVp (I := I) (M := M) G t c) x v X Y
      = Real.sqrt ((G t).inner x
          (dVp (I := I) (M := M) G t c
            (fun i => Submission.Diff.smoothExt x (v i)) (Submission.Diff.smoothExt x X)
            (Submission.Diff.smoothExt x Y) x)
          (dVp (I := I) (M := M) G t c
            (fun i => Submission.Diff.smoothExt x (v i)) (Submission.Diff.smoothExt x X)
            (Submission.Diff.smoothExt x Y) x)) := rfl

/-! ## The `(0,2)`-tensor tower of a metric -/

/-- Field-level operators with `k` direction slots and two value slots: the arity of the iterated
covariant derivatives of a `(0,2)`-tensor. -/
abbrev Op2p (k : ℕ) : Type _ := (Fin k → TF (I := I) (M := M)) →
  TF (I := I) (M := M) → TF (I := I) (M := M) → M → ℝ

/-- The recursion step for a `(0,2)`-tensor tower. -/
noncomputable def gstepP (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op2p (I := I) (M := M) k) : Op2p (I := I) (M := M) (k + 1) :=
  fun v X Y x =>
    mvfderiv I (τ (fun i : Fin k => v i.succ) X Y) x (v 0 x)
      - ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
          (fun y => cov (v i.succ) y (v 0 y))) X Y x
      - τ (fun i : Fin k => v i.succ) (fun y => cov X y (v 0 y)) Y x
      - τ (fun i : Fin k => v i.succ) X (fun y => cov Y y (v 0 y)) x

/-- The tower of a `(0,2)`-tensor. -/
noncomputable def gtowP (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Op2p (I := I) (M := M) 0) : ∀ k : ℕ, Op2p (I := I) (M := M) k
  | 0, v, X, Y => base v X Y
  | k + 1, v, X, Y => gstepP cov (gtowP cov base k) v X Y

/-- A metric as a `(0,2)`-tensor. -/
noncomputable def gtBaseP (g : SMet I M) : Op2p (I := I) (M := M) 0 :=
  fun _ X Y y => g.inner y (X y) (Y y)

/-- The iterated covariant derivatives of the metric `g₁` for the connection `∇^{g₀}`. -/
noncomputable def gtTowerP (g₀ g₁ : SMet I M) (i : ℕ) : Op2p (I := I) (M := M) i :=
  gtowP (Submission.Diff.lcOf g₀) (gtBaseP g₁) i

/-! ## The pairing of the metric tower with the `δ`-tower -/

/-- The pairing of a `(0,2+i)`-tensor `P` with a vector-valued `(1,2+j)`-tensor `T` along the index
maps `a : Fin i → Fin c`, `b : Fin j → Fin c`: `(P ⊙ T)(d; A, B, C) = P(d ∘ a; T(d ∘ b; B, A), C)`. -/
noncomputable def pairT {c i j : ℕ} (a : Fin i → Fin c) (b : Fin j → Fin c)
    (P : Op2p (I := I) (M := M) i) (T : Work.Diff.EXT.ConnCov.VOpM (I := I) (M := M) j) :
    Op3 (I := I) (M := M) c :=
  fun d A B C y => P (fun l => d (a l)) (T (fun l => d (b l)) B A) C y

/-- The `i = 0` term of the expansion: the lowering of the `δ`-tower by the metric `g`. -/
noncomputable def Wterm (g : SMet I M) {c : ℕ}
    (T : Work.Diff.EXT.ConnCov.VOpM (I := I) (M := M) c) : Op3 (I := I) (M := M) c :=
  fun v A B C y => g.inner y (T v B A y) (C y)

/-- The `i = 0` term of the pairing at `i = 0` is the lowering. -/
theorem pairT_zero_eq_Wterm (g : SMet I M) {c : ℕ}
    (T : Work.Diff.EXT.ConnCov.VOpM (I := I) (M := M) c) :
    pairT (I := I) (M := M) (c := c) (i := 0) (j := c)
      (fun l : Fin 0 => l.elim0) (fun l : Fin c => l) (gtBaseP g) T
      = Wterm (I := I) (M := M) g T := rfl

end Work.Diff.EXT.ConnCov.RicTr
