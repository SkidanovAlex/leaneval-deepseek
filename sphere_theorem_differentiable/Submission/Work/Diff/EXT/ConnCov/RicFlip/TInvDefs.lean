import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ATens.Defs
import Submission.Work.Diff.EXT.ATens.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The packed connection-difference tower `packTower`, its unpacked twin `pkTower`, and the
induction invariants `PInv`

`Work.Diff.EXT.ATower.tower (lcOf g) base k` (`Submission/Work/Diff/EXT/ATower/Defs.lean`) is the
`k`-th iterated covariant derivative of the base operator `base : Op3 0` with respect to the
Levi-Civita connection of `g`; it has `k` derivative slots and `3` value slots.

This module provides:

* `packStep g τ F` — one recursion step in *packed* coordinates: the tuple `F : Fin (k+4) → TF`
  carries the differentiation direction in slot `0` and the `k+3` slots of `τ` in the slots
  `Fin.succ ·` (so the inserted connection term in slot `j` is `dirFA g (slot j) (direction)`).
* `packTower g base k : (Fin (k+3) → TF) → M → ℝ` — the packed tower, defined by its own recursion
  `packTower g base (k+1) F = packStep g (packTower g base k) F` (`packTower_succ`, definitional).
* `pkTower g base k F` — the *same* object read off from `tower` with the slot convention
  `derivative slots = F (Fin.castAdd 3 ·)`, `value slots = F (Fin.natAdd k ·)`; the link
  `packTower = pkTower` is `Work.Diff.EXT.ConnCov.RicFlip.packTower_eq_pkTower` (proved in the
  target file from the recursion `pkTower_succ_rec`).
* `PInv g base k` — the three induction invariants of the packed tower:
  * `SmF` (smoothness on tuples of smooth fields),
  * `C^∞`-linearity in every slot (two-term form with smooth scalar coefficients),
  * germ-locality at every point.

The induction `PInv g base 0 → PInv g base (k+1)` is decomposed into the four lemmas
`packTower_sm`, `packTower_lin_dir`, `packTower_lin_tail`, `packTower_loc` (each taking
`PInv g base k` as a hypothesis), and the base case is `PInv_zero`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov.RicFlip

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- **One recursion step in packed coordinates.**  `F` carries the differentiation direction in
slot `0` and the `k+3` slots of `τ` in the slots `Fin.succ ·`; the connection correction inserted
into slot `j` is `dirFA g (slot j) (direction)`. -/
noncomputable def packStep (g : Submission.Diff.SMet I M) {k : ℕ}
    (τ : (Fin (k + 3) → (Π y : M, TangentSpace I y)) → M → ℝ)
    (F : Fin (k + 4) → (Π y : M, TangentSpace I y)) : M → ℝ :=
  fun x => mvfderiv I (τ (fun j : Fin (k + 3) => F j.succ)) x (F 0 x)
    - ∑ j : Fin (k + 3), τ (Function.update (fun j' : Fin (k + 3) => F j'.succ) j
        (Work.Diff.EXT.dirFA g ((fun j' : Fin (k + 3) => F j'.succ) j) (F 0))) x

/-- **The packed tower.** -/
noncomputable def packTower (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) :
    ∀ k : ℕ, (Fin (k + 3) → (Π y : M, TangentSpace I y)) → M → ℝ
  | 0, F =>
      base (fun i : Fin 0 => i.elim0) (F (Fin.natAdd 0 0)) (F (Fin.natAdd 0 1))
        (F (Fin.natAdd 0 2))
  | k + 1, F => packStep g (packTower g base k) F

/-- The defining recursion of the packed tower (definitional). -/
theorem packTower_succ (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (F : Fin (k + 4) → (Π y : M, TangentSpace I y)) :
    packTower g base (k + 1) F = packStep g (packTower g base k) F := rfl

/-- The level-`0` packed tower in the shape of the base operator. -/
theorem packTower_zero (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0)
    (F : Fin 3 → (Π y : M, TangentSpace I y)) :
    packTower g base 0 F = base (fun i : Fin 0 => i.elim0) (F 0) (F 1) (F 2) := rfl

/-- **The unpacked packed tower**: `tower (lcOf g) base k` with the `k` derivative slots and the
three value slots read off from the packed tuple `F`. -/
noncomputable def pkTower (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (F : Fin (k + 3) → (Π y : M, TangentSpace I y)) : M → ℝ :=
  Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k
    (fun j : Fin k => F (Fin.castAdd 3 j)) (F (Fin.natAdd k 0)) (F (Fin.natAdd k 1))
    (F (Fin.natAdd k 2))

/-- `pkTower` of a tuple assembled from an unpacked tuple is the unpacked tower itself
(definitional through `mkT3`/`trip3`). -/
theorem pkTower_mkT3 (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (v : Fin k → (Π y : M, TangentSpace I y))
    (A B C : Π y : M, TangentSpace I y) :
    pkTower g base k (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
      = Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v A B C := by
  simp only [pkTower, Work.Diff.EXT.mkT3_castAdd, Work.Diff.EXT.mkT3_natAdd,
    Work.Diff.EXT.trip3_zero, Work.Diff.EXT.trip3_one, Work.Diff.EXT.trip3_two]

/-- **The three induction invariants of the packed tower at level `k`.** -/
def PInv (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ) : Prop :=
  ∀ F : Fin (k + 3) → (Π y : M, TangentSpace I y),
    (∀ s, Work.Diff.EXT.ATower.SmE I M (F s)) →
    Work.Diff.EXT.ATower.SmF I M (packTower g base k F) ∧
    (∀ (s : Fin (k + 3)) (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      packTower g base k (Function.update F s (f₁ • X₁ + f₂ • X₂))
        = f₁ • packTower g base k (Function.update F s X₁)
          + f₂ • packTower g base k (Function.update F s X₂)) ∧
    (∀ (x : M) (F' : Fin (k + 3) → (Π y : M, TangentSpace I y)),
      (∀ s, Work.Diff.EXT.ATower.SmE I M (F' s)) →
      (∀ s, F s =ᶠ[𝓝 x] F' s) →
      packTower g base k F =ᶠ[𝓝 x] packTower g base k F')

end Work.Diff.EXT.ConnCov.RicFlip
