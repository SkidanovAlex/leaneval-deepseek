import Mathlib
import Submission.Work.Diff.EXT.ladderSrcDefs
import Submission.Work.Diff.EXT.ladderEfDefs
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.ckt_step_tderiv
import Submission.Work.Diff.GE.curv_var_prelim
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.Evol.cv_dLC
import Submission.Work.Diff.EXT.Kpt_norm_bound
import Submission.Work.Diff.EXT.curvNormK_frame_indep
import Submission.Work.Diff.EXT.evolX.opJetSmooth_lapOpE
import Submission.Work.Diff.EXT.ConnCov.covDerivSym2DtMet
import Submission.Work.Diff.GE.Kato3.CovRmKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The trace form of the connection-variation pairing, and its jets

The target `Work.Diff.EXT.evolX.connVar_pair_jets` bounds the `a`-th jet of the pairing

  `(V, W, Z) ↦ y ↦ g_y (dLC G t V W y, Z y)`

of the first variation of the Levi-Civita connection along a Ricci flow.  The bound is
`C · √|∇^{a+1}Rm|² · ∏ √|F r|²`, i.e. it is governed by the *value* of the level-`(a+1)` covariant
derivative of the curvature at the base point.

## Route

* `dLC G t V W` is a `∇Ric` combination (`Submission.Diff.LCVariation` + `Work.Diff.GE.dLC_pairing`),
  and along a Ricci flow `∂ₜ g = −2 Ric` (`Work.Diff.GE.Sm.dtMet_eq_ric_of_flow`), so the pairing is
  a `covDerivSym2` combination (`Work.Diff.T.variation_algebra`).
* `Ric = tr Rm` in any orthonormal frame (`Work.Diff.Evol.ricAt_eq_sum_frame_ovf`), so the pairing
  is a *frame trace* of the level-`1` tower `∇Rm = ckt g 1` — this is `cvTr0` below.
* `cvTr0` traces the two *curvature* slots `1` and `3` of `ckt g 1`, the three remaining slots
  holding the arguments `(V, W, Z)`.  Its `a`-th jet is the level-`(a+1)` tower evaluated on the
  tuple in which the frame vectors are inserted in those two slots — the *trace lemma* below.  Its
  proof is the induction on the jet order, in which the two extra Leibniz corrections (from the
  inserted frame vectors) cancel by the antisymmetry of the frame velocity against its own
  symmetry.
* The tower value is bounded sharply by the Hilbert–Schmidt inequality for `Kpt`
  (`Work.Diff.EXT.Kpt_norm_bound`), whose value dependence on the tuple is
  `Work.Diff.EXT.ckt_val_dep_all`.

This module contains only the *definitions* and the elementary ballot of the insertion maps, so that
the lemmas about them can be stated in a stable vocabulary.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Insertion patterns -/

/-- The `5`-tuple `(Z 0, u, Z 1, u, Z 2)`: the slots `1` and `3` receive the frame vector `u`, the
three *free* slots `0, 2, 4` the three entries of `Z`. -/
noncomputable def cvIns5 {α : Type*} (Z : Fin 3 → α) (u : α) : Fin 5 → α :=
  ![Z 0, u, Z 1, u, Z 2]

/-- **The level-`a` insertion.**  `cvHins ρ F u : Fin (a+5)` is the tuple whose first `a` entries are
the *differentiation slots* `F 0, …, F (a-1)` and whose last five entries are the pattern
`(F (ρ 0), u, F (ρ 1), u, F (ρ 2))` on the arity-`3` block: the two `u`-slots are the two traced
curvature slots and `ρ` permutes the three free slots. -/
noncomputable def cvHins {α : Type*} {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α) :
    Fin (a + 5) → α :=
  Fin.append (fun r : Fin a => F (Fin.castAdd 3 r))
    (cvIns5 (fun t : Fin 3 => F (Fin.natAdd a (ρ t))) u)

/-- The embedding of `Fin 3` into the three even slots of `Fin 5`. -/
def cvEven (t : Fin 3) : Fin 5 := ⟨2 * t.val, by have := t.isLt; omega⟩

/-- The position of the entry `Z s` inside the insertion `cvHins ρ Z u`: the first `a` slots are
fixed, and the three entries of the arity-`3` block sit in the free positions `a`, `a+2`, `a+4`. -/
noncomputable def cvHpos (a : ℕ) (ρ : Fin 3 ≃ Fin 3) : Fin (a + 3) → Fin (a + 5) :=
  Fin.append (fun r : Fin a => Fin.castAdd 5 r)
    (fun t : Fin 3 => Fin.natAdd a (cvEven (ρ.symm t)))

/-- The permutation of the free slots used by the first `∇Ric` term of the pairing. -/
def cvRho1 : Fin 3 ≃ Fin 3 := Equiv.refl _

/-- The permutation of the free slots used by the second `∇Ric` term of the pairing. -/
def cvRho2 : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

/-- The permutation of the free slots used by the third `∇Ric` term of the pairing. -/
def cvRho3 : Fin 3 ≃ Fin 3 where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide
  right_inv := by decide

/-- The first of the two slots of the insertion `cvHins F u` that carries the frame vector `u`
(`u` sits in the `5`-block at positions `1` and `3`). -/
def cvUslot0 (a : ℕ) : Fin (a + 5) := Fin.natAdd a ⟨1, by omega⟩

/-- The second of the two slots carrying the frame vector `u`. -/
def cvUslot1 (a : ℕ) : Fin (a + 5) := Fin.natAdd a ⟨3, by omega⟩

/-- `cvDrop0 G` deletes the first (differentiation) slot of the tuple `G`. -/
def cvDrop0 {α : Type*} {n : ℕ} (G : Fin (n + 1) → α) : Fin n → α := fun r => G r.succ

/-! ## The trace operator and the operators of the pairing -/

/-- The reindexing `Fin (a+3) ≃ Fin (3+a)` used to feed the `jetAll`-tuple of the trace lemma. -/
def cvCast3 (a : ℕ) : Fin (a + 3) → Fin (3 + a) := Fin.cast (by omega)

@[simp] theorem cvCast3_val {a : ℕ} (i : Fin (a + 3)) : (cvCast3 a i).val = i.val := rfl

/-- The reindexing `Fin (3+a) ≃ Fin (a+3)`, the inverse of `cvCast3`. -/
def cvCast3' (a : ℕ) : Fin (3 + a) → Fin (a + 3) := Fin.cast (by omega)

theorem cvCast3'_cvCast3 {a : ℕ} (i : Fin (a + 3)) : cvCast3' a (cvCast3 a i) = i := by
  simp [cvCast3, cvCast3']

theorem cvCast3_cast3' {a : ℕ} (i : Fin (3 + a)) : cvCast3 a (cvCast3' a i) = i := by
  simp [cvCast3, cvCast3']

/-- **The trace of the level-`1` curvature tower**:
`cvTr0 g ef Z y = ∑_m (∇_{Z 0} Rm)(ef m, Z 1, ef m, Z 2)`, i.e. the trace of `∇Rm` in the two
curvature slots `1` and `3` along the frame `ef`. -/
noncomputable def cvTr0 (g : SMet I M)
    (ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)) :
    (Fin 3 → TField (I := I) (M := M)) → M → ℝ :=
  fun Z y => ∑ m, ckt g 1 (cvIns5 Z (ef m)) y

/-- **The general trace operator**: the trace of the level-`1` tower along the frame `ef` in the two
curvature slots `1` and `3`, with the three free slots permuted by `ρ`. -/
noncomputable def cvTr0ρ (g : SMet I M)
    (ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)) (ρ : Fin 3 ≃ Fin 3) :
    (Fin 3 → TField (I := I) (M := M)) → M → ℝ :=
  fun Z y => ∑ m, ckt g 1 (cvHins ρ Z (ef m)) y

/-- The slot permutation `(Z 0, Z 1, Z 2) ↦ (Z 1, Z 0, Z 2)` of an arity-`3` tuple. -/
noncomputable def cvSw3 {α : Type*} (Z : Fin 3 → α) : Fin 3 → α := ![Z 1, Z 0, Z 2]

/-- The slot permutation `(Z 0, Z 1, Z 2) ↦ (Z 2, Z 0, Z 1)` of an arity-`3` tuple. -/
noncomputable def cvCyc3 {α : Type*} (Z : Fin 3 → α) : Fin 3 → α := ![Z 2, Z 0, Z 1]

/-- **The `rmP` operator** of a metric: `u ↦ (y ↦ rmP g y (u 0 y) (u 1 y) (u 2 y) (u 3 y))`.  Its
iterated `jetAll` is the tower `ckt`. -/
noncomputable def cvRmOp (g : SMet I M) : (Fin 4 → TField (I := I) (M := M)) → M → ℝ :=
  fun u y => rmP g y (u 0 y) (u 1 y) (u 2 y) (u 3 y)

/-- **The operator of the target**: the pairing `(V,W,Z) ↦ ⟪dLC G t V W, Z⟫` of the first variation
of the Levi-Civita connection along the flow `G`. -/
noncomputable def cvPairOp (G : ℝ → SMet I M) (t : ℝ) :
    (Fin 3 → TField (I := I) (M := M)) → M → ℝ :=
  fun Z y => (G t).inner y (dLC G t (Z 0) (Z 1) y) (Z 2 y)

/-- **The combination of the three frame traces** that equals the pairing
(`connVar_pair_base`).  It is written as a *nested difference* so that the linearity of `jetAll` in
the operator (`Work.Diff.EXT.jetAll_sub_of_JetSmoothOp`) applies without further boilerplate. -/
noncomputable def cvTraceComb (g : SMet I M)
    (ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)) :
    (Fin 3 → TField (I := I) (M := M)) → M → ℝ :=
  (cvTr0ρ g ef cvRho3 - cvTr0ρ g ef cvRho1) - cvTr0ρ g ef cvRho2

/-- The combination is (pointwise) the negative of the sum of the `connVar_pair_base` statement. -/
theorem cvTraceComb_apply (g : SMet I M)
    (ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (Z : Fin 3 → TField (I := I) (M := M)) (y : M) :
    cvTraceComb g ef Z y
      = -(((cvTr0ρ g ef cvRho1) Z y) + ((cvTr0ρ g ef cvRho2) Z y)
          - ((cvTr0ρ g ef cvRho3) Z y)) := by
  simp only [cvTraceComb, Pi.sub_apply]
  ring

/-- The reindexing `Fin (a+3) ≃ Fin (3+a)` as an equivalence, for reindexing products. -/
def cvCastEquiv (a : ℕ) : Fin (a + 3) ≃ Fin (3 + a) where
  toFun := cvCast3 a
  invFun := cvCast3' a
  left_inv := cvCast3'_cvCast3
  right_inv := cvCast3_cast3'

end Work.Diff.EXT.evolX
