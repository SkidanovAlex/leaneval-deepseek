import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.BlockDefs` — the two-block fibres of a box state

`Work.BoseFixR.BoxWordLower` needs the **additivity of the box word over blocks of
particles**: the word `wordB v h μ n Φ` splits as the sum of the words of the two
blocks of a partition of the slots (the intra-block pair terms, the intra-block
kinetic slot forms and the intra-block chemical terms), while the cross-block pair
terms are `≥ 0` (they carry the pointwise nonnegative kernel `wLoc ℓ v 0`).

This module provides the two *fibre* maps used to state that splitting: for a
smooth `Φ : XN (k + j) → ℝ`, a state of the first block (`k` slots) and of the
second block (`j` slots) is obtained by fixing the other block's variables.

* `bfL k j Φ y : XN k → ℝ`, `z ↦ Φ (z, y)` — the first-block fibre;
* `bfR k j Φ z : XN j → ℝ`, `y ↦ Φ (z, y)` — the second-block fibre.

The split itself is the theorem `Work.BoseFixR.SplitTwo` in the sibling module
`Submission.Work.BoseFixR.SplitTwo`; it is stated in terms of these two maps.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixR

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The first-block fibre**: fix the last `j` slots to `y`, keep the first `k` free. -/
def bfL {k j : ℕ} (Φ : XN (k + j) → ℝ) (y : XN j) : XN k → ℝ :=
  fun z => Φ (fun i : Fin (k + j) =>
    if h : (i : ℕ) < k then z ⟨i, h⟩
    else y ⟨(i : ℕ) - k, by omega⟩)

/-- **The second-block fibre**: fix the first `k` slots to `z`, keep the last `j` free. -/
def bfR {k j : ℕ} (Φ : XN (k + j) → ℝ) (z : XN k) : XN j → ℝ :=
  fun y => Φ (fun i : Fin (k + j) =>
    if h : (i : ℕ) < k then z ⟨i, h⟩
    else y ⟨(i : ℕ) - k, by omega⟩)

@[simp] lemma bfL_apply {k j : ℕ} (Φ : XN (k + j) → ℝ) (y : XN j) (z : XN k) :
    bfL Φ y z = Φ (fun i : Fin (k + j) =>
      if h : (i : ℕ) < k then z ⟨i, h⟩ else y ⟨(i : ℕ) - k, by omega⟩) := rfl

@[simp] lemma bfR_apply {k j : ℕ} (Φ : XN (k + j) → ℝ) (z : XN k) (y : XN j) :
    bfR Φ z y = Φ (fun i : Fin (k + j) =>
      if h : (i : ℕ) < k then z ⟨i, h⟩ else y ⟨(i : ℕ) - k, by omega⟩) := rfl

/-- `bfL` and `bfR` agree on the common configuration. -/
lemma bfL_bfR {k j : ℕ} (Φ : XN (k + j) → ℝ) (y : XN j) (z : XN k) :
    bfL Φ y z = bfR Φ z y := rfl

end Work.BoseFixR
