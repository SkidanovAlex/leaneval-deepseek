/-
# The naive colouring procedure: from the probabilistic core to `SparseGraphStatement`

This module isolates the *deterministic* assembly of the proof of
`ErdosFaberLovaszConjecture.SparseGraphStatement` (`Submission/Deep/Reed.lean`) from the
probabilistic core.

* `NCPCore` — the probabilistic content of the naive colouring procedure (Molloy–Reed
  Chapter 10, Bruhn–Joos, Bonamy–Perrett–Postle §3), stated exactly as the sibling module
  `Submission.Work.Deep.Sparse.ncp_core` proves it: for a graph of maximum degree at most `Δ`
  in which every neighbourhood spans at most `(1-δ)Δ²/2` edges and `Δ ≥ 10²⁴/δ⁸`, every colour
  count `k` in the window `(1-δ/100)(Δ+1) - 1 ≤ k ≤ (1-δ/100)(Δ+1)` admits a *partial* proper
  `k`-colouring with `Col(v) - Dist(v) ≥ d(v) + 1 - k` at every vertex.
* `sparseGraphStatement_of_core` — the extension proposition turns such a partial colouring
  into a genuine `k`-colouring, and the constants `c = 1/100`, `Δ₀ δ = 10²⁴/δ⁸ + 2` discharge
  `SparseGraphStatement`.
-/
import Submission.Deep.Reed
import Submission.Work.Deep.Sparse.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

/-- The probabilistic core of the naive colouring procedure, as proved in
`Submission.Work.Deep.Sparse.ncp_core`. -/
def NCPCore : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {δ Δ : ℝ}, 0 < δ → δ ≤ 1 → (10 : ℝ) ^ 24 / δ ^ 8 ≤ Δ →
    (G.maxDegree : ℝ) ≤ Δ →
    (∀ v : V, (ErdosFaberLovaszConjecture.nbrEdges G v : ℝ) ≤ (1 - δ) * Δ ^ 2 / 2) →
    ∀ {k : ℕ}, (1 - δ / 100) * (Δ + 1) - 1 ≤ (k : ℝ) →
      (k : ℝ) ≤ (1 - δ / 100) * (Δ + 1) →
    ∃ φ : PartialColoring G k,
      ∀ v : V, (G.degree v : ℝ) + 1 - k ≤ (φ.numColored v : ℝ) - (φ.numDistinct v : ℝ)

/-- **`SparseGraphStatement` from the probabilistic core.**  The extension proposition
(`PartialColoring.colorable_of_partial`) upgrades a good partial colouring to a genuine
colouring; the constants are `c = 1/100` and `Δ₀ δ = 10²⁴/δ⁸ + 2`. -/
theorem sparseGraphStatement_of_core (h : NCPCore) :
    ErdosFaberLovaszConjecture.SparseGraphStatement := by
  refine ⟨1 / 100, by norm_num, fun δ => (10 : ℝ) ^ 24 / δ ^ 8 + 2, ?_, ?_, ?_⟩
  · intro δ hδ0 hδ1
    positivity
  · refine ⟨(10 : ℝ) ^ 24 + 2, by positivity, 8, ?_⟩
    intro δ hδ0 hδ1
    have hδ8pos : (0 : ℝ) < δ ^ 8 := by positivity
    have hδ8 : δ ^ 8 ≤ 1 := pow_le_one₀ (le_of_lt hδ0) hδ1
    have h2 : (2 : ℝ) ≤ 2 / δ ^ 8 := by
      rw [le_div_iff₀ hδ8pos]
      simpa using hδ8
    rw [add_div]
    linarith
  · intro δ hδ0 hδ1 V _ _ G _ Δ hΔ hdeg hsp
    -- the colour count prescribed by the core
    set r : ℝ := (1 - δ / 100) * (Δ + 1) with hr
    have hrpos : 0 < r := by
      have h1 : δ / 100 < 1 := by linarith
      have h2 : (0 : ℝ) < 1 - δ / 100 := by linarith
      have h3 : (0 : ℝ) < Δ + 1 := by
        have : (0 : ℝ) < (10 : ℝ) ^ 24 / δ ^ 8 + 2 := by positivity
        linarith
      exact mul_pos h2 h3
    refine ⟨⌊r⌋₊, ?_, ?_⟩
    · -- the colour count lies below the allowed bound
      have hle := Nat.floor_le (le_of_lt hrpos)
      have hEq : (1 - (1 / 100) * δ) * (Δ + 1) = r := by rw [hr]; ring
      rw [hEq]
      exact hle
    · -- the probabilistic core supplies the partial colouring, and the extension proposition
      -- upgrades it to a genuine colouring
      obtain ⟨φ, hφ⟩ : ∃ φ : PartialColoring G ⌊r⌋₊,
          ∀ v : V, (G.degree v : ℝ) + 1 - ⌊r⌋₊
            ≤ (φ.numColored v : ℝ) - (φ.numDistinct v : ℝ) :=
        h V G hδ0 hδ1 (by linarith [hΔ]) hdeg hsp
          (by have := Nat.lt_floor_add_one r; linarith)
          (by have := Nat.floor_le (le_of_lt hrpos); linarith)
      have hZ : ∀ v : V, (G.degree v : ℤ) + 1 - (⌊r⌋₊ : ℤ)
          ≤ (φ.numColored v : ℤ) - (φ.numDistinct v : ℤ) := by
        intro v
        have hcast : (((G.degree v : ℤ) + 1 - (⌊r⌋₊ : ℤ) : ℤ) : ℝ)
            ≤ (((φ.numColored v : ℤ) - (φ.numDistinct v : ℤ) : ℤ) : ℝ) := by
          push_cast
          exact hφ v
        exact_mod_cast hcast
      exact PartialColoring.colorable_of_partial φ hZ

end Work.Deep.Sparse
