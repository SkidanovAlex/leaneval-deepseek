/-
# From the probabilistic core to `SparseGraphStatement`

`Submission/Deep/NCP.lean` isolates the *probabilistic half* of the proof of
`SparseGraphStatement` as the proposition `ErdosFaberLovaszConjecture.NCPCoreStatement`: a
polynomial threshold `Δ₀ δ`, a constant `c ≥ 1/100`, and, for every `δ`-sparse graph of maximum
degree at most `Δ ≥ Δ₀ δ`, a number of colours `k ≤ (1-cδ)(Δ+1)` and a partial proper
`k`-colouring `ψ` with `Dist(u) + d(u) < Col(u) + k` at every vertex.  The deterministic
extension step `ErdosFaberLovaszConjecture.sparseGraphStatement_of_ncp` already turns that into
`SparseGraphStatement`.

This module proves that `NCPCoreStatement` follows from the probabilistic core `NCPCore` of
`Submission/Work/Deep/Sparse/Assembly.lean` (which is what
`Submission/Work/Deep/Sparse/ncp_core` establishes), and hence so does `SparseGraphStatement`.
-/
import Submission.Deep.NCP
import Submission.Work.Deep.Sparse.Assembly
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

/-- The paper's `Col(u)`, computed from the partial colouring, agrees with
`colCount` of `Submission/Deep/NCP.lean`. -/
lemma colCount_of_partial (φ : PartialColoring G k) (u : V) :
    ErdosFaberLovaszConjecture.colCount G φ.col u = φ.numColored u := by
  rw [ErdosFaberLovaszConjecture.colCount]
  exact φ.coloredNbrs_card u

/-- The paper's `Dist(u)`, computed from the partial colouring, agrees with
`distCount` of `Submission/Deep/NCP.lean`. -/
lemma distCount_of_partial (φ : PartialColoring G k) (u : V) :
    ErdosFaberLovaszConjecture.distCount G φ.col u = φ.numDistinct u := by
  rw [ErdosFaberLovaszConjecture.distCount, PartialColoring.numDistinct,
    PartialColoring.distinctColors]
  refine congrArg Finset.card (Finset.filter_congr fun c _ => ?_)
  constructor
  · rintro ⟨v, hv, hvc⟩
    intro hzero
    rw [SimpleGraph.mem_neighborFinset] at hv
    exact (PartialColoring.colCount_eq_zero_iff φ).mp hzero v hv hvc
  · intro hne
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    exact hne ((PartialColoring.colCount_eq_zero_iff φ).mpr fun v hv hvc =>
      hcon v ((SimpleGraph.mem_neighborFinset G u v).mpr hv) hvc)

/-- **The probabilistic core implies the interface `NCPCoreStatement`.** -/
theorem ncpCoreStatement_of_ncpCore (h : NCPCore) :
    ErdosFaberLovaszConjecture.NCPCoreStatement := by
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
    set r : ℝ := (1 - δ / 100) * (Δ + 1) with hr
    have hrpos : 0 < r := by
      have h1 : δ / 100 < 1 := by linarith
      have h2 : (0 : ℝ) < 1 - δ / 100 := by linarith
      have h3 : (0 : ℝ) < Δ + 1 := by
        have : (0 : ℝ) < (10 : ℝ) ^ 24 / δ ^ 8 + 2 := by positivity
        linarith
      exact mul_pos h2 h3
    refine ⟨⌊r⌋₊, ?_, ?_⟩
    · have hle := Nat.floor_le (le_of_lt hrpos)
      have hEq : (1 - (1 / 100) * δ) * (Δ + 1) = r := by rw [hr]; ring
      rw [hEq]
      exact hle
    · obtain ⟨φ, hφ⟩ : ∃ φ : PartialColoring G ⌊r⌋₊,
          ∀ v : V, (G.degree v : ℝ) + 1 - ⌊r⌋₊
            ≤ (φ.numColored v : ℝ) - (φ.numDistinct v : ℝ) :=
        h V G hδ0 hδ1 (by linarith [hΔ]) hdeg hsp
          (by have := Nat.lt_floor_add_one r; linarith)
          (by have := Nat.floor_le (le_of_lt hrpos); linarith)
      refine ⟨φ.col, φ.isProper, fun u => ?_⟩
      have hZ : (G.degree u : ℤ) + 1 - (⌊r⌋₊ : ℤ)
          ≤ (φ.numColored u : ℤ) - (φ.numDistinct u : ℤ) := by
        have hcast : (((G.degree u : ℤ) + 1 - (⌊r⌋₊ : ℤ) : ℤ) : ℝ)
            ≤ (((φ.numColored u : ℤ) - (φ.numDistinct u : ℤ) : ℤ) : ℝ) := by
          push_cast
          exact hφ u
        exact_mod_cast hcast
      have hnat : φ.numDistinct u + G.degree u < φ.numColored u + ⌊r⌋₊ := by omega
      rw [colCount_of_partial φ u, distCount_of_partial φ u]
      exact hnat

/-- **`SparseGraphStatement` from the probabilistic core**, through the interface of
`Submission/Deep/NCP.lean`. -/
theorem sparseGraphStatement_of_ncpCore (h : NCPCore) :
    ErdosFaberLovaszConjecture.SparseGraphStatement :=
  ErdosFaberLovaszConjecture.sparseGraphStatement_of_ncp (ncpCoreStatement_of_ncpCore h)

end Work.Deep.Sparse
