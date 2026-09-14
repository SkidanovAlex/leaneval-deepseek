import Mathlib

open scoped Topology
set_option autoImplicit false

/-!
# (B-ii infra) first-countability of the matrix topology

`Matrix m n R` carries the product topology (its `TopologicalSpace` instance is literally the
Pi-topology of `m → n → R`), but typeclass search does not unfold `Matrix`, so the generic
Pi instances (metric / first-countable / …) do not fire on `Matrix`.  This module registers
the missing first-countability for the square real matrices `Matrix (Fin m) (Fin m) ℝ`
(finite product of the first-countable space `ℝ`), which makes the neighbourhood filters
`𝓝 A₀` countably generated — the hypothesis of the filter-version dominated convergence
theorem used in P3.2's topological γ-continuity.
-/

noncomputable section

/-- The space of real `m × m` matrices (product topology) is first countable: it is (up to
definitional equality) the finite function space `Fin m → Fin m → ℝ`, where the generic Pi
first-countability instance applies. -/
instance instFirstCountableTopologyMatrix (m : ℕ) :
    FirstCountableTopology (Matrix (Fin m) (Fin m) ℝ) := by
  change FirstCountableTopology ((Fin m) → (Fin m) → ℝ)
  infer_instance
