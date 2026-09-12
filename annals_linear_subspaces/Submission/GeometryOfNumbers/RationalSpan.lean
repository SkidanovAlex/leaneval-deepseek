import Mathlib
import ChallengeDeps

/-!
# Rationality of subspaces spanned by integer vectors (dictionary fact)

For the Theorem-9-model assembly (`Work/ModelStar`) the planes produced from flow-lattice
vectors are `V = span ℝ (range m)` of the **integer preimage** family `m : Fin k → ℤᵈ`.
This module records the dictionary fact that such `V` is rational in the challenge's
sense (`IsRational V = IsZLattice ℝ (intPointsSubspace V)`):

`isRational_span_of_mem_intPoints` — if every `m i` is an integer point of `ℤᵈ`, then
`span ℝ (range m)` is rational.  Remarkably no linear-independence hypothesis is needed:
with the challenge's `IsRational` definition the only propositional content of
`IsZLattice ℝ (V ∩ ℤᵈ)` is the `span_top` field (its `DiscreteTopology` instance is free
for every `V`, as the comap of the discrete `ℤᵈ`), and `V ∩ ℤᵈ` ℝ-spans `V` as soon as
`V` has an integer spanning family.

Proof: lift `m` to the family `mv i = ⟨m i, _⟩ : V`; each `mv i` lies in
`intPointsSubspace V = ZLattice.comap ℝ ℤᵈ V.subtype` (unfold `ZLattice.comap`, membership
in a comap, value `V.subtype (mv i) = m i ∈ ℤᵈ`); every `x : V` expands over `range m`
(`Submodule.mem_span_range_iff_exists_fun`), hence lies in the ℝ-span of the integer
points of `V` (`span_mono` from `range mv ⊆ ↑(intPointsSubspace V)`), giving
`span_top = ⊤`; the `IsZLattice` structure is assembled from that field (discreteness by
the global instance).

Problem-side code (`ChallengeDeps` definitions only besides Mathlib).
-/

noncomputable section
open Module exteriorPower InnerProductGeometry
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open LinearSubspaces

namespace Submission.RationalSpan

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The span of a family of integer points is a rational subspace (no independence needed:
the integer points of `V` already ℝ-span `V` when the spanning family is integer). -/
lemma isRational_span_of_mem_intPoints {k : ℕ} (m : Fin k → ℝᵈ)
    (hmem : ∀ i, m i ∈ intPoints (d := d)) :
    IsRational (Submodule.span ℝ (Set.range m)) := by
  classical
  let V : Submodule ℝ ℝᵈ := Submodule.span ℝ (Set.range m)
  change IsZLattice ℝ (intPointsSubspace (d := d) V)
  constructor
  -- span_top : span ℝ (↑(intPointsSubspace V) : Set V) = ⊤  (ambient V)
  apply le_antisymm
  · exact le_top
  · intro x hx_top
    -- x ∈ ⊤; show x ∈ span ℝ (carrier of intPointsSubspace V)
    have hxV : (x : ℝᵈ) ∈ Submodule.span ℝ (Set.range m) := by
      dsimp [V] at x
      exact x.2
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := m)).mp hxV with ⟨c, hc⟩
    -- x as an ℝ-combination of the lifted vectors mv i : V
    let mv : Fin k → V := fun i => ⟨m i, by dsimp [V]; exact Submodule.subset_span ⟨i, rfl⟩⟩
    have hmv : ∀ i : Fin k, mv i ∈ intPointsSubspace (d := d) V := by
      intro i
      dsimp [mv, intPointsSubspace, ZLattice.comap]
      rw [Submodule.mem_comap]
      simpa using hmem i
    have hx_eq : (x : V) = ∑ i : Fin k, c i • mv i := by
      apply Subtype.ext
      have hval : (∑ i : Fin k, c i • mv i : V).1 = ∑ i : Fin k, c i • m i := by
        simp [mv]
      calc
        (x : ℝᵈ) = ∑ i : Fin k, c i • m i := hc.symm
        _ = (∑ i : Fin k, c i • mv i : V).1 := by rw [hval]
    have hx_in_span_mv : (x : V) ∈ Submodule.span ℝ (Set.range mv) := by
      rw [hx_eq]
      exact Submodule.sum_mem _ (fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hsub : Set.range mv ⊆ (intPointsSubspace (d := d) V : Set V) := by
      intro y hy
      rcases hy with ⟨i, rfl⟩
      exact hmv i
    exact (Submodule.span_mono (s := Set.range mv)
      (t := (intPointsSubspace (d := d) V : Set V)) hsub) hx_in_span_mv

end Submission.RationalSpan
