import Mathlib
import Submission.Work.BW.closedSubAux
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A primitive system spanning the saturation of the character lattice

For an arbitrary set `K ⊆ ℂ^N` (typical case: a subgroup of the torus `G_m^N`), this file
produces a matrix `M : Fin ρ → Fin N → ℤ` whose rows form a *primitive system* and whose
`ℤ`-span is exactly the saturation `satLat (charLat K)` of the character lattice of `K`.

The mathematics is the structure theory of lattices: `satLat (charLat K)` is a pure
(saturated) submodule of the free `ℤ`-module `ℤ^N`, hence it is free of rank `ρ ≤ N`; a basis
of it has `ℚ`-linearly independent rows (its `ℤ`-independence upgrades to `ℚ`-independence)
and its `ℤ`-span is saturated by construction. The basis is produced by
`Submodule.basisOfPid` applied to the standard basis of `ℤ^N`, and the `ℚ`-independence of its
rows by `linearIndependent_algebraMap_comp_iff` (flatness of `ℚ` over `ℤ`).
-/

open Module

namespace Work.BW

/-- The rows of a basis `B` of a submodule `L ≤ ℤ^N`, viewed in the ambient `ℤ^N`, span `L`. -/
private theorem span_range_coe_basis {N ρ : ℕ} (L : Submodule ℤ (Fin N → ℤ))
    (B : Basis (Fin ρ) ℤ L) :
    Submodule.span ℤ (Set.range (fun j : Fin ρ => ((B j : L) : Fin N → ℤ))) = L := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (B j).2
  · intro z hz
    have hrepr : ∑ i, B.repr ⟨z, hz⟩ i • ((B i : L) : Fin N → ℤ) = z := by
      have h := congrArg (Submodule.subtype L) (B.sum_repr ⟨z, hz⟩)
      simp only [map_sum, map_smul] at h
      simpa using h
    rw [← hrepr]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-- A submodule of `ℤ^N` whose free basis is indexed by `Fin ρ` has `ρ ≤ N`. -/
private theorem card_basis_le {N ρ : ℕ} (L : Submodule ℤ (Fin N → ℤ)) (B : Basis (Fin ρ) ℤ L) :
    ρ ≤ N := by
  have hfin : Module.Finite ℤ (Fin N → ℤ) := inferInstance
  have h1 : finrank ℤ L = ρ := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  have h2 : finrank ℤ L ≤ finrank ℤ (Fin N → ℤ) := Submodule.finrank_le L
  rw [h1, Module.finrank_fin_fun] at h2
  exact h2

theorem torus_basis_satLat {N : ℕ} (K : Set (Fin N → ℂ)) :
    ∃ (ρ : ℕ) (M : Fin ρ → Fin N → ℤ), ρ ≤ N ∧ PrimSys M ∧
      Submodule.span ℤ (Set.range M) = satLat (charLat K) := by
  classical
  let L : Submodule ℤ (Fin N → ℤ) := satLat (charLat K)
  let b : Basis (Fin N) ℤ (Fin N → ℤ) := Pi.basisFun ℤ (Fin N)
  let s := Submodule.basisOfPid b L
  let Ma : Fin s.1 → Fin N → ℤ := fun j => ((s.2 j : L) : Fin N → ℤ)
  have hspan : Submodule.span ℤ (Set.range Ma) = L := span_range_coe_basis L s.2
  have hρ : s.1 ≤ N := card_basis_le L s.2
  -- The rows are `ℤ`-linearly independent, being the image of a basis of `L`.
  have hvZ : LinearIndependent ℤ Ma := by
    rw [linearIndependent_iff']
    intro t c hc
    have hb := (s.2).linearIndependent
    rw [linearIndependent_iff'] at hb
    refine hb t c ?_
    apply Subtype.coe_injective
    simpa [Ma, Submodule.coe_sum, Submodule.coe_smul] using hc
  -- ... hence `ℚ`-linearly independent after casting (`ℚ` is flat over `ℤ`).
  have hq : LinearIndependent ℚ (fun j i => ((Ma j i : ℤ) : ℚ)) :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ) (v := Ma)).mpr hvZ
  refine ⟨s.1, Ma, hρ, ⟨hq, ?_⟩, ?_⟩
  · -- Saturation: `L = satLat (charLat K)` is pure.
    intro x m hm hmx
    rw [hspan] at hmx ⊢
    exact satLat_sat (charLat K) hm hmx
  · rw [hspan]

end Work.BW
