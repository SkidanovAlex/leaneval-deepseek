import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Counting the hyperplanes containing a given subspace over `𝔽₂`

For a finite-dimensional `𝔽₂`-vector space `V` and a subspace `X ≤ V`, the number of
codimension-one subspaces `H` with `X ≤ H` is `2 ^ (finrank V - finrank X) - 1`.

The proof is the standard duality argument.  For a vector space `V` the map
`H ↦ H.dualAnnihilator` is an order-reversing bijection between the subspaces of `V` and
those of the dual `Module.Dual (ZMod 2) V`; it sends the codimension-one subspaces of `V`
onto the one-dimensional subspaces of the dual and restricts to a bijection

`{H : Submodule (ZMod 2) V // X ≤ H ∧ finrank H + 1 = finrank V} ≃
 {L ≤ X.dualAnnihilator // finrank L = 1}`.

The one-dimensional subspaces of a space of dimension `d` are the points of its
projectivisation, of which there are `Nat.card - 1 = 2 ^ d - 1`, and
`finrank X.dualAnnihilator = finrank V - finrank X`.
-/

set_option autoImplicit false

namespace Work.Hering.Wagner

open Module Submodule

/-! ## A correspondence of subspaces of a submodule

The submodules of `↥p` correspond to the submodules of the ambient space that are contained
in `p`, preserving both the dimension and the condition of being one-dimensional. -/

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

/-- Subspaces of a submodule `↥p` correspond to the subspaces of the ambient space lying
in `p`; this correspondence preserves `finrank`. -/
noncomputable def submoduleLeOneEquivSubtype (p : Submodule K M) :
    {L : Submodule K M // L ≤ p ∧ Module.finrank K ↥L = 1} ≃
    {L' : Submodule K ↥p // Module.finrank K ↥L' = 1} where
  toFun L := ⟨L.1.comap p.subtype, by
      have h : (L.1.comap p.subtype).map p.subtype = L.1 := by
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr L.2.1]
      rw [← Submodule.finrank_map_subtype_eq p (L.1.comap p.subtype), h]
      exact L.2.2⟩
  invFun L' := ⟨L'.1.map p.subtype, ⟨Submodule.map_subtype_le p L'.1, by
      rw [Submodule.finrank_map_subtype_eq]
      exact L'.2⟩⟩
  left_inv L := by
      apply Subtype.ext
      show Submodule.map p.subtype (Submodule.comap p.subtype L.1) = L.1
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr L.2.1]
  right_inv L' := by
      apply Subtype.ext
      show Submodule.comap p.subtype (Submodule.map p.subtype L'.1) = L'.1
      have hmap : Submodule.map p.subtype
            (Submodule.comap p.subtype (Submodule.map p.subtype L'.1))
          = Submodule.map p.subtype L'.1 := by
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr (Submodule.map_subtype_le p L'.1)]
      exact Submodule.map_injective_of_injective (Subtype.coe_injective) hmap

/-! ## The duality bijection -/

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The codimension-one subspaces of a finite-dimensional space `V` containing a subspace `X`
correspond to the one-dimensional subspaces of the annihilator `X.dualAnnihilator`, via the
annihilator / coannihilator duality. -/
noncomputable def hypEquivAnnihilatorLines [FiniteDimensional K V] (X : Submodule K V) :
    {H : Submodule K V // X ≤ H ∧ Module.finrank K ↥H + 1 = Module.finrank K V} ≃
    {L : Submodule K (Module.Dual K V) // L ≤ X.dualAnnihilator ∧ Module.finrank K ↥L = 1} where
  toFun H := ⟨H.1.dualAnnihilator, by
      refine ⟨Submodule.dualAnnihilator_anti H.2.1, ?_⟩
      have h := Subspace.finrank_add_finrank_dualAnnihilator_eq H.1
      omega⟩
  invFun L := ⟨L.1.dualCoannihilator, by
      refine ⟨?_, ?_⟩
      · exact le_trans (Submodule.le_dualAnnihilator_dualCoannihilator X)
          (Submodule.dualCoannihilator_anti L.2.1)
      · have h := Subspace.finrank_add_finrank_dualCoannihilator_eq L.1
        omega⟩
  left_inv H := by
      apply Subtype.ext
      exact Subspace.dualAnnihilator_dualCoannihilator_eq (W := H.1)
  right_inv L := by
      apply Subtype.ext
      exact Subspace.dualCoannihilator_dualAnnihilator_eq (W := L.1)

/-! ## The count -/

theorem card_hyp_above {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (X : Submodule (ZMod 2) V) :
    Nat.card {H : Submodule (ZMod 2) V //
        X ≤ H ∧ Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) V}
      = 2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) X) - 1 := by
  classical
  -- `V` is finite, hence (over the finite field `𝔽₂`) finite-dimensional.
  have h1 : Nat.card {H : Submodule (ZMod 2) V //
        X ≤ H ∧ Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) V}
      = Nat.card {L : Submodule (ZMod 2) (Module.Dual (ZMod 2) V) //
          L ≤ X.dualAnnihilator ∧ Module.finrank (ZMod 2) ↥L = 1} :=
    Nat.card_congr (hypEquivAnnihilatorLines X)
  -- Move the condition `L ≤ X.dualAnnihilator` into the subtype.
  have h2 : Nat.card {L : Submodule (ZMod 2) (Module.Dual (ZMod 2) V) //
          L ≤ X.dualAnnihilator ∧ Module.finrank (ZMod 2) ↥L = 1}
      = Nat.card {L : Submodule (ZMod 2) ↥(X.dualAnnihilator) //
          Module.finrank (ZMod 2) ↥L = 1} :=
    Nat.card_congr (submoduleLeOneEquivSubtype X.dualAnnihilator)
  -- The dual of a finite space is finite.
  have hfinDual : Finite (Module.Dual (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) V => (f : V → ZMod 2))
      (fun _ _ h => LinearMap.ext (congrFun h))
  have hfinA : Finite ↥(X.dualAnnihilator) :=
    Finite.of_injective (fun x : ↥(X.dualAnnihilator) => (x : Module.Dual (ZMod 2) V))
      Subtype.val_injective
  -- One-dimensional subspaces are the points of the projectivisation.
  have h3 : Nat.card {L : Submodule (ZMod 2) ↥(X.dualAnnihilator) //
          Module.finrank (ZMod 2) ↥L = 1}
      = Nat.card (Projectivization (ZMod 2) ↥(X.dualAnnihilator)) :=
    (Nat.card_congr (Projectivization.equivSubmodule (ZMod 2) ↥(X.dualAnnihilator))).symm
  have h4 : Nat.card (Projectivization (ZMod 2) ↥(X.dualAnnihilator))
      = Nat.card ↥(X.dualAnnihilator) - 1 := by
    have h := Projectivization.card' (ZMod 2) ↥(X.dualAnnihilator)
    rw [Nat.card_zmod] at h
    omega
  have h5 : Nat.card ↥(X.dualAnnihilator) = 2 ^ Module.finrank (ZMod 2) ↥(X.dualAnnihilator) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(X.dualAnnihilator))
    rw [Nat.card_zmod] at h
    exact h
  have h6 : Module.finrank (ZMod 2) ↥(X.dualAnnihilator)
      = Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) X := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq X
    omega
  rw [h1, h2, h3, h4, h5, h6]

end Work.Hering.Wagner
