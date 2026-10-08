/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.PSTAB.QuadPairAux

set_option autoImplicit false

/-!
# `Work.PSTAB.FactorRep` — the representation on a simple factor

Given a `ρ`-invariant submodule `W ≤ U`, the representation `ρ` induces a representation on the
quotient `U ⧸ W` (`Representation.quotient` of the subrepresentation on `U`).  If `W` is a
*maximal* proper invariant submodule of `U`, the induced representation is irreducible, it
preserves the quadratic condition, and its kernel on `x` is detected by the condition
`ρ x v - v ∈ W` (`v ∈ U`).

This is the "replace `L` by its image on a composition factor" step of the reduction of
`Work.PSTAB.QuadPairSection` to the irreducible case `Work.PSTAB.QuadPairIrrProp`.
-/

namespace Work.PSTAB

variable {L : Type*} [Group L] {p : ℕ} [Fact p.Prime] {V : Type*}
  [AddCommGroup V] [Module (ZMod p) V] [Finite V]

theorem FactorRep (ρ : Representation (ZMod p) L V)
    {U W : Submodule (ZMod p) V} (hU : RepInv ρ U) (hW : RepInv ρ W) (hWU : W ≤ U)
    (hmax : ∀ S : Submodule (ZMod p) V, RepInv ρ S → W ≤ S → S ≤ U → S = W ∨ S = U)
    (x : L) (hx : ((ρ x : Module.End (ZMod p) V) - 1) ^ 2 = 0) :
    ∃ ρq : Representation (ZMod p) L (↥U ⧸ (W.comap U.subtype)),
      (∀ (S : Submodule (ZMod p) (↥U ⧸ (W.comap U.subtype))),
          (∀ g : L, ∀ v ∈ S, ρq g v ∈ S) → S = ⊥ ∨ S = ⊤) ∧
      (((ρq x : Module.End (ZMod p) (↥U ⧸ (W.comap U.subtype))) - 1) ^ 2 = 0) ∧
      (ρq x = 1 ↔ ∀ v ∈ U, ρ x v - v ∈ W) := by
  classical
  have hU' : ∀ g : L, U ≤ U.comap (ρ g) := fun g v hv => hU g v hv
  let W' : Submodule (ZMod p) ↥U := W.comap U.subtype
  let ρs : Representation (ZMod p) L ↥U := ρ.subrepresentation U hU'
  have hsub : ∀ g : L, W' ≤ W'.comap (ρs g) := by
    intro g u hu
    have hu' : (u : V) ∈ W := hu
    show (ρ g) (u : V) ∈ W
    exact hW g (u : V) hu'
  let ρq : Representation (ZMod p) L (↥U ⧸ W') := ρs.quotient W' hsub
  -- the basic computation on representatives
  have hqx : ∀ (g : L) (u : ↥U), ρq g (Submodule.mkQ W' u) = Submodule.mkQ W' (ρs g u) := by
    intro g u
    show (Submodule.mapQ W' W' (ρs g) (hsub g)) (Submodule.mkQ W' u) = Submodule.mkQ W' (ρs g u)
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply]
  have hkey : ∀ w : ↥U, ((ρs x w : ↥U) : V) = (ρ x) (w : V) := fun _ => rfl
  have hqsub : ∀ (g : L) (u : ↥U),
      (ρq g - 1) (Submodule.mkQ W' u) = Submodule.mkQ W' (ρs g u - u) := by
    intro g u
    rw [LinearMap.sub_apply, Module.End.one_apply, hqx g u, ← map_sub]
  -- `ρ x - 1` squares to zero, in explicit form on vectors
  have hx' : ∀ v : V, (ρ x : Module.End (ZMod p) V) ((ρ x) v - v) - ((ρ x) v - v) = 0 := by
    intro v
    have h0 := congrArg (fun φ : Module.End (ZMod p) V => φ v) hx
    rw [LinearMap.zero_apply] at h0
    rwa [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.sub_apply, Module.End.one_apply] at h0
  refine ⟨ρq, ?_, ?_, ?_⟩
  · -- irreducibility of `U ⧸ W` for `L`
    intro S hS
    let S₁ : Submodule (ZMod p) ↥U := S.comap (Submodule.mkQ W')
    let S₂ : Submodule (ZMod p) V := S₁.map U.subtype
    have hW'S₁ : W' ≤ S₁ := by
      intro u hu
      have h0 : Submodule.mkQ W' u = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hu
      show Submodule.mkQ W' u ∈ S
      rw [h0]
      exact S.zero_mem
    have hmap : S₁.map (Submodule.mkQ W') = S :=
      Submodule.map_comap_eq_self (f := Submodule.mkQ W') (q := S) (by simp)
    have hS₂inv : RepInv ρ S₂ := by
      intro g v hv
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
      have huS : Submodule.mkQ W' u ∈ S := hu
      have hmem : Submodule.mkQ W' (ρs g u) ∈ S := by
        rw [← hqx g u]
        exact hS g (Submodule.mkQ W' u) huS
      refine Submodule.mem_map.mpr ⟨ρs g u, hmem, ?_⟩
      rfl
    have hW_S₂ : W ≤ S₂ := by
      intro v hv
      refine Submodule.mem_map.mpr ⟨⟨v, hWU hv⟩, ?_, rfl⟩
      exact hW'S₁ (show (⟨v, hWU hv⟩ : ↥U) ∈ W' from hv)
    have hS₂_U : S₂ ≤ U := by
      intro v hv
      obtain ⟨u, _, rfl⟩ := Submodule.mem_map.mp hv
      exact u.2
    rcases hmax S₂ hS₂inv hW_S₂ hS₂_U with hS₂W | hS₂U
    · left
      have hS₁eq : S₁ = W' := by
        refine le_antisymm ?_ hW'S₁
        intro u hu
        have hmem : U.subtype u ∈ S₂ := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
        rw [hS₂W] at hmem
        exact hmem
      rw [← hmap, hS₁eq, Submodule.mkQ_map_self]
    · right
      have hS₁top : S₁ = ⊤ := by
        refine top_le_iff.mp (fun u _ => ?_)
        have hmem : U.subtype u ∈ S₂ := by rw [hS₂U]; exact u.2
        obtain ⟨u', hu', heq⟩ := Submodule.mem_map.mp hmem
        have huu : u' = u := Subtype.ext heq
        rwa [← huu]
      rw [← hmap, hS₁top, Submodule.map_top, Submodule.range_mkQ]
  · -- `(ρq x - 1)^2 = 0`
    rw [pow_two]
    apply Submodule.quot_hom_ext
    intro u
    rw [← Submodule.mkQ_apply]
    rw [Module.End.mul_apply, hqsub x, hqsub x, LinearMap.zero_apply]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hV : ((ρs x (ρs x u - u) - (ρs x u - u) : ↥U) : V) ∈ W := by
      rw [Submodule.coe_sub, hkey (ρs x u - u), Submodule.coe_sub, hkey u]
      rw [hx' (u : V)]
      exact W.zero_mem
    exact hV
  · -- the kernel of `x` on the factor
    constructor
    · intro h1 v hv
      have h2 : Submodule.mkQ W' (ρs x ⟨v, hv⟩) = Submodule.mkQ W' ⟨v, hv⟩ := by
        rw [← hqx x ⟨v, hv⟩, h1, Module.End.one_apply]
      have h3 : ρs x ⟨v, hv⟩ - ⟨v, hv⟩ ∈ W' := by
        have h4 : Submodule.mkQ W' (ρs x ⟨v, hv⟩ - ⟨v, hv⟩) = 0 := by
          rw [map_sub, h2, sub_self]
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h4
      have h5 : ((ρs x ⟨v, hv⟩ - ⟨v, hv⟩ : ↥U) : V) ∈ W := h3
      rw [Submodule.coe_sub, hkey ⟨v, hv⟩] at h5
      simpa using h5
    · intro h2
      apply Submodule.quot_hom_ext
      intro u
      rw [Module.End.one_apply, ← Submodule.mkQ_apply]
      rw [hqx x u, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have hmem : ((ρs x u - u : ↥U) : V) ∈ W := by
        rw [Submodule.coe_sub, hkey u]
        exact h2 (u : V) u.2
      exact hmem

end Work.PSTAB
