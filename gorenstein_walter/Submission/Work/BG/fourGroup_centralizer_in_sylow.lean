/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BG area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.GLUE.Defs
import Submission.Work.L2F.Dihedral.fourGroup_centralizer_dihedral

/-!
# Four-subgroups of a dihedral Sylow 2-subgroup are self-centralizing

This file proves `Work.BG.fourGroup_centralizer_in_sylow`: if `R` is a Sylow `2`-subgroup of a
group `G`, `φ : R ≃* DihedralGroup m` exhibits it as a dihedral group, and `W ≤ R` is a Klein
four-group, then `C_G(W) ∩ R = W`.

The mathematical content is entirely local to `R`: since `W ≤ R`, an element of `R` centralizes
`W` in `G` if and only if it centralizes `W` viewed as a subgroup `W.subgroupOf R` of `R`, so

`C_G(W) ∩ R = (C_R(W.subgroupOf R)).map R.subtype`.

Transporting along the isomorphism `φ` turns `C_R(W.subgroupOf R)` into the centralizer of the
four-group `W.map φ ≤ DihedralGroup m`, which is itself by the colleague-proved dihedral lemma
`Work.L2F.Dihedral.fourGroup_centralizer_dihedral`; transporting back gives `C_R(W) = W`, and
`(W.subgroupOf R).map R.subtype = W` (because `W ≤ R`) finishes the proof.

Note that `R` being a Sylow subgroup plays no role beyond providing the isomorphism `φ` to
`DihedralGroup m`: the statement is a pure statement about dihedral groups.
-/

namespace Work.BG

open Subgroup

/-! ## Two transport lemmas -/

/-- The centralizer of a subgroup commutes with restriction along an injective homomorphism:
`C_H(V.map φ) = φ '' C_G(V)` read as an equality of subgroups of `G` after `comap`. -/
private lemma centralizer_comap_eq_of_injective {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) (V : Subgroup G) :
    (Subgroup.centralizer (V.map φ : Set H)).comap φ = Subgroup.centralizer (V : Set G) := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx u hu
    apply hφ
    rw [map_mul, map_mul]
    exact hx (φ u) ⟨u, hu, rfl⟩
  · intro hx y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, hx u hu]

/-- A four-group (a subgroup of order `4` all of whose elements are involutions) is carried to a
four-group by an injective homomorphism. -/
private lemma isFourGroup_map_of_injective {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) {V : Subgroup G} (hV : Work.L2F.IsFourGroup V) :
    Work.L2F.IsFourGroup (V.map φ) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hφ, hV.1]
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_pow, hV.2 u hu, map_one]

/-! ## The main result -/

/-- **A four-subgroup of a dihedral Sylow `2`-subgroup is self-centralizing in that Sylow.**
If `R` is a Sylow `2`-subgroup of `G` isomorphic to `DihedralGroup m` and `W ≤ R` is a Klein
four-group, then `C_G(W) ∩ R = W`. -/
theorem fourGroup_centralizer_in_sylow {G : Type*} [Group G] (R : Sylow 2 G) {m : ℕ}
    (φ : ↥(R : Subgroup G) ≃* DihedralGroup m) {W : Subgroup G} (hWR : W ≤ (R : Subgroup G))
    (hW : Work.GW2.IsFourGroup W) :
    Subgroup.centralizer (W : Set G) ⊓ (R : Subgroup G) = W := by
  -- View `W` inside `R` and map it into `DihedralGroup m`; the result is again a four-group.
  have hV4 : Work.L2F.IsFourGroup
      ((W.subgroupOf (R : Subgroup G)).map (φ : ↥(R : Subgroup G) →* DihedralGroup m)) := by
    refine isFourGroup_map_of_injective (φ : ↥(R : Subgroup G) →* DihedralGroup m)
      φ.injective ?_
    refine ⟨?_, ?_⟩
    · -- `|W.subgroupOf R| = |W| = 4`
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWR).toEquiv, hW.1]
    · -- every element of `W.subgroupOf R` is an involution
      intro v hv
      have hvG : (v : G) ∈ W := hv
      apply Subtype.ext
      simpa using hW.2 (v : G) hvG
  -- In a dihedral group a four-subgroup is self-centralizing.
  have hdih : Subgroup.centralizer
      (((W.subgroupOf (R : Subgroup G)).map (φ : ↥(R : Subgroup G) →* DihedralGroup m)) :
        Set (DihedralGroup m))
      = (W.subgroupOf (R : Subgroup G)).map (φ : ↥(R : Subgroup G) →* DihedralGroup m) :=
    Work.L2F.Dihedral.fourGroup_centralizer_dihedral _ hV4
  -- Transport back along `φ`: inside `R` the four-group is self-centralizing.
  have hC2 : Subgroup.centralizer ((W.subgroupOf (R : Subgroup G)) : Set ↥(R : Subgroup G))
      = W.subgroupOf (R : Subgroup G) := by
    have h := centralizer_comap_eq_of_injective (φ : ↥(R : Subgroup G) →* DihedralGroup m)
      φ.injective (W.subgroupOf (R : Subgroup G))
    rw [hdih, Subgroup.comap_map_eq_self_of_injective φ.injective] at h
    exact h.symm
  -- Centralizing `W` in `G` and then restricting to `R` is centralizing `W.subgroupOf R` in `R`.
  have hC1 : (Subgroup.centralizer (W : Set G)).subgroupOf (R : Subgroup G)
      = Subgroup.centralizer ((W.subgroupOf (R : Subgroup G)) : Set ↥(R : Subgroup G)) := by
    have h := centralizer_comap_eq_of_injective (R : Subgroup G).subtype
      (R : Subgroup G).subtype_injective (W.subgroupOf (R : Subgroup G))
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWR] at h
    exact h
  calc Subgroup.centralizer (W : Set G) ⊓ (R : Subgroup G)
      = ((Subgroup.centralizer (W : Set G)).subgroupOf (R : Subgroup G)).map
          (R : Subgroup G).subtype := (Subgroup.subgroupOf_map_subtype _ _).symm
    _ = (Subgroup.centralizer ((W.subgroupOf (R : Subgroup G)) : Set ↥(R : Subgroup G))).map
          (R : Subgroup G).subtype := by rw [hC1]
    _ = (W.subgroupOf (R : Subgroup G)).map (R : Subgroup G).subtype := by rw [hC2]
    _ = W := Subgroup.map_subgroupOf_eq_of_le hWR

end Work.BG
