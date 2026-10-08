/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area FUS, `Work.FUS`)

# Proof of `Work.GW2.CentralizerSplitProp`

`C_G(t) = O(C_G(t)) · S` for `t` the central involution of a dihedral Sylow `2`-subgroup.

The mathematical input is `Work.FUS.centralizer_has_normal_two_complement`: Frobenius' normal
`p`-complement theorem (from the odd-order library, `OddOrder.Isaacs.Ch05`) applied to `C_G(t)`,
whose verification rests on `Work.FUS.odd_normalizer_centralizes` (the `N/C`-input in the dihedral
case). This file assembles the two: a complement `N` of the Sylow inside `C_G(t)` has odd order,
hence lies in `O(C_G(t))`, and `N ⊔ S = C_G(t)` pushes down to the stated identity.
-/
import Mathlib
import Submission.Work.FUS.Defs
import Submission.Work.FUS.centralizer_has_normal_two_complement

namespace Work.FUS

open Subgroup

/-- **`Work.GW2.CentralizerSplitProp`**: for `t` the central involution of a dihedral Sylow
`2`-subgroup `S`, `C_G(t) = O(C_G(t)) · S`. -/
theorem centralizerSplitProp : Work.GW2.CentralizerSplitProp := by
  intro G _inst _fin S n hn2 hiso t htS ht2 htc
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  have hSH : (S : Subgroup G) ≤ H := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      obtain rfl : y = t := Set.mem_singleton_iff.mp hy
      exact (htc x hx).symm)
  obtain ⟨N, hNnorm, hcomp⟩ := centralizer_has_normal_two_complement S n hn2 hiso t htS ht2 htc
  haveI : N.Normal := hNnorm
  let P : Sylow 2 ↥H := S.subtype hSH
  have hPcarrier : (P : Subgroup ↥H) = (S : Subgroup G).subgroupOf H :=
    Sylow.coe_subtype (P := S) (N := H) hSH
  have hcompP : N.IsComplement' (P : Subgroup ↥H) := hcomp P
  have hsup : N ⊔ (P : Subgroup ↥H) = ⊤ := hcompP.sup_eq_top
  -- `N` has odd order: its cardinality is the index of the Sylow `P`, which divides `|G : S|`
  have hNodd : Odd (Nat.card N) := by
    have hrel : (P : Subgroup ↥H).index = (S : Subgroup G).relIndex H := by
      rw [hPcarrier]
      rfl
    have hidx : (P : Subgroup ↥H).index = Nat.card N := hcompP.index_eq_card
    rw [hrel] at hidx
    rw [← hidx]
    have hmul : (S : Subgroup G).relIndex H * H.index = (S : Subgroup G).index :=
      Subgroup.relIndex_mul_index hSH
    have hSodd : Odd (S : Subgroup G).index := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact S.not_dvd_index
    rcases hSodd with ⟨m, hm⟩
    rcases Nat.even_or_odd ((S : Subgroup G).relIndex H) with hev | hodd
    · exfalso
      rw [even_iff_two_dvd] at hev
      have h2 : (2 : ℕ) ∣ (S : Subgroup G).relIndex H * H.index := dvd_mul_of_dvd_left hev _
      rw [hmul, hm] at h2
      omega
    · exact hodd
  -- hence `N ≤ O(H)`
  have hNle : N ≤ Work.GW2.oddCore ↥H :=
    Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hNnorm, hNodd⟩)
  have hPmap : (P : Subgroup ↥H).map H.subtype = (S : Subgroup G) := by
    rw [hPcarrier]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hSH hx⟩, hx, rfl⟩
  -- `N ⊔ P = ⊤` upgrades to `O(H) ⊔ P = ⊤`, and mapping back to `G` gives the statement
  have hmap_eq : Work.GW2.oddCoreIn H ⊔ (S : Subgroup G)
      = (Work.GW2.oddCore ↥H ⊔ (P : Subgroup ↥H)).map H.subtype := by
    simp only [Work.GW2.oddCoreIn]
    rw [Subgroup.map_sup (Work.GW2.oddCore ↥H) (P : Subgroup ↥H) H.subtype, hPmap]
  have hsup' : Work.GW2.oddCore ↥H ⊔ (P : Subgroup ↥H) = ⊤ := by
    refine le_antisymm le_top ?_
    calc (⊤ : Subgroup ↥H) = N ⊔ (P : Subgroup ↥H) := hsup.symm
      _ ≤ Work.GW2.oddCore ↥H ⊔ (P : Subgroup ↥H) := sup_le_sup_right hNle _
  have htop2 : (⊤ : Subgroup ↥H).map H.subtype = H := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hfinal : Work.GW2.oddCoreIn H ⊔ (S : Subgroup G) = H := by
    rw [hmap_eq, hsup', htop2]
  exact hfinal

end Work.FUS
