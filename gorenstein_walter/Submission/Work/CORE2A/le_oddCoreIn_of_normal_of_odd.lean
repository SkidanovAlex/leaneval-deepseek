import Mathlib
import Submission.Work.CORE2A.Defs

/-!
# Odd-order normal subgroups live in `O_{2'}`

`Work.GW2.oddCoreIn M = O_{2'}(↥M)`, the largest normal subgroup of odd order of `M`, viewed as a
subgroup of the ambient group `G` (as the image of `Work.GW2.oddCore ↥M` under `M.subtype`).

The lemma proved here is the *maximality* of that object, read in the ambient group: if
`X ≤ M` and `X` is normal in `M` (i.e. `X.subgroupOf M` is normal in `↥M`) and of odd order,
then `X ≤ O_{2'}(M)`.

The proof is a two-line reduction to the abstract group `↥M`:

* `X.subgroupOf M ≃* X` (`Subgroup.subgroupOfEquivOfLe hXM`), so `X.subgroupOf M` has odd order;
* in the abstract group `↥M`, the subgroup `X.subgroupOf M` is normal and of odd order, hence it
  lies in the `sSup` of `{N | N.Normal ∧ Odd (Nat.card N)}`; being normal, it survives the
  `normalCore` wrapper, `Subgroup.normal_le_normalCore`;
* pushing forward along `M.subtype` and using `Subgroup.map_subgroupOf_eq_of_le hXM` gives the
  claim.
-/

namespace Work.CORE2A

/-- **Maximality of `O_{2'}(M)` in the ambient group.** A subgroup `X ≤ M` of odd order that is
normal in `M` lies in `Work.GW2.oddCoreIn M`. -/
theorem le_oddCoreIn_of_normal_of_odd {G : Type} [Group G] [Finite G] {X M : Subgroup G} (hXM : X ≤ M) (hn : (X.subgroupOf M).Normal) (hodd : Odd (Nat.card X)) : X ≤ Work.GW2.oddCoreIn M := by
  -- `X.subgroupOf M` is a copy of `X`, so it too has odd order.
  have hcard : Nat.card (X.subgroupOf M) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
  have hodd' : Odd (Nat.card (X.subgroupOf M)) := hcard.symm ▸ hodd
  -- Inside `↥M`, the normal odd-order subgroup `X.subgroupOf M` lies in `O_{2'}(↥M)`.
  have hle : X.subgroupOf M ≤ Work.GW2.oddCore ↥M :=
    (Subgroup.normal_le_normalCore (N := X.subgroupOf M) (hN := hn)
      (H := sSup {N : Subgroup ↥M | N.Normal ∧ Odd (Nat.card N)})).mpr
      (le_sSup ⟨hn, hodd'⟩)
  -- Transport along `M.subtype`: `X.subgroupOf M` maps onto `X`.
  rw [← Subgroup.map_subgroupOf_eq_of_le hXM]
  simpa [Work.GW2.oddCoreIn] using Subgroup.map_mono (f := M.subtype) hle

end Work.CORE2A
