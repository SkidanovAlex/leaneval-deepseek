import Mathlib
import Submission.Work.CORE4.Defs

open scoped Pointwise

namespace Work.CORE4

/-- **Sylow conjugacy inside `E`.** If `S` is a Sylow `p`-subgroup of `G` lying in `E`, and
`V ≤ E` is a `p`-subgroup of `E`, then some `E`-conjugate of `V` lies in `S`.

Proof. `S` is also a Sylow `p`-subgroup of `E` (`Sylow.subtype`), so it suffices to conjugate
`V` into it there: `V` lies in some Sylow `Q` of `E` (`IsPGroup.exists_le_sylow`), and Sylow's
second theorem inside the finite group `E` conjugates `Q` to `S`. Mapping back along
`E.subtype` turns the `E`-conjugacy into `Work.GW2.conjSub`. -/
theorem exists_conj_le_of_le_sylow {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E : Subgroup G} (S : Sylow p G) (hSE : (S : Subgroup G) ≤ E)
    {V : Subgroup G} (hVE : V ≤ E) (hV : IsPGroup p V) :
    ∃ e ∈ E, Work.GW2.conjSub e V ≤ (S : Subgroup G) := by
  -- `S` viewed as a Sylow `p`-subgroup of the subgroup `E`.
  let SE : Sylow p E := S.subtype hSE
  -- A Sylow `p`-subgroup of `E` containing `V` (as a subgroup of `E`).
  obtain ⟨Q, hVQ⟩ : ∃ Q : Sylow p E, V.subgroupOf E ≤ Q :=
    (hV.comap_subtype).exists_le_sylow
  -- Sylow's second theorem inside `E`: `Q` and `SE` are conjugate.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E Q SE
  refine ⟨(g : G), g.2, ?_⟩
  have hQ : MulAut.conj g • (Q : Subgroup E) = (SE : Subgroup E) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  have hle : MulAut.conj g • (V.subgroupOf E) ≤ (SE : Subgroup E) := by
    rw [← hQ]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hVQ
  have hmap : Subgroup.map E.subtype (MulAut.conj g • (V.subgroupOf E)) ≤
      Subgroup.map E.subtype (SE : Subgroup E) := Subgroup.map_mono hle
  have hL : Subgroup.map E.subtype (MulAut.conj g • (V.subgroupOf E)) =
      Work.GW2.conjSub (g : G) V := by
    rw [Subgroup.conj_smul_subgroupOf hVE g, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (Subgroup.conj_smul_le_of_le hVE g)]
    rfl
  have hR : Subgroup.map E.subtype (SE : Subgroup E) = (S : Subgroup G) := by
    show Subgroup.map E.subtype (S.subtype hSE : Subgroup E) = (S : Subgroup G)
    rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSE]
  rw [hL, hR] at hmap
  exact hmap

end Work.CORE4
