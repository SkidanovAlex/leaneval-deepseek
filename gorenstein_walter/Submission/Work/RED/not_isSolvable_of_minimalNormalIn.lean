import Mathlib
import Submission.Work.RED.Basic
import Submission.Work.RED.CharSimpleNotSolvable

/-!
# `not_isSolvable_of_minimalNormalIn`

A minimal normal subgroup of a group that is nonabelian is not solvable: such a subgroup is
*characteristically simple*, and a characteristically simple nonabelian group is not solvable
(`Work.RED.CharSimpleNotSolvable`).

Here `K` is a minimal normal subgroup of `N` inside an ambient group `G`
(`Work.RED.GW2.IsMinimalNormalIn N K`, i.e. `K.subgroupOf N` is a minimal normal subgroup of
`↥N`), and `N` is itself a minimal normal subgroup of `G`.

The only structure-theoretic input used is `Work.RED.GW2.MinimalNormalFactsProp.char_normal`
(a characteristic subgroup of `K` is normal in `N`, since `K ⊴ N`) together with the
minimality of `K` among normal subgroups of `N` contained in it.
-/

namespace Work.RED

/-- A subgroup of `↥K` is the `subgroupOf K` of its image in `G` under `K.subtype`. -/
private theorem map_subtype_subgroupOf' {G : Type} [Group G] (K : Subgroup G)
    (C : Subgroup ↥K) : (C.map K.subtype).subgroupOf K = C := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, hlx⟩
    have hlx' : l = x := Subtype.ext hlx
    rwa [← hlx']
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem not_isSolvable_of_minimalNormalIn
    (hmin : Work.RED.GW2.MinimalNormalFactsProp)
    {G : Type} [Group G] [Finite G] {N K : Subgroup G} (hN : Work.RED.GW2.IsMinimalNormal N)
    (hK : Work.RED.GW2.IsMinimalNormalIn N K) (hKnab : ¬ IsMulCommutative K) :
    ¬ Group.IsSolvable ↥K := by
  -- It suffices to show that `↥K` is characteristically simple.
  refine CharSimpleNotSolvable ↥K ?_ hKnab
  intro C hC
  have hKleN : K ≤ N := hK.le
  set Cg : Subgroup G := C.map K.subtype with hCg
  have hle : Cg ≤ K := by rw [hCg]; exact Subgroup.map_subtype_le C
  have hsub : Cg.subgroupOf K = C := by
    rw [hCg]; exact map_subtype_subgroupOf' K C
  -- `Cg` is characteristic in `K`, hence normal in `N` (as `K ⊴ N`).
  have hcharCK : (Cg.subgroupOf K).Characteristic := by
    rw [hsub]; exact hC
  have hnormN : (Cg.subgroupOf N).Normal :=
    hmin.char_normal G N K Cg hN hle hKleN hK.normal hcharCK
  -- By minimality of `K` as a normal subgroup of `N`, `Cg` is `⊥` or `K`.
  by_cases hbot : Cg = ⊥
  · left
    rw [← hsub, hbot, Subgroup.bot_subgroupOf]
  · right
    have hCK : Cg = K := hK.minimal Cg hle hnormN hbot
    rw [← hsub, hCK, Subgroup.subgroupOf_self]

end Work.RED
