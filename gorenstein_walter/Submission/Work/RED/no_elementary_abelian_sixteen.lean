import Mathlib
import Submission.Work.RED.Basic

/-!
# RED: no elementary abelian subgroup of order 16

A Sylow 2-subgroup `P` of `G` is isomorphic to `DihedralGroup n`, and dihedral groups
have 2-rank at most 2 (`DihedralFactsProp.elementary_abelian_card_le_four`).  Every
subgroup of order `16` is a 2-group, hence lies in a Sylow 2-subgroup; all Sylow
2-subgroups are isomorphic, so such a subgroup would embed into `DihedralGroup n` as an
elementary abelian subgroup of order `16`, contradicting the 2-rank bound.  This rules
out the configuration produced by `Work.RED.exists_sixteen_of_two_fourGroups` inside `G`.
-/

namespace Work.RED

open Subgroup

theorem no_elementary_abelian_sixteen (hdi : Work.RED.GW2.DihedralFactsProp)
    {G : Type*} [Group G] [Finite G] {n : ℕ} [NeZero n] {P : Sylow 2 G}
    (e : ↥(P : Subgroup G) ≃* DihedralGroup n) :
    ¬ ∃ W : Subgroup G, Nat.card W = 16 ∧ ∀ x ∈ W, x ^ 2 = 1 := by
  rintro ⟨W, hWcard, hWsq⟩
  -- `W` has order `16 = 2 ^ 4`, so it is a 2-group and lies in a Sylow 2-subgroup.
  have hWpg : IsPGroup 2 ↥W := by
    apply IsPGroup.of_card (n := 4)
    rw [hWcard]; norm_num
  obtain ⟨Q, hWQ⟩ := IsPGroup.exists_le_sylow hWpg
  -- The Sylow 2-subgroup `Q` is isomorphic to `DihedralGroup n`.
  let eQ : ↥Q ≃* DihedralGroup n := (Sylow.equiv Q P).trans e
  -- Embed `W` into `DihedralGroup n`.
  let f : ↥W →* DihedralGroup n := eQ.toMonoidHom.comp (Subgroup.inclusion hWQ)
  let E : Subgroup (DihedralGroup n) := (⊤ : Subgroup ↥W).map f
  have hfinj : Function.Injective f := eQ.injective.comp (Subgroup.inclusion_injective hWQ)
  have hcard : Nat.card E = 16 := by
    dsimp only [E]
    rw [Subgroup.card_map_of_injective hfinj]
    simp [hWcard]
  -- Every element of `W` is an involution, so the same holds in the image.
  have hsq' : ∀ w : ↥W, w ^ 2 = 1 := fun w => by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hWsq w w.2]
    rfl
  have hEsq : ∀ x ∈ E, x ^ 2 = 1 := by
    intro x hx
    simp only [E, Subgroup.mem_map, Subgroup.mem_top, true_and] at hx
    obtain ⟨w, rfl⟩ := hx
    rw [← map_pow, hsq' w, map_one]
  -- The 2-rank of `DihedralGroup n` is at most `4`.
  have h4 := hdi.elementary_abelian_card_le_four n E hEsq
  omega

end Work.RED
