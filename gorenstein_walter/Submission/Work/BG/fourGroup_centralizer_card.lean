import Mathlib
import Submission.Work.GLUE.Defs
import Submission.Work.L2F.Dihedral.fourGroup_centralizer_dihedral
import Submission.Work.BG.fourGroup_centralizer_in_sylow

/-!
# `|C_G(V)|` has 2-part exactly `4` for a four-subgroup `V` of a dihedral Sylow

`Work.BG.fourGroup_centralizer_card`: if `T` is a Sylow 2-subgroup of a finite group `G`,
`T ≃* DihedralGroup m`, and `V ≤ T` is a Klein four-subgroup (`Work.GW2.IsFourGroup V`),
then `|C_G(V)| = 4 * a` with `a` odd.

The mathematical content: every Sylow 2-subgroup of `G` is isomorphic to `DihedralGroup m`
(`sylow_two_iso_dihedral_aux`), and in such a Sylow a Klein four-subgroup is self-centralizing
(`Work.BG.fourGroup_centralizer_in_sylow`, transported from
`Work.L2F.Dihedral.fourGroup_centralizer_dihedral`).  Consequently every 2-subgroup `Q` of
`C_G(V)` is contained in `V`: joining `Q` with `V` (possible because `Q ≤ C_G(V)` makes `V`
normal in `V ⊔ Q`) gives a 2-subgroup of `G`, hence one inside a Sylow `R` of `G`; there
`C_R(V) = V`, so `Q ≤ V`.  Thus `V` is a Sylow 2-subgroup of `C_G(V)`, its index in `C_G(V)`
is odd (Sylow's theorem), and Lagrange finishes.
-/

open scoped Pointwise

set_option linter.unusedVariables false

namespace Work.BG

/-- Any Sylow 2-subgroup of a finite group is isomorphic to `DihedralGroup m` as soon as one
of them is: Sylow subgroups are conjugate, and conjugation gives a multiplicative equivalence. -/
theorem sylow_two_iso_dihedral_aux {G : Type*} [Group G] [Finite G] (T R : Sylow 2 G) {m : ℕ}
    (e : ↥(T : Subgroup G) ≃* DihedralGroup m) :
    Nonempty (↥(R : Subgroup G) ≃* DihedralGroup m) := by
  obtain ⟨g, hg⟩ := @MulAction.IsPretransitive.exists_smul_eq G (Sylow 2 G) _ _ T R
  have hsub : (R : Subgroup G) = (T : Subgroup G).map ((MulAut.conj g : MulAut G) : G →* G) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  exact ⟨hsub ▸ (Subgroup.equivMapOfInjective (T : Subgroup G) _ (MulAut.conj g).injective).symm.trans e⟩

theorem fourGroup_centralizer_card {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {m : ℕ}
    (e : ↥(T : Subgroup G) ≃* DihedralGroup m) {V : Subgroup G} (hVT : V ≤ (T : Subgroup G))
    (hV : Work.GW2.IsFourGroup V) :
    ∃ a : ℕ, Odd a ∧ Nat.card (Subgroup.centralizer (V : Set G)) = 4 * a := by
  set C : Subgroup G := Subgroup.centralizer (V : Set G) with hCdef
  -- `V` is abelian (all its elements are involutions), so `V ≤ C_G(V)`.
  have hVC : V ≤ C := Work.L2F.Dihedral.le_centralizer_of_sq_eq_one hV.2
  have hVp : IsPGroup 2 ↥V := IsPGroup.of_card (n := 2) (by rw [hV.1]; norm_num)
  -- a Sylow 2-subgroup of `C_G(V)` containing `V`
  have hVpg : IsPGroup 2 ↥(V.subgroupOf C) := hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVC).symm
  obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow hVpg
  -- Key step: every 2-subgroup of `C_G(V)` is contained in `V`.
  have hkey : ∀ Q : Subgroup ↥C, IsPGroup 2 Q → Q ≤ V.subgroupOf C := by
    intro Q hQ
    have hQ₁p : IsPGroup 2 ↥(Q.map C.subtype) := hQ.map C.subtype
    have hQ₁C : Q.map C.subtype ≤ C := Subgroup.map_subtype_le Q
    have hQ₁norm : Q.map C.subtype ≤ Subgroup.normalizer (V : Set G) :=
      hQ₁C.trans (Subgroup.centralizer_le_normalizer (V : Set G))
    -- `V ⊔ Q` is a 2-subgroup, because `Q` centralizes `V` (so `V` is normal in the join)
    have hsup : IsPGroup 2 ↥(V ⊔ Q.map C.subtype) :=
      IsPGroup.to_sup_of_normal_left' hVp hQ₁p hQ₁norm
    obtain ⟨R, hR⟩ := IsPGroup.exists_le_sylow hsup
    obtain ⟨φ⟩ := sylow_two_iso_dihedral_aux T R e
    have hVR : V ≤ (R : Subgroup G) := le_trans le_sup_left hR
    -- in a dihedral Sylow, a four-subgroup is self-centralizing
    have hcent : Subgroup.centralizer (V : Set G) ⊓ (R : Subgroup G) = V :=
      fourGroup_centralizer_in_sylow R φ hVR hV
    have hsupC : V ⊔ Q.map C.subtype ≤ Subgroup.centralizer (V : Set G) := sup_le hVC hQ₁C
    have hle : V ⊔ Q.map C.subtype ≤ V := (le_inf hsupC hR).trans (le_of_eq hcent)
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact le_trans le_sup_right hle (Subgroup.mem_map_of_mem C.subtype hx)
  -- hence `V` is a Sylow 2-subgroup of `C_G(V)`
  have hPeq : (P : Subgroup ↥C) = V.subgroupOf C := le_antisymm (hkey P P.isPGroup') hPle
  have hPcard : Nat.card ↥(P : Subgroup ↥C) = 4 := by
    rw [hPeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv, hV.1]
  refine ⟨(P : Subgroup ↥C).index, ?_, ?_⟩
  · -- the index of a Sylow 2-subgroup is odd
    have hnd : ¬ 2 ∣ (P : Subgroup ↥C).index := Sylow.not_dvd_index P
    rw [← even_iff_two_dvd] at hnd
    exact Nat.not_even_iff_odd.mp hnd
  · -- Lagrange
    have hcard := Subgroup.card_mul_index (P : Subgroup ↥C)
    rw [← hcard, hPcard]

end Work.BG
