import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Basic.isNormalPComplement_complement_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.ThreePoints.P3NeBot

/-- A quotient of a group by the kernel of a homomorphism whose range is a `p`-group is a
`p`-group. -/
private theorem isPGroup_quotient_of_ker_eq {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (K : Subgroup G) [K.Normal] (hK : φ.ker = K) {p : ℕ}
    (h : IsPGroup p φ.range) : IsPGroup p (G ⧸ K) :=
  h.of_equiv ((QuotientGroup.quotientKerEquivRange φ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hK))

theorem exists_sylow_compl_of_isPGroup_image {F Y : Type} [Group F] [Finite F] [Group Y]
    (Z P : Subgroup F) (hZ : Z ≤ Subgroup.center F) (hZP : Z ≤ P)
    (hodd : Odd (Nat.card Z)) (φ : F →* Y) (hker : φ.ker = Z)
    (hP2 : IsPGroup 2 (Subgroup.map φ P)) :
    ∃ S : Subgroup F, S ≤ P ∧ IsPGroup 2 S ∧ Z ⊓ S = ⊥ ∧ Z ⊔ S = P ∧
      ∀ T : Subgroup F, T ≤ P → IsPGroup 2 T → T ≤ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥P := inferInstance
  -- `Z` is normal in `F`, since it lies in the centre.
  have hZnorm : Z.Normal := Subgroup.Normal.mk (fun n hn g => by
    have hc : g * n = n * g := (Subgroup.mem_center_iff.mp (hZ hn)) g
    have hgn : g * n * g⁻¹ = n := by rw [hc]; group
    rwa [hgn])
  have hZn : (Z.subgroupOf P).Normal := hZnorm.subgroupOf P
  -- The range of `φ ∘ P.subtype` is `P.map φ`.
  have hrange : (φ.comp P.subtype).range = Subgroup.map φ P := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  -- The kernel of `φ ∘ P.subtype` is `Z.subgroupOf P`.
  have hkerc : (φ.comp P.subtype).ker = Z.subgroupOf P := by
    rw [← MonoidHom.comap_ker, hker, Subgroup.comap_subtype]
  -- Hence `↥P ⧸ Z.subgroupOf P` is a `2`-group.
  have hquot : IsPGroup 2 (↥P ⧸ Z.subgroupOf P) := by
    refine isPGroup_quotient_of_ker_eq (φ.comp P.subtype) (Z.subgroupOf P) hkerc ?_
    rw [hrange]; exact hP2
  -- `Z.subgroupOf P` is a normal `2`-complement of `↥P`.
  have hcardZ : Nat.card (Z.subgroupOf P) = Nat.card Z := by
    rw [← Subgroup.card_map_of_injective (f := P.subtype) P.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZP]
  have hNPC : Work.NPC.IsNormalPComplement 2 (Z.subgroupOf P) :=
    { normal := hZn
      coprime_card := by rw [hcardZ]; exact Nat.coprime_two_right.mpr hodd
      isPGroup_quotient := hquot }
  -- A Sylow `2`-subgroup of `↥P`, which is a complement of `Z.subgroupOf P`.
  obtain ⟨P2⟩ := Sylow.nonempty (p := 2) (G := ↥P)
  let Sg : Subgroup ↥P := (P2 : Subgroup ↥P)
  have hcomp : (Z.subgroupOf P).IsComplement' Sg :=
    Work.NPC.Basic.isNormalPComplement_complement_sylow hNPC P2
  have hSg_p : IsPGroup 2 Sg := P2.isPGroup'
  -- `Z.subgroupOf P` lies in the centre of `↥P`.
  have hZgc : Z.subgroupOf P ≤ Subgroup.center ↥P := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hZ (Subgroup.mem_subgroupOf.mp hz))) (g : F)
  -- `Sg` is normal in `↥P`.
  have hSgn : Sg.Normal := by
    refine Subgroup.Normal.mk (fun n hn g => ?_)
    have hgm : g ∈ ((Z.subgroupOf P : Subgroup ↥P) : Set ↥P) * (Sg : Set ↥P) := by
      rw [hcomp.mul_eq]; exact Set.mem_univ g
    obtain ⟨z, hz, s, hs, hzs⟩ := Set.mem_mul.mp hgm
    have hzc : ∀ y : ↥P, y * z = z * y := Subgroup.mem_center_iff.mp (hZgc hz)
    rw [← hzs]
    have key : z * s * n * (z * s)⁻¹ = s * n * s⁻¹ := by
      rw [mul_inv_rev]
      have h1 : z * s * n * (s⁻¹ * z⁻¹) = z * (s * n * s⁻¹) * z⁻¹ := by group
      rw [h1, (hzc (s * n * s⁻¹)).symm]
      group
    rw [key]
    exact Sg.mul_mem (Sg.mul_mem hs hn) (Sg.inv_mem hs)
  -- The index of `Sg` is odd.
  have hSgidx : ¬ 2 ∣ Sg.index := by
    rw [hcomp.index_eq_card, hcardZ]
    intro hd
    have h0 : Nat.card Z % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    have h1 : Nat.card Z % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  refine ⟨Sg.map P.subtype, Subgroup.map_subtype_le Sg, hSg_p.map P.subtype, ?_, ?_, ?_⟩
  · -- `Z ⊓ S = ⊥`
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSg_p
    have hSm : Nat.card (Sg.map P.subtype) = Nat.card Sg :=
      Subgroup.card_map_of_injective P.subtype_injective
    have hcop : (Nat.card Z).Coprime (Nat.card (Sg.map P.subtype)) := by
      rw [hSm, hk]
      exact (Nat.coprime_two_right.mpr hodd).pow_right k
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  · -- `Z ⊔ S = P`
    have hmap := congrArg (Subgroup.map P.subtype) hcomp.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZP] at hmap
    exact hmap
  · -- universal property
    intro T hTP hT2
    have hTgp : IsPGroup 2 (T.subgroupOf P) := hT2.comap_subtype
    obtain ⟨Q2, hQ2⟩ := hTgp.exists_le_sylow
    haveI : Sg.Normal := hSgn
    have hSg_le : Sg ≤ (Q2 : Subgroup ↥P) := hSg_p.le_sylow_of_normal Q2
    have hQ2eq : (Q2 : Subgroup ↥P) = Sg := by
      have hmax := (hSg_p.toSylow hSgidx).is_maximal' (Q := (Q2 : Subgroup ↥P))
        Q2.isPGroup' hSg_le
      rwa [IsPGroup.toSylow_coe] at hmax
    have hle : T.subgroupOf P ≤ Sg := by rw [← hQ2eq]; exact hQ2
    calc T = (T.subgroupOf P).map P.subtype := (Subgroup.map_subgroupOf_eq_of_le hTP).symm
      _ ≤ Sg.map P.subtype := Subgroup.map_mono hle

end Work.ThreePoints.P3NeBot
