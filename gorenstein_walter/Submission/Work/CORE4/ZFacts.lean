import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F

namespace Work.CORE4

open Work.GW2 Subgroup

theorem ZFacts {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} {D : Work.GW2.Case2Data B} (hpre : Work.GW2.Case2Pre B D) :
    (D.F ⊓ Subgroup.centralizer (D.F : Set G)) ≠ ⊥ ∧
      Subgroup.normalizer (((D.F ⊓ Subgroup.centralizer (D.F : Set G)) : Subgroup G) : Set G)
        = D.M := by
  set Z : Subgroup G := D.F ⊓ Subgroup.centralizer (D.F : Set G) with hZ
  have hF_ne : D.F ≠ ⊥ := Case2Pre.F_ne B D hpre
  have hNF : Subgroup.normalizer (D.F : Set G) = D.M := Case2Pre.N_F B D hpre
  -- `F ≤ F(U)`, and `F(U)` is nilpotent, so `F` is nilpotent
  have hFle : D.F ≤ fittingIn B.U := Case2Data.F_le_fitting B D
  haveI : Group.IsNilpotent ↥(D.F.subgroupOf (fittingIn B.U)) := by
    haveI : Group.IsNilpotent ↥(fittingIn B.U) :=
      Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn B.U
    infer_instance
  haveI : Group.IsNilpotent ↥D.F :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hFle)).mp inferInstance
  haveI : Nontrivial ↥D.F := (Subgroup.nontrivial_iff_ne_bot D.F).mpr hF_ne
  -- the centre of `F` is nontrivial and lies in `Z`
  have hcent : Subgroup.center ↥D.F ≠ ⊥ := Group.IsNilpotent.center_ne_bot ↥D.F
  have hmaple : (Subgroup.center ↥D.F).map D.F.subtype ≤ Z := by
    rintro x ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hc := Subgroup.mem_center_iff.mp hy (⟨g, hg⟩ : ↥D.F)
    simpa using congrArg Subtype.val hc
  have hZne : Z ≠ ⊥ := by
    refine ne_bot_of_le_ne_bot (fun h => hcent ?_) hmaple
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥D.F)
      D.F.subtype_injective).mp h
  -- `M = N_G(F) ≤ N_G(Z)`
  have hM_le : D.M ≤ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro m hm k hk
    rw [hZ] at hk ⊢
    obtain ⟨hkF, hkC⟩ := Subgroup.mem_inf.mp hk
    have hmN : m ∈ Subgroup.normalizer (D.F : Set G) := hNF.symm ▸ hm
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hmN k).mp hkF
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hm' : m ∈ Subgroup.normalizer (D.F : Set G) := hmN
      have hminN : m⁻¹ ∈ Subgroup.normalizer (D.F : Set G) := Subgroup.inv_mem _ hm'
      have hwF : m⁻¹ * g * m ∈ D.F := by
        simpa using (Subgroup.mem_normalizer_iff.mp hminN g).mp hg
      have hwk : (m⁻¹ * g * m) * k = k * (m⁻¹ * g * m) :=
        Subgroup.mem_centralizer_iff.mp hkC (m⁻¹ * g * m) hwF
      have hg_eq : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
      calc g * (m * k * m⁻¹) = (m * (m⁻¹ * g * m) * m⁻¹) * (m * k * m⁻¹) :=
            congrArg (fun t => t * (m * k * m⁻¹)) hg_eq
        _ = m * ((m⁻¹ * g * m) * k) * m⁻¹ := by group
        _ = m * (k * (m⁻¹ * g * m)) * m⁻¹ := by rw [hwk]
        _ = (m * k * m⁻¹) * (m * (m⁻¹ * g * m) * m⁻¹) := by group
        _ = (m * k * m⁻¹) * g :=
            congrArg (fun t => (m * k * m⁻¹) * t) hg_eq.symm
  -- `N_G(Z) = M`: `M` is a coatom, so `N_G(Z) > M` would force `Z ⊴ G`
  have hnorm : Subgroup.normalizer (Z : Set G) = D.M := by
    refine le_antisymm ?_ hM_le
    by_contra hnotle
    have hne : Subgroup.normalizer (Z : Set G) ≠ D.M := fun h => hnotle h.le
    have hlt : D.M < Subgroup.normalizer (Z : Set G) := lt_of_le_of_ne hM_le (Ne.symm hne)
    have htop : Subgroup.normalizer (Z : Set G) = ⊤ := D.M_coatom.2 _ hlt
    haveI : Z.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    haveI : IsSimpleGroup G := hbc.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Z with hZbot | hZtop
    · exact hZne hZbot
    · -- then `Z = G`, so `F = G` and `G` is commutative
      have hFtop : D.F = ⊤ := by
        have hle : Z ≤ D.F := by rw [hZ]; exact inf_le_left
        exact top_le_iff.mp (hZtop ▸ hle)
      obtain ⟨a, b, hab⟩ := hbc.nonab
      apply hab
      have hbF : b ∈ (D.F : Set G) := by rw [hFtop]; exact Subgroup.mem_top b
      have haZ : a ∈ Z := by rw [hZtop]; exact Subgroup.mem_top a
      have haC : a ∈ Subgroup.centralizer (D.F : Set G) := by
        rw [hZ] at haZ
        exact (Subgroup.mem_inf.mp haZ).2
      exact (Subgroup.mem_centralizer_iff.mp haC b hbF).symm
  exact ⟨hZne, hnorm⟩

end Work.CORE4
