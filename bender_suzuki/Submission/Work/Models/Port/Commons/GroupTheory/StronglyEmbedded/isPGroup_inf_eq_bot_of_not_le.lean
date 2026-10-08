import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.mem_map_conj_iff
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.sylow2_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem isPGroup_inf_eq_bot_of_not_le {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {T : Subgroup G} (hT : IsPGroup 2 T) (hTM : ¬ T ≤ M) : T ⊓ M = ⊥ := by
  classical
  by_contra hne
  set S : Subgroup G := T ⊓ M with hSdef
  have hSleT : S ≤ T := inf_le_left
  have hSleM : S ≤ M := inf_le_right
  have hSne : S ≠ ⊥ := by rw [hSdef]; exact hne
  have hSpg : IsPGroup 2 S := hT.to_inf_left
  have hSneT : S ≠ T := by
    intro hST
    exact hTM (hST ▸ hSleM)
  have hS₀lt : S.subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    exact hSneT (le_antisymm hSleT (Subgroup.subgroupOf_eq_top.mp htop))
  obtain ⟨y0, hyN0, hyS0⟩ := pGroup_normalizer_grows (H := T) hT hS₀lt
  let y : G := (y0 : G)
  have hyT : y ∈ T := y0.2
  have hbr : (Subgroup.normalizer (S : Set G)).subgroupOf T
      = Subgroup.normalizer (S.subgroupOf T : Subgroup T) :=
    Subgroup.subgroupOf_normalizer_eq hSleT
  have hyN' : y0 ∈ (Subgroup.normalizer (S : Set G)).subgroupOf T := by
    rw [hbr]; exact hyN0
  have hyN : y ∈ Subgroup.normalizer (S : Set G) := Subgroup.mem_subgroupOf.mp hyN'
  have hyS : y ∉ S := by
    intro hyS'
    exact hyS0 (Subgroup.mem_subgroupOf.mpr hyS')
  have hyM : y ∉ M := by
    intro hyM'
    exact hyS ⟨hyT, hyM'⟩
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
  have hxM : (x : G) ∈ M := hSleM x.2
  have hSleMy : S ≤ M.map (MulAut.conj y).toMonoidHom := by
    intro s hs
    rw [mem_map_conj_iff]
    exact hSleM ((Subgroup.mem_set_normalizer_iff''.mp hyN s).mp hs)
  have hxMy : (x : G) ∈ M.map (MulAut.conj y).toMonoidHom := hSleMy x.2
  have hxinter : (x : G) ∈ (M ⊓ M.map (MulAut.conj y).toMonoidHom : Subgroup G) :=
    ⟨hxM, hxMy⟩
  have hdvd : 2 ∣ Nat.card (M ⊓ M.map (MulAut.conj y).toMonoidHom : Subgroup G) := by
    have hd := Subgroup.orderOf_dvd_natCard
      (M ⊓ M.map (MulAut.conj y).toMonoidHom : Subgroup G) hxinter
    have hord : 2 ∣ orderOf (x : G) := by
      have h2 := hSpg.dvd_orderOf hxne
      rwa [← Subgroup.orderOf_coe x] at h2
    exact dvd_trans hord hd
  have hoddY : Odd (Nat.card (M ⊓ M.map (MulAut.conj y).toMonoidHom : Subgroup G)) :=
    hOdd y hyM
  exact (Nat.not_even_iff_odd.mpr hoddY) (even_iff_two_dvd.mpr hdvd)

end Commons.GroupTheory.StronglyEmbedded
