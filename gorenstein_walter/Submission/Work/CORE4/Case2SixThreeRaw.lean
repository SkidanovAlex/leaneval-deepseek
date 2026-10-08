import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.SixThree

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

theorem Case2SixThreeRaw (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G) (s : G) (K B0 F : Subgroup G),
        s ∈ B.H → s ∈ M → orderOf s = 2 →
        B.U ⊓ M = K ⊔ B0 → K ≤ B.U ⊓ M → B0 ≤ B.U ⊓ M →
        (K : Set G) = Work.GW2.invSet (B.U ⊓ M) s →
        B0 = (B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G) →
        F = B0 ⊓ Work.GW2.fittingIn B.U →
        Work.GW2.fittingIn B.U ⊓ M = (Work.GW2.fittingIn B.U ⊓ K) ⊔ F := by
  intro G _ _ _ B M s K B0 F hsH hsM hs_order hU_eq hK_le hB0_le hK_def hB0_def hF_def
  have hF_le_fitting : F ≤ fittingIn B.U := by rw [hF_def]; exact inf_le_right
  have hF_le_UinfM : F ≤ B.U ⊓ M := le_trans (by rw [hF_def]; exact inf_le_left) hB0_le
  have hK_le_M : K ≤ M := le_trans hK_le inf_le_right
  have hK_le_U : K ≤ B.U := le_trans hK_le inf_le_left
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxA, hxM⟩ := Subgroup.mem_inf.mp hx
    have hxX : x ∈ B.U ⊓ M :=
      Subgroup.mem_inf.mpr ⟨Subgroup.map_subtype_le (fitting ↥B.U) hxA, hxM⟩
    have hUnorm : ∀ y ∈ B.U, ∀ k ∈ B.H, k * y * k⁻¹ ∈ B.U := fun y hy k hk =>
      (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal y k hy hk
    have hconjU : conjSub s B.U = B.U := by
      refine le_antisymm ?_ ?_
      · intro y hy
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
        rw [← hzy]
        simpa [MulAut.conj_apply] using hUnorm z hz s hsH
      · intro y hy
        refine Subgroup.mem_map.mpr ⟨s⁻¹ * y * s, by simpa using hUnorm y hy s⁻¹ (B.H.inv_mem hsH), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hconjA : ∀ y ∈ fittingIn B.U, s * y * s⁻¹ ∈ fittingIn B.U := by
      have hkey : conjSub s (fittingIn B.U) = fittingIn B.U := by
        rw [conjSub_fittingIn, hconjU]
      intro y hy
      have hmem : (MulAut.conj s) y ∈ conjSub s (fittingIn B.U) :=
        Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom hy
      rw [hkey, MulAut.conj_apply] at hmem
      exact hmem
    have hsN_U : s ∈ Subgroup.normalizer ((B.U : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact ⟨fun hy => hUnorm y hy s hsH, fun hy => by
        have h2 := hUnorm (s * y * s⁻¹) hy s⁻¹ (B.H.inv_mem hsH)
        rw [inv_inv, show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h2
        exact h2⟩
    have hsN_M : s ∈ Subgroup.normalizer ((M : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => M.mul_mem (M.mul_mem hsM hy) (M.inv_mem hsM), fun hy => ?_⟩
      have h : y = s⁻¹ * (s * y * s⁻¹) * s := by group
      rw [h]
      exact M.mul_mem (M.mul_mem (M.inv_mem hsM) hy) hsM
    have hsNX : s ∈ Subgroup.normalizer (((B.U ⊓ M : Subgroup G)) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
        exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hsN_U y).mp hy1,
          (Subgroup.mem_normalizer_iff.mp hsN_M y).mp hy2⟩
      · intro hy
        obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
        exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hsN_U y).mpr hy1,
          (Subgroup.mem_normalizer_iff.mp hsN_M y).mpr hy2⟩
    have hOddX : Odd (Nat.card ↥(B.U ⊓ M)) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le (inf_le_left : B.U ⊓ M ≤ B.U))
    have hKnorm : (K.subgroupOf (B.U ⊓ M)).Normal :=
      (I.toolkit.c15 G I.toolkit.ft (B.U ⊓ M) s hs_order hOddX hsNX).2.2 K hK_def |>.2.1
    obtain ⟨k, hkK, b, hbB0, hkb⟩ :=
      exists_mul_of_mem_of_normal_subgroupOf hK_le hB0_le hKnorm hU_eq.symm x hxX
    have hk_inv : k ∈ invSet (B.U ⊓ M) s := by rw [← hK_def]; exact hkK
    have hsk : MulAut.conj s k = k⁻¹ := by
      rw [MulAut.conj_apply]; exact hk_inv.2
    have hsb : MulAut.conj s b = b := by
      rw [MulAut.conj_apply]
      have hb_c : b ∈ Subgroup.centralizer ({s} : Set G) := by
        have h := hbB0
        rw [hB0_def] at h
        exact (Subgroup.mem_inf.mp h).2
      have hbs : b * s = s * b := Subgroup.mem_centralizer_singleton_iff.mp hb_c
      rw [← hbs]; group
    have hk2 : k ^ 2 ∈ fittingIn B.U := by
      have hxx : x * (s * x⁻¹ * s⁻¹) ∈ fittingIn B.U :=
        (fittingIn B.U).mul_mem hxA (hconjA x⁻¹ ((fittingIn B.U).inv_mem hxA))
      have h1 : s * x⁻¹ * s⁻¹ = b⁻¹ * k := by
        have hxconj : MulAut.conj s x = k⁻¹ * b := by
          rw [← hkb, map_mul, hsk, hsb]
        rw [← MulAut.conj_apply, map_inv, hxconj]
        group
      have heq : k ^ 2 = x * (s * x⁻¹ * s⁻¹) := by
        rw [h1, ← hkb, pow_two]
        group
      rwa [← heq] at hxx
    have hkA : k ∈ fittingIn B.U := by
      have hdvd : orderOf k ∣ Nat.card ↥B.U :=
        Subgroup.orderOf_dvd_natCard B.U (hK_le_U hkK)
      have hodd : Odd (orderOf k) := Odd.of_dvd_nat B.U_odd hdvd
      obtain ⟨t, ht⟩ := hodd
      have h2dvd : 2 ∣ orderOf k + 1 := ⟨t + 1, by omega⟩
      have hkey : k = (k ^ 2) ^ ((orderOf k + 1) / 2) := by
        rw [← pow_mul, Nat.mul_div_cancel' h2dvd, pow_succ, pow_orderOf_eq_one, one_mul]
      rw [hkey]
      exact (fittingIn B.U).pow_mem hk2 _
    have hbA : b ∈ fittingIn B.U := by
      have hb_eq : b = k⁻¹ * x := by rw [← hkb]; group
      rw [hb_eq]
      exact (fittingIn B.U).mul_mem ((fittingIn B.U).inv_mem hkA) hxA
    rw [← hkb]
    refine Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hkA, hkK⟩) ?_
    rw [hF_def]
    exact Subgroup.mem_inf.mpr ⟨hbB0, hbA⟩
  · refine sup_le (le_inf inf_le_left (le_trans inf_le_right hK_le_M)) ?_
    exact le_inf hF_le_fitting (le_trans hF_le_UinfM inf_le_right)

end Work.CORE4
