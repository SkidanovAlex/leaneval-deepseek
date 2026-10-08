import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CORE3

theorem exists_mem_centralizer_normalizer_notMem_centralizer {G : Type*} [Group G]
    {S0 : Subgroup G} {t t1 s : G}
    (hs : s ∈ S0) (ht : t ∈ S0) (hcomm : ∀ a ∈ S0, ∀ b ∈ S0, a * b = b * a)
    (hsord : orderOf s = 4) (hs2 : s * s = t)
    (ht1sq : t1 * t1 = 1) (hinv : t1 * s * t1 = s⁻¹) (htne : t ≠ 1) :
    ∃ x ∈ Subgroup.centralizer ({t} : Set G),
      x ∈ Subgroup.normalizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers t1 : Subgroup G) : Set G) ∧
      x ∉ Subgroup.centralizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers t1 : Subgroup G) : Set G) := by
  have hs2' : s ^ 2 = t := by rw [pow_two, hs2]
  have hs4 : s ^ 4 = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hsord] at h
  have ht2 : t * t = 1 := by
    have h : t * t = s ^ 4 := by rw [← hs2', ← pow_two, ← pow_mul]
    rw [h, hs4]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ht1inv : t1⁻¹ = t1 := inv_eq_of_mul_eq_one_right ht1sq
  have hcA : ∀ x : G, (MulAut.conj t1) x = t1 * x * t1 := fun x => by
    rw [MulAut.conj_apply, ht1inv]
  have hconj_t1_t : t1 * t * t1 = t := by
    have h1 : (MulAut.conj t1) (s * s) = s⁻¹ * s⁻¹ := by
      rw [map_mul, hcA, hinv]
    have h3 : s⁻¹ * s⁻¹ = t := by
      have hh : s⁻¹ * s⁻¹ = (s * s)⁻¹ := by rw [mul_inv_rev]
      rw [hh, hs2, htinv]
    have ht' : t = s * s := hs2.symm
    calc t1 * t * t1 = (MulAut.conj t1) t := by rw [hcA]
      _ = (MulAut.conj t1) (s * s) := by rw [ht']
      _ = s⁻¹ * s⁻¹ := h1
      _ = t := h3
  have ht1t : t1 * t = t * t1 :=
    mul_right_cancel (show (t1 * t) * t1 = (t * t1) * t1 by
      rw [hconj_t1_t, mul_assoc, ht1sq, mul_one])
  have hstar : t1 * s = s⁻¹ * t1 := by
    rw [← hinv, mul_assoc, ht1sq, mul_one]
  have hs_t1 : s * t1 = t1 * s⁻¹ :=
    mul_right_cancel (show (s * t1) * s = (t1 * s⁻¹) * s by
      calc (s * t1) * s = s * (t1 * s) := by rw [mul_assoc]
        _ = s * (s⁻¹ * t1) := by rw [hstar]
        _ = (s * s⁻¹) * t1 := by rw [mul_assoc]
        _ = 1 * t1 := by rw [mul_inv_cancel]
        _ = t1 := by rw [one_mul]
        _ = (t1 * s⁻¹) * s := by rw [mul_assoc, inv_mul_cancel, mul_one])
  have hconj_t1 : s * t1 * s⁻¹ = t1 * t := by
    rw [hs_t1, mul_assoc, ← mul_inv_rev, hs2, htinv]
  have hconj_t1_inv : s⁻¹ * t1 * s = t1 * t := by
    rw [← hstar, mul_assoc, hs2]
  have hconj_t : s * t * s⁻¹ = t := by
    rw [← hs2']; group
  have hconj_t_inv : s⁻¹ * t * s = t := by
    rw [← hs2]; group
  have htV : t ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers t1 : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have ht1V : t1 ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers t1 : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers t1)
  have ht1tV : t1 * t ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers t1 : Subgroup G) := mul_mem ht1V htV
  have happly : ∀ x : G, (↑(MulAut.conj s) : G →* G) x = s * x * s⁻¹ := fun x => by
    change (MulAut.conj s) x = s * x * s⁻¹
    rw [MulAut.conj_apply]
  have happly_inv : ∀ x : G, (↑(MulAut.conj s⁻¹) : G →* G) x = s⁻¹ * x * s := fun x => by
    change (MulAut.conj s⁻¹) x = s⁻¹ * x * s
    rw [MulAut.conj_apply, inv_inv]
  have hmapV : Subgroup.map (↑(MulAut.conj s) : G →* G)
      (Subgroup.zpowers t ⊔ Subgroup.zpowers t1) ≤ (Subgroup.zpowers t ⊔ Subgroup.zpowers t1) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, happly t, hconj_t]; exact htV
    · rw [Subgroup.zpowers_le, happly t1, hconj_t1]; exact ht1tV
  have hmapVinv : Subgroup.map (↑(MulAut.conj s⁻¹) : G →* G)
      (Subgroup.zpowers t ⊔ Subgroup.zpowers t1) ≤ (Subgroup.zpowers t ⊔ Subgroup.zpowers t1) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, happly_inv t, hconj_t_inv]; exact htV
    · rw [Subgroup.zpowers_le, happly_inv t1, hconj_t1_inv]; exact ht1tV
  have hconj : ∀ h ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers t1 : Subgroup G),
      s * h * s⁻¹ ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers t1 : Subgroup G) := by
    intro h hh
    have hx := hmapV (Subgroup.mem_map_of_mem (↑(MulAut.conj s) : G →* G) hh)
    rwa [happly h] at hx
  have hconj_inv : ∀ h ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers t1 : Subgroup G),
      s⁻¹ * h * s ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers t1 : Subgroup G) := by
    intro h hh
    have hx := hmapVinv (Subgroup.mem_map_of_mem (↑(MulAut.conj s⁻¹) : G →* G) hh)
    rwa [happly_inv h] at hx
  refine ⟨s, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (hcomm s hs t ht).symm
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hconj h hh
    · intro hh
      have hx := hconj_inv (s * h * s⁻¹) hh
      have heq : s⁻¹ * (s * h * s⁻¹) * s = h := by group
      rwa [heq] at hx
  · intro hmem
    rw [Subgroup.mem_centralizer_iff] at hmem
    have h := hmem t1 ht1V
    have hthis : t1 * t = t1 := by
      rw [← hconj_t1, ← h, mul_assoc, mul_inv_cancel, mul_one]
    have ht1 : t = 1 := by
      have h' : t1 * t = t1 * 1 := by rw [hthis, mul_one]
      exact mul_left_cancel h'
    exact htne ht1

end Work.CORE3
