import Mathlib
import Submission.Work.DSMap.Mix2

namespace Work.DSM5b.HCF

universe u

theorem prod_div_tS_mem_chartRing {W : Type u} [CommRing W] {ι : Type u} [DecidableEq ι]
    [Fintype ι] (t : ι → W) {S : Finset ι} {i₀ : ι} (hi₀ : i₀ ∈ S)
    (k : ℕ) (a : ι → ℕ) (ha : ∑ i, a i = k * S.card) :
    IsLocalization.mk' (Localization.Away (DSMap.Mix2.tS t S)) (∏ i, t i ^ a i)
      ⟨(DSMap.Mix2.tS t S) ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩
      ∈ DSMap.Mix2.chartRing t S := by
  classical
  let A : W →+* (Localization.Away (DSMap.Mix2.tS t S)) := algebraMap W _
  let P : ι → W := fun i => ∏ j ∈ S.erase i, t j
  have hP : ∀ i, i ∈ S → t i * P i = DSMap.Mix2.tS t S := by
    intro i hi
    show t i * (∏ j ∈ S.erase i, t j) = ∏ j ∈ S, t j
    exact Finset.mul_prod_erase S t hi
  have hAP : ∀ i, i ∈ S → A (P i) * A (t i) = A (DSMap.Mix2.tS t S) := by
    intro i hi
    exact ((map_mul A (P i) (t i)).symm).trans
      (congrArg A ((mul_comm (P i) (t i)).trans (hP i hi)))
  have hu : IsUnit (A (DSMap.Mix2.tS t S)) := IsLocalization.Away.algebraMap_isUnit _
  let uinv : Localization.Away (DSMap.Mix2.tS t S) := ↑(hu.unit)⁻¹
  have huinv : A (DSMap.Mix2.tS t S) * uinv = 1 := by
    have h : (↑hu.unit : Localization.Away (DSMap.Mix2.tS t S)) * ↑(hu.unit)⁻¹ = 1 :=
      Units.mul_inv _
    rw [IsUnit.unit_spec hu] at h
    exact h
  let G : ι → Localization.Away (DSMap.Mix2.tS t S) := fun c => A (t c) * A (P i₀) * uinv
  let H : ι → Localization.Away (DSMap.Mix2.tS t S) := fun j => A (t i₀) * A (P j) * uinv
  have hG : ∀ c, G c * A (t i₀) = A (t c) := by
    intro c
    have hAPi : A (P i₀) * A (t i₀) = A (DSMap.Mix2.tS t S) := hAP i₀ hi₀
    change A (t c) * A (P i₀) * uinv * A (t i₀) = A (t c)
    calc A (t c) * A (P i₀) * uinv * A (t i₀)
        = A (t c) * (A (P i₀) * A (t i₀)) * uinv := by ring
      _ = A (t c) * A (DSMap.Mix2.tS t S) * uinv := by rw [hAPi]
      _ = A (t c) * (A (DSMap.Mix2.tS t S) * uinv) := by ring
      _ = A (t c) := by rw [huinv, mul_one]
  have hH : ∀ j, j ∈ S → H j * A (t j) = A (t i₀) := by
    intro j hj
    change A (t i₀) * A (P j) * uinv * A (t j) = A (t i₀)
    calc A (t i₀) * A (P j) * uinv * A (t j)
        = A (t i₀) * (A (P j) * A (t j)) * uinv := by ring
      _ = A (t i₀) * A (DSMap.Mix2.tS t S) * uinv := by rw [hAP j hj]
      _ = A (t i₀) * (A (DSMap.Mix2.tS t S) * uinv) := by ring
      _ = A (t i₀) := by rw [huinv, mul_one]
  have hGmem : ∀ c, G c ∈ DSMap.Mix2.chartRing t S := by
    intro c
    exact Algebra.subset_adjoin ⟨i₀, hi₀, c, hG c⟩
  have hHmem : ∀ j, j ∈ S → H j ∈ DSMap.Mix2.chartRing t S := by
    intro j hj
    exact Algebra.subset_adjoin ⟨j, hj, i₀, hH j hj⟩
  have key1 : (∏ j ∈ S, H j ^ k) * A (DSMap.Mix2.tS t S) ^ k
      = A (t i₀) ^ (k * S.card) := by
    have hB : A (DSMap.Mix2.tS t S) ^ k = ∏ j ∈ S, A (t j) ^ k := by
      rw [Finset.prod_pow]
      exact congrArg (· ^ k) (map_prod A t S)
    rw [hB, ← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl (fun j hj => by rw [← mul_pow, hH j hj]), Finset.prod_const,
      ← pow_mul]
  have hN : A (∏ i, t i ^ a i) = ∏ c : ι, A (t c) ^ a c := by
    rw [map_prod A (fun i => t i ^ a i) Finset.univ]
    exact Finset.prod_congr rfl (fun c _ => map_pow A (t c) (a c))
  have key2 : (∏ c : ι, G c ^ a c) * A (t i₀) ^ (k * S.card)
      = A (∏ i, t i ^ a i) := by
    have hp : A (t i₀) ^ (k * S.card) = ∏ c : ι, A (t i₀) ^ a c := by
      rw [← ha]
      exact (Finset.prod_pow_eq_pow_sum Finset.univ a (A (t i₀))).symm
    rw [hp, ← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl (fun c _ => by rw [← mul_pow, hG c]), hN]
  have hmain : ((∏ c : ι, G c ^ a c) * (∏ j ∈ S, H j ^ k)) * A (DSMap.Mix2.tS t S) ^ k
      = A (∏ i, t i ^ a i) := by
    rw [mul_assoc, key1, key2]
  have hmk : IsLocalization.mk' (Localization.Away (DSMap.Mix2.tS t S)) (∏ i, t i ^ a i)
      ⟨(DSMap.Mix2.tS t S) ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩
      = (∏ c : ι, G c ^ a c) * (∏ j ∈ S, H j ^ k) := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, map_pow]
    exact hmain.symm
  rw [hmk]
  exact mul_mem
    (Subalgebra.prod_mem (DSMap.Mix2.chartRing t S)
      (fun c _ => Subalgebra.pow_mem _ (hGmem c) (a c)))
    (Subalgebra.prod_mem (DSMap.Mix2.chartRing t S)
      (fun j hj => Subalgebra.pow_mem _ (hHmem j hj) k))

end Work.DSM5b.HCF
