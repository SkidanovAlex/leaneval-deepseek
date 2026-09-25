import Mathlib
import Submission.NK.NUV2.RouteD.LevelDescent

/-!
# The transition map on fundamental classes (Route F)
-/

open CategoryTheory

namespace NK.NUV2.RouteF

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- **The transition on fundamental classes.**  If `u` is a fundamental class at the level `E`
(additive order `[E : F]`) and `M = E^N` a normal level with `N` the Galois group of `E/M`, then
the preimage of `[E : M] • u` under `levelInfMap` is a fundamental class at the level `M`. -/
theorem transition_generator (N : Subgroup (L ≃ₐ[F] L)) [N.Normal]
    (hfin : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2))
    (hcard : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2) = Nat.card (L ≃ₐ[F] L))
    (u : groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2))
    (hcardK : Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)) 2) = N.index) :
    ∃ v : groupCohomology (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)) 2,
      addOrderOf v = Nat.card (groupCohomology
          (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)) 2) ∧
      NK.NUV2.RouteD.levelInfMap (F := F) (M := ↥(IntermediateField.fixedField N)) (L := L) v
        = ((Nat.card (L ≃ₐ[F] L) / N.index : ℕ) : ℤ) • u := by
  have : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2) := hfin
  obtain ⟨hinj, hrange⟩ := NK.NUV2.RouteD.levelInfMap_injective_range (F := F) (L := L) N
    hfin hcard u hu hcardK
  have hdvd : N.index ∣ Nat.card (L ≃ₐ[F] L) := Subgroup.index_dvd_card N
  have hk : Nat.card (L ≃ₐ[F] L) / N.index * N.index = Nat.card (L ≃ₐ[F] L) :=
    Nat.div_mul_cancel hdvd
  have hku : Nat.card (L ≃ₐ[F] L) / N.index ∣ Nat.card (L ≃ₐ[F] L) := ⟨N.index, hk.symm⟩
  have hc : addOrderOf u = Nat.card (L ≃ₐ[F] L) := by rw [hu, hcard]
  have hTop : Nat.card (L ≃ₐ[F] L) • u = 0 := by
    rw [← hc]; exact addOrderOf_nsmul_eq_zero u
  have hcpos : 0 < Nat.card (L ≃ₐ[F] L) := by
    rw [IsGalois.card_aut_eq_finrank]
    exact Module.finrank_pos
  have hnpos : 0 < N.index := by
    by_contra h
    rw [not_lt, Nat.le_zero] at h
    have h2 := Subgroup.card_mul_index N
    rw [h, mul_zero] at h2
    rw [← h2] at hcpos
    exact lt_irrefl 0 hcpos
  have hkpos : 0 < Nat.card (L ≃ₐ[F] L) / N.index :=
    Nat.div_pos (Nat.le_of_dvd hcpos hdvd) hnpos
  -- the multiple `[E : M] • u` is killed by `N.index`, hence lies in the range
  have hmem : (((Nat.card (L ≃ₐ[F] L) / N.index : ℕ) : ℤ) • u)
      ∈ LinearMap.range (NK.NUV2.RouteD.levelInfMap (F := F)
          (M := ↥(IntermediateField.fixedField N)) (L := L)).hom := by
    rw [hrange, LinearMap.mem_ker]
    change (N.index : ℤ) • (((Nat.card (L ≃ₐ[F] L) / N.index : ℕ) : ℤ) • u) = 0
    rw [← mul_zsmul, ← Nat.cast_mul, mul_comm N.index _, hk, natCast_zsmul u]
    exact hTop
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hmem
  refine ⟨v, ?_, hv⟩
  have hd1 : addOrderOf (NK.NUV2.RouteD.levelInfMap (F := F)
      (M := ↥(IntermediateField.fixedField N)) (L := L) v) ∣ addOrderOf v := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
  have hd2 : addOrderOf v ∣ addOrderOf (NK.NUV2.RouteD.levelInfMap (F := F)
      (M := ↥(IntermediateField.fixedField N)) (L := L) v) := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    apply hinj
    rw [map_nsmul, map_zero, addOrderOf_nsmul_eq_zero]
  have hEq : addOrderOf v = addOrderOf (NK.NUV2.RouteD.levelInfMap (F := F)
      (M := ↥(IntermediateField.fixedField N)) (L := L) v) := dvd_antisymm hd2 hd1
  rw [hEq, hv, natCast_zsmul u, addOrderOf_nsmul, hc, Nat.gcd_eq_right hku,
    ← Nat.eq_div_of_mul_eq_right hkpos.ne' hk]
  exact hcardK.symm

end NK.NUV2.RouteF
