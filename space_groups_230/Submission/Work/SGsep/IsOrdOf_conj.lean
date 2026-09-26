import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG
open LeanEval.Geometry.SpaceGroupsProblem
open Classical

/-! ## The lattice of a product / of a conjugate -/

/-- `(A B) ℤ³ = A (B ℤ³)`. -/
theorem latImg_mul (A B : IMat) : latImg (A * B) = (latImg B).map (mulVecHom A) := by
  ext v
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨(toRMat B).mulVec (toRVec w), ⟨w, rfl⟩, by
      rw [mulVecHom_apply, ← hw, toRMat_mul, Matrix.mulVec_mulVec]⟩
  · rintro ⟨x, hx, hxu⟩
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    show (toRMat (A * B)).mulVec (toRVec y) = v
    rw [toRMat_mul, ← Matrix.mulVec_mulVec, hy]
    exact hxu

theorem mem_latImg_mul {A B : IMat} {v : Fin 3 → ℝ} :
    v ∈ latImg (A * B) ↔ ∃ w ∈ latImg B, (toRMat A).mulVec w = v := by
  rw [latImg_mul, AddSubgroup.mem_map]
  simp only [mulVecHom_apply]

/-- `(U⁻¹) ℤ³ = ℤ³` for unimodular `U`. -/
theorem latImg_invMat {U : IMat} (hU : IsUnit U.det) : latImg (invMat U) = zLat := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨w, hw⟩ := mem_latImg.mp hv
    rw [mem_zLat]
    refine ⟨(invMat U).mulVec w, ?_⟩
    rw [← hw, mulVec_toRVec]
  · intro v hv
    obtain ⟨w, hw⟩ := mem_zLat.mp hv
    rw [← hw, mem_latImg]
    exact ⟨U.mulVec w, by
      rw [mulVec_toRVec, Matrix.mulVec_mulVec, invMat_mul hU, Matrix.one_mulVec]⟩

/-- The conjugation action on lattices: `(U A U⁻¹) ℤ³ = U (A ℤ³)`. -/
theorem latImg_conj_eq_map {U : IMat} (hU : IsUnit U.det) (A : IMat) :
    latImg (U * A * invMat U) = (latImg A).map (mulVecHom U) := by
  have h1 : U * A * invMat U = U * (A * invMat U) := by rw [Matrix.mul_assoc]
  rw [h1, latImg_mul, latImg_mul, latImg_invMat hU, show zLat = latImg (1 : IMat) from rfl,
    ← latImg_mul (A := A) (B := 1), Matrix.mul_one]

/-! ## The two composite homomorphisms are the identity -/

theorem mulVecHom_invMat_comp {U : IMat} (hU : IsUnit U.det) :
    (mulVecHom (invMat U)).comp (mulVecHom U) = AddMonoidHom.id (Fin 3 → ℝ) := by
  rw [← mulVecHom_mul, invMat_mul hU, mulVecHom_one]

theorem mulVecHom_comp_invMat {U : IMat} (hU : IsUnit U.det) :
    (mulVecHom U).comp (mulVecHom (invMat U)) = AddMonoidHom.id (Fin 3 → ℝ) := by
  rw [← mulVecHom_mul, mul_invMat hU, mulVecHom_one]

/-- Membership in a conjugated lattice, transported back by `U⁻¹`. -/
theorem mem_latImg_conj_iff {U : IMat} (hU : IsUnit U.det) {N : IMat} {y : Fin 3 → ℝ} :
    y ∈ latImg (U * N * invMat U) ↔ (mulVecHom (invMat U)) y ∈ latImg N := by
  rw [latImg_conj_eq_map hU, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxy' : (mulVecHom (invMat U)) y = x := by
      rw [← hxy, ← AddMonoidHom.comp_apply, mulVecHom_invMat_comp hU, AddMonoidHom.id_apply]
    rw [hxy']
    exact hx
  · rintro hy
    exact ⟨(mulVecHom (invMat U)) y, hy, by
      rw [← AddMonoidHom.comp_apply, mulVecHom_comp_invMat hU, AddMonoidHom.id_apply]⟩

/-- Order of a vector modulo a lattice is preserved by conjugation `N ↦ U N U⁻¹` (with `U`
unimodular) up to the vector transformation `v ↦ U v + m`, `m ∈ U N U⁻¹ ℤ³`.  Use
`latImg_conj_eq_map` (in `SGsepDefs`) and integrality of `U`. -/
theorem IsOrdOf_conj {U : IMat} (hU : IsUnit U.det) {N : IMat} {v m : Fin 3 → ℝ} {o : ℕ}
    (hm : m ∈ latImg (U * N * invMat U)) (h : IsOrdOf (latImg N) v o) :
    IsOrdOf (latImg (U * N * invMat U)) ((toRMat U).mulVec v + m) o := by
  obtain ⟨ho1, hov, hmin⟩ := h
  refine ⟨ho1, ?_, ?_⟩
  · -- `o • (U v + m) = U (o • v) + o • m`
    rw [smul_add]
    refine add_mem ?_ (AddSubgroup.zsmul_mem _ hm o)
    have hmap : (mulVecHom U) ((o : ℤ) • v) = (o : ℤ) • (mulVecHom U) v :=
      AddMonoidHom.map_zsmul _ _ _
    have hmem : (mulVecHom U) ((o : ℤ) • v) ∈ (latImg N).map (mulVecHom U) :=
      AddSubgroup.mem_map.mpr ⟨(o : ℤ) • v, hov, rfl⟩
    rw [hmap, ← latImg_conj_eq_map hU] at hmem
    exact hmem
  · -- minimality: transport back by `U⁻¹`
    intro p hp hpd hmem
    have hψ := (mem_latImg_conj_iff hU).mp hmem
    rw [smul_add, AddMonoidHom.map_add] at hψ
    have h1 : (mulVecHom (invMat U))
        (((o / p : ℕ) : ℤ) • (toRMat U).mulVec v) = ((o / p : ℕ) : ℤ) • v := by
      rw [AddMonoidHom.map_zsmul]
      congr 1
      show (mulVecHom (invMat U)) ((mulVecHom U) v) = v
      rw [← AddMonoidHom.comp_apply, mulVecHom_invMat_comp hU, AddMonoidHom.id_apply]
    rw [h1] at hψ
    have h2 : (mulVecHom (invMat U)) (((o / p : ℕ) : ℤ) • m) ∈ latImg N := by
      rw [AddMonoidHom.map_zsmul]
      exact AddSubgroup.zsmul_mem _ ((mem_latImg_conj_iff hU).mp hm) _
    refine hmin p hp hpd ?_
    have hsub := sub_mem hψ h2
    rwa [add_sub_cancel_right] at hsub

end Work.SGsep
