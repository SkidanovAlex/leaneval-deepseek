import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.NZ_conj
import Submission.Work.SGsep.vA_conj
import Submission.Work.SGsep.det_trace_conj
import Submission.Work.SGsep.IsOrdOf_unique
import Submission.Work.SGsep.IsOrdOf_conj

namespace Work.SGsep

open Work.SG
open LeanEval.Geometry.SpaceGroupsProblem
open Classical

/-! ## Preparing the third component of `keyE`

The third component of `keyE k A` is `ordInLat (latImg (NZ A)) (vA (sgTau k) A)`, the order of
the intrinsic translation `v_A` in `ℝ³/N_Aℤ³`.  It is a definite description built from the
predicate `IsOrdOf`; the three lemmas below let us compare two such orders by comparing the
underlying predicates. -/

/-- `IsOrdOf` determines `ordInLat`: whenever `IsOrdOf L v o` holds, `ordInLat L v` is that
(uniquely determined) `o`. -/
theorem ordInLat_eq_of_spec {L : AddSubgroup (Fin 3 → ℝ)} {v : Fin 3 → ℝ} {o : ℕ}
    (h : IsOrdOf L v o) : ordInLat L v = o :=
  IsOrdOf_unique (ordInLat_spec ⟨o, h⟩) h

/-- If no order exists, `ordInLat` takes its junk value `0`. -/
theorem ordInLat_eq_zero_of_not {L : AddSubgroup (Fin 3 → ℝ)} {v : Fin 3 → ℝ}
    (h : ¬ ∃ o, IsOrdOf L v o) : ordInLat L v = 0 := by
  unfold ordInLat
  exact dite_eq_right h

/-- Translating `v` by an element `m` of the lattice does not change its order modulo the
lattice: `k • v ∈ L` iff `k • (v + m) ∈ L` for every integer `k`. -/
theorem IsOrdOf_add_mem_iff {L : AddSubgroup (Fin 3 → ℝ)} {v m : Fin 3 → ℝ} (hm : m ∈ L)
    {o : ℕ} : IsOrdOf L (v + m) o ↔ IsOrdOf L v o := by
  have hmem : ∀ k : ℤ, k • (v + m) ∈ L ↔ k • v ∈ L := by
    intro k
    have hkm : k • m ∈ L := L.zsmul_mem hm k
    rw [smul_add]
    constructor
    · intro h
      have hs := sub_mem h hkm
      rwa [add_sub_cancel_right] at hs
    · intro h
      exact add_mem h hkm
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (hmem o).mp h2,
      fun p hp hpd hz => h3 p hp hpd ((hmem _).mpr hz)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (hmem o).mpr h2,
      fun p hp hpd hz => h3 p hp hpd ((hmem _).mp hz)⟩

/-- An injective additive map preserves orders: `f v` has the same order modulo `L.map f` as `v`
modulo `L`. -/
theorem IsOrdOf_map_iff {f : (Fin 3 → ℝ) →+ (Fin 3 → ℝ)} (hf : Function.Injective f)
    {L : AddSubgroup (Fin 3 → ℝ)} {v : Fin 3 → ℝ} {o : ℕ} :
    IsOrdOf (L.map f) (f v) o ↔ IsOrdOf L v o := by
  have hmem : ∀ k : ℤ, k • f v ∈ L.map f ↔ k • v ∈ L := by
    intro k
    rw [← AddMonoidHom.map_zsmul]
    constructor
    · intro h
      obtain ⟨x, hx, hxeq⟩ := AddSubgroup.mem_map.mp h
      rwa [hf hxeq] at hx
    · intro h
      exact AddSubgroup.mem_map.mpr ⟨k • v, h, rfl⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (hmem o).mp h2,
      fun p hp hpd hz => h3 p hp hpd ((hmem _).mpr hz)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (hmem o).mpr h2,
      fun p hp hpd hz => h3 p hp hpd ((hmem _).mp hz)⟩

/-- The `elem` key `keyE k A = (det A, trace A, order of `v_A` in `ℤ³/N_Aℤ³`)` is invariant under conjugation `A ↦ U A U⁻¹` by a unimodular integer matrix, provided the cocycle transforms as `τ'(U A U⁻¹) = U τ(A) + s - (U A U⁻¹) s + n`, `n ∈ ℤ³`. -/
theorem keyE_conj (k l : Fin 230) (U : IMat) (s : Fin 3 → ℝ) (hU : IsUnit U.det) {A : IMat}
    (hcoc : ∃ n : Fin 3 → ℤ, sgTau l (U * A * invMat U) =
      (toRMat U).mulVec (sgTau k A) + s - (toRMat (U * A * invMat U)).mulVec s + toRVec n) :
    keyE l (U * A * invMat U) = keyE k A := by
  obtain ⟨n, hn⟩ := hcoc
  -- The intrinsic translations are related by `v_{UAU⁻¹} = U v_A + m`, `m ∈ N_{UAU⁻¹} ℤ³`.
  obtain ⟨m, hm, hmv⟩ := vA_conj (U := U) hU (sgTau k) (sgTau l) s A ⟨n, hn⟩
  -- And `N_{UAU⁻¹} = U N_A U⁻¹`, so `N_{UAU⁻¹} ℤ³ = U (N_A ℤ³)`.
  have hNZ : NZ (U * A * invMat U) = U * NZ A * invMat U := NZ_conj (U := U) hU A
  have hLmap : latImg (NZ (U * A * invMat U)) = (latImg (NZ A)).map (mulVecHom U) := by
    rw [hNZ, Work.SG.latImg_conj_eq_map hU (NZ A)]
  have hm' : m ∈ latImg (NZ (U * A * invMat U)) := by rw [hNZ]; exact hm
  have hm'' : m ∈ (latImg (NZ A)).map (mulVecHom U) := by rw [← hLmap]; exact hm'
  -- Hence `IsOrdOf` agrees on the two sides: strip the lattice element `m`, then push
  -- through the injective map `mulVecHom U`.
  have hiff : ∀ o, IsOrdOf (latImg (NZ (U * A * invMat U)))
        (vA (sgTau l) (U * A * invMat U)) o ↔ IsOrdOf (latImg (NZ A)) (vA (sgTau k) A) o := by
    intro o
    rw [hmv, hLmap, IsOrdOf_add_mem_iff hm'']
    exact IsOrdOf_map_iff (f := mulVecHom U) (mulVecHom_injective hU)
  -- The definite descriptions therefore agree.
  have hord : ordInLat (latImg (NZ (U * A * invMat U))) (vA (sgTau l) (U * A * invMat U))
      = ordInLat (latImg (NZ A)) (vA (sgTau k) A) := by
    by_cases hA : ∃ o, IsOrdOf (latImg (NZ A)) (vA (sgTau k) A) o
    · obtain ⟨o, ho⟩ := hA
      rw [ordInLat_eq_of_spec ((hiff o).mpr ho), ordInLat_eq_of_spec ho]
    · have hB : ¬ ∃ o, IsOrdOf (latImg (NZ (U * A * invMat U)))
          (vA (sgTau l) (U * A * invMat U)) o := by
        rintro ⟨o, ho⟩
        exact hA ⟨o, (hiff o).mp ho⟩
      rw [ordInLat_eq_zero_of_not hB, ordInLat_eq_zero_of_not hA]
  -- Assemble: `det` and `trace` are invariant by `det_trace_conj`.
  rw [keyE, keyE, (det_trace_conj (U := U) hU A).1, (det_trace_conj (U := U) hU A).2, hord]

end Work.SGsep
