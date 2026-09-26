/-
Fallback development of the naturality of the six pair bits `pairBitsG` under conjugation,
for `Work.SGsep.pair_separates`.

The one non-trivial point is the `fix`/`afix` bit.  Both are instances of the following
transport statement: the membership of `(toRMat Z) · v_A` in `Z N_A ℤ³` is transported to the
membership of `(toRMat φZ) · v_{φA}` in `φZ · N_{φA} ℤ³`, where `φ X = U X U⁻¹` and `Z` is an
arbitrary integer matrix.  We prove the transport for an arbitrary `Z`; the `fix` bit is
`Z = B - 1` and the `afix` bit is `Z = B + 1`.
-/
import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.PairAux
import Submission.Work.SGsep.PairAux2
import Submission.Work.SGsep.vA_conj
import Submission.Work.SGsep.NZ_conj
import Submission.Work.SGsep.IsOrdOf_conj
import Submission.Work.SGsep.sym_prep

namespace Work.SGsep
open Work.SG
open Work.SGsep.PSep
open Classical

namespace PSep

theorem toRMat_conj {U : IMat} (X : IMat) :
    toRMat (U * X * invMat U) = toRMat U * toRMat X * toRMat (invMat U) := by
  rw [toRMat_mul, toRMat_mul]

theorem toRMat_invMat_mul {U : IMat} (hU : IsUnit U.det) :
    toRMat (invMat U) * toRMat U = 1 := by
  rw [← toRMat_mul, invMat_mul hU, toRMat_one]

/-- The `fix`/`afix` transport: membership of `Z · v_A` in `Z N_A ℤ³` is equivalent to the
corresponding membership for the conjugate `φ X = U X U⁻¹` and the transformed cocycle. -/
theorem mem_conj_transport {U : IMat} (hU : IsUnit U.det) (τ τ' : IMat → Fin 3 → ℝ)
    (s : Fin 3 → ℝ) (A Z : IMat)
    (hc : ∃ n : IVec, τ' (U * A * invMat U) = (toRMat U).mulVec (τ A) + s
        - (toRMat (U * A * invMat U)).mulVec s + toRVec n) :
    ((toRMat Z).mulVec (vA τ A) ∈ latImg (Z * NZ A))
      ↔ ((toRMat (U * Z * invMat U)).mulVec (vA τ' (U * A * invMat U))
          ∈ latImg ((U * Z * invMat U) * NZ (U * A * invMat U))) := by
  obtain ⟨n, hn⟩ := hc
  obtain ⟨m, hm, hmv⟩ := vA_conj (U := U) hU τ τ' s A ⟨n, hn⟩
  -- `m` is the image under `U` of a lattice vector
  obtain ⟨w, hw, hmw⟩ : ∃ w ∈ latImg (NZ A), m = mulVecHom U w := by
    have h := hm
    rw [latImg_conj_eq_map hU (NZ A), AddSubgroup.mem_map] at h
    obtain ⟨w, hw, hwv⟩ := h
    exact ⟨w, hw, hwv.symm⟩
  -- the conjugated lattice
  have hNZ : NZ (U * A * invMat U) = U * NZ A * invMat U := NZ_conj hU A
  have hK : (U * Z * invMat U) * NZ (U * A * invMat U) = U * (Z * NZ A) * invMat U := by
    rw [hNZ]
    rw [show U * Z * invMat U * (U * NZ A * invMat U)
        = U * Z * (invMat U * U) * (NZ A * invMat U) from by noncomm_ring,
      invMat_mul hU, Matrix.mul_one]
    noncomm_ring
  have hRiRu : toRMat (invMat U) * toRMat U = 1 := toRMat_invMat_mul hU
  -- the core `mulVec` computation, phrased with the additive homomorphism `mulVecHom`
  have hcore : (toRMat (U * Z * invMat U)).mulVec ((toRMat U).mulVec (vA τ A) + m)
      = (toRMat U).mulVec ((toRMat Z).mulVec (vA τ A + w)) := by
    show mulVecHom (U * Z * invMat U) (mulVecHom U (vA τ A) + m)
        = mulVecHom U (mulVecHom Z (vA τ A + w))
    rw [mulVecHom_mul, mulVecHom_mul]
    simp only [AddMonoidHom.comp_apply, map_add]
    rw [show mulVecHom (invMat U) (mulVecHom U (vA τ A)) = vA τ A from by
          rw [← AddMonoidHom.comp_apply, mulVecHom_invMat_comp hU, AddMonoidHom.id_apply],
      hmw,
      show mulVecHom (invMat U) (mulVecHom U w) = w from by
          rw [← AddMonoidHom.comp_apply, mulVecHom_invMat_comp hU, AddMonoidHom.id_apply]]
  -- the second summand lands in the conjugated lattice
  have hsum2 : (toRMat U).mulVec ((toRMat Z).mulVec w) ∈ latImg (U * (Z * NZ A) * invMat U) := by
    rw [latImg_conj_eq_map hU (Z * NZ A), AddSubgroup.mem_map]
    refine ⟨(toRMat Z).mulVec w, ?_, rfl⟩
    rw [latImg_mul, AddSubgroup.mem_map]
    exact ⟨w, hw, rfl⟩
  constructor
  · intro hZ
    rw [hK, hmv, hcore]
    have hgoal : (toRMat U).mulVec ((toRMat Z).mulVec (vA τ A))
        + (toRMat U).mulVec ((toRMat Z).mulVec w) ∈ latImg (U * (Z * NZ A) * invMat U) :=
      add_mem (by
        rw [latImg_conj_eq_map hU (Z * NZ A), AddSubgroup.mem_map]
        exact ⟨(toRMat Z).mulVec (vA τ A), hZ, rfl⟩) hsum2
    rw [Matrix.mulVec_add, Matrix.mulVec_add]
    exact hgoal
  · intro hconj
    rw [hK, hmv, hcore] at hconj
    have hsum1 : (toRMat U).mulVec ((toRMat Z).mulVec (vA τ A))
        + (toRMat U).mulVec ((toRMat Z).mulVec w) ∈ latImg (U * (Z * NZ A) * invMat U) := by
      rw [← Matrix.mulVec_add, ← Matrix.mulVec_add]
      exact hconj
    have hsub := sub_mem hsum1 hsum2
    rw [add_sub_cancel_right] at hsub
    rw [latImg_conj_eq_map hU (Z * NZ A), AddSubgroup.mem_map] at hsub
    obtain ⟨y, hy, hyv⟩ := hsub
    have hyw : (toRMat Z).mulVec (vA τ A) = y := by
      apply mulVecHom_injective hU
      rw [hyv]
      rfl
    rw [hyw]
    exact hy

/-- The `fix` bit is transported by conjugation. -/
theorem fixBitG_conj {U : IMat} (hU : IsUnit U.det) {τ τ' : IMat → Fin 3 → ℝ} {s : Fin 3 → ℝ}
    {A B : IMat}
    (hc : ∃ n : IVec, τ' (U * A * invMat U) = (toRMat U).mulVec (τ A) + s
        - (toRMat (U * A * invMat U)).mulVec s + toRVec n) :
    (fixBitG τ' (U * A * invMat U) (U * B * invMat U) ↔ fixBitG τ A B) := by
  have hsub' : toRMat (U * B * invMat U) - 1 = toRMat (U * (B - 1) * invMat U) := by
    conv_lhs => rw [← toRMat_one]
    rw [← toRMat_sub, ← conj_sub_one hU B]
  have h1 : fixBitG τ A B
      ↔ ((toRMat (B - 1)).mulVec (vA τ A) ∈ latImg ((B - 1) * NZ A)) := by
    unfold fixBitG
    rw [show toRMat B - 1 = toRMat (B - 1) from by rw [toRMat_sub, toRMat_one]]
  have h2 : fixBitG τ' (U * A * invMat U) (U * B * invMat U)
      ↔ ((toRMat (U * (B - 1) * invMat U)).mulVec (vA τ' (U * A * invMat U))
          ∈ latImg ((U * (B - 1) * invMat U) * NZ (U * A * invMat U))) := by
    unfold fixBitG
    rw [hsub', show U * B * invMat U - 1 = U * (B - 1) * invMat U from (conj_sub_one hU B).symm]
  rw [h1, h2]
  exact (mem_conj_transport hU τ τ' s A (B - 1) hc).symm

/-- The `afix` bit is transported by conjugation. -/
theorem afixBitG_conj {U : IMat} (hU : IsUnit U.det) {τ τ' : IMat → Fin 3 → ℝ} {s : Fin 3 → ℝ}
    {A B : IMat}
    (hc : ∃ n : IVec, τ' (U * A * invMat U) = (toRMat U).mulVec (τ A) + s
        - (toRMat (U * A * invMat U)).mulVec s + toRVec n) :
    (afixBitG τ' (U * A * invMat U) (U * B * invMat U) ↔ afixBitG τ A B) := by
  have hadd' : toRMat (U * B * invMat U) + 1 = toRMat (U * (B + 1) * invMat U) := by
    conv_lhs => rw [← toRMat_one]
    rw [← toRMat_add, ← conj_add_one hU B]
  have h1 : afixBitG τ A B
      ↔ ((toRMat (B + 1)).mulVec (vA τ A) ∈ latImg ((B + 1) * NZ A)) := by
    unfold afixBitG
    rw [show toRMat B + 1 = toRMat (B + 1) from by rw [toRMat_add, toRMat_one]]
  have h2 : afixBitG τ' (U * A * invMat U) (U * B * invMat U)
      ↔ ((toRMat (U * (B + 1) * invMat U)).mulVec (vA τ' (U * A * invMat U))
          ∈ latImg ((U * (B + 1) * invMat U) * NZ (U * A * invMat U))) := by
    unfold afixBitG
    rw [hadd', show U * B * invMat U + 1 = U * (B + 1) * invMat U from (conj_add_one hU B).symm]
  rw [h1, h2]
  exact (mem_conj_transport hU τ τ' s A (B + 1) hc).symm

/-- Naturality of the six pair bits under conjugation. -/
theorem pairBitsG_conj {U : IMat} (hU : IsUnit U.det) (τ τ' : IMat → Fin 3 → ℝ)
    (s : Fin 3 → ℝ) (A B : IMat)
    (hc : ∃ n : IVec, τ' (U * A * invMat U) = (toRMat U).mulVec (τ A) + s
        - (toRMat (U * A * invMat U)).mulVec s + toRVec n) :
    pairBitsG τ' (U * A * invMat U) (U * B * invMat U) = pairBitsG τ A B := by
  have hfix := fixBitG_conj (A := A) (B := B) hU hc
  have hafix := afixBitG_conj (A := A) (B := B) hU hc
  have ht0 : (latImg (U * A * invMat U - 1) ≤ latImg (U * B * invMat U - 1)
      ↔ latImg (A - 1) ≤ latImg (B - 1)) := by
    rw [← conj_sub_one hU A, ← conj_sub_one hU B, latImg_le_conj_iff hU]
  have ht1 : (latImg (U * A * invMat U + 1) ≤ latImg (U * B * invMat U + 1)
      ↔ latImg (A + 1) ≤ latImg (B + 1)) := by
    rw [← conj_add_one hU A, ← conj_add_one hU B, latImg_le_conj_iff hU]
  have ht2 : (latImg (U * A * invMat U - 1) ≤ latImg (U * B * invMat U + 1)
      ↔ latImg (A - 1) ≤ latImg (B + 1)) := by
    rw [← conj_sub_one hU A, ← conj_add_one hU B, latImg_le_conj_iff hU]
  have ht3 : (latImg (U * A * invMat U + 1) ≤ latImg (U * B * invMat U - 1)
      ↔ latImg (A + 1) ≤ latImg (B - 1)) := by
    rw [← conj_add_one hU A, ← conj_sub_one hU B, latImg_le_conj_iff hU]
  simp only [pairBitsG, hfix, hafix, ht0, ht1, ht2, ht3]

end PSep

end Work.SGsep
