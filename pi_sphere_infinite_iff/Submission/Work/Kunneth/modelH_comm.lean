import Mathlib
import Submission.Work.Kunneth.ModelContr

/-!
# The contraction identity for the Koszul tensor product

`Work.Kunneth.modelH` is the contracting homotopy `s ⊗ 1 + P ⊗ t` of the tensor product of two
contracted complexes, and `Work.Kunneth.modelQ` is its deficiency `P ⊗ Q`.  This file proves the
commutation identity `Work.Kunneth.modelH_comm`:

`d (H z) + H (d z) = z - Q z`

for every `z` in degree `m+1`, i.e. that `modelH` is a contraction of the Koszul tensor product.

The proof is an explicit computation: on a generator `lof pq (x ⊗ y)` the identity is checked
component by component (bidegree by bidegree), using the contraction identities
`d s + s d = 1 - P` of `C` and `D`, the compatibility `d P + P d = 0` of the deficiency, and the
vanishing of the deficiency in positive degrees.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- Two elements of `tpX C D n` are equal as soon as all their components are: the composite of
the projections out of a direct sum is injective. -/
lemma tpX_ext_components {C D : ChainComplex (ModuleCat ℤ) ℕ} {n : ℕ} {L R : tpX C D n}
    (h : ∀ rs : tpIdx n,
      (DirectSum.component ℤ (tpIdx n) (fun pq => tpSummand C D pq.1.1 pq.1.2) rs) L
        = (DirectSum.component ℤ (tpIdx n) (fun pq => tpSummand C D pq.1.1 pq.1.2) rs) R) :
    L = R := by
  rw [DirectSum.ext_iff]
  intro rs
  exact h rs

/-- **The contraction identity, on a generator of the tensor product.** -/
lemma modelH_comm_gen (C D : ChainComplex (ModuleCat ℤ) ℕ) (cC : ModelContr C)
    (cD : ModelContr D) (m : ℕ) (pq : tpIdx (m+1)) (x : ↥(C.X pq.1.1)) (y : ↥(D.X pq.1.2)) :
    tpD C D (m+1) (modelH cC cD (m+1) (tpLof C D (m+1) pq (x ⊗ₜ[ℤ] y)))
      + modelH cC cD m (tpD C D m (tpLof C D (m+1) pq (x ⊗ₜ[ℤ] y)))
      = tpLof C D (m+1) pq (x ⊗ₜ[ℤ] y)
        - modelQ cC cD (m+1) (tpLof C D (m+1) pq (x ⊗ₜ[ℤ] y)) := by
  apply tpX_ext_components
  intro rs
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  rcases p with _ | P
  · rcases q with _ | Q
    · omega
    · -- `p = 0`, `q = Q + 1`
      rw [map_add, map_sub, modelH_tmul, modelQ_tmul, map_add, map_add, tpD_lof_tmul,
        tpD_lof_tmul, tpD_lof_tmul]
      simp only [tpIdxL, tpIdxR]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> try (exfalso; omega)
      repeat (first | rw [map_add] | rw [map_zsmul] | rw [modelH_tmul] | rw [zsmul_add])
      simp only [tpIdxL, tpIdxR]
      rw [DirectSum.component, DFinsupp.lapply_apply, DirectSum.lof_eq_of, DirectSum.of_apply]
      repeat (first | rw [DFinsupp.lapply_apply] | rw [DirectSum.lof_eq_of] | rw [DirectSum.of_apply])
      by_cases hA : rs.1 = (0, Q+1)
      · have hrsA : rs = ⟨(0,Q+1), hpq⟩ := Subtype.ext hA
        rw [hrsA]
        have hne1 : ¬ ((⟨(1,Q), by omega⟩ : tpIdx (m+1)) = ⟨(0,Q+1),hpq⟩) := by
          intro hh; simp only [Subtype.mk.injEq, Prod.mk.injEq] at hh; omega
        simp only [Nat.succ_sub_one, hne1, dif_pos trivial, dif_neg (not_false), pow_zero, pow_one,
          one_zsmul, zsmul_zero, add_zero, zero_add, sub_zero, map_zero, DFinsupp.zero_apply]
        have hQ : (cD.P (Q+1)) y = 0 := by simp [cD.P_succ Q]
        rw [hQ, TensorProduct.tmul_zero, sub_zero]
        rw [add_assoc, ← TensorProduct.tmul_add]
        rw [cD.s_succ Q y]
        rw [hQ, sub_zero]
        rw [cC.s_zero x]
        rw [TensorProduct.sub_tmul]
        abel
      · by_cases hB : rs.1 = (1, Q)
        · have hrsB : rs = ⟨(1,Q), by omega⟩ := Subtype.ext hB
          rw [hrsB]
          have hne1 : ¬ ((⟨(0,Q+1), by omega⟩ : tpIdx (m+1)) = ⟨(1,Q), by omega⟩) := by
            intro hh; simp only [Subtype.mk.injEq, Prod.mk.injEq] at hh; omega
          simp only [Nat.succ_sub_one, hne1, dif_pos trivial, dif_neg (not_false), pow_zero,
            pow_one, one_zsmul, zsmul_zero, add_zero, zero_add, sub_zero, map_zero,
            DFinsupp.zero_apply]
          abel
        · have hne1 : ¬ ((⟨(0,Q+1), by omega⟩ : tpIdx (m+1)) = rs) :=
            fun hh => hA (congrArg Subtype.val hh).symm
          have hne2 : ¬ ((⟨(1,Q), by omega⟩ : tpIdx (m+1)) = rs) :=
            fun hh => hB (congrArg Subtype.val hh).symm
          simp only [Nat.succ_sub_one, hne1, hne2, dif_neg (not_false), pow_zero, pow_one,
            one_zsmul, zsmul_zero, add_zero, zero_add, sub_zero, map_zero, DFinsupp.zero_apply]
  · rcases q with _ | Q
    · -- `p = P + 1`, `q = 0`
      rw [map_add, map_sub, modelH_tmul, modelQ_tmul, map_add, map_add, tpD_lof_tmul,
        tpD_lof_tmul, tpD_lof_tmul]
      simp only [tpIdxL, tpIdxR]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> try (exfalso; omega)
      repeat (first | rw [map_add] | rw [map_zsmul] | rw [modelH_tmul] | rw [zsmul_add])
      simp only [tpIdxL, tpIdxR]
      rw [DirectSum.component, DFinsupp.lapply_apply, DirectSum.lof_eq_of, DirectSum.of_apply]
      repeat (first | rw [DFinsupp.lapply_apply] | rw [DirectSum.lof_eq_of] | rw [DirectSum.of_apply])
      by_cases hA : rs.1 = (P+1, 0)
      · have hrsA : rs = ⟨(P+1,0), hpq⟩ := Subtype.ext hA
        rw [hrsA]
        have hne1 : ¬ ((⟨(P,1), by omega⟩ : tpIdx (m+1)) = ⟨(P+1,0),hpq⟩) := by
          intro hh; simp only [Subtype.mk.injEq, Prod.mk.injEq] at hh; omega
        simp only [Nat.succ_sub_one, hne1, dif_pos trivial, dif_neg (not_false), pow_zero, pow_one,
          one_zsmul, zsmul_zero, add_zero, zero_add, sub_zero, map_zero, DFinsupp.zero_apply]
        have hP : (cC.P (P+1)) x = 0 := by simp [cC.P_succ P]
        rw [hP]
        simp only [TensorProduct.zero_tmul, zsmul_zero, add_zero, sub_zero]
        rw [← TensorProduct.add_tmul]
        rw [cC.s_succ P x]
        rw [hP, sub_zero]
      · by_cases hB : rs.1 = (P, 1)
        · have hrsB : rs = ⟨(P,1), by omega⟩ := Subtype.ext hB
          rw [hrsB]
          have hne1 : ¬ ((⟨(P+1,0), by omega⟩ : tpIdx (m+1)) = ⟨(P,1), by omega⟩) := by
            intro hh; simp only [Subtype.mk.injEq, Prod.mk.injEq] at hh; omega
          simp only [Nat.succ_sub_one, hne1, dif_pos trivial, dif_neg (not_false), pow_zero,
            pow_one, one_zsmul, zsmul_zero, add_zero, zero_add, sub_zero, map_zero,
            DFinsupp.zero_apply]
          rw [← TensorProduct.add_tmul]
          have hPd : ((C.d (P+1) P).hom (cC.P (P+1) x) + (cC.P P) ((C.d (P+1) P).hom x)) = 0 := by
            simpa only [Nat.succ_sub_one] using cC.Pd (P+1) x
          rw [hPd, TensorProduct.zero_tmul]
        · have hne1 : ¬ ((⟨(P+1,0), by omega⟩ : tpIdx (m+1)) = rs) :=
            fun hh => hA (congrArg Subtype.val hh).symm
          have hne2 : ¬ ((⟨(P,1), by omega⟩ : tpIdx (m+1)) = rs) :=
            fun hh => hB (congrArg Subtype.val hh).symm
          simp only [Nat.succ_sub_one, hne1, hne2, dif_neg (not_false), pow_zero, pow_one,
            one_zsmul, zsmul_zero, add_zero, zero_add, sub_zero, map_zero, DFinsupp.zero_apply]
    · -- `p = P + 1`, `q = Q + 1`
      rw [map_add, map_sub, modelH_tmul, modelQ_tmul, map_add, map_add, tpD_lof_tmul,
        tpD_lof_tmul, tpD_lof_tmul]
      simp only [tpIdxL, tpIdxR]
      rw [dif_pos (show (1:ℕ) ≤ P+1+1 by omega), dif_pos (show (1:ℕ) ≤ Q+1 by omega),
        dif_pos (show (1:ℕ) ≤ P+1 by omega), dif_pos (show (1:ℕ) ≤ Q+1+1 by omega)]
      rw [dif_pos (show (1:ℕ) ≤ P+1 by omega), dif_pos (show (1:ℕ) ≤ Q+1 by omega)]
      repeat (first | rw [map_add] | rw [map_zsmul] | rw [modelH_tmul] | rw [zsmul_add])
      simp only [tpIdxL, tpIdxR]
      rw [DirectSum.component, DFinsupp.lapply_apply, DirectSum.lof_eq_of, DirectSum.of_apply]
      repeat (first | rw [DFinsupp.lapply_apply] | rw [DirectSum.lof_eq_of] | rw [DirectSum.of_apply])
      by_cases hA : rs.1 = (P+1,Q+1)
      · have hrsA : rs = ⟨(P+1,Q+1), hpq⟩ := Subtype.ext hA
        rw [hrsA]
        have hne1 : ¬ ((⟨(P+1+1,Q), by omega⟩ : tpIdx (m+1)) = ⟨(P+1,Q+1),hpq⟩) := by
          intro hh; simp only [Subtype.mk.injEq, Prod.mk.injEq] at hh; omega
        have hne2 : ¬ ((⟨(P,Q+1+1), by omega⟩ : tpIdx (m+1)) = ⟨(P+1,Q+1),hpq⟩) := by
          intro hh; simp only [Subtype.mk.injEq, Prod.mk.injEq] at hh; omega
        simp only [Nat.succ_sub_one, hne1, hne2, dif_pos trivial, dif_neg (not_false), zsmul_zero,
          add_zero, zero_add, sub_zero]
        have hP : (cC.P (P+1)) x = 0 := by simp [cC.P_succ P]
        rw [hP]
        simp only [TensorProduct.zero_tmul, zsmul_zero, add_zero, sub_zero]
        rw [← TensorProduct.add_tmul]
        rw [cC.s_succ P x]
        rw [hP]
        simp
      · by_cases hB : rs.1 = (P+1+1, Q+1-1)
        · have hrsB : rs = ⟨(P+2,Q), by omega⟩ := Subtype.ext (by rw [hB]; rfl)
          rw [hrsB]
          have hne1 : ¬ ((⟨(P+1,Q+1), by omega⟩ : tpIdx (m+1)) = ⟨(P+2,Q), by omega⟩) := by
            intro hh; simp only [Subtype.mk.injEq, Prod.mk.injEq] at hh; omega
          have hne2 : ¬ ((⟨(P,Q+2), by omega⟩ : tpIdx (m+1)) = ⟨(P+2,Q), by omega⟩) := by
            intro hh; simp only [Subtype.mk.injEq, Prod.mk.injEq] at hh; omega
          simp only [Nat.succ_sub_one, hne1, hne2, dif_pos trivial, dif_neg (not_false), zsmul_zero,
            add_zero, zero_add, sub_zero]
          rw [← add_zsmul]
          have hsign : (-1:ℤ)^(P+1+1) + (-1)^(P+1) = 0 := by rw [pow_succ]; ring
          rw [hsign, zero_zsmul]
        · by_cases hC : rs.1 = (P+1-1, Q+1+1)
          · have hrsC : rs = ⟨(P,Q+2), by omega⟩ := Subtype.ext (by rw [hC]; rfl)
            rw [hrsC]
            have hne1 : ¬ ((⟨(P+1,Q+1), by omega⟩ : tpIdx (m+1)) = ⟨(P,Q+2), by omega⟩) := by
              intro hh; simp only [Subtype.mk.injEq, Prod.mk.injEq] at hh; omega
            have hne2 : ¬ ((⟨(P+2,Q), by omega⟩ : tpIdx (m+1)) = ⟨(P,Q+2), by omega⟩) := by
              intro hh; simp only [Subtype.mk.injEq, Prod.mk.injEq] at hh; omega
            simp only [Nat.succ_sub_one, hne1, hne2, dif_pos trivial, dif_neg (not_false),
              zsmul_zero, add_zero, zero_add, sub_zero]
            rw [← TensorProduct.add_tmul]
            have hPd : ((C.d (P+1) P).hom (cC.P (P+1) x) + (cC.P P) ((C.d (P+1) P).hom x)) = 0 := by
              simpa only [Nat.succ_sub_one] using cC.Pd (P+1) x
            rw [hPd, TensorProduct.zero_tmul]
          · have hne1 : ¬ ((⟨(P+1,Q+1), by omega⟩ : tpIdx (m+1)) = rs) :=
              fun hh => hA (congrArg Subtype.val hh).symm
            have hne2 : ¬ ((⟨(P+2,Q), by omega⟩ : tpIdx (m+1)) = rs) :=
              fun hh => hB (congrArg Subtype.val hh).symm
            have hne3 : ¬ ((⟨(P,Q+2), by omega⟩ : tpIdx (m+1)) = rs) :=
              fun hh => hC (congrArg Subtype.val hh).symm
            simp only [Nat.succ_sub_one, hne1, hne2, hne3, dif_neg (not_false), zsmul_zero, add_zero,
              zero_add, sub_zero]

/-- **The contraction identity for the Koszul tensor product.** -/
theorem modelH_comm (C D : ChainComplex (ModuleCat ℤ) ℕ) (cC : ModelContr C) (cD : ModelContr D)
    (m : ℕ) (z : tpX C D (m+1)) :
    tpD C D (m+1) (modelH cC cD (m+1) z) + modelH cC cD m (tpD C D m z)
      = z - modelQ cC cD (m+1) z := by
  have hlin : (tpD C D (m+1)).comp (modelH cC cD (m+1))
      + (modelH cC cD m).comp (tpD C D m)
      = LinearMap.id - modelQ cC cD (m+1) := by
    apply DirectSum.linearMap_ext
    intro pq
    apply TensorProduct.ext'
    intro x y
    have h := modelH_comm_gen C D cC cD m pq x y
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply] using h
  have hz := congrArg (fun (f : tpX C D (m+1) →ₗ[ℤ] tpX C D (m+1)) => f z) hlin
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply] using hz

end

end Work.Kunneth
