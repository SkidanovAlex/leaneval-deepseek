import Mathlib
import Submission.Work.Gen.EulerModel
import Submission.Work.Gen.EulerDefs
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

open Work.Projective Work.Whitney

/-! # `CbigInv` is a two-sided inverse of `CbigCLM`

The copy-order shuffle `CbigCLM = sumShuffle ∘ pairing` of the Euler target, and its declared
inverse `CbigInv = pairingInv ∘ sumShuffle⁻¹`.  It therefore suffices to show that `pairingInv` is
a two-sided inverse of `pairing`; the rest is the `≃L`-bookkeeping of `sumShuffle`.

`pairing` sends `(u, v)` to the nested tuple whose `k`-th `ℂ²`-component is the pair
`(u k, v k)`, and `pairingInv` reads those components back.  All the work is the explicit
coordinate computation below. -/

/-- `zipK k` of `pairing (u, v)` reads off the `k`-th coordinate of `u`. -/
theorem cbig_zipK_pairing (u v : EuclideanSpace ℂ (Fin 5)) (k : Fin 5) :
    zipK k (pairing (u, v)) = toC1 (coord5 k u) := by
  fin_cases k <;>
  · simp only [zipK, pairing, pairK, nestK,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    simp

/-- `zipK' k` of `pairing (u, v)` reads off the `k`-th coordinate of `v`. -/
theorem cbig_zipK'_pairing (u v : EuclideanSpace ℂ (Fin 5)) (k : Fin 5) :
    zipK' k (pairing (u, v)) = toC1 (coord5 k v) := by
  fin_cases k <;>
  · simp only [zipK', pairing, pairK, nestK,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    simp

/-- `pairingInvL` inverts `pairing` on the left factor. -/
theorem cbig_pairingInvL_pairing (u v : EuclideanSpace ℂ (Fin 5)) :
    pairingInvL (pairing (u, v)) = wlpC 5 u := by
  ext k
  simp only [pairingInvL, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply]
  rw [cbig_zipK_pairing]
  simp [coord5]

/-- `pairingInvR` inverts `pairing` on the right factor. -/
theorem cbig_pairingInvR_pairing (u v : EuclideanSpace ℂ (Fin 5)) :
    pairingInvR (pairing (u, v)) = wlpC 5 v := by
  ext k
  simp only [pairingInvR, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply]
  rw [cbig_zipK'_pairing]
  simp [coord5]

/-- The left inverse identity. -/
theorem cbig_pairingInv_comp_pairing : pairingInv.comp pairing = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨u, v⟩ := x
  rw [ContinuousLinearMap.comp_apply, one_apply_eq_self]
  rw [pairingInv, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      cbig_pairingInvL_pairing, cbig_pairingInvR_pairing]
  simp

/-- `nestK k` of `pairing (u, v)` is the `k`-th coordinate pair. -/
theorem cbig_nestK_pairing (u v : EuclideanSpace ℂ (Fin 5)) (k : Fin 5) :
    nestK k (pairing (u, v)) = pairK k (u, v) := by
  fin_cases k <;>
  · simp only [nestK, pairing, ContinuousLinearMap.prod_apply]
    simp

/-- `coord5 k` of the inverse of `wlpC` evaluates the `k`-th coordinate. -/
theorem cbig_coord5_wlpC_symm (y : Fin 5 → ℂ) (k : Fin 5) :
    coord5 k ((wlpC 5).symm y) = y k := by
  simp [coord5]

/-- Unfolding `pairK` on a pair. -/
theorem cbig_pairK_apply (u v : EuclideanSpace ℂ (Fin 5)) (k : Fin 5) :
    pairK k (u, v) =
      (Work.Whitney.sumFibreC 1 1) (toC1 (coord5 k u), toC1 (coord5 k v)) := by
  simp [pairK]

/-- The components of `pairing (pairingInv x)` recover those of `x`. -/
theorem cbig_nestK_pairing_pairingInv (x : Nested5) (k : Fin 5) :
    nestK k (pairing (pairingInv x)) = nestK k x := by
  have h1 : (pairingInv x).1 = (wlpC 5).symm (pairingInvL x) := by
    simp [pairingInv]
  have h2 : (pairingInv x).2 = (wlpC 5).symm (pairingInvR x) := by
    simp [pairingInv]
  rw [← Prod.mk.eta (p := pairingInv x)]
  rw [cbig_nestK_pairing, cbig_pairK_apply]
  rw [h1, h2, cbig_coord5_wlpC_symm, cbig_coord5_wlpC_symm]
  have hL : toC1 ((pairingInvL x) k) = zipK k x := by
    simp [pairingInvL]
  have hR : toC1 ((pairingInvR x) k) = zipK' k x := by
    simp [pairingInvR]
  rw [hL, hR]
  have hz : (zipK k x, zipK' k x) = (Work.Whitney.sumFibreC 1 1).symm (nestK k x) := by
    simp only [zipK, zipK', ContinuousLinearMap.comp_apply]
    exact Prod.mk.eta
  rw [hz]
  simp

/-- A nested vector is determined by its five `ℂ²`-components. -/
theorem cbig_nested_ext {a b : Nested5} (h : ∀ k : Fin 5, nestK k a = nestK k b) : a = b := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := a
  obtain ⟨b0, b1, b2, b3, b4⟩ := b
  have h0 : a0 = b0 := by simpa [nestK] using h 0
  have h1 : a1 = b1 := by simpa [nestK] using h 1
  have h2 : a2 = b2 := by simpa [nestK] using h 2
  have h3 : a3 = b3 := by simpa [nestK] using h 3
  have h4 : a4 = b4 := by simpa [nestK] using h 4
  rw [h0, h1, h2, h3, h4]

/-- The right inverse identity. -/
theorem cbig_pairing_comp_pairingInv : pairing.comp pairingInv = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, one_apply_eq_self]
  apply cbig_nested_ext
  intro k
  exact cbig_nestK_pairing_pairingInv x k

/-- `sumShuffle⁻¹ ∘ sumShuffle = 1`. -/
theorem cbig_sumShuffle_symm_comp :
    ((sumShuffle.symm : EuclideanSpace ℂ (Fin 10) →L[ℂ] Nested5)).comp
      (sumShuffle : Nested5 →L[ℂ] EuclideanSpace ℂ (Fin 10)) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, one_apply_eq_self]
  simp

/-- `sumShuffle ∘ sumShuffle⁻¹ = 1`. -/
theorem cbig_sumShuffle_comp_symm :
    (sumShuffle : Nested5 →L[ℂ] EuclideanSpace ℂ (Fin 10)).comp
      ((sumShuffle.symm : EuclideanSpace ℂ (Fin 10) →L[ℂ] Nested5)) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, one_apply_eq_self]
  simp

theorem Cbig_inv : Work.Gen.CbigInv.comp Work.Gen.CbigCLM = 1 ∧ Work.Gen.CbigCLM.comp Work.Gen.CbigInv = 1 := by
  constructor
  · rw [CbigInv, CbigCLM, ContinuousLinearMap.comp_assoc]
    have h : ((sumShuffle.symm : EuclideanSpace ℂ (Fin 10) →L[ℂ] Nested5)).comp
        ((sumShuffle : Nested5 →L[ℂ] EuclideanSpace ℂ (Fin 10)).comp pairing) = pairing := by
      rw [← ContinuousLinearMap.comp_assoc, cbig_sumShuffle_symm_comp]
      apply ContinuousLinearMap.ext
      intro x
      simp
    rw [h, cbig_pairingInv_comp_pairing]
  · rw [CbigInv, CbigCLM, ContinuousLinearMap.comp_assoc]
    have h : pairing.comp
        (pairingInv.comp (sumShuffle.symm : EuclideanSpace ℂ (Fin 10) →L[ℂ] Nested5)) =
        (sumShuffle.symm : EuclideanSpace ℂ (Fin 10) →L[ℂ] Nested5) := by
      rw [← ContinuousLinearMap.comp_assoc, cbig_pairing_comp_pairingInv]
      apply ContinuousLinearMap.ext
      intro x
      simp
    rw [h, cbig_sumShuffle_comp_symm]

end Work.Gen
