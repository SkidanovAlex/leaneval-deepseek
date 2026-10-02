import Mathlib
import Submission.Work.GenTwo.Split
import Submission.Work.Gen.EulerDefs
import Submission.Work.Gen.Cbig_inv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The copy-order shuffle of the three-fold sum `(ℂ ⊗ O(1))³` over `ℂP²`

The `n = 2` instance of `Submission/Work/Gen/EulerModel.lean` / `Cbig_inv.lean` /
`cbigDiagCLM.lean`: the target of the complexified Euler sequence is
`Work.Gen.E2.Tgt = lineC 2 ⊕ (lineC 2 ⊕ lineC 2)`, and `CbigCLM : ℂ³ × ℂ³ → ℂ⁶` reorders the pair
(G-block, H-block) into the copy order of the three summands, so that the diagonal transition of
`Tgt` becomes the block scaling `diag(λ⁻¹, λ)` of that pair.
-/

namespace Work.Gen.E2

open Work.Projective Work.Whitney

noncomputable section

/-! ## The target bundle -/

/-- The index type of `lineC 2 = O(1) ⊕ O(-1)` over `ℂP²`. -/
abbrev Idx2 : Type := Fin 3 × Fin 3

/-- **`(ℂ ⊗ O(1))³ = (O(1) ⊕ O(-1))³` over `ℂP²`**: the right-hand side of the complexified Euler
sequence. -/
abbrev Tgt : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin (2 + (2 + 2))))
    (Idx2 × (Idx2 × Idx2)) :=
  whitneySum (lineC 2) (whitneySum (lineC 2) (lineC 2))

/-- The index type of the target bundle. -/
abbrev TgtIdx : Type := Idx2 × (Idx2 × Idx2)

/-- The diagonal index over the chart `p`. -/
def diagIdx (p : Fin 3) : TgtIdx := ((p, p), ((p, p), (p, p)))

@[simp] theorem Tgt_baseSet_diagIdx (p : Fin 3) : Tgt.baseSet (diagIdx p) = chartSet p := by
  show (whitneySum (lineC 2) (whitneySum (lineC 2) (lineC 2))).baseSet
    ((p, p), ((p, p), (p, p))) = chartSet p
  simp only [whitneySum_baseSet, lineC_baseSet, Set.inter_self]

/-! ## The nested triple of `ℂ²`s -/

/-- The nested type `ℂ² × (ℂ² × ℂ²)`, the fibre of `Tgt` before the shuffle. -/
abbrev Nested3 : Type :=
  EuclideanSpace ℂ (Fin 2) × (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2))

/-- The `k`-th coordinate functional of `ℂ³`. -/
noncomputable def coord3 (k : Fin 3) : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj k).comp (wlpC 3 : EuclideanSpace ℂ (Fin 3) →L[ℂ] (Fin 3 → ℂ))

/-- The `k`-th pair of two vectors of `ℂ³`, as a vector of `ℂ²`. -/
noncomputable def pairK (k : Fin 3) :
    (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (sumFibreC 1 1).toContinuousLinearMap.comp
    (((toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)).comp
        ((coord3 k).comp (ContinuousLinearMap.fst ℂ _ _))).prod
      ((toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)).comp
        ((coord3 k).comp (ContinuousLinearMap.snd ℂ _ _))))

/-- The `k`-th component of `Nested3`. -/
noncomputable def nestK (k : Fin 3) : Nested3 →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  match k with
  | 0 => ContinuousLinearMap.fst ℂ _ _
  | 1 => (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  | 2 => (ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)

/-- The `k`-th "first" coordinate of a nested vector, as an element of `ℂ¹`. -/
noncomputable def zipK (k : Fin 3) : Nested3 →L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  ((ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin 1)) (EuclideanSpace ℂ (Fin 1))).comp
    ((sumFibreC 1 1).symm.toContinuousLinearMap.comp (nestK k)))

/-- The `k`-th "second" coordinate of a nested vector, as an element of `ℂ¹`. -/
noncomputable def zipK' (k : Fin 3) : Nested3 →L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  ((ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin 1)) (EuclideanSpace ℂ (Fin 1))).comp
    ((sumFibreC 1 1).symm.toContinuousLinearMap.comp (nestK k)))

/-- The "pairing" `ℂ³ × ℂ³ → Nested3`. -/
noncomputable def pairing :
    (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) →L[ℂ] Nested3 :=
  (pairK 0).prod ((pairK 1).prod (pairK 2))

/-- The nested `sumFibreC` shuffle `Nested3 ≃L ℂ⁶`. -/
noncomputable def sumShuffle : Nested3 ≃L[ℂ] EuclideanSpace ℂ (Fin (2 + (2 + 2))) :=
  let e2 := ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 2))
  let Y2 : (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) ≃L[ℂ]
      EuclideanSpace ℂ (Fin (2 + 2)) := sumFibreC 2 2
  (ContinuousLinearEquiv.prodCongr e2 Y2).trans (sumFibreC 2 (2 + 2))

/-- The "unpairing": read a nested vector of `ℂ²`s back into a pair of vectors of `ℂ³`. -/
noncomputable def pairingInvL : Nested3 →L[ℂ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi (fun k : Fin 3 =>
    (toC1.symm : EuclideanSpace ℂ (Fin 1) →L[ℂ] ℂ).comp (zipK k))

noncomputable def pairingInvR : Nested3 →L[ℂ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi (fun k : Fin 3 =>
    (toC1.symm : EuclideanSpace ℂ (Fin 1) →L[ℂ] ℂ).comp (zipK' k))

/-- The inverse of `pairing`. -/
noncomputable def pairingInv :
    Nested3 →L[ℂ] (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) :=
  ((wlpC 3).symm.toContinuousLinearMap.comp pairingInvL).prod
    ((wlpC 3).symm.toContinuousLinearMap.comp pairingInvR)

/-- The copy-order shuffle of `Tgt`, as a continuous linear map. -/
noncomputable def CbigCLM :
    (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) →L[ℂ] EuclideanSpace ℂ (Fin (2 + (2 + 2))) :=
  sumShuffle.toContinuousLinearMap.comp pairing

/-- Its inverse. -/
noncomputable def CbigInv :
    EuclideanSpace ℂ (Fin (2 + (2 + 2))) →L[ℂ] (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) :=
  pairingInv.comp sumShuffle.symm.toContinuousLinearMap

/-! ## `CbigInv` is a two-sided inverse of `CbigCLM` -/

/-- `zipK k` of `pairing (u, v)` reads off the `k`-th coordinate of `u`. -/
theorem cbig_zipK_pairing (u v : EuclideanSpace ℂ (Fin 3)) (k : Fin 3) :
    zipK k (pairing (u, v)) = toC1 (coord3 k u) := by
  fin_cases k <;>
  · simp only [zipK, pairing, pairK, nestK,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    simp

/-- `zipK' k` of `pairing (u, v)` reads off the `k`-th coordinate of `v`. -/
theorem cbig_zipK'_pairing (u v : EuclideanSpace ℂ (Fin 3)) (k : Fin 3) :
    zipK' k (pairing (u, v)) = toC1 (coord3 k v) := by
  fin_cases k <;>
  · simp only [zipK', pairing, pairK, nestK,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    simp

/-- `pairingInvL` inverts `pairing` on the left factor. -/
theorem cbig_pairingInvL_pairing (u v : EuclideanSpace ℂ (Fin 3)) :
    pairingInvL (pairing (u, v)) = wlpC 3 u := by
  ext k
  simp only [pairingInvL, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply]
  rw [cbig_zipK_pairing]
  simp [coord3]

/-- `pairingInvR` inverts `pairing` on the right factor. -/
theorem cbig_pairingInvR_pairing (u v : EuclideanSpace ℂ (Fin 3)) :
    pairingInvR (pairing (u, v)) = wlpC 3 v := by
  ext k
  simp only [pairingInvR, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply]
  rw [cbig_zipK'_pairing]
  simp [coord3]

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
theorem cbig_nestK_pairing (u v : EuclideanSpace ℂ (Fin 3)) (k : Fin 3) :
    nestK k (pairing (u, v)) = pairK k (u, v) := by
  fin_cases k <;>
  · simp only [nestK, pairing, ContinuousLinearMap.prod_apply]
    simp

/-- `coord3 k` of the inverse of `wlpC` evaluates the `k`-th coordinate. -/
theorem cbig_coord3_wlpC_symm (y : Fin 3 → ℂ) (k : Fin 3) :
    coord3 k ((wlpC 3).symm y) = y k := by
  simp [coord3]

/-- Unfolding `pairK` on a pair. -/
theorem cbig_pairK_apply (u v : EuclideanSpace ℂ (Fin 3)) (k : Fin 3) :
    pairK k (u, v) =
      (Work.Whitney.sumFibreC 1 1) (toC1 (coord3 k u), toC1 (coord3 k v)) := by
  simp [pairK]

/-- The components of `pairing (pairingInv x)` recover those of `x`. -/
theorem cbig_nestK_pairing_pairingInv (x : Nested3) (k : Fin 3) :
    nestK k (pairing (pairingInv x)) = nestK k x := by
  have h1 : (pairingInv x).1 = (wlpC 3).symm (pairingInvL x) := by
    simp [pairingInv]
  have h2 : (pairingInv x).2 = (wlpC 3).symm (pairingInvR x) := by
    simp [pairingInv]
  rw [← Prod.mk.eta (p := pairingInv x)]
  rw [cbig_nestK_pairing, cbig_pairK_apply]
  rw [h1, h2, cbig_coord3_wlpC_symm, cbig_coord3_wlpC_symm]
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

/-- A nested vector is determined by its three `ℂ²`-components. -/
theorem cbig_nested_ext {a b : Nested3} (h : ∀ k : Fin 3, nestK k a = nestK k b) : a = b := by
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  have h0 : a0 = b0 := by simpa [nestK] using h 0
  have h1 : a1 = b1 := by simpa [nestK] using h 1
  have h2 : a2 = b2 := by simpa [nestK] using h 2
  rw [h0, h1, h2]

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
    ((sumShuffle.symm : EuclideanSpace ℂ (Fin (2 + (2 + 2))) →L[ℂ] Nested3)).comp
      (sumShuffle : Nested3 →L[ℂ] EuclideanSpace ℂ (Fin (2 + (2 + 2)))) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, one_apply_eq_self]
  simp

/-- `sumShuffle ∘ sumShuffle⁻¹ = 1`. -/
theorem cbig_sumShuffle_comp_symm :
    (sumShuffle : Nested3 →L[ℂ] EuclideanSpace ℂ (Fin (2 + (2 + 2)))).comp
      ((sumShuffle.symm : EuclideanSpace ℂ (Fin (2 + (2 + 2))) →L[ℂ] Nested3)) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, one_apply_eq_self]
  simp

theorem Cbig_inv : CbigInv.comp CbigCLM = 1 ∧ CbigCLM.comp CbigInv = 1 := by
  constructor
  · rw [CbigInv, CbigCLM, ContinuousLinearMap.comp_assoc]
    have h : ((sumShuffle.symm : EuclideanSpace ℂ (Fin (2 + (2 + 2))) →L[ℂ] Nested3)).comp
        ((sumShuffle : Nested3 →L[ℂ] EuclideanSpace ℂ (Fin (2 + (2 + 2)))).comp pairing) = pairing := by
      rw [← ContinuousLinearMap.comp_assoc, cbig_sumShuffle_symm_comp]
      apply ContinuousLinearMap.ext
      intro x
      simp
    rw [h, cbig_pairingInv_comp_pairing]
  · rw [CbigInv, CbigCLM, ContinuousLinearMap.comp_assoc]
    have h : pairing.comp
        (pairingInv.comp (sumShuffle.symm : EuclideanSpace ℂ (Fin (2 + (2 + 2))) →L[ℂ] Nested3)) =
        (sumShuffle.symm : EuclideanSpace ℂ (Fin (2 + (2 + 2))) →L[ℂ] Nested3) := by
      rw [← ContinuousLinearMap.comp_assoc, cbig_pairing_comp_pairingInv]
      apply ContinuousLinearMap.ext
      intro x
      simp
    rw [h, cbig_sumShuffle_comp_symm]

end

end Work.Gen.E2
