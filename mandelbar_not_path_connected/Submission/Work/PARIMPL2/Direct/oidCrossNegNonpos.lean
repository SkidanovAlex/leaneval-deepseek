import Mathlib
import Submission.Work.PARIMPL2.Direct.oidAux
import Submission.Work.PARIMPL2.Direct.orbitCrossBound
import Submission.Work.PARIMPL2.Direct.oidDefs
import Submission.Work.PARIMPL2.Direct.oidArcNeg
import Submission.Work.PARIMPL2.Direct.oidArcPos
import Submission.Work.PARIMPL2.Direct.oidCfSign
import Submission.Work.PARIMPL2.Direct.oidcnHelpers
import Submission.Work.PARIMPL2.Direct.oidcnArith
import Submission.Work.PARIMPL2.Direct.oidcnSplit
import Submission.Work.PARIMPL2.Direct.oidcnArcALe
import Submission.Work.PARIMPL2.Direct.oidcnArcBLe

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

-- Re-exported helpers (see `oidcnHelpers.lean`) used below:
--   `oidcn_prod_le_prod`, `oidcn_prod_le_one`, `oidcn_one_sub_prod_le_sum`,
--   `oidcn_exists_cross`, `oidcn_one_sub_prod_le_exp`.

/-! ## The `cr ≤ 0` weighted cross-sum bound

We bound `X := Σ_{j<n} ocA_j · ∏_{i∈(j,n)} (1 + oidCf_i)` by `8(1 + log R)`, under the extra
hypothesis `S := Σ_{j<n} ocA_j ≤ 0` and `|S| ≤ 8(1+log R)`.

Since `cr ≤ 0`, each coefficient `C_i := oidCf_i` is `≤ 0`, so the backward products
`Q_j := ∏_{i∈(j,n)}(1 + C_i)` lie in `(0,1]`.  Let `j0` be the crossing index of `λ x` through
`π/2`: then `ocA_j ≤ 0` for `j < j0` (arc A) and `ocA_j ≥ 0` for `j0 ≤ j < n` (arc B).
Writing `Qbar := ∏_{i∈(j0,n)}(1+C_i)` one has the exact decomposition (`oidcnSplit`)

`X = Qbar·S + P + Q`,  `P := Σ_{j<j0} |ocA_j| · Qbar · (1 - ∏_{i∈(j,j0]}(1+C_i)) ≥ 0`,
`Q := Σ_{j0≤j<n} ocA_j · (Q_{j+1} - Qbar) ≥ 0`.

Hence `X ≥ Qbar·S ≥ S ≥ -(8(1+log R))` (as `0 ≤ Qbar ≤ 1` and `S ≤ 0`), and
`X ≤ P + Q ≤ 8δ + 6δ = 14δ ≤ 8(1+log R)` where `δ := exp(12|cr|/R) - 1`, using
`oidcnArcALe`, `oidcnArcBLe` and the arithmetic lemma `oidcnArith`. -/

theorem oidCrossNegNonpos (lam R cr : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hcr : cr ≤ 0) (hcpR : |cr| ≤ 3 * R / 32 + 81 / 64)
    (n : ℕ) (x y : ℕ → ℝ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hDpos : ∀ j ≤ n, 0 < Work.PARIMPL2.Direct.ocDen lam x y j)
    (hCnp : ∀ j < n, Work.PARIMPL2.Direct.oidCf lam cr x y j ≤ 0)
    (hCab1 : ∀ j < n, |Work.PARIMPL2.Direct.oidCf lam cr x y j| ≤ 1)
    (hSnn : ∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j ≤ 0)
    (hSn : |∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j| ≤ 8 * (1 + Real.log R)) :
    |∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + Work.PARIMPL2.Direct.oidCf lam cr x y i)|
      ≤ 8 * (1 + Real.log R) := by
  classical
  have hRpos : (0:ℝ) < R := by linarith
  have hβpos : 0 < 8 * (1 + Real.log R) := by
    have : 0 < Real.log R := Real.log_pos (by linarith)
    linarith
  have hxpos : ∀ j ≤ n, 0 < x j := fun j hj => by linarith [hx1 j hj]
  have htxpos : ∀ j ≤ n, 0 < lam * x j := fun j hj => mul_pos hlam (hxpos j hj)
  have htxltpi : ∀ j ≤ n, lam * x j < Real.pi := by
    intro j hj
    have h := mul_le_mul_of_nonneg_left (hx2 j hj) hlam.le
    have he : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by field_simp
    rw [he] at h
    have h2 : 0 < lam * R / 4 := by positivity
    linarith
  have hs : ∀ j ≤ n, 0 < Real.sin (lam * x j) := fun j hj =>
    Real.sin_pos_of_pos_of_lt_pi (htxpos j hj) (htxltpi j hj)
  obtain ⟨j0, hj0le, hnegg, hposg⟩ := oidcn_exists_cross lam hlam n x hdec
  have hAle : ∀ j, j < j0 → ocA lam x y j ≤ 0 := by
    intro j hj
    have hjn : j ≤ n := le_trans (le_of_lt hj) hj0le
    have hcos : Real.cos (lam * x j) < 0 := by
      have h2 : lam * x j < Real.pi := htxltpi j hjn
      have hp := Real.cos_pos_of_mem_Ioo (x := Real.pi - lam * x j)
        ⟨by linarith [Real.pi_pos], by linarith [hnegg j hj]⟩
      rw [Real.cos_pi_sub] at hp
      linarith [hp]
    rw [ocA]
    have hD := hDpos j hjn
    have hs' := hs j hjn
    have h1 : 0 < lam * Real.sin (lam * x j) := mul_pos hlam hs'
    exact div_nonpos_of_nonpos_of_nonneg (mul_neg_of_pos_of_neg h1 hcos).le hD.le
  have hAge : ∀ j, j0 ≤ j → j < n → 0 ≤ ocA lam x y j := by
    intro j hj hjn
    have hjn' : j ≤ n := le_of_lt hjn
    have hcos : 0 ≤ Real.cos (lam * x j) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [htxpos j hjn', Real.pi_pos], hposg j hj hjn⟩
    rw [ocA]
    have hD := hDpos j hjn'
    have hs' := hs j hjn'
    exact div_nonneg (mul_nonneg (mul_nonneg hlam.le hs'.le) hcos) hD.le
  have hCneg : ∀ i < n, -1 ≤ oidCf lam cr x y i := fun i hi => (abs_le.mp (hCab1 i hi)).1
  have h1Cnn : ∀ i < n, 0 ≤ 1 + oidCf lam cr x y i := fun i hi => by linarith [hCneg i hi]
  have h1Cle1 : ∀ i < n, 1 + oidCf lam cr x y i ≤ 1 := fun i hi => by linarith [hCnp i hi]
  rcases lt_or_eq_of_le hj0le with hj0lt | hj0eq
  · -- main case
    have hQbar_nn : 0 ≤ ∏ i ∈ Finset.Ico (j0+1) n, (1 + oidCf lam cr x y i) :=
      Finset.prod_nonneg (fun i hi => h1Cnn i (Finset.mem_Ico.mp hi).2)
    have hQbar_le1 : (∏ i ∈ Finset.Ico (j0+1) n, (1 + oidCf lam cr x y i)) ≤ 1 :=
      oidcn_prod_le_one _ _ (fun i hi => h1Cnn i (Finset.mem_Ico.mp hi).2)
        (fun i hi => h1Cle1 i (Finset.mem_Ico.mp hi).2)
    have hsplit := oidcnSplit (ocA lam x y) (oidCf lam cr x y) n j0 hj0lt hAle
    have hA := oidcnArcALe lam R cr hlam hR hlamR hcr hcpR n j0 x y hj0lt hnegg hx1 hx2 hdec hDpos hCab1 hSn
    have hB := oidcnArcBLe lam R cr hlam hR hlamR hcr n j0 x y hj0lt hposg hx1 hx2 hdec hDpos hCab1 hSn
    have harith := oidcnArith R cr hR hcpR
    have hPnn : 0 ≤ ∑ j ∈ Finset.range j0, |ocA lam x y j|
        * (∏ i ∈ Finset.Ico (j0+1) n, (1 + oidCf lam cr x y i))
        * (1 - ∏ i ∈ Finset.Ico (j+1) (j0+1), (1 + oidCf lam cr x y i)) := by
      apply Finset.sum_nonneg
      intro j hj
      have hjlt : j < j0 := Finset.mem_range.mp hj
      have hq : (∏ i ∈ Finset.Ico (j+1) (j0+1), (1 + oidCf lam cr x y i)) ≤ 1 :=
        oidcn_prod_le_one _ _ (fun i hi => h1Cnn i (by have := (Finset.mem_Ico.mp hi).2; omega))
          (fun i hi => h1Cle1 i (by have := (Finset.mem_Ico.mp hi).2; omega))
      exact mul_nonneg (mul_nonneg (abs_nonneg _) hQbar_nn) (by linarith)
    have hQnn : 0 ≤ ∑ j ∈ Finset.Ico j0 n, ocA lam x y j
        * ((∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i))
          - ∏ i ∈ Finset.Ico (j0+1) n, (1 + oidCf lam cr x y i)) := by
      apply Finset.sum_nonneg
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have hAj := hAge j hj1 hj2
      have hfac : (∏ i ∈ Finset.Ico (j0+1) n, (1 + oidCf lam cr x y i))
          = (∏ i ∈ Finset.Ico (j0+1) (j+1), (1 + oidCf lam cr x y i))
            * (∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i)) :=
        (Finset.prod_Ico_consecutive (fun i => 1 + oidCf lam cr x y i) (by omega) (by omega)).symm
      have hq' : (∏ i ∈ Finset.Ico (j0+1) (j+1), (1 + oidCf lam cr x y i)) ≤ 1 :=
        oidcn_prod_le_one _ _ (fun i hi => h1Cnn i (by have := (Finset.mem_Ico.mp hi).2; omega))
          (fun i hi => h1Cle1 i (by have := (Finset.mem_Ico.mp hi).2; omega))
      have hq'nn : 0 ≤ (∏ i ∈ Finset.Ico (j0+1) (j+1), (1 + oidCf lam cr x y i)) :=
        Finset.prod_nonneg (fun i hi => h1Cnn i (by have := (Finset.mem_Ico.mp hi).2; omega))
      have hWnn : 0 ≤ (∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i)) :=
        Finset.prod_nonneg (fun i hi => h1Cnn i (Finset.mem_Ico.mp hi).2)
      have hsub : 0 ≤ (∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i))
          - ∏ i ∈ Finset.Ico (j0+1) n, (1 + oidCf lam cr x y i) := by
        rw [hfac]; nlinarith [hq'nn, hq', hWnn]
      exact mul_nonneg hAj hsub
    have hSge : -(8 * (1 + Real.log R)) ≤ ∑ j ∈ Finset.range n, ocA lam x y j := by
      have := (abs_le.mp hSn).1; linarith
    have hXle : (∑ j ∈ Finset.range n, ocA lam x y j
        * ∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i)) ≤ 8 * (1 + Real.log R) := by
      rw [hsplit]
      have hAl : (∏ i ∈ Finset.Ico (j0+1) n, (1 + oidCf lam cr x y i))
          * (∑ j ∈ Finset.range n, ocA lam x y j) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hQbar_nn hSnn
      linarith [hAl, hA, hB, harith]
    have hXge : -(8 * (1 + Real.log R)) ≤ (∑ j ∈ Finset.range n, ocA lam x y j
        * ∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i)) := by
      rw [hsplit]
      have hAl : (∑ j ∈ Finset.range n, ocA lam x y j)
          ≤ (∏ i ∈ Finset.Ico (j0+1) n, (1 + oidCf lam cr x y i))
            * (∑ j ∈ Finset.range n, ocA lam x y j) := by
        nlinarith [hQbar_nn, hQbar_le1, hSnn]
      linarith [hPnn, hQnn, hAl, hSge]
    rw [abs_le]
    exact ⟨hXge, hXle⟩
  · -- j0 = n
    have hAen : ∀ j < n, ocA lam x y j ≤ 0 := by
      intro j hj
      exact hAle j (by omega)
    have hWnn : ∀ j < n, 0 ≤ ∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i) :=
      fun j hj => Finset.prod_nonneg (fun i hi => h1Cnn i (Finset.mem_Ico.mp hi).2)
    have hWle1 : ∀ j < n, (∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i)) ≤ 1 :=
      fun j hj => oidcn_prod_le_one _ _ (fun i hi => h1Cnn i (Finset.mem_Ico.mp hi).2)
        (fun i hi => h1Cle1 i (Finset.mem_Ico.mp hi).2)
    have hXle : (∑ j ∈ Finset.range n, ocA lam x y j
        * ∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      have hj' := Finset.mem_range.mp hj
      exact mul_nonpos_of_nonpos_of_nonneg (hAen j hj') (hWnn j hj')
    have hXge : -(8 * (1 + Real.log R)) ≤ (∑ j ∈ Finset.range n, ocA lam x y j
        * ∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i)) := by
      have hle : (∑ j ∈ Finset.range n, ocA lam x y j)
          ≤ (∑ j ∈ Finset.range n, ocA lam x y j
              * ∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have h2 := mul_nonpos_of_nonpos_of_nonneg (hAen j hj') (sub_nonneg.mpr (hWle1 j hj'))
        nlinarith [h2]
      have := (abs_le.mp hSn).1
      linarith
    rw [abs_le]
    exact ⟨hXge, by linarith [hXle, hβpos]⟩

end Work.PARIMPL2.Direct
