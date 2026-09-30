import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology Work.DeltaHomology

/-- The semi-simplicial identity `d_i d_j = d_{j-1} d_i` (`i < j`) at the level of
the chain-level face maps: for `u : Fin (n+3)` and `v : Fin (n+2)` with `v < u`
(viewed as natural numbers),

`faceMap u ≫ faceMap v = faceMap v.castSucc ≫ faceMap (u.pred hu)`,

i.e. `d_v ∘ d_u = d_{u-1} ∘ d_v`.  This is `DeltaCx.face_face_pred` transported to
the free modules `K.chainX`. -/
theorem DeltaCx.faceMap_comp_faceMap (K : DeltaCx) (n : ℕ) (u : Fin (n + 3)) (hu : u ≠ 0)
    (v : Fin (n + 2)) (hv : (v : ℕ) < (u : ℕ)) :
    K.faceMap (k := n + 1) u ≫ K.faceMap (k := n) v
      = K.faceMap (k := n + 1) (Fin.castSucc v) ≫ K.faceMap (k := n) (u.pred hu) := by
  apply DeltaCx.chainX_hom_ext
  intro σ
  simp only [← Category.assoc, DeltaCx.faceMap, Limits.Sigma.ι_comp_desc]
  rw [DeltaCx.face_face_pred K σ v u hu hv]

/-- `∂ ∘ ∂ = 0` for the `Δ`-chain complex: the alternating sum of the face maps of a `Δ`-complex squares to zero. (`K.chainD k = ∑ i : Fin (k+2), (-1 : ℤ)^i • K.faceMap i` is the boundary of `K` in the free module `K.chainX k := ∐ (fun _ : Fin (K.card k) => ℤ)`; useful lemmas: `DeltaCx.ι_chainD`, `DeltaCx.face_face_pred`, `DeltaCx.chainX_hom_ext`.) -/
theorem chainD_comp (K : DeltaCx) (n : ℕ) : K.chainD (n + 1) ≫ K.chainD n = 0 := by
  -- Abbreviation for the summands of the double sum `∂_{n+1} ∂_n`, indexed by a
  -- pair `(inner face index, outer face index)`.
  set T : Fin (n + 3) × Fin (n + 2) → (K.chainX (n + 2) ⟶ K.chainX n) :=
    fun p => ((-1 : ℤ) ^ (p.1 : ℕ) * (-1 : ℤ) ^ (p.2 : ℕ)) •
      (K.faceMap (k := n + 1) p.1 ≫ K.faceMap (k := n) p.2) with hT
  have hTp : ∀ p, T p = ((-1 : ℤ) ^ (p.1 : ℕ) * (-1 : ℤ) ^ (p.2 : ℕ)) •
      (K.faceMap (k := n + 1) p.1 ≫ K.faceMap (k := n) p.2) := fun p => by rw [hT]
  -- Expand `∂_{n+1} ∂_n` as the double sum over `Fin (n+3) × Fin (n+2)`.
  have hexp : K.chainD (n + 1) ≫ K.chainD n = ∑ p : Fin (n + 3) × Fin (n + 2), T p := by
    rw [DeltaCx.chainD, DeltaCx.chainD, Preadditive.sum_comp]
    simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [hTp (u, v), mul_comm]
  rw [hexp]
  -- Split the pairs according to whether the outer index `p.2` is below the inner
  -- index `p.1` or not.
  have hsplit : (∑ p : Fin (n + 3) × Fin (n + 2), T p)
      = (Finset.univ.filter (fun p : Fin (n + 3) × Fin (n + 2) => (p.2 : ℕ) < (p.1 : ℕ))).sum T
      + (Finset.univ.filter
          (fun p : Fin (n + 3) × Fin (n + 2) => ¬ ((p.2 : ℕ) < (p.1 : ℕ)))).sum T := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (n + 3) × Fin (n + 2)))
      (fun p : Fin (n + 3) × Fin (n + 2) => (p.2 : ℕ) < (p.1 : ℕ)) T]
  rw [hsplit]
  -- The two partial sums cancel: `(u, v) ↦ (v.castSucc, u.pred)` is a sign
  -- reversing bijection between the pairs with `v < u` and the remaining ones.
  have hbij : (Finset.univ.filter
        (fun p : Fin (n + 3) × Fin (n + 2) => (p.2 : ℕ) < (p.1 : ℕ))).sum T
      = (Finset.univ.filter
          (fun p : Fin (n + 3) × Fin (n + 2) => ¬ ((p.2 : ℕ) < (p.1 : ℕ)))).sum
        (fun p => -T p) := by
    refine Finset.sum_bij'
      (fun p hp => (Fin.castSucc p.2, p.1.pred (by
        have h := (Finset.mem_filter.mp hp).2
        intro h0
        have h' : (p.1 : ℕ) = 0 := Fin.val_eq_zero_iff.mpr h0
        omega)))
      (fun p hp => (p.2.succ, p.1.castLT (by
        have h := (Finset.mem_filter.mp hp).2
        omega)))
      ?_ ?_ ?_ ?_ ?_
    · -- the image of the forward map lies in the complementary region
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Fin.val_pred, Fin.val_castSucc]
      have h := (Finset.mem_filter.mp hp).2
      omega
    · -- the image of the backward map lies in the region `v < u`
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Fin.val_castLT, Fin.val_succ]
      have h := (Finset.mem_filter.mp hp).2
      omega
    · -- left inverse
      intro p hp
      apply Prod.ext
      · rw [Fin.succ_pred]
      · apply Fin.ext
        rw [Fin.val_castLT, Fin.val_castSucc]
    · -- right inverse
      intro p hp
      apply Prod.ext
      · apply Fin.ext
        rw [Fin.val_castSucc, Fin.val_castLT]
      · rw [Fin.pred_succ]
    · -- the terms match up to sign
      intro p hp
      have hv : (p.2 : ℕ) < (p.1 : ℕ) := (Finset.mem_filter.mp hp).2
      have h1 : p.1 ≠ 0 := by
        intro h0
        have h' : (p.1 : ℕ) = 0 := Fin.val_eq_zero_iff.mpr h0
        omega
      have hA : (-1 : ℤ) ^ (p.1 : ℕ) = -((-1 : ℤ) ^ ((p.1 : ℕ) - 1)) := by
        have h : (p.1 : ℕ) - 1 + 1 = (p.1 : ℕ) := by omega
        nth_rewrite 1 [← h]
        rw [pow_succ]
        ring
      rw [hT]
      simp only []
      rw [← DeltaCx.faceMap_comp_faceMap K n p.1 h1 p.2 hv]
      rw [Fin.val_pred, Fin.val_castSucc, hA]
      rw [← neg_smul]
      congr 1
      ring
  rw [Finset.sum_neg_distrib] at hbij
  rw [hbij]
  simp

end Work.DeltaHomology
