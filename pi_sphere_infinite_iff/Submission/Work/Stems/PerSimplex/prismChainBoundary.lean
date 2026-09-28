import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Stems.PerSimplex.prismChainDefs

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial BigOperators
open Work.RatHurewicz.Bridge (coface coface_apply)

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The singular `(n+2)`-simplex carried by the `x`-th piece of the prism of `F`. -/
def px (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) (x : Fin (n+2)) :
    Work.Serre.SSetSimplex X (n+2) :=
  Work.RatHurewicz.Bridge.simplexOf (n+2) (F.comp (Work.Serre.pp (n+1) x))

/-- The singular `(n+1)`-simplex carried by the `y`-th piece of the prism of the `x`-th face
homotopy of `F`. -/
def qf (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (x : Fin (n+2)) (y : Fin (n+1)) : Work.Serre.SSetSimplex X (n+1) :=
  Work.RatHurewicz.Bridge.simplexOf (n+1)
    ((F.comp ((coface n x).prodMap (ContinuousMap.id unitInterval))).comp (Work.Serre.pp n y))

/-- The bottom simplex of `F`. -/
def pbot (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    Work.Serre.SSetSimplex X (n+1) :=
  Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.botIncl (n+1)))

/-- The top simplex of `F`. -/
def ptop (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    Work.Serre.SSetSimplex X (n+1) :=
  Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.topIncl (n+1)))

/-- The face of the singular simplex attached to a continuous map is the simplex attached to the
composite with the coface. -/
theorem delta_simplexOf (m : ℕ) (f : Fin (m+2)) (c : C(↥(stdSimplex ℝ (Fin (m+2))), X)) :
    (Work.Serre.singX X).δ f (Work.RatHurewicz.Bridge.simplexOf (m+1) c)
      = Work.RatHurewicz.Bridge.simplexOf m (c.comp (coface m f)) := by
  apply ((TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk m))).injective
  rw [Work.Serre.toSSetObjEquiv_δ, Work.RatHurewicz.Bridge.toSSetObjEquiv_simplexOf,
    Work.RatHurewicz.Bridge.toSSetObjEquiv_simplexOf]

/-- The `0`-th face of the first prism piece is the top simplex. -/
theorem delta_px_zero (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    (Work.Serre.singX X).δ 0 (px n F 0) = ptop n F := by
  rw [px, ptop, delta_simplexOf (n+1) 0 (F.comp (Work.Serre.pp (n+1) 0))]
  congr 1
  rw [ContinuousMap.comp_assoc, Work.Serre.pp_coface_zero_zero]

/-- The last face of the last prism piece is the bottom simplex. -/
theorem delta_px_last (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    (Work.Serre.singX X).δ (Fin.last (n+2)) (px n F (Fin.last (n+1))) = pbot n F := by
  rw [px, pbot, delta_simplexOf (n+1) (Fin.last (n+2))
    (F.comp (Work.Serre.pp (n+1) (Fin.last (n+1))))]
  congr 1
  rw [ContinuousMap.comp_assoc, Work.Serre.pp_coface_last_last]

/-- The `(k+1)`-st face is shared by the `k`-th and `(k+1)`-st prism piece. -/
theorem delta_px_diag (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (k : Fin (n+1)) :
    (Work.Serre.singX X).δ k.castSucc.succ (px n F k.castSucc)
      = (Work.Serre.singX X).δ k.castSucc.succ (px n F k.succ) := by
  rw [px, px, delta_simplexOf (n+1) k.castSucc.succ (F.comp (Work.Serre.pp (n+1) k.castSucc)),
    delta_simplexOf (n+1) k.castSucc.succ (F.comp (Work.Serre.pp (n+1) k.succ))]
  congr 1
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, Work.Serre.pp_coface_diag]

/-- For `f < k`, the `f`-th face of the `k`-th prism piece is the prism piece of the `f`-th face. -/
theorem delta_px_lt (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (f : Fin (n+3)) (k : Fin (n+2)) (hfk : (f:ℕ) < (k:ℕ)) :
    (Work.Serre.singX X).δ f (px n F k)
      = qf n F ⟨(f:ℕ), by omega⟩ ⟨(k:ℕ)-1, by omega⟩ := by
  rw [px, qf, delta_simplexOf (n+1) f (F.comp (Work.Serre.pp (n+1) k))]
  congr 1
  rw [ContinuousMap.comp_assoc, Work.Serre.pp_coface_lt k f hfk]
  exact (ContinuousMap.comp_assoc F _ _).symm

/-- For `f > k+1`, the `f`-th face of the `k`-th prism piece is the prism piece of the
`(f-1)`-st face. -/
theorem delta_px_gt (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (f : Fin (n+3)) (k : Fin (n+2)) (hfk : (k:ℕ) + 1 < (f:ℕ)) :
    (Work.Serre.singX X).δ f (px n F k)
      = qf n F ⟨(f:ℕ)-1, by omega⟩ ⟨(k:ℕ), by omega⟩ := by
  rw [px, qf, delta_simplexOf (n+1) f (F.comp (Work.Serre.pp (n+1) k))]
  congr 1
  rw [ContinuousMap.comp_assoc, Work.Serre.pp_coface_gt k f hfk]
  exact (ContinuousMap.comp_assoc F _ _).symm

end

end Work.Stems.PerSimplex

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The terms of the prism identity: the faces of the prism pieces, the prism pieces of the face
homotopies, and the two boundary terms. -/
def pval (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    Work.Serre.PIdx n → (Work.Serre.SSetSimplex X (n+1) →₀ ℤ) := fun z =>
  match z with
  | Sum.inl (k, f) =>
      ((-1:ℤ)^((k:ℕ)+1+(f:ℕ))) • Finsupp.single ((Work.Serre.singX X).δ f (px n F k)) (1:ℤ)
  | Sum.inr (Sum.inl (x, y)) =>
      ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (qf n F x y) (1:ℤ)
  | Sum.inr (Sum.inr (Sum.inl _)) => - Finsupp.single (pbot n F) (1:ℤ)
  | Sum.inr (Sum.inr (Sum.inr _)) => Finsupp.single (ptop n F) (1:ℤ)

theorem pval_ne_zero (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (z : Work.Serre.PIdx n) : pval n F z ≠ 0 := by
  match z with
  | Sum.inl (k, f) =>
      intro h
      have h1 := congrArg (fun (w : Work.Serre.SSetSimplex X (n+1) →₀ ℤ) =>
        w ((Work.Serre.singX X).δ f (px n F k))) h
      simp only [pval, Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.zero_apply,
        smul_eq_mul, mul_one] at h1
      exact pow_ne_zero _ (by norm_num : (-1:ℤ) ≠ 0) h1
  | Sum.inr (Sum.inl (x, y)) =>
      intro h
      have h1 := congrArg (fun (w : Work.Serre.SSetSimplex X (n+1) →₀ ℤ) =>
        w (qf n F x y)) h
      simp only [pval, Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.zero_apply,
        smul_eq_mul, mul_one] at h1
      exact pow_ne_zero _ (by norm_num : (-1:ℤ) ≠ 0) h1
  | Sum.inr (Sum.inr (Sum.inl u)) =>
      intro h
      have h1 := congrArg (fun (w : Work.Serre.SSetSimplex X (n+1) →₀ ℤ) => w (pbot n F)) h
      simp only [pval, Finsupp.neg_apply, Finsupp.single_eq_same, Finsupp.zero_apply] at h1
      exact one_ne_zero (neg_eq_zero.mp h1)
  | Sum.inr (Sum.inr (Sum.inr u)) =>
      intro h
      have h1 := congrArg (fun (w : Work.Serre.SSetSimplex X (n+1) →₀ ℤ) => w (ptop n F)) h
      simp only [pval, Finsupp.single_eq_same, Finsupp.zero_apply] at h1
      exact one_ne_zero h1

theorem pval_pinv (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (z : Work.Serre.PIdx n) : pval n F (Work.Serre.pinv z) = - pval n F z := by
  match z with
  | Sum.inl (k, f) =>
      simp only [Work.Serre.pinv]
      by_cases h1 : (f:ℕ) < (k:ℕ)
      · rw [dif_pos h1]
        simp only [pval]
        rw [delta_px_lt n F f k h1, ← neg_smul]
        congr 1
        rw [show (↑k + 1 + ↑f : ℕ) = (↑f + (↑k - 1 + 1)) + 1 by omega, pow_succ]
        ring
      · rw [dif_neg h1]
        by_cases h2 : (f:ℕ) = (k:ℕ)
        · rw [dif_pos h2]
          by_cases h3 : (k:ℕ) = 0
          · rw [dif_pos h3]
            simp only [pval]
            rw [show (↑k + 1 + ↑f : ℕ) = 1 by omega, pow_one]
            rw [show (f : Fin (n+3)) = 0 from Fin.ext (by simp only [Fin.val_zero]; omega),
              show (k : Fin (n+2)) = 0 from Fin.ext (by simp only [Fin.val_zero]; omega),
              delta_px_zero n F]
            rw [neg_one_smul, neg_neg]
          · rw [dif_neg h3]
            simp only [pval]
            have hfac : (Work.Serre.singX X).δ f
                  (px n F (⟨(k:ℕ)-1, by have hk := k.isLt; omega⟩ : Fin (n+2)))
                = (Work.Serre.singX X).δ f (px n F k) := by
              let j : Fin (n+1) := ⟨(k:ℕ)-1, by have hk := k.isLt; omega⟩
              have hjv : (j:ℕ) = (k:ℕ)-1 := rfl
              have hjc : j.castSucc
                  = (⟨(k:ℕ)-1, by have hk := k.isLt; omega⟩ : Fin (n+2)) := rfl
              rw [← hjc]
              rw [show f = j.castSucc.succ from
                Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
              rw [show k = j.succ from Fin.ext (by simp only [Fin.val_succ]; omega)]
              exact delta_px_diag n F j
            rw [hfac, ← neg_smul]
            congr 1
            rw [show (↑k + 1 + ↑f : ℕ) = (↑k - 1 + 1 + ↑f) + 1 by omega, pow_succ]
            ring
        · rw [dif_neg h2]
          by_cases h4 : (f:ℕ) = (k:ℕ)+1
          · rw [dif_pos h4]
            by_cases h5 : (k:ℕ) = n+1
            · rw [dif_pos h5]
              simp only [pval]
              rw [show (↑k + 1 + ↑f : ℕ) = 2 * (n + 2) by omega]
              rw [pow_mul, show ((-1:ℤ)^2) = 1 by norm_num, one_pow, one_smul]
              rw [show (f : Fin (n+3)) = Fin.last (n+2) from
                  Fin.ext (by simp only [Fin.val_last]; omega),
                show (k : Fin (n+2)) = Fin.last (n+1) from
                  Fin.ext (by simp only [Fin.val_last]; omega),
                delta_px_last n F]
            · rw [dif_neg h5]
              simp only [pval]
              have hfac : (Work.Serre.singX X).δ f
                    (px n F (⟨(k:ℕ)+1, by have hk := k.isLt; omega⟩ : Fin (n+2)))
                  = (Work.Serre.singX X).δ f (px n F k) := by
                let j : Fin (n+1) := ⟨(k:ℕ), by have hk := k.isLt; omega⟩
                have hjv : (j:ℕ) = (k:ℕ) := rfl
                have hjs : j.succ
                    = (⟨(k:ℕ)+1, by have hk := k.isLt; omega⟩ : Fin (n+2)) := rfl
                rw [← hjs]
                rw [show f = j.castSucc.succ from
                  Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
                rw [show k = j.castSucc from Fin.ext (by simp only [Fin.val_castSucc]; omega)]
                exact (delta_px_diag n F j).symm
              rw [hfac, ← neg_smul]
              congr 1
              rw [show (↑k + 1 + 1 + ↑f : ℕ) = (↑k + 1 + ↑f) + 1 by omega, pow_succ]
              ring
          · rw [dif_neg h4]
            simp only [pval]
            rw [delta_px_gt n F f k (by omega), ← neg_smul]
            congr 1
            rw [show (↑k + 1 + ↑f : ℕ) = (↑f - 1 + (↑k + 1)) + 1 by omega, pow_succ]
            ring
  | Sum.inr (Sum.inl (x, y)) =>
      simp only [Work.Serre.pinv]
      by_cases h1 : (x:ℕ) ≤ (y:ℕ)
      · rw [dif_pos h1]
        simp only [pval]
        rw [delta_px_lt n F (⟨(x:ℕ), by have hx := x.isLt; omega⟩ : Fin (n+3))
          (⟨(y:ℕ)+1, by have hy := y.isLt; omega⟩ : Fin (n+2))
          (by simp only [Fin.val_mk]; omega), ← neg_smul]
        congr 1
        rw [show (↑y + 1 + 1 + ↑x : ℕ) = (↑x + (↑y + 1)) + 1 by omega, pow_succ]
        ring
      · rw [dif_neg h1]
        simp only [pval]
        rw [delta_px_gt n F (⟨(x:ℕ)+1, by have hx := x.isLt; omega⟩ : Fin (n+3))
          (⟨(y:ℕ), by have hy := y.isLt; omega⟩ : Fin (n+2))
          (by simp only [Fin.val_mk]; omega), ← neg_smul]
        congr 1
        rw [show (↑y + 1 + (↑x + 1) : ℕ) = (↑x + (↑y + 1)) + 1 by omega, pow_succ]
        ring
  | Sum.inr (Sum.inr (Sum.inl u)) =>
      cases u
      simp only [Work.Serre.pinv, pval]
      rw [show (↑(Fin.last (n+1)) + 1 + ↑(Fin.last (n+2)) : ℕ) = 2 * (n + 2) by
        simp only [Fin.val_last]; omega]
      rw [pow_mul, show ((-1:ℤ)^2) = 1 by norm_num, one_pow, one_smul]
      simp only [delta_px_last n F, neg_neg]
  | Sum.inr (Sum.inr (Sum.inr u)) =>
      cases u
      simp only [Work.Serre.pinv, pval]
      rw [delta_px_zero n F]
      norm_num

end

end Work.Stems.PerSimplex

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

theorem pinv_ne_self (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (z : Work.Serre.PIdx n) : Work.Serre.pinv z ≠ z := by
  intro h
  have hpinv : pval n F (Work.Serre.pinv z) = pval n F z := by rw [h]
  rw [pval_pinv n F z] at hpinv
  have h1 : pval n F z + pval n F z = 0 := neg_eq_iff_add_eq_zero.mp hpinv
  have h2 : (2:ℤ) • pval n F z = 0 := by rw [two_smul ℤ (pval n F z)]; exact h1
  exact pval_ne_zero n F z ((smul_eq_zero.mp h2).resolve_left (by norm_num))

/-- The combinatorial content of the prism identity, in the free module on the singular
`(n+1)`-simplices. -/
theorem prismSumIdentityF (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    (∑ x : Fin (n+2), ∑ y : Fin (n+3),
        ((-1:ℤ)^((x:ℕ)+1+(y:ℕ))) • Finsupp.single ((Work.Serre.singX X).δ y (px n F x)) (1:ℤ))
      + (∑ x : Fin (n+2), ∑ y : Fin (n+1),
          ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (qf n F x y) (1:ℤ))
      = Finsupp.single (pbot n F) (1:ℤ) - Finsupp.single (ptop n F) (1:ℤ) := by
  have hsum : ∑ z : Work.Serre.PIdx n, pval n F z = 0 := by
    have h := Finset.sum_ninvolution (s := (Finset.univ : Finset (Work.Serre.PIdx n)))
      (f := pval n F) (Work.Serre.pinv (m := n))
      (fun a => by rw [pval_pinv n F a]; abel) (fun a _ => pinv_ne_self n F a)
      (fun a => Finset.mem_univ (Work.Serre.pinv a)) (fun a => Work.Serre.pinv_pinv a)
    simpa using h
  have hsplit : ∑ z : Work.Serre.PIdx n, pval n F z
      = (∑ x : Fin (n+2), ∑ y : Fin (n+3),
            ((-1:ℤ)^((x:ℕ)+1+(y:ℕ))) •
              Finsupp.single ((Work.Serre.singX X).δ y (px n F x)) (1:ℤ))
        + ((∑ x : Fin (n+2), ∑ y : Fin (n+1),
              ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (qf n F x y) (1:ℤ))
          + (- Finsupp.single (pbot n F) (1:ℤ) + Finsupp.single (ptop n F) (1:ℤ))) := by
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, pval, Finset.univ_unique,
      Finset.sum_singleton]
  rw [hsplit] at hsum
  have hsum' : ((∑ x : Fin (n+2), ∑ y : Fin (n+3),
            ((-1:ℤ)^((x:ℕ)+1+(y:ℕ))) •
              Finsupp.single ((Work.Serre.singX X).δ y (px n F x)) (1:ℤ))
        + (∑ x : Fin (n+2), ∑ y : Fin (n+1),
              ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (qf n F x y) (1:ℤ)))
        + (- Finsupp.single (pbot n F) (1:ℤ) + Finsupp.single (ptop n F) (1:ℤ)) = 0 := by
    rw [← hsum]; abel
  have h2 := add_eq_zero_iff_eq_neg.mp hsum'
  rw [neg_add_rev, neg_neg] at h2
  rw [sub_eq_add_neg]
  exact h2.trans (add_comm _ _)

end

end Work.Stems.PerSimplex

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **The boundary of the prism chain.**  For a homotopy `F : Δ^{n+1} × I → X` of an
`(n+1)`-simplex, the boundary of the prism chain of `F` is the difference of the top and bottom
chains minus the alternating sum of the prism chains of the face homotopies. -/
theorem prismChainBoundary (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    (ModuleCat.Hom.hom ((Work.Stems.hChain X).d (n+2) (n+1)))
        (prismChain (X := X) (n+1) F)
      = Work.Stems.simplexChain (X:=X) (n+1)
          (Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.botIncl (n+1))))
        - Work.Stems.simplexChain (X:=X) (n+1)
            (Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.topIncl (n+1))))
        - ∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) •
            prismChain (X := X) n
              (F.comp ((Work.RatHurewicz.Bridge.coface n i).prodMap
                (ContinuousMap.id unitInterval))) := by
  have hs : (ModuleCat.Hom.hom ((Work.Stems.hChain X).d (n+2) (n+1)))
        (prismChain (X := X) (n+1) F)
      = ∑ x : Fin (n+2), (-1:ℤ)^((x:ℕ)+1) •
          ∑ f : Fin (n+3), (-1:ℤ)^((f:ℕ)) •
            Work.Stems.simplexChain (X:=X) (n+1) ((Work.Serre.singX X).δ f (px n F x)) := by
    simp only [prismChain_def, px, map_sum, map_zsmul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    rw [Work.RatHurewicz.Bridge.d_ιChainComplex_one]
  have ht : (∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) •
        prismChain (X := X) n
          (F.comp ((Work.RatHurewicz.Bridge.coface n i).prodMap
            (ContinuousMap.id unitInterval))))
      = ∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) •
          ∑ y : Fin (n+1), (-1:ℤ)^((y:ℕ)+1) •
            Work.Stems.simplexChain (X:=X) (n+1) (qf n F i y) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [prismChain_def, qf]
  have key : (∑ x : Fin (n+2), ∑ f : Fin (n+3),
        ((-1:ℤ)^((x:ℕ)+1+(f:ℕ))) •
          Finsupp.single ((Work.Serre.singX X).δ f (px n F x)) (1:ℤ))
      = Finsupp.single
            (Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.botIncl (n+1)))) (1:ℤ)
        - Finsupp.single
            (Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.topIncl (n+1)))) (1:ℤ)
        - ∑ x : Fin (n+2), ∑ y : Fin (n+1),
            ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (qf n F x y) (1:ℤ) := by
    have h := prismSumIdentityF n F
    simp only [pbot, ptop, sub_eq_add_neg] at h ⊢
    rw [← h]
    abel
  rw [hs, ht]
  apply Work.Cohomology.Crux33.eq_of_coords_eq
  simp only [map_sub, map_sum, map_zsmul, Work.Stems.coords_simplexChain]
  simp_rw [Finset.smul_sum, smul_smul, ← pow_add]
  exact key

end

end Work.Stems.PerSimplex
