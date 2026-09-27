import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kappa_indep
import Submission.Work.KT.Fund.kappa_add_defs
import Submission.Work.KT.Fund.graphProj_block_aux
import Submission.Work.KT.Fund.graphProj_blockB
import Submission.Work.KT.Fund.recipProj_blockB
import Submission.Work.KT.Fund.fromBlocks_unit_inv

namespace Work.KT.Fund

open Matrix

noncomputable section

-- ===== aux =====

lemma kab_reindex_map {m n : Type} {α β : Type} (e : m ≃ n) (M : Matrix m m α) (f : α → β) :
    (Matrix.reindex e e M).map f = Matrix.reindex e e (M.map f) := by
  funext i j; rfl

lemma kab_reindex_reindex {a b c : Type} {R : Type} (e : a ≃ b) (f : b ≃ c) (M : Matrix a a R) :
    Matrix.reindex f f (Matrix.reindex e e M) = Matrix.reindex (e.trans f) (e.trans f) M := by
  funext i j; rfl

lemma kab_fromBlocks_map {m n : Type} {α β : Type} [Semiring α] [Semiring β]
    (φ : α →+* β) (A : Matrix m m α) (B : Matrix n n α) :
    (Matrix.fromBlocks A 0 0 B).map φ = Matrix.fromBlocks (A.map φ) 0 0 (B.map φ) := by
  funext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp [Matrix.map_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

lemma kab_fromBlocks_reindex {m n m' n' : Type} {R : Type} [Zero R]
    (e : m ≃ m') (f : n ≃ n') (A : Matrix m m R) (B : Matrix n n R) :
    Matrix.reindex (Equiv.sumCongr e f) (Equiv.sumCongr e f) (Matrix.fromBlocks A 0 0 B)
      = Matrix.fromBlocks (Matrix.reindex e e A) 0 0 (Matrix.reindex f f B) := by
  funext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

lemma kab_fromBlocks_reindex_symm {m n m' n' : Type} {R : Type} [Zero R]
    (e : m ≃ m') (f : n ≃ n') (A : Matrix m m R) (B : Matrix n n R) :
    Matrix.fromBlocks (Matrix.reindex e e A) 0 0 (Matrix.reindex f f B)
      = Matrix.reindex (Equiv.sumCongr e f) (Equiv.sumCongr e f) (Matrix.fromBlocks A 0 0 B) :=
  (kab_fromBlocks_reindex e f A B).symm

lemma kappa_eq_cls (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (F G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map (fun f => bdryRestrict X f) = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG : G.map (fun f => bdryRestrict X f)
      = (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) :
    kappa X n u = (k0Glue X).symm (cls (clutchIdem X n u F G hF hG)) := by
  rw [kappa_val]
  congr 1
  exact kappa_indep X n u
    (liftOf X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    F
    (liftOf X (((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))))
    G
    (liftOf_spec X _) hF (liftOf_spec X _) hG

theorem kappa_add_blocks (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n k : ℕ) (u : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ)
    (u₁ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (u₂ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ)
    (h : (u : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (u₁ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
            (u₂ : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)))) :
    Work.KT.Fund.kappa X (n + k) u
      = Work.KT.Fund.kappa X n u₁ + Work.KT.Fund.kappa X k u₂ := by
  let F₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    liftOf X (u₁ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
  let G₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    liftOf X (((u₁⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
  let F₂ : Matrix (Fin k) (Fin k) C(X × Ball ℂ, ℂ) :=
    liftOf X (u₂ : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))
  let G₂ : Matrix (Fin k) (Fin k) C(X × Ball ℂ, ℂ) :=
    liftOf X (((u₂⁻¹ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)))
  have hF₁ : F₁.map (fun f => bdryRestrict X f)
      = (u₁ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := liftOf_spec X _
  have hG₁ : G₁.map (fun f => bdryRestrict X f)
      = (↑(u₁⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := liftOf_spec X _
  have hF₂ : F₂.map (fun f => bdryRestrict X f)
      = (u₂ : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)) := liftOf_spec X _
  have hG₂ : G₂.map (fun f => bdryRestrict X f)
      = (↑(u₂⁻¹) : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)) := liftOf_spec X _
  let F : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Ball ℂ, ℂ) :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks F₁ 0 0 F₂)
  let G : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Ball ℂ, ℂ) :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks G₁ 0 0 G₂)
  have hF : F.map (fun f => bdryRestrict X f)
      = (u : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)) := by
    have hFr : F = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks F₁ 0 0 F₂) := rfl
    rw [hFr, h, kab_reindex_map, kab_fromBlocks_map, hF₁, hF₂]
  have hG : G.map (fun f => bdryRestrict X f)
      = (↑(u⁻¹) : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)) := by
    rw [fromBlocks_unit_inv n k u u₁ u₂ h]
    have hGr : G = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks G₁ 0 0 G₂) := rfl
    rw [hGr, kab_reindex_map, kab_fromBlocks_map, hG₁, hG₂]
  -- the two per-summand pairMats
  set P₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥(pullAlg2 X) :=
    pairMat X (graphProj C(X × Ball ℂ, ℂ) F₁) (recipProj C(X × Ball ℂ, ℂ) G₁)
      (clutch_agree X n u₁ F₁ G₁ hF₁ hG₁) with hP₁def
  set P₂ : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ↥(pullAlg2 X) :=
    pairMat X (graphProj C(X × Ball ℂ, ℂ) F₂) (recipProj C(X × Ball ℂ, ℂ) G₂)
      (clutch_agree X k u₂ F₂ G₂ hF₂ hG₂) with hP₂def
  have hcd₁ : clutchIdem X n u₁ F₁ G₁ hF₁ hG₁
      = ⟨n + n, Matrix.reindex finSumFinEquiv finSumFinEquiv P₁⟩ := by
    rw [hP₁def]; rfl
  have hcd₂ : clutchIdem X k u₂ F₂ G₂ hF₂ hG₂
      = ⟨k + k, Matrix.reindex finSumFinEquiv finSumFinEquiv P₂⟩ := by
    rw [hP₂def]; rfl
  -- the block decomposition of the big pairMat
  have hP : pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
        (clutch_agree X (n + k) u F G hF hG)
      = Matrix.reindex (blkEquiv n k) (blkEquiv n k) (Matrix.fromBlocks P₁ 0 0 P₂) := by
    have hgp : graphProj C(X × Ball ℂ, ℂ) F
        = Matrix.reindex (blkEquiv n k) (blkEquiv n k)
            (Matrix.fromBlocks (graphProj C(X × Ball ℂ, ℂ) F₁) 0 0
              (graphProj C(X × Ball ℂ, ℂ) F₂)) := by
      have hFr : F = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks F₁ 0 0 F₂) := rfl
      rw [hFr]; exact graphProj_blockB n k F₁ F₂
    have hrp : recipProj C(X × Ball ℂ, ℂ) G
        = Matrix.reindex (blkEquiv n k) (blkEquiv n k)
            (Matrix.fromBlocks (recipProj C(X × Ball ℂ, ℂ) G₁) 0 0
              (recipProj C(X × Ball ℂ, ℂ) G₂)) := by
      have hGr : G = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks G₁ 0 0 G₂) := rfl
      rw [hGr]; exact recipProj_blockB n k G₁ G₂
    apply mat_ext X
    · rw [pairMat_map_prF, hgp, kab_reindex_map, kab_fromBlocks_map, hP₁def, hP₂def,
          pairMat_map_prF, pairMat_map_prF]
    · rw [pairMat_map_prS, hrp, kab_reindex_map, kab_fromBlocks_map, hP₁def, hP₂def,
          pairMat_map_prS, pairMat_map_prS]
  let E : (Fin n ⊕ Fin n) ⊕ (Fin k ⊕ Fin k) ≃ Fin ((n + k) + (n + k)) :=
    (blkEquiv n k).trans finSumFinEquiv
  let E' : (Fin n ⊕ Fin n) ⊕ (Fin k ⊕ Fin k) ≃ Fin ((n + n) + (k + k)) :=
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv
  have hcd₁2 : (clutchIdem X n u₁ F₁ G₁ hF₁ hG₁).2
      = Matrix.reindex finSumFinEquiv finSumFinEquiv P₁ := by
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
        (pairMat X (graphProj C(X × Ball ℂ, ℂ) F₁) (recipProj C(X × Ball ℂ, ℂ) G₁)
          (clutch_agree X n u₁ F₁ G₁ hF₁ hG₁))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv P₁
    rw [hP₁def]
  have hcd₂2 : (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂).2
      = Matrix.reindex finSumFinEquiv finSumFinEquiv P₂ := by
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
        (pairMat X (graphProj C(X × Ball ℂ, ℂ) F₂) (recipProj C(X × Ball ℂ, ℂ) G₂)
          (clutch_agree X k u₂ F₂ G₂ hF₂ hG₂))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv P₂
    rw [hP₂def]
  have hbig2 : (clutchIdem X (n + k) u F G hF hG).2
      = Matrix.reindex E E (Matrix.fromBlocks P₁ 0 0 P₂) := by
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
        (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
          (clutch_agree X (n + k) u F G hF hG))
      = Matrix.reindex ((blkEquiv n k).trans finSumFinEquiv)
          ((blkEquiv n k).trans finSumFinEquiv) (Matrix.fromBlocks P₁ 0 0 P₂)
    rw [hP, kab_reindex_reindex]
  have hsum2 : ((clutchIdem X n u₁ F₁ G₁ hF₁ hG₁).sum
        (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂)).2
      = Matrix.reindex E' E' (Matrix.fromBlocks P₁ 0 0 P₂) := by
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (clutchIdem X n u₁ F₁ G₁ hF₁ hG₁).2 0 0
          (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂).2)
      = Matrix.reindex ((Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv)
          ((Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv)
          (Matrix.fromBlocks P₁ 0 0 P₂)
    rw [hcd₁2, hcd₂2]
    exact (congrArg (fun M => Matrix.reindex finSumFinEquiv finSumFinEquiv M)
        (kab_fromBlocks_reindex_symm finSumFinEquiv finSumFinEquiv P₁ P₂)).trans
      (kab_reindex_reindex (Equiv.sumCongr finSumFinEquiv finSumFinEquiv) finSumFinEquiv
        (Matrix.fromBlocks P₁ 0 0 P₂))
  have hEE : E.trans (E.symm.trans E') = E' := by
    ext i
    simp [E, E', Equiv.trans_apply]
  have hΦ : Matrix.reindex (E.symm.trans E') (E.symm.trans E')
        (clutchIdem X (n + k) u F G hF hG).2
      = ((clutchIdem X n u₁ F₁ G₁ hF₁ hG₁).sum
          (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂)).2 := by
    rw [hbig2, hsum2, kab_reindex_reindex, hEE]
  have hmv : Mat.MvN (clutchIdem X (n + k) u F G hF hG)
      ((clutchIdem X n u₁ F₁ G₁ hF₁ hG₁).sum (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂)) := by
    have h2 : (⟨(n + n) + (k + k),
        Matrix.reindex (E.symm.trans E') (E.symm.trans E')
          (clutchIdem X (n + k) u F G hF hG).2⟩ : Mat ↥(pullAlg2 X))
        = (clutchIdem X n u₁ F₁ G₁ hF₁ hG₁).sum (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂) :=
      Sigma.ext rfl (heq_of_eq hΦ)
    rw [← h2]
    exact Mat.mvN_reindex (E.symm.trans E') (clutchIdem X (n + k) u F G hF hG).2
  have hcls : cls (clutchIdem X (n + k) u F G hF hG)
      = cls (clutchIdem X n u₁ F₁ G₁ hF₁ hG₁)
        + cls (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂) := by
    have h1 := cls_eq_of_mvn (clutchIdem_isIdem X (n + k) u F G hF hG)
      (Mat.sum_isIdem (clutchIdem_isIdem X n u₁ F₁ G₁ hF₁ hG₁)
        (clutchIdem_isIdem X k u₂ F₂ G₂ hF₂ hG₂)) hmv
    rwa [cls_sum (clutchIdem_isIdem X n u₁ F₁ G₁ hF₁ hG₁)
        (clutchIdem_isIdem X k u₂ F₂ G₂ hF₂ hG₂)] at h1
  calc kappa X (n + k) u
      = (k0Glue X).symm (cls (clutchIdem X (n + k) u F G hF hG)) :=
        kappa_eq_cls X (n + k) u F G hF hG
    _ = (k0Glue X).symm (cls (clutchIdem X n u₁ F₁ G₁ hF₁ hG₁)
          + cls (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂)) := by rw [hcls]
    _ = (k0Glue X).symm (cls (clutchIdem X n u₁ F₁ G₁ hF₁ hG₁))
          + (k0Glue X).symm (cls (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂)) := by rw [map_add]
    _ = kappa X n u₁ + kappa X k u₂ := by
        rw [← kappa_eq_cls X n u₁ F₁ G₁ hF₁ hG₁,
            ← kappa_eq_cls X k u₂ F₂ G₂ hF₂ hG₂]

end

end Work.KT.Fund
