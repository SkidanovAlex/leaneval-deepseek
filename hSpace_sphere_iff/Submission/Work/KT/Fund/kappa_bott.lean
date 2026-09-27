import Mathlib
import Submission.Work.KT.Fund.kbi_defs
import Submission.Work.KT.Fund.kbi_hopfsq
import Submission.Work.KT.Fund.kbi_Wbd
import Submission.Work.KT.Fund.kbi_frame
import Submission.Work.KT.Fund.kbi_hu
import Submission.Work.KT.Fund.kbi_or_sum
import Submission.Work.KT.Fund.kbi_kron_E00
import Submission.Work.KT.Fund.kbi_hopf2
import Submission.Work.KT.Fund.kbi_cls
import Submission.Work.KT.Fund.kbi_kg
import Submission.Work.KT.Fund.kbi_kron_congr
import Submission.Work.KT.kappa_span
import Submission.Work.KT.k0_basic
import Submission.Work.KT.patch_idem_dim

/-!
# `Work.KT.Fund.kappa_bott` — the Bott unit formula for the clutched class

The assembly of the proof of `kappa_bott`; the pieces live in the `kbi_*` files (see
`NOTES_kbi_kappa_bott.md`).
-/

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- `Bott.blk 0` is the identity. -/
lemma kappa_bott_blk0 {R : Type} [Ring R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) :
    Bott.blk 0 M = M := by
  ext i j
  simp only [Bott.blk, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [show (finSumFinEquiv.symm i : Fin N ⊕ Fin 0) = Sum.inl i from by
        rw [Equiv.symm_apply_eq]; rfl,
      show (finSumFinEquiv.symm j : Fin N ⊕ Fin 0) = Sum.inl j from by
        rw [Equiv.symm_apply_eq]; rfl]
  simp [Matrix.fromBlocks_apply₁₁]

/-- A `pairMat` of idempotents, glued along compatible boundaries, is idempotent. -/
lemma kappa_bott_pairMat_idem {N : ℕ}
    {A B : Matrix (Fin N) (Fin N) C(X × Ball ℂ, ℂ)}
    (hA : A * A = A) (hB : B * B = B)
    (h : A.map (fun f => bdryRestrict X f) = B.map (fun f => bdryRestrict X f)) :
    pairMat X A B h * pairMat X A B h = pairMat X A B h := by
  apply mat_ext X
  · rw [← Work.KT.Matrix.map_mul' (prF X) (pairMat X A B h) (pairMat X A B h),
      pairMat_map_prF, hA]
  · rw [← Work.KT.Matrix.map_mul' (prS X) (pairMat X A B h) (pairMat X A B h),
      pairMat_map_prS, hB]

set_option maxHeartbeats 800000 in
theorem kappa_bott (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Work.KT.Fund.pullMat X (1 - P)
        + (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X P)
    (μ : Work.KT.K0 C(X × S2, ℂ) →+ Work.KT.K0 C(X × S2, ℂ) →+ Work.KT.K0 C(X × S2, ℂ))
    (hμ : Work.KT.IsK0Mul μ) :
    Work.KT.Fund.kappa X n u
      = Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X)))
          (Work.KT.cls (⟨n, 1 - P⟩ : Work.KT.Mat C(X, ℂ)))
        + μ (Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X)))
              (Work.KT.cls (⟨n, P⟩ : Work.KT.Mat C(X, ℂ))))
            (Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.snd : C(X × S2, S2)))
              (Work.KT.cls Work.KT.hopfIdem)) := by
  -- the two gluing data
  have h1 : (KBI.h1e X).map (fun f => Work.KT.Fund.bdryRestrict X f) =
      (KBI.h2e X).map (fun f => Work.KT.Fund.bdryRestrict X f) := by
    funext i j
    have h := congrFun (congrFun (Work.KT.Fund.kbi_hopfsq X).2.2 (finSumFinEquiv i))
      (finSumFinEquiv j)
    simpa only [Matrix.map_apply, KBI.h1e, KBI.h2e, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm] using h
  have hW : (KBI.W1 X n P).map (fun f => Work.KT.Fund.bdryRestrict X f) =
      (KBI.W2 X n P).map (fun f => Work.KT.Fund.bdryRestrict X f) := by
    funext i j
    have h := congrFun (congrFun (Work.KT.Fund.kbi_Wbd X n P) (finProdFinEquiv.symm i))
      (finProdFinEquiv.symm j)
    simpa only [Matrix.map_apply, KBI.W1, KBI.W2, Matrix.reindex_apply,
      Matrix.submatrix_apply] using h
  -- the target idempotent
  let E : Matrix (Fin (n*2)) (Fin (n*2)) ↥(Work.KT.Fund.pullAlg2 X) :=
    Work.KT.Fund.pairMat X (KBI.W1 X n P) (KBI.W2 X n P) hW
  -- its idempotency, from the frame identities
  obtain ⟨hfr1, hfr2, hfr3, hfr4⟩ := Work.KT.Fund.kbi_frame X n P hP
  have hW1p_idem : KBI.W1p X n P * KBI.W1p X n P = KBI.W1p X n P := by
    rw [← hfr3]
    calc (KBI.TB1p X n P * KBI.SA1p X n P) * (KBI.TB1p X n P * KBI.SA1p X n P)
        = KBI.TB1p X n P * ((KBI.SA1p X n P * KBI.TB1p X n P) * KBI.SA1p X n P) := by
          rw [Matrix.mul_assoc,
            Matrix.mul_assoc (KBI.SA1p X n P) (KBI.TB1p X n P) (KBI.SA1p X n P)]
      _ = KBI.TB1p X n P * KBI.SA1p X n P := by rw [hfr1, Matrix.one_mul]
  have hW2p_idem : KBI.W2p X n P * KBI.W2p X n P = KBI.W2p X n P := by
    rw [← hfr4]
    calc (KBI.TB2p X n P * KBI.SA2p X n P) * (KBI.TB2p X n P * KBI.SA2p X n P)
        = KBI.TB2p X n P * ((KBI.SA2p X n P * KBI.TB2p X n P) * KBI.SA2p X n P) := by
          rw [Matrix.mul_assoc,
            Matrix.mul_assoc (KBI.SA2p X n P) (KBI.TB2p X n P) (KBI.SA2p X n P)]
      _ = KBI.TB2p X n P * KBI.SA2p X n P := by rw [hfr2, Matrix.one_mul]
  have hW1_idem : KBI.W1 X n P * KBI.W1 X n P = KBI.W1 X n P := by
    simp only [KBI.W1, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [hW1p_idem]
  have hW2_idem : KBI.W2 X n P * KBI.W2 X n P = KBI.W2 X n P := by
    simp only [KBI.W2, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [hW2p_idem]
  have hEidem : Work.KT.Mat.IsIdem (⟨n*2, E⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) :=
    kappa_bott_pairMat_idem X hW1_idem hW2_idem hW
  -- the four hypotheses of the gluing tool
  have h₁ : KBI.TB1 X n P * KBI.SA1 X n P = Bott.blk 0 (E.map (prF X)) := by
    show KBI.TB1 X n P * KBI.SA1 X n P = Bott.blk 0 (KBI.W1 X n P)
    rw [KBI.TB1_mul_SA1 X n P hfr3, kappa_bott_blk0]
  have h₂ : KBI.SA1 X n P * KBI.TB1 X n P = 1 := KBI.SA1_mul_TB1 X n P hfr1
  have h₃ : KBI.TB2 X n P * KBI.SA2 X n P = Bott.blk 0 (E.map (prS X)) := by
    show KBI.TB2 X n P * KBI.SA2 X n P = Bott.blk 0 (KBI.W2 X n P)
    rw [KBI.TB2_mul_SA2 X n P hfr4, kappa_bott_blk0]
  have h₄ : KBI.SA2 X n P * KBI.TB2 X n P = 1 := KBI.SA2_mul_TB2 X n P hfr2
  obtain ⟨hu1, hu2⟩ := Work.KT.Fund.kbi_hu X n P hP u hu
  have hmv := Work.KT.clutchIdem_mvN X (n*2) n 0 E (KBI.SA1 X n P) (KBI.TB1 X n P)
    (KBI.SA2 X n P) (KBI.TB2 X n P) h₁ h₂ h₃ h₄ u hu1 hu2
  -- `kappa` is the class of the target idempotent
  have hkappa : Work.KT.Fund.kappa X n u
      = (Work.KT.Fund.k0Glue X).symm
          (Work.KT.cls (⟨n*2, E⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))) := by
    rw [Work.KT.Fund.kappa_val X n u]
    congr 1
    have hsumIdem : (Work.KT.Mat.sum (⟨n*2, E⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
        (Work.KT.Mat.one ↥(Work.KT.Fund.pullAlg2 X) 0)).IsIdem :=
      Work.KT.Mat.sum_isIdem hEidem (Work.KT.Mat.one_isIdem _ 0)
    have hclIdem : (Work.KT.Fund.clutchIdem X n u
        (Work.KT.Fund.liftOf X (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
        (Work.KT.Fund.liftOf X (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
        (Work.KT.Fund.liftOf_spec X (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
        (Work.KT.Fund.liftOf_spec X (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))).IsIdem :=
      Work.KT.Fund.clutchIdem_isIdem X n u _ _ _ _
    have hcl := Work.KT.cls_eq_of_mvn hsumIdem hclIdem hmv
    rw [Work.KT.cls_sum (p := (⟨n*2, E⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))) hEidem
      (Work.KT.Mat.one_isIdem _ 0), Work.KT.cls_one_zero, add_zero] at hcl
    exact hcl.symm
  -- the two sides agree in `K₀ (pullAlg2 X)`
  have key : (Work.KT.Fund.k0Glue X)
      (Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X)))
          (Work.KT.cls (⟨n, 1 - P⟩ : Work.KT.Mat C(X, ℂ)))
        + μ (Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X)))
              (Work.KT.cls (⟨n, P⟩ : Work.KT.Mat C(X, ℂ))))
            (Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.snd : C(X × S2, S2)))
              (Work.KT.cls Work.KT.hopfIdem)))
      = Work.KT.cls (⟨n*2, E⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := by
    have hA : (Work.KT.Fund.k0Glue X)
        (Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X)))
          (Work.KT.cls (⟨n, 1 - P⟩ : Work.KT.Mat C(X, ℂ))))
        = Work.KT.cls (⟨n, KBI.QR X n P⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) :=
      (Work.KT.Fund.kbi_kg X n P h1).2.1
    have hB : (Work.KT.Fund.k0Glue X)
        (μ (Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X)))
              (Work.KT.cls (⟨n, P⟩ : Work.KT.Mat C(X, ℂ))))
            (Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.snd : C(X × S2, S2)))
              (Work.KT.cls Work.KT.hopfIdem)))
        = Work.KT.k0Mul ↥(Work.KT.Fund.pullAlg2 X) (fun x y => mul_comm x y)
            (Work.KT.cls (⟨n, KBI.PR X n P⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)))
            (Work.KT.cls (Work.KT.Fund.pairIdem X (KBI.h1e X) (KBI.h2e X) h1)) := by
      have hmul := Work.KT.k0_mul_natural (C(X × S2, ℂ)) ↥(Work.KT.Fund.pullAlg2 X)
        (Work.KT.Fund.glueEquiv X : C(X × S2, ℂ) →+* ↥(Work.KT.Fund.pullAlg2 X))
        μ (Work.KT.k0Mul ↥(Work.KT.Fund.pullAlg2 X) (fun x y => mul_comm x y))
        (fun x y => mul_comm x y) hμ
        (Work.KT.k0Mul_isK0Mul ↥(Work.KT.Fund.pullAlg2 X) (fun x y => mul_comm x y))
        (Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X)))
              (Work.KT.cls (⟨n, P⟩ : Work.KT.Mat C(X, ℂ))))
        (Work.KT.K0.mapA (Work.KT.pullAlg (ContinuousMap.snd : C(X × S2, S2)))
              (Work.KT.cls Work.KT.hopfIdem))
      have kg1 : Work.KT.K0.map (Work.KT.Fund.glueEquiv X : C(X × S2, ℂ) →+*
          ↥(Work.KT.Fund.pullAlg2 X)) (Work.KT.K0.mapA (Work.KT.pullAlg
            (ContinuousMap.fst : C(X × S2, X))) (Work.KT.cls (⟨n, P⟩ : Work.KT.Mat C(X, ℂ))))
          = Work.KT.cls (⟨n, KBI.PR X n P⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) :=
        (Work.KT.Fund.kbi_kg X n P h1).1
      have kg3 : Work.KT.K0.map (Work.KT.Fund.glueEquiv X : C(X × S2, ℂ) →+*
          ↥(Work.KT.Fund.pullAlg2 X)) (Work.KT.K0.mapA (Work.KT.pullAlg
            (ContinuousMap.snd : C(X × S2, S2))) (Work.KT.cls Work.KT.hopfIdem))
          = Work.KT.cls (Work.KT.Fund.pairIdem X (KBI.h1e X) (KBI.h2e X) h1) :=
        (Work.KT.Fund.kbi_kg X n P h1).2.2
      show Work.KT.K0.map (Work.KT.Fund.glueEquiv X : C(X × S2, ℂ) →+*
          ↥(Work.KT.Fund.pullAlg2 X)) (μ _ _) = _
      rw [hmul, kg1, kg3]
    rw [map_add, hA, hB, add_comm]
    exact (Work.KT.Fund.kbi_cls X n P hP h1 hW
      (Work.KT.k0Mul ↥(Work.KT.Fund.pullAlg2 X) (fun x y => mul_comm x y))
      (Work.KT.k0Mul_isK0Mul ↥(Work.KT.Fund.pullAlg2 X) (fun x y => mul_comm x y))).symm
  rw [hkappa, ← key]
  exact (Work.KT.Fund.k0Glue X).symm_apply_apply _

end

end Work.KT.Fund
