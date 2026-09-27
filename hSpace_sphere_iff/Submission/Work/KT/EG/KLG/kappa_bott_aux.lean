import Mathlib
import Submission.Work.KT.EG.KLG.kappa_bott_defs
import Submission.Work.KT.EG.KLG.tgt_blocks

/-!
# `Work.KT.EG.KLG.kappa_bott_aux` — auxiliary computations for `kappa_bott_gen`

Idempotency of the glued Hopf block `RhopPair` and the block/reindexing bookkeeping that identifies
the class of the glued target `tgtPair` with the two summands of the right hand side of
`kappa_bott_gen`.
-/

namespace Work.KT.EG.KLG

open _root_.Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## Idempotency of the Hopf blocks -/

/-- `hopfIdem` is idempotent. -/
theorem hopfIdem_mat_mul_self : Work.KT.hopfIdem.2 * Work.KT.hopfIdem.2 = Work.KT.hopfIdem.2 :=
  Work.KT.Fund.twoByTwo_idem_of_trace_det Work.KT.hopfIdem.2
    Work.KT.Fund.hopf_trace_det.1 Work.KT.Fund.hopf_trace_det.2

theorem RhopUp_mul_self : Work.KT.Fund.KL.RhopUp X * Work.KT.Fund.KL.RhopUp X =
    Work.KT.Fund.KL.RhopUp X := by
  change Work.KT.hopfIdem.2.map
      ((Work.KT.Fund.pullUp X).comp (Work.KT.pullAlg (ContinuousMap.snd : C(X × Work.KT.S2, Work.KT.S2)))) *
    Work.KT.hopfIdem.2.map
      ((Work.KT.Fund.pullUp X).comp (Work.KT.pullAlg (ContinuousMap.snd : C(X × Work.KT.S2, Work.KT.S2))))
    = Work.KT.hopfIdem.2.map
      ((Work.KT.Fund.pullUp X).comp (Work.KT.pullAlg (ContinuousMap.snd : C(X × Work.KT.S2, Work.KT.S2))))
  rw [Work.KT.Matrix.map_mul', hopfIdem_mat_mul_self]

theorem RhopDn_mul_self : Work.KT.Fund.KL.RhopDn X * Work.KT.Fund.KL.RhopDn X =
    Work.KT.Fund.KL.RhopDn X := by
  change Work.KT.hopfIdem.2.map
      ((Work.KT.Fund.pullDn X).comp (Work.KT.pullAlg (ContinuousMap.snd : C(X × Work.KT.S2, Work.KT.S2)))) *
    Work.KT.hopfIdem.2.map
      ((Work.KT.Fund.pullDn X).comp (Work.KT.pullAlg (ContinuousMap.snd : C(X × Work.KT.S2, Work.KT.S2))))
    = Work.KT.hopfIdem.2.map
      ((Work.KT.Fund.pullDn X).comp (Work.KT.pullAlg (ContinuousMap.snd : C(X × Work.KT.S2, Work.KT.S2))))
  rw [Work.KT.Matrix.map_mul', hopfIdem_mat_mul_self]

/-- The glued Hopf block `(RhopUp, RhopDn)` is idempotent. -/
theorem RhopPair_mul_self
    (hhop : (Work.KT.Fund.KL.RhopUp X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.Fund.KL.RhopDn X).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    RhopPair X hhop * RhopPair X hhop = RhopPair X hhop := by
  show Work.KT.Fund.pairMat X (Work.KT.Fund.KL.RhopUp X) (Work.KT.Fund.KL.RhopDn X) hhop *
      Work.KT.Fund.pairMat X (Work.KT.Fund.KL.RhopUp X) (Work.KT.Fund.KL.RhopDn X) hhop
    = Work.KT.Fund.pairMat X (Work.KT.Fund.KL.RhopUp X) (Work.KT.Fund.KL.RhopDn X) hhop
  rw [Work.KT.pairMat_pull_mul hhop hhop]
  exact Work.KT.pairMat_pull_congr (RhopUp_mul_self X) (RhopDn_mul_self X) _ _

/-! ## Bookkeeping: the class of the glued target -/

section Book

/-- Entrywise application of a ring hom commutes with `kroneckerMap`. -/
lemma kronMap_map_ring {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {m n : Type}
    [Fintype m] [Fintype n] (M : Matrix m m R) (N : Matrix n n R) :
    (Matrix.kroneckerMap (· * ·) M N).map φ
      = Matrix.kroneckerMap (· * ·) (M.map φ) (N.map φ) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp [Matrix.kroneckerMap_apply, Matrix.map_apply, map_mul]

/-- Reindexing along the identity. -/
lemma reindex_refl_refl {R : Type} [Ring R] {m n : Type} (M : Matrix m n R) :
    Matrix.reindex (Equiv.refl m) (Equiv.refl n) M = M := by
  rw [Matrix.reindex_apply]
  change M.submatrix id id = M
  exact Matrix.submatrix_id_id M

/-- Splitting a block matrix along `idxEquiv`. -/
lemma reindex_fromBlocks_prod {R : Type} [Ring R] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) R) (Q : Matrix (Fin n × Fin 2) (Fin n × Fin 2) R) :
    Matrix.reindex (idxEquiv n) (idxEquiv n) (Matrix.fromBlocks P 0 0 Q)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks P 0 0 (Matrix.reindex finProdFinEquiv finProdFinEquiv Q)) := by
  rw [show idxEquiv n = (Equiv.sumCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans
      finSumFinEquiv from rfl,
    ← Work.KT.Fund.reindex_reindex' (Equiv.sumCongr (Equiv.refl (Fin n)) finProdFinEquiv)
      finSumFinEquiv (Matrix.fromBlocks P 0 0 Q),
    Work.KT.Fund.fromBlocks_reindex_sumCongr (Equiv.refl (Fin n)) finProdFinEquiv P Q,
    reindex_refl_refl]

/-- `1 - E` is idempotent when `E` is. -/
lemma one_sub_mul_self {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E) :
    (1 - E) * (1 - E) = 1 - E := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hE]
  abel

end Book

/-! ## The block decomposition of the glued target -/

section Decomp

variable {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
include hE

/-- The glued target is the block sum of the `(1-E)`-part and the `B ⊗ R`-part. -/
theorem tgtPair_eq_blocks
    (hbdry : (upTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (dnTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f))
    (h12 : (R1 X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (R2 X).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    tgtPair X E hbdry
      = Matrix.fromBlocks (trivPair X (1 - E)) 0 0
          (Matrix.kroneckerMap (· * ·) (trivPair X E) (R12Pair X h12)) := by
  have hb := tgt_blocks X (Amat X E) (Bmat X E) (Amat_mul_self X E hE) (Bmat_mul_self X E hE)
    (Amat_mul_Bmat X E hE) (Bmat_mul_Amat X E hE)
  have h1' : upTgt X (Amat X E) (Bmat X E)
      = Matrix.fromBlocks (Amat X E) 0 0
          (Matrix.kroneckerMap (· * ·) (Bmat X E) (R1 X)) := hb.1
  have h2' : dnTgt X (Amat X E) (Bmat X E)
      = Matrix.fromBlocks (Amat X E) 0 0
          (Matrix.kroneckerMap (· * ·) (Bmat X E) (R2 X)) := hb.2
  have hA : (Amat X E).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Amat X E).map (fun f => Work.KT.Fund.bdryRestrict X f) := rfl
  have hR : (Matrix.kroneckerMap (· * ·) (Bmat X E) (R1 X)).map
        (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Matrix.kroneckerMap (· * ·) (Bmat X E) (R2 X)).map
        (fun f => Work.KT.Fund.bdryRestrict X f) := by
    rw [kronMap_map_ring (Work.KT.Fund.bdryRestrict X) (Bmat X E) (R1 X),
      kronMap_map_ring (Work.KT.Fund.bdryRestrict X) (Bmat X E) (R2 X), h12]
  have hb' : (Matrix.fromBlocks (Amat X E) 0 0
        (Matrix.kroneckerMap (· * ·) (Bmat X E) (R1 X))).map
        (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Matrix.fromBlocks (Amat X E) 0 0
        (Matrix.kroneckerMap (· * ·) (Bmat X E) (R2 X))).map
        (fun f => Work.KT.Fund.bdryRestrict X f) := by
    rw [← h1', ← h2']
    exact hbdry
  have hQ : Work.KT.Fund.pairMat X (Matrix.kroneckerMap (· * ·) (Bmat X E) (R1 X))
        (Matrix.kroneckerMap (· * ·) (Bmat X E) (R2 X)) hR
      = Matrix.kroneckerMap (· * ·) (trivPair X E) (R12Pair X h12) := by
    apply Work.KT.Fund.mat_ext X
    · rw [Work.KT.Fund.pairMat_map_prF,
        kronMap_map_ring (Work.KT.Fund.prF X) (trivPair X E) (R12Pair X h12)]
      simp only [trivPair, R12Pair, Bmat, Work.KT.Fund.pairMat_map_prF]
    · rw [Work.KT.Fund.pairMat_map_prS,
        kronMap_map_ring (Work.KT.Fund.prS X) (trivPair X E) (R12Pair X h12)]
      simp only [trivPair, R12Pair, Bmat, Work.KT.Fund.pairMat_map_prS]
  calc tgtPair X E hbdry
      = Work.KT.Fund.pairMat X (Matrix.fromBlocks (Amat X E) 0 0
            (Matrix.kroneckerMap (· * ·) (Bmat X E) (R1 X)))
          (Matrix.fromBlocks (Amat X E) 0 0
            (Matrix.kroneckerMap (· * ·) (Bmat X E) (R2 X))) hb' :=
        Work.KT.pairMat_pull_congr h1' h2' hbdry hb'
    _ = Matrix.fromBlocks (Work.KT.Fund.pairMat X (Amat X E) (Amat X E) hA) 0 0
          (Work.KT.Fund.pairMat X (Matrix.kroneckerMap (· * ·) (Bmat X E) (R1 X))
            (Matrix.kroneckerMap (· * ·) (Bmat X E) (R2 X)) hR) :=
        @Work.KT.Fund.pairMat_fromBlocks_kappa_add X _ _ _ (Fin n) (Fin n × Fin 2)
          (Amat X E) (Amat X E)
          (Matrix.kroneckerMap (· * ·) (Bmat X E) (R1 X))
          (Matrix.kroneckerMap (· * ·) (Bmat X E) (R2 X)) hb' hA hR
    _ = Matrix.fromBlocks (trivPair X (1 - E)) 0 0
          (Matrix.kroneckerMap (· * ·) (trivPair X E) (R12Pair X h12)) := by
        rw [hQ]
        exact congrArg (fun M => Matrix.fromBlocks M 0 0
          (Matrix.kroneckerMap (· * ·) (trivPair X E) (R12Pair X h12)))
          (Work.KT.pairMat_pull_congr (show Amat X E = Work.KT.Fund.KC.gUp X (1 - E) from rfl)
            (show Amat X E = Work.KT.Fund.KC.gUp X (1 - E) from rfl) hA rfl)

end Decomp

/-! ## The class of the glued target -/

section Cls

variable {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
include hE

/-- The class of the glued target splits into the `(1-E)`-part and the `B ⊗ R`-part. -/
theorem cls_tgt_aux
    (hbdry : (upTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (dnTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f))
    (h12 : (R1 X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (R2 X).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    Work.KT.cls (⟨n + n * 2,
        Matrix.reindex (idxEquiv n) (idxEquiv n) (tgtPair X E hbdry)⟩ :
        Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      = Work.KT.cls (⟨n, trivPair X (1 - E)⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
        + Work.KT.cls (⟨n * 2,
            Work.KT.kronMat (trivPair X E) (R12Pair X h12)⟩ :
            Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := by
  have hcomm : ∀ x y : ↥(Work.KT.Fund.pullAlg2 X), x * y = y * x := fun x y => mul_comm x y
  have hb := tgtPair_eq_blocks X E hE hbdry h12
  have hp : Work.KT.Mat.IsIdem (⟨n, trivPair X (1 - E)⟩ :
      Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) :=
    trivPair_mul_self X (1 - E) (one_sub_mul_self X E hE)
  have hk : Work.KT.Mat.IsIdem (Work.KT.Mat.kron (⟨n, trivPair X E⟩ :
        Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      (⟨2, R12Pair X h12⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))) :=
    Work.KT.Mat.kron_idem hcomm (trivPair_mul_self X E hE) (R12Pair_mul_self X h12)
  have hq : Work.KT.Mat.IsIdem (⟨n * 2, Work.KT.kronMat (trivPair X E) (R12Pair X h12)⟩ :
      Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := hk
  rw [hb, reindex_fromBlocks_prod]
  change Work.KT.cls (Work.KT.Mat.sum (⟨n, trivPair X (1 - E)⟩ :
      Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      (⟨n * 2, Work.KT.kronMat (trivPair X E) (R12Pair X h12)⟩ :
      Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))) =
    Work.KT.cls (⟨n, trivPair X (1 - E)⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      + Work.KT.cls (⟨n * 2, Work.KT.kronMat (trivPair X E) (R12Pair X h12)⟩ :
        Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
  exact Work.KT.cls_sum hp hq

/-- Passing from the `R`-block to the Hopf block in the class of the product. -/
theorem kron_cls_eq
    (h12 : (R1 X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (R2 X).map (fun f => Work.KT.Fund.bdryRestrict X f))
    (hhop : (Work.KT.Fund.KL.RhopUp X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.Fund.KL.RhopDn X).map (fun f => Work.KT.Fund.bdryRestrict X f))
    (hR : Work.KT.Mat.MvN (⟨2, R12Pair X h12⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      (⟨2, RhopPair X hhop⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))) :
    Work.KT.cls (⟨n * 2, Work.KT.kronMat (trivPair X E) (R12Pair X h12)⟩ :
        Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      = Work.KT.cls (⟨n * 2, Work.KT.kronMat (trivPair X E) (RhopPair X hhop)⟩ :
        Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := by
  have hcomm : ∀ x y : ↥(Work.KT.Fund.pullAlg2 X), x * y = y * x := fun x y => mul_comm x y
  have hp : Work.KT.Mat.IsIdem (⟨n, trivPair X E⟩ :
      Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := trivPair_mul_self X E hE
  have hq : Work.KT.Mat.IsIdem (⟨2, R12Pair X h12⟩ :
      Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := R12Pair_mul_self X h12
  have hq' : Work.KT.Mat.IsIdem (⟨2, RhopPair X hhop⟩ :
      Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := RhopPair_mul_self X hhop
  have hmv : (Work.KT.Mat.kron (⟨n, trivPair X E⟩ :
        Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      (⟨2, R12Pair X h12⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))).MvN
      (Work.KT.Mat.kron (⟨n, trivPair X E⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      (⟨2, RhopPair X hhop⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))) :=
    kron_mvN hcomm (Work.KT.Mat.MvN_refl hp) hR
  exact Work.KT.cls_eq_of_mvn (Work.KT.Mat.kron_idem hcomm hp hq)
    (Work.KT.Mat.kron_idem hcomm hp hq') hmv

end Cls

end

end Work.KT.EG.KLG
