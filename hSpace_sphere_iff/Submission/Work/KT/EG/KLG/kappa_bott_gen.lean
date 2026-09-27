import Mathlib
import Submission.Work.KT.EG.kappaRedDefs
import Submission.Work.KT.EG.KLG.kappa_bott_defs
import Submission.Work.KT.EG.KLG.kappa_bott_aux
import Submission.Work.KT.EG.KLG.retract_frames
import Submission.Work.KT.EG.KLG.Rhop_bdry
import Submission.Work.KT.EG.KLG.Rhop_chart
import Submission.Work.KT.EG.KLG.bottUnit_bdry
import Submission.Work.KT.EG.KLG.mvN_clutch_of_data
import Submission.Work.KT.EG.KLG.mvN_R12_RhopHop
import Submission.Work.KT.EG.KLG.k0Glue_RHS

namespace Work.KT.EG.KLG

open _root_.Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## Auxiliary: idempotency of the glued target and reindexing lemmas -/

lemma reindex_map_rect {R S : Type} [Ring R] [Ring S] {m m' n n' : Type}
    (e : m ≃ m') (f : n ≃ n') (φ : R →+* S) (M : Matrix m n R) :
    (Matrix.reindex e f M).map φ = Matrix.reindex e f (M.map φ) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map]

theorem upTgt_mul_self {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hA : A * A = A) (hB : B * B = B) (hA1B : A + B = 1) :
    upTgt X A B * upTgt X A B = upTgt X A B := by
  have h := (retract_frames X A B hA hB hA1B).1
  show (upFrame X A B * upRet X A B) * (upFrame X A B * upRet X A B)
    = upFrame X A B * upRet X A B
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (upRet X A B) (upFrame X A B) (upRet X A B), h,
    Matrix.one_mul]

theorem dnTgt_mul_self {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hA : A * A = A) (hB : B * B = B) (hA1B : A + B = 1) :
    dnTgt X A B * dnTgt X A B = dnTgt X A B := by
  have h := (retract_frames X A B hA hB hA1B).2
  show (dnFrame X A B * dnRet X A B) * (dnFrame X A B * dnRet X A B)
    = dnFrame X A B * dnRet X A B
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dnRet X A B) (dnFrame X A B) (dnRet X A B), h,
    Matrix.one_mul]

theorem tgtPair_mul_self {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
    (hbdry : (upTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (dnTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    tgtPair X E hbdry * tgtPair X E hbdry = tgtPair X E hbdry := by
  have hA := Amat_mul_self X E hE
  have hB := Bmat_mul_self X E hE
  have h1 := Amat_add_Bmat X E
  show (Work.KT.Fund.pairMat X (upTgt X (Amat X E) (Bmat X E))
        (dnTgt X (Amat X E) (Bmat X E)) hbdry) *
      (Work.KT.Fund.pairMat X (upTgt X (Amat X E) (Bmat X E))
        (dnTgt X (Amat X E) (Bmat X E)) hbdry)
    = Work.KT.Fund.pairMat X (upTgt X (Amat X E) (Bmat X E))
        (dnTgt X (Amat X E) (Bmat X E)) hbdry
  rw [Work.KT.pairMat_pull_mul hbdry hbdry]
  exact Work.KT.pairMat_pull_congr (upTgt_mul_self X _ _ hA hB h1)
    (dnTgt_mul_self X _ _ hA hB h1) _ _

theorem reindex_tgtPair_mul_self {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
    (hbdry : (upTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (dnTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    (Matrix.reindex (idxEquiv n) (idxEquiv n) (tgtPair X E hbdry)) *
        (Matrix.reindex (idxEquiv n) (idxEquiv n) (tgtPair X E hbdry))
      = Matrix.reindex (idxEquiv n) (idxEquiv n) (tgtPair X E hbdry) := by
  rw [Work.KT.reindexMul, tgtPair_mul_self X E hE hbdry]

/-! ## The Bott periodicity computation for the Bott unit of an idempotent -/

theorem kappa_bott_gen (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Work.KT.Fund.pullMat X (1 - E)
        + (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X E)
    (μ : Work.KT.K0 C(X × S2, ℂ) →+ Work.KT.K0 C(X × S2, ℂ) →+ Work.KT.K0 C(X × S2, ℂ))
    (hμ : Work.KT.IsK0Mul μ) :
    Work.KT.Fund.kappa X n u
      = Work.KT.EG.fstStar X (Work.KT.cls (⟨n, 1 - E⟩ : Work.KT.Mat C(X, ℂ)))
        + μ (Work.KT.EG.fstStar X (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ))))
            (Work.KT.EG.gammaHopf X) := by
  classical
  -- ### the boundary data of the two discs
  have h12 := (Rhop_bdry X).1
  have hhop := (Rhop_bdry X).2
  obtain ⟨_hUpEq, _hDnEq, hrel1, hrel2, hrel3, hrel4⟩ := Rhop_chart X
  have hR := mvN_R12_RhopHop X h12 hhop hrel1 hrel2 hrel3 hrel4
  have hbd := bottUnit_bdry X E hE
  have hbdry := hbd.2.2
  have hu₁' := hbd.1
  have hu₂' := hbd.2.1
  have hret := retract_frames X (Amat X E) (Bmat X E)
    (Amat_mul_self X E hE) (Bmat_mul_self X E hE) (Amat_add_Bmat X E)
  -- ### it suffices to compare the two classes after `k0Glue`
  refine (Work.KT.Fund.k0Glue X).injective ?_
  have hL : Work.KT.Fund.k0Glue X (Work.KT.Fund.kappa X n u)
      = Work.KT.cls (Work.KT.Fund.clutchIdem X n u
          (Work.KT.Fund.liftOf X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
          (Work.KT.Fund.liftOf X ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
            Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
          (Work.KT.Fund.liftOf_spec X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
          (Work.KT.Fund.liftOf_spec X ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
            Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))) := by
    rw [Work.KT.Fund.kappa_val]
    exact (Work.KT.Fund.k0Glue X).apply_symm_apply _
  -- ### the explicit reindexed clutching data
  set SA₁ : Matrix (Fin n) (Fin (n + n * 2)) C(X × Ball ℂ, ℂ) :=
    Matrix.reindex (Equiv.refl (Fin n)) (idxEquiv n) (upRet X (Amat X E) (Bmat X E)) with hSA₁
  set SA₂ : Matrix (Fin n) (Fin (n + n * 2)) C(X × Ball ℂ, ℂ) :=
    Matrix.reindex (Equiv.refl (Fin n)) (idxEquiv n) (dnRet X (Amat X E) (Bmat X E)) with hSA₂
  set TB₁ : Matrix (Fin (n + n * 2)) (Fin n) C(X × Ball ℂ, ℂ) :=
    Matrix.reindex (idxEquiv n) (Equiv.refl (Fin n)) (upFrame X (Amat X E) (Bmat X E)) with hTB₁
  set TB₂ : Matrix (Fin (n + n * 2)) (Fin n) C(X × Ball ℂ, ℂ) :=
    Matrix.reindex (idxEquiv n) (Equiv.refl (Fin n)) (dnFrame X (Amat X E) (Bmat X E)) with hTB₂
  set F : Matrix (Fin (n + n * 2)) (Fin (n + n * 2)) ↥(Work.KT.Fund.pullAlg2 X) :=
    Matrix.reindex (idxEquiv n) (idxEquiv n) (tgtPair X E hbdry) with hF
  have h₁ : TB₁ * SA₁ = F.map (Work.KT.Fund.prF X) := by
    rw [hTB₁, hSA₁, Work.KT.reindexMul, hF, Bott.reindex_map_bott]
    simp only [tgtPair, Work.KT.Fund.pairMat_map_prF]
    rfl
  have h₂ : SA₁ * TB₁ = 1 := by
    rw [hTB₁, hSA₁, Work.KT.reindexMul, hret.1, Bott.reindex_one_bott]
  have h₃ : TB₂ * SA₂ = F.map (Work.KT.Fund.prS X) := by
    rw [hTB₂, hSA₂, Work.KT.reindexMul, hF, Bott.reindex_map_bott]
    simp only [tgtPair, Work.KT.Fund.pairMat_map_prS]
    rfl
  have h₄ : SA₂ * TB₂ = 1 := by
    rw [hTB₂, hSA₂, Work.KT.reindexMul, hret.2, Bott.reindex_one_bott]
  have hu₁ : (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
      SA₁.map (⇑(Work.KT.Fund.bdryRestrict X))
      = SA₂.map (⇑(Work.KT.Fund.bdryRestrict X)) := by
    rw [hSA₁, hSA₂, reindex_map_rect, reindex_map_rect,
      ← reindex_refl_refl (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)),
      Work.KT.reindexMul, hu, hu₁']
  have hu₂ : TB₁.map (⇑(Work.KT.Fund.bdryRestrict X))
      = TB₂.map (⇑(Work.KT.Fund.bdryRestrict X)) *
        (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hTB₁, hTB₂, reindex_map_rect, reindex_map_rect,
      ← reindex_refl_refl (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)),
      Work.KT.reindexMul, hu, hu₂']
  -- ### the clutched idempotent is the glued target
  have hmvN := mvN_clutch_of_data X n F u SA₁ SA₂ TB₁ TB₂ h₁ h₂ h₃ h₄ hu₁ hu₂
  have hcl : Work.KT.cls (Work.KT.Fund.clutchIdem X n u
        (Work.KT.Fund.liftOf X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
        (Work.KT.Fund.liftOf X ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
        (Work.KT.Fund.liftOf_spec X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
        (Work.KT.Fund.liftOf_spec X ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))))
      = Work.KT.cls (⟨n + n * 2,
          Matrix.reindex (idxEquiv n) (idxEquiv n) (tgtPair X E hbdry)⟩ :
          Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := by
    refine (Work.KT.cls_eq_of_mvn ?_ (Work.KT.Fund.clutchIdem_isIdem X n u _ _ _ _) hmvN).symm
    rw [hF]
    exact reindex_tgtPair_mul_self X E hE hbdry
  -- ### the class of the glued target
  have htgt := cls_tgt_aux X E hE hbdry h12
  have hkron := kron_cls_eq X E hE h12 hhop hR
  -- ### the class of the right hand side
  have hrhs := k0Glue_RHS X E hE hhop μ hμ
  rw [hL, hcl, htgt, hkron]
  exact hrhs.symm

end

end Work.KT.EG.KLG
