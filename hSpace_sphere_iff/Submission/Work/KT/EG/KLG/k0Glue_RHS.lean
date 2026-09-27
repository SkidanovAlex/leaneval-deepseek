import Mathlib
import Submission.Work.KT.EG.KLG.kappa_bott_defs

namespace Work.KT.EG.KLG

open _root_.Matrix
open Work.KT

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

noncomputable section

section Helpers

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## The glue interface for `glueEquiv`

(`Work.KT.KL.Helpers` proves `glue_pullAlg_fst`/`glue_pullAlg_snd`, but importing it together with
`kappa_bott_defs` clashes (`Work.KT.Fund.continuous_recipB`), so the two lemmas are re-proved
locally.) -/

/-- The `glueEquiv`-image of a matrix pulled back along the first projection, as a pair matrix. -/
lemma glueEquiv_pullAlg_fst {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (M.map (⇑(pullAlg (ContinuousMap.fst : C(X × S2, X))))).map
        (⇑(Work.KT.Fund.glueEquiv X))
      = Work.KT.Fund.pairMat X (Work.KT.Fund.KC.gUp X M) (Work.KT.Fund.KC.gUp X M) rfl := by
  apply Work.KT.Fund.mat_ext X
  · rw [_root_.Matrix.map_map, Work.KT.Fund.pairMat_map_prF]
    apply _root_.Matrix.ext
    intro i j
    rfl
  · rw [_root_.Matrix.map_map, Work.KT.Fund.pairMat_map_prS]
    apply _root_.Matrix.ext
    intro i j
    rfl

/-- The `glueEquiv`-image of the Hopf idempotent pulled back along the second projection. -/
lemma glueEquiv_pullAlg_snd
    (hRupdn : (Work.KT.Fund.KL.RhopUp X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.Fund.KL.RhopDn X).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    ((hopfIdem.2 : Matrix (Fin 2) (Fin 2) C(S2, ℂ)).map
        (⇑(pullAlg (ContinuousMap.snd : C(X × S2, S2))))).map
        (⇑(Work.KT.Fund.glueEquiv X))
      = Work.KT.Fund.pairMat X (Work.KT.Fund.KL.RhopUp X) (Work.KT.Fund.KL.RhopDn X)
          hRupdn := by
  ext i j <;> rfl

/-! ## Naturality of `k0Glue` on the two summands -/

/-- `k0Glue` sends the pull-back of `[M]` along the first projection to the class of
`trivPair X M`. -/
lemma k0Glue_fstStar_cls {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (hM : M * M = M) :
    (Work.KT.Fund.k0Glue X)
        (Work.KT.EG.fstStar X (Work.KT.cls (⟨n, M⟩ : Work.KT.Mat C(X, ℂ))))
      = Work.KT.cls (⟨n, Work.KT.EG.KLG.trivPair X M⟩ :
          Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := by
  have hMid : Work.KT.Mat.IsIdem (⟨n, M⟩ : Work.KT.Mat C(X, ℂ)) := hM
  have hMP : (Work.KT.Mat.map (pullAlg (ContinuousMap.fst : C(X × S2, X))).toRingHom
      (⟨n, M⟩ : Work.KT.Mat C(X, ℂ))).IsIdem := Work.KT.Mat.map_idem _ hMid
  show Work.KT.K0.map (Work.KT.Fund.glueEquiv X :
        C(X × S2, ℂ) →+* ↥(Work.KT.Fund.pullAlg2 X))
      (Work.KT.K0.map (pullAlg (ContinuousMap.fst : C(X × S2, X))).toRingHom
        (Work.KT.cls (⟨n, M⟩ : Work.KT.Mat C(X, ℂ))))
    = Work.KT.cls (⟨n, Work.KT.EG.KLG.trivPair X M⟩ :
        Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
  rw [Work.KT.K0.map_cls (pullAlg (ContinuousMap.fst : C(X × S2, X))).toRingHom hMid,
      Work.KT.K0.map_cls (Work.KT.Fund.glueEquiv X :
        C(X × S2, ℂ) →+* ↥(Work.KT.Fund.pullAlg2 X)) hMP]
  exact congrArg Work.KT.cls
    (congrArg (fun N => (⟨n, N⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)))
      (glueEquiv_pullAlg_fst X M))

/-- `k0Glue` sends the Hopf class `γ` to the class of `RhopPair`. -/
lemma k0Glue_gammaHopf
    (hhop : (Work.KT.Fund.KL.RhopUp X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.Fund.KL.RhopDn X).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    (Work.KT.Fund.k0Glue X) (Work.KT.EG.gammaHopf X)
      = Work.KT.cls (⟨2, Work.KT.EG.KLG.RhopPair X hhop⟩ :
          Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := by
  have hhid : Work.KT.Mat.IsIdem hopfIdem :=
    Work.KT.Fund.twoByTwo_idem_of_trace_det _ Work.KT.Fund.hopf_trace_det.1
      Work.KT.Fund.hopf_trace_det.2
  have hHU : (Work.KT.Mat.map (pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom
      hopfIdem).IsIdem := Work.KT.Mat.map_idem _ hhid
  show Work.KT.K0.map (Work.KT.Fund.glueEquiv X :
        C(X × S2, ℂ) →+* ↥(Work.KT.Fund.pullAlg2 X))
      (Work.KT.K0.map (pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom
        (Work.KT.cls hopfIdem))
    = Work.KT.cls (⟨2, Work.KT.EG.KLG.RhopPair X hhop⟩ :
        Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
  rw [Work.KT.K0.map_cls (pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom hhid,
      Work.KT.K0.map_cls (Work.KT.Fund.glueEquiv X :
        C(X × S2, ℂ) →+* ↥(Work.KT.Fund.pullAlg2 X)) hHU]
  exact congrArg Work.KT.cls
    (congrArg (fun N => (⟨2, N⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)))
      (glueEquiv_pullAlg_snd X hhop))

/-- `k0Glue` sends the product `μ (fst* [E]) γ` to the class of the Kronecker product. -/
lemma k0Glue_mu_fstStar_gamma {n : ℕ}
    (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
    (hhop : (Work.KT.Fund.KL.RhopUp X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.Fund.KL.RhopDn X).map (fun f => Work.KT.Fund.bdryRestrict X f))
    (μ : Work.KT.K0 C(X × S2, ℂ) →+ Work.KT.K0 C(X × S2, ℂ) →+ Work.KT.K0 C(X × S2, ℂ))
    (hμ : Work.KT.IsK0Mul μ) :
    (Work.KT.Fund.k0Glue X)
        (μ (Work.KT.EG.fstStar X (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ))))
            (Work.KT.EG.gammaHopf X))
      = Work.KT.cls (Work.KT.Mat.kron
          (⟨n, Work.KT.EG.KLG.trivPair X E⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
          (⟨2, Work.KT.EG.KLG.RhopPair X hhop⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))) := by
  have hhid : Work.KT.Mat.IsIdem hopfIdem :=
    Work.KT.Fund.twoByTwo_idem_of_trace_det _ Work.KT.Fund.hopf_trace_det.1
      Work.KT.Fund.hopf_trace_det.2
  have hEid : Work.KT.Mat.IsIdem (⟨n, E⟩ : Work.KT.Mat C(X, ℂ)) := hE
  have hEP : (Work.KT.Mat.map (pullAlg (ContinuousMap.fst : C(X × S2, X))).toRingHom
      (⟨n, E⟩ : Work.KT.Mat C(X, ℂ))).IsIdem := Work.KT.Mat.map_idem _ hEid
  have hHP : (Work.KT.Mat.map (pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom
      hopfIdem).IsIdem := Work.KT.Mat.map_idem _ hhid
  have hK : (Work.KT.Mat.kron
      (Work.KT.Mat.map (pullAlg (ContinuousMap.fst : C(X × S2, X))).toRingHom
        (⟨n, E⟩ : Work.KT.Mat C(X, ℂ)))
      (Work.KT.Mat.map (pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom
        hopfIdem)).IsIdem :=
    Work.KT.Mat.kron_idem (fun x y => mul_comm x y) hEP hHP
  have h1 : Work.KT.Mat.map (Work.KT.Fund.glueEquiv X :
        C(X × S2, ℂ) →+* ↥(Work.KT.Fund.pullAlg2 X))
      (Work.KT.Mat.map (pullAlg (ContinuousMap.fst : C(X × S2, X))).toRingHom
        (⟨n, E⟩ : Work.KT.Mat C(X, ℂ)))
      = (⟨n, Work.KT.EG.KLG.trivPair X E⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := by
    show (⟨n, (E.map ⇑(pullAlg (ContinuousMap.fst : C(X × S2, X)))).map
        ⇑(Work.KT.Fund.glueEquiv X)⟩ :
          Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) = _
    exact congrArg (fun N => (⟨n, N⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)))
      (glueEquiv_pullAlg_fst X E)
  have h2 : Work.KT.Mat.map (Work.KT.Fund.glueEquiv X :
        C(X × S2, ℂ) →+* ↥(Work.KT.Fund.pullAlg2 X))
      (Work.KT.Mat.map (pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom hopfIdem)
      = (⟨2, Work.KT.EG.KLG.RhopPair X hhop⟩ :
          Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := by
    show (⟨2, (hopfIdem.2.map ⇑(pullAlg (ContinuousMap.snd : C(X × S2, S2)))).map
        ⇑(Work.KT.Fund.glueEquiv X)⟩ :
          Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) = _
    exact congrArg (fun N => (⟨2, N⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)))
      (glueEquiv_pullAlg_snd X hhop)
  show Work.KT.K0.map (Work.KT.Fund.glueEquiv X :
        C(X × S2, ℂ) →+* ↥(Work.KT.Fund.pullAlg2 X))
      (μ (Work.KT.K0.map (pullAlg (ContinuousMap.fst : C(X × S2, X))).toRingHom
            (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ))))
        (Work.KT.K0.map (pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom
            (Work.KT.cls hopfIdem)))
    = Work.KT.cls (Work.KT.Mat.kron
        (⟨n, Work.KT.EG.KLG.trivPair X E⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
        (⟨2, Work.KT.EG.KLG.RhopPair X hhop⟩ :
          Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)))
  rw [Work.KT.K0.map_cls (pullAlg (ContinuousMap.fst : C(X × S2, X))).toRingHom hEid,
      Work.KT.K0.map_cls (pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom hhid]
  rw [Work.KT.IsK0Mul_cls hμ hEP hHP]
  rw [Work.KT.K0.map_cls (Work.KT.Fund.glueEquiv X :
        C(X × S2, ℂ) →+* ↥(Work.KT.Fund.pullAlg2 X)) hK]
  rw [Work.KT.Mat.map_kron (Work.KT.Fund.glueEquiv X :
        C(X × S2, ℂ) →+* ↥(Work.KT.Fund.pullAlg2 X))]
  rw [h1, h2]

end Helpers

theorem k0Glue_RHS (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
    (hhop : (Work.KT.Fund.KL.RhopUp X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.Fund.KL.RhopDn X).map (fun f => Work.KT.Fund.bdryRestrict X f))
    (μ : Work.KT.K0 C(X × Work.KT.S2, ℂ) →+ Work.KT.K0 C(X × Work.KT.S2, ℂ) →+
      Work.KT.K0 C(X × Work.KT.S2, ℂ))
    (hμ : Work.KT.IsK0Mul μ) :
    Work.KT.Fund.k0Glue X
        (Work.KT.EG.fstStar X (Work.KT.cls (⟨n, 1 - E⟩ : Work.KT.Mat C(X, ℂ)))
          + μ (Work.KT.EG.fstStar X (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ))))
              (Work.KT.EG.gammaHopf X))
      = Work.KT.cls (⟨n, Work.KT.EG.KLG.trivPair X (1 - E)⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
        + Work.KT.cls (Work.KT.Mat.kron
            (⟨n, Work.KT.EG.KLG.trivPair X E⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
            (⟨2, Work.KT.EG.KLG.RhopPair X hhop⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))) := by
  have hA0 : (1 - E) * (1 - E) = 1 - E := by
    rw [sub_mul, _root_.Matrix.one_mul, _root_.Matrix.mul_sub, _root_.Matrix.mul_one, hE,
      sub_self, sub_zero]
  rw [map_add, k0Glue_fstStar_cls X (1 - E) hA0, k0Glue_mu_fstStar_gamma X E hE hhop μ hμ]

end

end Work.KT.EG.KLG
