/-
# `BridgeSquare/subtorusBoundaries_of_fibreIdent.lean`

From the three *fibre identities* (the hypotheses `hA`, `hB`, `hT`: the singular `1`- and
`2`-chains of `M̄` obtained by pushing the `Δ`-generators of `H_1(T²)`, `H_2(T²)` along the
subtorus map `F_v` differ from the corresponding *cellular* loops of `Gen.mbarCx` — pushed through
the comparison `Ψ_M = PsiM` — by a boundary) to `Work.BridgeSquare.SubtorusBoundaries`.

The mathematics is entirely finite: by `Gen.fibreLoop_bd` and `Gen.planeCycle_bd` the cellular
fibre loops `fibreLoopVec v j` and the plane cycles `planeCycleVec v 0` are *themselves*
boundaries of `Gen.mbarCx` (`∂ (fibreWitVec v j) = fibreLoopVec v j`,
`∂ (planeWitVec v 0) = planeCycleVec v 0`).  Since `PsiM` is a chain map, their `PsiM`-images are
boundaries of the singular chains of `M̄`; adding the witness of the fibre identity to such a
null-homology produces the required boundary.

All the explicit matrix computations are performed in the *numeral* presentation
(`MbarBd1 : Matrix (Fin 168) (Fin 192) ℤ` etc.), where the type class inference of `*` on
matrices does not have to see through `mbarDim`; the `mbarDim`-indexed statements of the chain
complex are recovered by definitional unfolding (`rfl`).
-/
import Mathlib
import Submission.Work.BridgeSquare.FibreData
import Submission.Work.BridgeSquare.subtorusNull_of_boundaries
import Submission.Work.Certificates.SOp.eqb_sound
import Submission.Work.Certificates.SVec.eqb_sound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.BridgeSquare

open Work.Certificates
open Work.HomologyIso.Gen (mbarDim mbarBd mbarCx)

noncomputable section

/-! ## §1  Positioning of the columns

The `(v, j)`-th fibre loop is the column `2v + j` of the `SOp` `Gen.fibreLoop`, and the `v`-th
plane cycle is the column `v` of `Gen.planeCycle`. -/

/-- The column of `Gen.fibreLoop` / `Gen.fibreWit` corresponding to `(v, j)`. -/
def fidx (v : Fin 5) (j : Fin 2) : Fin 10 := ⟨2 * (v : ℕ) + (j : ℕ), by omega⟩

/-- The column of `Gen.planeCycle` / `Gen.planeWit` corresponding to `v`. -/
def pidx (v : Fin 5) : Fin 5 := ⟨(v : ℕ), v.2⟩

/-! ## §2  The boundary operators in the numeral presentation -/

/-- `∂₁ : C₁ → C₀` of `Gen.mbarCx`, as a `168 × 192` matrix over `ℤ`. -/
def MbarBd1 : Matrix (Fin 168) (Fin 192) ℤ := (mbarBd 1).toMatrix

/-- `∂₂ : C₂ → C₁` of `Gen.mbarCx`, as a `192 × 72` matrix over `ℤ`. -/
def MbarBd2 : Matrix (Fin 192) (Fin 72) ℤ := (mbarBd 2).toMatrix

/-- The matrix of the ten fibre loops. -/
def fibreLoopM : Matrix (Fin 168) (Fin 10) ℤ := Gen.fibreLoop.toMatrix

/-- The matrix of the ten fibre null-homologies. -/
def fibreWitM : Matrix (Fin 192) (Fin 10) ℤ := Gen.fibreWit.toMatrix

/-- The matrix of the five plane cycles. -/
def planeCycleM : Matrix (Fin 192) (Fin 5) ℤ := Gen.planeCycle.toMatrix

/-- The matrix of the five plane null-homologies. -/
def planeWitM : Matrix (Fin 72) (Fin 5) ℤ := Gen.planeWit.toMatrix

/-- `∂₁ ∘ fibreWit` in the numeral presentation. -/
def mulM1 : Matrix (Fin 168) (Fin 10) ℤ := ((mbarBd 1).mul Gen.fibreWit).toMatrix

/-- `∂₂ ∘ planeWit` in the numeral presentation. -/
def mulM2 : Matrix (Fin 192) (Fin 5) ℤ := ((mbarBd 2).mul Gen.planeWit).toMatrix

/-! ## §3  The explicit loops are the columns of the matrices -/

theorem fibreLoopVec_eq_colT (v : Fin 5) (j : Fin 2) :
    fibreLoopVec v j = fun i => Gen.fibreLoop.toMatrix i (fidx v j) := by
  fin_cases v <;> fin_cases j <;> decide

theorem fibreWitVec_eq_colT (v : Fin 5) (j : Fin 2) :
    fibreWitVec v j = fun i => Gen.fibreWit.toMatrix i (fidx v j) := by
  fin_cases v <;> fin_cases j <;> decide

theorem planeCycleVec_eq_colT (v : Fin 5) (j : Fin 2) :
    planeCycleVec v j = fun i => Gen.planeCycle.toMatrix i (pidx v) := by
  fin_cases v <;> fin_cases j <;> decide

theorem planeWitVec_eq_colT (v : Fin 5) (j : Fin 2) :
    planeWitVec v j = fun i => Gen.planeWit.toMatrix i (pidx v) := by
  fin_cases v <;> fin_cases j <;> decide

/-! ## §4  The cellular null-homologies in the numeral presentation -/

theorem mulM1_eq_fibreLoopM : mulM1 = fibreLoopM := SOp.eqb_sound Gen.fibreLoop_bd

theorem mulM1_eq_mul : MbarBd1 * fibreWitM = mulM1 :=
  (SOp.toMatrix_mul (mbarBd 1) Gen.fibreWit).symm

theorem mulM2_eq_planeCycleM : mulM2 = planeCycleM := SOp.eqb_sound Gen.planeCycle_bd

theorem mulM2_eq_mul : MbarBd2 * planeWitM = mulM2 :=
  (SOp.toMatrix_mul (mbarBd 2) Gen.planeWit).symm

theorem MbarBd1_mulVec_fibreWit (v : Fin 5) (j : Fin 2) :
    Matrix.mulVec MbarBd1 (fibreWitVec v j) = fibreLoopVec v j := by
  have hwit : ∀ k : Fin 192, fibreWitVec v j k = fibreWitM k (fidx v j) :=
    fun k => congrFun (fibreWitVec_eq_colT v j) k
  funext i
  rw [Matrix.mulVec_apply_eq_sum]
  calc ∑ k : Fin 192, MbarBd1 i k * fibreWitVec v j k
      = ∑ k : Fin 192, MbarBd1 i k * fibreWitM k (fidx v j) :=
        Finset.sum_congr rfl (fun k _ => by rw [hwit k])
    _ = (MbarBd1 * fibreWitM) i (fidx v j) := Matrix.mul_apply.symm
    _ = mulM1 i (fidx v j) := by rw [mulM1_eq_mul]
    _ = fibreLoopM i (fidx v j) := by rw [mulM1_eq_fibreLoopM]
    _ = fibreLoopVec v j i := (congrFun (fibreLoopVec_eq_colT v j) i).symm

theorem MbarBd2_mulVec_planeWit (v : Fin 5) (j : Fin 2) :
    Matrix.mulVec MbarBd2 (planeWitVec v j) = planeCycleVec v j := by
  have hwit : ∀ k : Fin 72, planeWitVec v j k = planeWitM k (pidx v) :=
    fun k => congrFun (planeWitVec_eq_colT v j) k
  funext i
  rw [Matrix.mulVec_apply_eq_sum]
  calc ∑ k : Fin 72, MbarBd2 i k * planeWitVec v j k
      = ∑ k : Fin 72, MbarBd2 i k * planeWitM k (pidx v) :=
        Finset.sum_congr rfl (fun k _ => by rw [hwit k])
    _ = (MbarBd2 * planeWitM) i (pidx v) := Matrix.mul_apply.symm
    _ = mulM2 i (pidx v) := by rw [mulM2_eq_mul]
    _ = planeCycleM i (pidx v) := by rw [mulM2_eq_planeCycleM]
    _ = planeCycleVec v j i := (congrFun (planeCycleVec_eq_colT v j) i).symm

/-! ## §5  The cellular null-homologies, in the chain complex `Gen.mbarCx` -/

theorem mbarCx_d21_fibreWit (v : Fin 5) (j : Fin 2) :
    (mbarCx.toChainComplex).d 2 1 (fibreWitVec v j) = fibreLoopVec v j := by
  have h : (mbarCx.toChainComplex).d 2 1 (fibreWitVec v j)
      = MbarBd1.mulVec (fibreWitVec v j) := rfl
  exact h.trans (MbarBd1_mulVec_fibreWit v j)

theorem mbarCx_d32_planeWit (v : Fin 5) (j : Fin 2) :
    (mbarCx.toChainComplex).d 3 2 (planeWitVec v j) = planeCycleVec v j := by
  have h : (mbarCx.toChainComplex).d 3 2 (planeWitVec v j)
      = MbarBd2.mulVec (planeWitVec v j) := rfl
  exact h.trans (MbarBd2_mulVec_planeWit v j)

/-! ## §6  The images of the null-homologies under the chain map `Ψ_M` -/

/-- The chain-map identity `D.d (n+1) n (φ.f (n+1) x) = φ.f n (C.d (n+1) n x)`,
evaluated on an element. -/
theorem chainMap_d_apply {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) (n : ℕ)
    (x : ↑(C.X (n + 1))) :
    D.d (n + 1) n (φ.f (n + 1) x) = φ.f n (C.d (n + 1) n x) := by
  have h := congrArg (fun f => f x) (φ.comm (n + 1) n)
  rwa [ModuleCat.comp_apply, ModuleCat.comp_apply] at h

/-- `∂ (Ψ_M(fibreWitVec v j)) = Ψ_M(fibreLoopVec v j)`. -/
theorem PsiM_d_fibreWit (v : Fin 5) (j : Fin 2) :
    ((singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1)
        (PsiM.f 2 (fibreWitVec v j))
      = PsiM.f 1 (fibreLoopVec v j) := by
  have h := chainMap_d_apply PsiM 1 (fibreWitVec v j)
  have h2 := congrArg (PsiM.f 1) (mbarCx_d21_fibreWit v j)
  exact h.trans h2

/-- `∂ (Ψ_M(planeWitVec v 0)) = Ψ_M(planeCycleVec v 0)`. -/
theorem PsiM_d_planeWit (v : Fin 5) :
    ((singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 3 2)
        (PsiM.f 3 (planeWitVec v 0))
      = PsiM.f 2 (planeCycleVec v 0) := by
  have h := chainMap_d_apply PsiM 2 (planeWitVec v 0)
  have h2 := congrArg (PsiM.f 2) (mbarCx_d32_planeWit v 0)
  exact h.trans h2

/-! ## §7  The assembly -/

theorem subtorusBoundaries_of_fibreIdent
    (hA : ∀ v : Fin 5, ∃ y : ↑((Work.BridgeSquare.singCxFun.obj
            (TopCat.of Work.FoldInst.Mbar)).X 2),
        ((Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1) y
          = Work.BridgeSquare.singA v
            - (Work.BridgeSquare.PsiM.f 1) (Work.BridgeSquare.fibreLoopVec v 0))
    (hB : ∀ v : Fin 5, ∃ y : ↑((Work.BridgeSquare.singCxFun.obj
            (TopCat.of Work.FoldInst.Mbar)).X 2),
        ((Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1) y
          = Work.BridgeSquare.singB v
            - (Work.BridgeSquare.PsiM.f 1) (Work.BridgeSquare.fibreLoopVec v 1))
    (hT : ∀ v : Fin 5, ∃ y : ↑((Work.BridgeSquare.singCxFun.obj
            (TopCat.of Work.FoldInst.Mbar)).X 3),
        ((Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 3 2) y
          = Work.BridgeSquare.singT v
            - (Work.BridgeSquare.PsiM.f 2) (Work.BridgeSquare.planeCycleVec v 0)) :
    Work.BridgeSquare.SubtorusBoundaries := by
  intro v
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hA v
    refine ⟨y + PsiM.f 2 (fibreWitVec v 0), ?_⟩
    rw [map_add, hy, PsiM_d_fibreWit v 0, sub_add_cancel]
  · obtain ⟨y, hy⟩ := hB v
    refine ⟨y + PsiM.f 2 (fibreWitVec v 1), ?_⟩
    rw [map_add, hy, PsiM_d_fibreWit v 1, sub_add_cancel]
  · obtain ⟨y, hy⟩ := hT v
    refine ⟨y + PsiM.f 3 (planeWitVec v 0), ?_⟩
    rw [map_add, hy, PsiM_d_planeWit v, sub_add_cancel]

end

end Work.BridgeSquare
