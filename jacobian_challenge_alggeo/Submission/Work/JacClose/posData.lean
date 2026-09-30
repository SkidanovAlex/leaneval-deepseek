import Mathlib
import Submission.Work.JacClose.ClosePos
import Submission.Work.JacClose.posCovOrbit
import Submission.Work.JacClose.posSymGalBeta
import Submission.Work.JacClose.symGeomFamilyData
import Submission.Work.JacClose.normal_sym
import Submission.Work.JacClose.normal_sym_tensor
import Submission.Work.JacClose.nonempty_symBCNaming
import Submission.Work.JacClose.isAddSumMapOfInput
import Submission.Work.BNChart.All
import Submission.Work.CurveFacts.All
import Submission.Work.GenusZero.All

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.JacClose

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory MonObj
open scoped Work.GCBasics

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## A6 in the shape of `Work.JacClose.KLLemma.kl_add`

`Work.CurveFacts.kl_add_of_input` states the additivity of `Σ f` with respect to the `hadd`
datum `Work.CurveFacts.IsAddSumMap`; `Work.JacClose.isAddSumMapOfInput` shows that this datum is
a *theorem*, so the additivity of `Σ f` holds for every chart datum.  The statement below is the
`kl_add`-shape of `Work.JacClose.KLLemma` (`[IsProper A.hom]` as an instance argument). -/

/-- **A6, additivity of `Σ f`, in the shape of `Work.JacClose.KLLemma.kl_add`.** -/
theorem kl_add_of_input_of_isProper {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : Work.AbVar.Point C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D] :
    ∀ {A : Work.GCBasics.Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
      (f : C.toOver ⟶ A) {F : Type u} [Field F] [Algebra K F]
      (E E' : Work.GCBasics.Dv C F) (hE : E.IsEffective) (hE' : E'.IsEffective) (n m : ℕ)
      (hn : Work.GCBasics.Ddeg C F E = (n : ℤ)) (hm : Work.GCBasics.Ddeg C F E' = (m : ℤ))
      (hEE' : (E + E').IsEffective),
      Work.Universal.sumDiv D f (E + E') hEE' (n + m) (Work.Universal.ddeg_add hn hm) =
        Work.Universal.sumDiv D f E hE n hn * Work.Universal.sumDiv D f E' hE' m hm := by
  intro A _ _ _ f F _ _ E E' hE hE' n m hn hm hEE'
  exact Work.CurveFacts.kl_add_of_input D
    (fun {A} _ _ f m n => Work.JacClose.isAddSumMapOfInput D f m n)
    f E E' hE hE' n m hn hm hEE'

end

/-- **The `Data` of the final assembly for a curve of genus `≠ 0` and a base point.**  Recipe
(the hard theorems are already proved, this is assembling their outputs):

* `D` from area `BNChart`'s COV′ (B6) at `Work.BNChart.rochDataPos C h` and the base point `P0`,
  with `hstalk` supplied by `Work.JacClose.normal_sym_tensor`;
* `h' : Work.RiemannRoch.Curve.genus (C.baseChange D.k') ≠ 0` from `h`
  (`Work.GenusZero.genus_baseChange`, or `RiemannRoch.Curve.genus_eq`);
* `sy := (Work.JacClose.symGeomFamilyData (C.baseChange D.k') (bcPt) ).some`;
* `hg` from `Work.BNChart.rochDataPos_g` on both sides, then `B := Work.JacClose.posCanonBC`
  with the naming data of `Work.JacClose.nonempty_symBCNaming`;
* `cd := (D.chartsK' (instDivBase _) (rochDataPos _ h') (symGeomFamily _ R'.g) (bcPt) B).toChartDatum`
  so that `Work.JacClose.posChartEq` is `rfl`;
* `hresid` from `Work.JacClose.residOld_of_input` (with `Work.BNChart.ell_bc` and
  `Work.SpecLin.specLin`), `hP0Div` from `Work.CurveFacts.bcKF_ptDiv` (A5) plus
  `Work.JacClose.bcPtK_P0Pt`, `hnorm_g`/`hnorm_gg` from
  `Work.JacClose.normal_sym`/`normal_sym_tensor`;
* `hkl : Work.JacClose.CloseKL` from `Work.CurveFacts.kl_of_input_of_isProper` /
  `kl_add_of_input_of_isProper` (A6, now that `Work.JacClose.KLLemma` carries
  `[IsProper A.hom]` like `Work.Universal.Input`);
* conclude `Work.JacFinal.Data.of_covOrbit` (or `Work.JacClose.closeData`) with
  `hV := cd.isAffineOpen_V` and `hcov := Work.JacClose.posCovOrbit` (C6, proved). -/
theorem posData {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
    (h : Work.RiemannRoch.Curve.genus C ≠ 0)
    (P0 : Work.Charts.unitSch k ⟶ C.toOver) :
    Nonempty (Work.JacFinal.Data C P0) := by
  classical
  -- **(B6)** the Galois-equivariant covering `D` of `Pic⁰` over `k`, with the normality input
  -- of area `NM` (`Work.JacClose.normal_sym`).
  have hstalk : ∀ x : ((Work.SymQuot.symGeomFamily C
      ((Work.BNChart.rochDataPos C h).g + (Work.BNChart.rochDataPos C h).g)).S).left,
      IsIntegrallyClosed (((Work.SymQuot.symGeomFamily C
        ((Work.BNChart.rochDataPos C h).g + (Work.BNChart.rochDataPos C h).g)).S).left.presheaf.stalk x) :=
    fun x => Work.JacClose.normal_sym C
      ((Work.BNChart.rochDataPos C h).g + (Work.BNChart.rochDataPos C h).g) x
  obtain ⟨D⟩ := Work.BNChart.exists_galCharts C h P0 hstalk
  -- the genus of `C_{k'}` is nonzero, and the two successor-shaped genera agree
  have h' : Work.RiemannRoch.Curve.genus (C.baseChange D.k') ≠ 0 := by
    rw [Work.GenusZero.genus_baseChange C D.k']; exact h
  have hgen : (Work.BNChart.rochDataPos (C.baseChange D.k') h').g
      = (Work.BNChart.rochDataPos C h).g :=
    (Work.BNChart.rochDataPos_g (C.baseChange D.k') h').trans
      ((Work.GenusZero.genus_baseChange C D.k').trans
        (Work.BNChart.rochDataPos_g C h).symm)
  -- **(SY)** the `SY`-side data over `k'`, for the concrete family of symmetric powers
  obtain ⟨sy⟩ := Work.JacClose.symGeomFamilyData (C.baseChange D.k')
    (Work.JacFinal.bcPt C P0 D.k')
  -- **(C1)** the naming data of the base-change comparison of symmetric powers
  obtain ⟨naming⟩ := Work.JacClose.nonempty_symBCNaming (L := D.k') C
    (Work.BNChart.rochDataPos (C.baseChange D.k') h')
  -- **(B7)** the comparison `B` of symmetric powers over `k'`
  let B := Work.JacClose.posCanonBC (C := C) (P0 := P0) h D h' hgen naming.Q' naming.U'
    naming.hU' naming.h' naming.h_mem' naming.h_span'
  -- **(C2)** the Brill–Noether chart datum over `k'`, transported along `B`
  let cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _
      (Work.BNChart.rochDataPos (C.baseChange D.k') h')
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
      (Work.JacFinal.bcPt C P0 D.k') :=
    (D.chartsK' (Work.SymQuot.instDivBase (C.baseChange D.k'))
      (Work.BNChart.rochDataPos (C.baseChange D.k') h')
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
      (Work.JacFinal.bcPt C P0 D.k') B).toChartDatum
  -- **(DM)** the RESID data, from the `SY`-side data, RR7, `ell_bc` and SPEC-LIN
  let RD : Work.Domain.Resid.ResidData (K := D.k')
      (Work.SymQuot.symGeomFamily (C.baseChange D.k'))
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g :=
    { addMap := sy.addMap
      addMap_divOf := sy.addMap_divOf
      rr7 := Work.JacFinal.rr7_of_rochData (Work.BNChart.rochDataPos (C.baseChange D.k') h')
      isProper := sy.isProper_Sym
      locallyOfFiniteType := sy.locallyOfFiniteType_Sym
      ell_bc := fun e A => Work.BNChart.ell_bc e A
      specLin := fun G R _ _ _ _ a b => Work.SpecLin.specLin G R a b }
  -- **(DM)** the `resid_exists` field of the chart datum
  have hresid : Work.JacClose.ResidOld (C.baseChange D.k')
      (Work.SymQuot.symGeomFamily (C.baseChange D.k'))
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g sy.isProper_Sym := by
    intro X _ _ hX r m a b hm
    exact ⟨_, Work.Domain.Resid.ResidMap.toResid
      (RD.residMap_spec hX (inferInstance : IsReduced X.left)
        (by haveI := sy.isProper_Sym m; exact inferInstance) a b hm)⟩
  -- **(A5)** the divisor of the base point is compatible with base change of the field
  have hP0Div : ∀ {F : Type u} [Field F] [Algebra D.k' F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (Work.JacFinal.bcPt C P0 D.k') F)
        = Work.GroupChunk.bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
            (Work.JacFinal.bcPt C P0 D.k') D.k')) := by
    intro F _ _
    have h1 : Work.SpecLin.RPt.map (Algebra.ofId D.k' F)
        (Work.Universal.P0Pt (C.baseChange D.k') (Work.JacFinal.bcPt C P0 D.k') D.k')
        = Work.Universal.P0Pt (C.baseChange D.k') (Work.JacFinal.bcPt C P0 D.k') F :=
      Work.Charts.RPt_map_toCurveFPt (C := C.baseChange D.k')
        (P0 := Work.JacFinal.bcPt C P0 D.k') (e := Algebra.ofId D.k' F)
    exact ((Work.CurveFacts.bcKF_ptDiv (C := C.baseChange D.k')
      (x := Work.Universal.P0Pt (C.baseChange D.k') (Work.JacFinal.bcPt C P0 D.k') D.k')
      (F := F)).trans (congrArg Work.SpecLin.ptDiv h1)).symm
  -- **(NM)** the normality of the symmetric power and of its square
  have hnorm_g : ∀ x : ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S).left,
      IsIntegrallyClosed (((Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S).left.presheaf.stalk x) :=
    fun x => Work.JacClose.normal_sym (C.baseChange D.k')
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g x
  have hnorm_gg : ∀ x : (((Work.SymQuot.symGeomFamily (C.baseChange D.k')
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)
      ⊗ ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)).left,
      IsIntegrallyClosed ((((Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)
        ⊗ ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)).left.presheaf.stalk x) :=
    fun x => Work.JacClose.normal_sym_tensor (C.baseChange D.k')
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g x
  -- **(A6)** the key lemma for the chart datum `gcInputOf`
  have hkl : Work.JacClose.CloseKL (C := C) (P0 := P0) D sy
      (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd hresid hP0Div hnorm_g hnorm_gg := by
    letI hsym : Work.Universal.SymQuotData (C.baseChange D.k')
        (Work.JacFinal.bcPt C P0 D.k')
        (Work.JacClose.gcInputOf (C := C) (P0 := P0) D sy
          (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd hresid hP0Div
          hnorm_g hnorm_gg) :=
      Work.JacClose.symQuotDataOf (C := C) (P0 := P0) D sy
        (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd hresid hP0Div hnorm_g hnorm_gg
    refine ⟨?_, ?_⟩
    · intro A _ _ hA f F _ _ E E' hE hE' n hn hn' hlin
      exact Work.CurveFacts.kl_of_input_of_isProper
        (Work.JacClose.gcInputOf (C := C) (P0 := P0) D sy
          (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd hresid hP0Div
          hnorm_g hnorm_gg) hA f E E' hE hE' n hn hn' hlin
    · exact Work.JacClose.kl_add_of_input_of_isProper
        (Work.JacClose.gcInputOf (C := C) (P0 := P0) D sy
          (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd hresid hP0Div hnorm_g hnorm_gg)
  -- **(C6)** the class-level `Γ`-orbit statement
  have hcov := Work.JacClose.posCovOrbit (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
    hnorm_gg hkl hgen naming.Q' naming.U' naming.hU' naming.h' naming.h_mem' naming.h_span'
    (by
      show cd = (D.chartsK' (Work.SymQuot.instDivBase (C.baseChange D.k'))
        (Work.BNChart.rochDataPos (C.baseChange D.k') h')
        (Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
        (Work.JacFinal.bcPt C P0 D.k')
        (Work.JacClose.posCanonBC (C := C) (P0 := P0) h D h' hgen naming.Q' naming.U'
          naming.hU' naming.h' naming.h_mem' naming.h_span')).toChartDatum
      rfl)
  refine ⟨Work.JacFinal.Data.of_covOrbit
    (Work.JacClose.posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g hnorm_gg
      hkl) ⟨?_, hcov⟩⟩
  exact cd.isAffineOpen_V

end Work.JacClose
