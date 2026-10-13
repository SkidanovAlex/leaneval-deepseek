import Mathlib
import Submission.Work.DSM5b.HCF.Complex
import Submission.Work.DSCOH.chartCech_finite_vanishing
import Submission.Work.DSCOH.ChartULift
import Submission.Work.DSM5b.HCF.ReesGraded
import Submission.Work.DSM5b.HCF.PullCoeff
import Submission.Work.DSM5b.HCF.reesGr_isInternal
import Submission.Work.DSM5b.HCF.reesDegZero
import Submission.Work.DSM5b.HCF.stcPullCoeff_iso_chartCech

set_option maxHeartbeats 1000000

namespace Work.DSM5b.HCF

universe u

open MvPolynomial Polynomial CategoryTheory Work.DSM5b

/-- **Finiteness of the sorted chart Čech cohomology (lifted index type).**  `R` is Noetherian,
`t : Fin n → R`, and the sorted (increasing tuple) complex of the chart coefficient system
`S ↦ chartRing t S` (`Work.DSM5b.chartCoeff`, `Work.DSM5b.stcComplex`) is indexed by
`ULift.{u} (Fin n)` (the index type must live in the same universe as `R`, and `ULift` carries the
standard order).  Claim: every cohomology group of this complex is a finitely generated
`R`-module.

The proof follows the route indicated above.  The Rees module `reesM t = ⨁_d J^d ⊆ R[u]`
(`J = (t_i)`, `Submission/Work/DSM5b/HCF/ReesDefs.lean`) with its grading `reesGr t` is a finitely
generated graded module over `R[X_0,…,X_{n-1}]` (acting by `X_i ↦ t_i u`); the degree-zero parts
of its chart localisations are the chart rings of the blow-up
(`Work.DSM5b.HCF.reesDegZero`), so the sorted chart complex is the chart Čech complex of a finitely
generated graded module (`Work.DSM5b.HCF.stcPullCoeff_iso_chartCech`), whose cohomology is finite
by `Work.DSCOH.chartCech_finite_vanishing`. -/
theorem stcChartCoeff_ulift_finite (n : ℕ) (R : Type u) [CommRing R] [IsNoetherianRing R]
    (t : Fin n → R) (q : ℕ) :
    Module.Finite R ((Work.DSM5b.stcComplex
      (Work.DSM5b.chartCoeff (R := R) (ι := ULift.{u} (Fin n)) (fun i => t i.down))).homology q) := by
  classical
  haveI hgsm : SetLike.GradedSMul (Work.DSCOH.homSub R n) (reesGr t) := reesGr_gradedSMul t
  haveI hdec : DirectSum.Decomposition (reesGr t) := reesGr_isInternal t |>.chooseDecomposition
  haveI hfin : Module.Finite (Work.DSCOH.Poly R n) (↥(reesM t)) := reesM_finite t
  obtain ⟨e, he⟩ := reesDegZero t
  obtain ⟨Φ⟩ := stcPullCoeff_iso_chartCech (n := n) (R := R) (ℳ := reesGr t)
  -- naturality of `(e S).symm` with respect to the restriction maps
  have hf_nat : ∀ (S T : Finset (ULift.{u} (Fin n))) (hST : S ⊆ T)
      (y : ↥(DSMap.Mix2.chartRing (fun i : ULift.{u} (Fin n) => t i.down) S)),
      (pullCoeff (n := n) (R := R) (reesGr t)).res hST (⇑((e S).symm.toLinearMap) y) =
        ⇑((e T).symm.toLinearMap) ((chartCoeff (R := R) (ι := ULift.{u} (Fin n))
          (fun i => t i.down)).res hST y) := by
    intro S T hST y
    have h := he S T hST ((e S).symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    have h2 := congrArg (fun z => (e T).symm z) h
    rw [LinearEquiv.symm_apply_apply] at h2
    exact h2
  -- the morphism of coefficient systems `chartCoeff t' → pullCoeff (reesGr t)`
  let φ : CoeffSys.Hom (chartCoeff (R := R) (ι := ULift.{u} (Fin n)) (fun i => t i.down))
      (pullCoeff (n := n) (R := R) (reesGr t)) :=
    { φ := fun S => ((e S).symm).toLinearMap
      comm := fun S T hST x => (hf_nat S T hST x).symm }
  -- it is a termwise equivalence
  let stcEqv : ∀ q : ℕ, Stc (chartCoeff (R := R) (ι := ULift.{u} (Fin n)) (fun i => t i.down)) q ≃ₗ[R]
      Stc (pullCoeff (n := n) (R := R) (reesGr t)) q :=
    fun q => LinearEquiv.piCongrRight (fun τ : IncrTuple (ι := ULift.{u} (Fin n)) q =>
      (e (tupRng τ.1)).symm)
  have hstc : ∀ q : ℕ, CoeffSys.Hom.stcMap φ q = (stcEqv q).toLinearMap := by
    intro q
    refine LinearMap.ext ?_
    intro x
    funext τ
    rw [CoeffSys.Hom.stcMap_apply]
    rfl
  haveI : ∀ q : ℕ, IsIso ((stcHom φ).f q) := by
    intro q
    rw [stcHom_f, hstc q]
    exact (LinearEquiv.toModuleIso (stcEqv q)).isIso_hom
  haveI : IsIso (stcHom φ) := HomologicalComplex.Hom.isIso_of_components (stcHom φ)
  -- the chart Čech cohomology of the Rees module is finite
  have hchart : Module.Finite R ((Work.DSCOH.chartCech (A := R) (n := n) (M := ↥(reesM t))
      (reesGr t)).homology q) :=
    (Work.DSCOH.chartCech_finite_vanishing (A := R) (n := n) (M := ↥(reesM t))
      (reesGr t)).1 q
  have hiso : stcComplex (chartCoeff (R := R) (ι := ULift.{u} (Fin n)) (fun i => t i.down)) ≅
      Work.DSCOH.chartCech (A := R) (n := n) (M := ↥(reesM t)) (reesGr t) :=
    (asIso (stcHom φ)) ≪≫ Φ
  have hhom : (stcComplex (chartCoeff (R := R) (ι := ULift.{u} (Fin n))
        (fun i => t i.down))).homology q ≅
      (Work.DSCOH.chartCech (A := R) (n := n) (M := ↥(reesM t)) (reesGr t)).homology q :=
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q).mapIso hiso
  exact (Module.Finite.equiv_iff hhom.toLinearEquiv).mpr hchart

end Work.DSM5b.HCF
