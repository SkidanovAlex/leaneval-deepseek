import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.FirstPage.HomElts
import Submission.Work.SSS.FirstPageCF.ZsqElts

namespace Work.SSS.FirstPageCF

/-- If an `n`-cycle `x` of `F_s` has the same `E¹`-class as an element `z` of the model `Zsq`
(under `jF` respectively `psi`), then `z` and the projection of `x` differ by a boundary in the
graded piece `grF ξ.F s`. -/
lemma sub_mem_range_of_jF_homologypi {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C)
    (s t : ℕ) (hs : 2 ≤ s)
    (z : ↥(Work.SSS.Zsq ξ s (s+t)))
    (x : (ξ.F.obj s).X (s+t))
    (hx : (Work.SSS.dFs ξ s (s+t) ((s+t)-1)) x = 0)
    (h : (Work.SSS.jF ξ s t).hom ((HomologicalComplex.homologyπ (ξ.F.obj s) (s+t))
          ((ξ.F.obj s).cyclesMk x ((s+t)-1) (Work.SSS.next_down_eq_pred (s+t)) hx))
        = Work.SSS.FirstPageCF.psi ξ s t hs z) :
    (z : (Work.SSS.grF ξ.F s).X (s+t)) - Work.SSS.projQ ξ s (s+t) x
      ∈ LinearMap.range ((Work.SSS.grF ξ.F s).d ((s+t)+1) (s+t)).hom := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  have hj : (ComplexShape.down ℕ).next ((k+2)+t) = ((k+2)+t)-1 := Work.SSS.next_down_eq_pred _
  have hzcyc : ((Work.SSS.grF ξ.F (k+2)).d ((k+2)+t) (((k+2)+t)-1)).hom
      (z : (Work.SSS.grF ξ.F (k+2)).X ((k+2)+t)) = 0 :=
    Work.SSS.FirstPageCF.Zsq_d_eq_zero ξ (k+2) ((k+2)+t) (by omega) z
  have hpxcyc : ((Work.SSS.grF ξ.F (k+2)).d ((k+2)+t) (((k+2)+t)-1)).hom
      (Work.SSS.projQ ξ (k+2) ((k+2)+t) x) = 0 := by
    rw [Work.SSS.FirstPageCF.projQ_d_comm ξ (k+1) ((k+2)+t) x, hx, map_zero]
  let cz : (Work.SSS.grF ξ.F (k+2)).cycles ((k+2)+t) :=
    (Work.SSS.grF ξ.F (k+2)).cyclesMk (z : (Work.SSS.grF ξ.F (k+2)).X ((k+2)+t))
      (((k+2)+t)-1) hj hzcyc
  let cx : (Work.SSS.grF ξ.F (k+2)).cycles ((k+2)+t) :=
    (Work.SSS.grF ξ.F (k+2)).cyclesMk (Work.SSS.projQ ξ (k+2) ((k+2)+t) x)
      (((k+2)+t)-1) hj hpxcyc
  have hpsi := Work.SSS.FirstPageCF.psi_apply_cyclesMk ξ k t z hj hzcyc
  have hpsi' : Work.SSS.FirstPageCF.psi ξ (k+2) t hs z =
      (Work.SSS.grF ξ.F (k+2)).homologyπ ((k+2)+t) cz := by
    rw [show Work.SSS.FirstPageCF.psi ξ (k+2) t hs z = Work.SSS.FirstPageCF.psi ξ (k+2) t (by omega) z from by congr 1]
    exact hpsi
  have hjf := Work.SSS.FirstPageCF.jF_apply_cyclesMk ξ (k+1) t x (Work.SSS.projQ ξ (k+2) ((k+2)+t) x)
    rfl hj hx hj hpxcyc
  have hjf' : (Work.SSS.jF ξ (k+2) t).hom
        ((HomologicalComplex.homologyπ (ξ.F.obj (k+2)) ((k+2)+t))
          ((ξ.F.obj (k+2)).cyclesMk x (((k+2)+t)-1) hj hx)) =
      (Work.SSS.grF ξ.F (k+2)).homologyπ ((k+2)+t) cx := hjf
  have heq : (Work.SSS.grF ξ.F (k+2)).homologyπ ((k+2)+t) cz =
      (Work.SSS.grF ξ.F (k+2)).homologyπ ((k+2)+t) cx :=
    hpsi'.symm.trans (h.symm.trans hjf')
  have hmem := (Work.SSS.homologypi_eq_iff_sub_mem_range (Work.SSS.grF ξ.F (k+2)) ((k+2)+t)
    cz cx).mp heq
  simp only [cz, cx, Work.SSS.iCycles_cyclesMk_C] at hmem
  exact hmem

end Work.SSS.FirstPageCF
