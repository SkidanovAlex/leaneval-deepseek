import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.FirstPage.HomElts

namespace Work.SSS.FirstPageCF

noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- **A homology class of `F_s` killed in `F_{s+1}` is carried by a cycle which is a boundary in
`F_{s+1}`.**  If `v ∈ H_{s+t}(F_s)` maps to `0` under `H_{s+t}(F_s) → H_{s+t}(F_{s+1})`, then `v`
has a cycle representative `x` whose image in `F_{s+1}` is a boundary `∂e`. -/
lemma exists_cycle_lift {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C) (s t : ℕ)
    (v : (ξ.F.obj s).homology (s+t))
    (hv : (HomologicalComplex.homologyMap (Work.SSS.incF ξ.F s) (s+t)).hom v = 0) :
    ∃ (x : (ξ.F.obj s).X (s+t)) (hx : (Work.SSS.dFs ξ s (s+t) ((s+t)-1)) x = 0),
      (HomologicalComplex.homologyπ (ξ.F.obj s) (s+t))
          ((ξ.F.obj s).cyclesMk x ((s+t)-1) (Work.SSS.next_down_eq_pred (s+t)) hx) = v ∧
      ∃ (e : (ξ.F.obj (s+1)).X ((s+t)+1)),
        (Work.SSS.dFs ξ (s+1) ((s+t)+1) (s+t)) e
          = (Work.SSS.Finc ξ s (s+1) (Nat.le_succ s) (s+t)) x := by
  -- choose a cycle representative `c` of the class `v`
  obtain ⟨c, hc⟩ : ∃ c : (ξ.F.obj s).cycles (s+t),
      (HomologicalComplex.homologyπ (ξ.F.obj s) (s+t)) c = v :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance v
  refine ⟨(ξ.F.obj s).iCycles (s+t) c, ?_, ?_, ?_⟩
  · exact Work.SSS.iCycles_d_C (ξ.F.obj s) (s+t) ((s+t)-1) c
  · rw [Work.SSS.cyclesMk_iCycles_C, hc]
  · -- the image of `c` in `F_{s+1}` has vanishing homology class
    have hzero : (HomologicalComplex.homologyπ (ξ.F.obj (s+1)) (s+t))
        ((HomologicalComplex.cyclesMap (Work.SSS.incF ξ.F s) (s+t)) c) = 0 := by
      have h : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSS.incF ξ.F s) (s+t)))
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (ξ.F.obj s) (s+t))) c)
          = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (ξ.F.obj (s+1)) (s+t)))
            ((ModuleCat.Hom.hom
              (HomologicalComplex.cyclesMap (Work.SSS.incF ξ.F s) (s+t))) c) :=
        Work.SSS.homologyMap_homologypi_C (ξ.F.obj s) (ξ.F.obj (s+1))
          (Work.SSS.incF ξ.F s) (s+t) c
      rw [← h, hc, hv]
    -- hence it is a boundary in `F_{s+1}`
    obtain ⟨w, hw⟩ := Work.SSS.exists_d_eq_of_homologypi_eq_zero (ξ.F.obj (s+1)) (s+t)
      ((HomologicalComplex.cyclesMap (Work.SSS.incF ξ.F s) (s+t)) c) hzero
    refine ⟨w, ?_⟩
    -- `∂w` is the image of `x` under the inclusion `F_s → F_{s+1}`
    have h2 : (ModuleCat.Hom.hom (HomologicalComplex.iCycles (ξ.F.obj (s+1)) (s+t)))
        ((ConcreteCategory.hom (HomologicalComplex.cyclesMap (Work.SSS.incF ξ.F s) (s+t))) c)
        = (Work.SSS.Finc ξ s (s+1) (Nat.le_succ s) (s+t))
            ((ConcreteCategory.hom (HomologicalComplex.iCycles (ξ.F.obj s) (s+t))) c) :=
      Work.SSS.iCycles_cyclesMap_C (ξ.F.obj s) (ξ.F.obj (s+1))
        (Work.SSS.incF ξ.F s) (s+t) c
    exact hw.trans h2

end

end Work.SSS.FirstPageCF
