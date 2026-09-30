import Mathlib
import Submission.Work.Pi6.SQM.SIG.Basic
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open CategoryTheory

namespace Work.Pi6.SQM.SIG

/-- A cycle of a cochain complex of modules whose homology class vanishes is a boundary: the
elementwise form of the fact that `homologyπ` is the cokernel of `toCycles`. -/
lemma exists_toCycles_eq_of_homologyπ_eq_zero {R : Type} [CommRing R]
    (K : CochainComplex (ModuleCat R) ℕ) (n : ℕ) [K.HasHomology (n + 1)]
    (z : K.cycles (n + 1)) (h : ModuleCat.Hom.hom (K.homologyπ (n + 1)) z = 0) :
    ∃ y : K.X n, ModuleCat.Hom.hom (K.toCycles n (n + 1)) y = z := by
  let T := ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
    (K.toCycles_comp_homologyπ n (n + 1))
  have hprev : (ComplexShape.up ℕ).prev (n + 1) = n :=
    ComplexShape.prev_eq' (c := ComplexShape.up ℕ) (ComplexShape.up_mk n (n + 1) rfl)
  have hT : T.Exact :=
    ShortComplex.exact_of_g_is_cokernel T (K.homologyIsCokernel n (n + 1) hprev)
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff T).mp hT z h
  exact ⟨y, hy⟩

/-- A cocycle whose cohomology class vanishes is a coboundary.  This is the cokernel description
of `homology`: `ker (homologyπ) = range (toCycles)`.  Useful Mathlib API:
`HomologicalComplex.homologyπ`, `HomologicalComplex.toCycles`, `HomologicalComplex.sc`,
`ShortComplex.homologyπ`, `ShortComplex.toCycles_comp_homologyπ`,
`ShortComplex.isColimit_homologyπ` / `CokernelCofork` structure, and
`Work.Cohomology.cohomologyClassOf` (which is `homologyπ` applied to `cocycleOf`). -/
theorem classZeroCoboundary (X : SSet) (n : ℕ)
    (u : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X (n + 1))
    (hu : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X u = 0)
    (h : Work.Cohomology.cohomologyClassOf Work.Pi6.SQ.F2 X u hu = 0) :
    ∃ v : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X n,
      Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X v = u := by
  have hz : ModuleCat.Hom.hom
      ((Work.Cohomology.SSetCochainComplex Work.Pi6.SQ.F2 X).homologyπ (n + 1))
      (Work.Cohomology.cocycleOf Work.Pi6.SQ.F2 X u hu) = 0 := h
  obtain ⟨y, hy⟩ := exists_toCycles_eq_of_homologyπ_eq_zero
    (Work.Cohomology.SSetCochainComplex Work.Pi6.SQ.F2 X) n
    (Work.Cohomology.cocycleOf Work.Pi6.SQ.F2 X u hu) hz
  refine ⟨y, ?_⟩
  have hA : ModuleCat.Hom.hom
        ((Work.Cohomology.SSetCochainComplex Work.Pi6.SQ.F2 X).iCycles (n + 1))
        (ModuleCat.Hom.hom
          ((Work.Cohomology.SSetCochainComplex Work.Pi6.SQ.F2 X).toCycles n (n + 1)) y) = u := by
    rw [hy]
    exact Work.Cohomology.iCycles_cocycleOf Work.Pi6.SQ.F2 X u hu
  have hB : ModuleCat.Hom.hom
        ((Work.Cohomology.SSetCochainComplex Work.Pi6.SQ.F2 X).d n (n + 1)) y
      = ModuleCat.Hom.hom
        ((Work.Cohomology.SSetCochainComplex Work.Pi6.SQ.F2 X).iCycles (n + 1))
        (ModuleCat.Hom.hom
          ((Work.Cohomology.SSetCochainComplex Work.Pi6.SQ.F2 X).toCycles n (n + 1)) y) := by
    have hc := congrArg (fun f => ModuleCat.Hom.hom f y)
      (HomologicalComplex.toCycles_i (Work.Cohomology.SSetCochainComplex Work.Pi6.SQ.F2 X) n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    exact hc.symm
  have hC : ModuleCat.Hom.hom
      ((Work.Cohomology.SSetCochainComplex Work.Pi6.SQ.F2 X).d n (n + 1)) y = u :=
    hB.trans hA
  have hd : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X y
      = ModuleCat.Hom.hom
        ((Work.Cohomology.SSetCochainComplex Work.Pi6.SQ.F2 X).d n (n + 1)) y := by
    rw [Work.Cohomology.SSetCochainComplex_d]
    exact (Work.Cohomology.cochainDiffLM_apply Work.Pi6.SQ.F2 X n y).symm
  exact hd.trans hC

end Work.Pi6.SQM.SIG
