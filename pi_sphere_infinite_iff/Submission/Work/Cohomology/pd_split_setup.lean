import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_hatcher_data
import Submission.Work.Cohomology.cap_mem_range_inclChains
import Submission.Work.Cohomology.pd_ab_clean
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Cohomology.pd_glue2
import Submission.Work.Cohomology.mem_range_inclChains_of_image
import Submission.Work.Cohomology.chainRetract_mem_range_inclChains
import Submission.Work.Cohomology.pd_relsub_aux
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.pd_hatcher_cycles_inter
import Submission.Work.Cohomology.pd_localFundClass_of_cycle
import Submission.Work.Cohomology.pd_union_crux_zero_wk
import Submission.Work.Cohomology.cap_cochainDiff_mem_range
import Submission.Work.Cohomology.pdABInclRel_comp_pdABEnlarge
import Submission.Work.Cohomology.pdABdelta_natural
import Submission.Work.Cohomology.pdABCoh_quasiIso
import Submission.Work.Cohomology.pd_boundary_of_zero_class
import Submission.Work.Cohomology.pd_split_aux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Simplicial
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **Setup**: from a relative cohomology class of the pair `(U∪V, (U∪V)∖(K₁∪K₂))` produce a
representing cocycle, and a lift of it along the `A+B` difference map. -/
theorem pd_split_setup {M : TopCat} [T2Space M] {k : ℕ}
    {U V : Set M} {K₁ K₂ : Set M}
    (x : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k) :
    ∃ (φ φA φB : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k),
      φ ∈ Work.Cohomology.relKern ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) k ∧
      Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φ = 0 ∧
      φA ∈ Work.Cohomology.relKern ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁) k ∧
      φB ∈ Work.Cohomology.relKern ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) k ∧
      φ = φA - φB := by
  classical
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyπ (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k)).mp inferInstance x
  set φ : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k :=
    ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z).1 with hφdef
  have hφmem : φ ∈ Work.Cohomology.relKern ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) k :=
    ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z).2
  have hφd : Work.Cohomology.cochainDiff ℤ
      (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φ = 0 := by
    have h0 : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d k (k+1)
        ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z) = 0 := by
      have hcomp : (ConcreteCategory.hom ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k ≫
            (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d k (k+1))) z
          = (ConcreteCategory.hom ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d k (k+1)))
            ((ConcreteCategory.hom ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k)) z) :=
        CategoryTheory.ConcreteCategory.comp_apply
          ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k)
          ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d k (k+1)) z
      rw [← hcomp]
      exact congrArg (fun (g : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).cycles k ⟶
          (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).X (k+1)) =>
          (ConcreteCategory.hom g) z)
        (HomologicalComplex.iCycles_d (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k (k+1))
    have hcomm := congrArg
      (fun (g : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).X k ⟶
          (Work.Cohomology.singularCochainComplex ℤ (TopCat.of (U ∪ V : Set M))).X (k+1)) =>
        (ConcreteCategory.hom g)
          ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z))
      ((Work.Cohomology.relIncl ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).comm k (k+1))
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at hcomm
    rw [h0, map_zero] at hcomm
    have hrel : (ConcreteCategory.hom ((Work.Cohomology.relIncl ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).f k))
          ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z) = φ := rfl
    rw [hrel] at hcomm
    have hx : (ConcreteCategory.hom ((Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of (U ∪ V : Set M))).d k (k+1))) φ
        = Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) φ := by
      simp only [Work.Cohomology.singularCochainComplex_eq, Work.Cohomology.SSetCochainComplex_d]
      exact Work.Cohomology.cochainDiffLM_apply ℤ
        (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k φ
    rw [hx] at hcomm
    exact hcomm

  -- the lift
  have hsplit : Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)
      = Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁
        ∩ Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂ :=
    Work.Cohomology.pdRelSub_union (U ∪ V : Set M) K₁ K₂
  have hφmem' : φ ∈ Work.Cohomology.relKern ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁
        ∩ Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) k := hsplit ▸ hφmem
  obtain ⟨φt, hφt⟩ := PDABClean.pdBiprodToInter_surj (TopCat.of (U ∪ V : Set M))
    (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)
    (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) k ⟨φ, hφmem'⟩
  set y₁ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)).X k :=
    (ModuleCat.Hom.hom ((biprod.fst : Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁) ⊞
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) ⟶
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)).f k)) φt with hy₁
  set y₂ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).X k :=
    (ModuleCat.Hom.hom ((biprod.snd : Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁) ⊞
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) ⟶
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).f k)) φt with hy₂
  refine ⟨φ, y₁.1, y₂.1, hφmem, hφd, y₁.2, y₂.2, ?_⟩
  have htotal : (ModuleCat.Hom.hom ((biprod.inl : Work.Cohomology.relComplex ℤ
        (TopCat.of (U ∪ V : Set M)) (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁) ⟶
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁) ⊞
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).f k)) y₁
      + (ModuleCat.Hom.hom ((biprod.inr : Work.Cohomology.relComplex ℤ
        (TopCat.of (U ∪ V : Set M)) (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) ⟶
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁) ⊞
        Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).f k)) y₂ = φt :=
    PDABClean.pdBiprod_total (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) k φt
  have hcoe := PDABClean.pdBiprodToInter_coe (TopCat.of (U ∪ V : Set M))
    (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)
    (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) k y₁ y₂
  rw [htotal] at hcoe
  have h3 : ((show Work.Cohomology.relKern ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁
        ∩ Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂) k from
      (ModuleCat.Hom.hom ((pdBiprodToInter (TopCat.of (U ∪ V : Set M))
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)
        (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).f k)) φt)).1 = φ := by
    rw [hφt]
  exact h3.symm.trans hcoe

end

end Work.Cohomology
