import Mathlib
import Submission.Work.CrauderKatz.BlowUp.exists_birationalMap_exDiv_singleton_of_openImmersion
import Submission.Work.Motivic.cInv_eq_zero_of_pseudoReg

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CrauderKatz.BlowUp

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- **The `IsOver` refinement of `exists_birationalMap_exDiv_singleton_of_openImmersion`.**  If the
dominant open immersion `ι : X ⟶ Y` is a morphism over `Spec 𝕜` (i.e.
`ι ≫ (Y ↘ Spec 𝕜) = (X ↘ Spec 𝕜)`), then the birational map `φ : Y ⤏ X` produced by
`Work.CrauderKatz.BlowUp.exists_birationalMap_exDiv_singleton_of_openImmersion` (whose hypotheses
are repeated verbatim) is a morphism over `Spec 𝕜`.

Note that the base scheme is `Spec 𝕜`, as in the original lemma, and not an arbitrary `S`: the
`exDiv` argument needs `Y.IsSeparated`, which the original derives from
`IsSeparated (Y ↘ Spec 𝕜)` because `Spec 𝕜` is separated over the terminal.

Proof route: copy the proof of `exists_birationalMap_exDiv_singleton_of_openImmersion`, which builds
`A := opensRangePartialIso ι : X.PartialIso Y` (source `⊤`, target `ι.opensRange`, iso
`X.topIso ≪≫ ι.isoOpensRange`) and `φ := A.symm.toBirationalMap`, and add the `IsOver` conjunct:
`A.IsOver (X ↘ Spec 𝕜) (Y ↘ Spec 𝕜)` holds by `PartialIso.IsOver` since
`A.iso.hom = X.topIso.hom ≫ ι.isoOpensRange.hom` and `Scheme.Hom.isoOpensRange_hom_ι` gives
`ι.isoOpensRange.hom ≫ ι.opensRange.ι = ι`, so `hι` closes it; then `PartialIso.IsOver.symm` gives
`A.symm.IsOver (Y ↘ Spec 𝕜) (X ↘ Spec 𝕜)`, hence `A.symm.toPartialMap.IsOver (Spec 𝕜)` (the two
unfoldings differ only by `Category.assoc`), hence `RationalMap.IsOver` and finally
`BirationalMap.IsOver` for `φ`. -/
theorem exists_birationalMap_exDiv_singleton_of_openImmersion_over (𝕜 : Type) [Field 𝕜]
    {X Y : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [AlgebraicGeometry.IsReduced Y]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [AlgebraicGeometry.IsSeparated (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (ι : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion ι] (hdense : DenseRange ι)
    (hι : ι ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
      = (X ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
    (y : Y) (hy : Order.coheight y = 1) (hyr : y ∉ Set.range ι)
    (huniq : ∀ y' : Y, Order.coheight y' = 1 → y' ∉ Set.range ι → y' = y) :
    ∃ φ : Y.BirationalMap X,
      φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) ∧ exDiv φ = {y} ∧
        exDiv φ.symm = ∅ := by
  haveI hdom : IsDominant ι := ⟨hdense⟩
  -- `Y` is separated as a scheme, since it is separated over `Spec 𝕜`
  haveI hYsep : Y.IsSeparated := by
    refine ⟨?_⟩
    rw [← Limits.terminal.comp_from (Y ↘ Spec (CommRingCat.of 𝕜))]
    infer_instance
  let A : X.PartialIso Y := opensRangePartialIso ι
  have hAsrc : A.source = ⊤ := rfl
  have hAtgt : A.target = ι.opensRange := rfl
  -- the partial isomorphism `A` is a morphism over `Spec 𝕜`
  have hAover : A.IsOver (X ↘ Spec (CommRingCat.of 𝕜)) (Y ↘ Spec (CommRingCat.of 𝕜)) := by
    rw [PartialIso.IsOver]
    simp only [A, opensRangePartialIso, Iso.trans_hom, Category.assoc]
    rw [Scheme.Hom.isoOpensRange_hom_ι_assoc, hι]
    rfl
  -- hence so is the resulting birational map `A.symm.toBirationalMap`
  have hφover : A.symm.toBirationalMap.IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_toBirationalMap A.symm (PartialIso.IsOver.symm hAover)
  -- every point in the image is an isomorphism point of the inverse
  have hisoAt_of_mem : ∀ z ∈ Set.range ι, IsIsoAt A.symm.toBirationalMap z := by
    rintro z ⟨x, rfl⟩
    refine ⟨A.symm, ?_, rfl⟩
    rw [PartialIso.symm_source, hAtgt]
    exact (Hom.mem_opensRange).mpr ⟨x, rfl⟩
  -- and the missing point is not
  have hnotIsoAt : ¬ IsIsoAt A.symm.toBirationalMap y := by
    rintro ⟨i, hyi, hr⟩
    have hmem : y ∈ A.target :=
      mem_target_of_toRationalMap_eq_symm i A hAsrc (by rw [hr, PartialIso.toBirationalMap_hom]) hyi
    exact hyr ((Hom.mem_opensRange).mp (by rw [← hAtgt]; exact hmem))
  refine ⟨A.symm.toBirationalMap, hφover, ?_, ?_⟩
  · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hy, hnotIsoAt⟩, ?_⟩
    rintro z ⟨hz1, hz2⟩
    by_contra hzy
    refine hz2 (hisoAt_of_mem z ?_)
    by_contra hzr
    exact hzy (huniq z hz1 hzr)
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hz⟩
    -- the inverse of the inverse is the original partial isomorphism
    have hsymm : (A.symm.toBirationalMap).symm = A.toBirationalMap := by
      apply BirationalMap.ext
      rw [BirationalMap.symm_hom, PartialIso.toBirationalMap_inv,
        show A.symm.symm = A from rfl, PartialIso.toBirationalMap_hom]
    rw [hsymm] at hz
    exact hz (isIsoAt_of_mem_source A (by rw [hAsrc]; trivial))

end Work.CrauderKatz.BlowUp
