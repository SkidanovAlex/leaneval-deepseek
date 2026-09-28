import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Thom.LineSection
import Submission.Work.Thom.LineComponent
import Submission.Work.Thom.Indicator

set_option synthInstance.maxHeartbeats 400000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The "difference of the two ends" class of the trivial line bundle

For the trivial real line bundle `E = B × ℝ → B` with total space `X` and zero complement
`A = E∖0`, this module constructs the class `Work.Thom.lineDiffClass ∈ H⁰(E∖0;ℤ)` that is `1` on
the negative half `A₋` and `0` on the positive half `A₊` — the *difference of the two ends* of the
line bundle — together with the two properties that the construction of the Thom class uses:

* `Work.Thom.sigmaPlus_lineDiffClass` : **`σ₊^* u = 0`**,
* `Work.Thom.sigmaMinus_lineDiffClass` : **`σ₋^* u = 1`**,

where `σ₊, σ₋ : X → A` are the constant sections `x ↦ ⟨x,1⟩`, `x ↦ ⟨x,-1⟩`.

The class is the indicator class (`Work.Thom.indicatorClass`) of the connected components of `A`
that meet `A₋`; the two properties follow from the naturality of the indicator class
(`Work.Thom.indicatorClass_pullback`) and from the fact that the connected components of `A` are
contained in `A₊` or in `A₋` (`Submission/Work/Thom/LineComponent.lean`).
-/

open CategoryTheory AlgebraicTopology Limits Simplicial

open scoped Topology Simplicial

open Classical

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι₀ : Type} [Inhabited ι₀]

/-! ## Naturality of the identification of `0`-simplices with points -/

/-- **Naturality of `TopCat.toSSetObj₀Equiv`**: the point of the image `0`-simplex is the image of
the point. -/
theorem toSSetObj₀Equiv_naturality {X Y : TopCat} (f : X ⟶ Y)
    (s : (TopCat.toSSet.obj X) _⦋0⦌) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map f).app _ s) = f (TopCat.toSSetObj₀Equiv s) := by
  rw [TopCat.toSSetObj₀Equiv_eq_T _ (⟨Pi.single (0 : Fin (0 + 1)) 1, single_mem_stdSimplex ℝ (0 : Fin (0 + 1))⟩ : stdSimplex ℝ (Fin (0 + 1))), TopCat.toSSetObj₀Equiv_eq_T _ (⟨Pi.single (0 : Fin (0 + 1)) 1, single_mem_stdSimplex ℝ (0 : Fin (0 + 1))⟩ : stdSimplex ℝ (Fin (0 + 1)))]
  rw [Work.Cohomology.toSSetObjEquiv_map_apply]

/-! ## The two constant sections land in the two halves -/

theorem sigmaPlus_mem_linePos (p : (RealBundle.trivial B ℝ ι₀).TotalSpace) :
    (((sigmaPlus (B := B) (ι₀ := ι₀) p :
      ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ linePos := by
  change (0:ℝ) < (show ℝ from ((sigmaPlus (B := B) (ι₀ := ι₀) p :
    ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
      (RealBundle.trivial B ℝ ι₀).TotalSpace).2)
  rw [sigmaPlus_apply]
  norm_num

theorem sigmaMinus_mem_lineNeg (p : (RealBundle.trivial B ℝ ι₀).TotalSpace) :
    (((sigmaMinus (B := B) (ι₀ := ι₀) p :
      ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg := by
  change (show ℝ from ((sigmaMinus (B := B) (ι₀ := ι₀) p :
    ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
      (RealBundle.trivial B ℝ ι₀).TotalSpace).2) < 0
  rw [sigmaMinus_apply]
  norm_num

/-! ## Equality of `0`-cochains from their values on generators -/

/-- **Two `0`-cochains with the same values on the generators are equal.** -/
theorem cochain_zero_ext (X : SSet) {α β : Work.Cohomology.Cochain ℤ X 0}
    (h : ∀ s : X _⦋0⦌, Work.Cohomology.genEval ℤ X α s = Work.Cohomology.genEval ℤ X β s) :
    α = β := by
  have hm : ModuleCat.ofHom α = ModuleCat.ofHom β := by
    apply Cofan.IsColimit.hom_ext (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) 0)
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    have hr : r = r • (1 : ℤ) := by simp
    rw [hr, map_smul, map_smul]
    congr 1
    exact h s
  have := congrArg ModuleCat.Hom.hom hm
  simpa using this

/-! ## The difference of the two ends -/

/-- The connected components of `E∖0` that meet the negative half. -/
def lineNegComponents : Set (SSet.π₀ (TopCat.toSSet.obj
    (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))))) :=
  {c | ∃ τ : (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))) _⦋0⦌,
    SSet.π₀.mk τ = c ∧ ((TopCat.toSSetObj₀Equiv τ :
      ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ lineNeg}

/-- **The "difference of the two ends" class** of the trivial line bundle: the class in `H⁰(E∖0;ℤ)`
that is `1` on the negative half of the fibre and `0` on the positive one. -/
noncomputable def lineDiffClass :
    Coh ℤ 0 ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)) :=
  indicatorClass (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))))
    (lineNegComponents (B := B) (ι₀ := ι₀))

/-- The values of the pullback of the indicator cochain along `σ₊` are all zero. -/
theorem genEval_pullback_sigmaPlus
    (s : (TopCat.toSSet.obj (TopCat.of (RealBundle.trivial B ℝ ι₀).TotalSpace)) _⦋0⦌) :
    Work.Cohomology.genEval ℤ
      (TopCat.toSSet.obj (TopCat.of (RealBundle.trivial B ℝ ι₀).TotalSpace))
      (((Work.Cohomology.dualChainMap ℤ (TopCat.of (RealBundle.trivial B ℝ ι₀).TotalSpace)
        (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))
        (TopCat.ofHom (sigmaPlus (B := B) (ι₀ := ι₀)))).f 0).hom
        (indicatorCochain (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))))
          (lineNegComponents (B := B) (ι₀ := ι₀)))) s = 0 := by
  rw [genEval_dualChainMap]
  refine genEval_indicatorCochain_of_not_mem _ _ _ ?_
  rintro ⟨τ, hτ, hmem⟩
  have hpt : ((TopCat.toSSetObj₀Equiv
      ((TopCat.toSSet.map (TopCat.ofHom (sigmaPlus (B := B) (ι₀ := ι₀)))).app _ s) :
        ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))) :
          (RealBundle.trivial B ℝ ι₀).TotalSpace) ∈ linePos := by
    rw [toSSetObj₀Equiv_naturality]
    exact sigmaPlus_mem_linePos _
  exact (not_mem_lineNeg_of_pi0_mk_eq_of_mem_linePos (B := B) (ι₀ := ι₀) hτ hpt) hmem

/-- **The pullback of the indicator cochain along `σ₊` is zero.** -/
theorem sigmaPlus_indicatorCochain_eq_zero :
    ((Work.Cohomology.dualChainMap ℤ (TopCat.of (RealBundle.trivial B ℝ ι₀).TotalSpace)
        (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))
        (TopCat.ofHom (sigmaPlus (B := B) (ι₀ := ι₀)))).f 0).hom
      (indicatorCochain (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))))
        (lineNegComponents (B := B) (ι₀ := ι₀))) = 0 :=
  cochain_zero_ext _ (fun s => genEval_pullback_sigmaPlus s)

/-! ## The class of the zero cochain, and the two properties of `lineDiffClass` -/

/-- The cycle of the zero cochain is zero (`iCycles` is injective and kills `0`). -/
theorem cocycleOf_zero (X : SSet)
    (h : Work.Cohomology.cochainDiff ℤ X (0 : Work.Cohomology.Cochain ℤ X 0) = 0) :
    Work.Cohomology.cocycleOf ℤ X (0 : Work.Cohomology.Cochain ℤ X 0) h = 0 := by
  have hK : Work.Cohomology.cocycleOf ℤ X (0 : Work.Cohomology.Cochain ℤ X 0) h =
      Work.Cohomology.cocycleOfK (Work.Cohomology.SSetCochainComplex ℤ X) 0 h := rfl
  rw [hK]
  refine Work.Cohomology.iCycles_injective_K _ 0 ?_
  rw [Work.Cohomology.iCycles_cocycleOfK, map_zero]

/-- **The class of the zero `0`-cocycle is zero.** -/
theorem cohomologyClassOf_zero (X : SSet)
    (h : Work.Cohomology.cochainDiff ℤ X (0 : Work.Cohomology.Cochain ℤ X 0) = 0) :
    Work.Cohomology.cohomologyClassOf ℤ X (0 : Work.Cohomology.Cochain ℤ X 0) h = 0 := by
  rw [Work.Cohomology.cohomologyClassOf, cocycleOf_zero X h, map_zero]

/-- **`σ₊^* u = 0`** for the difference-of-the-ends class. -/
theorem sigmaPlus_lineDiffClass :
    (CohMap (sigmaPlus (B := B) (ι₀ := ι₀)) ℤ 0).hom (lineDiffClass (B := B) (ι₀ := ι₀)) = 0 := by
  rw [lineDiffClass, indicatorClass_pullback (sigmaPlus (B := B) (ι₀ := ι₀))
    (lineNegComponents (B := B) (ι₀ := ι₀)), indicatorClass]
  have hcoe : indicatorCochain (TopCat.toSSet.obj (TopCat.of (RealBundle.trivial B ℝ ι₀).TotalSpace))
        {c | SSet.mapπ₀ (TopCat.toSSet.map (TopCat.ofHom (sigmaPlus (B := B) (ι₀ := ι₀)))) c
          ∈ lineNegComponents (B := B) (ι₀ := ι₀)} = 0 := by
    rw [← dualChainMap_indicatorCochain (TopCat.ofHom (sigmaPlus (B := B) (ι₀ := ι₀)))
      (lineNegComponents (B := B) (ι₀ := ι₀))]
    exact sigmaPlus_indicatorCochain_eq_zero (B := B) (ι₀ := ι₀)
  simp only [hcoe]
  exact cohomologyClassOf_zero _ _

/-- The preimage of `lineNegComponents` under `σ₋` is everything: every component of `E∖0`
contains a point of the negative half, namely one in the image of `σ₋`. -/
theorem sigmaMinus_preimage_eq_univ :
    {c | SSet.mapπ₀ (TopCat.toSSet.map (TopCat.ofHom (sigmaMinus (B := B) (ι₀ := ι₀)))) c
        ∈ lineNegComponents (B := B) (ι₀ := ι₀)} = Set.univ := by
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective c
  refine ⟨(TopCat.toSSet.map (TopCat.ofHom (sigmaMinus (B := B) (ι₀ := ι₀)))).app _ s, ?_, ?_⟩
  · rw [SSet.mapπ₀_mk]
  · rw [toSSetObj₀Equiv_naturality]
    exact sigmaMinus_mem_lineNeg _

/-- The pullback of the indicator cochain along `σ₋` is the unit cochain. -/
theorem sigmaMinus_indicatorCochain_eq_unit :
    ((Work.Cohomology.dualChainMap ℤ (TopCat.of (RealBundle.trivial B ℝ ι₀).TotalSpace)
        (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀)))
        (TopCat.ofHom (sigmaMinus (B := B) (ι₀ := ι₀)))).f 0).hom
      (indicatorCochain (TopCat.toSSet.obj (TopCat.of ↥(zeroComplement (RealBundle.trivial B ℝ ι₀))))
        (lineNegComponents (B := B) (ι₀ := ι₀)))
      = Work.Cohomology.unitCochain ℤ
          (TopCat.toSSet.obj (TopCat.of (RealBundle.trivial B ℝ ι₀).TotalSpace)) := by
  rw [dualChainMap_indicatorCochain, sigmaMinus_preimage_eq_univ]
  refine cochain_zero_ext _ (fun s => ?_)
  rw [genEval_indicatorCochain_of_mem _ _ _ (Set.mem_univ s), Work.Cohomology.genEval_unitCochain]

/-- **`σ₋^* u = 1`** for the difference-of-the-ends class. -/
theorem sigmaMinus_lineDiffClass :
    (CohMap (sigmaMinus (B := B) (ι₀ := ι₀)) ℤ 0).hom (lineDiffClass (B := B) (ι₀ := ι₀))
      = Work.Cohomology.oneH ℤ
          (TopCat.toSSet.obj (TopCat.of (RealBundle.trivial B ℝ ι₀).TotalSpace)) := by
  rw [lineDiffClass, indicatorClass_pullback (sigmaMinus (B := B) (ι₀ := ι₀))
    (lineNegComponents (B := B) (ι₀ := ι₀)), indicatorClass]
  have hcoe : indicatorCochain (TopCat.toSSet.obj (TopCat.of (RealBundle.trivial B ℝ ι₀).TotalSpace))
        {c | SSet.mapπ₀ (TopCat.toSSet.map (TopCat.ofHom (sigmaMinus (B := B) (ι₀ := ι₀)))) c
          ∈ lineNegComponents (B := B) (ι₀ := ι₀)}
      = Work.Cohomology.unitCochain ℤ
          (TopCat.toSSet.obj (TopCat.of (RealBundle.trivial B ℝ ι₀).TotalSpace)) := by
    rw [← dualChainMap_indicatorCochain (TopCat.ofHom (sigmaMinus (B := B) (ι₀ := ι₀)))
      (lineNegComponents (B := B) (ι₀ := ι₀))]
    exact sigmaMinus_indicatorCochain_eq_unit (B := B) (ι₀ := ι₀)
  simp only [hcoe]
  rw [Work.Cohomology.oneH]

end

end Work.Thom
