import Mathlib
import Submission.Work.Whitney.GaugePDefs
import Submission.Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_indexAt
import Submission.Work.Thom.complexification
import Submission.Work.Thom.Iso
import Submission.Work.Thom.coreMorphism

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **The transition function of the underlying real bundle** `E_ℝ` of `E`, in the `ℝ^{2m}`
presentation, is the realification `Work.Whitney.reImify m` of the transition function of `E`. -/
theorem realifiedCore_coordChange_reImify
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i j : ι) (b : B) :
    (realifiedCore Z).coordChange i j b = reImify m (Z.coordChange i j b) := by
  have h : (realification Z).coordChange i j b = (Z.coordChange i j b).restrictScalars ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    rw [realification_coordChange]
    rfl
  rw [realifiedCore, Work.TangentClasses.RealBundle.mapFibre_coordChange, h]
  rfl

/-- The transition function of `E_ℝ ⊗_ℝ ℂ` is the complexification of that of `E_ℝ`. -/
theorem complexificationCore_realifiedCore_coordChange
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i j : ι) (b : B) :
    (complexificationCore (realifiedCore Z)).coordChange i j b
      = cxTrans (reImify m (Z.coordChange i j b)) := by
  rw [complexificationCore_coordChange_clm, realifiedCore_coordChange_reImify]

/-- The transition function of `E ⊕ Ē` is the block-diagonal `g ⊕ ḡ` transported along the
splitting `Work.Whitney.sumFibreC`. -/
theorem whitneySum_conjCore_coordChange
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (p q : ι × ι) (b : B) :
    (whitneySum Z (conjCore Z)).coordChange p q b
      = transportEnd (sumFibreC m m) (Z.coordChange p.1 q.1 b)
          (conjCLM m (Z.coordChange p.2 q.2 b)) := by
  rw [whitneySum_coordChange]
  simp only [conjCore_coordChange]
  rfl

/-- The base sets of the two bundles agree along the diagonal cover. -/
theorem whitneySum_conjCore_baseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i : ι) :
    (whitneySum Z (conjCore Z)).baseSet (i, i)
      = (complexificationCore (realifiedCore Z)).baseSet i := by
  simp only [whitneySum_baseSet, conjCore_baseSet, complexificationCore_baseSet,
    realifiedCore_baseSet, Set.inter_self]

/-- The index maps of the two bundles agree along the diagonal cover. -/
theorem whitneySum_conjCore_indexAt (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (b : B) :
    (whitneySum Z (conjCore Z)).indexAt b
      = ((complexificationCore (realifiedCore Z)).indexAt b,
         (complexificationCore (realifiedCore Z)).indexAt b) := by
  simp only [whitneySum_indexAt, conjCore_indexAt, complexificationCore_indexAt,
    realifiedCore_indexAt]

/-
**DELIVERABLE ITEM 4 (first half): `E_ℝ ⊗_ℝ ℂ ≅ E ⊕ Ē`.**

`Work.Whitney.realifiedCore Z` (`Submission/Work/Whitney/Realified.lean`) is the underlying real
bundle of `Z` in the `ℝ^{2m}` presentation (transitions `reImCore ∘ g ∘ pairCxCore`, the real block
matrix `[[A, -B], [B, A]]` of `g = A + iB`), so the left side is `E_ℝ ⊗_ℝ ℂ` and the right side is
`E ⊕ Ē` (`Work.Whitney.whitneySum`, `Work.Whitney.conjCore`).  The gauge is CONSTANT:

  `P : ℂ^m ⊕ ℂ^m → ℂ^m ⊕ ℂ^m`,   `P (a, b) = (a + i b, a - i b)`,

in the `Work.Whitney.sumFibreC m m` coordinates, i.e. as an endomorphism of
`EuclideanSpace ℂ (Fin (m + m))` it is `sumFibreC m m ∘ P₀ ∘ (sumFibreC m m).symm` where
`P₀ (a, b) = (a + cxMulI b, a - cxMulI b)`.

The gauge is `Work.Whitney.gaugePC m` (`Submission/Work/Whitney/GaugePDefs.lean`), and the
compatibility with the transition functions is `Work.Whitney.gaugePC_cxTrans`: for every
complex-linear `g` on `ℂ^m`,

  `gaugePC m ∘ cxTrans (reImify m g) = transportEnd (sumFibreC m m) g (conjCLM m g) ∘ gaugePC m`,

i.e. the complexification of the realification of `g` is conjugate to `g ⊕ ḡ` through the gauge.
Since the transition functions of the two bundles are exactly these two maps (by
`Work.Whitney.complexificationCore_realifiedCore_coordChange` and
`Work.Whitney.whitneySum_conjCore_coordChange`), the constant gauge is a bundle isomorphism, by
`Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_indexAt` (the gauge is constant, so its
two-sided inverse is the inverse of the linear equivalence `Work.Whitney.gaugePE m`).
-/
theorem nonempty_bundleIso_complexificationCore_realifiedCore {m : ℕ} {B : Type}
    [TopologicalSpace B] {ι : Type} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.complexificationCore (realifiedCore Z))
      (Work.Whitney.whitneySum Z (conjCore Z))) := by
  refine Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_indexAt
    (Work.Thom.complexificationCore (realifiedCore Z))
    (Work.Whitney.whitneySum Z (conjCore Z)) (gaugePE m) (fun i => (i, i)) ?_ ?_
  · intro i
    exact whitneySum_conjCore_baseSet Z i
  · intro i b
    show ((whitneySum Z (conjCore Z)).coordChange ((whitneySum Z (conjCore Z)).indexAt b)
        (i, i) b).comp (gaugePC m)
      = (gaugePC m).comp ((complexificationCore (realifiedCore Z)).coordChange
          ((complexificationCore (realifiedCore Z)).indexAt b) i b)
    rw [complexificationCore_realifiedCore_coordChange, whitneySum_conjCore_coordChange]
    simp only [complexificationCore_indexAt, realifiedCore_indexAt, whitneySum_indexAt,
      conjCore_indexAt]
    rw [← gaugePC_cxTrans m (Z.coordChange (Z.indexAt b) i b)]

end

end Work.Whitney
