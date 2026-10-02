import Mathlib
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.lerayHirschGlue
import Submission.Work.LerayHirsch.CohMap_projMap_injective_of_LerayHirschFull
import Submission.Work.LerayHirsch.lerayHirschFull_of_bundleIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Leray–Hirsch for every complex gluing-data bundle

The Mayer–Vietoris rung `Work.LerayHirsch.lerayHirschGlue` is proved, so the assembly
`Work.LerayHirsch.lerayHirschTheorem_of` turns **`KunnethCP` into Leray–Hirsch for every complex
gluing-data bundle over every base**:

```lean
Work.LerayHirsch.lerayHirschFull_of_kunnethCP (hK : KunnethCP) : ∀ Z, LerayHirschFull Z
```

`KunnethCP` is Künneth for `B × ℂP^{m-1}` (`Submission/Work/Kunneth/`) and is therefore the *only*
remaining input of the Leray–Hirsch theorem of this chapter.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **Leray–Hirsch for every complex gluing-data bundle**, from Künneth (`KunnethCP`, subproject
KUNNETH) alone: the Mayer–Vietoris rung is proved (`Work.LerayHirsch.lerayHirschGlue`). -/
theorem lerayHirschFull_of_kunnethCP (hK : KunnethCP) :
    ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι), LerayHirschFull Z :=
  lerayHirschTheorem_of hK lerayHirschGlue

/-- The even-degree part: `H^{2k}(P(E)) ≅ ⊕_{i<m} H^{2(k-i)}(B)` for every bundle. -/
theorem lerayHirsch_of_kunnethCP (hK : KunnethCP) :
    ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι), LerayHirsch Z :=
  fun Z => (lerayHirschFull_of_kunnethCP hK Z).1

/-- The odd-degree part: `H^{2k+1}(P(E)) ≅ ⊕_{i<m} H^{2(k-i)+1}(B)` for every bundle. -/
theorem lerayHirschOdd_of_kunnethCP (hK : KunnethCP) :
    ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι), LerayHirschOdd Z :=
  fun Z => (lerayHirschFull_of_kunnethCP hK Z).2

/-- **The separation principle for every bundle**: `π^*` is injective on cohomology, from Künneth
alone (this is the tool WHITNEY §6(c) needs). -/
theorem CohMap_projMap_injective_of_kunnethCP (hK : KunnethCP) {m : ℕ} (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (n : ℕ) :
    Function.Injective (CohMap (projMap Z) ℤ n).hom :=
  CohMap_projMap_injective_of_LerayHirschFull hm Z (lerayHirschFull_of_kunnethCP hK Z) n

/-- **`KunnethCP` gives Leray–Hirsch for the trivial bundle** (the trivial bundle has a single chart
covering the base, so this is the instance of `KunnethCP` at `trivialVectorBundleCore`).  The
converse, that the trivial-bundle form of Künneth implies `KunnethCP`, is the target
`Work.LerayHirsch.kunnethCP_of_trivialBundles` (it needs the isomorphism between a single-chart
bundle and the trivial one, plus `lerayHirschFull_of_bundleIso`). -/
theorem lerayHirschFull_trivial_of_kunnethCP (hK : KunnethCP) (m : ℕ) (B : Type)
    [TopologicalSpace B] :
    LerayHirschFull (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) :=
  hK _ ⟨PUnit.unit, rfl⟩

end

end Work.LerayHirsch
