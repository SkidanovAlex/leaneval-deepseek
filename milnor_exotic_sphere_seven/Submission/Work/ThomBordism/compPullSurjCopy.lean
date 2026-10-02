import Mathlib
import Submission.Work.ThomBordism.collapseM4Defs
import Submission.Work.ThomBordism.somePullbackCompPullV2
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Thom.bijective_relCohMap_of_homotopyEquiv
import Submission.Work.Tubular.ThomComparison

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Surjectivity of `Work.Tubular.compPull` (local copy)

A copy of the three lemmas `excision_pullback_bijective`, `homeo_pullback_bijective` and
`compPull_surjective` of `Submission/Work/ThomBordism/cla_localisation.lean`, under fresh names.
The original module `Submission.Work.ThomBordism.cla_localisation` cannot be imported from the
target file: it declares `Work.ThomBordism.some_pullback_eq_compPull`, which
`Submission.Work.ThomBordism.somePullbackCompPullV2` (imported below, for the import cycle)
declares as well, so the module no longer builds.
-/

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

open Work.Tubular

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The excision factor of `compPull` is bijective (cohomological excision). -/
theorem excision_pullback_bijective_v2 (E : PontryaginThom.EmbeddingData V (8 + k)) (n : ℕ) :
    Function.Bijective ((Work.Thom.relCohMap (infComplIncl E) (excSub E) (onePointNonzero E)
        (fun y hy => hy) ℤ n).hom) := by
  have h2 : IsIso (Work.Thom.relCohMap (infComplIncl E) (excSub E) (onePointNonzero E)
      (fun y hy => hy) ℤ n) :=
    Work.Cohomology.capRel_excision_isIso (TopCat.of (OnePoint (NormalTotal E))) (infCompl E)
      (onePointNonzero E) (OnePoint.isClosed_infty.isOpen_compl) (isOpen_onePointNonzero E)
      (infCompl_union_onePointNonzero E) n (fun y hy => hy)
  exact CategoryTheory.ConcreteCategory.bijective_of_isIso _

/-- The homeomorphism factor of `compPull` is bijective. -/
theorem homeo_pullback_bijective_v2 (E : PontryaginThom.EmbeddingData V (8 + k)) (n : ℕ) :
    Function.Bijective ((Work.Thom.relCohMap
        (⟨fun x => homeoV E x, (homeoV E).continuous_toFun⟩)
        (normalNonzero E) (excSub E) (fun x hx => (homeoV_mem E x).mp hx) ℤ n).hom) :=
  Work.Thom.bijective_relCohMap_of_homotopyEquiv (A := normalNonzero E) (B := excSub E)
    (f := ⟨fun x => homeoV E x, (homeoV E).continuous_toFun⟩)
    (hf := fun x hx => (homeoV_mem E x).mp hx) (homeoV E).toHomotopyEquiv rfl
    ((homeoV E).subtype (homeoV_mem E)).toHomotopyEquiv (fun q => rfl) n

/-- **`compPull` is surjective** (it is the pullback along `some`, an excision isomorphism). -/
theorem compPull_surjective_v2 (E : PontryaginThom.EmbeddingData V (8 + k)) (n : ℕ) :
    Function.Surjective (compPull E n) := by
  intro y
  obtain ⟨v, hv⟩ := (homeo_pullback_bijective_v2 (k := k) E n).2 y
  obtain ⟨w, hw⟩ := (excision_pullback_bijective_v2 (k := k) E n).2 v
  exact ⟨w, by rw [show (compPull E n) w = ((Work.Thom.relCohMap
      (⟨fun x => homeoV E x, (homeoV E).continuous_toFun⟩)
      (normalNonzero E) (excSub E) (fun x hx => (homeoV_mem E x).mp hx) ℤ n).hom)
      (((Work.Thom.relCohMap (infComplIncl E) (excSub E) (onePointNonzero E)
        (fun y hy => hy) ℤ n).hom) w) from rfl, hw, hv]⟩

end

end Work.ThomBordism
