import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.affRing_eq_adjoin

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- Every element of the affine coordinate ring `L[X, Y]/(W_E)`, transported into the function
field `L(E)`, lies in `L[genX E, genY E]`. -/
private lemma algebraMap_coord_mem_adjoin (L : Type) [Field L] (E : WeierstrassCurve L)
    (a : Work.MotC2.Coord E) :
    algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) a ∈
      Algebra.adjoin L ({Work.MotC2.genX E, Work.MotC2.genY E} :
        Set (Work.MotC2.Func E)) := by
  have h1 : algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) a ∈ Work.MotC2.affRing E :=
    Algebra.subset_adjoin ⟨a, rfl⟩
  rwa [Work.MotC2.affRing_eq_adjoin L E] at h1

theorem adjoin_genX_genY (L : Type) [Field L] (E : WeierstrassCurve L) :
    IntermediateField.adjoin L
        ({Work.MotC2.genX E, Work.MotC2.genY E} : Set (Work.MotC2.Func E)) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [IntermediateField.mem_adjoin_iff_div]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Work.MotC2.Coord E) f
  exact ⟨algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) a,
    algebraMap_coord_mem_adjoin L E a,
    algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) b,
    algebraMap_coord_mem_adjoin L E b,
    hab.symm⟩

end Work.MotV5
