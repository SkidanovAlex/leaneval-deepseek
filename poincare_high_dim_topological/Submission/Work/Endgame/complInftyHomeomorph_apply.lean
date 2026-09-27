import Mathlib
import Submission.Work.Endgame.Defs

open scoped OnePoint

namespace Work.Endgame

/-- The complement of the point at infinity in `OnePoint X` is `X`, via the identity on the
underlying points. In particular `complInftyHomeomorph X` sends the point `x : X`, seen as an
element of `OnePoint X` (hence different from `∞`), back to `x`. -/
theorem complInftyHomeomorph_apply (X : Type*) [TopologicalSpace X] (x : X) :
    complInftyHomeomorph X ⟨(x : OnePoint X), by simp⟩ = x := by
  -- It suffices to compute the inverse homeomorphism on `x`.
  have hh : (complInftyHomeomorph X).symm x = ⟨(x : OnePoint X), by simp⟩ := by
    rw [complInftyHomeomorph, Homeomorph.symm_symm, Homeomorph.trans_apply]
    -- `complInftyHomeomorph X` inverts the composite
    -- `OnePoint X ≃ₜ Set.range OnePoint.some ≃ₜ {∞}ᶜ`, both stages being the identity on points.
    rw [show (OnePoint.isOpenEmbedding_coe.toIsEmbedding.toHomeomorph x) =
        ⟨(x : OnePoint X), Set.mem_range_self x⟩ from
      Subtype.ext (Topology.IsEmbedding.toHomeomorph_apply_coe _ x)]
    change (Set.equivOfEq (by rw [← OnePoint.compl_range_coe, compl_compl]))
        (⟨(x : OnePoint X), Set.mem_range_self x⟩ : Set.range OnePoint.some) =
      ⟨(x : OnePoint X), by simp⟩
    rw [Set.equivOfEq_apply]
  rw [← hh, Homeomorph.apply_symm_apply]

end Work.Endgame
