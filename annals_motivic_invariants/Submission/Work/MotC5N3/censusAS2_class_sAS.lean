import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.CensusAux
import Submission.Work.MotC5N3.ASRulingDiv2
import Submission.Work.MotC5N3.ASZTwistDiv2

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

/-- **The `sAS2` clause of the generic AS census** (the conjunct `hS`): every height-one prime of
`K[Fin 3]` containing the source ruling quintic `sAS2 (aK K D) (bK K D) g` has either residue field
`K`-isomorphic to `RatFunc (twistFieldAS D (2 • g))` (the residual class `z ≅ C_{2g}`) or is a junk
class.

This is the `RatFunc 𝕜 ↦ K` fork of `Work.MotAS.censusAS2_class_sAS`
(`Submission/Work/MotAS/censusAS2_class_sAS.lean`), whose base field is `RatFunc 𝕜` and whose class
is `Work.MotV.fAS 𝕜`.  Here `K` is an arbitrary `𝕜`-algebra field of characteristic `5`, the class
is an arbitrary `g ∉ ℘(K)`, the coordinates are `Work.MotC5N3.aK K D`, `Work.MotC5N3.bK K D` and
the twist fields are the generic ones of `Submission/Work/MotC5N3/Defs.lean`.

Route (WP7 of `MOTIVIC_CHAR5_N3_LEAD.md`): the source proof is
`rcases ASRulingDiv2 𝕜 D hD x hx hmem with h | hj` followed by `ASZTwistDiv2`.  Fork those two and
their chain into namespace `Work.MotC5N3` — `Submission/Work/MotAS/ASRulingDiv2.lean`,
`ASZTwistDiv2.lean`, `ASResidual.lean`, `ASZTwistDivBase.lean`, `ASZTwistDivPlaneGeomV2.lean`,
`ASZelimModel.lean`, `ASRulingMainV2.lean`, `aszPresentation.lean`, `ASZChartPresentation.lean`,
`ASZChartSetup.lean`, `ASZRingIsDomain.lean`, `ASZTwistDefs.lean`, `AsRhoDefs.lean`,
`aeval_asM_twIdeal_subset.lean`, `asChartHomogenisation.lean`, `asChartKernelLe.lean`,
`asChartPhi_height_le.lean`, `kerAevalKleinPAS_gen.lean`, `transcendental_twistFieldAS_gen.lean`,
`ASLocal/aevalAsMAevalAsMinv.lean` — generalising the base field to `K` with class `g`.
`Submission/Work/MotC5N3/port.py` performs the textual port.  Five of those are still `sorry` in
`MotAS` (`ASRulingMainV2`, `ASZelimModel`, `aszPresentation`, `ASZTwistDivBase`,
`ASZTwistDivPlaneGeomV2`) and must be supplied in generic form; several of their *statements* are
already generic in `(K, a, b, g)` with `g ∉ ℘(K)`, so this is a supply-the-proof job.  No `t`-degree
or transcendence-of-`t` argument may be used (§7 of the design file).

Deliverable: namespace `Work.MotC5N3`, file `Submission/Work/MotC5N3/censusAS2_class_sAS.lean`
(helpers in sibling files), sorry-free and axiom-clean. -/
theorem censusAS2_class_sAS (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.sAS2 (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g ∈ x.asIdeal →
        Nonempty (Work.MotV.resF K x ≃ₐ[K]
            RatFunc ↥(Work.MotC5N3.twistFieldAS D (2 • g))) ∨
        Work.MotV.JunkClass K x := by
  intro x hx hmem
  rcases ASRulingDiv2 K D hD g hg x hx hmem with h | hj
  · obtain ⟨e₁⟩ := h
    obtain ⟨e₂⟩ := ASZTwistDiv2 K D hD g hg
    exact Or.inl ⟨e₁.trans e₂⟩
  · exact Or.inr hj

end Work.MotC5N3
