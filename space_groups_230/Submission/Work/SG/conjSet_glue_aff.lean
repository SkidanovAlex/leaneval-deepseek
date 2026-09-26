import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.affEquiv_facts

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

/-- Gluing conjugacies to lattice-normalised data, affine version (no determinant condition on
`θ`): if `ψ` carries the affine image of `G` onto `sgSet P τ`, `ψ'` carries that of `G'` onto
`sgSet P' τ'`, and `θ` carries `sgSet P τ` onto `sgSet P' τ'`, then `G` and `G'` are affinely
equivalent. -/
theorem conjSet_glue_aff {G G' : Subgroup (EuclideanIsom 3)}
    {P P' : Set IMat} {τ τ' : IMat → Fin 3 → ℝ} {ψ ψ' θ : AffineGroup 3}
    (hψ : conjSet ψ (affImage G) = sgSet P τ)
    (hψ' : conjSet ψ' (affImage G') = sgSet P' τ')
    (hθ : conjSet θ (sgSet P τ) = sgSet P' τ') :
    AffinelyEquivalent G G' := by
  -- `conjSet` and `AffFacts.conjAct` define the same conjugation action on sets, and
  -- `affImage` and `AffFacts.affImage` the same affine image, so we may use the general
  -- action laws for `conjAct` here.
  obtain ⟨-, hiffAE, -⟩ := affinelyEquivalent_conjAct 3
  obtain ⟨hc1, hc2⟩ := conjAct_action 3
  rw [hiffAE]
  -- the conjugator gluing `ψ`, `θ`, `ψ'` together
  refine ⟨ψ'⁻¹ * θ * ψ, ?_⟩
  -- `conjSet (ψ'⁻¹ * θ * ψ) (affImage G)
  --    = conjSet ψ'⁻¹ (conjSet θ (conjSet ψ (affImage G)))`
  rw [hc2 (ψ'⁻¹ * θ) ψ]
  change AffFacts.conjAct (ψ'⁻¹ * θ) (conjSet ψ (affImage G)) = AffFacts.affImage G'
  rw [hψ]
  rw [hc2 ψ'⁻¹ θ]
  change AffFacts.conjAct ψ'⁻¹ (conjSet θ (sgSet P τ)) = AffFacts.affImage G'
  rw [hθ]
  rw [← hψ']
  change AffFacts.conjAct ψ'⁻¹ (AffFacts.conjAct ψ' (AffFacts.affImage G')) =
    AffFacts.affImage G'
  rw [← hc2 ψ'⁻¹ ψ']
  rw [inv_mul_cancel, hc1]

end Work.SG
