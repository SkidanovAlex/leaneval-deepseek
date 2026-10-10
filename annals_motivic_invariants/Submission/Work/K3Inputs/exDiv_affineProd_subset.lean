import Mathlib
import Submission.Work.K3Inputs.Defs
import Submission.Work.K3.coheight_le_of_flat
import Submission.Work.K3.isIsoAt_genericPoint
import Submission.Work.K3.eq_genericPoint_of_coheight_eq_zero
import Submission.Work.K3.partialIso_isOver_of_toRationalMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open MotivicInvariants

/-- **The provable half of the `exDiv` analysis of the product map `φ × id_𝔸ⁿ`.**

Let `φ : X ⤏ Y` be a birational map over `𝕜` and let `Ψ` be the base change of `φ` along the
projection `f : 𝔸(Fin n; Spec 𝕜) ⟶ Spec 𝕜` — i.e. the product map `φ × id_{𝔸ⁿ}` on
`X ×_{Spec 𝕜} 𝔸ⁿ ⤏ Y ×_{Spec 𝕜} 𝔸ⁿ` (the identification of the two models is
`CategoryTheory.Limits.pullbackSymmetry`).  If `p` is an exceptional divisor of `Ψ`, then its image
under the projection `baseChangeAlongProj f X : X ×_{Spec 𝕜} 𝔸ⁿ ⟶ X` is an exceptional divisor
of `φ`.

This is the stabilisation step of Lin–Shinder's proof of `thm:bir-generation` (b)
(`c(φ × id_W) ≠ 0` for `W = 𝔸^{n-4}`): the *inclusion* of exceptional divisors, proved from the K3
chapter's already-proved descent lemmas — `Work.K3.isIsoAt_baseChangeAlong` (isomorphism points
base change), `Work.K3.partialIso_isOver_of_toRationalMap`, `Work.K3.coheight_le_of_flat`
(codimension does not decrease along the flat projection), `Work.K3.isIsoAt_genericPoint` and
`Work.K3.eq_genericPoint_of_coheight_eq_zero`.  The *reverse* inclusion (every exceptional divisor
of `φ` gives one of `φ × id`, i.e. the codimension-one-ness of `Z × 𝔸ⁿ`) needs the codimension of
a divisor in a product, which is not in Mathlib: it is the named residual of the stabilisation
step (`Work.K3Inputs.StabilisationStep`). -/
theorem exDiv_affineProd_subset (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y]
    (φ : X.BirationalMap Y) [φ.IsOver (Spec (.of 𝕜))] (n : ℕ)
    [IsIntegral (Work.K3.baseChangeAlong (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) X)]
    [IsIntegral (Work.K3.baseChangeAlong (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) Y)]
    (Ψ : (Work.K3.baseChangeAlong (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) X).BirationalMap
      (Work.K3.baseChangeAlong (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) Y))
    (hΨ : ∀ (g : X.PartialMap Y) [g.IsOver (Spec (.of 𝕜))], g.toRationalMap = φ.hom →
      (Work.K3.PartialMap.baseChangeAlong (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) g).toRationalMap
        = Ψ.hom)
    {p : Work.K3.baseChangeAlong (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) X}
    (hp : p ∈ exDiv Ψ) :
    Work.K3.baseChangeAlongProj (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) X p ∈ exDiv φ := by
  simp only [exDiv, Set.mem_ofPred_eq] at hp ⊢
  obtain ⟨hco, hiso⟩ := hp
  -- `key` is the engine of both halves: a point of `X × 𝔸ⁿ` lying over a point at which `φ` is an
  -- isomorphism (or over the generic point of `X`) is an isomorphism point of `Ψ`, contradicting
  -- `p ∈ exDiv Ψ`.
  have key : ∀ (i : X.PartialIso Y), i.toRationalMap = φ.hom →
      Work.K3.baseChangeAlongProj (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) X p ∈ i.source →
      False := by
    intro i hi hmem
    exact hiso (Work.K3.isIsoAt_baseChangeAlong
      (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) Ψ hΨ i hi
      (Work.K3.partialIso_isOver_of_toRationalMap 𝕜 i φ hi) hmem p rfl)
  refine ⟨?_, ?_⟩
  · -- the codimension count: `coheight (proj p) = 1`
    refine le_antisymm ?_ ?_
    · -- `≤ 1`, because the projection is flat (a base change of `𝔸ⁿ ⟶ Spec 𝕜`)
      have h := Work.K3.coheight_le_of_flat
        (Work.K3.baseChangeAlongProj (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) X) p
      rwa [hco] at h
    · -- `≥ 1`: the projection of `p` is not the generic point of `X`, since `p` is not an
      -- isomorphism point of `Ψ` while every point over the generic point of `X` is one
      refine Order.one_le_iff_ne_zero.mpr ?_
      intro h0
      obtain ⟨i, hx, hi⟩ := Work.K3.isIsoAt_genericPoint φ
      exact key i hi (by
        rw [Work.K3.eq_genericPoint_of_coheight_eq_zero _ h0]
        exact hx)
  · -- not an isomorphism point: an isomorphism point of `φ` base changes to one of `Ψ`
    intro hφ
    obtain ⟨i, hx, hi⟩ := hφ
    exact key i hi hx

end Work.K3Inputs
