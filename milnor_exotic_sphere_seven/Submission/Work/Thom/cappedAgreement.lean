import Mathlib
import Submission.Work.Thom.smooth8
import Submission.Work.Milnor.CappedManifold
import Submission.Work.TangentClasses.Capped
import Submission.Work.SignatureBordism.Obstruction
import Submission.Work.Milnor.CongruenceInterface

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The consistency of the repaired interface with the delivered `TangentClasses` chapter

The repaired interface of `Submission/Work/Thom/smooth8.lean` defines `p₁(TM) = p1Tangent'` for
*every* compact smooth manifold, in particular for the capped `8`-manifold
`X = D(ξ) ∪_F D⁸ = Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)`.  The delivered
`TangentClasses` chapter constructs a class `Work.TangentClasses.p1Tangent F hF S` for `p₁(TX)`
(from the disc-bundle splitting `S` of `TX`, and equal to `Work.Milnor.cappedPontryaginClass F hF`
by `p1Tangent_eq_cappedPontryaginClass`).

This module **records the statement that the two agree**, in the sharpest available form (the sign
being the normalisation of the generator of `H⁴(S⁴;ℤ)`, exactly as in
`Work.TangentClasses.p1Tangent_eq_pm_cappedPontryaginClass`; the sign is irrelevant for the endgame
because it uses `p₁²`, `Work.TangentClasses.p1SqNumber_neg`).

It is **not proved here**: it needs the naturality of the Chern classes under pullback and
restriction — the splitting principle — which in turn needs choice-free (canonical) Thom classes;
see `README.md` ADDENDUM 20, items (G1)–(G3).
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
variable (hF : Work.Milnor.IsCappingDiffeo F)

section

attribute [local instance] Work.Milnor.cappedChartedSpace
attribute [local instance] Work.Milnor.capped_isManifold
attribute [local instance] Work.Milnor.isCompact_capped

/-- **The consistency of `p1Tangent'` with the delivered `p₁(TX)`**, up to the global sign coming
from the normalisation of the generator of `H⁴(S⁴;ℤ)`: for every disc-bundle splitting `S` of `TX`,
the class `Work.Thom.p1Tangent'` of the tangent bundle of `X = D(ξ) ∪_F D⁸` is
`± Work.TangentClasses.p1Tangent F hF S` (hence, by
`Work.TangentClasses.p1Tangent_eq_cappedPontryaginClass`, `± Work.Milnor.cappedPontryaginClass F hF`).

This is the theorem a future session must prove (see `README.md` ADDENDUM 20 (G3)); it is the
statement that the *defined* class of the new chapter agrees with the *constructed* class of the
delivered one. -/
def CappedAgreement (S : DiscTangentSplitting) : Prop :=
  p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
      (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))
    = p1Tangent F hF S ∨
  p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
      (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))
    = - p1Tangent F hF S

/-- **The consistency of `p1Tangent'` with `Work.Milnor.cappedPontryaginClass`**: the only
mathematical input of the reduction of the project's target to the repaired interface (see
`README.md` ADDENDUM 20 (G3)). -/
def CappedAgreement' : Prop :=
  p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
      (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))
    = Work.Milnor.cappedPontryaginClass F hF ∨
  p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
      (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))
    = - Work.Milnor.cappedPontryaginClass F hF

/-- **The instantiation of the repaired interface at the capped family**: the congruence
`7 ∣ ⟨p₁(TX) ⌣ p₁(TX), [X]⟩ − 4 σ(X)` for `X = D(ξ) ∪_F D⁸`, with `p₁(TX)` the **defined** class
`Work.Thom.p1Tangent'` of the tangent bundle rather than the class `Work.Milnor.cappedPontryaginClass`
constructed by the characteristic-classes chapter.

This is *the same statement* as `Work.Milnor.CappedCongruence` except that `p₁(TX)` is the new
*defined* class; `CappedAgreement'` is exactly what relates the two, and
`Work.Thom.cappedCongruenceTangent_of_hirzebruchCongruence8` shows that the repaired global
statement `Work.Thom.HirzebruchCongruence8` implies it **unconditionally**. -/
def CappedCongruenceTangent : Prop :=
  ∀ (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8) (hF : Work.Milnor.IsCappingDiffeo F)
    (c : (Work.Cohomology.chainC ℤ (Work.SignatureBordism.cappedSSet F hF)).homology 8),
    Submodule.span ℤ {c} = ⊤ →
      7 ∣ Work.SignatureBordism.p₁SqNumber (Work.SignatureBordism.cappedSSet F hF) c
              (p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
                (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
            - 4 * Work.SignatureBordism.sigma 4 (Work.SignatureBordism.cappedSSet F hF) c

/-- **The repaired interface (with the consistency statement) implies the project's target.**
Given the global congruence `Work.Thom.HirzebruchCongruence8` for closed oriented smooth
`8`-manifolds with the *defined* tangent-bundle Pontryagin classes, and the consistency
`CappedAgreement'` of `p1Tangent'` with `Work.Milnor.cappedPontryaginClass`, the project's remaining
target `Work.Milnor.CappedCongruence` holds.

Together with `Work.Milnor.no_cappingDiffeo_of_cappedCongruence` this is the F2 architecture of
`Submission/NOTES.md` §15.10: *repaired interface ⟹ target*; the converse direction (the target
follows from the classical dimension-`8` signature theorem) is in
`Submission/Work/OrientedBordism8/`. -/
theorem cappedCongruence_of_cappedCongruenceTangent
    (h : CappedCongruenceTangent)
    (hagree : ∀ (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
      (hF : Work.Milnor.IsCappingDiffeo F), CappedAgreement' F hF) :
    Work.Milnor.CappedCongruence := by
  intro F hF c hc
  rcases hagree F hF with hp | hp
  · rw [← hp]
    exact h F hF c hc
  · have hkey : Work.SignatureBordism.p₁SqNumber (Work.SignatureBordism.cappedSSet F hF) c
          (Work.Milnor.cappedPontryaginClass F hF)
        = Work.SignatureBordism.p₁SqNumber (Work.SignatureBordism.cappedSSet F hF) c
          (p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
            (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))) := by
      rw [hp]
      simp only [Work.SignatureBordism.p₁SqNumber_apply, map_neg, LinearMap.neg_apply, neg_neg]
    rw [hkey]
    exact h F hF c hc

end

end

end Work.Thom
