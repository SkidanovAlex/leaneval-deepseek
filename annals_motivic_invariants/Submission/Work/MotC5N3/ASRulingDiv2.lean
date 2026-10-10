import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.CensusAux
import Submission.Work.MotC5N3.ASZTwistDiv2
import Submission.Work.MotC5N3.K5Ruling
import Submission.Work.MotC5N3.IsDomainOfRatFuncEquiv
import Submission.Work.MotC5N3.JunkFwVec0

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASRulingDiv2` — K5 of the AS branch, generic in the base field `K`

The `RatFunc 𝕜 ↦ K`, `fAS 𝕜 ↦ g` fork of `Work.MotAS.ASRulingDiv2`
(`Submission/Work/MotAS/ASRulingDiv2.lean`): every height-one prime `x` of `K[x₀,x₁,x₂]` containing
the source ruling quintic `sAS2 (aK K D) (bK K D) g` has residue field
`FractionRing (Polynomial (K[x₀,x₁,x₂] ⧸ √(ZIAS (aK K D) (bK K D) g)))` — the function field of
`(residual curve) × 𝔸¹` — or is a junk class.

The two facts are independent, exactly as in the source:

* the **junk case** `fwVecAS2 (aK K D) (bK K D) g 0 ∈ x` is `Work.MotC5N3.JunkFwVec0`;
* the **main case** `fwVecAS2 … 0 ∉ x` is `Work.MotC5N3.K5Ruling` (a *temporary scaffold*
  standing for the in-progress `Work.MotC5N3.ASRulingMainV2Hab`, see `K5Ruling.lean` and
  `ASRULINGMAINV2_STATE.md`), whose
  domain input `IsDomain (K[x] ⧸ √(ZIAS a b g))` is supplied here by the K6 node: the fraction-ring
  isomorphism `Work.MotC5N3.ASZTwistDiv2` (whose right-hand side is a field) makes the quotient
  inject into a field (`Work.MotC5N3.isDomain_of_algEquiv_ratFunc`, via the injectivity of
  `A → A[X] → FractionRing (A[X])`).  The alternative route
  `Work.MotC5N3.ASZRingIsDomainGen` (from the plane-model certificate
  `Work.MotAS.aszPresentation`) is also available and still imported.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotC5N3

/-- **K5 of the AS branch, generic in `K`**: the source ruling divisor `sAS2 (aK K D) (bK K D) g`
is ruled over the residual curve `V(√(ZIAS (aK K D) (bK K D) g)) × 𝔸¹`. -/
theorem ASRulingDiv2 (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.sAS2 (aK K D) (bK K D) g ∈ x.asIdeal →
        Nonempty (Work.MotV.resF K x ≃ₐ[K]
          FractionRing (Polynomial (MvPolynomial (Fin 3) K ⧸
            Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)))) ∨
        Work.MotV.JunkClass K x := by
  intro x hx hmem
  by_cases hfw : Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0 ∈ x.asIdeal
  · exact Or.inr (JunkFwVec0 K D hD g hg x hx hfw)
  · -- the K6 node supplies the irreducibility of the residual quotient: its fraction ring over the
    -- polynomial ring is `RatFunc` of a field
    obtain ⟨e₂⟩ := ASZTwistDiv2 K D hD g hg
    haveI hDZ : IsDomain (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)) :=
      isDomain_of_algEquiv_ratFunc e₂
    exact Or.inl (K5Ruling K (aK K D) (bK K D) g
      (aK_sq_sub_ne (K := K) D hD) (mul_ne_zero (aK_ne_zero (K := K) D hD) (bK_ne_zero (K := K) D hD))
      hg x hx hmem hfw hDZ)

end Work.MotC5N3
