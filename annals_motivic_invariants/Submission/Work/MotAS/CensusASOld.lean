import Mathlib
import Submission.Work.MotAS.AK
import Submission.Work.MotK.CensusPrime.eq_span_of_height_one

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The (refuted) AS census `CensusAS` and its bridge, kept for the record

`CensusAS` is the census of the **degenerate** AS chart of `ChartDefs.lean`: its source divisor
`FdivAS = linAS · sAS · fwVecAS 4` is the zero polynomial, so `CensusAS` is false for every
`ASGood D` (`Submission/Work/MotAS/CensusASFalse.lean`) and `linkCertAS_of_censusAS` is vacuous.

This material used to live in `Submission/Work/MotAS/linkCertAS.lean`.  It is moved here because
the corrected interface (`Submission/Work/MotAS/CensusAS2.lean`) and the target theorem
`Work.MotAS.linkCertAS` now live on opposite sides of the import graph: the census modules must not
import `linkCertAS.lean` (that would be a cycle, since `linkCertAS` is proved *from* the census).

The replacement is `Work.MotAS.CensusAS2` / `Work.MotAS.linkCertAS_of_censusAS2`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Work.MotAS

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- **The census of the AS link.**  The six divisor clauses of the two link equations, in the
robust "every codimension-one point above the factor is of the stated class" form, together with
the non-vanishing of the two divisors and the chart isomorphism.

The two *class* clauses are the ruling assertions (the source and target ruling quintics are ruled
over the twisted Klein curve and its `Jac²`); the four *junk* clauses are the polar factors
`linAS`/`cubAS` (linear in the chart coordinates) and the two chart denominators. -/
def CensusAS (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) : Prop :=
  ∃ (hpr : (Ideal.span {sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜)} :
      Ideal (MvPolynomial (Fin 3) (RatFunc 𝕜))).IsPrime),
    Ideal.height (Ideal.span {sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜)}) = 1 ∧
    Nonempty (Work.MotV.resF (RatFunc 𝕜)
        ⟨Ideal.span {sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜)}, hpr⟩ ≃ₐ[RatFunc 𝕜]
      RatFunc ↥(twistFieldAS D (Work.MotV.fAS 𝕜))) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      sAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal →
    Nonempty (Work.MotV.resF (RatFunc 𝕜) x ≃ₐ[RatFunc 𝕜]
        RatFunc ↥(twistFieldAS D (2 • Work.MotV.fAS 𝕜))) ∨
      Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      linAS (aK D) (bK D) ∈ x.asIdeal → Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      cubAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      fwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      bwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  FdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 ∧
  GdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 ∧
  Nonempty (Localization.Away (FdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜)) ≃ₐ[RatFunc 𝕜]
    Localization.Away (GdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜)))

/-- **The census implies the certificate** (the AS analogue of
`Work.MotK.linkCertTGenInf_of_census`). -/
theorem linkCertAS_of_censusAS (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (hc : CensusAS D hD) :
    Nonempty (Work.MotV.LinkCert (RatFunc 𝕜) ↥(twistFieldAS D (Work.MotV.fAS 𝕜))
      ↥(twistFieldAS D (2 • Work.MotV.fAS 𝕜))) := by
  obtain ⟨hpr, hht, hres, hS, hLin, hCub, hFw, hBw, hFne, hGne, hΦ⟩ := hc
  have hcoh : ∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      Ideal.height x.asIdeal = 1 := fun x hx =>
    (AlgebraicGeometry.idealHeight_eq_coheight
      (CommRingCat.of (MvPolynomial (Fin 3) (RatFunc 𝕜))) x).trans hx
  let zP : Work.MotA.polySpec (RatFunc 𝕜) 3 :=
    ⟨Ideal.span {sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜)}, hpr⟩
  have hzP_ht : Order.coheight zP = 1 := by
    rw [← AlgebraicGeometry.idealHeight_eq_coheight
      (CommRingCat.of (MvPolynomial (Fin 3) (RatFunc 𝕜))) zP]
    exact hht
  refine ⟨{ F := FdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜)
            G := GdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜)
            hF := hFne
            hG := hGne
            Φ := Classical.choice hΦ
            zP := zP
            zP_ht := hzP_ht
            zP_mem := ?_
            zP_res := hres
            G_other := ?_
            F_all := ?_ }⟩
  · have hmul : cubAS (aK D) (bK D) (Work.MotV.fAS 𝕜) * sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜)
        * bwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 4
        ∈ Ideal.span {sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜)} :=
      Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    exact hmul
  · intro x hcx hxG hxne
    haveI hxprime : x.asIdeal.IsPrime := x.2
    have h1 : cubAS (aK D) (bK D) (Work.MotV.fAS 𝕜) * sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜)
        ∈ x.asIdeal ∨ bwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ∈ x.asIdeal :=
      hxprime.mem_or_mem hxG
    rcases h1 with hcs | hbw
    · have h2 : cubAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal
          ∨ sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal :=
        hxprime.mem_or_mem hcs
      rcases h2 with hc | hs
      · exact hCub x hcx hc
      · exact absurd (PrimeSpectrum.ext
          (Work.MotK.CensusPrime.eq_span_of_height_one _ hpr hht x.asIdeal (hcoh x hcx) hs)) hxne
    · exact hBw x hcx hbw
  · intro x hcx hxF
    haveI hxprime : x.asIdeal.IsPrime := x.2
    have h1 : linAS (aK D) (bK D) * sAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal
        ∨ fwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ∈ x.asIdeal :=
      hxprime.mem_or_mem hxF
    rcases h1 with hls | hfw
    · have h2 : linAS (aK D) (bK D) ∈ x.asIdeal
          ∨ sAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal :=
        hxprime.mem_or_mem hls
      rcases h2 with hl | hs
      · exact Or.inr (hLin x hcx hl)
      · exact hS x hcx hs
    · exact Or.inr (hFw x hcx hfw)

end Work.MotAS
