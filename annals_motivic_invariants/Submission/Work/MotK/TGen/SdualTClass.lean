import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.LinkCertGen
import Submission.Work.MotV.Defs
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TwCensus.SdualTPrime
import Submission.Work.MotK.TwRuling.SdualTClass_charTwo
import Submission.Work.MotK.TwRuling.SdThetaKernel_charNeTwo
import Submission.Work.MotK.TwRuling.SdThetaFracTop_charNeTwo
import Submission.Work.MotK.CensusBridge.resF_span_eq_ratFunc
import Submission.Work.MotK.CensusBridge.isFractionRing_adjoin_range_ratFunc

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

open MvPolynomial

/-- The range of `sdTheta` is the subalgebra `sdR`. -/
theorem sdTheta_range (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) :
    (sdTheta K D h).range = sdR K D h := by
  have := MvPolynomial.aeval_range (R := K) (S₁ := sdA K D h) (σ := Fin 3) (sdPhi K D h)
  simpa only [sdTheta, sdR] using this

/-- **The `sdualT` clause of the census away from characteristic 2.**  This is `SdualTClass`
with the hypothesis `(2 : K) ≠ 0`, its proof being the same; the hypothesis is necessary
because the `sdTheta` presentation is *false* in characteristic 2 (there the two ruling
vectors of the twisted Klein curve are proportional, so `sdPhi` loses its `t`-dependence and
`sdR` drops to transcendence degree `<= 1`; see the module docstring of
`Submission/Work/MotK/TwRuling/SdThetaKernel.lean`).  The characteristic-2 case is handled by
`Work.MotK.TwRuling.SdualTClass_charTwo`, where the ruling degenerates but the fibration
`kleinTwR|_{s'=0} : {s' = 0} ⇢ C_h` still has rational fibres
(`Submission/Work/MotK/TwRuling/NOTE_charTwo_fibres.md`). -/
theorem SdualTClass_charNeTwo (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (h2 : (2 : K) ≠ 0) (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    ∃ hpr : (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
        Ideal (MvPolynomial (Fin 3) K)).IsPrime,
      Ideal.height (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
        Ideal (MvPolynomial (Fin 3) K)) = 1 ∧
      Nonempty (Work.MotV.resF K ⟨Ideal.span {Work.MotK.TGen.sdualT D.a D.b h}, hpr⟩ ≃ₐ[K]
        RatFunc ↥(Work.MotK.twistFieldTG K D h)) := by
  have hG : Prime (sdualT D.a D.b h) :=
    Work.MotK.TwCensus.SdualTPrimeGood K hk D hD h hh
  have hker : RingHom.ker (sdTheta K D h) = Ideal.span {sdualT D.a D.b h} :=
    Work.MotK.TwRuling.SdThetaKernel_charNeTwo K h2 D hD h hh hG
  have hfrac : Subfield.closure
      (Set.range (algebraMap (sdR K D h) (sdA K D h))) = ⊤ :=
    Work.MotK.TwRuling.SdThetaFracTop_charNeTwo K h2 D hD h hh
  haveI : IsDomain ↥(sdR K D h) := inferInstance
  haveI hFR : IsFractionRing (sdR K D h) (sdA K D h) :=
    Work.MotK.CensusBridge.isFractionRing_of_subfield_closure_range (sdR K D h) hfrac
  -- the codRestricted presentation
  let θR : MvPolynomial (Fin 3) K →ₐ[K] ↥(sdR K D h) :=
    (sdTheta K D h).codRestrict (sdR K D h) (fun p => by
      rw [← sdTheta_range K D h]
      exact ⟨p, rfl⟩)
  have hsurj : Function.Surjective θR := by
    intro y
    have hy : (y : sdA K D h) ∈ (sdTheta K D h).range := by
      rw [sdTheta_range K D h]; exact y.2
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, Subtype.ext hp⟩
  have hkerR : RingHom.ker θR = Ideal.span {sdualT D.a D.b h} := by
    rw [← hker]
    ext p
    simp only [RingHom.mem_ker]
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · exact Subtype.ext_iff.mp hp
    · exact Subtype.ext_iff.mpr hp
  have he : FractionRing ↥(sdR K D h) ≃ₐ[K] sdA K D h :=
    (IsFractionRing.algEquivOfAlgEquiv (A := ↥(sdR K D h)) (B := ↥(sdR K D h))
      (K := FractionRing ↥(sdR K D h)) (L := sdA K D h)
      (AlgEquiv.refl (R := ↥(sdR K D h)))).restrictScalars K
  exact Work.MotK.CensusBridge.resF_span_eq_ratFunc (K := K) (R := ↥(sdR K D h))
    (F := ↥(Work.MotK.twistFieldTG K D h)) θR (sdualT D.a D.b h) hG.ne_zero hkerR hsurj he


/-- **Node K5/K4 of the census: the `sdualT` clause of `Work.MotK.TGenCensus`.**

`(sdualT D.a D.b h)` is a height-one prime whose residue field is `RatFunc ↥(twistFieldTG K D h)`,
i.e. the function field of the target ruling divisor `{sdualT = 0}` is `κ(C_h)(t)`.

The proof splits on the characteristic, because the *presentation* of that surface depends on it:

* **characteristic 2**: the two ruling vectors of the twisted Klein curve are proportional, so the
  ruling `A + t·B` degenerates and the `sdTheta` presentation is unavailable; but the fibration
  `kleinTwR|_{s'=0} : {s' = 0} ⇢ C_h` still has rational fibres
  (`Submission/Work/MotK/TwRuling/NOTE_charTwo_fibres.md` records the numerical check: the fibres
  have `31`/`32` projective points over `GF(32)`, a spread of one, while a genus-one fibre would
  fluctuate by `±11`), and that presentation is `Work.MotK.TwRuling.SdualTClass_charTwo`.
* **characteristic `≠ 2`**: `Work.MotK.TGen.SdualTClass_charNeTwo` (the `sdTheta` presentation,
  `ker (sdTheta) = (sdualT)`) — whose hypothesis `(2 : K) ≠ 0` is exactly what makes
  `Work.MotK.TwRuling.SdThetaFracTop` true. -/
theorem SdualTClass (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    ∃ hpr : (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
        Ideal (MvPolynomial (Fin 3) K)).IsPrime,
      Ideal.height (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
        Ideal (MvPolynomial (Fin 3) K)) = 1 ∧
      Nonempty (Work.MotV.resF K ⟨Ideal.span {Work.MotK.TGen.sdualT D.a D.b h}, hpr⟩ ≃ₐ[K]
        RatFunc ↥(Work.MotK.twistFieldTG K D h)) := by
  by_cases h2 : (2 : K) = 0
  · exact Work.MotK.TwRuling.SdualTClass_charTwo K h2 D hD h hh
  · exact SdualTClass_charNeTwo K hk h2 D hD h hh

end Work.MotK.TGen
