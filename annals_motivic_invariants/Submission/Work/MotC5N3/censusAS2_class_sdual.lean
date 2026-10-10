import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.CensusAux
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.Prime_sdualAS2
import Submission.Work.MotC5N3.SdualChart
import Submission.Work.MotC5N3.ASZChartSetupGen
import Submission.Work.MotC5N3.asTheta2_ker
import Submission.Work.MotK.CensusBridge.resF_span_eq_ratFunc
import Submission.Work.MotK.CensusBridge.isFractionRing_adjoin_range_ratFunc

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

/-- **The `sdualAS2` clause of the generic AS census** (the conjuncts `hpr`, `hht`, `hres`): the
principal ideal spanned by the target ruling quintic `sdualAS2 (aK K D) (bK K D) g` is prime of
height one, and its residue field is `K`-isomorphic to `RatFunc (twistFieldAS D g)`.

This is the `RatFunc 𝕜 ↦ K` fork of `Work.MotV5.ASLocal.censusAS2_class_sdual`
(`Submission/Work/MotV5/ASLocal/ClassSdual.lean`, itself a local fork of
`Submission/Work/MotAS/censusAS2_class_sdual.lean`).  The source is proved at `RatFunc 𝕜` with
coordinates `Work.MotAS.aK D`, `Work.MotAS.bK D` and class `Work.MotV.fAS 𝕜`; here the base field
is an arbitrary `𝕜`-algebra field `K` of characteristic `5`, the class is an arbitrary `g ∉ ℘(K)`,
the coordinates are `Work.MotC5N3.aK K D`, `Work.MotC5N3.bK K D`
(`Submission/Work/MotC5N3/AK.lean`) and the twist field is the generic
`Work.MotC5N3.twistFieldAS D g` of `Submission/Work/MotC5N3/Defs.lean`.  `hg` is exactly the
engine's input: `¬ ∃ u, u ^ 5 - u = g` implies `g ≠ 0` and `Irreducible (C g · X⁵ − X⁴ + 1)` for
`prime_sdualAS2_of`; the final residue-field step is the already-generic
`Work.MotK.CensusBridge.resF_span_eq_ratFunc`.

Route: fork into namespace `Work.MotC5N3` the `RatFunc 𝕜`-specific wrappers the source uses —
`Submission/Work/MotAS/Prime_sdualAS2.lean`, `asTheta2_ker.lean`, `asTheta2_fracTop.lean`,
`asR2_trdeg_two.lean`, `asTheta2_sdualAS2.lean`, `ASZTwistDiv2.lean`, and the local forks under
`Submission/Work/MotV5/ASLocal/` — together with the generic engine they call.
`Submission/Work/MotC5N3/port.py` performs the textual port; the six files already forked under
`Submission/Work/MotC5N3/TwistField/` are the model.  Two engine results the chain uses are still
`sorry` in `MotAS` and must be supplied generically: `Work.MotAS.KleinTwI2AS` (a pure polynomial
identity over any commutative ring of characteristic `5`; note that
`Work.MotV5.ASChart.kleinPAS_kleinRAS_free` proves exactly it in every commutative ring with
`5 = 0`) and `Work.MotV5.ASLocal.asRho_cert_rank(_alt)`.  Nothing about `fAS` or about
`RatFunc 𝕜` beyond `g ≠ 0` and `g ∉ ℘(K)` may be used.

Deliverable: namespace `Work.MotC5N3`, file `Submission/Work/MotC5N3/censusAS2_class_sdual.lean`
(helpers in sibling files), sorry-free and axiom-clean. -/
theorem censusAS2_class_sdual (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    ∃ (hpr : (Ideal.span {Work.MotAS.sdualAS2 (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g} : Ideal (MvPolynomial (Fin 3) K)).IsPrime),
      Ideal.height (Ideal.span {Work.MotAS.sdualAS2 (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g}) = 1 ∧
      Nonempty (Work.MotV.resF K ⟨Ideal.span {Work.MotAS.sdualAS2 (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g}, hpr⟩ ≃ₐ[K]
        RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) := by
  classical
  haveI h𝕜 : CharP 𝕜 5 := charP_of_algebra_charP (𝕜 := 𝕜) (K := K)
  have hG : Prime (Work.MotAS.sdualAS2 (aK K D) (bK K D) g) := Prime_sdualAS2 K D hD g hg
  have hker := asTheta2_ker K D hD g hg
  have hfrac := asTheta2_fracTop D hD g
  haveI : IsDomain ↥(asR2 D g) := inferInstance
  haveI hFR : IsFractionRing (asR2 D g) (RatFunc ↥(twistFieldAS D g)) :=
    Work.MotK.CensusBridge.isFractionRing_of_subfield_closure_range _ hfrac
  let θR : MvPolynomial (Fin 3) K →ₐ[K] ↥(asR2 D g) :=
    (asTheta2 D g).codRestrict (asR2 D g) (fun p => by
      rw [← asTheta2_range D g]
      exact ⟨p, rfl⟩)
  have hsurj : Function.Surjective θR := by
    intro y
    have hy : (y : RatFunc ↥(twistFieldAS D g)) ∈ (asTheta2 D g).range := by
      rw [asTheta2_range D g]
      exact y.2
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, Subtype.ext hp⟩
  have hkerR : RingHom.ker θR
      = Ideal.span {Work.MotAS.sdualAS2 (aK K D) (bK K D) g} := by
    rw [← hker]
    ext p
    simp only [RingHom.mem_ker]
    exact ⟨fun hp => Subtype.ext_iff.mp hp, fun hp => Subtype.ext_iff.mpr hp⟩
  have he : FractionRing ↥(asR2 D g) ≃ₐ[K] RatFunc ↥(twistFieldAS D g) :=
    (IsFractionRing.algEquivOfAlgEquiv (A := ↥(asR2 D g)) (B := ↥(asR2 D g))
      (K := FractionRing ↥(asR2 D g)) (L := RatFunc ↥(twistFieldAS D g))
      (AlgEquiv.refl (R := ↥(asR2 D g)))).restrictScalars K
  exact Work.MotK.CensusBridge.resF_span_eq_ratFunc (K := K)
    (R := ↥(asR2 D g)) (F := ↥(twistFieldAS D g))
    θR (Work.MotAS.sdualAS2 (aK K D) (bK K D) g) hG.ne_zero hkerR hsurj he

end Work.MotC5N3
