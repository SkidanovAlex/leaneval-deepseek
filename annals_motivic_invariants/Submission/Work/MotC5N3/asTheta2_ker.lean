import Mathlib
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.ASZChartSetupGen
import Submission.Work.MotC5N3.asY0_curve
import Submission.Work.MotC5N3.asPhi2_denom
import Submission.Work.MotC5N3.asRule_rank
import Submission.Work.MotC5N3.asTheta2_sdualAS2_aux
import Submission.Work.MotC5N3.asTheta2_fracTop_of
import Submission.Work.MotC5N3.trdeg_twistFieldAS
import Submission.Work.MotC5N3.Prime_sdualAS2
import Submission.Work.MotV.trdeg_fractionRing_mvPolynomial
import Submission.Work.MotK.TwCensus.TwistFieldTGRatFuncTrdeg
import Submission.Work.MotK.TwRuling.height_ker_eq_one
import Submission.Work.MotK.CensusPrime.eq_span_of_height_one
import Submission.Work.MotC5N3.Work.asRho_ne_zero_general_ne

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.asTheta2_ker` — the kernel of the chart-2 presentation

See the docstring of `asTheta2_ker` below.

The file is written with a *minimal* dependency surface (no import of
`Submission.Work.MotC5N3.SdualChart` / `…asR2_trdeg_two`, whose closures contain the
`RatFunc 𝕜`-hardwired rho certificate): the three chart-2 non-degeneracy inputs, the twist-field
transcendence degree and the two `MotK` height/assembly lemmas are taken from their own modules,
and the fraction-field generation (`asTheta2_fracTop`) and the surface statement
(`asR2_trdeg_two`) are assembled here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotC5N3

variable {𝕜 : Type} [Field 𝕜]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-- **The fraction field of the AS twist curve has transcendence degree two.**  Tower law over the
twist field (`Work.MotC5N3.trdeg_twistFieldAS`, transcendence degree `1`) and the extra variable
(`Work.MotK.TwCensus.trdeg_ratFunc_eq_two_of_trdeg_eq_one`). -/
theorem trdeg_twistFieldAS_ratFunc_ker (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Algebra.trdeg K (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) = 2 :=
  Work.MotK.TwCensus.trdeg_ratFunc_eq_two_of_trdeg_eq_one K
    ↥(Work.MotC5N3.twistFieldAS D g) (trdeg_twistFieldAS K D hD g)

/-- **The rho input**: the inverse AS quadro-cubic map `kleinRAS` does not vanish identically on
the ruling line over the generic curve point `asY0 D g`. -/
theorem asRho_ne_zero_ker (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K) (hg0 : g ≠ 0) :
    ∃ i : Fin 5, Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) (asW2 D g) i ≠ 0 :=
  Work.MotC5N3.Work.asRho_ne_zero_general_ne K D hD g hg0

/-- **The normalised rho input**: `kleinRAS` does not vanish at the normalised ruling point
`(1, φ 0, φ 1, φ 2, 0)`.  From `asRho_ne_zero_ker` by degree-`3` homogeneity and `asPhi2_denom`. -/
theorem asPhi2_rho_ne_zero_ker (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K) (hg0 : g ≠ 0) :
    Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g)
      (fun j => asW2 D g j / asW2 D g 0) ≠ 0 := by
  obtain ⟨i, hi⟩ := asRho_ne_zero_ker K D hD g hg0
  have hW0 : asW2 D g 0 ≠ 0 := asPhi2_denom K D hD g
  have hdiv : (fun j => asW2 D g j / asW2 D g 0)
      = fun j => (asW2 D g 0)⁻¹ * asW2 D g j := by
    funext j
    rw [div_eq_mul_inv, mul_comm]
  rw [hdiv, Work.MotAS.kleinRAS_smul]
  intro hzero
  have h := congrFun hzero i
  simp only [Pi.zero_apply] at h
  exact hi ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 (inv_ne_zero hW0)))

/-- **The target ruling quintic lies in the kernel of the chart presentation.** -/
theorem asTheta2_sdualAS2_ker (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    asTheta2 D g (Work.MotAS.sdualAS2 (aK K D) (bK K D) g) = 0 :=
  asTheta2_sdualAS2_aux K D hD g (asY0_curve K D hD g) (asPhi2_denom K D hD g)

/-- **The fraction field of the chart algebra is everything**: the ruling parametrisation of the
corrected AS chart generates `RatFunc ↥(twistFieldAS D g)`. -/
theorem asTheta2_fracTop_ker (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K) (hg0 : g ≠ 0) :
    Subfield.closure (Set.range (algebraMap ↥(asR2 D g)
      (RatFunc ↥(twistFieldAS D g)))) = ⊤ :=
  asTheta2_fracTop_of K D hD g (asPhi2_denom K D hD g) (asPhi2_rho_ne_zero_ker D hD g hg0)
    (asRule_rank K D hD g)

/-- **The chart-2 presentation is a surface**: `Algebra.trdeg K ↥(asR2 D g) = 2`. -/
theorem asR2_trdeg_two_ker (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg0 : g ≠ 0) :
    Algebra.trdeg K ↥(Work.MotC5N3.asR2 D g) = 2 := by
  have hfrac := asTheta2_fracTop_ker D hD g hg0
  haveI hFR : IsFractionRing ↥(asR2 D g) (RatFunc ↥(twistFieldAS D g)) :=
    Work.MotK.CensusBridge.isFractionRing_of_subfield_closure_range _ hfrac
  -- passing to the fraction ring does not change the transcendence degree
  have h1 : Algebra.trdeg K ↥(asR2 D g)
      = Algebra.trdeg K (FractionRing ↥(asR2 D g)) := by
    haveI : Algebra.IsAlgebraic ↥(asR2 D g) (FractionRing ↥(asR2 D g)) :=
      Work.MotV.isAlgebraic_fractionRing_self _
    have h := trdeg_add_eq K ↥(asR2 D g) (A := FractionRing ↥(asR2 D g))
    have h0 : Algebra.trdeg ↥(asR2 D g) (FractionRing ↥(asR2 D g)) = 0 := trdeg_eq_zero
    rw [h0, add_zero] at h
    exact h
  have he : FractionRing ↥(asR2 D g) ≃ₐ[K] RatFunc ↥(twistFieldAS D g) :=
    (IsFractionRing.algEquivOfAlgEquiv (A := ↥(asR2 D g)) (B := ↥(asR2 D g))
      (K := FractionRing ↥(asR2 D g)) (L := RatFunc ↥(twistFieldAS D g))
      (AlgEquiv.refl (R := ↥(asR2 D g)))).restrictScalars K
  rw [h1, AlgEquiv.trdeg_eq he, trdeg_twistFieldAS_ratFunc_ker K D hD g]

/-- **The kernel of the chart-2 presentation is exactly `(sdualAS2 (aK K D) (bK K D) g)`.**
Port (general base field `K`, general class `g ∉ ℘(K)`) of
`Submission/Work/MotV5/ASLocal/asTheta2_ker.lean` (itself the fork of `MotAS/asTheta2_ker.lean`).
Route: `Algebra.trdeg K ↥((asTheta2 D g).range) = 2` (from `MotC5N3.asTheta2_range` and
`MotC5N3.asR2_trdeg_two`), so `(RingHom.ker (asTheta2 D g)).height = 1` by
`Work.MotK.TwRuling.height_ker_eq_one`; `MotC5N3.asTheta2_sdualAS2` puts `sdualAS2` in the kernel
and `MotC5N3.Prime_sdualAS2` makes it prime, so the principal prime `(sdualAS2)` has height `1` and
`Work.MotK.CensusPrime.eq_span_of_height_one` gives the equality. -/
theorem asTheta2_ker (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    RingHom.ker (Work.MotC5N3.asTheta2 D g)
      = Ideal.span {Work.MotAS.sdualAS2 (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g} := by
  -- the transcendence degree of the range: the presentation is a surface
  haveI h𝕜 : CharP 𝕜 5 := charP_of_algebra_charP (𝕜 := 𝕜) (K := K)
  have hg0 : g ≠ 0 := by
    intro h
    exact hg ⟨0, by rw [h]; ring⟩
  have htr : Algebra.trdeg K ↥((asTheta2 D g).range) = 2 := by
    rw [asTheta2_range D g]
    exact asR2_trdeg_two_ker K D hD g hg0
  -- the kernel is a height-one prime
  have hht : (RingHom.ker (asTheta2 D g)).height = 1 :=
    Work.MotK.TwRuling.height_ker_eq_one K (asTheta2 D g) htr
  -- `sdualAS2` is a prime element of the kernel
  have hGprime : Prime (Work.MotAS.sdualAS2 (aK K D) (bK K D) g) :=
    Prime_sdualAS2 K D hD g hg
  have hGmem : asTheta2 D g (Work.MotAS.sdualAS2 (aK K D) (bK K D) g) = 0 :=
    asTheta2_sdualAS2_ker D hD g
  have hle : (Ideal.span {Work.MotAS.sdualAS2 (aK K D) (bK K D) g} :
        Ideal (MvPolynomial (Fin 3) K)) ≤ RingHom.ker (asTheta2 D g) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact hGmem
  have hspan_prime : (Ideal.span {Work.MotAS.sdualAS2 (aK K D) (bK K D) g} :
      Ideal (MvPolynomial (Fin 3) K)).IsPrime :=
    (Ideal.span_singleton_prime hGprime.ne_zero).mpr hGprime
  -- the principal prime has height one as well: it is nonzero and below a height-one prime
  have hhtG : (Ideal.span {Work.MotAS.sdualAS2 (aK K D) (bK K D) g} :
      Ideal (MvPolynomial (Fin 3) K)).height = 1 := by
    refine le_antisymm (le_trans (Ideal.height_mono hle) (le_of_eq hht)) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot]
    exact hGprime.ne_zero
  have hkerprime : (RingHom.ker (asTheta2 D g)).IsPrime := RingHom.ker_isPrime _
  haveI := hkerprime
  exact Work.MotK.CensusPrime.eq_span_of_height_one
    (Work.MotAS.sdualAS2 (aK K D) (bK K D) g) hspan_prime hhtG
    (RingHom.ker (asTheta2 D g)) hht
    (by simpa using hle (Ideal.mem_span_singleton_self _))

end Work.MotC5N3
