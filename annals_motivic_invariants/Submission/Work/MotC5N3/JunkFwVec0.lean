import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.AzPrime

-- the polynomial engine of the AS chart, already generic in `(a b g : K)`:
import Submission.Work.MotAS.AzDefs
import Submission.Work.MotAS.azThetaDefs
import Submission.Work.MotAS.kleinPAS_kleinRAS_azPlane
import Submission.Work.MotAS.azTheta_fwVecAS2
import Submission.Work.MotAS.azFracRange
import Submission.Work.MotAS.azKerHeight
-- the two generic closing tools
import Submission.Work.MotK.CensusPrime.eq_span_of_height_one
import Submission.Work.MotK.LinkCertDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.MotC5N3

open MvPolynomial

/-- **The fraction field of `R ⧸ ker f` is the fraction field of the range of `f`** (a local copy
of the two-line argument of `Work.MotK.TGen.fractionRing_quotient_ker_algEquiv`, reproduced so that
this module does not depend on the `TGen` tree). -/
theorem fractionRing_quotient_ker_algEquiv {K R S : Type} [Field K] [CommRing R] [Algebra K R]
    [CommRing S] [IsDomain S] [Algebra K S] (f : R →ₐ[K] S) :
    Nonempty (FractionRing (R ⧸ RingHom.ker f) ≃ₐ[K] FractionRing f.range) := by
  have i : (R ⧸ RingHom.ker f) ≃ₐ[K] ↥f.range :=
    (AlgHom.ker_rangeRestrict f).symm ▸
      Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective f)
  exact ⟨IsFractionRing.algEquivOfAlgEquiv i⟩

/-- **The `fwVecAS2 · 0` junk conjunct of the generic AS census** (the conjunct `hFw`): every
height-one prime of `K[Fin 3]` containing the forward chart denominator
`fwVecAS2 (aK K D) (bK K D) g 0` is a junk class (`Work.MotV.JunkClass K x`).

Fork of `Work.MotV5.ASLocal.JunkFwVec0` (WP5, LK-3 of `MOTIVIC_CHAR5_N3_LEAD.md` §6, 277 lines),
whose base field is `RatFunc 𝕜`, whose coordinates are `Work.MotAS.aK D`, `Work.MotAS.bK D` and
whose class is `Work.MotV.fAS 𝕜`.  Here `K` is an arbitrary `𝕜`-algebra field of characteristic `5`,
the class is an arbitrary `g ∉ ℘(K)`, the coordinates are `Work.MotC5N3.aK K D`,
`Work.MotC5N3.bK K D` (`Submission/Work/MotC5N3/AK.lean`) and the twist field is
`Work.MotC5N3.twistFieldAS D g`.

Route: fork the module chain `Submission/Work/MotV5/ASLocal/JunkFwVec0.lean`,
`Submission/Work/MotV5/ASLocal/azContent.lean`, `Submission/Work/MotV5/ASLocal/azPrimeFwVec0.lean`,
`Submission/Work/MotAS/AzContent/*` and `Submission/Work/MotAS/AzDisc/*` into namespace
`Work.MotC5N3`, replacing `RatFunc 𝕜` by `K`, `Work.MotV.fAS 𝕜` by `g`, `Work.MotAS.aK D`,
`Work.MotAS.bK D` by `Work.MotC5N3.aK K D`, `Work.MotC5N3.bK K D`, and `Work.MotAS.twistFieldAS` by
`Work.MotC5N3.twistFieldAS`.  The polynomial engine is already generic in `(a b g : K)` (for
instance `azTheta_fwVecAS2`, `azFracRange`, `azKerHeight`, `fwVecAS2_zero_ne_zero_gen`,
`azDisc_not_square` all take free coordinates; the closing step is the generic
`Work.MotK.junkClass_of_resF_ratFunc_ratFunc`), so the work is wrapper-level; the source only uses
`g ≠ 0` (which `hg` gives by `u = 0`).  `Submission/Work/MotC5N3/port.py` performs the textual port.

Deliverable: namespace `Work.MotC5N3`, file `Submission/Work/MotC5N3/JunkFwVec0.lean` (helpers in
sibling files), sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`). -/
-- Proof route of this file (the docstring above is the original assignment text, kept verbatim):
-- * `f̂₀ = fwVecAS2 (aK K D) (bK K D) g 0` is *prime* in `K[x₀,x₁,x₂]`, by the generic
--   `Work.MotC5N3.azPrimeFwVec0` (`Submission/Work/MotC5N3/AzPrime.lean`, itself resting on the two
--   forked engines `Work.MotC5N3.azContent` and `Work.MotC5N3.azDisc_not_square`);
-- * the kernel of the chart parametrisation `θ = Work.MotAS.azTheta (aK K D) (bK K D) g` has height
--   one (`Work.MotAS.azKerHeight`) and contains `f̂₀` (`Work.MotAS.azTheta_fwVecAS2`), so it equals
--   `(f̂₀)` (`Work.MotK.CensusPrime.eq_span_of_height_one`), as does any height-one prime `x`
--   containing `f̂₀`;
-- * the fraction field of the residue field is `FractionRing θ.range ≃ K(u)(v)` by
--   `Work.MotAS.azFracRange`, i.e. the second iterate of `RatFunc`, which is junk
--   (`Work.MotK.JunkClass_of_resF_ratFunc_ratFunc`, with `GeomRuled_ratFunc_self`).
theorem JunkFwVec0 (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.fwVecAS2 (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g 0 ∈ x.asIdeal →
        Work.MotV.JunkClass K x := by
  intro x hcoh hmem
  -- the non-degeneracy of the Klein parameters, inherited from `ASGood D`
  have ha : aK K D ≠ 0 := aK_ne_zero D hD
  have hb : bK K D ≠ 0 := bK_ne_zero D hD
  have hab : aK K D * bK K D ≠ 0 := mul_ne_zero ha hb
  have hA : Work.MotAS.azA (aK K D) (bK K D) ≠ 0 := by
    simpa only [Work.MotAS.azA] using aK_sq_sub_ne D hD
  -- `g ∉ ℘(K)` in particular gives `g ≠ 0` (take `u = 0`)
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hg ⟨0, by ring⟩
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h5P : (5 : MvPolynomial (Fin 2) K) = 0 := CharP.cast_eq_zero _ 5
  -- the AS link identity `P^AS ∘ R^AS = s'·id` on the parametrising plane
  have hI2 : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (MvPolynomial.C (aK K D)) (MvPolynomial.C (bK K D))
          (MvPolynomial.C g)
          (Work.MotAS.kleinRAS (MvPolynomial.C (aK K D)) (MvPolynomial.C (bK K D))
            (MvPolynomial.C g) (Work.MotAS.azP K)) k
        = Work.MotAS.kleinSecDualAS (MvPolynomial.C (aK K D)) (MvPolynomial.C (bK K D))
            (MvPolynomial.C g) (Work.MotAS.azP K) * Work.MotAS.azP K k := by
    intro k
    have h := congrFun (Work.MotAS.kleinPAS_kleinRAS_azPlane (R := MvPolynomial (Fin 2) K) h5P
      (MvPolynomial.C (aK K D)) (MvPolynomial.C (bK K D)) (MvPolynomial.C g)
      (MvPolynomial.X 0) (MvPolynomial.X 1)) k
    simpa only [Work.MotAS.azP, Work.MotAS.azPlane] using h
  -- the parametrisation facts
  obtain ⟨h0, h3nz, h1, h2⟩ :=
    Work.MotAS.azTheta_fwVecAS2 (aK K D) (bK K D) g h5 ha hb hg0
      (aK_sq_sub_ne D hD) hI2
  obtain ⟨e⟩ := Work.MotAS.azFracRange (aK K D) (bK K D) g h3nz h1 h2
  have hkerht : (RingHom.ker (Work.MotAS.azTheta (aK K D) (bK K D) g)).height = 1 :=
    Work.MotAS.azKerHeight (aK K D) (bK K D) g h3nz h1 h2
  -- the chart denominator is a prime element, so every height-one prime above it is principal
  have hprime : Prime (Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0) :=
    azPrimeFwVec0 K (aK K D) (bK K D) g hA hab hg0
  have hf0ne : Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0 ≠ 0 := hprime.ne_zero
  have hspan : (Ideal.span {Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0} :
      Ideal (MvPolynomial (Fin 3) K)).IsPrime :=
    (Ideal.span_singleton_prime hf0ne).mpr hprime
  have hht : (Ideal.span {Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0} :
      Ideal (MvPolynomial (Fin 3) K)).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hf0ne) hprime.not_isUnit
  -- the kernel of the parametrisation is the span of the chart denominator
  have hf0mem : Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0 ∈
      RingHom.ker (Work.MotAS.azTheta (aK K D) (bK K D) g) := by
    rw [RingHom.mem_ker]
    exact h0
  haveI : (RingHom.ker (Work.MotAS.azTheta (aK K D) (bK K D) g)).IsPrime :=
    RingHom.ker_isPrime _
  have hker : RingHom.ker (Work.MotAS.azTheta (aK K D) (bK K D) g)
      = Ideal.span {Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0} :=
    Work.MotK.CensusPrime.eq_span_of_height_one _ hspan hht _
      hkerht hf0mem
  -- the residue field of that prime is `K(u,v)`
  have key : Nonempty (Work.MotV.resF K
      (⟨Ideal.span {Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0}, hspan⟩ :
        Work.MotA.polySpec K 3) ≃ₐ[K] RatFunc (RatFunc K)) := by
    obtain ⟨e1⟩ := fractionRing_quotient_ker_algEquiv (K := K)
      (Work.MotAS.azTheta (aK K D) (bK K D) g)
    rw [hker] at e1
    exact ⟨e1.trans e⟩
  -- every height-one prime containing `f̂₀` *is* that prime
  have hx : x.asIdeal = Ideal.span {Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0} := by
    haveI : x.asIdeal.IsPrime := x.2
    have hxht : x.asIdeal.height = 1 := by
      rw [AlgebraicGeometry.idealHeight_eq_coheight
        (CommRingCat.of (MvPolynomial (Fin 3) K)) x]
      exact hcoh
    exact Work.MotK.CensusPrime.eq_span_of_height_one _ hspan hht x.asIdeal hxht hmem
  rw [show x = (⟨Ideal.span {Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0}, hspan⟩ :
      Work.MotA.polySpec K 3) from PrimeSpectrum.ext hx]
  exact Work.MotK.JunkClass_of_resF_ratFunc_ratFunc K _ key

end Work.MotC5N3
