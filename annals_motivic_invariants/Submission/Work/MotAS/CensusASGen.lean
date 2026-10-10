import Mathlib
import Submission.Work.MotAS.CensusASFalse
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The repaired AS chart interface: the census, parameterised by the normalising component

`CensusAS` (`Submission/Work/MotAS/linkCertAS.lean`) is **false** because its source divisor
`FdivAS = linAS · sAS · fwVecAS 4` is the zero polynomial
(`MotAS.FdivAS_eq_zero`, `MotAS.not_censusAS`).  This file does three things.

## 1. The chart-parametrisation lemma that localises the obstruction

The fourth coordinate of the forward chart map is, for **every** stereographic datum `(p, v)` on the
quadric,

  `kleinPAS a b g (kleinStereoAS a b p v) 4 = -(kleinQAS a b v)^2 · kleinQAS a b p`

(`MotAS.kleinPAS_kleinStereoAS_four`), because `kleinPAS · 4 = -kleinQAS`
(`MotAS.kleinPAS_four_eq_neg`) and `kleinQAS (kleinStereoAS a b p v) = kleinQAS v ^ 2 * kleinQAS p`
(`Work.MotV5.ASChart.kleinQAS_stereoAS`, proved).  So as soon as the stereographic point `p` lies on
the quadric — which the link composition identities *require* — the fourth coordinate of the forward
chart map vanishes identically, and the affine chart `(f̂₁/f̂₄, f̂₂/f̂₄, f̂₃/f̂₄)` has no meaning.

Crucially this is **not** an artefact of the particular point `pAS = 288 • e₀` (the "open issue" in
the `ChartDefs.lean` warning): the vanishing holds for every point of the quadric.  The obstruction
is therefore attached to the *component* `4`, i.e. to the choice of normalising coordinate of the
affine chart `V₀ = 0`, not to the choice of stereographic point.  (In the split/T model there is no
such collapse: there `kleinTwP · 4 ≠ -kleinTwQ`, which is why `TGen` can normalise by `f̂₄`.)

## 2. The repair: parameterise the census by the normalising component

`MotAS.FdivAS_gen a b g i = linAS a b * sAS a b g * fwVecAS a b g i` and `MotAS.CensusAS_gen D hD i`
is the census of `linkCertAS.lean` with `fwVecAS · 4` replaced by `fwVecAS · i`.  The bridge
`MotAS.linkCertAS_of_censusAS_gen` then produces the certificate from `CensusAS_gen D hD i`.

`CensusAS_gen D hD 4` is *definitionally* `CensusAS D hD` (hence false, `MotAS.not_censusAS`), so
the parameterisation is faithful.  A usable index `i` must be one for which the corresponding clause
`fwVecAS · i ∉ x` holds — clause 5 of `CensusAS_gen` states exactly that — and the chart isomorphism
clause must be proved for that index.  Deciding *which* `i` works is the remaining geometric
question; the normalising component cannot be `4`, and the natural candidate is `3`.

## 3. What is *not* claimed here

No index is asserted to work, and no clause is proved: this file only isolates the choice as a
parameter and supplies the bridge.  The `cubAS` / `bwVecAS 4` (target) side is unaffected by the
above: `cubAS = -576 (aK² − aK bK − bK²) · (kleinRAS (chart3))₄` (`MotAS.cubAS_eq`) is a non-zero
cubic times a unit, and `bwVecAS · 4 = (kleinRAS (chart3))₄` because `pAS` is supported in
coordinate `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace Work.MotAS

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- **The chart-parametrisation lemma.**  The fourth coordinate of the AS forward chart map is
`-q(v)² q(p)`, for every stereographic datum.  In particular it vanishes identically as soon as the
stereographic point `p` lies on the quadric `q = 0` — which is exactly the hypothesis under which the
link composition identities hold. -/
theorem kleinPAS_kleinStereoAS_four {K : Type*} [CommRing K] (a b g : K) (p v : Fin 5 → K) :
    kleinPAS a b g (kleinStereoAS a b p v) 4 = -(kleinQAS a b v) ^ 2 * kleinQAS a b p := by
  rw [kleinPAS_four_eq_neg, Work.MotV5.ASChart.kleinQAS_stereoAS]
  first | refl_ring1 | ring

/-- The source divisor of the certificate, normalised by the `i`-th coordinate of the forward chart
map: `FdivAS_gen a b g i = linAS a b * sAS a b g * fwVecAS a b g i`. -/
noncomputable def FdivAS_gen {K : Type*} [Field K] (a b g : K) (i : Fin 5) :
    MvPolynomial (Fin 3) K :=
  linAS a b * sAS a b g * fwVecAS a b g i

/-- `FdivAS_gen · 4` is the (degenerate) `FdivAS` of `ChartDefs.lean`. -/
theorem FdivAS_gen_four {K : Type*} [Field K] (a b g : K) :
    FdivAS_gen a b g 4 = FdivAS a b g := rfl

/-- **The census, parameterised by the normalising component `i`.**  It is the census of
`linkCertAS.lean` with the source denominator `fwVecAS · 4` replaced everywhere by `fwVecAS · i`
(so `CensusAS_gen D hD 4` is `CensusAS D hD`). -/
def CensusAS_gen (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (i : Fin 5) : Prop :=
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
      fwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) i ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      bwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  FdivAS_gen (aK D) (bK D) (Work.MotV.fAS 𝕜) i ≠ 0 ∧
  GdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 ∧
  Nonempty (Localization.Away (FdivAS_gen (aK D) (bK D) (Work.MotV.fAS 𝕜) i) ≃ₐ[RatFunc 𝕜]
    Localization.Away (GdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜)))

/-- `CensusAS_gen D hD 4` is the (refuted) census of `linkCertAS.lean`. -/
theorem censusAS_gen_four_eq (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    CensusAS_gen D hD 4 = CensusAS D hD := rfl

/-- **The certificate from the `i`-parameterised census**: the AS analogue of
`Work.MotK.linkCertTGenInf_of_census`, with the source denominator `fwVecAS · i`. -/
theorem linkCertAS_of_censusAS_gen (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (i : Fin 5) (hc : CensusAS_gen D hD i) :
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
  refine ⟨{ F := FdivAS_gen (aK D) (bK D) (Work.MotV.fAS 𝕜) i
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
        ∨ fwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) i ∈ x.asIdeal :=
      hxprime.mem_or_mem hxF
    rcases h1 with hls | hfw
    · have h2 : linAS (aK D) (bK D) ∈ x.asIdeal
          ∨ sAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal :=
        hxprime.mem_or_mem hls
      rcases h2 with hl | hs
      · exact Or.inr (hLin x hcx hl)
      · exact hS x hcx hs
    · exact Or.inr (hFw x hcx hfw)

/-- **The third component of the AS forward chart map at the origin of the chart**: evaluating
`fwVecAS a b g 3` at `X₀ = X₁ = X₂ = 0` gives `331776 · g · (a² − ab − b²)³`.  Hence — unlike the
fourth component, which vanishes identically (`MotAS.fwVecAS_four_eq_zero`) — the third component is
a non-zero polynomial as soon as `g ≠ 0` and `a² − ab − b² ≠ 0`, so `i = 3` is a legitimate
normalising coordinate for the repaired chart `CensusAS_gen`.

(For comparison, the same evaluation at the origin gives, computed symbolically,
`fwVecAS · 0 = -82944·ab(a²-ab-b²)(4a²-ab-4b²)` and
`fwVecAS · 2 = 331776·ab(a²+b²)(a²-ab-b²)`, both of which can vanish for admissible `(a,b)`; and
`fwVecAS · 4 = 0`.) -/
theorem aeval_zero_fwVecAS_three {K : Type*} [Field K] (a b g : K) :
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) (fwVecAS a b g 3)
      = 331776 * g * (a ^ 2 - a * b - b ^ 2) ^ 3 := by
  have h : fwVecAS a b g 3
      = kleinPAS3 (C a) (C b) (C g)
          (kleinStereoAS (C a) (C b) (pAS K) (Work.MotK.chart3 K)) := rfl
  rw [h]
  simp only [kleinPAS3, kleinStereoAS, kleinBilinAS, kleinQAS, pAS, Work.MotK.chart3,
    Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]
  simp
  have hcc : MvPolynomial.constantCoeff (2 : MvPolynomial (Fin 3) K) = (2 : K) :=
    map_natCast MvPolynomial.constantCoeff 2
  simp only [hcc]
  first | refl_ring1 | ring

end Work.MotAS
