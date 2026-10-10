import Mathlib
import Submission.Work.MotAS.CensusASGen
import Submission.Work.MotAS.CensusLinAS
import Submission.Work.MotAS.GdivASAssembly
import Submission.Work.MotK.CensusPrime.eq_span_of_height_one

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The AS chart, corrected: the target hyperplane is `{ẑ₄ = 0}`

`ChartDefs.lean` normalises the *target* chart map `π_p ∘ R^AS` at the chart vector
`chart3 = (0, X₀, X₁, X₂, 1)`.  That is the correct chart vector for the *source* (the source
hyperplane is `{v₀ = 0}`, where `π_p` lands), but **not** for the target: the twisted inverse map
`kleinPAS` satisfies `kleinPAS_i = -kleinQAS` at `i = 4` (the fourth AS Pfaffian *is* minus the
quadric), so `P^AS` maps the quadric `{q^AS = 0}` into the hyperplane `{ẑ₄ = 0}`.  Hence the target
chart vector must lie in `{ẑ₄ = 0}` — the natural choice (mirroring `MotK`) is

`tchart = (1, X₀, X₁, X₂, 0)`

(the affine chart `{ẑ₄ = 0} ∩ {ẑ₀ = 1}` of the target hyperplane), while the source chart vector
stays `chart3 = (0, X₀, X₁, X₂, 1)` (the chart `{v₀ = 0} ∩ {v₄ = 1}`).

With the two chart vectors distinguished, the chart isomorphism argument of
`MotK/TGen/{ChartDefs,ChartMaps,ChartIso}` transposes verbatim:

* `Phi0 = aeval psiG` with `psiG_j = bwVecAS2 (j+1) / bwVecAS2 4` is the pullback of the inverse
  map `χ = π_p ∘ R^AS` (the source point `χ(tchart)` has `v₀ = 0`, normalised by `v₄ = 1`);
* `Psi0 = aeval phiF` with `phiF_j = fwVecAS2 (j+1) / fwVecAS2 0` is the pullback of the forward
  map `f = P^AS ∘ Stereo^AS` (the image `f(chart3)` has `ẑ₄ = 0`, normalised by `ẑ₀ = 1`);
* the two divisors are therefore `FdivAS2 = GambAS2 · fwVecAS2 0 = linAS2 · sAS2 · fwVecAS2 0`
  and `GdivAS2 = FambAS2 · bwVecAS2 4 = cubAS2 · sdualAS2 · bwVecAS2 4`.

Where `ChartDefs`' factors survive unchanged (`fwVecAS`, `linAS`, `sAS` are evaluated at the source
chart vector), the target-side ones (`bwVecAS`, `FambAS`, `cubAS`, `sdualAS`, `GdivAS`) are
re-pointed at `tchart`; this is the same correction flagged in the `WARNING` of `ChartDefs.lean`,
with the additional observation that the *index* used for the source normalisation is `0` (not `4`).

## Contents

* the corrected chart data `tchart`, `fwVecAS2`, `bwVecAS2`, `GambAS2`, `FambAS2`, `linAS2`, `sAS2`,
  `cubAS2`, `sdualAS2`, `FdivAS2`, `GdivAS2`;
* the corrected census `CensusAS2` and the bridge `linkCertAS_of_censusAS2`, obtained from the
  certified `Work.MotV.LinkCert` assembly of `CensusASGen.lean` by changing only the two divisors.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Work.MotAS

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-! ## The corrected chart data -/

/-- **The target chart vector** of the AS link: `(1, X₀, X₁, X₂, 0)`, the affine chart
`{ẑ₄ = 0} ∩ {ẑ₀ = 1}` of the target hyperplane. -/
noncomputable def tchart (K : Type*) [CommRing K] : Fin 5 → MvPolynomial (Fin 3) K :=
  ![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0]

/-- **The stereographic point of the AS chart**, normalised so that its `0`-th coordinate is `1`:
`p = e₀ = (1, 0, 0, 0, 0)`.  The point is the same projective point as `MotAS.pAS = 288 • e₀`
(`kleinQAS_stereoPt` uses only the projective point), but the *vector* matters: the projection
`kleinTwPi p x = x - x 0 • p` is the projection of `ℙ⁴` onto the source chart `{v₀ = 0}` only when
`p₀ = 1` (`π_p(x)₀ = x₀(1 - p₀)`), which is exactly what makes the two chart maps mutually
inverse.  This is the AS analogue of `MotK.kleinPointT a b h = (1,0,1,b/(ah),0)`, whose `0`-th
coordinate is `1`. -/
noncomputable def pAS0 (K : Type*) [CommRing K] : Fin 5 → MvPolynomial (Fin 3) K :=
  ![1, 0, 0, 0, 0]

@[simp] theorem pAS0_zero {K : Type*} [CommRing K] : pAS0 K 0 = 1 := rfl
@[simp] theorem pAS0_four {K : Type*} [CommRing K] : pAS0 K 4 = 0 := rfl

@[simp] theorem tchart_zero {K : Type*} [CommRing K] : tchart K 0 = 1 := rfl
@[simp] theorem tchart_one {K : Type*} [CommRing K] : tchart K 1 = MvPolynomial.X 0 := rfl
@[simp] theorem tchart_two {K : Type*} [CommRing K] : tchart K 2 = MvPolynomial.X 1 := rfl
@[simp] theorem tchart_three {K : Type*} [CommRing K] : tchart K 3 = MvPolynomial.X 2 := rfl
@[simp] theorem tchart_four {K : Type*} [CommRing K] : tchart K 4 = 0 := rfl

/-- **The forward chart map of the AS link**, evaluated at the source chart vector `chart3`:
the image point `P^AS ∘ y^AS(p, chart3)` in AS coordinates. -/
noncomputable def fwVecAS2 {K : Type*} [CommRing K] (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K) (Work.MotK.chart3 K))

/-- **The inverse chart map of the AS link**, evaluated at the target chart vector `tchart`:
the source point `π_p ∘ R^AS(tchart)`. -/
noncomputable def bwVecAS2 {K : Type*} [CommRing K] (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  Work.MotK.kleinTwPi (pAS0 K)
    (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K))

/-- The source equation at the source chart vector: `linAS2 · sAS2`. -/
noncomputable def GambAS2 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  kleinFhomAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (pAS0 K)
    (Work.MotK.chart3 K)

/-- The target equation at the target chart vector: `cubAS2 · sdualAS2`. -/
noncomputable def FambAS2 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  kleinGhomAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (pAS0 K) (tchart K)

/-- The polar factor `b^AS(p, chart3)` of the source equation (a *unit* for the stereographic point
`p = pAS`, cf. `MotAS.linAS_eq_const`). -/
noncomputable def linAS2 {K : Type*} [CommRing K] (a b : K) : MvPolynomial (Fin 3) K :=
  kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K) (Work.MotK.chart3 K)

/-- The source ruling quintic `s^AS(y^AS(p, chart3))`. -/
noncomputable def sAS2 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K) (Work.MotK.chart3 K))

/-- The polar factor `b^AS(p, R^AS(tchart))` of the target equation. -/
noncomputable def cubAS2 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K)
    (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K))

/-- The target ruling quintic `s'^AS(tchart)`. -/
noncomputable def sdualAS2 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K)

/-- The source equation factors through the polar factor and the source ruling quintic. -/
theorem GambAS2_eq {K : Type*} [CommRing K] (a b g : K) :
    GambAS2 a b g = linAS2 a b * sAS2 a b g := rfl

/-- The target equation factors through the polar factor and the target ruling quintic. -/
theorem FambAS2_eq {K : Type*} [CommRing K] (a b g : K) :
    FambAS2 a b g = cubAS2 a b g * sdualAS2 a b g := rfl

/-- **The source divisor of the corrected AS chart**: the source equation times the denominator
`fwVecAS2 · 0` of the forward chart map. -/
noncomputable def FdivAS2 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  linAS2 a b * sAS2 a b g * fwVecAS2 a b g 0

/-- **The target divisor of the corrected AS chart**: the target equation times the denominator
`bwVecAS2 · 4` of the inverse chart map. -/
noncomputable def GdivAS2 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  cubAS2 a b g * sdualAS2 a b g * bwVecAS2 a b g 4

/-! ## The corrected census and the bridge -/

/-- **The census of the corrected AS chart.**  Same shape as `CensusAS_gen`, with the two divisors
of the corrected chart and the normalising components `0` (source) and `4` (target). -/
def CensusAS2 (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) : Prop :=
  ∃ (hpr : (Ideal.span {sdualAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜)} :
      Ideal (MvPolynomial (Fin 3) (RatFunc 𝕜))).IsPrime),
    Ideal.height (Ideal.span {sdualAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜)}) = 1 ∧
    Nonempty (Work.MotV.resF (RatFunc 𝕜)
        ⟨Ideal.span {sdualAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜)}, hpr⟩ ≃ₐ[RatFunc 𝕜]
      RatFunc ↥(twistFieldAS D (Work.MotV.fAS 𝕜))) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      sAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal →
    Nonempty (Work.MotV.resF (RatFunc 𝕜) x ≃ₐ[RatFunc 𝕜]
        RatFunc ↥(twistFieldAS D (2 • Work.MotV.fAS 𝕜))) ∨
      Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      linAS2 (aK D) (bK D) ∈ x.asIdeal → Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      cubAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      fwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 0 ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      bwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  FdivAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 ∧
  GdivAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 ∧
  Nonempty (Localization.Away (FdivAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜)) ≃ₐ[RatFunc 𝕜]
    Localization.Away (GdivAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜)))

/-- **The corrected census implies the certificate.** -/
theorem linkCertAS_of_censusAS2 (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (hc : CensusAS2 D hD) :
    Nonempty (Work.MotV.LinkCert (RatFunc 𝕜) ↥(twistFieldAS D (Work.MotV.fAS 𝕜))
      ↥(twistFieldAS D (2 • Work.MotV.fAS 𝕜))) := by
  obtain ⟨hpr, hht, hres, hS, hLin, hCub, hFw, hBw, hFne, hGne, hΦ⟩ := hc
  have hcoh : ∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      Ideal.height x.asIdeal = 1 := fun x hx =>
    (AlgebraicGeometry.idealHeight_eq_coheight
      (CommRingCat.of (MvPolynomial (Fin 3) (RatFunc 𝕜))) x).trans hx
  let zP : Work.MotA.polySpec (RatFunc 𝕜) 3 :=
    ⟨Ideal.span {sdualAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜)}, hpr⟩
  have hzP_ht : Order.coheight zP = 1 := by
    rw [← AlgebraicGeometry.idealHeight_eq_coheight
      (CommRingCat.of (MvPolynomial (Fin 3) (RatFunc 𝕜))) zP]
    exact hht
  refine ⟨{ F := FdivAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜)
            G := GdivAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜)
            hF := hFne
            hG := hGne
            Φ := Classical.choice hΦ
            zP := zP
            zP_ht := hzP_ht
            zP_mem := ?_
            zP_res := hres
            G_other := ?_
            F_all := ?_ }⟩
  · have hmul : cubAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) * sdualAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜)
        * bwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 4
        ∈ Ideal.span {sdualAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜)} :=
      Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    exact hmul
  · intro x hcx hxG hxne
    haveI hxprime : x.asIdeal.IsPrime := x.2
    have h1 : cubAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) * sdualAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜)
        ∈ x.asIdeal ∨ bwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ∈ x.asIdeal :=
      hxprime.mem_or_mem hxG
    rcases h1 with hcs | hbw
    · have h2 : cubAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal
          ∨ sdualAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal :=
        hxprime.mem_or_mem hcs
      rcases h2 with hc | hs
      · exact hCub x hcx hc
      · exact absurd (PrimeSpectrum.ext
          (Work.MotK.CensusPrime.eq_span_of_height_one _ hpr hht x.asIdeal (hcoh x hcx) hs)) hxne
    · exact hBw x hcx hbw
  · intro x hcx hxF
    haveI hxprime : x.asIdeal.IsPrime := x.2
    have h1 : linAS2 (aK D) (bK D) * sAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal
        ∨ fwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 0 ∈ x.asIdeal :=
      hxprime.mem_or_mem hxF
    rcases h1 with hls | hfw
    · have h2 : linAS2 (aK D) (bK D) ∈ x.asIdeal
          ∨ sAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal :=
        hxprime.mem_or_mem hls
      rcases h2 with hl | hs
      · exact Or.inr (hLin x hcx hl)
      · exact hS x hcx hs
    · exact Or.inr (hFw x hcx hfw)

end Work.MotAS
