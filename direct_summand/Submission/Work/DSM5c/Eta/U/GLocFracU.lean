import Mathlib
import Submission.Work.DSM5c.Eta.U.Setup
import Submission.Work.DSM5c.Eta.U.SharpChartTiltGen
import Submission.Work.DSM5c.Eta.U.TeichAlgebraMap

universe a

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c.Eta.U

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

/-!
# DSM5c / Eta — the generator dictionary of the chart map `η`

This file proves `Work.DSM5c.Eta.U.gLoc_fracU`, the "generator dictionary" of the chart map `η`
of the M5c node: the localisation map `gLoc : W_{t_S} →+* D_S[1/v_S]` sends the honest chart
fraction `t_j/t_i ∈ W_{t_S}` (`i ∈ S`) to the image under `locD` of the Teichmüller lift of the
tilted chart fraction `u_j/u_i ∈ R_S`.

## Strategy

Both sides are computed by showing that each is characterised by the *same* linear equation with
the (invertible) denominator `t_i`:

* on the honest side, `fracT t S i j hi * algebraMap W _ (t i) = algebraMap W _ (t j)`
  (`Work.DSM5c.Eta.U.fracT_spec`), and `gLoc` is the `IsLocalization.Away.lift` of `algebraMap W _`
  (`Work.DSM5c.Eta.U.gLoc_algebraMap`), whose value on `algebraMap W _ w` is
  `locD (untiltOf.algebraMap hθ φ_S w)`;
* on the tilted side, the chart fraction identity `fracU i j * φ(u i) = φ(u j)` in `R_S`
  (`fracU_mul_uEl`), multiplicativity of the Teichmüller map (`teich_mul`), and
  `teich (φ (u k)) = untiltOf.algebraMap hθ φ_S (t k)` (`teich_uEl`), obtained from
  `Work.DSM5c.Eta.U.teich_algebraMap` (the `♯` of a Teichmüller lift is the `♯`-element) together
  with `Work.DSM5c.Eta.U.sharp_chartTiltGen` (`♯(u k) = t k`).
-/

section Setup

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]
  (Q : PerfectoidData p W)
  (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
  (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
  (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)

/-- **The tilted chart generator inside the perfected tilted chart**: the element of
`R_S = tiltChart Q t tr … S` which is the image of `chartTiltGen Q t tr … k ∈ W♭` under the
`W♭`-algebra structure `φ_S = chartPhi … S` of the chart.  By `sharp_chartTiltGen` its `♯` is
`t k`, and it is the numerator/denominator of the chart fraction `fracU`. -/
noncomputable def uEl (S : Finset ι) (k : ι) : tiltChart' Q t tr htr0 htr j₀ e S :=
  algebraMap (PreTilt W p) (tiltChart Q t tr htr0 htr j₀ e S) (chartTiltGen Q t tr htr0 htr j₀ e k)

/-- **The defining property of `gLoc` on the image of `W`**: `Work.DSM5c.Eta.U.gLoc` is the
`IsLocalization.Away.lift` of `algebraMap W _` along `W → W_{t_S}`, so on `algebraMap W _ w` it is
the image of `w` under the `W`-algebra structure of `D_S[1/v_S]`, i.e. the `locD`-image of the
`W`-algebra structure of `D_S`. -/
theorem gLoc_algebraMap (S : Finset ι) (w : W) :
    gLoc Q hθ t tr htr0 htr j₀ e S (algebraMap W (Localization.Away (tS t S)) w)
      = locD Q hθ t tr htr0 htr j₀ e S
          (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) w) := by
  letI := DSlocAlg Q hθ t tr htr0 htr j₀ e S
  rw [show gLoc Q hθ t tr htr0 htr j₀ e S
        = IsLocalization.Away.lift (tS t S) (g := algebraMap W _) _ from rfl]
  rw [IsLocalization.Away.lift_eq]
  rfl

/-- **Multiplicativity of the Teichmüller map** `teich S` on the perfected tilted chart: the
Teichmüller lift is multiplicative and so is the quotient map `𝕎 R_S → D_S` defining the untilt. -/
theorem teich_mul (S : Finset ι) (x y : tiltChart' Q t tr htr0 htr j₀ e S) :
    teich Q t tr htr0 htr j₀ e S (x * y)
      = teich Q t tr htr0 htr j₀ e S x * teich Q t tr htr0 htr j₀ e S y := by
  simp only [teich]
  rw [map_mul (WittVector.teichmuller p), map_mul (untiltOf.mk (chartPhi Q t tr htr0 htr j₀ e S))]

/-- **The Teichmüller lift of a chart generator is the chart generator**: `teich (φ (u k))` is the
image in `D_S` of the honest generator `t k`.  This is `teich_algebraMap` (the `♯`-element of a
Teichmüller lift is the Teichmüller lift of the `♯`-element) applied to `u k = chartTiltGen … k`,
whose `♯` is `t k` by `sharp_chartTiltGen`. -/
theorem teich_uEl (hj₀ : t j₀ = Q.ϖ 0 ^ e) (S : Finset ι) (k : ι) :
    teich Q t tr htr0 htr j₀ e S (uEl Q t tr htr0 htr j₀ e S k)
      = untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t k) := by
  rw [uEl]
  rw [show teich Q t tr htr0 htr j₀ e S
        (algebraMap (PreTilt W p) (tiltChart Q t tr htr0 htr j₀ e S)
          (chartTiltGen Q t tr htr0 htr j₀ e k))
      = untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S)
          (PreTilt.untilt (chartTiltGen Q t tr htr0 htr j₀ e k)) from
    teich_algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (chartTiltGen Q t tr htr0 htr j₀ e k)]
  rw [sharp_chartTiltGen Q t tr htr0 htr j₀ e hj₀ k]

/-- **The chart fraction identity**: `fracU i j · φ(u i) = φ(u j)` in the perfected tilted chart
`R_S`.  Both sides are elements of the chart, so it suffices to check it in the ambient localisation
`(W♭)_{t_S}`, where it is `(u j · (u i)⁻¹) · u i = u j`. -/
theorem fracU_mul_uEl (S : Finset ι) (i j : ι) (hi : i ∈ S) :
    fracU Q t tr htr0 htr j₀ e S i j hi * uEl Q t tr htr0 htr j₀ e S i
      = uEl Q t tr htr0 htr j₀ e S j := by
  have hUi : ((unitU Q t tr htr0 htr j₀ e S i hi :
      (Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) S))ˣ) :
      Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) S)) =
      algebraMap (PreTilt W p) _ (chartTiltGen Q t tr htr0 htr j₀ e i) :=
    unitU_spec Q t tr htr0 htr j₀ e S i hi
  apply Subtype.ext
  change (algebraMap (PreTilt W p) (Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) S))
        (chartTiltGen Q t tr htr0 htr j₀ e j) * ↑((unitU Q t tr htr0 htr j₀ e S i hi)⁻¹)) *
      algebraMap (PreTilt W p) (Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) S))
        (chartTiltGen Q t tr htr0 htr j₀ e i)
      = algebraMap (PreTilt W p) (Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) S))
        (chartTiltGen Q t tr htr0 htr j₀ e j)
  rw [mul_assoc, ← hUi, Units.inv_mul, mul_one]

/-- **The honest side of the dictionary**: `gLoc (t_j/t_i) · locD(♯ t_i) = locD(♯ t_j)`, i.e. the
image under `gLoc` of the chart fraction `t_j/t_i` is "the fraction with denominator `♯ t i`". -/
theorem gLoc_fracT_mul (S : Finset ι) {i : ι} (hi : i ∈ S) (j : ι) :
    gLoc Q hθ t tr htr0 htr j₀ e S (fracT t S i j hi) *
      locD Q hθ t tr htr0 htr j₀ e S
        (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t i))
    = locD Q hθ t tr htr0 htr j₀ e S
        (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t j)) := by
  have h := congrArg (gLoc Q hθ t tr htr0 htr j₀ e S) (fracT_spec t S i j hi)
  rw [map_mul] at h
  rw [gLoc_algebraMap, gLoc_algebraMap] at h
  exact h

/-- **The tilted side of the dictionary**: `locD(teich (u_j/u_i)) · locD(♯ t_i) = locD(♯ t_j)`,
i.e. the `locD`-image of the Teichmüller lift of the tilted chart fraction is again "the fraction
with denominator `♯ t i`".  This is multiplicativity of `teich` (`teich_mul`) applied to the chart
fraction identity `fracU_mul_uEl`, together with `teich_uEl`. -/
theorem locD_teich_fracU_mul (hj₀ : t j₀ = Q.ϖ 0 ^ e) (S : Finset ι) {i : ι} (hi : i ∈ S) (j : ι) :
    locD Q hθ t tr htr0 htr j₀ e S
        (teich Q t tr htr0 htr j₀ e S (fracU Q t tr htr0 htr j₀ e S i j hi)) *
      locD Q hθ t tr htr0 htr j₀ e S
        (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t i))
    = locD Q hθ t tr htr0 htr j₀ e S
        (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t j)) := by
  have h := congrArg (locD Q hθ t tr htr0 htr j₀ e S)
    (congrArg (teich Q t tr htr0 htr j₀ e S)
      (fracU_mul_uEl Q t tr htr0 htr j₀ e S i j hi))
  rw [teich_mul, map_mul] at h
  rw [teich_uEl (hj₀ := hj₀) (k := i), teich_uEl (hj₀ := hj₀) (k := j)] at h
  exact h

/-- **The denominator `♯ t i` is invertible**: `v_S = ♯(t_S)` is a unit in `D_S[1/v_S]` by
construction of the localisation, and `♯ t i` divides `♯ t_S = ∏_{k ∈ S} ♯ t k`. -/
theorem isUnit_locD_t (S : Finset ι) {i : ι} (hi : i ∈ S) :
    IsUnit (locD Q hθ t tr htr0 htr j₀ e S
      (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t i))) := by
  have h1 : IsUnit (locD Q hθ t tr htr0 htr j₀ e S
      (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (tS t S))) :=
    IsLocalization.Away.algebraMap_isUnit (vS Q hθ t tr htr0 htr j₀ e S)
  exact isUnit_of_dvd_unit
    (map_dvd (locD Q hθ t tr htr0 htr j₀ e S)
      (map_dvd (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S))
        (Finset.dvd_prod_of_mem t hi))) h1

end Setup

/-- **The value of the localisation map `gLoc` on the chart generators.**

`Work.DSM5c.Eta.U.gLoc` is the `W`-algebra map `W_{t_S} →+* D_S[1/v_S]` obtained from
`IsLocalization.Away.lift` along `algebraMap W _`; on the honest chart fraction
`Work.DSM5c.Eta.U.fracT t S i j hi = t_j/t_i` (`i ∈ S`, any `j`) its value is the image under
`Work.DSM5c.Eta.U.locD` of the tilted Teichmüller fraction `Work.DSM5c.Eta.U.teich … (fracU …)`.

This is the "generator dictionary" of the chart map `η` of the M5c node.  It uses
`Work.DSM5c.Eta.U.teich_algebraMap` and `Work.DSM5c.Eta.U.sharp_chartTiltGen` (which, together with
the hypothesis `hj₀ : t j₀ = Q.ϖ 0 ^ e`, give `teich S (u j) = untiltOf.algebraMap hθ φ_S (t j)`
for every `j`), the multiplicativity of Teichmüller (`teich S y * teich S y' = teich S (y * y')`,
`teich S (u i / u i) = 1`), and the fact that `algebraMap W _ (t i)` is a unit of `W_{t_S}`
(`Work.DSM5c.Eta.U.unitT_spec`), whence both sides are "the fraction with denominator `t i`". -/
theorem gLoc_fracU {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = Q.ϖ 0 ^ e)
    (S : Finset ι) {i : ι} (hi : i ∈ S) (j : ι) :
    Work.DSM5c.Eta.U.gLoc Q hθ t tr htr0 htr j₀ e S (Work.DSM5c.Eta.U.fracT t S i j hi)
      = Work.DSM5c.Eta.U.locD Q hθ t tr htr0 htr j₀ e S
          (Work.DSM5c.Eta.U.teich Q t tr htr0 htr j₀ e S
            (Work.DSM5c.Eta.U.fracU Q t tr htr0 htr j₀ e S i j hi)) := by
  refine IsUnit.mul_right_cancel
    (isUnit_locD_t Q hθ t tr htr0 htr j₀ e S hi) ?_
  exact (gLoc_fracT_mul Q hθ t tr htr0 htr j₀ e S hi j).trans
    (locD_teich_fracU_mul Q hθ t tr htr0 htr j₀ e hj₀ S hi j).symm

end Work.DSM5c.Eta.U
