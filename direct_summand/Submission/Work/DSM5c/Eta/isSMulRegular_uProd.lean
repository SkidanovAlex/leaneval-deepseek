import Mathlib
import Submission.Work.DSM5c.Eta.Setup
import Submission.Work.DSM5c.Eta.gLoc_fracU
import Submission.Work.DSM5c.Charts

set_option maxHeartbeats 1600000

namespace Work.DSM5c.Eta

/-!
# DSM5c / Eta — `∏_{i ∈ S} u_i` is a nonzerodivisor in the perfected tilted chart `R_S`

The perfected tilted chart `R_S = Work.DSM5c.tiltChart Q t tr … S` is, by construction
(`DSMap.Mix2.perfChartRing`), the `PreTilt W p`-subalgebra

  `R_S ⊆ (W♭)_{t_S}`  (`t_S = DSMap.Mix2.tS (chartTiltGen Q t tr … j₀ e) S`),

of the localisation in which the chart denominator `t_S` is inverted.  The generators
`Work.DSM5c.Eta.uEl S i = algebraMap (PreTilt W p) R_S (chartTiltGen … i)` therefore multiply to the
image of `t_S` itself:

  `∏_{i ∈ S} u_i = algebraMap (PreTilt W p) R_S (t_S)`,

whose image in the ambient ring `(W♭)_{t_S}` is `algebraMap (PreTilt W p) (W♭)_{t_S} (t_S)`, a *unit*
of `(W♭)_{t_S}` (`IsLocalization.Away.algebraMap_isUnit`).  Since `R_S → (W♭)_{t_S}` is injective,
"nonzerodivisor in the ambient ring" implies "nonzerodivisor in `R_S`", which is the statement.

This is the regularity input for the "generator dictionary" of the chart map `η` of the M5c node
(used together with `Work.DSM5c.Eta.gLoc_fracU` and `Work.DSM5c.Eta.vS_eq_teich_prod`).
-/

theorem isSMulRegular_uProd {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k)
    (j₀ : ι) (e : ℕ) (S : Finset ι) :
    ∀ z : ↥(Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S),
      (∏ i ∈ S, Work.DSM5c.Eta.uEl Q t tr htr0 htr j₀ e S i) * z = 0 → z = 0 := by
  intro z hz
  -- The ambient ring in which the chart sits: the localisation `(W♭)_{t_S}`.
  -- The value of a generator `u_i = uEl S i` in the ambient ring is `algebraMap (φ (u i))`.
  have hcoe : ∀ i, (((Work.DSM5c.Eta.uEl Q t tr htr0 htr j₀ e S i) :
        ↥(Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S)) :
        Localization.Away (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S))
      = algebraMap (PreTilt W p)
          (Localization.Away (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S))
          (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e i) := by
    intro i
    rw [Work.DSM5c.Eta.uEl]
    exact Subalgebra.coe_algebraMap _ _
  -- Hence the product `∏_{i ∈ S} u_i` is the image of `t_S = ∏_{i ∈ S} u_i` in the ambient ring.
  have hprod : (((∏ i ∈ S, Work.DSM5c.Eta.uEl Q t tr htr0 htr j₀ e S i) :
        ↥(Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S)) :
        Localization.Away (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S))
      = algebraMap (PreTilt W p)
          (Localization.Away (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S))
          (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S) := by
    change (Subalgebra.val (Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S))
        (∏ i ∈ S, Work.DSM5c.Eta.uEl Q t tr htr0 htr j₀ e S i)
      = algebraMap (PreTilt W p)
          (Localization.Away (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S))
          (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S)
    rw [map_prod (Subalgebra.val (Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S))]
    trans ∏ i ∈ S, algebraMap (PreTilt W p)
        (Localization.Away (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S))
        (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e i)
    · exact Finset.prod_congr rfl (fun i _ => hcoe i)
    · rw [← map_prod (algebraMap (PreTilt W p)
        (Localization.Away (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S)))]
      rfl
  -- `t_S` is inverted in the ambient localisation, so the product is a unit there.
  have hunit : IsUnit (((∏ i ∈ S, Work.DSM5c.Eta.uEl Q t tr htr0 htr j₀ e S i) :
        ↥(Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S)) :
        Localization.Away (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S)) := by
    rw [hprod]
    exact IsLocalization.Away.algebraMap_isUnit _
  -- Move the hypothesis into the ambient ring, where the product is invertible.
  have hz' : (((∏ i ∈ S, Work.DSM5c.Eta.uEl Q t tr htr0 htr j₀ e S i) :
        ↥(Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S)) :
        Localization.Away (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S))
      * (z : Localization.Away
          (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S)) = 0 := by
    have h := congrArg (fun w : ↥(Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S) =>
      (w : Localization.Away
        (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S))) hz
    simpa [Subalgebra.coe_mul] using h
  -- So `z` vanishes in the ambient ring, hence in the subalgebra.
  have hzA : (z : Localization.Away
      (DSMap.Mix2.tS (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) S)) = 0 :=
    (IsUnit.mul_right_eq_zero hunit).mp hz'
  exact Subtype.ext (by simpa using hzA)

end Work.DSM5c.Eta
