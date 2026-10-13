import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngAWeak.aeTruncAux
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the angular `σ`-masses on a radial box

The three quantities `AAA u`, `BBB u`, `GGG G` of `aeTruncAux` are the angular `σ`-masses
(`σ = sin(2θ)^{-η}`) of the slices of `∂_θθu`, `z²∂_zzu` and `G`.  The hypothesis `AeData α u G`
of the weak class contains the honest `ℋ⁰`-membership of exactly these three functions, i.e.
the `z`-integrability of `z ↦ (w z)² · (the slice mass)`.  Since on a box `[a,b]` with
`0 < a` the radial weight `w z = (1+z)²/z²` is bounded away from `0`, the mass itself is
integrable there.

The proof of the general statement is `integrableOn_sliceMass_of_HkMem` below; the level-`0`
`HkIntegrand` is a single weighted square
(`Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta`), so the mass-times-`w²`
is literally the `z`-marginal of `HkIntegrand α 0 f`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- **Integrability of the `σ`-weighted slice mass on a radial box.**  If the level-`0`
integrand of `f` has finite iterated integral (`HkMem α 0 f`), then on every box `[a,b]` with
`0 < a` the slice mass `z ↦ ∫_θ (f z θ)² sin(2θ)^{-η}` is integrable. -/
theorem integrableOn_sliceMass_of_HkMem {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 f) :
    ∀ a b : ℝ, 0 < a →
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Icc a b) := by
  intro a b ha
  -- The boxes `[a,b]` with `0 < a` lie in the half-line `Iz` on which `HkMem` gives the
  -- `z`-integrability of the `θ`-marginal of the level-`0` integrand.
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun z hz => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hz.1)
  have hbase : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ) (Set.Icc a b) :=
    hm.2.mono_set hsub
  -- On `Iθ` the level-`0` integrand is `(f z θ)² w(z)² σ θ`, so its `θ`-integral is
  -- `w(z)²` times the slice mass.
  have hpt : ∀ z ∈ Set.Icc a b,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
        = (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    intro z _
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
        rw [Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta α f z hθ]; ring)
    rw [h1, MeasureTheory.integral_const_mul]
  have h2 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Icc a b) :=
    hbase.congr_fun hpt measurableSet_Icc
  -- `z ↦ (w z)²` is continuous and nonvanishing on `[a,b]`, so its inverse is bounded there
  -- (indeed continuous), and multiplying restores the mass.
  have hcont : ContinuousOn (fun z : ℝ => ((Work.Spaces.w z) ^ 2)⁻¹) (Set.Icc a b) := by
    have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc a b) := by
      refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hz.1))
    refine (hw.pow 2).inv₀ (fun z hz => ?_)
    show Work.Spaces.w z ^ 2 ≠ 0
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    apply pow_ne_zero
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz0))
  have h3 : MeasureTheory.IntegrableOn
      (fun z => ((Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * ((Work.Spaces.w z) ^ 2)⁻¹) (Set.Icc a b) :=
    h2.mul_continuousOn hcont isCompact_Icc
  refine h3.congr_fun (fun z hz => ?_) measurableSet_Icc
  show ((Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      * ((Work.Spaces.w z) ^ 2)⁻¹
      = ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  have hwz : Work.Spaces.w z ≠ 0 := by
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz0))
  field_simp

/-- **Integrability of the three angular `σ`-masses on a radial box.**  Under the
almost-everywhere hypotheses `AeData α u G` of the weak level-`0` class, the slice masses of
`∂_θθu`, `z²∂_zzu` and `G` are integrable on every `[a,b]` with `0 < a`. -/
theorem aeBoxMem : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    ∀ a b : ℝ, 0 < a →
    MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngAWeak.AAA u) (Set.Icc a b)
      ∧ MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngAWeak.BBB u) (Set.Icc a b)
      ∧ MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngAWeak.GGG G) (Set.Icc a b) := by
  intro α u G h a b ha
  refine ⟨?_, ?_, ?_⟩
  · exact integrableOn_sliceMass_of_HkMem h.memAng2 a b ha
  · exact integrableOn_sliceMass_of_HkMem h.memRad2 a b ha
  · exact integrableOn_sliceMass_of_HkMem h.memG a b ha

end Work.FTS.EllipticEst.AngAWeak
