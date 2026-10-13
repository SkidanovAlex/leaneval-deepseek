import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngAWeak.aeTruncAux
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Honest.SelfAux.SliceDerivBound
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.sliceCSWeightedOpen
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slicewise mass bound `aeUMassBound` of the weak angular class

For a datum `(u, G)` of the almost-everywhere class `AeData α u G` (the weak class of the
level-`0` elliptic estimate, `H2W/Ae/Defs.lean`), the values of the solution `u` on a compact
radial interval `[a,b] ⊂ (0,∞)` are bounded by the *angular* `H²`-mass of the slice

  `AAA u z = ∫_θ (∂_θθ u(z,θ))² sin(2θ)^{-η} dθ`

of the same slice, up to a constant `K` (allowed to depend on `α`, `u`, `G`, `a`, `b`, but
not on `z ∈ [a,b]` or `θ ∈ Iθ`).

## Route

For a fixed `z ∈ [a,b]` the slice `θ ↦ u(z,·)` is `C^∞` on `(0,π/2)` and its second derivative
is square integrable against `σ = sin(2θ)^{-η}` (`HkMem α 0 (∂_θθu)` is a hypothesis of
`AeData`, and `HkIntegrand α 0 (∂_θθu) = w(z)² (∂_θθu)² σ` on `Iθ`).  Hence

* `∫_{Iθ} |∂_θθ u(z,·)| ≤ √(AAA u z) · √(∫_{Iθ} sin(2θ)^η)` (weighted Cauchy–Schwarz,
  `sliceCSWeightedOpen`);
* the fundamental theorem of calculus based at the interior point `π/4` bounds `u` and
  `∂_θ u` on the slice by their values at `π/4` plus that mass
  (`Endpt.psi_le_of_strip_HkMem`).

The values at `π/4` are bounded *uniformly in `z ∈ [a,b]`* because `z ↦ u(z,π/4)` and
`z ↦ ∂_θu(z,π/4)` are continuous on the compact interval `[a,b]` (joint `C^∞`-regularity of
`u` on the open quadrant); this is where the compactness of `[a,b]` and the positivity of `a`
enter, and it is the only place where the constant is not explicit.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option maxHeartbeats 1000000

/-- `σ θ = sEta θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
private lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hθ) _

theorem aeUMassBound : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    ∀ a b : ℝ, 0 < a →
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ,
      |u z θ| ≤ K * (1 + Real.sqrt (Work.FTS.EllipticEst.AngAWeak.AAA u z)) := by
  intro α u G h a b ha
  by_cases hba : b < a
  · -- the interval is empty
    exact ⟨1, one_pos, fun z hz _ _ => by
      exfalso
      rw [Set.mem_Icc] at hz
      linarith [hz.1, hz.2]⟩
  push Not at hba
  -- ## the interior angle `π/4` and the joint smoothness
  have hpi4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hU : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmap : Set.MapsTo (fun z : ℝ => (z, Real.pi / 4)) (Set.Icc a b)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro z hz
    rw [Set.mem_Icc] at hz
    refine ⟨?_, hpi4⟩
    show (0 : ℝ) < z
    linarith [hz.1, ha]
  have hq : ContinuousOn (fun z : ℝ => (z, Real.pi / 4)) (Set.Icc a b) :=
    (continuous_id.prodMk continuous_const).continuousOn
  -- ## continuity in `z` of the two reference values
  have hcont0 : ContinuousOn (fun z : ℝ => u z (Real.pi / 4)) (Set.Icc a b) := by
    have h1 := ((h.smooth 0).continuousOn).comp hq hmap
    simpa [Function.comp_def, Function.uncurry_apply_pair] using h1
  have hcont1 : ContinuousOn (fun z : ℝ => Work.Spaces.pth u z (Real.pi / 4)) (Set.Icc a b) := by
    have h1 := ((hU.pth).continuousOn).comp hq (by simpa [Work.FTS.EllipticEst.Q0] using hmap)
    simpa [Function.comp_def, Function.uncurry_apply_pair] using h1
  -- ## uniform bounds of the two reference values on `[a,b]`
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont0
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont1
  refine ⟨max 0 C0 + (Real.pi / 2) * max 0 C1
      + (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ max 0 C0 := le_max_left _ _
    have h2 : (0 : ℝ) ≤ max 0 C1 := le_max_left _ _
    have h3 : (0 : ℝ) ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    have h5 : (0 : ℝ) ≤ (Real.pi / 2) * max 0 C1 := mul_nonneg h4 h2
    have h6 : (0 : ℝ) ≤ (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := mul_nonneg h4 h3
    linarith
  · intro z hz θ hθ
    have hz0 : 0 < z := by
      rw [Set.mem_Icc] at hz
      show (0 : ℝ) < z
      linarith [hz.1, ha]
    -- the two reference bounds at this `z`
    have hb0 : |u z (Real.pi / 4)| ≤ max 0 C0 := by
      have h1 := hC0 z hz
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_max_right _ _)
    have hb1 : |Work.Spaces.pth u z (Real.pi / 4)| ≤ max 0 C1 := by
      have h1 := hC1 z hz
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_max_right _ _)
    have hK0 : 0 < max 0 C0 + (Real.pi / 2) * max 0 C1
        + (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) + 1 := by
      have h1 : (0 : ℝ) ≤ max 0 C0 := le_max_left _ _
      have h2 : (0 : ℝ) ≤ max 0 C1 := le_max_left _ _
      have h3 : (0 : ℝ) ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := Real.sqrt_nonneg _
      have h4 : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      have h5 : (0 : ℝ) ≤ (Real.pi / 2) * max 0 C1 := mul_nonneg h4 h2
      have h6 : (0 : ℝ) ≤ (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := mul_nonneg h4 h3
      linarith
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · -- `θ = 0`
      rw [← h0, h.dirZero z, abs_zero]
      exact mul_nonneg (le_of_lt hK0) (by positivity)
    rcases eq_or_lt_of_le hθ.2 with hpi | hpi
    · -- `θ = π/2`
      rw [hpi, h.dirPi z, abs_zero]
      exact mul_nonneg (le_of_lt hK0) (by positivity)
    · -- `θ ∈ (0, π/2)`: the slice estimate
      have hIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h0, hpi⟩
      -- ## the slicewise `σ`-integrability of `∂_θθu` and the weighted Cauchy–Schwarz
      have hsEta : MeasureTheory.IntegrableOn
          (fun t => (Work.Spaces.pthIter 2 u z t) ^ 2 * Work.FTS.EllipticEst.sEta t)
          Work.Spaces.Iθ :=
        Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem (Ψ := u) h.memAng2 hz0
      have hcont2 : ContinuousOn (fun t => Work.Spaces.pthIter 2 u z t)
          (Set.Ioo 0 (Real.pi / 2)) :=
        Work.FTS.EllipticEst.Endpt.continuousOn_pthIter2_of_strip (Ψ := u) h.smooth hz0
      have hcs := Work.FTS.EllipticEst.sliceCSWeightedOpen
        (g := fun t => Work.Spaces.pthIter 2 u z t) hcont2 hsEta
      have hAAAA : Work.FTS.EllipticEst.AngAWeak.AAA u z
          = ∫ t in Work.Spaces.Iθ,
              (Work.Spaces.pthIter 2 u z t) ^ 2 * Work.FTS.EllipticEst.sEta t := rfl
      have hAAA0 : 0 ≤ Work.FTS.EllipticEst.AngAWeak.AAA u z := by
        rw [hAAAA]
        exact setIntegral_nonneg measurableSet_Icc
          (fun t ht => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ ht))
      -- ## `∫ |∂_θθu| ≤ √(AAA u z) · √(∫ sin^η)`
      have hint_le : (∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 u z t|)
          ≤ Real.sqrt (Work.FTS.EllipticEst.AngAWeak.AAA u z)
            * Real.sqrt (∫ t in Work.Spaces.Iθ, (Real.sin (2 * t)) ^ (Work.Spaces.eta)) := by
        have hsq : (∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 u z t|) ^ 2
            ≤ Work.FTS.EllipticEst.AngAWeak.AAA u z
              * ∫ t in Work.Spaces.Iθ, (Real.sin (2 * t)) ^ (Work.Spaces.eta) := by
          rw [hAAAA]
          exact hcs
        have hnn : 0 ≤ ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 u z t| :=
          integral_nonneg (fun t => abs_nonneg _)
        calc (∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 u z t|)
            = Real.sqrt ((∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 u z t|) ^ 2) :=
              (Real.sqrt_sq hnn).symm
          _ ≤ Real.sqrt (Work.FTS.EllipticEst.AngAWeak.AAA u z
                * ∫ t in Work.Spaces.Iθ, (Real.sin (2 * t)) ^ (Work.Spaces.eta)) :=
              Real.sqrt_le_sqrt hsq
          _ = Real.sqrt (Work.FTS.EllipticEst.AngAWeak.AAA u z)
                * Real.sqrt (∫ t in Work.Spaces.Iθ, (Real.sin (2 * t)) ^ (Work.Spaces.eta)) :=
              Real.sqrt_mul hAAA0 _
      -- ## the fundamental theorem of calculus based at `π/4`
      have hpsi := Work.FTS.EllipticEst.Endpt.psi_le_of_strip_HkMem (Ψ := u)
        h.smooth h.memAng2 hz0 θ hIoo
      -- ## assembly
      set s : ℝ := Real.sqrt (Work.FTS.EllipticEst.AngAWeak.AAA u z) with hsdef
      set t : ℝ := Real.sqrt (∫ τ in Work.Spaces.Iθ, (Real.sin (2 * τ)) ^ (Work.Spaces.eta))
        with htdef
      set K : ℝ := max 0 C0 + (Real.pi / 2) * max 0 C1 + (Real.pi / 2) * t + 1 with hKdef
      have hsnn : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
      have htnn : 0 ≤ t := by rw [htdef]; exact Real.sqrt_nonneg _
      have hst : s * t = Real.sqrt (Work.FTS.EllipticEst.AngAWeak.AAA u z)
          * Real.sqrt (∫ τ in Work.Spaces.Iθ, (Real.sin (2 * τ)) ^ (Work.Spaces.eta)) := by
        rw [hsdef, htdef]
      have hsmall : |u z θ| ≤ max 0 C0
          + (Real.pi / 2) * (max 0 C1 + s * t) := by
        have h1 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
        have h2 : |Work.Spaces.pth u z (Real.pi / 4)|
            + (∫ τ in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 u z τ|) ≤ max 0 C1 + s * t := by
          linarith [hb1, hint_le]
        have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt h1)
        linarith [hpsi, hb0, h3]
      have hbig : max 0 C0 + (Real.pi / 2) * (max 0 C1 + s * t) ≤ K * (1 + s) := by
        have hM0nn : (0 : ℝ) ≤ max 0 C0 := le_max_left _ _
        have hM1nn : (0 : ℝ) ≤ max 0 C1 := le_max_left _ _
        have h4 : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        rw [hKdef]
        have hkey : (max 0 C0 + Real.pi / 2 * max 0 C1 + Real.pi / 2 * t + 1) * (1 + s)
            = (max 0 C0 + Real.pi / 2 * (max 0 C1 + s * t))
              + (Real.pi / 2 * t + 1 + s * (max 0 C0 + Real.pi / 2 * max 0 C1) + s) := by
          ring
        rw [hkey]
        have h5 : 0 ≤ Real.pi / 2 * t + 1 + s * (max 0 C0 + Real.pi / 2 * max 0 C1) + s := by
          have h6 : 0 ≤ s * (max 0 C0 + Real.pi / 2 * max 0 C1) :=
            mul_nonneg hsnn (by
              have h8 : 0 ≤ Real.pi / 2 * max 0 C1 := mul_nonneg h4 hM1nn
              linarith)
          have h7 : 0 ≤ Real.pi / 2 * t := mul_nonneg h4 htnn
          linarith
        linarith [h5]
      calc |u z θ| ≤ max 0 C0 + (Real.pi / 2) * (max 0 C1 + s * t) := hsmall
        _ ≤ K * (1 + s) := hbig
        _ = K * (1 + Real.sqrt (Work.FTS.EllipticEst.AngAWeak.AAA u z)) := by
            rw [hsdef]

end Work.FTS.EllipticEst.AngAWeak
