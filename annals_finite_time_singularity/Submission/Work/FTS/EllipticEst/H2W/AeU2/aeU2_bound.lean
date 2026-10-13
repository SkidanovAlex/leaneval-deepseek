/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AeU2/aeU2_bound` — the weighted finiteness `∫ ρ u² < ∞` in the almost-everywhere class

Let `AeData α u G` be the almost-everywhere class of the level-`0` elliptic estimate
(`Submission/Work/FTS/EllipticEst/H2W/Ae/Defs.lean`): `bslOp α u = G` on the open quadrant, `u` is
`C^∞` there with the two Dirichlet traces, the two angular moments of `u` and `G` vanish a.e., and
the weighted squares of `G`, `z²∂_zz u` and `∂_θθ u` are honest.  Nothing is assumed about `u`
itself.  This module proves that `u` is nevertheless finite in the weighted `L²`-space, with a
universal constant:

  `∫⁻_z w(z)² · (∫⁻_θ (u z θ)² σ θ) ≤ C · ofReal (HkSq α 0 (∂_θθ u))`,

`w z = (1+z)²/z²`, `σ = sEta = sin(2θ)^{-η}`, provided the one-sided trace of `u` at `θ → 0⁺`
vanishes for a.e. `z` (the trace at `π/2` is free: it is a theorem in this class,
`H2W.AeProof.AeSliceRightTendsto`).

## Route

Everything is slicewise in `z`.  For a.e. `z` the slice `f := fun θ => u z θ` is `C²` on
`(0, π/2)`, has `∫_θ (f'')² σ < ∞` (`AeData.memAng2`), and has both endpoint traces `0`; the
second-order weighted Poincaré inequality `sliceSigmaTraceZero` then gives

  `∫⁻_θ (f)² σ ≤ C₁ · ∫⁻_θ (f'')² σ`.

Multiplying by the `z`-independent nonnegative constant `ofReal (w z)²` and integrating in `z`
(`lintegral_mono_ae`, `lintegral_const_mul'`), and identifying the resulting double `∫⁻` with
`ofReal (HkSq α 0 (∂_θθ u))` (`ofReal_HkSq_eq_lintegral`, from the honesty `AeData.memAng2`),
gives the claim.

The constant `C` is the constant `C₁` of `sliceSigmaTraceZero`, hence universal in `α`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Honest.HonSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.AeU2.sliceSigmaTraceZero
import Submission.Work.FTS.EllipticEst.H2W.AeU2.ofReal_HkSq_eq_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeU2

set_option autoImplicit false

/-- `Ioi 0` and `Iz = Ici 0` differ by the null singleton `{0}`, hence carry the same restriction
of Lebesgue measure. -/
lemma restrict_Ioi_eq_restrict_Iz :
    MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
  MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici

theorem aeU2_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      ≤ ENNReal.ofReal C
        * ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := sliceSigmaTraceZero
  refine ⟨C₁, hC₁pos, ?_⟩
  intro α u G hA h0
  -- the two `z`-slice `∫⁻`'s that occur in the target
  set Φ : ℝ → ENNReal := fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (u z θ ^ 2 * Work.FTS.EllipticEst.sEta θ) with hΦdef
  set Ψ : ℝ → ENNReal := fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((deriv (fun θ' => deriv (fun θ'' => u z θ'') θ')) θ ^ 2
        * Work.FTS.EllipticEst.sEta θ) with hΨdef
  -- (1) the slicewise bound, for almost every `z`
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Φ z ≤ ENNReal.ofReal C₁ * Ψ z := by
    filter_upwards [h0, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
    -- the slice is `C²` on the open interval
    have hsm : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.Honest.contDiffOn_slice u hzpos (hA.smooth 2)
    -- the `σ`-weighted square of `∂_θθ u` is integrable on the slice
    have hint : MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun θ' => deriv (fun θ'' => u z θ'') θ')) θ ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
      have h1 := Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma hA.memAng2 hzpos
      refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
      simp only [congrFun (Work.FTS.EllipticEst.Honest.pthIter_two_eq u z) θ]
    -- the trace at `π/2` vanishes in this class
    have hL : Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G hA z hzpos).1
    have hthis := hC₁ (fun θ => u z θ) hsm hint hz hL
    rwa [hΦdef, hΨdef]
  -- (2) integrate the slicewise bound in `z`
  have hmain : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Φ z)
      ≤ ENNReal.ofReal C₁
        * (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z) := by
    calc ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Φ z
        ≤ ∫⁻ z in Set.Ioi 0,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * (ENNReal.ofReal C₁ * Ψ z) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [hslice] with z hz
          exact mul_le_mul_right hz _
      _ = ENNReal.ofReal C₁
            * ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z := by
          rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal C₁) _
            ENNReal.ofReal_ne_top]
          exact MeasureTheory.lintegral_congr (fun z => by rw [mul_left_comm])
  -- (3) `Ioi 0` and `Iz` carry the same measure
  have hIoi : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z := by
    rw [restrict_Ioi_eq_restrict_Iz]
  -- (4) `Ψ` is the `θθ`-slice of `u`
  have hΨ : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    simp only [hΨdef]
    congr 1
  -- (5) the double `∫⁻` is `ofReal (HkSq α 0 (∂_θθ u))`
  have hHk : ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) :=
    ofReal_HkSq_eq_lintegral α (Work.Spaces.pthIter 2 u) hA.memAng2
  calc ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Φ z
      ≤ ENNReal.ofReal C₁
          * (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z) := hmain
    _ = ENNReal.ofReal C₁
          * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z) := by
        rw [hIoi]
    _ = ENNReal.ofReal C₁
          * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
                    * Work.FTS.EllipticEst.sEta θ))) := by
        rw [hΨ]
    _ = ENNReal.ofReal C₁
          * ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) := by
        rw [hHk]

end Work.FTS.EllipticEst.H2W.AeU2
