/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AeStepOneAux.sliceCoerciveAe` — the slicewise `σ`-coercivity of `Lzero1` in the `AeData` class

This is the *almost everywhere* form of the slicewise coercivity of
`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` needed by Step 1 of the level-`0` elliptic estimate:
from the abstract slice hypothesis `SigmaCoercive` (the sharp coercivity on slices that carry
the three explicit endpoint bounds `|u θ| ≤ C θ`, `|u θ| ≤ C(π/2-θ)`, `|u' θ| ≤ C` together
with the four `σ`-weighted integrabilities, `σ = sin(2θ)^{-η}`) one gets, for a datum
`AeData α u G` whose slices vanish at `θ = 0` along a.e. `z`, the *lower* bound

  `∫_θ Lzero1 (u z ·) θ · u z θ · σ θ ≥ -K ∫_θ (u z θ)² σ θ`   for a.e. `z > 0`.

The proof is a transfer: for a.e. `z` the slice of an `AeData` datum satisfies the four
hypotheses of `SigmaCoercive`,

* the endpoint rates `|u z θ| ≤ C min(θ, π/2-θ)` and `|∂_θu z θ| ≤ C` come from
  `AeSliceFacts.aeSliceBound` (the left limit is the hypothesis `hL`, the right limit is
  unconditional, the derivative bound is the fundamental theorem of calculus on the open
  interval, from the `σ`-square integrability of `∂_θθu`);
* the `σ`-weighted integrabilities are `AeSliceFacts.aeSliceSigmaInt` (four of them, for every
  `z > 0`) together with `∫ (∂_θθu)² σ < ∞` read off the honesty `HkMem α 0 (∂_θθu)` of the
  datum (`Endpt.integrableOn_pthIter2_sEta_of_HkMem`);

and then dropping the nonnegative left-hand side of the coercivity gives the claim.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AeStepOneAux.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeSliceFacts
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeStepOneAux

open scoped Real Topology
open MeasureTheory Set Filter

theorem sliceCoerciveAe (hK : Work.FTS.EllipticEst.AeStepOneAux.SigmaCoercive) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ =>
            Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ
              * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ
        ∧ -K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            ≤ ∫ θ in Work.Spaces.Iθ,
                Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ
                  * Work.FTS.EllipticEst.sEta θ := by
  obtain ⟨K, hKpos, hKmain⟩ := hK
  refine ⟨K, hKpos, ?_⟩
  intro α u G hAe hL
  -- the endpoint rates of the slices, a.e. in `z`
  have hbdd := Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceBound α u G hAe hL
  filter_upwards [hbdd, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hzb hz
  obtain ⟨C, hCpos, hC⟩ := hzb
  have hCnn : 0 ≤ C := le_of_lt hCpos
  -- the `σ`-weighted slice integrability (for every `z > 0`)
  obtain ⟨h1, h2, _h3, _h4, h5⟩ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G hAe z hz
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    Set.Ioo_subset_Icc_self
  -- the slice is `C²` on the open interval
  have hsm : ContDiffOn ℝ 2 (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hAe.smooth hz 2
  -- the second angular derivative, in the form of the two iterated `deriv`s
  have hpth2 : ∀ θ : ℝ,
      Work.Spaces.pthIter 2 u z θ = deriv (deriv (fun θ' : ℝ => u z θ')) θ := by
    intro θ
    simp only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ,
      Work.Spaces.pthIter_zero, Work.Spaces.pth]
  have hAng : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv (fun θ' : ℝ => u z θ')) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem hAe.memAng2 hz).congr_fun
      (fun θ _ => by simp only [hpth2 θ]) measurableSet_Icc
  -- the three `σ`-weighted integrabilities on the open interval
  have hduO : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' : ℝ => u z θ') θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := h2.mono_set hIoo
    simpa only [Work.Spaces.pth] using h
  have hdduO : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := hAng.mono_set hIoo
    simpa only using h
  have hu2O : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := h1.mono_set hIoo
  -- the coercivity of the abstract slice class
  have hkey := hKmain (fun θ : ℝ => u z θ) C hCnn hsm
    (fun θ hθ => (hC θ hθ).1)
    (fun θ hθ => (hC θ hθ).2.1)
    (fun θ hθ => by simpa only [Work.Spaces.pth] using (hC θ hθ).2.2)
    hduO hdduO hu2O h5
  -- drop the nonnegative left-hand side of the coercivity
  have hA0 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (deriv (fun θ' : ℝ => u z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ)
  have hcoef : 0 ≤ (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta) :=
    div_nonneg (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])
  have hprod : 0 ≤ (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
      * (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' : ℝ => u z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    mul_nonneg hcoef hA0
  have hLP : 0 ≤ (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ
          * Work.FTS.EllipticEst.sEta θ)
      + K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    le_trans hprod hkey
  refine ⟨h5, ?_⟩
  linarith [hLP]

end Work.FTS.EllipticEst.AeStepOneAux
