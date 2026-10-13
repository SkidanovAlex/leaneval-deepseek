/-
# `TraceEngine.cBK_integrable` — integrability of the `θ`-pairing `cBK` against `thEta`

For the logarithmic cut-off family `χ` (`CutFam χ K`, supported in the window
`[cA k, cB k] = [1/(k+1)², (k+1)²]`) and a datum `G` which is `C^∞` on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen G`), the main theorem of this file states that the angular
pairing

  `θ ↦ thEta θ · cBK χ k (D_zG) θ`,   `thEta θ = sin(2θ)^{-η}`,  `η = 99/100`,

is integrable on `Iθ = [0, π/2]`, as soon as the three weighted `H¹`-level slots of the paper
are finite (`hXi`, `hT`, `hD` below): the radial combination `Ξ = D_z²G + ((z-3)/(1+z))·D_zG`
against the weight `w(z)² = ((1+z)²/z²)²`, the angular second derivative `∂_θ²G`, and `D_zG`
itself.

## Proof

* `gK_ibp_fts` rewrites, at every angle `θ ∈ Iθ`, the pairing
  `cBK χ k (D_zG) θ = ∫_{cA k}^{cB k} χ_k w² (D_zG)(∂_θ²D_zG)` as the sum of the two pieces
  produced by the radial integration by parts,
  `- ∫_{cA k}^{cB k} χ_k w² Ξ ∂_θ²G - ∫_{cA k}^{cB k} (z χ_k') w² (D_zG) ∂_θ²G`
  (at `θ = 0, π/2` both sides vanish because `thEta` does).
* Each of the two pieces is a `θ`-marginal over `Iz` of a nonnegative joint integrand
  (`CutBk.bridge_cutPsi`, `CutBk.bridge_cutPsiB`), and each of those joint integrands is
  integrable on the strip by `CutBk.integrable_cutPsi` / `CutBk.integrable_cutPsiB`, which is
  the Cauchy–Schwarz/AM–GM combination of the hypotheses (`|χ_k| ≤ 1` and
  `|z χ_k'| ≤ K/log(k+2)`).  `MeasureTheory.Integrable.integral_prod_right` (Fubini) then gives
  the integrability of the two marginals, and `MeasureTheory.Integrable.congr` transfers it
  along the pointwise integration-by-parts identity to the target function.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore
import Submission.Work.FTS.EllSol.PkgK5.gK_ibp_fts
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.CutBkAux
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.CutBkAuxB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.TraceEngine

open CutBk

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem cBK_integrable {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (hXi : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 G p.1 p.2
            + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz G p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hT : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hD : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz G p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
        * Work.FTS.EllSol.PkgK5.cBK χ k (Work.Spaces.Dz G) θ) Work.Spaces.Iθ := by
  -- ## the three hypotheses in the notation of `CutBk`
  have hXiM : MeasureTheory.Integrable (fun p : ℝ × ℝ => cutRho p * cutXi G p ^ 2) Mu := hXi
  have hTM : MeasureTheory.Integrable (fun p : ℝ × ℝ => cutRho p * cutD2 G p ^ 2) Mu := hT
  have hDM : MeasureTheory.Integrable (fun p : ℝ × ℝ => cutRho p * cutPs G p ^ 2) Mu := hD
  -- ## integrability of the two joint integrands on the strip
  have hPsiM := integrable_cutPsi hχ k hG hXiM hTM
  have hPsiBM := integrable_cutPsiB hχ k hG hDM hTM
  have hPsiM' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← Mu_eq_prod]; exact hPsiM
  have hPsiBM' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← Mu_eq_prod]; exact hPsiBM
  -- ## the two marginal integrabilities (Fubini), identified with the two IBP pieces
  have hIntA : MeasureTheory.Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ *
      (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
        * cutXi G (z, θ) * cutD2 G (z, θ))) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h0 : MeasureTheory.Integrable (fun θ : ℝ => ∫ z, (fun p : ℝ × ℝ =>
        cutRho p * χ k p.1 * cutXi G p * cutD2 G p) (z, θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hPsiM'.integral_prod_right
    exact h0.congr (ae_of_mem_Iθ (fun θ _ => bridge_cutPsi hχ k θ))
  have hIntB : MeasureTheory.Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ *
      (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
        * cutPs G (z, θ) * cutD2 G (z, θ))) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h0 : MeasureTheory.Integrable (fun θ : ℝ => ∫ z, (fun p : ℝ × ℝ =>
        (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) (z, θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hPsiBM'.integral_prod_right
    exact h0.congr (ae_of_mem_Iθ (fun θ _ => bridge_cutPsiB hχ k θ))
  -- ## the radial integration by parts at each angle of `Iθ`
  have hslice : ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta θ * cBK χ k (Work.Spaces.Dz G) θ
        = - (Work.FTS.EllipticEst.thEta θ *
              (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
                * cutXi G (z, θ) * cutD2 G (z, θ))
            + Work.FTS.EllipticEst.thEta θ *
              (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
                * cutPs G (z, θ) * cutD2 G (z, θ))) := by
    intro θ hθ
    have hmem : θ ∈ Set.Icc (0 : ℝ) (π / 2) := hθ
    rcases lt_or_eq_of_le hmem.1 with h0 | h0
    · rcases lt_or_eq_of_le hmem.2 with h1 | h1
      · have h := gK_ibp_fts hχ k hG ⟨h0, h1⟩
        have hA : (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
              * cutXi G (z, θ) * cutD2 G (z, θ))
            = (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
                * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
                * Work.Spaces.pthIter 2 G z θ) := by
          refine intervalIntegral.integral_congr (fun z _ => ?_)
          rw [show cutXi G (z, θ) = Work.Spaces.DzIter 2 G z θ
                + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ from rfl,
              show cutD2 G (z, θ) = Work.Spaces.pthIter 2 G z θ from rfl]
        have hB : (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
              * cutPs G (z, θ) * cutD2 G (z, θ))
            = (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
                * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ) := by
          refine intervalIntegral.integral_congr (fun z _ => ?_)
          rw [show cutPs G (z, θ) = Work.Spaces.Dz G z θ from rfl,
              show cutD2 G (z, θ) = Work.Spaces.pthIter 2 G z θ from rfl]
        have hc : cBK χ k (Work.Spaces.Dz G) θ
            = - (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
                  * cutXi G (z, θ) * cutD2 G (z, θ))
              - (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
                  * cutPs G (z, θ) * cutD2 G (z, θ)) := by
          rw [show cBK χ k (Work.Spaces.Dz G) θ
              = (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2 * Work.Spaces.Dz G z θ
                  * Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ) from rfl, h, hA, hB]
        rw [hc]
        ring
      · rw [h1, thEta_piHalf]
        ring
    · rw [← h0, thEta_zero]
      ring
  -- ## assembly: the target is the negative of the sum of the two integrable pieces
  refine ((hIntA.add hIntB).neg).congr (ae_of_mem_Iθ (fun θ hθ => ?_))
  simp only [Pi.neg_apply, Pi.add_apply]
  rw [hslice θ hθ]

end Work.FTS.EllSol.PkgK5.TraceEngine
