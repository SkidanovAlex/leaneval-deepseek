/-
# `cutBkBound` — the cut-off bound for the `θ`-pairing `cBK`

For the logarithmic cut-off family `χ` (`CutFam χ K`, supported in
`[cA k, cB k] = [1/(k+1)², (k+1)²]`) and a datum `G` which is `C^∞` on the open quadrant the
pairing `cBK χ k (D_zG) θ = ∫_{cA k}^{cB k} χ_k w² (D_zG)(z,θ) (∂_θ²D_zG)(z,θ) dz`
(`w z = (1+z)²/z²`) satisfies, after multiplication by `thEta θ = sin(2θ)^{-η}` and
integration in `θ`, the Cauchy–Schwarz bound of the two corresponding `ℋ`-slots.

The proof is: (1) the radial integration by parts `gK_ibp_fts` at each `θ ∈ (0,π/2)`;
(2) `thEta` vanishes at the two endpoints, so the pointwise identity holds on all of `Iθ`, and
Fubini (`integral_prod_symm`) turns the `θ`-integral of each of the two pieces into the
corresponding integral over the strip `Iz ×ˢ Iθ`; (3) `|χ_k| ≤ 1`, `|zχ_k'| ≤ K/log(k+2)`
pointwise and Cauchy–Schwarz in `L²` on the strip.  All the analytic ingredients are in
`CutBkAux`/`CutBkAuxB`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
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

/-! ## The main bound -/

theorem cutBkBound {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
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
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hL : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
        * Work.FTS.EllSol.PkgK5.cBK χ k (Work.Spaces.Dz G) θ) Work.Spaces.Iθ) :
    - (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * Work.FTS.EllSol.PkgK5.cBK χ k (Work.Spaces.Dz G) θ)
      ≤ Real.sqrt ((∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
              * Work.FTS.EllipticEst.thEta p.2
              * (Work.Spaces.DzIter 2 G p.1 p.2
                  + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz G p.1 p.2) ^ 2)
          * (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
              * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2))
        + (K / Real.log ((k : ℝ) + 2)) * Real.sqrt (
            (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
              * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz G p.1 p.2) ^ 2)
            * (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
              * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2)) := by
  -- ## the hypotheses in the local notation
  have hXiM : Integrable (fun p : ℝ × ℝ => cutRho p * cutXi G p ^ 2) Mu := hXi
  have hTM : Integrable (fun p : ℝ × ℝ => cutRho p * cutD2 G p ^ 2) Mu := hT
  have hDM : Integrable (fun p : ℝ × ℝ => cutRho p * cutPs G p ^ 2) Mu := hD
  have hPsiM := integrable_cutPsi hχ k hG hXiM hTM
  have hPsiBM := integrable_cutPsiB hχ k hG hDM hTM
  have hPsiM' : Integrable (fun p : ℝ × ℝ => cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Mu_eq_prod]; exact hPsiM
  have hPsiBM' : Integrable
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Mu_eq_prod]; exact hPsiBM
  -- ## nonnegativity of the three slot integrals and of `K / log (k+2)`
  have hnonnegΞ : 0 ≤ ∫ p in Izθ, cutRho p * cutXi G p ^ 2 :=
    integral_nonneg_of_ae (ae_of_mem_Izθ fun p hp => mul_nonneg (cutRho_nonneg hp) (sq_nonneg _))
  have hnonnegD : 0 ≤ ∫ p in Izθ, cutRho p * cutD2 G p ^ 2 :=
    integral_nonneg_of_ae (ae_of_mem_Izθ fun p hp => mul_nonneg (cutRho_nonneg hp) (sq_nonneg _))
  have hnonnegPs : 0 ≤ ∫ p in Izθ, cutRho p * cutPs G p ^ 2 :=
    integral_nonneg_of_ae (ae_of_mem_Izθ fun p hp => mul_nonneg (cutRho_nonneg hp) (sq_nonneg _))
  have hKL : 0 ≤ K / Real.log ((k : ℝ) + 2) := div_nonneg hχ.K0 (log_k_pos k).le
  -- ## step 1: the radial integration by parts at each angle
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
  -- ## step 2: the two `θ`-integrals as integrals over the strip (Fubini)
  have hbridgeA := bridge_cutPsi hχ k (G := G)
  have hbridgeB := bridge_cutPsiB hχ k (G := G)
  have hIntA : Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
          * cutXi G (z, θ) * cutD2 G (z, θ))) (volume.restrict Work.Spaces.Iθ) := by
    have h0 : Integrable (fun θ : ℝ => ∫ z, (fun p : ℝ × ℝ =>
        cutRho p * χ k p.1 * cutXi G p * cutD2 G p) (z, θ)
        ∂(volume.restrict Work.Spaces.Iz)) (volume.restrict Work.Spaces.Iθ) :=
      hPsiM'.integral_prod_right
    exact h0.congr (ae_of_mem_Iθ (fun θ _ => hbridgeA θ))
  have hIntB : Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
          * cutPs G (z, θ) * cutD2 G (z, θ))) (volume.restrict Work.Spaces.Iθ) := by
    have h0 : Integrable (fun θ : ℝ => ∫ z, (fun p : ℝ × ℝ =>
        (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) (z, θ)
        ∂(volume.restrict Work.Spaces.Iz)) (volume.restrict Work.Spaces.Iθ) :=
      hPsiBM'.integral_prod_right
    exact h0.congr (ae_of_mem_Iθ (fun θ _ => hbridgeB θ))
  have hkeyA : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
          * cutXi G (z, θ) * cutD2 G (z, θ)))
      = ∫ p in Izθ, cutRho p * χ k p.1 * cutXi G p * cutD2 G p := by
    rw [setIntegral_congr_fun measurableSet_Iθ (fun θ _ => (hbridgeA θ).symm)]
    rw [setIntegral_Izθ_eq_prod]
    exact (integral_prod_symm (μ := volume.restrict Work.Spaces.Iz)
      (ν := volume.restrict Work.Spaces.Iθ)
      (fun p : ℝ × ℝ => cutRho p * χ k p.1 * cutXi G p * cutD2 G p) hPsiM').symm
  have hkeyB : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
          * cutPs G (z, θ) * cutD2 G (z, θ)))
      = ∫ p in Izθ, (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p := by
    rw [setIntegral_congr_fun measurableSet_Iθ (fun θ _ => (hbridgeB θ).symm)]
    rw [setIntegral_Izθ_eq_prod]
    exact (integral_prod_symm (μ := volume.restrict Work.Spaces.Iz)
      (ν := volume.restrict Work.Spaces.Iθ)
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p)
      hPsiBM').symm
  have hLHSelim : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * cBK χ k (Work.Spaces.Dz G) θ)
      = - ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
              (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
                * cutXi G (z, θ) * cutD2 G (z, θ)))
          + (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
              (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
                * cutPs G (z, θ) * cutD2 G (z, θ)))) := by
    rw [setIntegral_congr_fun measurableSet_Iθ hslice, integral_neg, integral_add hIntA hIntB]
  have hmain : - (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * cBK χ k (Work.Spaces.Dz G) θ)
      = (∫ p in Izθ, cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
        + (∫ p in Izθ, (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) := by
    rw [hLHSelim, neg_neg, hkeyA, hkeyB]
  -- ## step 3: the two Cauchy–Schwarz bounds
  have hcsA := csSqrt_ae (μ := Mu) (ρ := cutRho) (Ξ := cutXi G) (Φ := cutD2 G)
    (ae_of_mem_Izθ (fun p hp => cutRho_nonneg hp)) hXiM hTM
  have hcsB := csSqrt_ae (μ := Mu) (ρ := cutRho) (Ξ := cutPs G) (Φ := cutD2 G)
    (ae_of_mem_Izθ (fun p hp => cutRho_nonneg hp)) hDM hTM
  have hboundA : (∫ p in Izθ, cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
      ≤ Real.sqrt ((∫ p in Izθ, cutRho p * cutXi G p ^ 2)
          * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) := by
    calc (∫ p in Izθ, cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
        ≤ ∫ p in Izθ, cutRho p * |cutXi G p| * |cutD2 G p| := by
          refine integral_mono_ae hPsiM hcsA.1 ?_
          exact ae_of_mem_Izθ (fun p hp => cutPsi_le_abs hχ k hp)
      _ ≤ Real.sqrt (∫ p in Izθ, cutRho p * cutXi G p ^ 2)
            * Real.sqrt (∫ p in Izθ, cutRho p * cutD2 G p ^ 2) := hcsA.2
      _ = Real.sqrt ((∫ p in Izθ, cutRho p * cutXi G p ^ 2)
            * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) :=
          (Real.sqrt_mul hnonnegΞ _).symm
  have hboundB : (∫ p in Izθ, (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p)
      ≤ (K / Real.log ((k : ℝ) + 2)) * Real.sqrt ((∫ p in Izθ, cutRho p * cutPs G p ^ 2)
          * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) := by
    calc (∫ p in Izθ, (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p)
        ≤ (K / Real.log ((k : ℝ) + 2))
            * (∫ p in Izθ, cutRho p * |cutPs G p| * |cutD2 G p|) := by
          rw [← integral_const_mul]
          refine integral_mono_ae hPsiBM (hcsB.1.const_mul _) ?_
          exact ae_of_mem_Izθ (fun p hp => cutPsiB_le hχ k hp)
      _ ≤ (K / Real.log ((k : ℝ) + 2)) * (Real.sqrt (∫ p in Izθ, cutRho p * cutPs G p ^ 2)
            * Real.sqrt (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) :=
          mul_le_mul_of_nonneg_left hcsB.2 hKL
      _ = (K / Real.log ((k : ℝ) + 2)) * Real.sqrt ((∫ p in Izθ, cutRho p * cutPs G p ^ 2)
            * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) := by
          rw [Real.sqrt_mul hnonnegPs]
  -- ## assembly
  calc - (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * cBK χ k (Work.Spaces.Dz G) θ)
      = (∫ p in Izθ, cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
        + (∫ p in Izθ, (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) := hmain
    _ ≤ Real.sqrt ((∫ p in Izθ, cutRho p * cutXi G p ^ 2)
          * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2))
        + (K / Real.log ((k : ℝ) + 2)) * Real.sqrt ((∫ p in Izθ, cutRho p * cutPs G p ^ 2)
          * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) := add_le_add hboundA hboundB

end Work.FTS.EllSol.PkgK5.TraceEngine
