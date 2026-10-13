import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut.TTAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts.TendstoTermsCut.TTAuxLimit`

The four `k → ∞` limits of the doubly truncated `I₁` identity: the radial cut-off `cut k` and the
angular cut-off `SliceMixedAux.cut (1/(k+1))` are removed simultaneously by dominated convergence
on `nuQ`, the untruncated slot being the dominating integrand.

Each proof rewrites the iterated integral of the statement into the product-measure integral
`∫ p, A p ∂nuQ` (Fubini, `MeasureTheory.integral_prod` via `II_eq_integral`), applies the
dominated-convergence limit of `TTAux`, and rewrites the limit value back by Fubini.
-/

namespace Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut
local notation "wt" => Work.Spaces.w
local notation "cwt" => Work.FTS.EllipticEst.AngSecond.cw

theorem tendsto_AB {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (U u)) (hV : Work.Spaces.HkMem α 0 (V u))
    (hA : Work.Spaces.HkMem α 0 (AA u)) (hB : Work.Spaces.HkMem α 0 (BB u)) :
    Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * ψ (dk k) θ
          * (AA u z θ * BB u z θ + cwt z * U u z θ * BB u z θ))
      atTop
      (nhds (∫ z in Set.Ioi 0, (wt z) ^ 2 * ∫ θ in Iθo, sigE θ
          * (AA u z θ * BB u z θ + cwt z * U u z θ * BB u z θ))) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  let X : ℝ → ℝ → ℝ := fun z θ => AA u z θ * BB u z θ + cwt z * U u z θ * BB u z θ
  let A : ℝ → ℝ → ℝ := fun z θ => (wt z) ^ 2 * (sigE θ * X z θ)
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => A p.1 p.2) nuQ := by
    refine (integrable_AB_slot hS hA hB hU).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [A, X]
    ring
  have hmain := tendsto_integral_cut_pair hInt
  have hL : ∀ k : ℕ, (∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * ψ (dk k) θ * X z θ)
      = ∫ p, (χ k p.1 * ψ (dk k) p.2) * A p.1 p.2 ∂nuQ := by
    intro k
    let G : ℝ → ℝ → ℝ :=
      fun z θ => (χ k z * (wt z) ^ 2) * (sigE θ * ψ (dk k) θ * X z θ)
    have hG : MeasureTheory.Integrable (fun p : ℝ × ℝ => G p.1 p.2) nuQ := by
      refine (integrable_cut_pair_mul hInt k).congr
        (Filter.Eventually.of_forall (fun p => ?_))
      dsimp only [G, A, X]
      ring
    have h1 : (∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * ψ (dk k) θ * X z θ)
        = II (fun z θ => G z θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      exact (MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Iθo)
        (χ k z * (wt z) ^ 2) (fun θ => sigE θ * ψ (dk k) θ * X z θ)).symm
    rw [h1, II_eq_integral (g := fun z θ => G z θ) hG]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [G, A, X]
    ring
  have h1t : Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * ψ (dk k) θ * X z θ)
      atTop (nhds (∫ p, (fun z θ => A z θ) p.1 p.2 ∂nuQ)) :=
    hmain.congr' (Filter.Eventually.of_forall (fun k => (hL k).symm))
  have hR : (∫ p, (fun z θ => A z θ) p.1 p.2 ∂nuQ)
      = ∫ z in Set.Ioi 0, (wt z) ^ 2 * ∫ θ in Iθo, sigE θ * X z θ := by
    have key : (∫ p, (fun z θ => A z θ) p.1 p.2 ∂nuQ)
        = ∫ z in Set.Ioi 0, ∫ θ in Iθo, A z θ :=
      MeasureTheory.integral_prod (fun p : ℝ × ℝ => (fun z θ => A z θ) p.1 p.2) hInt
    rw [key]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    exact MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Iθo)
      ((wt z) ^ 2) (fun θ => sigE θ * X z θ)
  rw [hR] at h1t
  exact h1t

theorem tendsto_dchi {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (U u)) (hV : Work.Spaces.HkMem α 0 (V u))
    (hA : Work.Spaces.HkMem α 0 (AA u)) (hB : Work.Spaces.HkMem α 0 (BB u)) :
    Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, (z * deriv (χ k) z) * (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * ψ (dk k) θ * (U u z θ * BB u z θ))
      atTop (nhds 0) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  let A : ℝ → ℝ → ℝ := fun z θ => (wt z) ^ 2 * (sigE θ * (U u z θ * BB u z θ))
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => A p.1 p.2) nuQ := by
    refine (integrable_UBB_slot hS hB hU).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [A]
    ring
  have hmain := tendsto_integral_dcut_pair hInt
  have hL : ∀ k : ℕ, (∫ z in Set.Ioi 0, (z * deriv (χ k) z) * (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * ψ (dk k) θ * (U u z θ * BB u z θ))
      = ∫ p, (p.1 * deriv (χ k) p.1 * ψ (dk k) p.2) * A p.1 p.2 ∂nuQ := by
    intro k
    let G : ℝ → ℝ → ℝ := fun z θ => ((z * deriv (χ k) z) * (wt z) ^ 2)
      * (sigE θ * ψ (dk k) θ * (U u z θ * BB u z θ))
    have hG : MeasureTheory.Integrable (fun p : ℝ × ℝ => G p.1 p.2) nuQ := by
      refine (integrable_cut_pair_dmul hInt k).congr
        (Filter.Eventually.of_forall (fun p => ?_))
      dsimp only [G, A]
      ring
    have h1 : (∫ z in Set.Ioi 0, (z * deriv (χ k) z) * (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * ψ (dk k) θ * (U u z θ * BB u z θ))
        = II (fun z θ => G z θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      exact (MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Iθo)
        ((z * deriv (χ k) z) * (wt z) ^ 2)
        (fun θ => sigE θ * ψ (dk k) θ * (U u z θ * BB u z θ))).symm
    rw [h1, II_eq_integral (g := fun z θ => G z θ) hG]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [G, A]
    ring
  refine hmain.congr' (Filter.Eventually.of_forall (fun k => (hL k).symm))

theorem tendsto_Vsq {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (U u)) (hV : Work.Spaces.HkMem α 0 (V u))
    (hA : Work.Spaces.HkMem α 0 (AA u)) (hB : Work.Spaces.HkMem α 0 (BB u)) :
    Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * ψ (dk k) θ * (V u z θ) ^ 2)
      atTop
      (nhds (∫ z in Set.Ioi 0, (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * (V u z θ) ^ 2)) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  let A : ℝ → ℝ → ℝ := fun z θ => (wt z) ^ 2 * (sigE θ * (V u z θ) ^ 2)
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => A p.1 p.2) nuQ := by
    refine (integrable_Vsq_slot hS hV).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [A]
    ring
  have hmain := tendsto_integral_cut_pair hInt
  have hL : ∀ k : ℕ, (∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * ψ (dk k) θ * (V u z θ) ^ 2)
      = ∫ p, (χ k p.1 * ψ (dk k) p.2) * A p.1 p.2 ∂nuQ := by
    intro k
    let G : ℝ → ℝ → ℝ :=
      fun z θ => (χ k z * (wt z) ^ 2) * (sigE θ * ψ (dk k) θ * (V u z θ) ^ 2)
    have hG : MeasureTheory.Integrable (fun p : ℝ × ℝ => G p.1 p.2) nuQ := by
      refine (integrable_cut_pair_mul hInt k).congr
        (Filter.Eventually.of_forall (fun p => ?_))
      dsimp only [G, A]
      ring
    have h1 : (∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * ψ (dk k) θ * (V u z θ) ^ 2)
        = II (fun z θ => G z θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      exact (MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Iθo)
        (χ k z * (wt z) ^ 2) (fun θ => sigE θ * ψ (dk k) θ * (V u z θ) ^ 2)).symm
    rw [h1, II_eq_integral (g := fun z θ => G z θ) hG]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [G, A]
    ring
  have h1t : Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sigE θ * ψ (dk k) θ * (V u z θ) ^ 2)
      atTop (nhds (∫ p, (fun z θ => A z θ) p.1 p.2 ∂nuQ)) :=
    hmain.congr' (Filter.Eventually.of_forall (fun k => (hL k).symm))
  have hR : (∫ p, (fun z θ => A z θ) p.1 p.2 ∂nuQ)
      = ∫ z in Set.Ioi 0, (wt z) ^ 2 * ∫ θ in Iθo, sigE θ * (V u z θ) ^ 2 := by
    have key : (∫ p, (fun z θ => A z θ) p.1 p.2 ∂nuQ)
        = ∫ z in Set.Ioi 0, ∫ θ in Iθo, A z θ :=
      MeasureTheory.integral_prod (fun p : ℝ × ℝ => (fun z θ => A z θ) p.1 p.2) hInt
    rw [key]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    exact MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Iθo)
      ((wt z) ^ 2) (fun θ => sigE θ * (V u z θ) ^ 2)
  rw [hR] at h1t
  exact h1t

theorem tendsto_sig1 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (U u)) (hV : Work.Spaces.HkMem α 0 (V u))
    (hA : Work.Spaces.HkMem α 0 (AA u)) (hB : Work.Spaces.HkMem α 0 (BB u)) :
    Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sig1 θ * ψ (dk k) θ
          * (U u z θ * V u z θ * Real.cos (2 * θ)))
      atTop
      (nhds (∫ z in Set.Ioi 0, (wt z) ^ 2
        * ∫ θ in Iθo, sig1 θ * (U u z θ * V u z θ * Real.cos (2 * θ)))) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  let A : ℝ → ℝ → ℝ :=
    fun z θ => (wt z) ^ 2 * (sig1 θ * (U u z θ * V u z θ * Real.cos (2 * θ)))
  have hNint : MeasureTheory.Integrable (fun p : ℝ × ℝ => (wt p.1) ^ 2
      * ((U u p.1 p.2) ^ 2 * (Real.cos (2 * p.2)) ^ 2 * sig2 p.2)) nuQ :=
    integrable_w2_Nterm hS (Work.FTS.EllipticEst.AeI1Fts.N_bound h hV).1 (ntFinAux h hU hV)
  have hVint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (wt p.1) ^ 2 * (V u p.1 p.2) ^ 2 * sigE p.2) nuQ :=
    integrable_w2_sig_sq (Work.FTS.EllipticEst.AeI1Fts.smoothOpen_V hS) hV
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => A p.1 p.2) nuQ := by
    refine (integrable_w2sig1_cos hS hNint hVint).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [A]
    ring
  have hmain := tendsto_integral_cut_pair hInt
  have hL : ∀ k : ℕ, (∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sig1 θ * ψ (dk k) θ
          * (U u z θ * V u z θ * Real.cos (2 * θ)))
      = ∫ p, (χ k p.1 * ψ (dk k) p.2) * A p.1 p.2 ∂nuQ := by
    intro k
    let G : ℝ → ℝ → ℝ := fun z θ => (χ k z * (wt z) ^ 2)
      * (sig1 θ * ψ (dk k) θ * (U u z θ * V u z θ * Real.cos (2 * θ)))
    have hG : MeasureTheory.Integrable (fun p : ℝ × ℝ => G p.1 p.2) nuQ := by
      refine (integrable_cut_pair_mul hInt k).congr
        (Filter.Eventually.of_forall (fun p => ?_))
      dsimp only [G, A]
      ring
    have h1 : (∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sig1 θ * ψ (dk k) θ
          * (U u z θ * V u z θ * Real.cos (2 * θ)))
        = II (fun z θ => G z θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      exact (MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Iθo)
        (χ k z * (wt z) ^ 2)
        (fun θ => sig1 θ * ψ (dk k) θ * (U u z θ * V u z θ * Real.cos (2 * θ)))).symm
    rw [h1, II_eq_integral (g := fun z θ => G z θ) hG]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [G, A]
    ring
  have h1t : Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, χ k z * (wt z) ^ 2
        * ∫ θ in Iθo, sig1 θ * ψ (dk k) θ
          * (U u z θ * V u z θ * Real.cos (2 * θ)))
      atTop (nhds (∫ p, (fun z θ => A z θ) p.1 p.2 ∂nuQ)) :=
    hmain.congr' (Filter.Eventually.of_forall (fun k => (hL k).symm))
  have hR : (∫ p, (fun z θ => A z θ) p.1 p.2 ∂nuQ)
      = ∫ z in Set.Ioi 0, (wt z) ^ 2 * ∫ θ in Iθo, sig1 θ
          * (U u z θ * V u z θ * Real.cos (2 * θ)) := by
    have key : (∫ p, (fun z θ => A z θ) p.1 p.2 ∂nuQ)
        = ∫ z in Set.Ioi 0, ∫ θ in Iθo, A z θ :=
      MeasureTheory.integral_prod (fun p : ℝ × ℝ => (fun z θ => A z θ) p.1 p.2) hInt
    rw [key]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    exact MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict Iθo)
      ((wt z) ^ 2)
      (fun θ => sig1 θ * (U u z θ * V u z θ * Real.cos (2 * θ)))
  rw [hR] at h1t
  exact h1t

end

end Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut
