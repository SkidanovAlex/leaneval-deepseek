/-
# `TraceEngine.cutIntegralTendsto` — the cut-off approximation of the weighted `z,θ`-integral

For the logarithmic cut-off family `χ` of `CutFam χ K` (supported in the window
`[cA k, cB k] = [1/(k+1)², (k+1)²]`, increasing to `1` on `(0,∞)`) and a datum `F` whose weighted
square `g p = w(p.1)² · thEta(p.2) · F(p.1,p.2)²` is integrable on the strip
`Iz ×ˢ Iθ = [0,∞) × [0,π/2]`, the *iterated* cut-off integral

  `∫ θ in Iθ, thEta θ · ∫ z in cA k..cB k, χ k z · w(z)² · F(z,θ)²`

converges, as `k → ∞`, to the full integral `∫∫_{Iz ×ˢ Iθ} w² · thEta · F²`, and each of its
`θ`-fibres is integrable.

## The proof

Write `g : ℝ × ℝ → ℝ := fun p => w(p.1)² · thEta(p.2) · F(p.1,p.2)²` and
`hk : ℝ × ℝ → ℝ := fun p => χ k p.1 · g p`, so that both are functions on the strip.

1. **Domination.** `hFi` is integrability of `g`; on the strip `0 ≤ χ k p.1 ≤ 1` a.e. (the
   exceptional set `{p.1 ≤ 0}` is null, because on it `w(p.1)² = 0` at `p.1 = 0` and the
   remainder lies outside `Iz`), and `g ≥ 0` a.e. Hence `‖hk p‖ ≤ g p` a.e. and `hk` is
   integrable (`cutKIntegrable_aux`).
2. **Fibre bridge.** For *every* `θ`, `bridge_Iz_interval` (the cut-off vanishes off its
   support window) rewrites the half-line integral `∫ z in Iz` as the interval integral over
   `cA k .. cB k`, and `integral_const_mul` pulls `thEta θ` out; hence
   `∫ z, hk (z,θ) = thEta θ · ∫ z in cA k..cB k, χ k z · w(z)² · F(z,θ)²`
   (`cutBridgeK_aux`). Fubini (`integral_prod_symm`) turns the product integral
   `∫∫_{Iz ×ˢ Iθ} hk` into the iterated one, giving the bridge identity; the same Fubini identity
   plus `Integrable.integral_prod_right` gives the `θ`-integrability of each fibre.
3. **Limit.** `hk p → g p` a.e. as `k → ∞` (`CutFam.conv` at `p.1 > 0`; at `p.1 = 0` both sides
   vanish), with the integrable dominating function `g`; dominated convergence
   (`tendsto_integral_of_dominated_convergence`) yields `∫∫ hk → ∫∫ g` (`cutLimitK_aux`).

The three pieces are combined in `cutIntegralTendsto`, using the identity of step 2 to replace the
sequence of iterated integrals by the sequence of product integrals.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.PkgK5.InterpTrace.bridge_Iz_interval
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.CutBkAux
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.CutBkAuxB
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.cutAesmFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The measure of the strip `Iz ×ˢ Iθ` is the product of the two restricted measures. -/
private theorem restr_eq_prod :
    volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [Measure.prod_restrict, Measure.volume_eq_prod]

/-- The cut-off product `χ k p.1 · w(p.1)² · thEta(p.2) · F(p.1,p.2)²` is integrable on the strip
as soon as the un-cut product `w(p.1)² · thEta(p.2) · F(p.1,p.2)²` is: it is dominated by it
because `0 ≤ χ k z ≤ 1` for `z > 0` and the exceptional set `{p.1 ≤ 0}` is null. -/
private theorem cutKIntegrable_aux {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hFi : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => χ k p.1 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hp1 : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)), 0 ≤ p.1 :=
    CutBk.ae_of_mem_Izθ (fun p hp => hp.1)
  have hp2 : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      p.2 ∈ Work.Spaces.Iθ :=
    CutBk.ae_of_mem_Izθ (fun p hp => hp.2)
  have hcut : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => χ k p.1)
      (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [restr_eq_prod]
    exact aestronglyMeasurable_of_continuousOn_openQuad (CutBk.continuousOn_cutChi hχ k)
  have hfmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => χ k p.1 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
      (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    have h := hcut.mul hFi.aestronglyMeasurable
    refine h.congr ?_
    filter_upwards with p
    show χ k p.1 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2)
      = χ k p.1 * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2
    ring
  refine MeasureTheory.Integrable.mono' hFi hfmeas ?_
  filter_upwards [hp1, hp2] with p h1 h2
  have hth : 0 ≤ Work.FTS.EllipticEst.thEta p.2 := Work.FTS.EllipticEst.thEta_nonneg h2
  rcases eq_or_lt_of_le h1 with h0 | h0
  · -- `p.1 = 0`: both integrands vanish
    rw [← h0]
    simp [Work.Spaces.w]
  · have hb := hχ.bnd k p.1 h0
    have hg : 0 ≤ (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hth) (sq_nonneg _)
    have hfeq : χ k p.1 * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2
        = χ k p.1 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          * (F p.1 p.2) ^ 2) := by ring
    rw [hfeq, Real.norm_of_nonneg (mul_nonneg hb.1 hg)]
    exact mul_le_of_le_one_left hg hb.2

/-- The fibre bridge: the iterated cut-off integral over `θ` equals the product integral of the
cut-off integrand over the strip, and each `θ`-fibre is integrable. -/
private theorem cutBridgeK_aux {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hIntk : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => χ k p.1 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2)) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2))
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, χ k p.1 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2 := by
  set Hk : ℝ × ℝ → ℝ := fun p => χ k p.1 * (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2 with hHk
  have hInt' : MeasureTheory.Integrable Hk
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← restr_eq_prod]
    exact hIntk
  -- the θ-slice bridge, for every `θ`
  have hbridge : ∀ θ : ℝ, (∫ z, Hk (z, θ) ∂(volume.restrict Work.Spaces.Iz))
      = Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2) := by
    intro θ
    have h1 : (∫ z in Work.Spaces.Iz, Hk (z, θ))
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.thEta θ
            * (χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show χ k z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ * (F z θ) ^ 2
        = Work.FTS.EllipticEst.thEta θ * (χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2)
      ring
    rw [h1, MeasureTheory.integral_const_mul]
    rw [Work.FTS.EllSol.PkgK5.InterpTrace.bridge_Iz_interval hχ k
      (fun z => χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2) (fun z hz hout => by
        have hχz : χ k z = 0 := hχ.supp k z hz
          (hout.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le))
        simp [hχz])]
  have hIntθ : MeasureTheory.Integrable
      (fun θ => ∫ z, Hk (z, θ) ∂(volume.restrict Work.Spaces.Iz))
      (volume.restrict Work.Spaces.Iθ) := hInt'.integral_prod_right
  have hIntθ' : MeasureTheory.Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2))
      (volume.restrict Work.Spaces.Iθ) :=
    hIntθ.congr (Filter.Eventually.of_forall hbridge)
  refine ⟨hIntθ', ?_⟩
  have hfub := MeasureTheory.integral_prod_symm Hk hInt'
  calc (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2))
      = ∫ θ in Work.Spaces.Iθ, ∫ z, Hk (z, θ) ∂(volume.restrict Work.Spaces.Iz) :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun θ => (hbridge θ).symm))
    _ = ∫ p, Hk p ∂((volume.restrict Work.Spaces.Iz).prod
          (volume.restrict Work.Spaces.Iθ)) := hfub.symm
    _ = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, Hk p := by rw [restr_eq_prod]
    _ = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, χ k p.1 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2 := rfl

/-- The dominated convergence step: the product integrals of the cut-off integrands converge to
the full product integral. -/
private theorem cutLimitK_aux {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) {F : ℝ → ℝ → ℝ}
    (hIntk : ∀ k : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => χ k p.1
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hFi : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Filter.Tendsto (fun k : ℕ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        χ k p.1 * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
      Filter.atTop
      (nhds (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)) := by
  have hp1 : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)), 0 ≤ p.1 :=
    CutBk.ae_of_mem_Izθ (fun p hp => hp.1)
  have hp2 : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      p.2 ∈ Work.Spaces.Iθ :=
    CutBk.ae_of_mem_Izθ (fun p hp => hp.2)
  have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  have hconvχ : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun k : ℕ => χ k z) Filter.atTop (nhds 1) := by
    intro z hz
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hχ.conv z hz ε hε
    refine ⟨N, fun k hk => ?_⟩
    have hb := hχ.bnd k z hz
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hN k hk], by linarith [hb.2]⟩
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2) ?_ hFi ?_ ?_
  · intro k
    exact (hIntk k).aestronglyMeasurable
  · intro k
    filter_upwards [hp1, hp2] with p h1 h2
    have hth : 0 ≤ Work.FTS.EllipticEst.thEta p.2 := Work.FTS.EllipticEst.thEta_nonneg h2
    rcases eq_or_lt_of_le h1 with h0 | h0
    · rw [← h0, hw0]
      norm_num
    · have hb := hχ.bnd k p.1 h0
      have hgnn : 0 ≤ (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          * (F p.1 p.2) ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hth) (sq_nonneg _)
      have hfeq : χ k p.1 * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          * (F p.1 p.2) ^ 2
          = χ k p.1 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
            * (F p.1 p.2) ^ 2) := by ring
      rw [hfeq, Real.norm_of_nonneg (mul_nonneg hb.1 hgnn)]
      exact mul_le_of_le_one_left hgnn hb.2
  · filter_upwards [hp1] with p h1
    rcases eq_or_lt_of_le h1 with h0 | h0
    · have hzero : (fun k : ℕ => χ k p.1 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2) = fun _ => 0 := by
        funext k
        rw [← h0, hw0]
        norm_num
      rw [hzero]
      have hgzero : (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          * (F p.1 p.2) ^ 2 = 0 := by
        rw [← h0, hw0]; norm_num
      rw [hgzero]
      exact tendsto_const_nhds
    · have h1' : Filter.Tendsto (fun k : ℕ => χ k p.1
          * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2))
          Filter.atTop (nhds (1 * ((Work.Spaces.w p.1) ^ 2
            * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2))) :=
        (hconvχ p.1 h0).mul_const _
      rw [one_mul] at h1'
      refine h1'.congr (fun k => ?_)
      ring

/-- For the logarithmic cut-off family `χ` of `CutFam χ K` and an integrable weighted square
`w(z)²·thEta(θ)·F(z,θ)²`, the iterated cut-off integrals
`∫ θ in Iθ, thEta θ · ∫ z in cA k..cB k, χ k z · w(z)² · F(z,θ)²` converge, as `k → ∞`, to the
full integral over the strip `Iz ×ˢ Iθ`; each of the `θ`-fibres is integrable. -/
theorem cutIntegralTendsto {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K)
    {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hFi : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    (∀ k : ℕ, MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2)) Work.Spaces.Iθ) ∧
    Filter.Tendsto (fun k : ℕ => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2))
      Filter.atTop
      (nhds (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)) := by
  have hIntk : ∀ k : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => χ k p.1
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := fun k => cutKIntegrable_aux hχ k hFi
  refine ⟨fun k => (cutBridgeK_aux hχ k (hIntk k)).1, ?_⟩
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun k =>
    ((cutBridgeK_aux hχ k (hIntk k)).2).symm) (cutLimitK_aux hχ hIntk hFi)

end Work.FTS.EllSol.PkgK5.TraceEngine
