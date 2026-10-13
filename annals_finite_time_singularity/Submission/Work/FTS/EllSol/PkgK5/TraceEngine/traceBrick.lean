/-
# `TraceEngine.traceBrick` — the weighted `∂_θ D_z` interpolation brick

The target of this file is the estimate (`Ξ = D_z²G + b·D_zG`, `b z = (z-3)/(1+z)`,
`ρ = w(z)²·sin(2θ)^{-η}`)

  `∫∫ ρ (D_z∂_θG)²  ≤  C (∫∫ ρ (D_zG)² + √(∫∫ ρ Ξ² · ∫∫ ρ (∂_θ²G)²))`,

for `G` smooth on the open quadrant whose `D_zG`-slices have vanishing traces at `θ = 0, π/2`.

The proof is the cutoff (`m_k`) route of `PkgK5.InterpTraceCore`:

* for the logarithmic cut-off family `χ` (`CutFam`), with `ψ = D_zG` and the angular functions
  `m = cMK χ k ψ`, `P = cPK χ k ψ`, `A = cAK χ k ψ`, `B = cBK χ k ψ`
  (`m' = 2P`, `P' = A+B`, `P² ≤ m·A`, `m → 0` at both endpoints), the 1-D Agmon inequality
  applied to `√m` gives `(1/200)∫σ·A ≤ 2η·∫σ·m - ∫σ·B`
  (`agmonCutChainPos`, with the degenerate case removed by regularising `m ↦ m + δ·sin²(2θ)`);
* the radial integration by parts `gK_ibp_fts` turns `-∫σ·B` into the pairing of `Ξ` against
  `∂_θ²G`, and Cauchy–Schwarz bounds this by `√(DD'·T) + (K/log(k+2))·√(Z·T)`
  (`cutBkBound`);
* `k → ∞` by dominated convergence (`cutIntegralTendsto`), using the fact that every function
  involved is dominated by one of the four integrable integrands of the statement.

The Clairaut identification `D_z∂_θG = ∂_θ(D_zG)` on the open quadrant (a.e. on `Iz ×ˢ Iθ`) is
what makes the statement's left-hand side the `X` of the engine.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore
import Submission.Work.FTS.EllSol.PkgK5.InterpTrace.mK_hasDerivAt
import Submission.Work.FTS.EllSol.PkgK5.InterpTrace.mK_hasDerivAt_two
import Submission.Work.FTS.EllSol.PkgK5.InterpTrace.cs_mK
import Submission.Work.FTS.EllSol.PkgK5.InterpTrace.continuousOn_mK
import Submission.Work.FTS.EllSol.PkgK5.InterpTrace.sqrt_m_calc
import Submission.Work.FTS.EllSol.PkgK5.InterpTrace.bridge_Iz_interval
import Submission.Work.FTS.EllSol.PkgK5.gK_ibp_fts
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.massK_tendsto_zero
import Submission.Work.EllipticEst.Core.i0Aux.sliceAgmonOpenCore
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.sliceAgmonOpenCoreExplicit
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.agmonCutChainPos
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.cutBkBound
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.cutIntegralTendsto
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.cBK_integrable
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.TraceAux
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.TraceShift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
/-! ## The brick -/

theorem traceBrick : ∃ C : ℝ, 0 < C ∧ ∀ (G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen G →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz G p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 G p.1 p.2
          + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz G p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) →
    (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2)
      ≤ C * ((∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
            * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz G p.1 p.2) ^ 2)
          + Real.sqrt ((∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
                * Work.FTS.EllipticEst.thEta p.2
                * (Work.Spaces.DzIter 2 G p.1 p.2
                    + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz G p.1 p.2) ^ 2)
              * (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
                  * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2))) := by
  refine ⟨400, by norm_num, ?_⟩
  intro G hG htr0 htr1 hX hZ hXi hT
  -- abbreviations
  set ψ : ℝ → ℝ → ℝ := Work.Spaces.Dz G with hψdef
  set X : ℝ := ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2 with hXdef
  set Z : ℝ := ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz G p.1 p.2) ^ 2 with hZdef
  set DD : ℝ := ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 G p.1 p.2
          + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz G p.1 p.2) ^ 2 with hDDdef
  set TT : ℝ := ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2 with hTTdef
  have hψsm : Work.FTS.EllipticEst.SmoothOpen ψ := by rw [hψdef]; exact hG.Dz
  have hψpsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth ψ) := hψsm.pth
  have hZnn : 0 ≤ Z := by
    rw [hZdef]
    refine MeasureTheory.setIntegral_nonneg (measurableSet_Ici.prod measurableSet_Icc)
      (fun p hp => ?_)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hp.2))
      (sq_nonneg _)
  -- the Clairaut transfer
  have hae := ae_pth_sq_eq (G := G) hG
  have hXψ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hX.congr hae
  have hXid : X = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2 := by
    rw [hXdef]
    exact MeasureTheory.integral_congr_ae hae
  -- the cut-off family and the convergence of the truncated functionals
  obtain ⟨χ, K, hχ⟩ := Work.FTS.EllSol.PkgK5.cutFam_exists
  obtain ⟨hAKint, hAKtend⟩ := cutIntegralTendsto (χ := χ) (K := K) hχ
    (F := Work.Spaces.pth ψ) hψpsm hXψ
  obtain ⟨hMKint, hMKtend⟩ := cutIntegralTendsto (χ := χ) (K := K) hχ
    (F := ψ) hψsm hZ
  have hXtend : Filter.Tendsto (fun k : ℕ => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cAK χ k ψ θ)
      Filter.atTop (nhds X) := by
    rw [hXid]
    exact hAKtend
  have hZtend : Filter.Tendsto (fun k : ℕ => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cMK χ k ψ θ)
      Filter.atTop (nhds Z) := by
    have h := hMKtend
    simp only [hψdef] at h
    rw [← hZdef] at h
    exact h
  -- the Agmon hypothesis of the engine
  have hAgmon : ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      (1 / 200) * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
          + 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) :=
    fun f hf h0 h1 h2 h3 h4 => sliceAgmonOpenCoreExplicit f hf h0 h1 h2 h3 h4
  -- the m_k facts
  have hmk : ∀ (k : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
      → HasDerivAt (Work.FTS.EllSol.PkgK5.cMK χ k ψ)
          (2 * Work.FTS.EllSol.PkgK5.cPK χ k ψ θ) θ :=
    fun k θ hθ => Work.FTS.EllSol.PkgK5.InterpTrace.mK_hasDerivAt hχ k hψsm hθ
  have hmP : ∀ (k : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
      → HasDerivAt (Work.FTS.EllSol.PkgK5.cPK χ k ψ)
          (Work.FTS.EllSol.PkgK5.cAK χ k ψ θ + Work.FTS.EllSol.PkgK5.cBK χ k ψ θ) θ :=
    fun k θ hθ => Work.FTS.EllSol.PkgK5.InterpTrace.mK_hasDerivAt_two hχ k hψsm hθ
  have hcont : ∀ k : ℕ, ContinuousOn (fun θ : ℝ => Work.FTS.EllSol.PkgK5.cAK χ k ψ θ
      + Work.FTS.EllSol.PkgK5.cBK χ k ψ θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun k => ((Work.FTS.EllSol.PkgK5.InterpTrace.continuousOn_mK hχ k hψsm).2.2.1).add
      ((Work.FTS.EllSol.PkgK5.InterpTrace.continuousOn_mK hχ k hψsm).2.2.2)
  have hmnn : ∀ (k : ℕ) (θ : ℝ), 0 ≤ Work.FTS.EllSol.PkgK5.cMK χ k ψ θ := by
    intro k θ
    unfold Work.FTS.EllSol.PkgK5.cMK
    refine intervalIntegral.integral_nonneg (Work.FTS.EllSol.PkgK5.cA_le_cB k)
      (fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le (Work.FTS.EllSol.PkgK5.cA_pos k) hu.1
    exact mul_nonneg (mul_nonneg (hχ.bnd k u hu0).1 (sq_nonneg _)) (sq_nonneg _)
  have hAnk : ∀ (k : ℕ) (θ : ℝ), 0 ≤ Work.FTS.EllSol.PkgK5.cAK χ k ψ θ := by
    intro k θ
    unfold Work.FTS.EllSol.PkgK5.cAK
    refine intervalIntegral.integral_nonneg (Work.FTS.EllSol.PkgK5.cA_le_cB k)
      (fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le (Work.FTS.EllSol.PkgK5.cA_pos k) hu.1
    exact mul_nonneg (mul_nonneg (hχ.bnd k u hu0).1 (sq_nonneg _)) (sq_nonneg _)
  have hcs : ∀ (k : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
      → (Work.FTS.EllSol.PkgK5.cPK χ k ψ θ) ^ 2
        ≤ Work.FTS.EllSol.PkgK5.cMK χ k ψ θ * Work.FTS.EllSol.PkgK5.cAK χ k ψ θ :=
    fun k θ hθ => Work.FTS.EllSol.PkgK5.InterpTrace.cs_mK hχ k hψsm hθ
  have htr : ∀ k : ℕ,
      Filter.Tendsto (Work.FTS.EllSol.PkgK5.cMK χ k ψ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
        ∧ Filter.Tendsto (Work.FTS.EllSol.PkgK5.cMK χ k ψ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    intro k
    refine massK_tendsto_zero hχ k hψsm (fun z hz => ?_) (fun z hz => ?_) ?_
    · exact htr0 z hz
    · exact htr1 z hz
    · refine (hXψ.mono_set ?_).congr (Filter.Eventually.of_forall (fun p => by ring))
      intro p hp
      exact ⟨le_trans (le_of_lt (Work.FTS.EllSol.PkgK5.cA_pos k)) (Set.mem_Icc.mp hp.1).1,
        hp.2⟩
  -- σ-integrability of the truncated functionals
  have hAint : ∀ k : ℕ, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Work.FTS.EllSol.PkgK5.cAK χ k ψ θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    fun k => (hAKint k).congr (Filter.Eventually.of_forall (fun θ => mul_comm _ _))
  have hmInt : ∀ k : ℕ, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Work.FTS.EllSol.PkgK5.cMK χ k ψ θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    fun k => (hMKint k).congr (Filter.Eventually.of_forall (fun θ => mul_comm _ _))
  have hBint : ∀ k : ℕ, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Work.FTS.EllSol.PkgK5.cBK χ k ψ θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    fun k => (cBK_integrable (χ := χ) (K := K) hχ k hG hXi hT hZ).congr
      (Filter.Eventually.of_forall (fun θ => mul_comm _ _))
  -- the per-k chain
  have hperk : ∀ k : ℕ, (1 / 200) * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cAK χ k ψ θ)
      ≤ 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cMK χ k ψ θ)
        - ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllSol.PkgK5.cBK χ k ψ θ := by
    intro k
    have h := agmonChainShift hAgmon (hmk k) (hmP k) (hcont k) (hmnn k) (hAnk k) (hcs k)
      (htr k).1 (htr k).2 (hAint k) (hmInt k) (hBint k)
    have e1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllSol.PkgK5.cAK χ k ψ θ
        * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllSol.PkgK5.cAK χ k ψ θ :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    have e2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllSol.PkgK5.cMK χ k ψ θ
        * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllSol.PkgK5.cMK χ k ψ θ :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    have e3 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllSol.PkgK5.cBK χ k ψ θ
        * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllSol.PkgK5.cBK χ k ψ θ :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [e1, e2, e3] at h
    exact h
  -- the radial IBP bound
  have hbk : ∀ k : ℕ, - (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * Work.FTS.EllSol.PkgK5.cBK χ k ψ θ)
      ≤ Real.sqrt (DD * TT) + (K / Real.log ((k : ℝ) + 2)) * Real.sqrt (Z * TT) := by
    intro k
    have h := cutBkBound (χ := χ) (K := K) hχ k hG hXi hT hZ
      (cBK_integrable (χ := χ) (K := K) hχ k hG hXi hT hZ)
    rw [← hDDdef, ← hTTdef, ← hZdef] at h
    exact h
  -- the per-k estimate
  have hbound : ∀ k : ℕ, (1 / 200) * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cAK χ k ψ θ)
      ≤ 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cMK χ k ψ θ)
        + Real.sqrt (DD * TT) + (K / Real.log ((k : ℝ) + 2)) * Real.sqrt (Z * TT) := by
    intro k
    have h1 := hperk k
    have h2 := hbk k
    linarith
  -- the limit
  have hlimR : Filter.Tendsto (fun k : ℕ => 2 * Work.Spaces.eta
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
            * Work.FTS.EllSol.PkgK5.cMK χ k ψ θ)
      + Real.sqrt (DD * TT) + (K / Real.log ((k : ℝ) + 2)) * Real.sqrt (Z * TT))
      Filter.atTop (nhds (2 * Work.Spaces.eta * Z + Real.sqrt (DD * TT))) := by
    have hlog : Filter.Tendsto (fun k : ℕ => K / Real.log ((k : ℝ) + 2))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 2)) Filter.atTop Filter.atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have h2 : Filter.Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 2)) Filter.atTop
          Filter.atTop := Real.tendsto_log_atTop.comp h1
      simpa using h2.const_div_atTop K
    have h := ((hZtend.const_mul (2 * Work.Spaces.eta)).add_const (Real.sqrt (DD * TT))).add
      (hlog.mul_const (Real.sqrt (Z * TT)))
    simpa using h
  have hmain : (1 / 200) * X ≤ 2 * Work.Spaces.eta * Z + Real.sqrt (DD * TT) :=
    le_of_tendsto_of_tendsto (hXtend.const_mul (1 / 200)) hlimR
      (Filter.Eventually.of_forall (fun k => hbound k))
  -- final arithmetic
  have hη : (2 : ℝ) * Work.Spaces.eta = 99 / 50 := by norm_num [Work.Spaces.eta]
  have hsnn : 0 ≤ Real.sqrt (DD * TT) := Real.sqrt_nonneg _
  have h1 : X ≤ 200 * (2 * Work.Spaces.eta * Z + Real.sqrt (DD * TT)) := by linarith
  have h2 : 200 * (2 * Work.Spaces.eta * Z + Real.sqrt (DD * TT))
      ≤ 400 * (Z + Real.sqrt (DD * TT)) := by
    nlinarith [hZnn, hsnn, hη]
  exact le_trans h1 h2

end Work.FTS.EllSol.PkgK5.TraceEngine
