/-
# `Work.FTS.Apriori.Limit.tendsto_integral_mul_of_tendstoLocUnif` — passing a locally uniform
limit through the pairing `∫∫ f ψ`

The pairing of the chapter integrates a profile against a test function `ψ` (`TestQ ψ`: `C^∞`
on the open quadrant `Qd = (0,∞) × (0,π/2)` with compact support contained in it) with respect
to `Qμ = dz dθ` on the closed quadrant.  This module proves that this pairing is continuous
along a sequence which converges to `f` *locally uniformly on compact subsets of the quadrant*:

  `∫∫ (G n) ψ → ∫∫ f ψ`.

The proof is the elementary estimate

  `|∫∫ (G n - f) ψ| ≤ (sup_{supp ψ} |G n - f|) · ∫∫ |ψ|`,

which is legitimate because `ψ` is supported in a compact subset of `Qd`, where the convergence
is uniform (`TendstoUniformlyOn`), and because `ψ` is continuous with compact support, hence
`L¹(Qμ)`.  No integrability of `G n` or of `f` is needed beyond the continuity on the quadrant
supplied by `SmoothQuad` (it enters only through the compactly supported product `G n · ψ`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Apriori.Limit.Defs
import Submission.Work.FTS.Apriori.Limit.SlotCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)

/-- A `SmoothQuad` function (genuine `C^∞` on `(-1,∞) × (0,π/2)`) is continuous on the open
quadrant `Qd = (0,∞) × (0,π/2)` of the limit chapter. -/
theorem continuousOn_uncurry_of_smoothQuad {F : ℝ → ℝ → ℝ} (hF : SmoothQuad F) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) Qd := by
  refine hF.continuousOn.mono ?_
  intro p hp
  simp only [Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩

/-- A test function is integrable for the product measure `Qμ`. -/
theorem integrable_testQ {ψ : ℝ → ℝ → ℝ} (hψ : TestQ ψ) :
    Integrable (Function.uncurry ψ) Qμ :=
  integrable_of_continuousOn_of_support hψ.1.continuousOn hψ.2.1 hψ.2.2 (subset_tsupport _)

/-- **The pairing passes to the limit** along a sequence converging locally uniformly on the
quadrant: `∫∫ (G n) ψ → ∫∫ f ψ`. -/
theorem tendsto_integral_mul_of_tendstoLocUnif {G : ℕ → ℝ → ℝ → ℝ} {f ψ : ℝ → ℝ → ℝ}
    (hG : ∀ n, Work.FTS.LocData.SmoothQuad (G n)) (hf : Work.FTS.LocData.SmoothQuad f)
    (hψ : Work.FTS.Apriori.Limit.TestQ ψ)
    (hconv : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.Apriori.Limit.Qd →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G n p.1 p.2) (fun p => f p.1 p.2) Filter.atTop K) :
    Filter.Tendsto (fun n => MeasureTheory.integral Work.FTS.Apriori.Limit.Qμ
        (fun p : ℝ × ℝ => G n p.1 p.2 * ψ p.1 p.2)) Filter.atTop
      (nhds (MeasureTheory.integral Work.FTS.Apriori.Limit.Qμ
        (fun p : ℝ × ℝ => f p.1 p.2 * ψ p.1 p.2))) := by
  classical
  -- the closed support of `ψ` is a compact subset of the open quadrant
  have hKcomp : IsCompact (tsupport (Function.uncurry ψ)) := hψ.2.1
  have hKQ : tsupport (Function.uncurry ψ) ⊆ Qd := hψ.2.2
  have hψcont : ContinuousOn (Function.uncurry ψ) Qd := hψ.1.continuousOn
  -- the product of anything on the quadrant with `ψ` is supported in the support of `ψ`
  have hsupp_prod : ∀ H : ℝ → ℝ → ℝ,
      Function.support (fun p : ℝ × ℝ => H p.1 p.2 * ψ p.1 p.2)
        ⊆ tsupport (Function.uncurry ψ) := by
    intro H
    exact (Function.support_mul_subset_right (fun p : ℝ × ℝ => H p.1 p.2)
      (Function.uncurry ψ)).trans (subset_tsupport _)
  -- `ψ` and all the products are integrable
  have hψint : Integrable (Function.uncurry ψ) Qμ := integrable_testQ hψ
  have hψnint : Integrable (fun p : ℝ × ℝ => ‖Function.uncurry ψ p‖) Qμ := hψint.norm
  set A : ℝ := (∫ p, ‖Function.uncurry ψ p‖ ∂Qμ) with hA
  have hAnonneg : 0 ≤ A := by
    rw [hA]
    exact integral_nonneg (fun p => norm_nonneg _)
  have hGint : ∀ n, Integrable (fun p : ℝ × ℝ => G n p.1 p.2 * ψ p.1 p.2) Qμ := fun n =>
    integrable_of_continuousOn_of_support
      ((continuousOn_uncurry_of_smoothQuad (hG n)).mul hψcont) hKcomp hKQ (hsupp_prod (G n))
  have hfint : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * ψ p.1 p.2) Qμ :=
    integrable_of_continuousOn_of_support
      ((continuousOn_uncurry_of_smoothQuad hf).mul hψcont) hKcomp hKQ (hsupp_prod f)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := ε / (2 * (A + 1)) with hε'def
  have hA1 : 0 < A + 1 := by linarith
  have hε'pos : 0 < ε' := by
    rw [hε'def]
    positivity
  -- uniform convergence on the (compact) support of `ψ`
  have hunif : ∀ᶠ n in Filter.atTop, ∀ p ∈ tsupport (Function.uncurry ψ),
      dist (f p.1 p.2) (G n p.1 p.2) < ε' :=
    (Metric.tendstoUniformlyOn_iff.mp (hconv _ hKcomp hKQ)) ε' hε'pos
  filter_upwards [hunif] with n hn
  -- pointwise bound on the integrand
  have hpointwise : ∀ p : ℝ × ℝ,
      ‖(G n p.1 p.2 - f p.1 p.2) * ψ p.1 p.2‖ ≤ ε' * ‖Function.uncurry ψ p‖ := by
    intro p
    by_cases hp : p ∈ tsupport (Function.uncurry ψ)
    · have h1 : ‖G n p.1 p.2 - f p.1 p.2‖ ≤ ε' := by
        have h2 := hn p hp
        rw [dist_eq_norm, norm_sub_rev] at h2
        exact h2.le
      calc ‖(G n p.1 p.2 - f p.1 p.2) * ψ p.1 p.2‖
          = ‖G n p.1 p.2 - f p.1 p.2‖ * ‖ψ p.1 p.2‖ := norm_mul _ _
        _ ≤ ε' * ‖ψ p.1 p.2‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ε' * ‖Function.uncurry ψ p‖ := rfl
    · have hz : ψ p.1 p.2 = 0 := by
        by_contra h
        exact hp (subset_tsupport _ (by simpa [Function.mem_support, Function.uncurry] using h))
      rw [hz, mul_zero, norm_zero]
      positivity
  -- integrability of the difference of the two integrands
  have hdiffint : Integrable (fun p : ℝ × ℝ => (G n p.1 p.2 - f p.1 p.2) * ψ p.1 p.2) Qμ :=
    integrable_of_continuousOn_of_support
      (((continuousOn_uncurry_of_smoothQuad (hG n)).sub
        (continuousOn_uncurry_of_smoothQuad hf)).mul hψcont) hKcomp hKQ
      (hsupp_prod (fun z θ => G n z θ - f z θ))
  -- the difference of the integrals is the integral of the difference
  have hsub : ∫ p, G n p.1 p.2 * ψ p.1 p.2 ∂Qμ - ∫ p, f p.1 p.2 * ψ p.1 p.2 ∂Qμ
      = ∫ p, (G n p.1 p.2 - f p.1 p.2) * ψ p.1 p.2 ∂Qμ := by
    rw [← MeasureTheory.integral_sub (hGint n) hfint]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))
  -- the main estimate
  have hmain : ‖∫ p, G n p.1 p.2 * ψ p.1 p.2 ∂Qμ
      - ∫ p, f p.1 p.2 * ψ p.1 p.2 ∂Qμ‖ ≤ ε' * A := by
    rw [hsub]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    calc ∫ p, ‖(G n p.1 p.2 - f p.1 p.2) * ψ p.1 p.2‖ ∂Qμ
        ≤ ∫ p, ε' * ‖Function.uncurry ψ p‖ ∂Qμ :=
          MeasureTheory.integral_mono hdiffint.norm (hψnint.const_mul ε')
            (fun p => hpointwise p)
      _ = ε' * A := by rw [MeasureTheory.integral_const_mul, ← hA]
  -- `ε' * A < ε`
  have hε'lt : ε' * A < ε := by
    have h1 : ε' * A ≤ ε' * (A + 1) := mul_le_mul_of_nonneg_left (by linarith) hε'pos.le
    have h2 : ε' * (A + 1) = ε / 2 := by
      rw [hε'def]
      field_simp
    linarith
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hmain hε'lt

end Work.FTS.Apriori.Limit
