/-
# `Work.FTS.OpenPkg.HkNorm_le_of_tendstoLocUnif_open`

Lower semicontinuity of the `ℋ⁴`-norm under locally uniform convergence, in the
**open-quadrant** class of the migration:

  `|f|_{ℋ⁴} ≤ B` whenever `f` is `C^∞` on the open quadrant `Qd = (0,∞) × (0,π/2)` (the class
  `Work.FTS.EllipticEst.SmoothOpen`), `G n` are profiles of the frozen regular class
  `RegQ α 4` with `|G n|_{ℋ⁴} ≤ B`, and `G n → f` uniformly on the compact subsets of `Qd`.

This is `Work.FTS.Apriori.Limit.HkNorm_le_of_tendstoLocUnif` with the hypothesis
`Work.FTS.LocData.SmoothQuad f` (genuine `C^∞` on the larger strip `z > -1`, which is *not*
available for the cut-off profile of the route, cf. `Submission/Work/FTS/OpenPkg/Defs.lean`)
replaced by its open-quadrant part.  Nothing in the argument uses smoothness beyond `Qd`:

* the slots `slot α ji g = mixed j i g · slotWeight α ji` are continuous on `Qd` as soon as
  `g` is `C^∞` there (the operator chains `contDiffOn_mixed`, `contDiffOn_DzIter`, … of
  `Work.FTS.LocData.SmoothChain` are parametrised by an arbitrary *open* set);
* the integration by parts `∫ (mixed j i g) ψ = ∫ g (adjMixed (j,i) ψ)` and the locally
  uniform limit `∫ (G n) ψ → ∫ f ψ` only use `ContDiffOn` on `Qd` and `TestQ ψ`;
* Fatou/Tonelli only use continuity of the `ℋ⁴`-integrand on `Qd`.

The open-quadrant variants of the auxiliary lemmas of the limit chapter are collected here
(`continuousOn_slot_of_contDiffOn`, `HksqCut_eq_sum_slot_of_contDiffOn`,
`integral_mixed_mul_adjMixed_of_contDiffOn`,
`tendsto_integral_mul_of_tendstoLocUnif_of_contDiffOn`,
`continuousOn_HkIntegrand_four_of_contDiffOn`, `ofReal_HkSq_le_lintegral_of_contDiffOn`,
`lintegral_HkIntegrand_le_iSup_HksqCut_of_contDiffOn`), so that the whole chapter is
available in the open-quadrant class.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Apriori.Limit.HkNorm_le_of_tendstoLocUnif
import Submission.Work.FTS.OpenPkg.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Work.FTS.Apriori.Limit

/-! ## The bridge from the closed strip to the open quadrant -/

/-- `SmoothQuad` (`C^∞` on the strip `-1 < z`, `0 < θ < π/2`) restricted to the open quadrant
`Qd` of the limit chapter. -/
theorem contDiffOn_Qd_of_smoothQuad {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd :=
  hf.mono (by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_Qd_iff.mp hp
    exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr (by linarith), Set.mem_Ioo.mpr ⟨h2, h3⟩⟩)

/-! ## The slot functions in the open-quadrant class -/

/-- The weighted slot `slot α ji f` is continuous on the open quadrant as soon as `f` is `C^∞`
there. -/
theorem continuousOn_slot_of_contDiffOn {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) (α : ℝ)
    (ji : ℕ × ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => slot α ji f p.1 p.2) Qd := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed ji.1 ji.2 f p.1 p.2) Qd :=
    (Work.FTS.LocData.contDiffOn_mixed isOpen_Qd hf ji.1 ji.2).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => slotWeight α ji p.1 p.2) Qd := by
    by_cases hi : ji.2 = 0
    · have hfun : (fun p : ℝ × ℝ => slotWeight α ji p.1 p.2)
          = fun p : ℝ × ℝ => Work.Spaces.w p.1
              / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := by
        funext p; simp [slotWeight, hi]
      rw [hfun]
      exact contDiffOn_w_Qd.continuousOn.div (contDiffOn_sin_rpow_Qd _).continuousOn
        (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Qd hp) _))
    · have hfun : (fun p : ℝ × ℝ => slotWeight α ji p.1 p.2)
          = fun p : ℝ × ℝ => Work.Spaces.w p.1
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
        funext p; simp [slotWeight, hi, Work.Spaces.Wt, Work.Spaces.wTheta]
      rw [hfun]
      exact contDiffOn_w_Qd.continuousOn.mul (contDiffOn_sin_rpow_Qd _).continuousOn
  have h3 : (fun p : ℝ × ℝ => slot α ji f p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.mixed ji.1 ji.2 f p.1 p.2 * slotWeight α ji p.1 p.2 := by
    funext p; rfl
  rw [h3]
  exact h1.mul h2

/-- The cut-off `ℋ⁴`-energy is the sum of the cut-off energies of the individual slots, for a
profile smooth on the open quadrant. -/
theorem HksqCut_eq_sum_slot_of_contDiffOn {α : ℝ} {f η : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) (hη : TestQ η) :
    HksqCut α f η
      = ∑ ji ∈ activeSlots, ∫ p, (slot α ji f p.1 p.2) ^ 2 * η p.1 p.2 ∂Qμ := by
  have hpt : ∀ p : ℝ × ℝ, Work.Spaces.HkIntegrand α 4 f p.1 p.2 * η p.1 p.2
      = ∑ ji ∈ activeSlots, (slot α ji f p.1 p.2) ^ 2 * η p.1 p.2 := by
    intro p
    rw [HkIntegrand_eq_sum_slot, Finset.sum_mul]
  have hint : ∀ ji ∈ activeSlots,
      Integrable (fun p : ℝ × ℝ => (slot α ji f p.1 p.2) ^ 2 * η p.1 p.2) Qμ := by
    intro ji _
    refine integrable_of_continuousOn_of_support
      (((continuousOn_slot_of_contDiffOn hf α ji).pow 2).mul hη.1.continuousOn) hη.2.1 hη.2.2 ?_
    exact (Function.support_mul_subset_right _ _).trans (subset_tsupport _)
  rw [HksqCut]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact MeasureTheory.integral_finsetSum _ (fun ji hji => hint ji hji)

/-! ## Integration by parts in the open-quadrant class -/

/-- The adjointness of `mixed j i = D_z^j D_θ^i` for a profile smooth on the open quadrant. -/
theorem integral_mixed_mul_adjMixed_of_contDiffOn {g ψ : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd) (hψ : TestQ ψ)
    (j i : ℕ) :
    (∫ p, Work.Spaces.mixed j i g p.1 p.2 * ψ p.1 p.2 ∂Qμ)
      = ∫ p, g p.1 p.2 * adjMixed (j, i) ψ p.1 p.2 ∂Qμ := by
  have h1 := integral_DzIter_mul_adjDzIter
    (u := Work.Spaces.DthIter i g) (v := ψ)
    (Work.FTS.LocData.contDiffOn_DthIter isOpen_Qd hg i) hψ j
  have h2 := integral_DthIter_mul_adjDthIter (u := g) (v := adjDzIter j ψ) hg
    (TestQ_adjDzIter j hψ) i
  exact h1.trans h2

/-! ## Passing a locally uniform limit through the pairing -/

/-- **The pairing passes to the limit** along a sequence converging locally uniformly on the
quadrant, for profiles smooth on the open quadrant. -/
theorem tendsto_integral_mul_of_tendstoLocUnif_of_contDiffOn {G : ℕ → ℝ → ℝ → ℝ}
    {f ψ : ℝ → ℝ → ℝ}
    (hG : ∀ n, ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (G n)) Qd)
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd)
    (hψ : TestQ ψ)
    (hconv : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Qd →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G n p.1 p.2) (fun p => f p.1 p.2) Filter.atTop K) :
    Filter.Tendsto (fun n => ∫ p, G n p.1 p.2 * ψ p.1 p.2 ∂Qμ) Filter.atTop
      (nhds (∫ p, f p.1 p.2 * ψ p.1 p.2 ∂Qμ)) := by
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
      (((hG n).continuousOn).mul hψcont) hKcomp hKQ (hsupp_prod (G n))
  have hfint : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * ψ p.1 p.2) Qμ :=
    integrable_of_continuousOn_of_support
      (hf.continuousOn.mul hψcont) hKcomp hKQ (hsupp_prod f)
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
      (((hG n).continuousOn.sub hf.continuousOn).mul hψcont) hKcomp hKQ
      (hsupp_prod (fun z θ => G n z θ - f z θ))
  -- the difference of the integrals is the integral of the difference
  have hsub : ∫ p, G n p.1 p.2 * ψ p.1 p.2 ∂Qμ - ∫ p, f p.1 p.2 * ψ p.1 p.2 ∂Qμ
      = ∫ p, (G n p.1 p.2 - f p.1 p.2) * ψ p.1 p.2 ∂Qμ := by
    rw [← MeasureTheory.integral_sub (hGint n) hfint]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))
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

/-! ## Continuity of the `ℋ⁴`-integrand in the open-quadrant class -/

/-- The uncurried `ℋ⁴`-integrand is continuous on the open quadrant as soon as the profile is
`C^∞` there. -/
theorem continuousOn_HkIntegrand_four_of_contDiffOn {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2) Qd := by
  rw [show (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      = fun p : ℝ × ℝ => ∑ ji ∈ activeSlots, (slot α ji f p.1 p.2) ^ 2 from
    funext (fun p => HkIntegrand_eq_sum_slot α f p.1 p.2)]
  exact continuousOn_finsetSum _ (fun ji _ => (continuousOn_slot_of_contDiffOn hf α ji).pow 2)

/-! ## `ofReal` of `HkSq` against the `lintegral` of the integrand -/

/-- `ofReal (HkSq α 4 f)` is dominated by the `lintegral` of `ofReal (HkIntegrand α 4 f)`, for a
profile smooth on the open quadrant. -/
theorem ofReal_HkSq_le_lintegral_of_contDiffOn {α : ℝ} (f : ℝ → ℝ → ℝ)
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) :
    ENNReal.ofReal (Work.Spaces.HkSq α 4 f)
      ≤ MeasureTheory.lintegral Qμ
          (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2)) := by
  -- The integrand is a sum of squares, hence nonnegative.
  have hg : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2) Qd :=
    continuousOn_HkIntegrand_four_of_contDiffOn hf α
  have hmeas : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2)) Qμ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).aemeasurable
  -- Tonelli: the `lintegral` over the product measure is the iterated `lintegral`.
  have hton : MeasureTheory.lintegral Qμ
        (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ) := by
    rw [show Qμ = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      from rfl]
    exact MeasureTheory.lintegral_prod _ hmeas
  calc ENNReal.ofReal (Work.Spaces.HkSq α 4 f)
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := rfl
    _ ≤ ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) :=
        ofReal_setIntegral_le_lintegral measurableSet_Ici
          (fun z _ => integral_nonneg fun θ => hg z θ)
    _ ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ) :=
        lintegral_mono fun z =>
          ofReal_setIntegral_le_lintegral measurableSet_Icc (fun θ _ => hg z θ)
    _ = MeasureTheory.lintegral Qμ
          (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2)) :=
        hton.symm

/-! ## Fatou for an exhausting family of cut-offs -/

/-- Fatou's lemma for an exhausting family of cut-offs, for a profile smooth on the open
quadrant. -/
theorem lintegral_HkIntegrand_le_iSup_HksqCut_of_contDiffOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd)
    {η : ℕ → ℝ → ℝ → ℝ} (hη : ∀ k, TestQ (η k)) (h0 : ∀ k z θ, 0 ≤ η k z θ)
    (htend : ∀ z θ, (z, θ) ∈ Qd →
      Filter.Tendsto (fun k => η k z θ) Filter.atTop (nhds 1)) :
    MeasureTheory.lintegral Qμ
        (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2))
      ≤ ⨆ k, ENNReal.ofReal (HksqCut α f (η k)) := by
  have hG : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2) Qd :=
    continuousOn_HkIntegrand_four_of_contDiffOn hf α
  have hGnn : ∀ p : ℝ × ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f p.1 p.2 :=
    fun p => Work.Spaces.HkIntegrand_nonneg α 4 f p.1 p.2
  have hηcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ => η k p.1 p.2) Qd :=
    fun k => (hη k).1.continuousOn
  have hint : ∀ k, Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 4 f p.1 p.2 * η k p.1 p.2) Qμ := fun k =>
    integrable_of_continuousOn_of_support (hG.mul (hηcont k)) (hη k).2.1 (hη k).2.2
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport _))
  have hmain := lintegral_le_iSup_integral_mul_of_tendsto_one
    (G := fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
    hG hGnn hη (fun k p => h0 k p.1 p.2)
    (fun p hp => htend p.1 p.2 hp)
    (fun p hp => by rw [hp]; exact Work.Spaces.HkIntegrand_zero_z α 4 f p.2)
    hint
  simpa only [HksqCut] using hmain

/-! ## The target -/

theorem HkNorm_le_of_tendstoLocUnif_open {α B : ℝ} {G : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α)
    (hG : ∀ n, Work.FTS.Nonlin.RegQ α 4 (G n)) (hB : ∀ n, Work.FTS.Nonlin.Xn α (G n) ≤ B)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hconv : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.Construction.Qd →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G n p.1 p.2) (fun p => f p.1 p.2) atTop K) :
    Work.FTS.Nonlin.Xn α f ≤ B := by
  classical
  have hGsm : ∀ n, Work.FTS.LocData.SmoothQuad (G n) := fun n => (hG n).1
  have hGQ : ∀ n, ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (G n)) Qd :=
    fun n => contDiffOn_Qd_of_smoothQuad (hGsm n)
  have hGmem : ∀ n, Work.Spaces.HkMem α 4 (G n) := fun n => (hG n).2.1
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd := hf
  have hconvQ : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Qd →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G n p.1 p.2) (fun p => f p.1 p.2) atTop K :=
    fun K hK hKQ => hconv K hK hKQ
  have hBnn : 0 ≤ B := le_trans (Work.Spaces.HkNorm_nonneg α 4 (G 0)) (hB 0)
  have hGsq : ∀ n, Work.Spaces.HkSq α 4 (G n) ≤ B ^ 2 := by
    intro n
    have h1 : Real.sqrt (Work.Spaces.HkSq α 4 (G n)) ≤ B := hB n
    have h2 : 0 ≤ Work.Spaces.HkSq α 4 (G n) := Work.Spaces.HkSq_nonneg α 4 (G n)
    have h3 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 4 (G n)) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt h2]
  obtain ⟨η, hηT, hη01, hηtend⟩ := exists_test_cutoff
  -- ### the bound at each cut-off
  have hkey : ∀ k, HksqCut α f (η k) ≤ B ^ 2 := by
    intro k
    have hcut_n : ∀ n, HksqCut α (G n) (η k) ≤ B ^ 2 := fun n =>
      le_trans (HksqCut_le_HkSq (hGsm n) (hGmem n) (hηT k) (fun z θ => (hη01 k z θ).1)
        (fun z θ => (hη01 k z θ).2)) (hGsq n)
    -- ### weak convergence of each slot
    have hslot : ∀ ji ∈ activeSlots, Filter.Tendsto
        (fun n => ∫ p, slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2 ∂Qμ)
        Filter.atTop (nhds (∫ p, (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2 ∂Qμ)) := by
      intro ji _
      set Ψ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.mixed ji.1 ji.2 f z θ
        * (slotWeight α ji z θ) ^ 2 * η k z θ with hΨdef
      have hΨT : TestQ Ψ := by
        have hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun z θ =>
            Work.Spaces.mixed ji.1 ji.2 f z θ * (slotWeight α ji z θ) ^ 2)) Qd :=
          (Work.FTS.LocData.contDiffOn_mixed isOpen_Qd hfd ji.1 ji.2).mul
            (contDiffOn_slotWeight_sq α ji.1 ji.2)
        simpa [hΨdef] using (TestQ_mul_adjMixed (hηT k)).1 _ hg
      have hΨadjT : TestQ (adjMixed ji Ψ) := (TestQ_mul_adjMixed hΨT).2 ji.1 ji.2
      have hmain : Filter.Tendsto (fun n => ∫ p,
            Work.Spaces.mixed ji.1 ji.2 (G n) p.1 p.2 * Ψ p.1 p.2 ∂Qμ)
          Filter.atTop (nhds (∫ p, f p.1 p.2 * adjMixed ji Ψ p.1 p.2 ∂Qμ)) := by
        have hibp : ∀ n, (∫ p, Work.Spaces.mixed ji.1 ji.2 (G n) p.1 p.2 * Ψ p.1 p.2 ∂Qμ)
            = ∫ p, G n p.1 p.2 * adjMixed ji Ψ p.1 p.2 ∂Qμ := fun n =>
          integral_mixed_mul_adjMixed_of_contDiffOn (hGQ n) hΨT ji.1 ji.2
        rw [show (fun n => ∫ p, Work.Spaces.mixed ji.1 ji.2 (G n) p.1 p.2 * Ψ p.1 p.2 ∂Qμ)
            = fun n => ∫ p, G n p.1 p.2 * adjMixed ji Ψ p.1 p.2 ∂Qμ from funext hibp]
        exact tendsto_integral_mul_of_tendstoLocUnif_of_contDiffOn hGQ hfd hΨadjT hconvQ
      have hgoal : (∫ p, f p.1 p.2 * adjMixed ji Ψ p.1 p.2 ∂Qμ)
          = ∫ p, (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2 ∂Qμ := by
        rw [← integral_mixed_mul_adjMixed_of_contDiffOn hfd hΨT ji.1 ji.2]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        show Work.Spaces.mixed ji.1 ji.2 f p.1 p.2 * Ψ p.1 p.2
          = (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2
        rw [hΨdef]
        simp only [slot]
        ring
      rw [show (fun n => ∫ p, slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2
              * η k p.1 p.2 ∂Qμ)
          = fun n => ∫ p, Work.Spaces.mixed ji.1 ji.2 (G n) p.1 p.2 * Ψ p.1 p.2 ∂Qμ from
        funext (fun n => by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
          show slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2
            = Work.Spaces.mixed ji.1 ji.2 (G n) p.1 p.2 * Ψ p.1 p.2
          rw [hΨdef]
          simp only [slot]
          ring),
        show (∫ p, (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2 ∂Qμ)
          = ∫ p, f p.1 p.2 * adjMixed ji Ψ p.1 p.2 ∂Qμ from hgoal.symm]
      exact hmain
    have hsum_lim : Filter.Tendsto
        (fun n => ∑ ji ∈ activeSlots, ∫ p,
          slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2 ∂Qμ)
        Filter.atTop (nhds (∑ ji ∈ activeSlots, ∫ p,
          (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2 ∂Qμ)) :=
      tendsto_finsetSum _ hslot
    rw [← HksqCut_eq_sum_slot_of_contDiffOn hfd (hηT k)] at hsum_lim
    -- ### the elementary bound for each `n`
    have hsupp_gen : ∀ (F : ℝ × ℝ → ℝ), (∀ p, η k p.1 p.2 = 0 → F p = 0) →
        Function.support F ⊆ tsupport (Function.uncurry (η k)) := by
      intro F hF p hp
      exact subset_tsupport _ (fun h => hp (hF p h))
    have hprodint : ∀ (g : ℝ → ℝ → ℝ),
        ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd → ∀ ji : ℕ × ℕ,
        Integrable (fun p : ℝ × ℝ => slot α ji g p.1 p.2 * slot α ji f p.1 p.2
          * η k p.1 p.2) Qμ := by
      intro g hgsm ji
      refine integrable_of_continuousOn_of_support ?_ (hηT k).2.1 (hηT k).2.2 ?_
      · exact ((continuousOn_slot_of_contDiffOn hgsm α ji).mul
          (continuousOn_slot_of_contDiffOn hfd α ji)).mul (hηT k).1.continuousOn
      · exact hsupp_gen _ (fun p h => by simp [h])
    have hsqint : ∀ (g : ℝ → ℝ → ℝ),
        ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd → ∀ ji : ℕ × ℕ,
        Integrable (fun p : ℝ × ℝ => (slot α ji g p.1 p.2) ^ 2 * η k p.1 p.2) Qμ := by
      intro g hgsm ji
      refine integrable_of_continuousOn_of_support ?_ (hηT k).2.1 (hηT k).2.2 ?_
      · exact ((continuousOn_slot_of_contDiffOn hgsm α ji).pow 2).mul (hηT k).1.continuousOn
      · exact hsupp_gen _ (fun p h => by simp [h])
    have hsqsum : ∀ (g : ℝ → ℝ → ℝ),
        ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd →
        (∫ p, ∑ ji ∈ activeSlots, (slot α ji g p.1 p.2) ^ 2 * η k p.1 p.2 ∂Qμ)
          = HksqCut α g (η k) := by
      intro g hgsm
      rw [MeasureTheory.integral_finsetSum _ (fun ji _ => hsqint g hgsm ji),
        HksqCut_eq_sum_slot_of_contDiffOn hgsm (hηT k)]
    have hbnd : ∀ n, (∑ ji ∈ activeSlots, ∫ p,
          slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2 ∂Qμ)
        ≤ (1 / 2) * HksqCut α (G n) (η k) + (1 / 2) * HksqCut α f (η k) := by
      intro n
      have hint1 : Integrable (fun p : ℝ × ℝ => ∑ ji ∈ activeSlots,
          slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2) Qμ := by
        refine integrable_of_continuousOn_of_support ?_ (hηT k).2.1 (hηT k).2.2 ?_
        · exact continuousOn_finsetSum _ (fun ji _ =>
            ((continuousOn_slot_of_contDiffOn (hGQ n) α ji).mul
              (continuousOn_slot_of_contDiffOn hfd α ji)).mul (hηT k).1.continuousOn)
        · exact hsupp_gen _ (fun p h => by simp [h])
      have hint2a : Integrable (fun p : ℝ × ℝ => (1 / 2) *
          (∑ ji ∈ activeSlots, (slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)) Qμ := by
        refine integrable_of_continuousOn_of_support ?_ (hηT k).2.1 (hηT k).2.2 ?_
        · exact ContinuousOn.mul continuousOn_const (continuousOn_finsetSum _
            (fun ji _ => ((continuousOn_slot_of_contDiffOn (hGQ n) α ji).pow 2).mul
              (hηT k).1.continuousOn))
        · exact hsupp_gen _ (fun p h => by simp [h])
      have hint2b : Integrable (fun p : ℝ × ℝ => (1 / 2) *
          (∑ ji ∈ activeSlots, (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2)) Qμ := by
        refine integrable_of_continuousOn_of_support ?_ (hηT k).2.1 (hηT k).2.2 ?_
        · exact ContinuousOn.mul continuousOn_const (continuousOn_finsetSum _
            (fun ji _ => ((continuousOn_slot_of_contDiffOn hfd α ji).pow 2).mul
              (hηT k).1.continuousOn))
        · exact hsupp_gen _ (fun p h => by simp [h])
      have hsum_eq : (∑ ji ∈ activeSlots, ∫ p,
            slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2 ∂Qμ)
          = ∫ p, ∑ ji ∈ activeSlots, (slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2
              * η k p.1 p.2) ∂Qμ :=
        (MeasureTheory.integral_finsetSum _ (fun ji _ => hprodint (G n) (hGQ n) ji)).symm
      rw [hsum_eq]
      have hamgm : ∀ᵐ p ∂Qμ, (∑ ji ∈ activeSlots,
            slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2)
          ≤ (1 / 2) * (∑ ji ∈ activeSlots, (slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)
            + (1 / 2) * (∑ ji ∈ activeSlots, (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2) := by
        refine Filter.Eventually.of_forall (fun p => ?_)
        have hs : 0 ≤ η k p.1 p.2 := (hη01 k p.1 p.2).1
        have hterm : ∀ ji ∈ activeSlots,
            slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2
              ≤ (1 / 2) * ((slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)
                + (1 / 2) * ((slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2) := by
          intro ji _
          nlinarith [sq_nonneg (slot α ji (G n) p.1 p.2 - slot α ji f p.1 p.2), hs]
        calc (∑ ji ∈ activeSlots,
              slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2)
            ≤ ∑ ji ∈ activeSlots, ((1 / 2) * ((slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)
                + (1 / 2) * ((slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2)) :=
              Finset.sum_le_sum hterm
          _ = (1 / 2) * (∑ ji ∈ activeSlots, (slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)
                + (1 / 2) * (∑ ji ∈ activeSlots,
                    (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hmono : (∫ p, ∑ ji ∈ activeSlots, (slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2
              * η k p.1 p.2) ∂Qμ)
          ≤ ∫ p, ((1 / 2) * (∑ ji ∈ activeSlots,
                (slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)
              + (1 / 2) * (∑ ji ∈ activeSlots,
                (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2)) ∂Qμ :=
        integral_mono_ae hint1 (Integrable.add hint2a hint2b) hamgm
      refine le_trans hmono ?_
      rw [MeasureTheory.integral_add hint2a hint2b, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, hsqsum (G n) (hGQ n), hsqsum f hfd]
    have hlim_bound : HksqCut α f (η k) ≤ (1 / 2) * B ^ 2 + (1 / 2) * HksqCut α f (η k) :=
      le_of_tendsto' hsum_lim (fun n => le_trans (hbnd n) (by linarith [hcut_n n]))
    linarith
  -- ### pass to the limit in the cut-off
  have hlin : (∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2) ∂Qμ)
      ≤ ENNReal.ofReal (B ^ 2) := by
    refine le_trans (lintegral_HkIntegrand_le_iSup_HksqCut_of_contDiffOn hfd hηT
      (fun k z θ => (hη01 k z θ).1) hηtend) ?_
    refine iSup_le (fun k => ?_)
    exact ENNReal.ofReal_le_ofReal (hkey k)
  have hsq : Work.Spaces.HkSq α 4 f ≤ B ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg B)).mp
      (le_trans (ofReal_HkSq_le_lintegral_of_contDiffOn f hfd) hlin)
  calc Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
    _ ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hsq
    _ = B := Real.sqrt_sq hBnn

end Work.FTS.OpenPkg
