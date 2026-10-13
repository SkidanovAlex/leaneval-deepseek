/-
# Local integrability of the two-dimensional mollification integrand

`Work.FTS.EllSol.EllPkgAux.Hxy (Gquad G)` is the uncurried integrand `(t,s) ↦ Qext (Gquad G) (e^t) s`
of the doubly-mollified datum `zmoll (Gquad G) δ ε`.  This file proves that it is locally
integrable for Lebesgue measure on `ℝ × ℝ`.

The proof is a *domination* argument, using the two hypotheses supplied by the caller:

* `hdom` bounds the slice on the open quadrant by `MG G`, and
* `hint` says that `MG G` is locally integrable on `(0, ∞)`.

The doubly-odd extension `Qext` reflects the angular variable into `(0, π/2)`, so that
`|Qext (Gquad G) (e^t) s| ≤ MG G (e^t)` for *every* `s`.  Hence it suffices to see that
`p ↦ MG G (exp p.1)` is locally integrable for the planar Lebesgue measure.  Since `MG G` is
integrable on compact subintervals of `(0, ∞)` and `t ↦ exp t` is a diffeomorphism `ℝ ≃ (0,∞)`
whose Jacobian `exp t` is bounded below by `exp a > 0` on `(a,b)`, the substitution rule
(`intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg`) gives the claim on each
interval `(a,b)`; Fubini for product measures then upgrades this to `ℝ × ℝ`.

Measurability of `Qext (Gquad G) (e^·) ·` is obtained by splitting the angular variable into the
three open intervals `(0, π/2)`, `(-π/2, 0)` and `(π/2, π)` (on the complement the integrand
vanishes); on each piece the integrand is a reflected slice of `G`, continuous on an open set
because `G` is `C^∞` on the open quadrant (`SmoothOpen G`).
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol.PkgK5.K5c

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

set_option linter.unusedVariables false

theorem Hxy_quad_locallyIntegrable (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    (hdom : ∀ w : ℝ, 0 < w → ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |G w τ| ≤ Work.FTS.EllSol.EllPkgAux.MG G w)
    (hint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Work.FTS.EllSol.EllPkgAux.MG G) (Set.Ioo a b)) :
    MeasureTheory.LocallyIntegrable
      (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G)) MeasureTheory.volume := by
  -- `MG G` is nonnegative.
  have hMGnn : ∀ w : ℝ, 0 ≤ Work.FTS.EllSol.EllPkgAux.MG G w := by
    intro w
    have h1 : (0 : ℝ) ≤ |G w (Real.pi / 4)| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ |Work.Spaces.pth G w (Real.pi / 4)| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G w) := Real.sqrt_nonneg _
    simp only [Work.FTS.EllSol.EllPkgAux.MG]
    linarith
  -- The quadrant-killed datum is dominated by `MG G` on the positive half line.
  have hGq : ∀ z : ℝ, 0 < z → ∀ τ : ℝ, |Work.FTS.EllSol.EllPkgAux.Gquad G z τ|
      ≤ Work.FTS.EllSol.EllPkgAux.MG G z := by
    intro z hz τ
    by_cases hτ : τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · rw [Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_left hτ]
      exact hdom z hz τ hτ
    · rw [Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_right hτ, abs_zero]
      exact hMGnn z
  -- The doubly-odd extension is dominated by `MG G` as well.
  have hQb : ∀ z : ℝ, 0 < z → ∀ s : ℝ,
      |Qext (Work.FTS.EllSol.EllPkgAux.Gquad G) z s| ≤ Work.FTS.EllSol.EllPkgAux.MG G z := by
    intro z hz s
    by_cases h1 : 0 ≤ s ∧ s ≤ Real.pi / 2
    · rw [Qext, ite_eq_left h1]
      exact hGq z hz s
    · rw [Qext, ite_eq_right h1]
      by_cases h2 : s < 0
      · rw [ite_eq_left h2, abs_neg]
        exact hGq z hz (-s)
      · rw [ite_eq_right h2, abs_neg]
        exact hGq z hz (Real.pi - s)
  -- `t ↦ MG G (exp t)` is integrable on every bounded interval `(a,b)`, by substitution.
  have hexp : ∀ a b : ℝ, a < b →
      IntegrableOn (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t)) (Set.Ioo a b) := by
    intro a b hab
    have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := Real.exp) (f' := fun x => Real.exp x) (g := Work.FTS.EllSol.EllPkgAux.MG G)
      (a := a) (b := b)
      (by fun_prop) (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le)
    have hR : IntervalIntegrable (Work.FTS.EllSol.EllPkgAux.MG G) volume (Real.exp a)
        (Real.exp b) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt (Real.exp_lt_exp.mpr hab))).mpr
        (hint (Real.exp a) (Real.exp b) (Real.exp_pos a) (Real.exp_lt_exp.mpr hab))
    have hL : IntegrableOn
        (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) * Real.exp t)
        (Set.Ioo a b) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt hab)).mp (hiff.mpr hR)
    rw [IntegrableOn] at hL ⊢
    have h2 : Integrable
        (fun t : ℝ => (Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t)
          * Real.exp t)) (volume.restrict (Set.Ioo a b)) := hL.const_mul _
    refine h2.mono' ?_ ?_
    · have hcont : Continuous (fun t : ℝ => Real.exp a * (Real.exp t)⁻¹) :=
        continuous_const.mul (Real.continuous_exp.inv₀ (fun t => Real.exp_ne_zero t))
      refine (hcont.aestronglyMeasurable.mul h2.aestronglyMeasurable).congr ?_
      filter_upwards with t
      have ha : Real.exp a ≠ 0 := Real.exp_ne_zero a
      have ht : Real.exp t ≠ 0 := Real.exp_ne_zero t
      calc Real.exp a * (Real.exp t)⁻¹
            * ((Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) * Real.exp t))
          = (Real.exp t)⁻¹ * Real.exp t * (Real.exp a * (Real.exp a)⁻¹)
              * Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) := by ring
        _ = Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) := by
              rw [inv_mul_cancel₀ ht, mul_inv_cancel₀ ha]; ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hpa : 0 < Real.exp a := Real.exp_pos a
      have hlt : Real.exp a < Real.exp t := Real.exp_lt_exp.mpr ht.1
      have hge : 1 ≤ Real.exp t / Real.exp a := (one_le_div hpa).mpr hlt.le
      rw [Real.norm_of_nonneg (hMGnn _)]
      calc Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t)
          = Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) * 1 := by ring
        _ ≤ Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) * (Real.exp t / Real.exp a) :=
              mul_le_mul_of_nonneg_left hge (hMGnn _)
        _ = (Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) * Real.exp t) := by
              ring
  -- Local integrability of the dominating function on the plane.
  have hLI : LocallyIntegrable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.MG G (Real.exp p.1)) volume := by
    intro x
    refine ⟨Set.Ioo (x.1 - 1) (x.1 + 1) ×ˢ Set.Ioo (x.2 - 1) (x.2 + 1), ?_, ?_⟩
    · exact IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_Ioo)
        (mem_prod.mpr ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
    · have hA : Integrable
          (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t))
          (volume.restrict (Set.Ioo (x.1 - 1) (x.1 + 1))) :=
        hexp (x.1 - 1) (x.1 + 1) (by linarith)
      have h2 := hA.comp_fst (volume.restrict (Set.Ioo (x.2 - 1) (x.2 + 1)))
      rw [Measure.prod_restrict] at h2
      rw [← Measure.volume_eq_prod ℝ ℝ] at h2
      exact h2
  -- The pointwise decomposition of the integrand into three reflected pieces.
  have hfun : ∀ p : ℝ × ℝ, Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p =
      Set.indicator {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)}
          (fun q : ℝ × ℝ => G (Real.exp q.1) q.2) p
        + Set.indicator {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0}
          (fun q : ℝ × ℝ => -(G (Real.exp q.1) (-q.2))) p
        + Set.indicator {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi}
          (fun q : ℝ × ℝ => -(G (Real.exp q.1) (Real.pi - q.2))) p := by
    intro p
    by_cases hA : p ∈ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)}
    · have hAc : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hA
      have hAs : 0 < p.2 ∧ p.2 < Real.pi / 2 := Set.mem_Ioo.mp hAc
      have h1 : 0 ≤ p.2 ∧ p.2 ≤ Real.pi / 2 := ⟨hAs.1.le, hAs.2.le⟩
      have hBn : p ∉ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0} := fun h => by
        have hb : -(Real.pi / 2) < p.2 ∧ p.2 < 0 := Set.mem_Ioo.mp h
        linarith [hAs.1, hb.2]
      have hCn : p ∉ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} := fun h => by
        have hc : Real.pi / 2 < p.2 ∧ p.2 < Real.pi := Set.mem_Ioo.mp h
        linarith [hAs.2, hc.1]
      rw [Hxy, Qext, ite_eq_left h1, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_left hAc,
        Set.indicator_of_mem hA, Set.indicator_of_notMem hBn, Set.indicator_of_notMem hCn]
      ring
    · by_cases hB : p ∈ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0}
      · have hBs : -(Real.pi / 2) < p.2 ∧ p.2 < 0 := Set.mem_Ioo.mp hB
        have h1 : ¬ (0 ≤ p.2 ∧ p.2 ≤ Real.pi / 2) := fun h => by linarith [h.1, hBs.2]
        have hneg : -p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
          rw [Set.mem_Ioo]; exact ⟨by linarith [hBs.2], by linarith [hBs.1]⟩
        have hCn : p ∉ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} := fun h => by
          have hc : Real.pi / 2 < p.2 ∧ p.2 < Real.pi := Set.mem_Ioo.mp h
          linarith [hBs.2, hc.1]
        rw [Hxy, Qext, ite_eq_right h1, ite_eq_left hBs.2, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_left hneg,
          Set.indicator_of_notMem hA, Set.indicator_of_mem hB, Set.indicator_of_notMem hCn]
        ring
      · by_cases hC : p ∈ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi}
        · have hCs : Real.pi / 2 < p.2 ∧ p.2 < Real.pi := Set.mem_Ioo.mp hC
          have h1 : ¬ (0 ≤ p.2 ∧ p.2 ≤ Real.pi / 2) := fun h => by linarith [h.2, hCs.1]
          have hlt : ¬ p.2 < 0 := by linarith [hCs.1, Real.pi_pos]
          have hneg : Real.pi - p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
            rw [Set.mem_Ioo]; exact ⟨by linarith [hCs.2], by linarith [hCs.1]⟩
          rw [Hxy, Qext, ite_eq_right h1, ite_eq_right hlt, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_left hneg,
            Set.indicator_of_notMem hA, Set.indicator_of_notMem hB, Set.indicator_of_mem hC]
          ring
        · have hAc : p.2 ∉ Set.Ioo (0 : ℝ) (Real.pi / 2) := hA
          have h0 : Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p = 0 := by
            rw [Hxy, Qext]
            by_cases h1 : 0 ≤ p.2 ∧ p.2 ≤ Real.pi / 2
            · rw [ite_eq_left h1, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_right hAc]
            · rw [ite_eq_right h1]
              by_cases h2 : p.2 < 0
              · rw [ite_eq_left h2, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_right (fun hm => by
                  have hmm : 0 < -p.2 ∧ -p.2 < Real.pi / 2 := Set.mem_Ioo.mp hm
                  exact hB ⟨by linarith [hmm.2], h2⟩), neg_zero]
              · rw [ite_eq_right h2, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_right (fun hm => by
                  have hmm : 0 < Real.pi - p.2 ∧ Real.pi - p.2 < Real.pi / 2 :=
                    Set.mem_Ioo.mp hm
                  exact hC ⟨by linarith [hmm.1], by linarith [hmm.2]⟩), neg_zero]
          rw [h0, Set.indicator_of_notMem hA, Set.indicator_of_notMem hB,
            Set.indicator_of_notMem hC]
          ring
  -- Measurability of the integrand.
  have hmeasH : AEStronglyMeasurable
      (Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G)) (volume : Measure (ℝ × ℝ)) := by
    have hAmeas : MeasurableSet {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} :=
      (IsOpen.preimage continuous_snd isOpen_Ioo).measurableSet
    have hBmeas : MeasurableSet {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0} :=
      (IsOpen.preimage continuous_snd isOpen_Ioo).measurableSet
    have hCmeas : MeasurableSet {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} :=
      (IsOpen.preimage continuous_snd isOpen_Ioo).measurableSet
    have hcontA : ContinuousOn (fun q : ℝ × ℝ => G (Real.exp q.1) q.2)
        {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} := by
      have hmp : MapsTo (fun q : ℝ × ℝ => (Real.exp q.1, q.2))
          {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} Work.FTS.EllipticEst.Q0 := by
        intro q hq
        exact mem_prod.mpr ⟨Real.exp_pos q.1, hq⟩
      have hc := hS.continuousOn.comp (by fun_prop) hmp
      have hFeq : (fun q : ℝ × ℝ => G (Real.exp q.1) q.2)
          = (Function.uncurry G) ∘ (fun q : ℝ × ℝ => (Real.exp q.1, q.2)) := by
        funext q; rfl
      rw [hFeq]
      exact hc
    have hcontB : ContinuousOn (fun q : ℝ × ℝ => -(G (Real.exp q.1) (-q.2)))
        {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0} := by
      have hmp : MapsTo (fun q : ℝ × ℝ => (Real.exp q.1, -q.2))
          {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0} Work.FTS.EllipticEst.Q0 := by
        intro q hq
        have hq2 : q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0 := hq
        rw [Set.mem_Ioo] at hq2
        have hq' : -q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
          rw [Set.mem_Ioo]; exact ⟨by linarith [hq2.2], by linarith [hq2.1]⟩
        exact mem_prod.mpr ⟨Real.exp_pos q.1, hq'⟩
      have hc := hS.continuousOn.comp (by fun_prop) hmp
      have hFeq : (fun q : ℝ × ℝ => -(G (Real.exp q.1) (-q.2)))
          = -((Function.uncurry G) ∘ (fun q : ℝ × ℝ => (Real.exp q.1, -q.2))) := by
        funext q; rfl
      rw [hFeq]
      exact hc.neg
    have hcontC : ContinuousOn (fun q : ℝ × ℝ => -(G (Real.exp q.1) (Real.pi - q.2)))
        {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} := by
      have hmp : MapsTo (fun q : ℝ × ℝ => (Real.exp q.1, Real.pi - q.2))
          {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} Work.FTS.EllipticEst.Q0 := by
        intro q hq
        have hq2 : q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi := hq
        rw [Set.mem_Ioo] at hq2
        have hq' : Real.pi - q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
          rw [Set.mem_Ioo]; exact ⟨by linarith [hq2.2], by linarith [hq2.1]⟩
        exact mem_prod.mpr ⟨Real.exp_pos q.1, hq'⟩
      have hc := hS.continuousOn.comp (by fun_prop) hmp
      have hFeq : (fun q : ℝ × ℝ => -(G (Real.exp q.1) (Real.pi - q.2)))
          = -((Function.uncurry G) ∘ (fun q : ℝ × ℝ => (Real.exp q.1, Real.pi - q.2))) := by
        funext q; rfl
      rw [hFeq]
      exact hc.neg
    have hm1 : AEStronglyMeasurable
        ({q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)}.indicator
          (fun q : ℝ × ℝ => G (Real.exp q.1) q.2)) volume :=
      (aestronglyMeasurable_indicator_iff hAmeas).mpr (hcontA.aestronglyMeasurable hAmeas)
    have hm2 : AEStronglyMeasurable
        ({q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0}.indicator
          (fun q : ℝ × ℝ => -(G (Real.exp q.1) (-q.2)))) volume :=
      (aestronglyMeasurable_indicator_iff hBmeas).mpr (hcontB.aestronglyMeasurable hBmeas)
    have hm3 : AEStronglyMeasurable
        ({q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi}.indicator
          (fun q : ℝ × ℝ => -(G (Real.exp q.1) (Real.pi - q.2)))) volume :=
      (aestronglyMeasurable_indicator_iff hCmeas).mpr (hcontC.aestronglyMeasurable hCmeas)
    refine ((hm1.add hm2).add hm3).congr ?_
    filter_upwards with p
    exact (hfun p).symm
  -- Domination of the integrand by the locally integrable function, and conclusion.
  have hdomH : ∀ p : ℝ × ℝ,
      |Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p|
        ≤ Work.FTS.EllSol.EllPkgAux.MG G (Real.exp p.1) := by
    intro p
    have hp := hQb (Real.exp p.1) (Real.exp_pos p.1) p.2
    simpa only [Hxy] using hp
  exact hLI.mono hmeasH (Eventually.of_forall (fun p => by
    simp only [Real.norm_eq_abs, abs_of_nonneg (hMGnn (Real.exp p.1))]
    exact hdomH p))

end Work.FTS.EllSol.EllPkgAux.MollSmooth
