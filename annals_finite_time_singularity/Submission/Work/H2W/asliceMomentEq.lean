import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.T1HardSlice
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.dzSelfA2d
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.hardyAngL2Integrable
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimExtract_bounds
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.momentChainAe
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.EllipticEst.Core.HkSqLHS_le_summands_v2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The summand decomposition of `HkSq` of `α • D_z∂_θV`

`HkSq α k (α D_z∂_θV)` is, by definition, the iterated Bochner integral of the sum of squares
`HkIntegrand`; the summands of that sum are the quantities `mixIntS (D_z^r V)`,
`mixedIntS α i j V` of the deformation estimate.  This module proves the value-wise reduction

`HkSq α k (α • D_z∂_θV) ≤ α² ∑_r ∫_z mixIntS(D_z^rV) + α² ∑_{1≤i, i+j≤k} ∫_z mixedIntS α i j V`,

with constant `1`, *under the hypothesis that the majorant* (the same sum without the
integrals in `z`) *is integrable on `[0,∞)`*.  The hypothesis is exactly what the junk-value
convention of the Bochner integral needs: without it the summand-wise integrals throw away a
finite contribution that the left-hand side keeps (see the sibling
`NOTES_HkSqLHS_le_summands.md`), while with it the two sides agree.

The proof is assembled from the pieces of `Submission/Work/EllipticEst/Core/`:

* `v2_aesm_slice`, `v2_aesm_integral` : measurability of the summands in `θ` and in `z`;
* `v2_zBlock_ae`, `v2_mixedBlock_ae` : the a.e. identification of the two blocks of
  `HkIntegrand α k (α • D_z∂_θV)` with the summands (via `pth`-`D_z` and `D_θ`-`D_z`
  commutation on the open quadrant);
* `v2_slice_le` : the reduction of the inner (`θ`) integral, using
  `integral_finset_sum_le`/`integral_add_le_nonneg`;
* the outer (`z`) integral is treated with the same subadditivity lemmas and the integrability
  of the majorant.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

theorem HkSqLHS_le_summands_v2 (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α →
      Work.FTS.EllipticEst.SmoothOpen V →
      MeasureTheory.IntegrableOn (fun z : ℝ =>
          α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                Work.EllipticEst.Core.mixedIntS α i j V z
              else 0)) Work.Spaces.Iz →
      Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C * (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
                else 0)) := by
  refine ⟨1, one_pos, ?_⟩
  intro α V hα hV hInt
  -- ## Pointwise nonnegativity of the two families, and measurability in `z`
  have hAnnP : ∀ r : ℕ, ∀ z : ℝ, 0 ≤ mixIntS (Work.Spaces.DzIter r V) z := by
    intro r z
    rw [mixIntS]
    refine mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg hθ))))
  have hBnnP : ∀ i j : ℕ, ∀ z : ℝ, 0 ≤ mixedIntS α i j V z := by
    intro i j z
    rw [mixedIntS]
    refine mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thGam_nonneg hθ))))
  have hAesm : ∀ r : ℕ, AEMeasurable (fun z : ℝ => mixIntS (Work.Spaces.DzIter r V) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro r
    have h := v2_aesm_integral ((hV.DzIter r).pth.Dz) (-(Work.Spaces.eta))
    simpa only [mixIntS, Work.FTS.EllipticEst.thEta] using h
  have hBesm : ∀ i j : ℕ, AEMeasurable (fun z : ℝ => mixedIntS α i j V z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro i j
    have h := v2_aesm_integral ((hV.pth).mixed (j + 1) i) (-(Work.Spaces.gam α))
    simpa only [mixedIntS, Work.FTS.EllipticEst.thGam] using h
  -- ## Integrability of the majorant, from the hypothesis
  have hInt' : MeasureTheory.IntegrableOn (fun z : ℝ =>
      α ^ 2 * ((∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z)
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)))
      Work.Spaces.Iz :=
    hInt.congr_fun (fun z _ => by ring) measurableSet_Ici
  -- ## The `HkSq`-side bound: the slice inequality integrated in `z`
  have hSq : Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ ∫ z in Work.Spaces.Iz, α ^ 2 *
          ((∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)) := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => MeasureTheory.integral_nonneg (fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k _ z θ)))
      hInt'
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z hz => v2_slice_le k hα hV z hz))
  -- ## The majorant side: distribute the outer integral over the summands
  have hInt_le : (∫ z in Work.Spaces.Iz, α ^ 2 *
        ((∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)))
      ≤ α ^ 2 * ((∑ r ∈ Finset.range (k + 1),
            ∫ z in Work.Spaces.Iz, mixIntS (Work.Spaces.DzIter r V) z)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                ∫ z in Work.Spaces.Iz, mixedIntS α i j V z
              else 0)) := by
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg α)
    refine le_trans (integral_add_le_nonneg
      (aemeasurable_finset_sum_apply (fun r _ => hAesm r))
      (aemeasurable_finset_sum_apply
        (fun i _ => aemeasurable_finset_sum_apply (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact hBesm i j
          · simp only [if_neg hc]
            exact aemeasurable_const)))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z _ => Finset.sum_nonneg (fun r _ => hAnnP r z)))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact hBnnP i j z
          · simp only [if_neg hc]
            exact le_refl 0))))) ?_
    refine add_le_add ?_ ?_
    · exact integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (s := Finset.range (k + 1))
        (f := fun r : ℕ => fun z : ℝ => mixIntS (Work.Spaces.DzIter r V) z)
        (fun r _ => hAesm r)
        (fun r _ => Filter.Eventually.of_forall (fun z => hAnnP r z))
    · refine le_trans (integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (s := Finset.range (k + 1))
        (f := fun i : ℕ => fun z : ℝ => ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)
        (fun i _ => aemeasurable_finset_sum_apply (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact hBesm i j
          · simp only [if_neg hc]
            exact aemeasurable_const))
        (fun i _ => Filter.Eventually.of_forall (fun z => Finset.sum_nonneg (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact hBnnP i j z
          · simp only [if_neg hc]
            exact le_refl 0)))) ?_
      refine Finset.sum_le_sum (fun i _ => ?_)
      refine le_trans (integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (s := Finset.range (k + 1))
        (f := fun j : ℕ => fun z : ℝ =>
          if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)
        (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact hBesm i j
          · simp only [if_neg hc]
            exact aemeasurable_const)
        (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact Filter.Eventually.of_forall (fun z => hBnnP i j z)
          · simp only [if_neg hc]
            exact Filter.Eventually.of_forall (fun _ => le_refl 0))) ?_
      refine Finset.sum_le_sum (fun j _ => ?_)
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        exact le_refl _
      · simp only [if_neg hc]
        exact le_of_eq (MeasureTheory.integral_zero ℝ ℝ)
  calc Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ ∫ z in Work.Spaces.Iz, α ^ 2 *
          ((∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)) := hSq
    _ ≤ α ^ 2 * ((∑ r ∈ Finset.range (k + 1),
            ∫ z in Work.Spaces.Iz, mixIntS (Work.Spaces.DzIter r V) z)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                ∫ z in Work.Spaces.Iz, mixedIntS α i j V z
              else 0)) := hInt_le
    _ = 1 * (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
                  ∫ z in Work.Spaces.Iz, mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, mixedIntS α i j V z
                else 0)) := by ring

end Work.EllipticEst.Core
end
end
-- ===== merged: Submission.Work.FTS.ClassC.vanGrid_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.FTS.ClassC

/-- **Level-`0` honesty of an integrand.**  The integrand `F` has integrable angular slices on
`Iθ` for every `z ∈ Iz`, and its angular integral `z ↦ ∫_θ F z θ` is integrable on `Iz`.

For `F = fun z θ => Work.Spaces.HkIntegrand α 0 f z θ` this is exactly `Work.Spaces.HkMem α 0 f`,
and the hypothesis `hV` of `vanGrid_integrable` is exactly this statement for
`F = hVint α Ψ t l`.  The point of the abstraction is that this property is stable under finite
sums, which is what the integrability of the grid majorant `vanGrid` reduces to. -/
def Level0Integrable (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ) ∧
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) Work.Spaces.Iz

/-- A finite sum of level-`0` honest integrands is level-`0` honest. -/
theorem Level0Integrable_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ → ℝ}
    (h : ∀ i ∈ s, Level0Integrable (F i)) :
    Level0Integrable (fun z θ => ∑ i ∈ s, F i z θ) := by
  refine ⟨fun z hz => ?_, ?_⟩
  · exact MeasureTheory.integrable_finsetSum (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) s
      (fun i hi => (h i hi).1 z hz)
  · -- `z ↦ ∫_θ ∑_i F i z θ = ∑_i ∫_θ F i z θ` on `Iz`; the right-hand side is a finite sum of
    -- functions that are integrable on `Iz`.
    refine MeasureTheory.IntegrableOn.congr_fun
      (f := fun z => ∑ i ∈ s, ∫ θ in Work.Spaces.Iθ, F i z θ) ?_ ?_ measurableSet_Ici
    · exact MeasureTheory.integrable_finsetSum (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) s
        (fun i hi => (h i hi).2)
    · intro z hz
      exact (MeasureTheory.integral_finsetSum s (fun i hi => (h i hi).1 z hz)).symm

/-- A sum of two level-`0` honest integrands is level-`0` honest. -/
theorem Level0Integrable_add {F G : ℝ → ℝ → ℝ} (hF : Level0Integrable F)
    (hG : Level0Integrable G) : Level0Integrable (fun z θ => F z θ + G z θ) := by
  refine ⟨fun z hz => ?_, ?_⟩
  · exact MeasureTheory.IntegrableOn.add (hF.1 z hz) (hG.1 z hz)
  · refine MeasureTheory.IntegrableOn.congr_fun
      (f := fun z => (∫ θ in Work.Spaces.Iθ, F z θ) + ∫ θ in Work.Spaces.Iθ, G z θ)
      ?_ ?_ measurableSet_Ici
    · exact MeasureTheory.IntegrableOn.add hF.2 hG.2
    · intro z hz
      exact (MeasureTheory.integral_add (hF.1 z hz) (hG.1 z hz)).symm


end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.EllExist.hkMem_orthSource_of_Fstar_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

/-- **Honesty of the orthogonalised source, from the angular moment alone.**

`Work.Elliptic.orthSource g = g - (15/4)·sin 2θ·F_*(g)`, so for `g` smooth on the open quadrant
and honestly in `ℋ^k`, with `0 < α ≤ 1` and `F_*(g)` `C^∞` on `(0,∞)`, the orthogonalised source
is again honestly in `ℋ^k`.  This is the transfer the new class `ClassC`
(`Submission/Work/FTS/FTS_HARD_STMTS.lean.txt`) needs in order to feed the area's existence node
`Work.FTS.EllExist.ellClassOk_exists_of_Fstar_smooth k`, whose hypotheses are stated for the
source `orthSource g` (it is what the elliptic node `bslOp_sol_exists k` consumes).

The upper bound `α ≤ 1` is necessary: the mixed slot `(i=1, j=0)` of `orthSource g` is
`(D_θ(sin 2θ)·F_*(g))² · Wt²`, of order `θ^{2-γ}` with `γ = 1 + α/10`, which is `θ`-integrable
only for `γ < 3`, i.e. `α < 20`; the paper's range is `α ≤ 1/4` and the companion
`Work.FTS.EllipticEst.HkMem_orthSource` carries the same bound.

Expected proof: the pointwise subadditivity
`Work.FTS.LocData.HkIntegrand_add_le` (`HkIntegrand (a+b) ≤ 2 HkIntegrand a + 2 HkIntegrand b`)
reduces the claim to `HkMem α k (fun z θ => sin 2θ * F_*(g) z)`.  For that, bound each derivative
slot of `Φ z θ = sin 2θ · F_*(g) z` by the corresponding slot of `g`: `|D_θ^i(sin 2·)| ≤ 4^i`
and `(D_z^j F_*(g) z)² ≤ (π/2)·∫_θ (D_z^j g z θ)²` by Cauchy–Schwarz against `sinθcos²θ`, while
`∫_θ (D_z^j g)² ≤ w(z)^{-2}·∫_θ (D_z^j g · w(z)/sin(2θ)^{η/2})²` (the factor `sin^{-η} ≥ 1` only
helps).  `HkMem` then transfers by domination (`Work.FTS.LocData.HkMem_of_majorant`), the
`θ`-integrability at every `z ∈ Iz` coming from `α ≤ 1` (so that all `θ`-powers are integrable:
the worst slot is `θ^{2-γ}` with `γ ≤ 1.1`, and `1 + γ`-type exponents for the higher `<i>`), and
the `z`-integrability from `hmem`.  The companion facts making the `z`-derivatives of `F_*` exist
are supplied by `hF`. -/
theorem hkMem_orthSource_of_Fstar_smooth {α : ℝ} {k : ℕ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g)
    (hF : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0)) :
    Work.Spaces.HkMem α k (Work.Elliptic.orthSource g) := by
  -- The angular-moment term `Φ z θ = F_*(g) z · sin 2θ`.
  have hsin : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) :=
    sep_mul_open (g := Work.Elliptic.Fstar g)
      (χ := fun θ : ℝ => Real.sin (2 * θ)) hF hsin
  -- `Φ ∈ ℋ^k`: the certificate for the angular moment of an open-quadrant datum.
  have hΦmem : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
    have h := Work.FTS.EllipticEst.Cert.HkMem_bmom_sin_of_smoothOpen α k g hα hα1 hsm hmem
    simpa only [Work.FTS.EllipticEst.Bmom_zero] using h
  -- the scaled term `-(15/4)·Φ`.
  have hSsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
    const_mul_open (-(15 / 4)) hΦsm
  have hSmem : Work.Spaces.HkMem α k
      (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k (-(15 / 4)) hΦmem
  -- `orthSource g` is the sum of the two summands.
  have horth : Work.Elliptic.orthSource g
      = fun z θ => g z θ + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
    funext z θ
    simp only [Work.Elliptic.orthSource]
    ring
  rw [horth]
  exact Work.FTS.EllipticEst.HkMem_add_smoothOpen α k hα hsm hSsm hmem hSmem

end Work.FTS.EllExist
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Gbar_Hk_le_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

theorem Gbar_Hk_le_open (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k F →
      Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  obtain ⟨C, hC, h⟩ := Gbar_Hk_le_open_SmoothOpen k
  exact ⟨C, hC, fun α F hα hα1 hFraw hmem =>
    h α F hα hα1 (smoothOpen_of_forall hFraw) hmem⟩

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.H2.STMeas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Joint smoothness of the iterated operators for `SmoothInt` functions -/

theorem contDiffOn_uncurry_DzIter {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (b : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter b f)) V := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    have hpz := Work.Spaces.contDiffOn_uncurry_pz hV ih
    have hmul : ContDiffOn ℝ ⊤
        (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz (Work.Spaces.DzIter b f) p.1 p.2) V :=
      contDiffOn_fst.mul hpz
    have hfun : (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz (Work.Spaces.DzIter b f) p.1 p.2)
        = Function.uncurry (Work.Spaces.DzIter (b + 1) f) := rfl
    rwa [hfun] at hmul


/-! ## Transfer of almost-everywhere measurability -/


theorem volume_Icc_diff_Ioo : volume (Set.Icc (0 : ℝ) (π / 2) \ Set.Ioo 0 (π / 2)) = 0 := by
  have hsub : Set.Icc (0 : ℝ) (π / 2) \ Set.Ioo 0 (π / 2) ⊆ ({0} : Set ℝ) ∪ {π / 2} := by
    intro x hx
    rw [Set.mem_diff, Set.mem_Icc, Set.mem_Ioo] at hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_singleton_iff]
    by_cases h : x ≤ 0
    · left; linarith
    · right
      push_neg at h
      have hlt : ¬ (x < π / 2) := fun hlt => h3 ⟨h, hlt⟩
      linarith
  refine measure_mono_null hsub ?_
  rw [measure_union_null_iff]
  exact ⟨Real.volume_singleton, Real.volume_singleton⟩


/-! ## Measurability of the individual blocks -/





/-! ## Measurability of the slices of `EZ`, `EM`, `EC` -/






/-! ## The pointwise bound on the easy part, and its integrability -/



end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_bookkeeping =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 15: the `H⁴`-bookkeeping for `N₂^{ss}`

The pointwise information available for `f = N₂^{ss}(α, Φ_s)` — a bound on
`|D_z^j D_θ^i f · w|` at those `z > 0` where the angular derivatives of the stream
function `U(Φ̃_s)` tend to `0` at `θ → 0⁺` — is integrated here to give the `H⁴`-bound

`HkSq α 4 f ≤ (10⁶ K (Cs+1))² α⁴`.

The two complementary hypotheses are used as follows.  For `z > 0` where the θ-slice
`HkIntegrand α 4 f z ·` is **integrable** on `Iθ`, the contrapositive of `hbad` supplies
the vanishing of the angular derivatives, hence `hU` gives the pointwise bound and
`HkIntegrand_le_of_mixed_bound` turns it into `HkIntegrand α 4 f z θ ≤ C rlog(z)² Gwt α θ`,
whose θ-integral is `≤ 2000 C rlog(z)²/α` (`Gwt_integrableOn_and_integral_le`).  At the
`z` where the slice is **not** integrable, the slice integral is `0` by Mathlib's
convention for the Bochner integral of a non-integrable function, so the bound holds
there too.  Integrating in `z` with `∫_0^∞ rlog² ≤ 100`
(`rlog_sq_integrableOn_and_integral_le`) gives `HkSq ≤ 2·10⁵ K²(Cs+1)²α⁵`, and
`α ≤ 1` upgrades this to `10¹²K²(Cs+1)²α⁴`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.aemeasurable_uncurry_HkIntegrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint measurability of `(s,z,θ) ↦ HkIntegrand α k (H s) z θ`

For a family `H : ℝ → ℝ → ℝ → ℝ` whose slices `H s` (`s ∈ [0,T]`) are `C^∞` on the open
quadrant and whose values `s ↦ H s z θ` are continuous on `[0,T]` at every point `(z,θ)` of the
quadrant, the map

  `(s, z, θ) ↦ HkIntegrand α k (H s) z θ`

is a.e. strongly measurable for `(volume.restrict (Icc 0 T)).prod ((volume.restrict Iz).prod
(volume.restrict Iθ))`.

The proof has three parts.

* **Slicewise measurability in `s`.**  `HkIntegrand α k (H s) z θ` is a finite sum of squares of
  the mixed slots `mixed j i (H s) z θ` (times weights that depend on `(z,θ)` only), and
  `Work.FTS.StrongEps.aemeasurable_mixed_family` gives the a.e. strong measurability of every
  slot at any point of the *open* quadrant.

* **Carathéodory step.**  The integrand is continuous in `(z,θ)` on the open quadrant and (in its
  truncated version) zero off it, so `Work.FTS.EpsEngine.aesm_uncurry_restricted` gives joint
  measurability of the truncated integrand for `(volume.restrict (Icc 0 T)).prod volume`.

* **Passing to the restricted measure.**  `Iz ×ˢ Iθ` (the support of the target measure) and the
  open quadrant `Qd` agree up to a null set for the planar Lebesgue measure, so
  `(volume.restrict Iz).prod (volume.restrict Iθ) = volume.restrict Qd`, and on that measure the
  truncated integrand agrees a.e. with the integrand itself.
-/

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open MeasureTheory Set Filter

/-- The open quadrant `(0,∞) × (0,π/2)` of the elliptic estimates. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

private lemma measurableSet_Qd_compl : MeasurableSet Qdᶜ := isOpen_Qd.measurableSet.compl

/-- The product of the restrictions of the Lebesgue measure to `Iz = [0,∞)` and to
`Iθ = [0,π/2]` is the restriction of the planar Lebesgue measure to the open quadrant `Qd`:
the sets `Iz ×ˢ Iθ` and `Qd` differ only by the null lines `z = 0` and `θ = 0, π/2`. -/
private lemma prod_restrict_Iz_Iθ :
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = volume.restrict Qd := by
  simp only [Work.Spaces.Iz, Work.Spaces.Iθ, Qd]
  rw [MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.Measure.restrict_congr_set ?_
  exact MeasureTheory.Measure.set_prod_ae_eq MeasureTheory.Ioi_ae_eq_Ici.symm
    MeasureTheory.Ioo_ae_eq_Icc.symm

/-! ## Measurability in `s` of the integrand of a single slice -/

/-- A finite sum (evaluated pointwise) of a.e. strongly measurable real functions is a.e. strongly
measurable. -/
private lemma aesm_finsetSum_apply {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    {μ : Measure ℝ} (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a : ℝ => ∑ i ∈ s, f i a) μ := by
  have h := Finset.aestronglyMeasurable_sum (M := ℝ) (f := f) s hf
  refine h.congr (Filter.Eventually.of_forall fun a => ?_)
  exact Finset.sum_apply a s f

/-- **Measurability in `s` of `HkIntegrand α k (H s) z θ`** at a point of the open quadrant. -/
private lemma aesm_HkIntegrand_family {α T : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => H s z θ) (Set.Icc (0:ℝ) T))
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable (fun s : ℝ => Work.Spaces.HkIntegrand α k (H s) z θ)
      (volume.restrict (Set.Icc (0:ℝ) T)) := by
  have hslot : ∀ j i : ℕ, AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
      (volume.restrict (Set.Icc (0:ℝ) T)) :=
    fun j i => Work.FTS.StrongEps.aemeasurable_mixed_family hsm hcont j i z θ hzθ
  unfold Work.Spaces.HkIntegrand
  have hA : AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (H s) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (volume.restrict (Set.Icc (0:ℝ) T)) :=
    aesm_finsetSum_apply (fun i _ => ((hslot i 0).mul_const
      (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))).pow 2)
  have hB : AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) (volume.restrict (Set.Icc (0:ℝ) T)) :=
    aesm_finsetSum_apply (fun i _ => aesm_finsetSum_apply (fun j _ => by
      by_cases hh : 1 ≤ i ∧ i + j ≤ k
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun s : ℝ => (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
          funext fun s => ite_eq_left hh
        rw [hthis]
        exact (((hslot j i).mul_const (Work.Spaces.Wt α z θ)).pow 2)
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun _ : ℝ => (0:ℝ) :=
          funext fun s => ite_eq_right hh
        rw [hthis]
        exact aestronglyMeasurable_const))
  exact hA.add hB

/-! ## The target -/

theorem aemeasurable_uncurry_HkIntegrand {α T : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => H s z θ) (Set.Icc (0:ℝ) T)) :
    AEMeasurable
      (fun p : ℝ × (ℝ × ℝ) => Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2)
      ((volume.restrict (Set.Icc (0:ℝ) T)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) := by
  classical
  rw [prod_restrict_Iz_Iθ]
  -- the Carathéodory step, on the larger measure with an unrestricted `(z,θ)`-factor
  have hmain : AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) =>
        if (p.2.1, p.2.2) ∈ Qd
          then Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2 else 0)
      ((volume.restrict (Set.Icc (0:ℝ) T)).prod (volume : Measure (ℝ × ℝ))) := by
    refine Work.FTS.EpsEngine.aesm_uncurry_restricted (A := Set.Icc (0:ℝ) T)
      (g := fun s z θ => if (z, θ) ∈ Qd
        then Work.Spaces.HkIntegrand α k (H s) z θ else 0)
      measurableSet_Icc ?_ ?_ ?_
    · intro s hs
      refine ((hsm s hs).continuousOn_HkIntegrand α k).congr ?_
      intro q hq
      exact ite_eq_left hq
    · intro s hs q hq
      exact ite_eq_right hq
    · intro q
      by_cases hq : q ∈ Qd
      · have hthis : (fun s : ℝ =>
            if (q.1, q.2) ∈ Qd then Work.Spaces.HkIntegrand α k (H s) q.1 q.2 else 0)
            = fun s : ℝ => Work.Spaces.HkIntegrand α k (H s) q.1 q.2 :=
          funext fun s => ite_eq_left hq
        rw [hthis]
        exact aesm_HkIntegrand_family hsm hcont hq
      · have hthis : (fun s : ℝ =>
            if (q.1, q.2) ∈ Qd then Work.Spaces.HkIntegrand α k (H s) q.1 q.2 else 0)
            = fun _ : ℝ => (0:ℝ) :=
          funext fun s => ite_eq_right hq
        rw [hthis]
        exact aestronglyMeasurable_const
  -- restrict the `(z,θ)`-factor to the open quadrant
  have hg : AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) =>
        if (p.2.1, p.2.2) ∈ Qd
          then Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2 else 0)
      ((volume.restrict (Set.Icc (0:ℝ) T)).prod (volume.restrict Qd)) :=
    hmain.mono_measure
      (MeasureTheory.Measure.prod_mono le_rfl MeasureTheory.Measure.restrict_le_self)
  -- on that measure, the truncated integrand agrees a.e. with the integrand
  have hae : (fun p : ℝ × (ℝ × ℝ) =>
        if (p.2.1, p.2.2) ∈ Qd
          then Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2 else 0)
      =ᵐ[(volume.restrict (Set.Icc (0:ℝ) T)).prod (volume.restrict Qd)]
      (fun p : ℝ × (ℝ × ℝ) => Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine measure_mono_null (t := Set.univ ×ˢ Qdᶜ) ?_ ?_
    · intro p hp
      rw [Set.mem_prod]
      refine ⟨Set.mem_univ _, ?_⟩
      intro hpq
      exact hp (ite_eq_left hpq)
    · rw [MeasureTheory.Measure.prod_prod,
        MeasureTheory.Measure.restrict_apply measurableSet_Qd_compl]
      simp
  exact (hg.congr hae).aemeasurable

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G5.DthIter_intervalIntegral_eq_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Pointwise

namespace Work.FTS.StrongEps.E5G5

/-- **The angular exchange for an arbitrary order `l ≤ n`.** -/
theorem DthIter_intervalIntegral_eq_gen {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ} {n l : ℕ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed k l (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    (hl : l ≤ n) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0:ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have hsubIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  induction l with
  | zero => intro z θ _; rfl
  | succ l ih =>
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    obtain ⟨hzz, hθθ⟩ := hzθ
    have hzcl : z ∈ Set.Icc z₁ z₂ := ⟨le_of_lt hzz.1, le_of_lt hzz.2⟩
    have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨hzcl, ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩⟩
    obtain ⟨hz0, hθ0, hθπ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
    set θlo : ℝ := max θ₁ (θ / 2) with hθlo
    set θhi : ℝ := min θ₂ ((θ + Real.pi / 2) / 2) with hθhi
    have hθlo_lt : θlo < θ := by
      rw [hθlo]; exact max_lt hθθ.1 (by linarith)
    have hθ_lt_θhi : θ < θhi := by
      rw [hθhi]; exact lt_min hθθ.2 (by linarith)
    have hθlo0 : 0 < θlo := lt_of_lt_of_le (by linarith : (0:ℝ) < θ / 2) (le_max_right _ _)
    have hθhi_lt : θhi < Real.pi / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    obtain ⟨smin, hsmin_pos, hsmin_le⟩ := Work.FTS.StrongEps.exists_pos_min_sin_two hθlo0 hθhi_lt
    have hmem_box : ∀ y ∈ Set.Ioo θlo θhi,
        (z, y) ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ := by
      intro y hy
      exact ⟨hzcl, ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hy.1),
        le_of_lt (lt_of_lt_of_le hy.2 (min_le_left _ _))⟩⟩
    have hyQ : ∀ y ∈ Set.Ioo θlo θhi, (z, y) ∈ Work.FTS.EllipticEst.Q0 :=
      fun y hy => hboxQ (hmem_box y hy)
    have hyf : ∀ y ∈ Set.Ioo θlo θhi, 0 < y ∧ y < Real.pi / 2 := by
      intro y hy
      obtain ⟨-, hy1, hy2⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hyQ y hy)
      exact ⟨hy1, hy2⟩
    have hcore := Work.FTS.StrongEps.hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
      (G := fun t y => Work.Spaces.DthIter l (H t) z y)
      (G' := fun t y => Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y))
      (bound := fun _ => C / smin) hθlo_lt hθ_lt_θhi ?_ ?_ ?_ ?_ ?_ ?_
    rotate_left
    · intro y hy
      have := (hmeas 0 l z y (hyQ y hy)).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [Work.Spaces.mixed_zero_left] using this
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
      · have h1 := (hmeas 0 l z θ hzQ).mono_measure (Measure.restrict_mono hsubIoc le_rfl)
        simpa only [Work.Spaces.mixed_zero_left] using h1
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        have htT : t ∈ Set.Icc (0:ℝ) T := hsubIoc ht
        have := hbdd t htT 0 l (by omega) (z, θ)
          ⟨hzcl, ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩⟩
        simpa only [Work.Spaces.mixed_zero_left] using this
    · have h1 := (hmeas 0 (l + 1) z θ hzQ).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [div_eq_mul_inv] using h1.mul_const (Real.sin (2 * θ))⁻¹
    · intro t ht y hy
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hsinpos : 0 < Real.sin (2 * y) :=
        lt_of_lt_of_le hsmin_pos (hsmin_le y (Set.Ioo_subset_Icc_self hy))
      have hb := hbdd t htT 0 (l + 1) (by omega) (z, y) (hmem_box y hy)
      calc |Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y)|
          = |Work.Spaces.mixed 0 (l + 1) (H t) z y| / Real.sin (2 * y) := by
            rw [abs_div, abs_of_pos hsinpos]
        _ ≤ C / Real.sin (2 * y) := div_le_div_of_nonneg_right hb (le_of_lt hsinpos)
        _ ≤ C / smin := div_le_div_of_nonneg_left hC hsmin_pos
            (hsmin_le y (Set.Ioo_subset_Icc_self hy))
    · exact intervalIntegrable_const
    · intro t ht y hy
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hder := Work.FTS.StrongEps.SmoothOpen.hasDerivAt_slice_th
        (Work.FTS.LocData.contDiffOn_DthIter Work.FTS.EllipticEst.isOpen_Q0
          (hsm t htT) l) hz0 (hyf y hy)
      have hid : Work.Spaces.pth (Work.Spaces.DthIter l (H t)) z y
          = Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y) := by
        simpa only [Work.Spaces.mixed_zero_left] using
          Work.FTS.StrongEps.LocUnif.pth_mixed_div 0 l (hsm t htT) z y (hyQ y hy)
      exact hder.congr_deriv hid
    have hev : (fun y => Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z y)
        =ᶠ[𝓝 θ] (fun y => ∫ s in a..b, Work.Spaces.DthIter l (H s) z y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθθ] with y hy
      exact ih (by omega) z y ⟨hzz, hy⟩
    have hpth : Work.Spaces.pth (Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ)) z θ
        = ∫ s in a..b, Work.Spaces.mixed 0 (l + 1) (H s) z θ / Real.sin (2 * θ) := by
      show deriv (fun y => Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z y) θ = _
      rw [hev.deriv_eq, hcore.deriv]
    have hsinne : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    calc Work.Spaces.DthIter (l + 1) (fun z θ => ∫ s in a..b, H s z θ) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth
            (Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ)) z θ := by
          rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      _ = Real.sin (2 * θ) * (∫ s in a..b,
            Work.Spaces.mixed 0 (l + 1) (H s) z θ / Real.sin (2 * θ)) := by rw [hpth]
      _ = Real.sin (2 * θ) * ((∫ s in a..b,
            Work.Spaces.mixed 0 (l + 1) (H s) z θ) / Real.sin (2 * θ)) := by
          rw [intervalIntegral.integral_div]
      _ = ∫ s in a..b, Work.Spaces.mixed 0 (l + 1) (H s) z θ :=
          mul_div_cancel₀ _ hsinne
      _ = ∫ s in a..b, Work.Spaces.DthIter (l + 1) (H s) z θ := rfl

end Work.FTS.StrongEps.E5G5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G5.DzIter_intervalIntegral_eq_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G5

/-- **The radial exchange, for an arbitrary order `n`.**

The boundedness hypothesis `hbdd` is only assumed for the slots `D_z^j D_θ^i` of order
`j + i ≤ n`; the conclusion is the exchange of the `k`-th radial operator `D_z^k` with the
interval integral in `s`, provided `k + l ≤ n` (so that every slot produced by the
induction is covered by `hbdd`).

The proof is the verbatim induction on `k` of `Work.FTS.StrongEps.DzIter_intervalIntegral_eq`
(the case `n = 4`), with `4` replaced by `n`: at the successor stage the new slot is
`D_z^{k+1} D_θ^l`, of order `(k+1) + l ≤ n`, and the induction hypothesis is applied at the
order `k + l ≤ n`. -/
theorem DzIter_intervalIntegral_eq_gen {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ} {n : ℕ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed k l (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    (k l : ℕ) (hkl : k + l ≤ n) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.DzIter k (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) z θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0:ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have hsubIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  induction k with
  | zero => intro z θ _; rfl
  | succ k ih =>
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    obtain ⟨hzz, hθθ⟩ := hzθ
    have hθcl : θ ∈ Set.Icc θ₁ θ₂ := ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩
    have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    obtain ⟨hz0, hθ0, hθπ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
    set zlo : ℝ := max z₁ (z / 2) with hzlo
    have hzlo_lt : zlo < z := by
      rw [hzlo]; exact max_lt hzz.1 (by linarith)
    have hmem_box : ∀ x ∈ Set.Ioo zlo z₂,
        (x, θ) ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ := by
      intro x hx
      exact ⟨⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx.1), le_of_lt hx.2⟩, hθcl⟩
    have hxQ : ∀ x ∈ Set.Ioo zlo z₂, (x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      fun x hx => hboxQ (hmem_box x hx)
    have hxpos : ∀ x ∈ Set.Ioo zlo z₂, 0 < x := fun x hx =>
      lt_of_lt_of_le (by linarith : (0:ℝ) < z / 2)
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1))
    have hcore := Work.FTS.StrongEps.hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
      (G := fun t x => Work.Spaces.DzIter k (Work.Spaces.DthIter l (H t)) x θ)
      (G' := fun t x => Work.Spaces.mixed (k + 1) l (H t) x θ / x)
      (bound := fun _ => C * (2 / z)) hzlo_lt hzz.2 ?_ ?_ ?_ ?_ ?_ ?_
    rotate_left
    · intro x hx
      have := (hmeas k l x θ (hxQ x hx)).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [Work.Spaces.mixed] using this
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
      · have h1 := (hmeas k l z θ hzQ).mono_measure (Measure.restrict_mono hsubIoc le_rfl)
        simpa only [Work.Spaces.mixed] using h1
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        have htT : t ∈ Set.Icc (0:ℝ) T := hsubIoc ht
        exact hbdd t htT k l (by omega) (z, θ) ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    · have h1 := (hmeas (k + 1) l z θ hzQ).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [div_eq_mul_inv] using h1.mul_const z⁻¹
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hx2 : z / 2 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1)
      have hb := hbdd t htT (k + 1) l (by omega) (x, θ) (hmem_box x hx)
      calc |Work.Spaces.mixed (k + 1) l (H t) x θ / x|
          = |Work.Spaces.mixed (k + 1) l (H t) x θ| / x := by
            rw [abs_div, abs_of_pos (hxpos x hx)]
        _ ≤ C / x := div_le_div_of_nonneg_right hb (le_of_lt (hxpos x hx))
        _ ≤ C / (z / 2) := div_le_div_of_nonneg_left hC (by linarith) hx2
        _ = C * (2 / z) := by field_simp
    · exact intervalIntegrable_const
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hder : HasDerivAt (fun x' => Work.Spaces.mixed k l (H t) x' θ)
          (Work.Spaces.pz (Work.Spaces.mixed k l (H t)) x θ) x :=
        Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice
          (Work.FTS.LocData.contDiffOn_mixed Work.FTS.EllipticEst.isOpen_Q0 (hsm t htT) k l)
          (θ := θ) ⟨hθ0, hθπ2⟩ (hxpos x hx)
      exact hder.congr_deriv
        (Work.FTS.StrongEps.LocUnif.pz_mixed_div k l (hsm t htT) x θ (hxQ x hx))
    have hloc : (fun x => Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ)
        =ᶠ[𝓝 z] (fun x => ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) x θ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hzz] with x hx
      exact ih (by omega) x θ ⟨hx, hθθ⟩
    have hpz : Work.Spaces.pz (Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ
        = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z := by
      show deriv (fun x => Work.Spaces.DzIter k
        (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ) z = _
      rw [hloc.deriv_eq, hcore.deriv]
    have hzne : z ≠ 0 := ne_of_gt hz0
    calc Work.Spaces.DzIter (k + 1)
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter k
            (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ := by
          rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      _ = z * (∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z) := by rw [hpz]
      _ = z * ((∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ) / z) := by
          rw [intervalIntegral.integral_div]
      _ = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ := mul_div_cancel₀ _ hzne
      _ = ∫ s in a..b, Work.Spaces.DzIter (k + 1) (Work.Spaces.DthIter l (H s)) z θ := rfl

end Work.FTS.StrongEps.E5G5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.primitive_mixed_continuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.primitive_mixed_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false



/-! ## The two one-step differentiations -/



/-! ## The statement -/


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.W6.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.W6

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The substitution `f = z^4 κ` -/











/-! ## The derivatives of `(1+z)^{-5}` -/




/-! ## The reciprocal Leibniz bound -/

/-- The coefficient sum `∑_{e ≤ c} C(c,e)·(c-e+4)!/24` is at most `3·10^5` for `c ≤ 6`
(it equals `271801` for `c = 6`). -/
theorem choose_fact_sum_le {c : ℕ} (hc : c ≤ 6) :
    ∑ e ∈ Finset.range (c + 1), ((c.choose e : ℝ) * ((Nat.factorial (c - e + 4) : ℝ) / 24))
      ≤ 3 * 10 ^ 5 := by
  interval_cases c <;> norm_num [Finset.sum_range_succ, Nat.choose, Nat.factorial]


/-! ## The Leibniz expansion of `∂_z^k (z^4 κ)` and the weighted bounds -/







/-- `bell n ≤ 250` for `n ≤ 6` (the values are `1,1,2,5,15,52,203`). -/
theorem bell_le_six {n : ℕ} (hn : n ≤ 6) : Work.Spaces.bell n ≤ 250 := by
  interval_cases n <;> decide


end Work.FTS.StrongPersist.W6
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.LimExtract_bounds10 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option maxHeartbeats 2000000


end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.LimTower_dz3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The order-`3` tower, radial and angular halves.**

This is the order-`3` upgrade of `LimTower_dz`.  Here the mixed jets `D_z^c D_θ^d (G (φ n))`
are assumed to converge locally uniformly on the open quadrant `Q0 = (0,∞) × (0,π/2)` for all
`c + d ≤ 3` (one order more than the hypotheses of `LimTower_dz`).  The conclusion is the same
first-order tower relation `∂_z (F c d) = F (c+1) d / z`, `∂_θ (F c d) = F c (d+1) / sin 2θ`,
now for all `c + d ≤ 2` instead of `c + d ≤ 1`: the *derivative* sequences available are
`mixed (c+1) d` resp. `mixed c (d+1)` with `c + d + 1 ≤ 3`.

The proof is the proof of `LimTower_dz` verbatim — `hasDerivAt_of_tendstoLocallyUniformlyOn`
slicewise, using the defining recursions `D_z^{j+1} = z ∂_z ∘ D_z^j` and
`D_θ^{i+1} = sin 2θ ∂_θ ∘ D_θ^i` of the operators through
`Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen` — with the arithmetic bounds
`c + d + 1 ≤ 3` in place of `c + d + 1 ≤ 2`. -/
theorem LimTower_dz3 {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hconv : ∀ (c d : ℕ), c + d ≤ 3 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (G (φ n)) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0) :
    (∀ (c d : ℕ), c + d ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z) ∧
      (∀ (c d : ℕ), c + d ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) := by
  have hinv : ContinuousOn (fun p : ℝ × ℝ => p.1⁻¹) Work.FTS.EllipticEst.Q0 :=
    ContinuousOn.inv₀ continuousOn_fst
      (fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2))⁻¹)
      Work.FTS.EllipticEst.Q0 :=
    ContinuousOn.inv₀
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      (fun p hp => by
        obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact ne_of_gt (Work.FTS.StrongEps.LocUnif.sin_two_pos_Q0 ⟨h0, h1⟩))
  constructor
  · -- the radial half: `∂_z (F c d) = F (c+1) d / z`
    intro c d hcd z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hmem : ∀ x : ℝ, 0 < x → (x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hx, hθ0, hθ1⟩
    have hcd2 : c + 1 + d ≤ 3 := by omega
    have hmul := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_mul_continuousOn
      (U := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
      (hconv (c + 1) d hcd2) hinv
    have hslice := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_slice_fst
      (U := Work.FTS.EllipticEst.Q0) (θ := θ) (W := Set.Ioi (0 : ℝ)) hmem hmul
    have hf' : TendstoLocallyUniformlyOn
        (fun n x => x⁻¹ * Work.Spaces.mixed (c + 1) d (G (φ n)) x θ)
        (fun x => x⁻¹ * F (c + 1) d x θ) Filter.atTop (Set.Ioi (0 : ℝ)) := hslice
    have hf : ∀ᶠ n in Filter.atTop, ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z' : ℝ => Work.Spaces.mixed c d (G (φ n)) z' θ)
          (x⁻¹ * Work.Spaces.mixed (c + 1) d (G (φ n)) x θ) x :=
      Filter.Eventually.of_forall fun n x hx => by
        have hd := ((hsm (φ n)).mixed c d).hasDerivAt_slice (θ := θ) ⟨hθ0, hθ1⟩ hx
        refine hd.congr_deriv ?_
        rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen c d
          (hsm (φ n))).1 x θ (hmem x hx), div_eq_mul_inv, mul_comm]
    have hfg : ∀ x ∈ Set.Ioi (0 : ℝ), Tendsto
        (fun n => Work.Spaces.mixed c d (G (φ n)) x θ) Filter.atTop (𝓝 (F c d x θ)) :=
      fun x hx => (hconv c d (by omega)).tendsto_at (hmem x hx)
    have key := hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioi hf' hf hfg hz
    exact key.congr_deriv (by rw [div_eq_mul_inv, mul_comm])
  · -- the angular half: `∂_θ (F c d) = F c (d+1) / sin 2θ`
    intro c d hcd z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hmem : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (π / 2) →
        (z, t) ∈ Work.FTS.EllipticEst.Q0 :=
      fun t ht => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, ht.1, ht.2⟩
    have hcd2 : c + (d + 1) ≤ 3 := by omega
    have hmul := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_mul_continuousOn
      (U := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
      (hconv c (d + 1) hcd2) hsin
    have hslice := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_slice_snd
      (U := Work.FTS.EllipticEst.Q0) (z := z) (W := Set.Ioo (0 : ℝ) (π / 2)) hmem hmul
    have hf' : TendstoLocallyUniformlyOn
        (fun n t => (Real.sin (2 * t))⁻¹ * Work.Spaces.mixed c (d + 1) (G (φ n)) z t)
        (fun t => (Real.sin (2 * t))⁻¹ * F c (d + 1) z t)
        Filter.atTop (Set.Ioo (0 : ℝ) (π / 2)) := hslice
    have hf : ∀ᶠ n in Filter.atTop, ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
        HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d (G (φ n)) z θ')
          ((Real.sin (2 * t))⁻¹ * Work.Spaces.mixed c (d + 1) (G (φ n)) z t) t :=
      Filter.Eventually.of_forall fun n t ht => by
        have hd : HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d (G (φ n)) z θ')
            (Work.Spaces.pth (Work.Spaces.mixed c d (G (φ n))) z t) t :=
          (((hsm (φ n)).mixed c d).curry_θ hz).contDiffAt
            (isOpen_Ioo.mem_nhds ⟨ht.1, ht.2⟩) |>.differentiableAt (by simp) |>.hasDerivAt
        refine hd.congr_deriv ?_
        rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen c d
          (hsm (φ n))).2.1 z t (hmem t ht), div_eq_mul_inv, mul_comm]
    have hfg : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2), Tendsto
        (fun n => Work.Spaces.mixed c d (G (φ n)) z t) Filter.atTop (𝓝 (F c d z t)) :=
      fun t ht => (hconv c d (by omega)).tendsto_at (hmem t ht)
    have key := hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioo hf' hf hfg ⟨hθ0, hθ1⟩
    exact key.congr_deriv (by rw [div_eq_mul_inv, mul_comm])

end Work.FTS_EllLimOK
end
-- ===== merged: Submission.Work.GalerkinFix.Extraction.exists_subseq_convLocUnif_of_equicont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.GalerkinFix.Extraction

/-! ## Convergence on a dense set, by equicontinuity

The equicontinuous replacement for `Work.FTS.Galerkin.exists_tendsto_of_tendsto_dense`: the
Lipschitz bound `L * dist q p` is replaced by an arbitrary uniform modulus of continuity of the
family at `p`. -/


/-! ## The extraction on the slab -/


end Work.GalerkinFix.Extraction
end
end
-- ===== merged: Submission.Work.H2W.asliceLzero1Energy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The twice radially differentiated slice -/

/-- `sliceQ Ψ = z² ∂_z²Ψ`, the second radially differentiated slice of `Ψ`. -/
def sliceQ (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- `z²∂_z²Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_sliceQ {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (sliceQ Ψ) :=
  Work.FTS.EllipticEst.remov.SourceBound.smoothOpen_zsq_mul_pzIter_two h

/-- The smooth representative of the right-hand side of the identity of the module docstring:
`z²∂_z²(bslOp α Ψ) + α²D_z²(z²∂_z²Ψ) + 5αD_z(z²∂_z²Ψ)`, with the source replaced by the
`C^∞` function `bslOp α Ψ` (which agrees with `F` on the open quadrant only). -/
def sliceBF (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
    + α ^ 2 * Work.Spaces.DzIter 2 (sliceQ Ψ) z θ
    + 5 * α * Work.Spaces.DzIter 1 (sliceQ Ψ) z θ

/-- `sliceBF α Ψ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_sliceBF (α : ℝ) {Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (sliceBF α Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ) :=
    Work.FTS.EllipticEst.remov.SourceBound.smoothOpen_zsq_mul_pzIter_two
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen h)
  have h2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 2 (sliceQ Ψ)) :=
    (smoothOpen_sliceQ h).DzIter 2
  have h3 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 (sliceQ Ψ)) :=
    (smoothOpen_sliceQ h).DzIter 1
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl h1
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) h2))
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (5 * α) h3)) ?_
  intro z θ _ _ _
  rfl

/-! ## The two algebraic identities on the open quadrant -/

/-- **The radial identity for the source.**  On the open quadrant, where `bslOp α Ψ = F`, one has
`z²∂_z²(bslOp α Ψ) = z²∂_z²F`, and since `z²∂_z²g = D_z²g - D_zg` for `C^∞` `g`
(`AgmonSlice.zsq_pzIter2_eq_open`), also `z²∂_z²(bslOp α Ψ) = D_z²F - D_zF`. -/
theorem zsq_pzIter2_bslOp_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hSO : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
        = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hSO
  have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
      = Work.Spaces.DzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
        - Work.Spaces.DzIter 1 (Work.Elliptic.bslOp α Ψ) z θ := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open (Work.Elliptic.bslOp α Ψ) hFso hz hθ
  rw [h1, Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := Work.Elliptic.bslOp α Ψ)
      (G := F) heq 2 z θ hz hθ0 hθ1,
    Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := Work.Elliptic.bslOp α Ψ)
      (G := F) heq 1 z θ hz hθ0 hθ1]

/-- **The source identity for the twice radially differentiated slice.**  On the open quadrant,

  `Lzero (z²∂_z²Ψ) = D_z²F - D_zF + α² D_z²(z²∂_z²Ψ) + 5α D_z(z²∂_z²Ψ)`,

equivalently `Lzero1 (fun θ' => z²∂_z²Ψ (z,θ')) θ = sliceBF α Ψ z θ`.  This is the identity
that removes the singular angular coefficients of `Lzero1`. -/
theorem Lzero1_slice_eq_sliceBF (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hSO : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Lzero1 (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
        = sliceBF α Ψ z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hQso : Work.FTS.EllipticEst.SmoothOpen (sliceQ Ψ) := smoothOpen_sliceQ hSO
  have hBF : z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
      = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ :=
    zsq_pzIter2_bslOp_eq α F Ψ heq hSO z θ hz hθ0 hθ1
  -- the equation for the `z²∂_z²`-slice, from the commutation of `bslOp α` with `z²∂_z²`
  have hbsl : Work.Elliptic.bslOp α (sliceQ Ψ) z θ = z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
    change Work.Elliptic.bslOp α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 F z θ
    exact
      Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2 α F Ψ
        (fun z hz' θ hθ0' hθ1' => heq z θ hz' hθ0' hθ1')
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hSO) z hz θ hθ0 hθ1
  -- `Lzero` expressed through `bslOp`, in the `z²∂_z²` form of each radial slot
  have hlin : Work.Elliptic.Lzero (sliceQ Ψ) z θ
      = Work.Elliptic.bslOp α (sliceQ Ψ) z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (sliceQ Ψ) z θ)
        + (α * (5 + α)) * (z * Work.Spaces.pz (sliceQ Ψ) z θ) := by
    simp only [Work.Elliptic.bslOp_apply]
    ring
  have hQ2 : z ^ 2 * Work.Spaces.pzIter 2 (sliceQ Ψ) z θ
      = Work.Spaces.DzIter 2 (sliceQ Ψ) z θ - Work.Spaces.DzIter 1 (sliceQ Ψ) z θ := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open (sliceQ Ψ) hQso hz hθ
  have hz1 : z * Work.Spaces.pz (sliceQ Ψ) z θ = Work.Spaces.DzIter 1 (sliceQ Ψ) z θ := rfl
  have hF2 : z ^ 2 * Work.Spaces.pzIter 2 F z θ
      = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := by
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 F z θ
        = z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ := by
      congr 1
      refine Work.Elliptic.pzIter_congr_nhds 2 ?_
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact (heq z' θ hz' hθ0 hθ1).symm
    rw [h1, hBF]
  have hstep : Work.FTS.EllipticEst.Lzero1 (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
      = Work.Elliptic.Lzero (sliceQ Ψ) z θ :=
    Work.FTS.EllipticEst.remov.Lzero1_slice_eq (sliceQ Ψ) z θ
  rw [hstep, hlin, hbsl, hF2, hQ2, hz1]
  simp only [sliceBF]
  rw [hBF]
  ring

/-! ## Elementary square bounds -/

private theorem add_sq_le_three_aux (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

private theorem sub_sq_le_two_aux (a b : ℝ) : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a + b)]

/-! ## The target -/

theorem asliceLzero1Energy (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1
          (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  intro z hz
  have hSO : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hQso : Work.FTS.EllipticEst.SmoothOpen (sliceQ Ψ) := smoothOpen_sliceQ hSO
  have hBFso : Work.FTS.EllipticEst.SmoothOpen (sliceBF α Ψ) := smoothOpen_sliceBF α hSO
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hSO
  have heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ :=
    fun z θ hz' hθ0 hθ1 => h.eq z hz' θ hθ0 hθ1
  have hid := Lzero1_slice_eq_sliceBF α F Ψ heq hSO
  have hBF := zsq_pzIter2_bslOp_eq α F Ψ heq hSO
  -- a.e. strong measurability of the target integrand, from the `C^∞` representative
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.FTS.EllipticEst.Lzero1
          (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (Work.FTS.EllipticEst.remov.SourceBound.aesm_slice_sq_mul_sEta
      hBFso.continuousOn hz).congr ?_
    filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
    rw [hid z θ hz hθ.1 hθ.2]
  -- the four `D_z`-slots of the three `HkMem` fields
  have hmemQ : Work.Spaces.HkMem α 2 (sliceQ Ψ) := h.memA
  have hAESM_Q : ∀ i : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.Spaces.DzIter i (sliceQ Ψ) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun i => Work.FTS.EllipticEst.remov.SourceBound.aesm_slice_sq_mul_sEta
      ((hQso.DzIter i).continuousOn) hz
  have hAESM_F : ∀ i : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.Spaces.DzIter i F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro i
    refine (Work.FTS.EllipticEst.remov.SourceBound.aesm_slice_sq_mul_sEta
      ((hFso.DzIter i).continuousOn) hz).congr ?_
    filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
    rw [← Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := Work.Elliptic.bslOp α Ψ)
      (G := F) heq i z θ hz hθ.1 hθ.2]
  have hintQ : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter i (sliceQ Ψ) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    fun i hi => Work.FTS.EllipticEst.remov.SourceBound.integrableOn_DzIter_sq_mul_sEta
      hmemQ i hi hz (hAESM_Q i)
  have hintF : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter i F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    fun i hi => Work.FTS.EllipticEst.remov.SourceBound.integrableOn_DzIter_sq_mul_sEta
      h.memF i hi hz (hAESM_F i)
  -- the pointwise majorant
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => 3 * (((2 * ((Work.Spaces.DzIter 2 F z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
          + 2 * ((Work.Spaces.DzIter 1 F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          + α ^ 4 * ((Work.Spaces.DzIter 2 (sliceQ Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ))
        + 25 * α ^ 2 * ((Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ))) Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => 2 * ((Work.Spaces.DzIter 2 F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        Work.Spaces.Iθ := (hintF 2 le_rfl).const_mul 2
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => 2 * ((Work.Spaces.DzIter 1 F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        Work.Spaces.Iθ := (hintF 1 (by norm_num)).const_mul 2
    have h3 : MeasureTheory.IntegrableOn
        (fun θ => α ^ 4 * ((Work.Spaces.DzIter 2 (sliceQ Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iθ :=
      (hintQ 2 le_rfl).const_mul (α ^ 4)
    have h4 : MeasureTheory.IntegrableOn
        (fun θ => 25 * α ^ 2 * ((Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iθ :=
      (hintQ 1 (by norm_num)).const_mul (25 * α ^ 2)
    have hsum := (((h1.add h2).add h3).add h4).const_mul 3
    exact hsum
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
  have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.remov.SourceBound.sEta_nonneg_Ioo hθ
  rw [hid z θ hz hθ.1 hθ.2, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hs)]
  simp only [sliceBF]
  rw [hBF z θ hz hθ.1 hθ.2]
  have hfin : (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ
        + α ^ 2 * Work.Spaces.DzIter 2 (sliceQ Ψ) z θ
        + 5 * α * Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2
      ≤ 3 * ((2 * (Work.Spaces.DzIter 2 F z θ) ^ 2
            + 2 * (Work.Spaces.DzIter 1 F z θ) ^ 2)
          + α ^ 4 * (Work.Spaces.DzIter 2 (sliceQ Ψ) z θ) ^ 2
          + 25 * α ^ 2 * (Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2) := by
    have h3 := add_sq_le_three_aux (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
      (α ^ 2 * Work.Spaces.DzIter 2 (sliceQ Ψ) z θ)
      (5 * α * Work.Spaces.DzIter 1 (sliceQ Ψ) z θ)
    have h2 := sub_sq_le_two_aux (Work.Spaces.DzIter 2 F z θ) (Work.Spaces.DzIter 1 F z θ)
    nlinarith [h3, h2]
  calc (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ
        + α ^ 2 * Work.Spaces.DzIter 2 (sliceQ Ψ) z θ
        + 5 * α * Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      ≤ 3 * ((2 * (Work.Spaces.DzIter 2 F z θ) ^ 2
            + 2 * (Work.Spaces.DzIter 1 F z θ) ^ 2)
          + α ^ 4 * (Work.Spaces.DzIter 2 (sliceQ Ψ) z θ) ^ 2
          + 25 * α ^ 2 * (Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2)
        * Work.FTS.EllipticEst.sEta θ := mul_le_mul_of_nonneg_right hfin hs
    _ = 3 * (((2 * ((Work.Spaces.DzIter 2 F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 2 * ((Work.Spaces.DzIter 1 F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          + α ^ 4 * ((Work.Spaces.DzIter 2 (sliceQ Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ))
        + 25 * α ^ 2 * ((Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)) := by
        ring

end Work.H2W
end
end
-- ===== merged: Submission.Work.H2W.asliceMomentEq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-! ## Honesty of a `D_z`-slot against the angular profile -/

/-- **A `D_z`-slot of an `ℋ^k`-function is integrable against `sinθcos²θ`.**

For `g` of class `C^∞` on the open quadrant with `Work.Spaces.HkMem α k g` one has, for every
`i ≤ k` and every `z > 0`, the `θ`-integrability

  `∫_θ |D_z^i g(z,θ) · sinθcos²θ| < ∞`.

The proof is the pointwise domination `|g·sinθcos²θ| ≤ (g·w(z)/sin(2θ)^{η/2})² + 1`, whose
first summand is a single summand of the `ℋ^k`-integrand `HkIntegrand` (`sq_le_HkIntegrand_z`
and `abs_mul_sinCos2_le_weighted`), together with the a.e. strong measurability of the slice
(continuity of `D_z^i g` on the open quadrant). -/
theorem integrableOn_DzIter_mul_sinCos2 {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter i g z θ * sg θ) Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hvol : MeasureTheory.volume Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hsin : Continuous (fun p : ℝ × ℝ => sg p.2) := by
    simp only [Work.Elliptic.sinCos2]; fun_prop
  refine MeasureTheory.Integrable.mono'
    ((hm.1 z hzI).add (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol))
    (Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.DzIter i g p.1 p.2 * sg p.2)
      ((hsm.DzIter i).continuousOn.mul hsin.continuousOn) hz) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs]
  have h1 := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
    (f := fun θ => Work.Spaces.DzIter i g z θ) hz hθ
  have h2 := Work.Spaces.sq_le_HkIntegrand_z α k g z θ i hi
  simp only [Pi.add_apply]
  linarith

/-! ## The pointwise differentiated-equation identity -/

/-- **The elliptic equation, twice radially differentiated, read on the slice `z²∂_z²Ψ`.**

On the open quadrant,
`Lzero1 (z²∂_z²Ψ(z,·)) = (D_z²F - D_zF) + α²D_z²(z²∂_z²Ψ) + 5αD_z(z²∂_z²Ψ)`.

The identity is the combination of `H2W.bslOp_zsq_pzIter2` (`bslOp α (z²∂_z²Ψ) = z²∂_z²F`,
i.e. `= D_z²F - D_zF`) with the elementary relations `z²∂_z² = D_z² - D_z` and
`z∂_z = D_z`. -/
theorem lzero1_zsq_pzIter2_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hFs : Work.FTS.EllipticEst.SmoothOpen F)
    (hΨs : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Lzero1 (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
      = (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
        + α ^ 2 * Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + 5 * α * Work.Spaces.DzIter 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.H2W.MomentAe.smoothOpen_zsq hΨs
  have hbsl : Work.Elliptic.bslOp α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := by
    rw [Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2 α F Ψ heq hsm z hz θ hθ0 hθ1,
      Work.H2W.MomentAe.zsq_pzIter2_eq hFs hz hθI]
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  have hdec : Work.Elliptic.Lzero (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.Elliptic.bslOp α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
        + α * (5 + α) * z * Work.Spaces.pz
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
    rw [Work.Elliptic.bslOp_apply]; ring
  have hAA : z ^ 2 * Work.Spaces.pzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        - Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    Work.H2W.MomentAe.zsq_pzIter2_eq hA hz hθI
  have hstep : Work.FTS.EllipticEst.Lzero1
      (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
      = Work.Elliptic.Lzero (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := rfl
  rw [hstep, hdec, hbsl, hAA]
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  ring

/-! ## The moment identities of the two `A`-slots -/

/-- `F_*(D_zA) = 0` on the open quadrant: the a.e. identity `D_zA = D_z³Ψ - D_z²Ψ` turns the
moment of `D_zA` into the difference of the two vanishing moments of `D_z³Ψ` and `D_z²Ψ`. -/
theorem fstar_zsq_Dz_eq_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hΨs : Work.FTS.EllipticEst.SmoothOpen Ψ) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z = 0 := by
  have hmom3 : Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z = 0 :=
    Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 3 (by norm_num) z hz
  have hmom2 : Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z = 0 :=
    Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 2 (by norm_num) z hz
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 3 Ψ z θ * sg θ) Iθ :=
    (Work.H2W.MomentAe.level_bound hΨs h.memA h.memB 3 (by norm_num)).1 z hz
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 2 Ψ z θ * sg θ) Iθ :=
    (Work.H2W.MomentAe.level_bound hΨs h.memA h.memB 2 (by norm_num)).1 z hz
  have hae : (fun θ => Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => Work.Spaces.DzIter 3 Ψ z θ * sg θ
        - Work.Spaces.DzIter 2 Ψ z θ * sg θ) := by
    filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
    rw [Work.H2W.MomentAe.DzIter_zsq_pzIter2_eq hΨs 1 hz hθ]
    ring
  calc Work.Elliptic.Fstar (Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z
      = ∫ θ in Iθ, Work.Spaces.DzIter 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ := rfl
    _ = ∫ θ in Iθ, (Work.Spaces.DzIter 3 Ψ z θ * sg θ
          - Work.Spaces.DzIter 2 Ψ z θ * sg θ) := MeasureTheory.integral_congr_ae hae
    _ = (∫ θ in Iθ, Work.Spaces.DzIter 3 Ψ z θ * sg θ)
          - (∫ θ in Iθ, Work.Spaces.DzIter 2 Ψ z θ * sg θ) :=
        MeasureTheory.integral_sub h3 h2
    _ = Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z
          - Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z := rfl
    _ = 0 := by rw [hmom3, hmom2, sub_self]

/-- `F_*(D_z²A) = F_*(D_z⁴Ψ)` on the open quadrant: the a.e. identity
`D_z²A = D_z⁴Ψ - D_z³Ψ` together with the vanishing of `F_*(D_z³Ψ)`. -/
theorem fstar_DzIter_two_zsq_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hΨs : Work.FTS.EllipticEst.SmoothOpen Ψ) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z
      = Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z := by
  have hA2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        z θ * sg θ) Iθ :=
    integrableOn_DzIter_mul_sinCos2 (Work.H2W.MomentAe.smoothOpen_zsq hΨs) h.memA 2 le_rfl hz
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 3 Ψ z θ * sg θ) Iθ :=
    (Work.H2W.MomentAe.level_bound hΨs h.memA h.memB 3 (by norm_num)).1 z hz
  have h4 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 4 Ψ z θ * sg θ) Iθ := by
    have hae : (fun θ => Work.Spaces.DzIter 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ
          + Work.Spaces.DzIter 3 Ψ z θ * sg θ)
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => Work.Spaces.DzIter 4 Ψ z θ * sg θ) := by
      filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
      rw [Work.H2W.MomentAe.DzIter_zsq_pzIter2_eq hΨs 2 hz hθ]
      ring
    exact (hA2.add h3).congr hae
  have hmom3 : Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z = 0 :=
    Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 3 (by norm_num) z hz
  have hae2 : (fun θ => Work.Spaces.DzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => Work.Spaces.DzIter 4 Ψ z θ * sg θ
        - Work.Spaces.DzIter 3 Ψ z θ * sg θ) := by
    filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
    rw [Work.H2W.MomentAe.DzIter_zsq_pzIter2_eq hΨs 2 hz hθ]
    ring
  calc Work.Elliptic.Fstar (Work.Spaces.DzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z
      = ∫ θ in Iθ, Work.Spaces.DzIter 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ := rfl
    _ = ∫ θ in Iθ, (Work.Spaces.DzIter 4 Ψ z θ * sg θ
          - Work.Spaces.DzIter 3 Ψ z θ * sg θ) := MeasureTheory.integral_congr_ae hae2
    _ = (∫ θ in Iθ, Work.Spaces.DzIter 4 Ψ z θ * sg θ)
          - (∫ θ in Iθ, Work.Spaces.DzIter 3 Ψ z θ * sg θ) :=
        MeasureTheory.integral_sub h4 h3
    _ = Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z
          - Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z := rfl
    _ = Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z := by rw [hmom3, sub_zero]

/-! ## The target -/

theorem asliceMomentEq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z, 0 < z →
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1
          (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
        = Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z
          + α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z := by
  intro z hz
  have hΨs : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨hFs, -, hAs, -⟩ := Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0
  -- the four honest slots
  have hF1 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1 F z θ * sg θ) Iθ :=
    integrableOn_DzIter_mul_sinCos2 hFs h.memF 1 (by norm_num) hz
  have hF2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 2 F z θ * sg θ) Iθ :=
    integrableOn_DzIter_mul_sinCos2 hFs h.memF 2 le_rfl hz
  have hA1 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ) Iθ :=
    integrableOn_DzIter_mul_sinCos2 hAs h.memA 1 (by norm_num) hz
  have hA2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ) Iθ :=
    integrableOn_DzIter_mul_sinCos2 hAs h.memA 2 le_rfl hz
  -- the integrand identity on the open interval, and the termwise integration
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ * sg θ
        = ((Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
            + α ^ 2 * Work.Spaces.DzIter 2
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + 5 * α * Work.Spaces.DzIter 1
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ := by
    intro θ hθ
    rw [lzero1_zsq_pzIter2_eq h.eq h.smooth hFs hΨs hz hθ.1 hθ.2]
  have hsplit : (fun θ => ((Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
        + α ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + 5 * α * Work.Spaces.DzIter 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ)
      = (fun θ => Work.Spaces.DzIter 2 F z θ * sg θ)
        - (fun θ => Work.Spaces.DzIter 1 F z θ * sg θ)
        + (fun θ => α ^ 2 * (Work.Spaces.DzIter 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ))
        + (fun θ => 5 * α * (Work.Spaces.DzIter 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)) := by
    funext θ
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hid : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1
        (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ * sg θ)
      = Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z
        + α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z
        + 5 * α * Work.Elliptic.Fstar (Work.Spaces.DzIter 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z := by
    have hae : (fun θ => Work.FTS.EllipticEst.Lzero1
          (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ * sg θ)
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => ((Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
            + α ^ 2 * Work.Spaces.DzIter 2
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + 5 * α * Work.Spaces.DzIter 1
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ) :=
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt
    have hsplit : (fun θ => ((Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
          + α ^ 2 * Work.Spaces.DzIter 2
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + 5 * α * Work.Spaces.DzIter 1
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ)
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => Work.Spaces.DzIter 2 F z θ * sg θ
          - Work.Spaces.DzIter 1 F z θ * sg θ
          + α ^ 2 * (Work.Spaces.DzIter 2
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)
          + 5 * α * (Work.Spaces.DzIter 1
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)) := by
      filter_upwards with θ
      ring
    rw [MeasureTheory.integral_congr_ae (hae.trans hsplit)]
    rw [MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_add]
      · rw [MeasureTheory.integral_sub]
        · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          rfl
        · exact hF2
        · exact hF1
      · exact hF2.sub hF1
      · exact hA2.const_mul (α ^ 2)
    · exact (hF2.sub hF1).add (hA2.const_mul (α ^ 2))
    · exact hA1.const_mul (5 * α)
  -- the moment values
  have hF1zero : Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 :=
    Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two le_rfl h z hz
  have hA1zero := fstar_zsq_Dz_eq_zero h hΨs hz
  have hA2eq := fstar_DzIter_two_zsq_eq h hΨs hz
  rw [hid, hF1zero, hA1zero, hA2eq]
  ring

end Work.H2W
end
end
