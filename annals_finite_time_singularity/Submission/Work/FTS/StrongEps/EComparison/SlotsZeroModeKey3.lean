/-
# `SlotsZeroModeKey3` - the vanishing of the mode pairing (the last step of
`SlotsZeroModeODE`)

Part of `Work.FTS.StrongEps.EComparison.SlotsZeroModeODE`.  This module carries `key_iter`, the
vanishing of the pairing of a homogeneous `bslOp`-solution `Φ` with `bslOp α (ρ ⊗ e_m)` against
the self-adjoint weight `z^((5-α)/α)·cos θ`; the statement of the target itself lives in the
sibling file `SlotsZeroModeODE.lean`.

## Route

`bslOp α Ψ` is not compactly supported in `θ`, so the integration-by-parts identity
`Work.EllipticEst.ModalSolution.bslOp_ibp` does not apply to the test function `ρ ⊗ e_m` itself.
It does apply to the cut-off test functions `ρ ⊗ (χ_n·e_m)` with `χ_n = angCut n`, giving
`perN_zero_set`, and the two integrands differ only where `χ_n ≠ 1`, i.e. on the two boundary
layers `layer n = (0,2δ_n) ∪ (π/2-2δ_n, π/2)` (`δ_n = 1/(n+1)`), where the difference is bounded
by `A(1+1/δ_n)|Φ|·1_{[a,b]}(z)·1_{layer n}(θ)` (`SlotsZeroDiffBound`).  The `ℋ⁶`-membership of
`Φ/sin 2θ` gives `∫_{layer} |Φ| ≲ √(sliceEnergy Φ z)·δ_n^{(3+η)/2}` on each `z`-slice
(`SlotsZeroLayerSetBound`), and `(1+1/δ_n)δ_n^{(3+η)/2} = O(δ_n^{(1+η)/2}) → 0`
(`SlotsZeroLayerTendsto`).  Hence the pairing with `ρ ⊗ e_m` vanishes as well, and
`SlotsZeroPairingFubini` rewrites the product-measure integral as the iterated integral of the
statement.

## Contents

* `ae_eq_of_forall_ne`, `integrableOn_mul_of_abs_le`, `continuousOn_slice_of_continuousOn` -
  small technical helpers;
* `key_iter` - the vanishing of the pairing.

The four inputs `SlotsZeroLayerSetBound`, `SlotsZeroLayerTendsto`, `SlotsZeroPairingFubini` and
`SlotsZeroDiffBound` are the delegated sibling modules imported below.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.bslOp_ibp
import Submission.Work.FTS.ClassC.psiTrunc_uncurry_smooth
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeMain
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeIbp
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeKey
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeKey2
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeL2
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroCutoff
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroLayerSetBound
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroLayerTendsto
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroPairingFubini
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroDiffBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- Two functions which agree off a single point agree almost everywhere. -/
theorem ae_eq_of_forall_ne {f g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s) {c : ℝ}
    (h : ∀ x ∈ s, x ≠ c → f x = g x) : f =ᵐ[volume.restrict s] g := by
  change ∀ᵐ x ∂(volume.restrict s), f x = g x
  rw [MeasureTheory.ae_restrict_iff' hs, MeasureTheory.ae_iff]
  refine measure_mono_null (t := {c}) (fun x hx => ?_) (measure_singleton c)
  by_contra hne
  exact hx (fun hxs => h x hxs hne)

/-- A function bounded by a constant multiple of an integrable one is integrable. -/
theorem integrableOn_mul_of_abs_le {u v : ℝ → ℝ} {B' : ℝ}
    (hu : MeasureTheory.IntegrableOn (fun θ => |u θ|) Work.Spaces.Iθ) (hB : 0 ≤ B')
    (hv : ∀ θ, |v θ| ≤ B')
    (hsm : AEStronglyMeasurable (fun θ => u θ * v θ) (volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => u θ * v θ) Work.Spaces.Iθ := by
  refine Integrable.mono' (hu.integrable.mul_const B') hsm ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hv θ) (abs_nonneg _)

/-- The slice of a function continuous on the open quadrant is continuous on `(0,π/2)`. -/
theorem continuousOn_slice_of_continuousOn {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {z : ℝ}
    (hz : 0 < z) : ContinuousOn (fun θ => G z θ) (Set.Ioo 0 (π / 2)) :=
  hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => ⟨hz, hθ⟩)

/-- **The vanishing of the mode pairing.**  The pairing of `Φ` against `bslOp α (ρ ⊗ e_m)` with
the self-adjoint weight `z^((5-α)/α)·cos θ` vanishes.  Pair the equation `bslOp α Φ = 0` against
the compactly supported cut-off test functions `ρ ⊗ (χ_n·e_m)` (`perN_zero_set`); the difference
of the two integrands is supported in the two boundary layers of width `2δ_n` and is bounded by
`abs_sub_modeTest_le` (`SlotsZeroDiffBound`), whose integral is `O(δ_n^((1+η)/2))` by the layer
estimate (`SlotsZeroLayerSetBound`) and hence tends to `0` (`SlotsZeroLayerTendsto`).  The last
identification of the product-measure integral with the iterated one is `SlotsZeroPairingFubini`.
-/
theorem key_iter {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ} {C : ℝ} {a b : ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsol : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Φ z θ = 0)
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) (hρc : HasCompactSupport ρ) (hρs : tsupport ρ ⊆ Set.Ioi 0)
    (hCut : CutFacts m)
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hC : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (π / 4),
      (∫ θ in Set.Ioo 0 δ, |Φ z θ|)
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2) ∧
      (∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|)
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2))
    (hCpos : 0 ≤ C)
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b))
    (hEsqrt : MeasureTheory.IntegrableOn (fun z => Real.sqrt (sliceEnergy Φ z)) (Set.Icc a b))
    (ha : 0 < a) (hsub : tsupport ρ ⊆ Set.Icc a b) :
    (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Φ z θ
      * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
      * (z ^ ((5 - α) / α) * Real.cos θ)) = 0 := by
  classical
  obtain ⟨A, hA0, hAdiff⟩ := SlotsZeroDiffBound (α := α) (Φ := Φ) (ρ := ρ) (m := m)
    (a := a) (b := b) hsm hρ hCut hΦint hEint ha hsub
  have hbox : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => |Φ p.1 p.2|
      * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) Work.FTS.EllipticEst.Q0 :=
    integrableOn_absPhi_box hsm hΦint hEint
  have hf : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Φ p.1 p.2
      * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      * bslWeight α p) Work.FTS.EllipticEst.Q0 :=
    integrableOn_modeIntegrand (α := α) (Φ := Φ) (ρ := ρ) (m := m) hsm hρ ha hsub hbox
  have hM0 : 0 ≤ ∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z) :=
    integral_nonneg (fun z => Real.sqrt_nonneg _)
  have hstep : ∀ n : ℕ, 2 ≤ n →
      |∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            p.1 p.2
        * bslWeight α p|
      ≤ A * (1 + 1 / delta n) * (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)
          * (∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z))) := by
    intro n hn2
    have hδpos : 0 < delta n := hCut.delta_pos n
    have hn0 : 0 < 2 * delta n := by linarith
    have hn1 : 2 * delta n ≤ π / 4 := by
      have h1 : delta n ≤ 1 / 3 := by
        rw [delta]
        refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) ?_
        have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        linarith
      have h3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
      linarith
    obtain ⟨hdnint, hdnbnd⟩ := hAdiff n
    have hzero : (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p) = 0 :=
      perN_zero_set (α := α) (Φ := Φ) (ρ := ρ) (m := m) hsm hsol hρ hρc hρs hCut n
    have hsplit : (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p)
        = (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
            * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
                p.1 p.2 * bslWeight α p)
          + ∫ p in Work.FTS.EllipticEst.Q0,
              (Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
                - Φ p.1 p.2 * Work.Elliptic.bslOp α
                    (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
                  * bslWeight α p) := by
      have hcongr : (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
          * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p)
          = ∫ p in Work.FTS.EllipticEst.Q0,
              ((Φ p.1 p.2 * Work.Elliptic.bslOp α (fun z θ => ρ z
                    * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2 * bslWeight α p)
                + (Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
                  - Φ p.1 p.2 * Work.Elliptic.bslOp α (fun z θ => ρ z
                      * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2 * bslWeight α p)) :=
        MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => by ring)
      rw [hcongr, MeasureTheory.integral_add hf hdnint]
    have h7 : (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            p.1 p.2 * bslWeight α p)
        = -(∫ p in Work.FTS.EllipticEst.Q0,
              (Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
                - Φ p.1 p.2 * Work.Elliptic.bslOp α
                    (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
                  * bslWeight α p)) := by linarith [hsplit, hzero]
    have hL : (∫ p in Work.FTS.EllipticEst.Q0, |Φ p.1 p.2|
          * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
        ≤ 2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)
          * (∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z)) :=
      SlotsZeroLayerSetBound (Φ := Φ) (C := C) (a := a) (b := b)
        hsm hΦint hC hEint hEsqrt ha hn0 hn1
    calc |∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
            * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
                p.1 p.2 * bslWeight α p|
        = |∫ p in Work.FTS.EllipticEst.Q0,
              (Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
                - Φ p.1 p.2 * Work.Elliptic.bslOp α
                    (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
                  * bslWeight α p)| := by rw [h7, abs_neg]
      _ ≤ ∫ p in Work.FTS.EllipticEst.Q0, |Φ p.1 p.2
            * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
            - Φ p.1 p.2 * Work.Elliptic.bslOp α
                (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
              * bslWeight α p| := abs_integral_le_integral_abs
      _ ≤ A * (1 + 1 / delta n) * (∫ p in Work.FTS.EllipticEst.Q0, |Φ p.1 p.2|
            * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2) := hdnbnd
      _ ≤ A * (1 + 1 / delta n) * (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)
            * (∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z))) := by
          refine mul_le_mul_of_nonneg_left hL ?_
          exact mul_nonneg hA0 (add_nonneg zero_le_one (div_nonneg zero_le_one hδpos.le))
  have htend : Filter.Tendsto (fun n : ℕ => A * (1 + 1 / delta n)
      * (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)
          * (∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z)))) Filter.atTop (nhds 0) :=
    SlotsZeroLayerTendsto (A := A) (C := C)
      (M := ∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z)) hA0 hCpos hM0
  have hbound : |∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            p.1 p.2 * bslWeight α p| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds htend
      (eventually_atTop.mpr ⟨2, fun n hn => hstep n hn⟩)
  have hfzero : (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
      * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      * bslWeight α p) = 0 :=
    abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  rw [← SlotsZeroPairingFubini (α := α) (Φ := Φ) (ρ := ρ) (m := m) (a := a) (b := b)
    hsm hρ ha hsub hΦint hEint]
  exact hfzero

/-! ## The two delegated modules instantiate the bundles -/

example {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hHk : Work.Spaces.HkMem α 6 (fun z θ => Φ z θ / Work.Construction.s2 θ)) :
    L2Facts α Φ :=
  SlotsZeroModeL2 hsm hHk

example (m : ℕ) : CutFacts m := SlotsZeroCutoff m


end Work.FTS.StrongEps.EComparison
