/-
# `SlotsZeroDiffBound` — the `L¹` difference bound for the cut-off mode test function

This module proves `Work.FTS.StrongEps.EComparison.SlotsZeroDiffBound`: for `Φ` smooth on the
open quadrant, `ρ` smooth with `tsupport ρ ⊆ [a,b]`, `0 < a`, and the shrinking cut-off data
`CutFacts m`, there is a constant `A ≥ 0` such that for every `n`

  `∫_{Q0} |Φ·(bslOp α (modeTest m ρ n))·wgt − Φ·(bslOp α (ρ ⊗ e_m))·wgt|
      ≤ A·(1 + 1/δ_n)·∫_{Q0} |Φ|·1_{[a,b]}(z)·1_{layer_n}(θ)`,

together with the product-measure integrability of the difference integrand.

The mathematics is entirely pointwise: the cut-off test function `modeTest m ρ n = ρ ⊗ (χ_n e_m)`
satisfies `bslOp α (modeTest) = χ_n·bslOp α (ρ ⊗ e_m) + ρ·comm_n` (the proved
`bslOp_modeTest`), and on the support box `[a,b]` all the factors are bounded, while
`|χ_n − 1| ≤ 1_{layer_n}` and `|comm_n| ≤ C/δ_n·1_{layer_n}` (the `CutFacts` commutator bound).
The only care needed is that the resulting constant `(B + C_ρ C_c)·W` be *independent of `n`*,
so that a single `A` serves all `n`; this is why the pointwise estimate is re-derived here in its
uniform-in-`n` form (`abs_sub_modeTest_le_uniform`) rather than through the per-`n`
`abs_sub_modeTest_le` of `SlotsZeroModeKey2`.

The passage from the pointwise bound to the integral goes through the product-measure
integrability of `|Φ|·1_{[a,b]}(z)` (`integrableOn_absPhi_box`, from `hΦint` + `hEint`) and the
elementary fact that multiplying by the indicator of `layer_n` is a restriction to a measurable
set (dominated integrability), followed by the monotonicity of the integral.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeKey2

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

/-! ## The pointwise difference bound with a constant independent of `n` -/

/-- **The difference of the cut-off integrand and the model integrand**, with a constant that is
independent of the cut-off index `n`.  This is the uniform-in-`n` form of
`SlotsZeroModeKey2.abs_sub_modeTest_le` (whose constant is the same but is not stated to be
`n`-independent); it is what allows a single `A` to serve all `n` in `SlotsZeroDiffBound`. -/
theorem abs_sub_modeTest_le_uniform {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ}
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) {a b : ℝ} (ha : 0 < a)
    (hsub : tsupport ρ ⊆ Set.Icc a b) (hCut : CutFacts m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ Work.FTS.EllipticEst.Q0 →
      |Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
        - Φ p.1 p.2 * Work.Elliptic.bslOp α
            (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
          * bslWeight α p|
        ≤ C * (1 + 1 / delta n) * (|Φ p.1 p.2|
            * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_bslOp_Psi (α := α) hρ hsub
  obtain ⟨Cr, hCr0, hCr⟩ := exists_bound_abs_rho hρ hsub
  obtain ⟨Cc, hCc0, hCc⟩ := hCut.2.2.2.2.2.2
  obtain ⟨W, hW0, hW⟩ := abs_bslWeight_mul_indicator_le (α := α) ha
  refine ⟨(B + Cr * Cc) * W, by positivity, fun n p hp => ?_⟩
  have hδ : 0 < delta n := hCut.delta_pos n
  classical
  obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hcos : Real.cos p.2 ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  -- split the difference
  have hsplit : Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
      - Φ p.1 p.2 * Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2 * bslWeight α p
      = Φ p.1 p.2 * ((angCut n p.2 - 1) * Work.Elliptic.bslOp α
            (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
          + ρ p.1 * comm m n p.2) * bslWeight α p := by
    rw [bslOp_modeTest (α := α) hcos]
    ring
  rw [hsplit, abs_mul, abs_mul]
  -- bound each factor
  have hA : |angCut n p.2 - 1| ≤ layerInd n p.2 := by
    by_cases h : 2 * delta n ≤ p.2 ∧ p.2 ≤ π / 2 - 2 * delta n
    · have h1 := hCut.eq_one_off_layer n h.1 h.2
      rw [h1, sub_self, abs_zero]
      exact indicator_one_nonneg p.2
    · rw [abs_sub_le_iff, layerInd, Set.indicator_apply]
      split_ifs with hmem
      · exact ⟨by linarith [(hCut.bounds n p.2).2], by linarith [(hCut.bounds n p.2).1]⟩
      · have h2δ : 2 * delta n ≤ p.2 := by
          by_contra hcon
          simp only [not_le] at hcon
          exact hmem (Or.inl ⟨hθ0, hcon⟩)
        have hπ : p.2 ≤ π / 2 - 2 * delta n := by
          by_contra hcon
          simp only [not_le] at hcon
          exact hmem (Or.inr ⟨hcon, hθ1⟩)
        rw [hCut.eq_one_off_layer n h2δ hπ]
        norm_num
  have hBp : |Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      p.1 p.2| ≤ B * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := hB p hp
  have hcomm := hCc n p.2 hθ0 hθ1
  have hρb : |ρ p.1| ≤ Cr * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := hCr p.1
  -- assemble
  have hI : 0 ≤ (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := indicator_one_nonneg p.1
  have hL : 0 ≤ layerInd n p.2 := indicator_one_nonneg p.2
  have hstep1 : |(angCut n p.2 - 1) * Work.Elliptic.bslOp α
        (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      + ρ p.1 * comm m n p.2|
      ≤ (B + Cr * (Cc / delta n)) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
        * layerInd n p.2 := by
    calc |(angCut n p.2 - 1) * Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
          + ρ p.1 * comm m n p.2|
        ≤ |(angCut n p.2 - 1) * Work.Elliptic.bslOp α
            (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2|
          + |ρ p.1 * comm m n p.2| := abs_add_le _ _
      _ = |angCut n p.2 - 1| * |Work.Elliptic.bslOp α
            (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2|
          + |ρ p.1| * |comm m n p.2| := by rw [abs_mul, abs_mul]
      _ ≤ layerInd n p.2 * (B * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1)
          + (Cr * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1)
            * (Cc / delta n * layerInd n p.2) := by
          refine add_le_add (mul_le_mul hA hBp (abs_nonneg _) hL) (mul_le_mul hρb hcomm
            (abs_nonneg _) (mul_nonneg hCr0 hI))
      _ = (B + Cr * (Cc / delta n)) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
            * layerInd n p.2 := by ring
  have hfinal : |(angCut n p.2 - 1) * Work.Elliptic.bslOp α
        (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      + ρ p.1 * comm m n p.2|
      ≤ (B + Cr * Cc) * (1 + 1 / delta n) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
        * layerInd n p.2 := by
    refine hstep1.trans ?_
    have h2 : B + Cr * (Cc / delta n) ≤ (B + Cr * Cc) * (1 + 1 / delta n) := by
      have hδinv : 0 < (delta n)⁻¹ := inv_pos.mpr hδ
      have hexp : (B + Cr * Cc) * (1 + 1 / delta n)
          = B + B * (delta n)⁻¹ + Cr * Cc + Cr * Cc * (delta n)⁻¹ := by
        rw [div_eq_mul_inv]; ring
      rw [div_eq_mul_inv, hexp]
      nlinarith [mul_nonneg hB0 hδinv.le, mul_nonneg (mul_nonneg hCr0 hCc0.le) hδinv.le]
    calc (B + Cr * (Cc / delta n)) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
          * layerInd n p.2
        ≤ ((B + Cr * Cc) * (1 + 1 / delta n)) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
          * layerInd n p.2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hI) hL
      _ = (B + Cr * Cc) * (1 + 1 / delta n) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
          * layerInd n p.2 := by ring
  calc |Φ p.1 p.2| * |(angCut n p.2 - 1) * Work.Elliptic.bslOp α
        (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
        + ρ p.1 * comm m n p.2| * |bslWeight α p|
      ≤ |Φ p.1 p.2| * ((B + Cr * Cc) * (1 + 1 / delta n)
          * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2) * |bslWeight α p| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfinal (abs_nonneg _)) (abs_nonneg _)
    _ = (B + Cr * Cc) * (1 + 1 / delta n)
          * (|Φ p.1 p.2| * ((Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * |bslWeight α p|)
            * layerInd n p.2) := by ring
    _ ≤ (B + Cr * Cc) * (1 + 1 / delta n)
          * (|Φ p.1 p.2| * (W * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1)
            * layerInd n p.2) := by
        have hconst : (0 : ℝ) ≤ (B + Cr * Cc) * (1 + 1 / delta n) :=
          mul_nonneg (add_nonneg hB0 (mul_nonneg hCr0 hCc0.le))
            (add_nonneg zero_le_one (div_nonneg zero_le_one hδ.le))
        refine mul_le_mul_of_nonneg_left ?_ hconst
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) hL
        exact (mul_comm _ _).trans_le (hW p)
    _ = ((B + Cr * Cc) * W) * (1 + 1 / delta n)
          * (|Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
            * layerInd n p.2) := by ring

/-! ## The `L¹` bound -/

theorem SlotsZeroDiffBound {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ} {a b : ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) (hCut : Work.FTS.StrongEps.EComparison.CutFacts m)
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b))
    (ha : 0 < a) (hsub : tsupport ρ ⊆ Set.Icc a b) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ,
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        Φ p.1 p.2
            * Work.Elliptic.bslOp α (Work.FTS.StrongEps.EComparison.modeTest m ρ n) p.1 p.2
            * Work.FTS.StrongEps.EComparison.bslWeight α p
          - Φ p.1 p.2
            * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
                p.1 p.2
            * Work.FTS.StrongEps.EComparison.bslWeight α p)
        Work.FTS.EllipticEst.Q0 ∧
      (∫ p in Work.FTS.EllipticEst.Q0, |Φ p.1 p.2
          * Work.Elliptic.bslOp α (Work.FTS.StrongEps.EComparison.modeTest m ρ n) p.1 p.2
          * Work.FTS.StrongEps.EComparison.bslWeight α p
          - Φ p.1 p.2
            * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
                p.1 p.2
            * Work.FTS.StrongEps.EComparison.bslWeight α p|)
        ≤ A * (1 + 1 / Work.FTS.StrongEps.EComparison.delta n)
          * (∫ p in Work.FTS.EllipticEst.Q0,
              |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
                * Work.FTS.StrongEps.EComparison.layerInd n p.2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := abs_sub_modeTest_le_uniform (α := α) (Φ := Φ) (ρ := ρ) (m := m)
    hρ ha hsub hCut
  -- product-measure integrability of `|Φ| · 1_{[a,b]}(z)`
  have hbox : MeasureTheory.Integrable (fun p : ℝ × ℝ => |Φ p.1 p.2|
      * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1)
      (volume.restrict Work.FTS.EllipticEst.Q0) :=
    integrableOn_absPhi_box hsm hΦint hEint
  have hQ0m : MeasurableSet (Work.FTS.EllipticEst.Q0) :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- continuity of the relevant factors on the open quadrant
  have hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mpr hsm).continuousOn
  have hψ2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun k =>
      ((Work.FTS.ClassC.contDiffOn_uncurry_fst (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2))
          ((hρ k).contDiffOn)).mul
        (Work.FTS.ClassC.contDiffOn_uncurry_snd (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2))
          (Work.FTS.ClassC.contDiff_eFam_nat m k)))
  have hc2 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α
      (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := continuousOn_bslOp_of_smoothOpen hψ2
  refine ⟨C, hC0, fun n => ?_⟩
  -- the difference integrand `F` and the dominating function `G`
  set F : ℝ × ℝ → ℝ := fun p =>
      Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
      - Φ p.1 p.2 * Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2 * bslWeight α p
    with hFdef
  set G : ℝ × ℝ → ℝ := fun p => C * (1 + 1 / delta n)
      * (|Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
    with hGdef
  have hδ : 0 < delta n := hCut.delta_pos n
  have hψ1 : Work.FTS.EllipticEst.SmoothOpen (modeTest m ρ n) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun k =>
      (modeTest_contDiff hρ hCut k).contDiffOn
  have hFcont : ContinuousOn F Work.FTS.EllipticEst.Q0 := by
    rw [hFdef]
    exact ((hΦc.mul (continuousOn_bslOp_of_smoothOpen hψ1)).mul (continuousOn_weight α)).sub
      ((hΦc.mul hc2).mul (continuousOn_weight α))
  have hFmeas : AEStronglyMeasurable F (volume.restrict Work.FTS.EllipticEst.Q0) :=
    hFcont.aestronglyMeasurable (μ := volume) hQ0m
  -- the layer weight is an indicator of a measurable set
  have hlayerMeas : MeasurableSet (layer n) := by
    rw [layer]
    exact measurableSet_Ioo.union measurableSet_Ioo
  have hlayerInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => |Φ p.1 p.2|
      * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
      (volume.restrict Work.FTS.EllipticEst.Q0) := by
    have hfun : (fun p : ℝ × ℝ => |Φ p.1 p.2|
        * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
        = (Set.univ ×ˢ layer n).indicator (fun p : ℝ × ℝ => |Φ p.1 p.2|
            * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) := by
      funext p
      simp only [layerInd, Set.indicator_apply, Set.mem_prod, Set.mem_univ, true_and]
      by_cases h : p.2 ∈ layer n <;> simp [h]
    rw [hfun]
    exact hbox.indicator (MeasurableSet.univ.prod hlayerMeas)
  have hGint : MeasureTheory.Integrable G (volume.restrict Work.FTS.EllipticEst.Q0) := by
    rw [hGdef]
    exact hlayerInt.const_mul (C * (1 + 1 / delta n))
  -- the pointwise domination
  have hFG : ∀ᵐ p ∂(volume.restrict Work.FTS.EllipticEst.Q0), ‖F p‖ ≤ G p := by
    refine MeasureTheory.ae_restrict_of_forall_mem hQ0m fun p hp => ?_
    have h1 : F p = Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
        - Φ p.1 p.2 * Work.Elliptic.bslOp α
            (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2 * bslWeight α p := by
      simp only [hFdef]
    have h2 : G p = C * (1 + 1 / delta n)
        * (|Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
          * layerInd n p.2) := by
      simp only [hGdef]
    rw [Real.norm_eq_abs, h1, h2]
    exact hC n p hp
  have hIntF : MeasureTheory.Integrable F (volume.restrict Work.FTS.EllipticEst.Q0) :=
    hGint.mono' hFmeas hFG
  constructor
  · exact hIntF
  · have hFnorm : MeasureTheory.Integrable (fun p : ℝ × ℝ => |F p|)
        (volume.restrict Work.FTS.EllipticEst.Q0) := by
      simpa only [Real.norm_eq_abs] using hIntF.norm
    have hFG2 : ∀ᵐ p ∂(volume.restrict Work.FTS.EllipticEst.Q0), |F p| ≤ G p := by
      filter_upwards [hFG] with p hp
      simpa only [Real.norm_eq_abs] using hp
    have hmono : ∫ p in Work.FTS.EllipticEst.Q0, |F p|
        ≤ ∫ p in Work.FTS.EllipticEst.Q0, G p :=
      integral_mono_ae hFnorm hGint hFG2
    have hGval : ∫ p in Work.FTS.EllipticEst.Q0, G p
        = C * (1 + 1 / delta n) * (∫ p in Work.FTS.EllipticEst.Q0,
            |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
              * layerInd n p.2) := by
      rw [hGdef, integral_const_mul]
    calc ∫ p in Work.FTS.EllipticEst.Q0, |F p|
        ≤ ∫ p in Work.FTS.EllipticEst.Q0, G p := hmono
      _ = C * (1 + 1 / delta n) * (∫ p in Work.FTS.EllipticEst.Q0,
            |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
              * layerInd n p.2) := hGval

end Work.FTS.StrongEps.EComparison
