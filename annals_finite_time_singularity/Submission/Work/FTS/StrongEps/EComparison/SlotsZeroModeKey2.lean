/-
# `SlotsZeroModeKey2` - the vanishing of `∫ Φ·(bslOp (ρ ⊗ e_m))·wgt`

Part of `Work.FTS.StrongEps.EComparison.SlotsZeroModeODE`; see `SlotsZeroModeMain` for the
overview.  Contents:

* `perN_zero_set` - the proved `bslOp_ibp` identity for the cut-off test function, in
  product-measure form;
* `abs_sub_modeTest_le` - the pointwise bound for the difference of the model integrand and the
  cut-off integrand (a constant times `(1+1/δ_n)·|Φ|·1_{[a,b]}·1_{layer_n}`);
* `setIntegral_absPhi_layer` - the Fubini identity for the layer density;
* `key_set` - the vanishing of `∫_{Q0} Φ·(bslOp (ρ ⊗ e_m))·wgt`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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

/-! ## The cut-off identity in product-measure form -/

/-- The `bslOp_ibp` identity for the cut-off test function, product-measure form. -/
theorem perN_zero_set {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsol : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Φ z θ = 0)
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) (hρc : HasCompactSupport ρ) (hρs : tsupport ρ ⊆ Set.Ioi 0)
    (hCut : CutFacts m) (n : ℕ) :
    (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
      * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p) = 0 := by
  classical
  have hφ := modeTest_contDiff (m := m) (n := n) hρ hCut
  have hφc := modeTest_hasCompactSupport (m := m) (n := n) hρc hCut
  have hφs := modeTest_tsupport_subset_Q0 (m := m) (n := n) hρs hCut
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc hp.2.1,
      lt_of_le_of_lt hp.2.2 hd⟩
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen Φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mpr (fun k => hsm k)
  have htestsm : Work.FTS.EllipticEst.SmoothOpen (modeTest m ρ n) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun k => (hφ k).contDiffOn)
  have h1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Φ p.1 p.2
      * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0 := by
    refine integrableOn_Q0_of_box ha hab.le hc hcd.le hd (fun p hp => ?_) ?_
    · rw [Work.FTS.H2.ModalSolR.bslOp_eq_zero_off_box (α := α) hbox hp]
      ring
    · exact ((hΦsm.continuousOn.mono hKsub).mul
        ((continuousOn_bslOp_of_smoothOpen htestsm).mono hKsub)).mul
          ((continuousOn_weight α).mono hKsub)
  have h2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Elliptic.bslOp α Φ p.1 p.2) * (modeTest m ρ n) p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0 := by
    refine (integrableOn_zero (s := Work.FTS.EllipticEst.Q0)).congr_fun
      (fun p hp => ?_) Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    change (0 : ℝ) = (Work.Elliptic.bslOp α Φ p.1 p.2) * (modeTest m ρ n) p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
    rw [hsol p.1 hz p.2 hθ0 hθ1]
    ring
  have hibp := Work.EllipticEst.ModalSolution.bslOp_ibp α (u := Φ) (φ := modeTest m ρ n)
    hsm hφ hφc hφs h1 h2
  have hR : (∫ p in Work.FTS.EllipticEst.Q0, (Work.Elliptic.bslOp α Φ p.1 p.2)
      * (modeTest m ρ n) p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = 0 := by
    have hcongr := MeasureTheory.setIntegral_congr_fun (μ := volume)
      (f := fun p : ℝ × ℝ => (Work.Elliptic.bslOp α Φ p.1 p.2) * (modeTest m ρ n) p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) (g := fun _ => (0 : ℝ))
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet (fun p hp => by
        obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        show (Work.Elliptic.bslOp α Φ p.1 p.2) * (modeTest m ρ n) p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2) = 0
        rw [hsol p.1 hz p.2 hθ0 hθ1]
        ring)
    rw [hcongr]
    simp
  change (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
      * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = 0
  rw [hibp, hR]

/-! ## The pointwise difference bound -/

/-- **The difference of the cut-off integrand and the model integrand** is bounded by a constant
times `(1 + 1/δ_n)·|Φ|·1_{[a,b]}(z)·1_{layer_n}(θ)`. -/
theorem abs_sub_modeTest_le {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m n : ℕ}
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) {a b : ℝ} (ha : 0 < a)
    (hsub : tsupport ρ ⊆ Set.Icc a b) (hCut : CutFacts m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
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
  have hδ : 0 < delta n := hCut.delta_pos n
  refine ⟨(B + Cr * Cc) * W, by positivity, fun p hp => ?_⟩
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

end Work.FTS.StrongEps.EComparison

