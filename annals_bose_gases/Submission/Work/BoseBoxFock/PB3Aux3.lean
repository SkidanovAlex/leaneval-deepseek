import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Work.BoseBoxFock.aQC_aPC_comm
import Submission.Work.BoseBoxFock.pb3_bessel_box
import Submission.Work.BoseBoxFock.pb3_mass_ident
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3Aux3` — the per-pair bound of the block-III first half
-/

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Integrability of the per-label integrand -/

/-- The per-label integrand of the block-III row is integrable. -/
theorem integrable_pairTerm {n N : ℕ} {v : E3 → ℝ} {μ : ℝ} (j : Fin n) (k : Lab N)
    {Θ Ψ : Xn n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ))
    (hΨm : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C) :
    Integrable (fun x : Xn n => (starRingEnd ℂ) (Θ x)
      * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
          * Ψ (Function.update x j u))) (volume : Measure (Xn n)) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨Ck, hCk0, hCk⟩ := pinQ_bdd v μ N k
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  obtain ⟨CΨ, hCΨ⟩ := hΨb
  have hCΘ0 : 0 ≤ CΘ := le_trans (norm_nonneg _) (hCΘ (Classical.arbitrary (Xn n)))
  have hCΨ0 : 0 ≤ CΨ := le_trans (norm_nonneg _) (hCΨ (Classical.arbitrary (Xn n)))
  have hkm : Measurable (pinQ v μ N k) := pinQ_measurable v μ N k
  have hks : Function.support (pinQ v μ N k) ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) :=
    pb3_pinQ_support k
  have haesm : AEStronglyMeasurable (fun x : Xn n => (starRingEnd ℂ) (Θ x)
      * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
          * Ψ (Function.update x j u))) (volume : Measure (Xn n)) :=
    ((Complex.continuous_conj.measurable.comp hΘm).aestronglyMeasurable).mul
      (((hkm.comp (measurable_pi_apply j)).aestronglyMeasurable).mul
        (slotIntegral_measurable hΨm hkm hks).aestronglyMeasurable)
  have hbdd : ∀ᵐ x ∂(volume : Measure (Xn n)), ‖(starRingEnd ℂ) (Θ x)
      * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
          * Ψ (Function.update x j u))‖ ≤ CΘ * (Ck * (Ck * CΨ * (ellH v μ) ^ 3)) :=
    Filter.Eventually.of_forall fun x => by
      rw [norm_mul, norm_mul, Complex.norm_conj]
      exact mul_le_mul (hCΘ x) (mul_le_mul (hCk _)
        (slotIntegral_bound hℓ hks hCk hCΨ hCk0 hCΨ0)
        (norm_nonneg _) hCk0) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCΘ0
  exact (integrableOn_of_aesm_bound hℓ haesm hbdd).integrable_of_forall_notMem_eq_zero
    (fun x hx => by
      have hΘ0 : Θ x = 0 := by
        by_contra hc
        exact hx (hΘs (Function.mem_support.mpr hc))
      rw [hΘ0, map_zero, zero_mul])

/-! ## 2. The weighted square identity -/

/-- **The weighted square identity**: `∫_box χ_j² ‖P_i g‖² = ∫_box χ_j² conj (P_i g) · g`.
(The weight `χ_j²` is constant in the slot `i` and `P_i g` is itself constant in the slot `i`.) -/
theorem pb3_weighted_sq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin n) (hij : i ≠ j)
    {g : Xn n → ℂ} (gm : Measurable g) (gb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
          * ((Complex.normSq (aPC ℓ i g x) : ℝ) : ℂ))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
            * ((starRingEnd ℂ) (aPC ℓ i g x) * g x) := by
  classical
  obtain ⟨Cg, hCg⟩ := gb
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg _) (hCg (Classical.arbitrary (Xn n)))
  obtain ⟨Cχ, hCχ⟩ := chiLam_bdd ℓ (ne_of_gt hℓ)
  have hCχ0 : 0 ≤ max Cχ 0 := le_max_right _ _
  have hχeq : ∀ x : E3, Submission.BoseGases.chiScale ℓ x = Work.BoseK15.corpusBox.chiLam ℓ x :=
    fun x => rfl
  have hχb : ∀ x : E3, ‖Submission.BoseGases.chiScale ℓ x‖ ≤ max Cχ 0 := by
    intro x
    have h1 : Submission.BoseGases.chiScale ℓ x = Work.BoseK15.corpusBox.chiLam ℓ x := rfl
    rw [Real.norm_eq_abs, h1]
    exact le_trans (hCχ x) (le_max_left _ _)
  have hPm : Measurable (aPC ℓ i g) := aPC_measurable' i gm
  have hPb : ∀ᵐ x ∂(volume : Measure (Xn n)), ‖aPC ℓ i g x‖ ≤ Cg :=
    aPC_ae_bound_full ℓ hℓ i hCg0 (Filter.Eventually.of_forall hCg)
  -- the weight
  have hwm : Measurable (fun x : Xn n => ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)) := by
    have h1 : Measurable (fun x : Xn n => (((Submission.BoseGases.chiScale ℓ (x j) : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        ((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp (measurable_pi_apply j))
    have h2 : Measurable (fun x : Xn n => (((Submission.BoseGases.chiScale ℓ (x j) : ℝ)) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ (x j) : ℝ) : ℂ)) := h1.mul h1
    simpa only [pow_two] using h2
  have hwb : ∀ x : Xn n,
      ‖((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)‖ ≤ (max Cχ 0) ^ 2 := by
    intro x
    have h3 : 0 ≤ Submission.BoseGases.chiScale ℓ (x j) := Submission.BoseGases.chi_nonneg _
    have h4 : Submission.BoseGases.chiScale ℓ (x j) ≤ max Cχ 0 := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg h3] using hχb (x j)
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h3]
    exact pow_le_pow_left₀ h3 h4 2
  -- the weighted conjugate
  have hinv : ∀ x (u : E3),
      (fun y : Xn n => ((Submission.BoseGases.chiScale ℓ (y j)) ^ 2 : ℂ)
          * (starRingEnd ℂ) (aPC ℓ i g y)) (Function.update x i u)
        = (fun y : Xn n => ((Submission.BoseGases.chiScale ℓ (y j)) ^ 2 : ℂ)
            * (starRingEnd ℂ) (aPC ℓ i g y)) x := by
    intro x u
    simp only
    rw [show Function.update x i u j = x j from by
        rw [Function.update_apply]
        exact if_neg (Ne.symm hij),
      aPC_const_in_coord]
  have hhbd : ∀ x : Xn n,
      ‖((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ) * (starRingEnd ℂ) (aPC ℓ i g x)‖
        ≤ (max Cχ 0) ^ 2 * Cg := by
    intro x
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hwb x) (aPC_bound_pointwise hℓ i hCg hCg0 x) (norm_nonneg _) (sq_nonneg _)
  have hChv : 0 ≤ (max Cχ 0) ^ 2 * Cg := mul_nonneg (sq_nonneg _) hCg0
  have horth : (∫ x in Submission.BoseGases.abox n ℓ,
      (fun y : Xn n => ((Submission.BoseGases.chiScale ℓ (y j)) ^ 2 : ℂ)
          * (starRingEnd ℂ) (aPC ℓ i g y)) x * aQC ℓ i g x) = 0 :=
    invariant_mul_aQC_orth hℓ i hCg0 hChv gm.aestronglyMeasurable
      (Filter.Eventually.of_forall hCg)
      ((hwm.mul (Complex.continuous_conj.measurable.comp hPm)).aestronglyMeasurable) hinv (Filter.Eventually.of_forall hhbd)
  -- integrability of the two pieces of the splitting
  have h1 : IntegrableOn (fun x : Xn n => ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
      * ((starRingEnd ℂ) (aPC ℓ i g x) * aPC ℓ i g x)) (Submission.BoseGases.abox n ℓ) volume := by
    refine integrableOn_of_aesm_bound hℓ
      ((hwm.mul ((Complex.continuous_conj.measurable.comp hPm).mul hPm)).aestronglyMeasurable)
      (C := (max Cχ 0) ^ 2 * (Cg * Cg)) ?_
    filter_upwards with x
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul (hwb x) (mul_le_mul (aPC_bound_pointwise hℓ i hCg hCg0 x)
      (aPC_bound_pointwise hℓ i hCg hCg0 x) (norm_nonneg _) hCg0)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (sq_nonneg _)
  have h2 : IntegrableOn (fun x : Xn n => ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
      * ((starRingEnd ℂ) (aPC ℓ i g x) * aQC ℓ i g x)) (Submission.BoseGases.abox n ℓ) volume := by
    refine integrableOn_of_aesm_bound hℓ
      ((hwm.mul ((Complex.continuous_conj.measurable.comp hPm).mul (gm.sub hPm))).aestronglyMeasurable)
      (C := (max Cχ 0) ^ 2 * (Cg * (Cg + Cg))) ?_
    filter_upwards [Filter.Eventually.of_forall hCg] with x hx
    rw [norm_mul, norm_mul, Complex.norm_conj, aQC_apply]
    refine mul_le_mul (hwb x) (mul_le_mul (aPC_bound_pointwise hℓ i hCg hCg0 x)
      (le_trans (norm_sub_le _ _) (add_le_add hx (aPC_bound_pointwise hℓ i hCg hCg0 x)))
      (norm_nonneg _) hCg0) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (sq_nonneg _)
  have hmain : (∫ x in Submission.BoseGases.abox n ℓ,
        ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
          * ((starRingEnd ℂ) (aPC ℓ i g x) * g x))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
            * ((starRingEnd ℂ) (aPC ℓ i g x) * aPC ℓ i g x) := by
    rw [show (∫ x in Submission.BoseGases.abox n ℓ,
          ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
            * ((starRingEnd ℂ) (aPC ℓ i g x) * g x))
        = ∫ x in Submission.BoseGases.abox n ℓ,
            (((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
                * ((starRingEnd ℂ) (aPC ℓ i g x) * aPC ℓ i g x)
              + ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
                * ((starRingEnd ℂ) (aPC ℓ i g x) * aQC ℓ i g x)) from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [aQC_apply]; ring]
    rw [integral_add h1 h2, show (∫ x in Submission.BoseGases.abox n ℓ,
        ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
          * ((starRingEnd ℂ) (aPC ℓ i g x) * aQC ℓ i g x)) = 0 from by
      rw [show (∫ x in Submission.BoseGases.abox n ℓ,
          ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
            * ((starRingEnd ℂ) (aPC ℓ i g x) * aQC ℓ i g x))
          = ∫ x in Submission.BoseGases.abox n ℓ,
              (fun y : Xn n => ((Submission.BoseGases.chiScale ℓ (y j)) ^ 2 : ℂ)
                * (starRingEnd ℂ) (aPC ℓ i g y)) x * aQC ℓ i g x from
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)]
      exact horth, add_zero]
  have hp : (∫ x in Submission.BoseGases.abox n ℓ,
        ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
          * ((Complex.normSq (aPC ℓ i g x) : ℝ) : ℂ))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
            * ((starRingEnd ℂ) (aPC ℓ i g x) * aPC ℓ i g x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Complex.normSq_eq_conj_mul_self])
  exact hp.trans hmain.symm

/-! ## 3. The pointwise identification on the box -/

/-- On the box, `aPC ℓ i (aQC ℓ j Θ)` is the complexification of `aP ℓ i (aQ ℓ j Φ)`. -/
theorem pb3_aPC_aQC_box_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin n) (hij : i ≠ j)
    {Φ : Xn n → ℝ} (hΦ : Continuous Φ) {y : Xn n} (hy : y ∈ Submission.BoseGases.abox n ℓ) :
    aPC ℓ i (aQC ℓ j (boxRestrictC ℓ Φ)) y
      = ((Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) y : ℝ) : ℂ) := by
  have h1 : (∫ z in Submission.BoseGases.acube ℓ,
        aQC ℓ j (boxRestrictC ℓ Φ) (Function.update y i z))
      = ∫ z in Submission.BoseGases.acube ℓ,
          ((Submission.BoseGases.aQ ℓ j Φ (Function.update y i z) : ℝ) : ℂ) :=
    MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun z hz => boxRestrictC_aQC_eq hℓ j hΦ (Submission.BoseGases.update_mem_abox i hy hz))
  have hio : (∫ z in Submission.BoseGases.acube ℓ,
        ((Submission.BoseGases.aQ ℓ j Φ (Function.update y i z) : ℝ) : ℂ))
      = ((∫ z in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.aQ ℓ j Φ (Function.update y i z) : ℝ) : ℂ) := integral_ofReal
  rw [aPC, h1, hio, Submission.BoseGases.aP]
  push_cast
  ring

/-- The integral form of the identification: `∫_box χ_j² conj (aPC_i (aQC_j Θ)) · (aQC_j Θ)`
is the complexification of the `n₀`-mass word of the real state. -/
theorem pb3_aQC_int_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin n) (hij : i ≠ j)
    {Φ : Xn n → ℝ} (hΦ : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
          * ((starRingEnd ℂ) (aPC ℓ i (aQC ℓ j (boxRestrictC ℓ Φ)) x)
            * aQC ℓ j (boxRestrictC ℓ Φ) x))
      = (((∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
            * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x
            * Submission.BoseGases.aQ ℓ j Φ x) : ℝ) : ℂ) := by
  have hio : (((∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
          * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x
          * Submission.BoseGases.aQ ℓ j Φ x) : ℝ) : ℂ)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (((Submission.BoseGases.chiScale ℓ (x j)) ^ 2
            * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x
            * Submission.BoseGases.aQ ℓ j Φ x : ℝ) : ℂ) := integral_ofReal.symm
  rw [hio]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)]
    with x hx
  rw [pb3_aPC_aQC_box_eq hℓ i j hij hΦ hx, boxRestrictC_aQC_eq hℓ j hΦ hx]
  push_cast
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-! ## 4. The per-pair bound -/

/-- **The per-pair bound**: the `pairSet` term at `(i,j)` — summed over the truncation label `k` —
is bounded by the `(i,j)`-term of the `n₀`-mass word. -/
theorem pb3_pairBound {n N : ℕ} {v : E3 → ℝ} {μ : ℝ} (i j : Fin n) (hij : i ≠ j)
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))} :
    (∑ k : Lab N, (∫ x : Xn n,
        (starRingEnd ℂ) (boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x)
        * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
            * aPC (ellH v μ) i (boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
                (Function.update x j u))).re)
      ≤ ∫ x in Submission.BoseGases.abox n (ellH v μ),
          (Submission.BoseGases.chiScale (ellH v μ) (x j)) ^ 2
            * Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aQ (ellH v μ) j Φ) x
            * Submission.BoseGases.aQ (ellH v μ) j Φ x := by
  classical
  set ℓ : ℝ := ellH v μ with hℓdef
  have hℓ : 0 < ℓ := ellH_pos v μ
  set ΦR : Xn n → ℝ := (Φ : Submission.BoseGases.X n → ℝ) with hΦR
  have hΦc : Continuous ΦR := Φ.contDiff.continuous
  set Θ : Xn n → ℂ := boxRestrictC ℓ ΦR with hΘ
  have hΘm : Measurable Θ := by rw [hΘ]; exact boxRestrictC_measurable' ℓ hΦc
  obtain ⟨CΘ, hCΘ0, hCΘ⟩ := boxRestrictC_bound' hℓ hΦc
  have hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C := ⟨CΘ, by intro x; rw [hΘ]; exact hCΘ x⟩
  have hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ := by
    rw [hΘ]; exact boxRestrictC_support' ℓ ΦR
  -- the terms
  have hterm : ∀ k : Lab N, (∫ x : Xn n, (starRingEnd ℂ) (Θ x)
        * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
            * aPC ℓ i Θ (Function.update x j u))).re
      = (ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox n ℓ,
          Complex.normSq (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
            * aPC ℓ i Θ (Function.update x j u))) := by
    intro k
    rw [pb3_pairTerm_eq (v := v) (μ := μ) i j hij k hΘm hΘb hΘs,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsum1 : (∑ k : Lab N, (∫ x : Xn n, (starRingEnd ℂ) (Θ x)
        * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
            * aPC ℓ i Θ (Function.update x j u))).re)
      = (ℓ ^ 3)⁻¹ * (∑ k : Lab N, ∫ x in Submission.BoseGases.abox n ℓ,
          Complex.normSq (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
            * aPC ℓ i Θ (Function.update x j u))) := by
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.mul_sum]
  -- Bessel and the χ²-mass identity
  have hbess : (∑ k : Lab N, ∫ x in Submission.BoseGases.abox n ℓ,
        Complex.normSq (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
          * aPC ℓ i Θ (Function.update x j u)))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, ∫ u : E3,
          (Submission.BoseGases.chiScale ℓ u) ^ 2
            * ‖aQC ℓ j (aPC ℓ i Θ) (Function.update x j u)‖ ^ 2 :=
    pb3_bessel_box (N := N) (v := v) (μ := μ) i j hij hΘm hΘb hΘs
  have hmass := pb3_mass_ident (v := v) (μ := μ) i j hij hΘm hΘb hΘs
  -- the complex chain
  have hcomm : aQC ℓ j (aPC ℓ i Θ) = aPC ℓ i (aQC ℓ j Θ) :=
    aQC_aPC_comm (ℓ := ℓ) hℓ hij hΘm hΘb
  have hQm : Measurable (aQC ℓ j Θ) := by
    have hh : aQC ℓ j Θ = fun x => Θ x - aPC ℓ j Θ x := rfl
    rw [hh]
    exact hΘm.sub (aPC_measurable' j hΘm)
  have hQb : ∃ C : ℝ, ∀ x, ‖aQC ℓ j Θ x‖ ≤ C :=
    ⟨2 * CΘ, fun x => by
      rw [aQC_apply]
      calc ‖Θ x - aPC ℓ j Θ x‖ ≤ ‖Θ x‖ + ‖aPC ℓ j Θ x‖ := norm_sub_le _ _
        _ ≤ CΘ + CΘ := add_le_add (hCΘ x) (aPC_bound_pointwise hℓ j (fun y => hCΘ y) hCΘ0 x)
        _ = 2 * CΘ := by ring⟩
  have hsq := pb3_weighted_sq (ℓ := ℓ) hℓ i j hij (g := aQC ℓ j Θ) hQm hQb
  have hint := pb3_aQC_int_eq (ℓ := ℓ) hℓ i j hij hΦc
  -- the real identity
  have hreal : (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
          * ‖aQC ℓ j (aPC ℓ i Θ) x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
            * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j ΦR) x
            * Submission.BoseGases.aQ ℓ j ΦR x := by
    have h1 : ((∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
          * ‖aQC ℓ j (aPC ℓ i Θ) x‖ ^ 2 : ℝ) : ℂ)
        = ((∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
              * Complex.normSq (aPC ℓ i (aQC ℓ j Θ) x) : ℝ) : ℂ) := by
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hcomm, Complex.normSq_eq_norm_sq]
    have h2 : ((∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
              * Complex.normSq (aPC ℓ i (aQC ℓ j Θ) x) : ℝ) : ℂ)
        = ∫ x in Submission.BoseGases.abox n ℓ,
            ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
              * ((Complex.normSq (aPC ℓ i (aQC ℓ j Θ) x) : ℝ) : ℂ) := by
      rw [show ((∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
              * Complex.normSq (aPC ℓ i (aQC ℓ j Θ) x) : ℝ) : ℂ)
          = ∫ x in Submission.BoseGases.abox n ℓ,
              (((Submission.BoseGases.chiScale ℓ (x j)) ^ 2
                * Complex.normSq (aPC ℓ i (aQC ℓ j Θ) x) : ℝ) : ℂ) from
          integral_ofReal.symm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      push_cast
      ring
    have h3 : (∫ x in Submission.BoseGases.abox n ℓ,
            ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
              * ((Complex.normSq (aPC ℓ i (aQC ℓ j Θ) x) : ℝ) : ℂ))
        = ∫ x in Submission.BoseGases.abox n ℓ,
            ((Submission.BoseGases.chiScale ℓ (x j)) ^ 2 : ℂ)
              * ((starRingEnd ℂ) (aPC ℓ i (aQC ℓ j Θ) x) * (aQC ℓ j Θ) x) := hsq
    have h4 : ((∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
              * Complex.normSq (aPC ℓ i (aQC ℓ j Θ) x) : ℝ) : ℂ)
        = ((∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
              * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j ΦR) x
              * Submission.BoseGases.aQ ℓ j ΦR x : ℝ) : ℂ) := h2.trans (h3.trans hint)
    have h5 : ((∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
          * ‖aQC ℓ j (aPC ℓ i Θ) x‖ ^ 2 : ℝ) : ℂ)
        = ((∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
              * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j ΦR) x
              * Submission.BoseGases.aQ ℓ j ΦR x : ℝ) : ℂ) := h1.trans h4
    exact Complex.ofReal_injective h5
  -- assemble
  rw [hsum1]
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans hbess (le_of_eq hmass))
    (by positivity : (0:ℝ) ≤ (ℓ ^ 3)⁻¹)) ?_
  rw [hreal]
  rw [show (ℓ ^ 3)⁻¹ * (ℓ ^ 3 * (∫ x in Submission.BoseGases.abox n ℓ,
      (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
        * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j ΦR) x
        * Submission.BoseGases.aQ ℓ j ΦR x))
      = ∫ x in Submission.BoseGases.abox n ℓ,
      (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
        * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j ΦR) x
        * Submission.BoseGases.aQ ℓ j ΦR x from by
    field_simp]

end

end Work.BoseBoxFock
