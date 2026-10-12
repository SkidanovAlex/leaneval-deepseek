import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.BoseBoxFock.K1dirB.chiChi_row_le
import Submission.Work.BoseBoxFock.K1dirB.coulTail_le
import Submission.Work.BoseBoxFock.K1dirB.dirichlet_k1H_le
import Submission.Work.BoseBoxFock.K1dirB.k1ErrB_tendsto
import Submission.Work.BoseBoxFock.K1dirB.k1ErrC_tendsto
import Submission.Work.BoseBoxFock.K1dirB.k1ErrD_tendsto
import Submission.Work.BoseBoxFock.L1Tails.pairEnergy_bookkeeping
import Submission.Work.BoseFixB1S.intAbsCS
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- The box indicator is measurable. -/
lemma aesm_thetaFun (ℓ : ℝ) : Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := by
  classical
  show Measurable (fun y : E3 => if y ∈ Work.BoseK15.corpusBox.boxL ℓ then (1 : ℂ) else 0)
  exact Measurable.ite (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ) measurable_const measurable_const

/-! ## Measurability of the lattice sums -/

lemma aesm_pinQB {v : E3 → ℝ} {μ : ℝ} (N : ℕ) (c : Lab N → ℝ) :
    AEStronglyMeasurable (pinQB v μ N c) volume := by
  have h : Measurable (pinQB v μ N c) := by
    unfold pinQB
    fun_prop
  exact h.aestronglyMeasurable

lemma aesm_pinQC {v : E3 → ℝ} {μ : ℝ} (N : ℕ) (c : Lab N → ℝ) :
    AEStronglyMeasurable (pinQC v μ N c) volume := by
  have h : Measurable (pinQC v μ N c) := by
    unfold pinQC
    fun_prop
  exact h.aestronglyMeasurable

lemma aesm_k1ErrB {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) : AEStronglyMeasurable (k1ErrB v μ fu N Wa Wb) volume := by
  have h1 : AEStronglyMeasurable (pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N)) volume :=
    aesm_pinQB N _
  have h2 : AEStronglyMeasurable (pinQBl (ellH v μ) (Wa + Wb)) volume := errBdd_pinQBl_aesm
  have h3 : k1ErrB v μ fu N Wa Wb
      = fun w => pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N) w
          - pinQBl (ellH v μ) (Wa + Wb) w := rfl
  rw [h3]
  exact h1.sub h2

lemma aesm_k1ErrC {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) : AEStronglyMeasurable (k1ErrC v μ fu N Wa Wb) volume := by
  have h1 : AEStronglyMeasurable (pinQC v μ N (k1cfun fu Wa Wb (ellH v μ) N)) volume :=
    aesm_pinQC N _
  have h2 : AEStronglyMeasurable (pinQCl (ellH v μ) (Wa + Wb)) volume := errBdd_pinQCl_aesm
  have h3 : k1ErrC v μ fu N Wa Wb
      = fun y => pinQC v μ N (k1cfun fu Wa Wb (ellH v μ) N) y
          - pinQCl (ellH v μ) (Wa + Wb) y := rfl
  rw [h3]
  exact h1.sub h2


/-! ## Bounds and the pointwise decomposition -/

/-- The finite lattice sum `pinQA` is bounded by `card · B` when the coefficients are. -/
lemma bdd_pinQA {v : E3 → ℝ} {μ : ℝ} (N : ℕ) (c : Lab N → ℝ) {B : ℝ} (hB : ∀ k, ‖c k‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, ‖pinQA v μ N c z‖ ≤ C := by
  refine ⟨(Fintype.card (Lab N) : ℝ) * B, by
    exact mul_nonneg (Nat.cast_nonneg _) (le_trans (norm_nonneg _) (hB 0)), fun z => ?_⟩
  calc ‖pinQA v μ N c z‖
      = ‖∑ k : Lab N, (c k : ℂ) * Complex.exp
          (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) z : ℝ) : ℂ))‖ := rfl
    _ ≤ ∑ k : Lab N, ‖(c k : ℂ) * Complex.exp
          (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) z : ℝ) : ℂ))‖ := norm_sum_le _ _
    _ = ∑ k : Lab N, ‖(c k : ℝ)‖ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, errBdd_norm_exp_I, mul_one, errBdd_norm_ofReal, Real.norm_eq_abs]
    _ ≤ ∑ _k : Lab N, B := Finset.sum_le_sum fun k _ => hB k
    _ = (Fintype.card (Lab N) : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The coefficients `k1cfun` are bounded by the `L¹` masses of the two weights. -/
lemma exists_k1cfun_bound {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : Lab N, ‖k1cfun fu Wa Wb (ellH v μ) N k‖ ≤ B := by
  obtain ⟨Ba, hBa0, hBa⟩ := chat_abs_le_uniform (W := Wa)
  obtain ⟨Bb, hBb0, hBb⟩ := chat_abs_le_uniform (W := Wb)
  refine ⟨Ba + Bb, add_nonneg hBa0 hBb0, fun k => ?_⟩
  have hζ0 : 0 ≤ uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k) := by
    rw [uvCut]; exact Work.BoseBoxFix.LowCut.nonneg fu _
  have hζ1 : uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k) ≤ 1 := by
    rw [uvCut]; exact Work.BoseBoxFix.LowCut.le_one fu _
  have h1 : |uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
      * Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)|
      ≤ |Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)| := by
    rw [abs_mul, abs_of_nonneg hζ0]
    calc uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
          * |Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)|
        ≤ 1 * |Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)| :=
          mul_le_mul_of_nonneg_right hζ1 (abs_nonneg _)
      _ = |Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)| := one_mul _
  rw [k1cfun, Real.norm_eq_abs]
  calc |uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
        * Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)
        + Work.BoseFixR.chat Wb (kmomLab (ellH v μ) N k)|
      ≤ |uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
          * Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)|
        + |Work.BoseFixR.chat Wb (kmomLab (ellH v μ) N k)| := abs_add_le _ _
    _ ≤ Ba + Bb := add_le_add (le_trans h1 (hBa _)) (hBb _)

/-- The pointwise four-row decomposition of the kernel difference against a test function. -/
lemma k1KerDiff_mul_decomp {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) {G : E3 → E3 → ℂ} (w y : E3) :
    k1KerDiff v μ fu N Wa Wb w y * G w y
      = k1ErrA v μ fu N Wa Wb (w - y) * K1dirB.k1H (ellH v μ) G w y
        - k1ErrB v μ fu N Wa Wb w * K1dirB.k1HB (ellH v μ) G w y
        - k1ErrC v μ fu N Wa Wb y * K1dirB.k1HC (ellH v μ) G w y
        + k1ErrD v μ fu N Wa Wb * K1dirB.k1HD (ellH v μ) G w y := by
  rw [k1KerDiff, k1Kernel_decomp]
  simp only [K1dirB.k1H, K1dirB.k1HB, K1dirB.k1HC, K1dirB.k1HD, K1dirB.chiB,
    K1dirB.k1H, k1ErrA]
  ring


/-- Measurability of the `χχ` lattice sum. -/
lemma measurable_pinQA {v : E3 → ℝ} {μ : ℝ} (N : ℕ) (c : Lab N → ℝ) :
    Measurable (pinQA v μ N c) := by
  unfold pinQA
  fun_prop

/-- A uniform bound for a smooth test function on the box squared. -/
lemma exists_box_bound {ℓ : ℝ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    ∃ CG : ℝ, 0 ≤ CG ∧ ∀ w y, w ∈ Work.BoseK15.corpusBox.boxL ℓ →
      y ∈ Work.BoseK15.corpusBox.boxL ℓ → ‖G w y‖ ≤ CG := by
  have hK : IsCompact (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_compact _ ℓ).prod (Work.BoseB4.BoxData.boxL_compact _ ℓ)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.continuous.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun w y hw hy =>
    le_trans (hC (w, y) ⟨hw, hy⟩) (le_max_left _ _)⟩

/-- Uniform bound for the `χθ`-weighted test kernel. -/
theorem k1HB_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w y, ‖K1dirB.k1HB ℓ G w y‖ ≤ C := by
  classical
  obtain ⟨CG, hCG0, hCG⟩ := exists_box_bound hG
  refine ⟨‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * CG, by positivity, fun w y => ?_⟩
  have hχ : ‖K1dirB.chiB ℓ w‖ ≤ Real.sqrt k1Chi := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (K1dirB.chiB_sq_le ℓ w)
  have hθ : ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ ≤ 1 := K1dirB.thetaFun_norm_le ℓ y
  have hnorm : ‖K1dirB.k1HB ℓ G w y‖
      = ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖K1dirB.chiB ℓ w‖
        * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ * ‖G w y‖ := by
    rw [K1dirB.k1HB, norm_mul, norm_mul, norm_mul]
  rw [hnorm]
  by_cases hp : w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ
  · have hGG : ‖G w y‖ ≤ CG := hCG w y hp.1 hp.2
    have h1 : ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖K1dirB.chiB ℓ w‖
        ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi :=
      mul_le_mul_of_nonneg_left hχ (norm_nonneg _)
    have h2 : ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖K1dirB.chiB ℓ w‖
          * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖
        ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * 1 := by
      calc ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖K1dirB.chiB ℓ w‖
            * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖
          ≤ (‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi) * 1 :=
            mul_le_mul h1 hθ (norm_nonneg _) (by positivity)
        _ = ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * 1 := by ring
    calc ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖K1dirB.chiB ℓ w‖
            * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ * ‖G w y‖
        ≤ (‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * 1) * CG :=
          mul_le_mul h2 hGG (norm_nonneg _) (by positivity)
      _ = ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * CG := by ring
  · rcases not_and_or.mp hp with hw | hy
    · rw [K1dirB.chiB_eq_zero_of_notMem_boxL hℓ hw]
      have hz : (0 : ℝ) ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * CG :=
        mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hCG0
      simpa using hz
    · rw [show Work.BoseK15.corpusBox.thetaFun ℓ y = 0 from by
        rw [show Work.BoseK15.corpusBox.thetaFun ℓ y
          = if y ∈ Work.BoseK15.corpusBox.boxL ℓ then (1 : ℂ) else 0 from rfl, if_neg hy]]
      have hz : (0 : ℝ) ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * CG :=
        mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hCG0
      simpa using hz

/-- Uniform bound for the `θχ`-weighted test kernel. -/
theorem k1HC_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w y, ‖K1dirB.k1HC ℓ G w y‖ ≤ C := by
  classical
  obtain ⟨CG, hCG0, hCG⟩ := exists_box_bound hG
  refine ⟨‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * CG, by positivity, fun w y => ?_⟩
  have hχ : ‖K1dirB.chiB ℓ y‖ ≤ Real.sqrt k1Chi := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (K1dirB.chiB_sq_le ℓ y)
  have hθ : ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖ ≤ 1 := K1dirB.thetaFun_norm_le ℓ w
  have hnorm : ‖K1dirB.k1HC ℓ G w y‖
      = ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖
        * ‖K1dirB.chiB ℓ y‖ * ‖G w y‖ := by
    rw [K1dirB.k1HC, norm_mul, norm_mul, norm_mul]
  rw [hnorm]
  by_cases hp : w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ
  · have hGG : ‖G w y‖ ≤ CG := hCG w y hp.1 hp.2
    have h1 : ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖
        ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left hθ (norm_nonneg _)
    have h2 : ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖
          * ‖K1dirB.chiB ℓ y‖
        ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * 1 := by
      calc ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖
            * ‖K1dirB.chiB ℓ y‖
          ≤ (‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * 1) * Real.sqrt k1Chi :=
            mul_le_mul h1 hχ (norm_nonneg _) (by positivity)
        _ = ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * 1 := by ring
    calc ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖
            * ‖K1dirB.chiB ℓ y‖ * ‖G w y‖
        ≤ (‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * 1) * CG :=
          mul_le_mul h2 hGG (norm_nonneg _) (by positivity)
      _ = ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * CG := by ring
  · rcases not_and_or.mp hp with hw | hy
    · rw [show Work.BoseK15.corpusBox.thetaFun ℓ w = 0 from by
        rw [show Work.BoseK15.corpusBox.thetaFun ℓ w
          = if w ∈ Work.BoseK15.corpusBox.boxL ℓ then (1 : ℂ) else 0 from rfl, if_neg hw]]
      have hz : (0 : ℝ) ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * CG :=
        mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hCG0
      simpa using hz
    · rw [K1dirB.chiB_eq_zero_of_notMem_boxL hℓ hy]
      have hz : (0 : ℝ) ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * Real.sqrt k1Chi * CG :=
        mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hCG0
      simpa using hz

/-- Uniform bound for the `θθ`-weighted test kernel. -/
theorem k1HD_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w y, ‖K1dirB.k1HD ℓ G w y‖ ≤ C := by
  classical
  obtain ⟨CG, hCG0, hCG⟩ := exists_box_bound hG
  refine ⟨‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * CG, by positivity, fun w y => ?_⟩
  have hθw : ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖ ≤ 1 := K1dirB.thetaFun_norm_le ℓ w
  have hθy : ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ ≤ 1 := K1dirB.thetaFun_norm_le ℓ y
  have hnorm : ‖K1dirB.k1HD ℓ G w y‖
      = ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖
        * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ * ‖G w y‖ := by
    rw [K1dirB.k1HD, norm_mul, norm_mul, norm_mul]
  rw [hnorm]
  by_cases hp : w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ
  · have hGG : ‖G w y‖ ≤ CG := hCG w y hp.1 hp.2
    have h2 : ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖
          * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖
        ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * 1 * 1 := by
      calc ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖
            * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖
          ≤ (‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * 1) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hθw (norm_nonneg _)) hθy (norm_nonneg _)
              (by positivity)
        _ = ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * 1 * 1 := by ring
    calc ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖
            * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ * ‖G w y‖
        ≤ (‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * 1 * 1) * CG :=
          mul_le_mul h2 hGG (norm_nonneg _) (by positivity)
      _ = ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * CG := by ring
  · rcases not_and_or.mp hp with hw | hy
    · rw [show Work.BoseK15.corpusBox.thetaFun ℓ w = 0 from by
        rw [show Work.BoseK15.corpusBox.thetaFun ℓ w
          = if w ∈ Work.BoseK15.corpusBox.boxL ℓ then (1 : ℂ) else 0 from rfl, if_neg hw]]
      have hz : (0 : ℝ) ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * CG :=
        mul_nonneg (norm_nonneg _) hCG0
      simpa using hz
    · rw [show Work.BoseK15.corpusBox.thetaFun ℓ y = 0 from by
        rw [show Work.BoseK15.corpusBox.thetaFun ℓ y
          = if y ∈ Work.BoseK15.corpusBox.boxL ℓ then (1 : ℂ) else 0 from rfl, if_neg hy]]
      have hz : (0 : ℝ) ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * CG :=
        mul_nonneg (norm_nonneg _) hCG0
      simpa using hz


/-! ## The budget arithmetic -/

lemma ell_pow_identity9 {ℓ : ℝ} (hℓ : 0 < ℓ) : ℓ ^ 9 * ((ℓ ^ 3)⁻¹) ^ 2 = ℓ ^ 3 := by
  have h6 : ((ℓ ^ 3)⁻¹) ^ 2 = (ℓ ^ 6)⁻¹ := by rw [inv_pow, ← pow_mul]
  rw [h6, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero 6 (ne_of_gt hℓ))]
  ring

lemma ell_pow_identity6 {ℓ : ℝ} (hℓ : 0 < ℓ) : ℓ ^ 6 * ((ℓ ^ 3)⁻¹) ^ 2 = 1 := by
  have h6 : ((ℓ ^ 3)⁻¹) ^ 2 = (ℓ ^ 6)⁻¹ := by rw [inv_pow, ← pow_mul]
  rw [h6, mul_inv_cancel₀ (pow_ne_zero 6 (ne_of_gt hℓ))]

lemma tauA_key {ℓ ε : ℝ} (hℓ : 0 < ℓ) :
    ε ^ 2 / (256 * ℓ ^ 3 * k1Chi) * ℓ ^ 3 * k1Chi = (ε / 8) ^ 2 / 4 := by
  have hk : k1Chi ≠ 0 := ne_of_gt k1Chi_pos
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  field_simp
  ring

lemma tauB_key {ℓ ε : ℝ} (hℓ : 0 < ℓ) :
    ε ^ 2 / (64 * ℓ ^ 3 * k1Chi) * ℓ ^ 3 * k1Chi = (ε / 8) ^ 2 := by
  have hk : k1Chi ≠ 0 := ne_of_gt k1Chi_pos
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  field_simp
  ring

lemma sqrt_budgetA {ℓ ε τ D PE : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) (hτ : 0 ≤ τ) (hD0 : 0 ≤ D)
    (hD : D ≤ k1Chi * ((ℓ ^ 3)⁻¹) ^ 2 * PE) (hPE : 0 ≤ PE)
    (hkey : τ * ℓ ^ 3 * k1Chi = (ε / 8) ^ 2 / 4) :
    2 * Real.sqrt (τ * ℓ ^ 9 * D) ≤ (ε / 8) * Real.sqrt PE := by
  have hε8 : (0 : ℝ) < ε / 8 := by linarith
  have h4 : 4 * (τ * ℓ ^ 9 * D) ≤ (ε / 8) ^ 2 * PE := by
    have h9 : ℓ ^ 9 * (k1Chi * ((ℓ ^ 3)⁻¹) ^ 2 * PE) = k1Chi * PE * ℓ ^ 3 := by
      rw [show ℓ ^ 9 * (k1Chi * ((ℓ ^ 3)⁻¹) ^ 2 * PE)
          = (ℓ ^ 9 * ((ℓ ^ 3)⁻¹) ^ 2) * (k1Chi * PE) by ring, ell_pow_identity9 hℓ]
      ring
    have h2 : τ * ℓ ^ 9 * D ≤ τ * (k1Chi * PE * ℓ ^ 3) := by
      calc τ * ℓ ^ 9 * D ≤ τ * ℓ ^ 9 * (k1Chi * ((ℓ ^ 3)⁻¹) ^ 2 * PE) :=
            mul_le_mul_of_nonneg_left hD (by positivity)
        _ = τ * (ℓ ^ 9 * ((ℓ ^ 3)⁻¹) ^ 2 * (k1Chi * PE)) := by ring
        _ = τ * (k1Chi * PE * ℓ ^ 3) := by rw [ell_pow_identity9 hℓ]; ring
    have hb : τ * (k1Chi * PE * ℓ ^ 3) = (ε / 8) ^ 2 / 4 * PE := by
      rw [show τ * (k1Chi * PE * ℓ ^ 3) = τ * ℓ ^ 3 * k1Chi * PE by ring, hkey]
    linarith [h2, hb]
  have hid : (2 : ℝ) * Real.sqrt (τ * ℓ ^ 9 * D) = Real.sqrt (4 * (τ * ℓ ^ 9 * D)) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hid]
  calc Real.sqrt (4 * (τ * ℓ ^ 9 * D)) ≤ Real.sqrt ((ε / 8) ^ 2 * PE) := Real.sqrt_le_sqrt h4
    _ = (ε / 8) * Real.sqrt PE := by
        rw [Real.sqrt_mul (le_of_lt (pow_pos hε8 2)), Real.sqrt_sq hε8.le]

lemma sqrt_budgetB {ℓ ε τ D PE : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) (hτ : 0 ≤ τ) (hD0 : 0 ≤ D)
    (hD : D ≤ k1Chi * ((ℓ ^ 3)⁻¹) ^ 2 * PE) (hPE : 0 ≤ PE)
    (hkey : τ * ℓ ^ 3 * k1Chi = (ε / 8) ^ 2) :
    Real.sqrt (τ * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D) ≤ (ε / 8) * Real.sqrt PE := by
  have hε8 : (0 : ℝ) < ε / 8 := by linarith
  have h2 : (τ * ℓ ^ 3) * (ℓ ^ 6 * D) ≤ (ε / 8) ^ 2 * PE := by
    have h6 : ℓ ^ 6 * (k1Chi * ((ℓ ^ 3)⁻¹) ^ 2 * PE) = k1Chi * PE := by
      rw [show ℓ ^ 6 * (k1Chi * ((ℓ ^ 3)⁻¹) ^ 2 * PE)
          = (ℓ ^ 6 * ((ℓ ^ 3)⁻¹) ^ 2) * (k1Chi * PE) by ring, ell_pow_identity6 hℓ]
      ring
    have h4 : ℓ ^ 6 * D ≤ ℓ ^ 6 * (k1Chi * ((ℓ ^ 3)⁻¹) ^ 2 * PE) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    rw [h6] at h4
    have hb : (τ * ℓ ^ 3) * (k1Chi * PE) = (ε / 8) ^ 2 * PE := by
      rw [show (τ * ℓ ^ 3) * (k1Chi * PE) = τ * ℓ ^ 3 * k1Chi * PE by ring, hkey]
    calc (τ * ℓ ^ 3) * (ℓ ^ 6 * D) ≤ (τ * ℓ ^ 3) * (k1Chi * PE) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (ε / 8) ^ 2 * PE := hb
  have hid : Real.sqrt (τ * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D)
      = Real.sqrt ((τ * ℓ ^ 3) * (ℓ ^ 6 * D)) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ τ * ℓ ^ 3)]
  rw [hid]
  calc Real.sqrt ((τ * ℓ ^ 3) * (ℓ ^ 6 * D)) ≤ Real.sqrt ((ε / 8) ^ 2 * PE) :=
        Real.sqrt_le_sqrt h2
    _ = (ε / 8) * Real.sqrt PE := by
        rw [Real.sqrt_mul (le_of_lt (pow_pos hε8 2)), Real.sqrt_sq hε8.le]

/-- Reassociation helper: `c * Σ (f m * H) = (c * Σ f m) * H`. -/
lemma mul_sum_mul {ι : Type*} (s : Finset ι) (c H : ℂ) (X : ι → ℂ) :
    c * (∑ m ∈ s, X m * H) = (c * (∑ m ∈ s, X m)) * H := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring


/-- The final constant bookkeeping for the θ-rows. -/
lemma deltaB_final {ℓ ε MB : ℝ} (hℓ : 0 < ℓ) :
    (ε / (8 * Real.sqrt k1Chi)) * ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖
      * (Real.sqrt (k1Chi * ℓ ^ 6) * Real.sqrt MB) = (ε / 8) * Real.sqrt MB := by
  have hk : (0 : ℝ) < k1Chi := k1Chi_pos
  have hkne : Real.sqrt k1Chi ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hk)
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hnorm : ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ = (ℓ ^ 3)⁻¹ := by
    have h : ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ = |(ℓ ^ 3)⁻¹| := by simp
    rw [h, abs_of_pos (by positivity)]
  have hsq : Real.sqrt (k1Chi * ℓ ^ 6) = Real.sqrt k1Chi * ℓ ^ 3 := by
    rw [Real.sqrt_mul hk.le, show Real.sqrt (ℓ ^ 6) = ℓ ^ 3 by
      rw [show ℓ ^ 6 = (ℓ ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
  rw [hnorm, hsq]
  field_simp


/-- The final constant bookkeeping for the `θθ`-row. -/
lemma deltaD_final {ℓ ε MB : ℝ} (hℓ : 0 < ℓ) :
    (ε / 8) * ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * (Real.sqrt (ℓ ^ 6) * Real.sqrt MB)
      = (ε / 8) * Real.sqrt MB := by
  have hnorm : ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ = (ℓ ^ 3)⁻¹ := by
    have h : ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ = |(ℓ ^ 3)⁻¹| := by simp
    rw [h, abs_of_pos (by positivity)]
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  rw [hnorm, show Real.sqrt (ℓ ^ 6) = ℓ ^ 3 by
    rw [show ℓ ^ 6 = (ℓ ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
  field_simp

theorem K1exp_sub_K1lim_pairing_dirB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {R : ℝ}
    (hR : 0 < R) (hRl : R ≤ Work.BoseBoxFock.ellH v μ / 4)
    {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWai : MeasureTheory.Integrable Wa) (hWa0 : ∀ᵐ x, 0 ≤ Wa x)
    (hWas : ∀ x, R ≤ ‖x‖ → Wa x = 0) (hWae : ∀ x, Wa (-x) = Wa x)
    (hWaJ : MeasureTheory.Integrable (Work.BoseBoxFock.coulInt Wa))
    (hWbi : MeasureTheory.Integrable Wb) (hWb0 : ∀ᵐ x, 0 ≤ Wb x)
    (hWbs : ∀ x, R ≤ ‖x‖ → Wb x = 0) (hWbe : ∀ x, Wb (-x) = Wb x)
    (hWbJ : MeasureTheory.Integrable (Work.BoseBoxFock.coulInt Wb))
    (hWJ : MeasureTheory.Integrable (Work.BoseBoxFock.coulInt (Wa + Wb)))
    (fu : Work.BoseBoxFix.LowCut) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ,
      Work.BoseBoxFock.BoxSmooth (Work.BoseBoxFock.ellH v μ) G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
          ∫ y in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
          (Work.BoseBoxFock.K1exp v μ N (Work.BoseBoxFock.k1cfun fu Wa Wb (Work.BoseBoxFock.ellH v μ) N) w y
            - Work.BoseBoxFock.K1lim (Work.BoseBoxFock.ellH v μ) (Wa + Wb) w y) * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy (Work.BoseBoxFock.ellH v μ) G)
            + Real.sqrt (Work.BoseBoxFock.massBox (Work.BoseBoxFock.ellH v μ) G)) := by
  intro ε hε
  -- ============ setup ============
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hW0i : Integrable (fun x => Wa x + Wb x) := hWai.add hWbi
  have hW00 : ∀ᵐ x, 0 ≤ (fun x => Wa x + Wb x) x := by
    filter_upwards [hWa0, hWb0] with x hx hy
    linarith
  have hW0s : ∀ x, ellH v μ / 4 ≤ ‖x‖ → (fun x => Wa x + Wb x) x = 0 := by
    intro x hx
    show Wa x + Wb x = 0
    rw [hWas x (le_trans hRl hx), hWbs x (le_trans hRl hx), add_zero]
  have hWbs' : ∀ x, ellH v μ / 4 ≤ ‖x‖ → Wb x = 0 :=
    fun x hx => hWbs x (le_trans hRl hx)
  have hW0s'' : ∀ x, R < ‖x‖ → (Wa + Wb) x = 0 := by
    intro x hx
    rw [Pi.add_apply, hWas x hx.le, hWbs x hx.le, add_zero]
  have hWbs'' : ∀ x, R < ‖x‖ → Wb x = 0 := fun x hx => hWbs x hx.le
  have hk1 : (0 : ℝ) < k1Chi := k1Chi_pos
  have hℓ3 : (0 : ℝ) < (ellH v μ) ^ 3 := by positivity
  -- the budgets
  set τaMax : ℝ := ε ^ 2 / (256 * (ellH v μ) ^ 3 * k1Chi) with hτaMax
  set τbMax : ℝ := ε ^ 2 / (64 * (ellH v μ) ^ 3 * k1Chi) with hτbMax
  have hτaMaxpos : 0 < τaMax := by rw [hτaMax]; positivity
  have hτbMaxpos : 0 < τbMax := by rw [hτbMax]; positivity
  set δB : ℝ := ε / (8 * Real.sqrt k1Chi) with hδB
  set δD : ℝ := ε / 8 with hδD
  have hδBpos : 0 < δB := by rw [hδB]; positivity
  have hδDpos : 0 < δD := by rw [hδD]; linarith
  -- the two Coulomb tails
  obtain ⟨Λa, hΛapos, hτa⟩ := K1dirB.coulTail_le (ℓ := ellH v μ) hℓ hW0i hW00 hW0s hWJ
    τaMax hτaMaxpos
  obtain ⟨Λb, hΛbpos, hτb⟩ := K1dirB.coulTail_le (ℓ := ellH v μ) hℓ hWbi hWb0 hWbs' hWbJ
    τbMax hτbMaxpos
  -- the three supremum bounds
  obtain ⟨NB, hNB⟩ := K1dirB.k1ErrB_tendsto (v := v) (μ := μ) fu hWai hWbi δB hδBpos
  obtain ⟨NC, hNC⟩ := K1dirB.k1ErrC_tendsto (v := v) (μ := μ) fu hWai hWbi δB hδBpos
  obtain ⟨ND, hND⟩ := K1dirB.k1ErrD_tendsto (v := v) (μ := μ) fu hWai hWbi δD hδDpos
  -- choose N₀
  obtain ⟨Na, hNa⟩ : ∃ n : ℕ, 2 * (ellH v μ) * max Λa Λb / Real.pi ≤ (n : ℝ) :=
    exists_nat_ge _
  refine ⟨max (max (max (max 1 NB) NC) ND) Na, fun N hN G hGsmooth => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNB' : NB ≤ N := by omega
  have hNC' : NC ≤ N := by omega
  have hND' : ND ≤ N := by omega
  have hNa' : Na ≤ N := by omega
  have huvR : max Λa Λb ≤ uvRad (ellH v μ) N := by
    have hπ : 0 < Real.pi := Real.pi_pos
    have h1 : max Λa Λb ≤ (Real.pi * (N : ℝ)) / (2 * ellH v μ) := by
      have h2 : 2 * (ellH v μ) * max Λa Λb / Real.pi ≤ (Na : ℝ) := hNa
      have h3 : (Na : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNa'
      rw [div_le_iff₀ hπ] at h2
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * ellH v μ)]
      nlinarith [h2, h3]
    rw [uvRad]
    calc max Λa Λb ≤ Real.pi * (N : ℝ) / (2 * ellH v μ) := h1
      _ = 2 * Real.pi / (ellH v μ) * (N : ℝ) / 4 := by ring
  -- ============ the main argument ============
  obtain ⟨G', hG'sm, hG'eq⟩ := hGsmooth
  have hPE : L1Tails.pairEnergy (ellH v μ) G' = L1Tails.pairEnergy (ellH v μ) G :=
    pairEnergy_congr_box hℓ hG'eq
  have hM : massBox (ellH v μ) G' = massBox (ellH v μ) G := massBox_congr_box hG'eq
  rw [← hPE, ← hM]
  -- replace `G` by `G'` in the pairing
  rw [show (∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ),
        (K1exp v μ N (k1cfun fu Wa Wb (ellH v μ) N) w y
          - K1lim (ellH v μ) (Wa + Wb) w y) * G w y)
      = ∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ),
        (K1exp v μ N (k1cfun fu Wa Wb (ellH v μ) N) w y
          - K1lim (ellH v μ) (Wa + Wb) w y) * G' w y from
    (setIntegral_pairing_congr_box (K := fun w y => K1exp v μ N (k1cfun fu Wa Wb (ellH v μ) N) w y
      - K1lim (ellH v μ) (Wa + Wb) w y) hG'eq).symm]
  -- ============ the four rows of the kernel difference ============
  set PA : E3 → E3 → ℂ :=
    fun w y => k1ErrA v μ fu N Wa Wb (w - y) * K1dirB.k1H (ellH v μ) G' w y with hPA
  set PB : E3 → E3 → ℂ :=
    fun w y => k1ErrB v μ fu N Wa Wb w * K1dirB.k1HB (ellH v μ) G' w y with hPB
  set PC : E3 → E3 → ℂ :=
    fun w y => k1ErrC v μ fu N Wa Wb y * K1dirB.k1HC (ellH v μ) G' w y with hPC
  set PD : E3 → E3 → ℂ :=
    fun w y => k1ErrD v μ fu N Wa Wb * K1dirB.k1HD (ellH v μ) G' w y with hPD
  set c3 : ℂ := (((ellH v μ) ^ 3 : ℝ) : ℂ) with hc3
  set c3i : ℂ := ((((ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ) with hc3i
  set μ' : Measure (E3 × E3) :=
    (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
      (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))) with hμ'
  haveI hfinμ : IsFiniteMeasure μ' := by
    rw [hμ']
    haveI : IsFiniteMeasure
        ((volume : Measure E3).restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))) := by
      rw [isFiniteMeasure_restrict]
      intro htop
      have h := volume_real_boxL hℓ
      rw [MeasureTheory.measureReal_def, htop] at h
      simp at h
      linarith
    infer_instance
  have hpt : ∀ w y, k1KerDiff v μ fu N Wa Wb w y * G' w y
      = PA w y - PB w y - PC w y + PD w y := by
    intro w y
    rw [hPA, hPB, hPC, hPD, k1KerDiff_mul_decomp]
  have hF : Function.uncurry (fun w y : E3 => k1KerDiff v μ fu N Wa Wb w y * G' w y)
      = fun p : E3 × E3 => PA p.1 p.2 - PB p.1 p.2 - PC p.1 p.2 + PD p.1 p.2 := by
    funext p
    exact hpt p.1 p.2
  -- integrability of the χχ row
  set QA : E3 → E3 → ℂ := fun w y =>
    pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) (w - y) * K1dirB.k1H (ellH v μ) G' w y with hQA
  set RA : E3 → E3 → ℂ := fun w y =>
    latPer3 (ellH v μ) (Wa + Wb) (w - y) * K1dirB.k1H (ellH v μ) G' w y with hRA
  have hPA_eq : ∀ w y, PA w y = QA w y - RA w y := by
    intro w y
    rw [hPA, hQA, hRA]
    unfold k1ErrA
    ring
  have hIntQA : Integrable (Function.uncurry QA) μ' := by
    obtain ⟨B, hB0, hB⟩ := exists_k1cfun_bound (v := v) (μ := μ) fu N Wa Wb
    obtain ⟨Cq, hCq0, hCq⟩ := bdd_pinQA (v := v) (μ := μ) N
      (k1cfun fu Wa Wb (ellH v μ) N) hB
    obtain ⟨CH, hCH0, hCH⟩ := K1dirB.k1H_bdd hℓ hG'sm
    have haesm : AEStronglyMeasurable (Function.uncurry QA) μ' := by
      have h1 : AEStronglyMeasurable (fun p : E3 × E3 =>
          pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) (p.1 - p.2)) μ' :=
        ((measurable_pinQA N _).comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (Function.uncurry (K1dirB.k1H (ellH v μ) G')) μ' :=
        (K1dirB.k1H_aesm hℓ.ne' hG'sm).mono_measure (by
          rw [hμ', Measure.prod_restrict]; exact Measure.restrict_le_self)
      have : Function.uncurry QA
          = fun p : E3 × E3 => pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) (p.1 - p.2)
              * K1dirB.k1H (ellH v μ) G' p.1 p.2 := rfl
      rw [this]
      exact h1.mul h2
    refine Integrable.of_bound haesm (Cq * CH) (Filter.Eventually.of_forall fun p => ?_)
    rw [show Function.uncurry QA p
        = pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) (p.1 - p.2)
            * K1dirB.k1H (ellH v μ) G' p.1 p.2 from rfl, norm_mul]
    exact mul_le_mul (hCq _) (hCH p.1 p.2) (norm_nonneg _) hCq0
  have hIntRA : Integrable (Function.uncurry RA) μ' := by
    obtain ⟨CH, hCH0, hCH⟩ := K1dirB.k1H_bdd hℓ hG'sm
    have hsuppH : ∀ w y, K1dirB.k1H (ellH v μ) G' w y ≠ 0 →
        w ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
          ∧ y ∈ Work.BoseK15.corpusBox.boxL (ellH v μ) :=
      fun w y => K1dirB.k1H_support hℓ
    have hterm : ∀ m : Fin 3 → ℤ, Integrable (fun p : E3 × E3 =>
        (((Wa + Wb) (p.1 - p.2 - (ellH v μ) • latVec m) : ℝ) : ℂ)
          * K1dirB.k1H (ellH v μ) G' p.1 p.2) (volume.prod (volume : Measure E3)) :=
      fun m => K1dirB.integrable_translate_mul hℓ hW0i m (K1dirB.k1H_aesm hℓ.ne' hG'sm)
        ⟨CH, hCH⟩ hsuppH
    have h2 : Integrable (fun p : E3 × E3 =>
        ∑ m ∈ LatFourier.latFinSet (ellH v μ) R,
          (((Wa + Wb) (p.1 - p.2 - (ellH v μ) • latVec m) : ℝ) : ℂ)
            * K1dirB.k1H (ellH v μ) G' p.1 p.2) (volume.prod (volume : Measure E3)) :=
      integrable_finsetSum _ (fun m _ => hterm m)
    have hsum : Integrable (fun p : E3 × E3 =>
        (c3 * (∑ m ∈ LatFourier.latFinSet (ellH v μ) R,
          (((Wa + Wb) (p.1 - p.2 - (ellH v μ) • latVec m) : ℝ) : ℂ)))
          * K1dirB.k1H (ellH v μ) G' p.1 p.2) (volume.prod (volume : Measure E3)) := by
      refine (h2.const_mul c3).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [smul_eq_mul]
      exact mul_sum_mul _ _ _ _
    have hpt2' : ∀ᵐ p ∂(volume.prod (volume : Measure E3)),
        (c3 * (∑ m ∈ LatFourier.latFinSet (ellH v μ) R,
          (((Wa + Wb) (p.1 - p.2 - (ellH v μ) • latVec m) : ℝ) : ℂ)))
          * K1dirB.k1H (ellH v μ) G' p.1 p.2 = Function.uncurry RA p := by
      filter_upwards with p
      change (c3 * (∑ m ∈ LatFourier.latFinSet (ellH v μ) R,
          (((Wa + Wb) (p.1 - p.2 - (ellH v μ) • latVec m) : ℝ) : ℂ)))
          * K1dirB.k1H (ellH v μ) G' p.1 p.2
        = latPer3 (ellH v μ) (Wa + Wb) (p.1 - p.2) * K1dirB.k1H (ellH v μ) G' p.1 p.2
      rw [hc3, K1dirB.latPer3_mul_expand hℓ hW0s'' hsuppH p.1 p.2]
    have hfull : Integrable (Function.uncurry RA) (volume.prod (volume : Measure E3)) :=
      hsum.congr hpt2'
    refine hfull.mono_measure ?_
    rw [hμ', Measure.prod_restrict]
    exact Measure.restrict_le_self
  have hIntA : Integrable (Function.uncurry PA) μ' := by
    have hsub : Integrable (fun p : E3 × E3 =>
        (Function.uncurry QA p - Function.uncurry RA p)) μ' := hIntQA.sub hIntRA
    refine hsub.congr (Filter.Eventually.of_forall fun p => ?_)
    show QA p.1 p.2 - RA p.1 p.2 = PA p.1 p.2
    rw [hPA_eq p.1 p.2]
  -- integrability of the three θ-rows
  have hIntPB : Integrable (Function.uncurry PB) μ' := by
    classical
    obtain ⟨CH, hCH0, hCH⟩ := k1HB_bdd hℓ hG'sm
    have haesm : AEStronglyMeasurable (Function.uncurry PB) μ' := by
      have h1v : AEStronglyMeasurable (fun p : E3 × E3 => k1ErrB v μ fu N Wa Wb p.1)
          ((volume : Measure E3).prod volume) :=
        (aesm_k1ErrB fu N Wa Wb).comp_fst
      have h1 : AEStronglyMeasurable (fun p : E3 × E3 => k1ErrB v μ fu N Wa Wb p.1) μ' :=
        h1v.mono_measure (by rw [hμ', Measure.prod_restrict]; exact Measure.restrict_le_self)
      have hm : Measurable (fun p : E3 × E3 => K1dirB.k1HB (ellH v μ) G' p.1 p.2) := by
        have hχ : Measurable (fun p : E3 × E3 => K1dirB.chiB (ellH v μ) p.1) :=
          ((K1dirB.chiB_contDiff hℓ.ne').continuous.measurable).comp measurable_fst
        have hθ : Measurable (fun p : E3 × E3 =>
            Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2) :=
          (aesm_thetaFun (ellH v μ)).comp measurable_snd
        have hGm : Measurable (fun p : E3 × E3 => G' p.1 p.2) := hG'sm.continuous.measurable
        have : (fun p : E3 × E3 => K1dirB.k1HB (ellH v μ) G' p.1 p.2)
            = fun p : E3 × E3 => ((((ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ) * K1dirB.chiB (ellH v μ) p.1
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2 * G' p.1 p.2 := by
          funext p; rw [K1dirB.k1HB]
        rw [this]
        exact ((measurable_const.mul hχ).mul hθ).mul hGm
      have : Function.uncurry PB = fun p : E3 × E3 =>
          k1ErrB v μ fu N Wa Wb p.1 * K1dirB.k1HB (ellH v μ) G' p.1 p.2 := rfl
      rw [this]
      exact h1.mul hm.aestronglyMeasurable
    refine Integrable.of_bound haesm (δB * CH) (Filter.Eventually.of_forall fun p => ?_)
    rw [show Function.uncurry PB p
        = k1ErrB v μ fu N Wa Wb p.1 * K1dirB.k1HB (ellH v μ) G' p.1 p.2 from rfl, norm_mul]
    exact mul_le_mul (hNB N hNB' p.1) (hCH p.1 p.2) (norm_nonneg _) hδBpos.le
  have hIntPC : Integrable (Function.uncurry PC) μ' := by
    classical
    obtain ⟨CH, hCH0, hCH⟩ := k1HC_bdd hℓ hG'sm
    have haesm : AEStronglyMeasurable (Function.uncurry PC) μ' := by
      have h1v : AEStronglyMeasurable (fun p : E3 × E3 => k1ErrC v μ fu N Wa Wb p.2)
          ((volume : Measure E3).prod volume) :=
        (aesm_k1ErrC fu N Wa Wb).comp_snd
      have h1 : AEStronglyMeasurable (fun p : E3 × E3 => k1ErrC v μ fu N Wa Wb p.2) μ' :=
        h1v.mono_measure (by rw [hμ', Measure.prod_restrict]; exact Measure.restrict_le_self)
      have hm : Measurable (fun p : E3 × E3 => K1dirB.k1HC (ellH v μ) G' p.1 p.2) := by
        have hχ : Measurable (fun p : E3 × E3 => K1dirB.chiB (ellH v μ) p.2) :=
          ((K1dirB.chiB_contDiff hℓ.ne').continuous.measurable).comp measurable_snd
        have hθ : Measurable (fun p : E3 × E3 =>
            Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1) :=
          (aesm_thetaFun (ellH v μ)).comp measurable_fst
        have hGm : Measurable (fun p : E3 × E3 => G' p.1 p.2) := hG'sm.continuous.measurable
        have : (fun p : E3 × E3 => K1dirB.k1HC (ellH v μ) G' p.1 p.2)
            = fun p : E3 × E3 => ((((ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1 * K1dirB.chiB (ellH v μ) p.2
                * G' p.1 p.2 := by
          funext p; rw [K1dirB.k1HC]
        rw [this]
        exact ((measurable_const.mul hθ).mul hχ).mul hGm
      have : Function.uncurry PC = fun p : E3 × E3 =>
          k1ErrC v μ fu N Wa Wb p.2 * K1dirB.k1HC (ellH v μ) G' p.1 p.2 := rfl
      rw [this]
      exact h1.mul hm.aestronglyMeasurable
    refine Integrable.of_bound haesm (δB * CH) (Filter.Eventually.of_forall fun p => ?_)
    rw [show Function.uncurry PC p
        = k1ErrC v μ fu N Wa Wb p.2 * K1dirB.k1HC (ellH v μ) G' p.1 p.2 from rfl, norm_mul]
    exact mul_le_mul (hNC N hNC' p.2) (hCH p.1 p.2) (norm_nonneg _) hδBpos.le
  have hIntPD : Integrable (Function.uncurry PD) μ' := by
    classical
    obtain ⟨CH, hCH0, hCH⟩ := k1HD_bdd hℓ hG'sm
    have haesm : AEStronglyMeasurable (Function.uncurry PD) μ' := by
      have hm : Measurable (fun p : E3 × E3 => K1dirB.k1HD (ellH v μ) G' p.1 p.2) := by
        have hθ : Measurable (fun p : E3 × E3 =>
            Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1) :=
          (aesm_thetaFun (ellH v μ)).comp measurable_fst
        have hθ2 : Measurable (fun p : E3 × E3 =>
            Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2) :=
          (aesm_thetaFun (ellH v μ)).comp measurable_snd
        have hGm : Measurable (fun p : E3 × E3 => G' p.1 p.2) := hG'sm.continuous.measurable
        have : (fun p : E3 × E3 => K1dirB.k1HD (ellH v μ) G' p.1 p.2)
            = fun p : E3 × E3 => ((((ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2 * G' p.1 p.2 := by
          funext p; rw [K1dirB.k1HD]
        rw [this]
        exact ((measurable_const.mul hθ).mul hθ2).mul hGm
      have : Function.uncurry PD = fun p : E3 × E3 =>
          k1ErrD v μ fu N Wa Wb * K1dirB.k1HD (ellH v μ) G' p.1 p.2 := rfl
      rw [this]
      exact aestronglyMeasurable_const.mul hm.aestronglyMeasurable
    refine Integrable.of_bound haesm (‖k1ErrD v μ fu N Wa Wb‖ * CH)
      (Filter.Eventually.of_forall fun p => ?_)
    rw [show Function.uncurry PD p
        = k1ErrD v μ fu N Wa Wb * K1dirB.k1HD (ellH v μ) G' p.1 p.2 from rfl, norm_mul]
    exact mul_le_mul_of_nonneg_left (hCH p.1 p.2) (norm_nonneg _)

  -- ============ the scale factors ============
  set PE : ℝ := L1Tails.pairEnergy (ellH v μ) G' with hPEdef
  set MB : ℝ := massBox (ellH v μ) G' with hMBdef
  set Dt : ℝ := ∫ w : E3, ∫ y : E3, ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => K1dirB.k1H (ellH v μ) G' w' y) w
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 with hDt
  obtain ⟨hEeq, -, -, hdnn, hmnn⟩ := L1Tails.pairEnergy_bookkeeping hℓ hG'sm
  have hPE0 : 0 ≤ PE := by
    rw [hPEdef, hEeq]
    exact add_nonneg hdnn hmnn
  have hMB0 : 0 ≤ MB := massBox_nonneg _ _
  have hDt0 : 0 ≤ Dt := by
    rw [hDt]
    refine integral_nonneg fun w => integral_nonneg fun y => Finset.sum_nonneg fun j _ => by positivity
  have hDbound : Dt ≤ k1Chi * ((ellH v μ) ^ 3)⁻¹ ^ 2 * PE := by
    rw [hDt, hPEdef]
    exact K1dirB.dirichlet_k1H_le hℓ hG'sm
  -- ============ the split ============
  have hIntF : Integrable (Function.uncurry
      (fun w y : E3 => k1KerDiff v μ fu N Wa Wb w y * G' w y)) μ' := by
    rw [hF]
    exact ((hIntA.sub hIntPB).sub hIntPC).add hIntPD
  have hsplit : (∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ), k1KerDiff v μ fu N Wa Wb w y * G' w y)
      = (∫ p : E3 × E3, Function.uncurry PA p ∂μ')
        - (∫ p : E3 × E3, Function.uncurry PB p ∂μ')
        - (∫ p : E3 × E3, Function.uncurry PC p ∂μ')
        + (∫ p : E3 × E3, Function.uncurry PD p ∂μ') := by
    rw [show (∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
          ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ),
            k1KerDiff v μ fu N Wa Wb w y * G' w y)
        = ∫ p : E3 × E3, Function.uncurry
            (fun w y : E3 => k1KerDiff v μ fu N Wa Wb w y * G' w y) p ∂μ' from
      (MeasureTheory.integral_prod _ hIntF).symm]
    rw [hF]
    rw [MeasureTheory.integral_add
      (f := fun p : E3 × E3 => PA p.1 p.2 - PB p.1 p.2 - PC p.1 p.2)
      (g := fun p : E3 × E3 => PD p.1 p.2) ((hIntA.sub hIntPB).sub hIntPC) hIntPD]
    rw [MeasureTheory.integral_sub (f := fun p : E3 × E3 => PA p.1 p.2 - PB p.1 p.2)
      (g := fun p : E3 × E3 => PC p.1 p.2) (hIntA.sub hIntPB) hIntPC]
    rw [MeasureTheory.integral_sub (f := fun p : E3 × E3 => PA p.1 p.2)
      (g := fun p : E3 × E3 => PB p.1 p.2) hIntA hIntPB]
    rfl
  -- ============ row A (the χχ row) ============
  have hrowA : ‖∫ p : E3 × E3, Function.uncurry PA p ∂μ'‖ ≤ (ε / 4) * Real.sqrt PE := by
    have hconv : (∫ p : E3 × E3, Function.uncurry PA p ∂μ')
        = ∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
            ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ), PA w y :=
      MeasureTheory.integral_prod _ hIntA
    rw [hconv]
    have hA := K1dirB.chiChi_row_le (v := v) (μ := μ) (R := R) hWai hWbi hWae hWbe hWas hWbs
      fu hN1 (Λ := max Λa Λb) (τa := τaMax) (τb := τbMax) huvR
      (fun S hS => hτa S (fun n hn => le_trans (le_max_left _ _) (hS n hn)))
      (fun S hS => hτb S (fun n hn => le_trans (le_max_right _ _) (hS n hn))) hG'sm
    rw [← hDt] at hA
    have h1 : 2 * Real.sqrt (τaMax * (ellH v μ) ^ 9 * Dt) ≤ (ε / 8) * Real.sqrt PE :=
      sqrt_budgetA hℓ hε (by rw [hτaMax]; positivity) hDt0 hDbound hPE0
        (by rw [hτaMax]; exact tauA_key hℓ)
    have h2 : Real.sqrt (τbMax * (ellH v μ) ^ 3) * Real.sqrt ((ellH v μ) ^ 6 * Dt)
        ≤ (ε / 8) * Real.sqrt PE :=
      sqrt_budgetB hℓ hε (by rw [hτbMax]; positivity) hDt0 hDbound hPE0
        (by rw [hτbMax]; exact tauB_key hℓ)
    linarith [hA, h1, h2]
  -- ============ rows B, C, D (the θ rows) ============
  -- a.e. membership in the box for `μ'`
  have hmem : ∀ᵐ p ∂μ', p.1 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
      ∧ p.2 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
    have h1 : ∀ᵐ p ∂μ', p ∈ (Work.BoseK15.corpusBox.boxL (ellH v μ)
        ×ˢ Work.BoseK15.corpusBox.boxL (ellH v μ)) := by
      rw [hμ', MeasureTheory.Measure.prod_restrict]
      exact MeasureTheory.ae_restrict_mem
        ((Work.BoseB4.BoxData.boxL_measurableSet _ _).prod
          (Work.BoseB4.BoxData.boxL_measurableSet _ _))
    exact h1.mono fun p hp => hp
  -- the total mass of `μ'`
  have hμuniv : μ'.real Set.univ = (ellH v μ) ^ 6 := by
    have h1 : (∫ _p : E3 × E3, (1 : ℝ) ∂μ') = μ'.real Set.univ := by
      rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    rw [← h1, hμ']
    have h2 : ∀ _w : E3, (∫ _y in Work.BoseK15.corpusBox.boxL (ellH v μ), (1 : ℝ))
        = (ellH v μ) ^ 3 := by
      intro _w
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, volume_real_boxL hℓ]
    have h3 : (∫ _w in Work.BoseK15.corpusBox.boxL (ellH v μ),
          ∫ _y in Work.BoseK15.corpusBox.boxL (ellH v μ), (1 : ℝ))
        = (ellH v μ) ^ 3 * (ellH v μ) ^ 3 := by
      have h4 : (∫ _w in Work.BoseK15.corpusBox.boxL (ellH v μ),
            ∫ _y in Work.BoseK15.corpusBox.boxL (ellH v μ), (1 : ℝ))
          = ∫ _w in Work.BoseK15.corpusBox.boxL (ellH v μ), (ellH v μ) ^ 3 := by
        refine MeasureTheory.setIntegral_congr_fun
          (Work.BoseB4.BoxData.boxL_measurableSet _ _) fun w _ => h2 w
      rw [h4, MeasureTheory.setIntegral_const, smul_eq_mul, volume_real_boxL hℓ]
    rw [MeasureTheory.integral_prod (f := fun _ : E3 × E3 => (1 : ℝ)) (integrable_const _), h3]
    ring
  -- the mass of the test function
  have hMBprod : (∫ p : E3 × E3, ‖G' p.1 p.2‖ ^ 2 ∂μ') = MB := by
    rw [hMBdef, massBox]
    refine MeasureTheory.integral_prod (f := fun p : E3 × E3 => ‖G' p.1 p.2‖ ^ 2) ?_
    obtain ⟨CG, hCG0, hCG⟩ := exists_box_bound hG'sm
    refine Integrable.of_bound (((continuous_norm.pow 2).comp hG'sm.continuous).aestronglyMeasurable)
      (max CG 0 ^ 2) (hmem.mono fun p hp => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_trans (hCG p.1 p.2 hp.1 hp.2) (le_max_left _ _)) 2
  -- the window mass
  have hchi2 : (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.1‖ ^ 2 ∂μ')
      ≤ k1Chi * (ellH v μ) ^ 6 := by
    have hb : Integrable (fun _ : E3 × E3 => k1Chi) μ' := integrable_const _
    calc (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.1‖ ^ 2 ∂μ')
        ≤ ∫ _p : E3 × E3, k1Chi ∂μ' := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => by positivity) hb
            (Filter.Eventually.of_forall fun p => K1dirB.chiB_sq_le _ _)
      _ = k1Chi * (ellH v μ) ^ 6 := by
          rw [MeasureTheory.integral_const, smul_eq_mul, hμuniv, mul_comm]
  have hchi2' : (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.2‖ ^ 2 ∂μ')
      ≤ k1Chi * (ellH v μ) ^ 6 := by
    have hb : Integrable (fun _ : E3 × E3 => k1Chi) μ' := integrable_const _
    calc (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.2‖ ^ 2 ∂μ')
        ≤ ∫ _p : E3 × E3, k1Chi ∂μ' := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => by positivity) hb
            (Filter.Eventually.of_forall fun p => K1dirB.chiB_sq_le _ _)
      _ = k1Chi * (ellH v μ) ^ 6 := by
          rw [MeasureTheory.integral_const, smul_eq_mul, hμuniv, mul_comm]
  -- the pairing helpers
  have hGB_int : Integrable (fun p : E3 × E3 => ‖G' p.1 p.2‖) μ' := by
    obtain ⟨CG, hCG0, hCG⟩ := exists_box_bound hG'sm
    refine Integrable.of_bound (hG'sm.continuous.norm.aestronglyMeasurable) (max CG 0)
      (hmem.mono fun p hp => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact le_trans (hCG p.1 p.2 hp.1 hp.2) (le_max_left _ _)
  have hG2_int : Integrable (fun p : E3 × E3 => ‖G' p.1 p.2‖ ^ 2) μ' := by
    obtain ⟨CG, hCG0, hCG⟩ := exists_box_bound hG'sm
    refine Integrable.of_bound (((continuous_norm.pow 2).comp hG'sm.continuous).aestronglyMeasurable)
      (max CG 0 ^ 2) (hmem.mono fun p hp => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_trans (hCG p.1 p.2 hp.1 hp.2) (le_max_left _ _)) 2
  have hCS1int : Integrable (fun p : E3 × E3 =>
      ‖K1dirB.chiB (ellH v μ) p.1‖ * ‖G' p.1 p.2‖) μ' := by
    obtain ⟨CG, hCG0, hCG⟩ := exists_box_bound hG'sm
    refine Integrable.of_bound (((continuous_norm.comp
        ((K1dirB.chiB_contDiff hℓ.ne').continuous.comp continuous_fst)).mul
        (continuous_norm.comp hG'sm.continuous)).aestronglyMeasurable)
      (Real.sqrt k1Chi * max CG 0) (hmem.mono fun p hp => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) (Real.sqrt_nonneg _)
    · rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (K1dirB.chiB_sq_le _ _)
    · exact le_trans (hCG p.1 p.2 hp.1 hp.2) (le_max_left _ _)
  have hCS2int : Integrable (fun p : E3 × E3 =>
      ‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖) μ' := by
    obtain ⟨CG, hCG0, hCG⟩ := exists_box_bound hG'sm
    refine Integrable.of_bound (((continuous_norm.comp
        ((K1dirB.chiB_contDiff hℓ.ne').continuous.comp continuous_snd)).mul
        (continuous_norm.comp hG'sm.continuous)).aestronglyMeasurable)
      (Real.sqrt k1Chi * max CG 0) (hmem.mono fun p hp => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) (Real.sqrt_nonneg _)
    · rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (K1dirB.chiB_sq_le _ _)
    · exact le_trans (hCG p.1 p.2 hp.1 hp.2) (le_max_left _ _)
  have hchi_int : Integrable (fun p : E3 × E3 => ‖K1dirB.chiB (ellH v μ) p.1‖ ^ 2) μ' :=
    Integrable.of_bound (((continuous_norm.pow 2).comp
      ((K1dirB.chiB_contDiff hℓ.ne').continuous.comp continuous_fst)).aestronglyMeasurable) k1Chi
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact K1dirB.chiB_sq_le _ _)
  have hchi_int' : Integrable (fun p : E3 × E3 => ‖K1dirB.chiB (ellH v μ) p.2‖ ^ 2) μ' :=
    Integrable.of_bound (((continuous_norm.pow 2).comp
      ((K1dirB.chiB_contDiff hℓ.ne').continuous.comp continuous_snd)).aestronglyMeasurable) k1Chi
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact K1dirB.chiB_sq_le _ _)
  have hCS1 : (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.1‖ * ‖G' p.1 p.2‖ ∂μ')
      ≤ Real.sqrt (k1Chi * (ellH v μ) ^ 6) * Real.sqrt MB := by
    have hf : AEStronglyMeasurable (fun p : E3 × E3 => ‖K1dirB.chiB (ellH v μ) p.1‖) μ' :=
      ((K1dirB.chiB_contDiff hℓ.ne').continuous.norm.comp continuous_fst).aestronglyMeasurable
    have hg : AEStronglyMeasurable (fun p : E3 × E3 => ‖G' p.1 p.2‖) μ' :=
      hG'sm.continuous.norm.aestronglyMeasurable
    calc (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.1‖ * ‖G' p.1 p.2‖ ∂μ')
        = ∫ p : E3 × E3, |‖K1dirB.chiB (ellH v μ) p.1‖ * ‖G' p.1 p.2‖| ∂μ' := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          exact (abs_of_nonneg (by positivity)).symm
      _ ≤ Real.sqrt (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.1‖ ^ 2 ∂μ')
            * Real.sqrt (∫ p : E3 × E3, ‖G' p.1 p.2‖ ^ 2 ∂μ') :=
          Work.BoseFixB1S.int_abs_mul_le_sqrt_mul_sqrt hf hg hchi_int hG2_int
      _ = Real.sqrt (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.1‖ ^ 2 ∂μ')
            * Real.sqrt MB := by rw [hMBprod]
      _ ≤ Real.sqrt (k1Chi * (ellH v μ) ^ 6) * Real.sqrt MB :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hchi2) (Real.sqrt_nonneg _)
  have hCS2 : (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖ ∂μ')
      ≤ Real.sqrt (k1Chi * (ellH v μ) ^ 6) * Real.sqrt MB := by
    have hf : AEStronglyMeasurable (fun p : E3 × E3 => ‖K1dirB.chiB (ellH v μ) p.2‖) μ' :=
      ((K1dirB.chiB_contDiff hℓ.ne').continuous.norm.comp continuous_snd).aestronglyMeasurable
    have hg : AEStronglyMeasurable (fun p : E3 × E3 => ‖G' p.1 p.2‖) μ' :=
      hG'sm.continuous.norm.aestronglyMeasurable
    calc (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖ ∂μ')
        = ∫ p : E3 × E3, |‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖| ∂μ' := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          exact (abs_of_nonneg (by positivity)).symm
      _ ≤ Real.sqrt (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.2‖ ^ 2 ∂μ')
            * Real.sqrt (∫ p : E3 × E3, ‖G' p.1 p.2‖ ^ 2 ∂μ') :=
          Work.BoseFixB1S.int_abs_mul_le_sqrt_mul_sqrt hf hg hchi_int' hG2_int
      _ = Real.sqrt (∫ p : E3 × E3, ‖K1dirB.chiB (ellH v μ) p.2‖ ^ 2 ∂μ')
            * Real.sqrt MB := by rw [hMBprod]
      _ ≤ Real.sqrt (k1Chi * (ellH v μ) ^ 6) * Real.sqrt MB :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hchi2') (Real.sqrt_nonneg _)
  have hG1 : (∫ p : E3 × E3, ‖G' p.1 p.2‖ ∂μ')
      ≤ Real.sqrt ((ellH v μ) ^ 6) * Real.sqrt MB := by
    have hf : AEStronglyMeasurable (fun _ : E3 × E3 => (1 : ℝ)) μ' :=
      aestronglyMeasurable_const
    have hf2 : Integrable (fun p : E3 × E3 => (1 : ℝ) ^ 2) μ' := by
      simpa using integrable_const (μ := μ') (c := (1 : ℝ))
    have h := Work.BoseFixB1S.int_abs_mul_le_sqrt_mul_sqrt (μ := μ') hf
      (hG'sm.continuous.norm.aestronglyMeasurable) hf2 hG2_int
    have hone : (∫ p : E3 × E3, (1 : ℝ) ^ 2 ∂μ') = (ellH v μ) ^ 6 := by
      rw [one_pow]
      have h1 : (∫ _p : E3 × E3, (1 : ℝ) ∂μ') = μ'.real Set.univ := by
        rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
      rw [h1, hμuniv]
    calc (∫ p : E3 × E3, ‖G' p.1 p.2‖ ∂μ')
        = ∫ p : E3 × E3, |(1 : ℝ) * ‖G' p.1 p.2‖| ∂μ' := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          show ‖G' p.1 p.2‖ = |1 * ‖G' p.1 p.2‖|
          rw [one_mul, abs_of_nonneg (norm_nonneg _)]
      _ ≤ Real.sqrt (∫ p : E3 × E3, (1 : ℝ) ^ 2 ∂μ')
            * Real.sqrt (∫ p : E3 × E3, ‖G' p.1 p.2‖ ^ 2 ∂μ') := h
      _ = Real.sqrt ((ellH v μ) ^ 6) * Real.sqrt MB := by rw [hone, hMBprod]
  have hrowB : ‖∫ p : E3 × E3, Function.uncurry PB p ∂μ'‖ ≤ (ε / 8) * Real.sqrt MB := by
    have hpt : ∀ p : E3 × E3, ‖Function.uncurry PB p‖
        ≤ δB * ‖c3i‖ * (‖K1dirB.chiB (ellH v μ) p.1‖ * ‖G' p.1 p.2‖) := by
      intro p
      have h2 : ‖K1dirB.k1HB (ellH v μ) G' p.1 p.2‖
          ≤ ‖c3i‖ * (‖K1dirB.chiB (ellH v μ) p.1‖ * ‖G' p.1 p.2‖) := by
        rw [show K1dirB.k1HB (ellH v μ) G' p.1 p.2
            = ((((ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ) * K1dirB.chiB (ellH v μ) p.1
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2 * G' p.1 p.2 from rfl, hc3i]
        rw [norm_mul, norm_mul, norm_mul]
        calc ‖c3i‖ * ‖K1dirB.chiB (ellH v μ) p.1‖
              * ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2‖ * ‖G' p.1 p.2‖
            ≤ ‖c3i‖ * ‖K1dirB.chiB (ellH v μ) p.1‖ * 1 * ‖G' p.1 p.2‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (K1dirB.thetaFun_norm_le _ _) (by positivity))
                (norm_nonneg _)
          _ = ‖c3i‖ * (‖K1dirB.chiB (ellH v μ) p.1‖ * ‖G' p.1 p.2‖) := by ring
      have h3 := mul_le_mul (hNB N hNB' p.1) h2 (norm_nonneg _) hδBpos.le
      rw [show Function.uncurry PB p = k1ErrB v μ fu N Wa Wb p.1
          * K1dirB.k1HB (ellH v μ) G' p.1 p.2 from rfl, norm_mul]
      calc ‖k1ErrB v μ fu N Wa Wb p.1‖ * ‖K1dirB.k1HB (ellH v μ) G' p.1 p.2‖
          ≤ δB * (‖c3i‖ * (‖K1dirB.chiB (ellH v μ) p.1‖ * ‖G' p.1 p.2‖)) := h3
        _ = δB * ‖c3i‖ * (‖K1dirB.chiB (ellH v μ) p.1‖ * ‖G' p.1 p.2‖) := by ring
    calc ‖∫ p : E3 × E3, Function.uncurry PB p ∂μ'‖
        ≤ ∫ p : E3 × E3, ‖Function.uncurry PB p‖ ∂μ' := norm_integral_le_integral_norm _
      _ ≤ ∫ p : E3 × E3, δB * ‖c3i‖
            * (‖K1dirB.chiB (ellH v μ) p.1‖ * ‖G' p.1 p.2‖) ∂μ' :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _)
            (hCS1int.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = δB * ‖c3i‖ * (∫ p : E3 × E3,
            ‖K1dirB.chiB (ellH v μ) p.1‖ * ‖G' p.1 p.2‖ ∂μ') := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ δB * ‖c3i‖ * (Real.sqrt (k1Chi * (ellH v μ) ^ 6) * Real.sqrt MB) :=
          mul_le_mul_of_nonneg_left hCS1 (by positivity)
      _ = (ε / 8) * Real.sqrt MB := by
          rw [hc3i, hδB]
          exact deltaB_final hℓ
  have hrowC : ‖∫ p : E3 × E3, Function.uncurry PC p ∂μ'‖ ≤ (ε / 8) * Real.sqrt MB := by
    have hpt : ∀ p : E3 × E3, ‖Function.uncurry PC p‖
        ≤ δB * ‖c3i‖ * (‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖) := by
      intro p
      have h2 : ‖K1dirB.k1HC (ellH v μ) G' p.1 p.2‖
          ≤ ‖c3i‖ * (‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖) := by
        rw [show K1dirB.k1HC (ellH v μ) G' p.1 p.2
            = ((((ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1
              * K1dirB.chiB (ellH v μ) p.2 * G' p.1 p.2 from rfl, hc3i]
        rw [norm_mul, norm_mul, norm_mul]
        calc ‖c3i‖ * ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1‖
              * ‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖
            ≤ ‖c3i‖ * 1 * ‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (K1dirB.thetaFun_norm_le _ _) (norm_nonneg _))
                (norm_nonneg _)) (norm_nonneg _)
          _ = ‖c3i‖ * (‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖) := by ring
      have h3 := mul_le_mul (hNC N hNC' p.2) h2 (norm_nonneg _) hδBpos.le
      rw [show Function.uncurry PC p = k1ErrC v μ fu N Wa Wb p.2
          * K1dirB.k1HC (ellH v μ) G' p.1 p.2 from rfl, norm_mul]
      calc ‖k1ErrC v μ fu N Wa Wb p.2‖ * ‖K1dirB.k1HC (ellH v μ) G' p.1 p.2‖
          ≤ δB * (‖c3i‖ * (‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖)) := h3
        _ = δB * ‖c3i‖ * (‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖) := by ring
    calc ‖∫ p : E3 × E3, Function.uncurry PC p ∂μ'‖
        ≤ ∫ p : E3 × E3, ‖Function.uncurry PC p‖ ∂μ' := norm_integral_le_integral_norm _
      _ ≤ ∫ p : E3 × E3, δB * ‖c3i‖
            * (‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖) ∂μ' :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _)
            (hCS2int.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = δB * ‖c3i‖ * (∫ p : E3 × E3,
            ‖K1dirB.chiB (ellH v μ) p.2‖ * ‖G' p.1 p.2‖ ∂μ') := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ δB * ‖c3i‖ * (Real.sqrt (k1Chi * (ellH v μ) ^ 6) * Real.sqrt MB) :=
          mul_le_mul_of_nonneg_left hCS2 (by positivity)
      _ = (ε / 8) * Real.sqrt MB := by
          rw [hc3i, hδB]
          exact deltaB_final hℓ
  have hrowD : ‖∫ p : E3 × E3, Function.uncurry PD p ∂μ'‖ ≤ (ε / 8) * Real.sqrt MB := by
    have hpt : ∀ p : E3 × E3, ‖Function.uncurry PD p‖ ≤ δD * ‖c3i‖ * ‖G' p.1 p.2‖ := by
      intro p
      have h2 : ‖K1dirB.k1HD (ellH v μ) G' p.1 p.2‖ ≤ ‖c3i‖ * ‖G' p.1 p.2‖ := by
        rw [show K1dirB.k1HD (ellH v μ) G' p.1 p.2
            = ((((ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2 * G' p.1 p.2 from rfl, hc3i]
        rw [norm_mul, norm_mul, norm_mul]
        calc ‖c3i‖ * ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1‖
              * ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2‖ * ‖G' p.1 p.2‖
            ≤ ‖c3i‖ * 1 * 1 * ‖G' p.1 p.2‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul
                (mul_le_mul_of_nonneg_left (K1dirB.thetaFun_norm_le _ _) (norm_nonneg _))
                (K1dirB.thetaFun_norm_le _ _) (norm_nonneg _) (by positivity))
                (norm_nonneg _)
          _ = ‖c3i‖ * ‖G' p.1 p.2‖ := by ring
      have h3 := mul_le_mul (hND N hND') h2 (norm_nonneg _) hδDpos.le
      rw [show Function.uncurry PD p = k1ErrD v μ fu N Wa Wb
          * K1dirB.k1HD (ellH v μ) G' p.1 p.2 from rfl, norm_mul]
      calc ‖k1ErrD v μ fu N Wa Wb‖ * ‖K1dirB.k1HD (ellH v μ) G' p.1 p.2‖
          ≤ δD * (‖c3i‖ * ‖G' p.1 p.2‖) := h3
        _ = δD * ‖c3i‖ * ‖G' p.1 p.2‖ := by ring
    calc ‖∫ p : E3 × E3, Function.uncurry PD p ∂μ'‖
        ≤ ∫ p : E3 × E3, ‖Function.uncurry PD p‖ ∂μ' := norm_integral_le_integral_norm _
      _ ≤ ∫ p : E3 × E3, δD * ‖c3i‖ * ‖G' p.1 p.2‖ ∂μ' :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _)
            (hGB_int.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = δD * ‖c3i‖ * (∫ p : E3 × E3, ‖G' p.1 p.2‖ ∂μ') := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ δD * ‖c3i‖ * (Real.sqrt ((ellH v μ) ^ 6) * Real.sqrt MB) :=
          mul_le_mul_of_nonneg_left hG1 (by positivity)
      _ = (ε / 8) * Real.sqrt MB := by
          rw [hδD, hc3i]
          exact deltaD_final hℓ
  -- ============ the final assembly ============
  have htotal : ‖∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ), k1KerDiff v μ fu N Wa Wb w y * G' w y‖
      ≤ (ε / 4) * Real.sqrt PE + ((ε / 8) * Real.sqrt MB + (ε / 8) * Real.sqrt MB
          + (ε / 8) * Real.sqrt MB) := by
    rw [hsplit]
    have htri : ‖(∫ p : E3 × E3, Function.uncurry PA p ∂μ')
          - (∫ p : E3 × E3, Function.uncurry PB p ∂μ')
          - (∫ p : E3 × E3, Function.uncurry PC p ∂μ')
          + (∫ p : E3 × E3, Function.uncurry PD p ∂μ')‖
        ≤ ‖∫ p : E3 × E3, Function.uncurry PA p ∂μ'‖
          + ‖∫ p : E3 × E3, Function.uncurry PB p ∂μ'‖
          + ‖∫ p : E3 × E3, Function.uncurry PC p ∂μ'‖
          + ‖∫ p : E3 × E3, Function.uncurry PD p ∂μ'‖ := by
      calc ‖(∫ p : E3 × E3, Function.uncurry PA p ∂μ')
            - (∫ p : E3 × E3, Function.uncurry PB p ∂μ')
            - (∫ p : E3 × E3, Function.uncurry PC p ∂μ')
            + (∫ p : E3 × E3, Function.uncurry PD p ∂μ')‖
          ≤ ‖(∫ p : E3 × E3, Function.uncurry PA p ∂μ')
              - (∫ p : E3 × E3, Function.uncurry PB p ∂μ')
              - (∫ p : E3 × E3, Function.uncurry PC p ∂μ')‖
            + ‖∫ p : E3 × E3, Function.uncurry PD p ∂μ'‖ := norm_add_le _ _
        _ ≤ (‖(∫ p : E3 × E3, Function.uncurry PA p ∂μ')
              - (∫ p : E3 × E3, Function.uncurry PB p ∂μ')‖
            + ‖∫ p : E3 × E3, Function.uncurry PC p ∂μ'‖)
            + ‖∫ p : E3 × E3, Function.uncurry PD p ∂μ'‖ := by
            linarith [norm_sub_le ((∫ p : E3 × E3, Function.uncurry PA p ∂μ')
              - (∫ p : E3 × E3, Function.uncurry PB p ∂μ'))
              ((∫ p : E3 × E3, Function.uncurry PC p ∂μ'))]
        _ ≤ ((‖∫ p : E3 × E3, Function.uncurry PA p ∂μ'‖
            + ‖∫ p : E3 × E3, Function.uncurry PB p ∂μ'‖)
            + ‖∫ p : E3 × E3, Function.uncurry PC p ∂μ'‖)
            + ‖∫ p : E3 × E3, Function.uncurry PD p ∂μ'‖ := by
            linarith [norm_sub_le ((∫ p : E3 × E3, Function.uncurry PA p ∂μ'))
              ((∫ p : E3 × E3, Function.uncurry PB p ∂μ'))]
        _ = ‖∫ p : E3 × E3, Function.uncurry PA p ∂μ'‖
            + ‖∫ p : E3 × E3, Function.uncurry PB p ∂μ'‖
            + ‖∫ p : E3 × E3, Function.uncurry PC p ∂μ'‖
            + ‖∫ p : E3 × E3, Function.uncurry PD p ∂μ'‖ := by ring
    linarith [htri, hrowA, hrowB, hrowC, hrowD]
  have hfin : (ε / 4) * Real.sqrt PE + ((ε / 8) * Real.sqrt MB + (ε / 8) * Real.sqrt MB
      + (ε / 8) * Real.sqrt MB) ≤ ε * (Real.sqrt PE + Real.sqrt MB) := by
    nlinarith [Real.sqrt_nonneg PE, Real.sqrt_nonneg MB, hε]
  have hEq : ‖∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ),
        (K1exp v μ N (k1cfun fu Wa Wb (ellH v μ) N) w y
          - K1lim (ellH v μ) (Wa + Wb) w y) * G' w y‖
      = ‖∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ),
        k1KerDiff v μ fu N Wa Wb w y * G' w y‖ := rfl
  rw [hEq]
  linarith [htotal, hfin]


end Work.BoseBoxFock
