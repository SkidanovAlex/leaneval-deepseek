import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.latCubeSum_tendsto_L2
import Submission.Work.BoseBoxFock.latPer_bdd_of_norm_le
import Submission.Work.BoseBoxFock.latticeBall_tail_le
import Submission.Work.BoseBoxFock.latticeRow_tail_le
import Submission.Work.BoseBoxFock.limit_rows_add
import Submission.Work.BoseBoxFock.periodic_double_integral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1pairingDefs` — the vocabulary of the `K1exp` vs `K1lim` pairing bound

The truncation error of the expanded pair kernel `K1exp` against its limit `K1lim` splits,
definitionally, into the four rows `χχ, χ̂, χ̂, χ̂²` of `pinQ_kernel_expansion`
(`k1Kernel_decomp`).  This module fixes the vocabulary of that split (the generic lattice rows
`k1Row/k1RowCut/k1RowLim`, the coefficient sequences, the four error functions
`k1ErrA/k1ErrB/k1ErrC/k1ErrD`) and proves the *bookkeeping*: the four row splits, the kernel
decomposition, the decay majorants of the two `χ̂`-weights, the wrappers of the proved lattice-tail
statements and the annulus estimate for the cut rows.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. The generic lattice rows -/

noncomputable def k1Row (ℓ : ℝ) (N : ℕ) (F : (Fin 3 → ℤ) → ℂ) (z : E3) : ℂ :=
  ∑ k : Lab N, F (labVec N k) * latChr ℓ (labVec N k) z

noncomputable def k1RowCut (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (F : (Fin 3 → ℤ) → ℂ) (z : E3) : ℂ :=
  ∑ k : Lab N, ((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ) * F (labVec N k)
    * latChr ℓ (labVec N k) z

noncomputable def k1RowLim (ℓ : ℝ) (F : (Fin 3 → ℤ) → ℂ) (z : E3) : ℂ :=
  ∑' n : Fin 3 → ℤ, F n * latChr ℓ n z

/-- The **mirror** row: the same lattice row with the *conjugate* phase
`e^{-i⟪κ,z⟫} = e^{i⟪κ,-z⟫}` (the `χ̂`-rows `pinQC/pinQCl` carry it). -/
noncomputable def k1RowM (ℓ : ℝ) (N : ℕ) (F : (Fin 3 → ℤ) → ℂ) (z : E3) : ℂ :=
  ∑ k : Lab N, F (labVec N k)
    * Complex.exp (-(Complex.I * ((inner ℝ (kmomLab ℓ N k) z : ℝ) : ℂ)))

noncomputable def k1RowCutM (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (F : (Fin 3 → ℤ) → ℂ) (z : E3) : ℂ :=
  ∑ k : Lab N, ((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ) * F (labVec N k)
    * Complex.exp (-(Complex.I * ((inner ℝ (kmomLab ℓ N k) z : ℝ) : ℂ)))

noncomputable def k1RowLimM (ℓ : ℝ) (F : (Fin 3 → ℤ) → ℂ) (z : E3) : ℂ :=
  ∑' n : Fin 3 → ℤ, F n
    * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))

noncomputable def k1ChatWt (ℓ : ℝ) (W : E3 → ℝ) : (Fin 3 → ℤ) → ℂ :=
  fun n => ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)

noncomputable def k1KinWt (ℓ : ℝ) (W : E3 → ℝ) : (Fin 3 → ℤ) → ℂ :=
  fun n => Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomInt ℓ n)

noncomputable def k1ChiHatWt (ℓ : ℝ) (W : E3 → ℝ) : (Fin 3 → ℤ) → ℂ :=
  fun n => ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
    * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)

noncomputable def k1ChiHatSqWt (ℓ : ℝ) (W : E3 → ℝ) : (Fin 3 → ℤ) → ℂ :=
  fun n => ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
    * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ) ^ 2)

noncomputable def k1cfun (fu : Work.BoseBoxFix.LowCut) (Wa Wb : E3 → ℝ) (ℓ : ℝ) (N : ℕ)
    (k : Lab N) : ℝ :=
  uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) * Work.BoseFixR.chat Wa (kmomLab ℓ N k)
    + Work.BoseFixR.chat Wb (kmomLab ℓ N k)

/-! ## 2. Elementary rewrites -/

lemma k1latChr_labVec (ℓ : ℝ) (N : ℕ) (k : Lab N) (z : E3) :
    latChr ℓ (labVec N k) z
      = Complex.exp (Complex.I * ((inner ℝ (kmomLab ℓ N k) z : ℝ) : ℂ)) := rfl

/-- The mirror row is the original row at `-z`. -/
lemma k1RowM_eq (ℓ : ℝ) (N : ℕ) (F : (Fin 3 → ℤ) → ℂ) (z : E3) :
    k1RowM ℓ N F z = k1Row ℓ N F (-z) := by
  simp only [k1RowM, k1Row, k1latChr_labVec, inner_neg_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  push_cast
  ring_nf

lemma k1RowCutM_eq (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (F : (Fin 3 → ℤ) → ℂ) (z : E3) :
    k1RowCutM ℓ fu N F z = k1RowCut ℓ fu N F (-z) := by
  simp only [k1RowCutM, k1RowCut, k1latChr_labVec, inner_neg_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  push_cast
  ring_nf

lemma k1RowLimM_eq (ℓ : ℝ) (F : (Fin 3 → ℤ) → ℂ) (z : E3) :
    k1RowLimM ℓ F z = k1RowLim ℓ F (-z) := by
  simp only [k1RowLimM, k1RowLim, latChr, inner_neg_right]
  refine tsum_congr fun n => ?_
  congr 1
  push_cast
  ring_nf

lemma k1ChatWt_eq_kinWt {ℓ : ℝ} {W : E3 → ℝ} (hWe : ∀ z, W (-z) = W z) (n : Fin 3 → ℤ) :
    k1ChatWt ℓ W n = k1KinWt ℓ W n := by
  rw [k1ChatWt, k1KinWt]
  exact chat_eq_kinFT_of_even hWe (kmomInt ℓ n)

lemma k1RowSum_eq_cut (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (W : E3 → ℝ)
    (z : E3) : rowSum ℓ fu N W z = k1RowCut ℓ fu N (k1KinWt ℓ W) z := rfl

/-- A compactly supported function vanishes outside a ball (the radius form used by all the
lattice-tail statements). -/
lemma k1ExistsRadius {W : E3 → ℝ} (hW : HasCompactSupport W) :
    ∃ R : ℝ, ∀ x : E3, R < ‖x‖ → W x = 0 := by
  obtain ⟨R, hR⟩ := (hW.isCompact.isBounded).subset_closedBall (0 : E3)
  refine ⟨R, fun x hx => ?_⟩
  by_contra h
  have hxmem : x ∈ tsupport W := subset_tsupport W (by simpa [Function.mem_support] using h)
  have hdist : dist x 0 ≤ R := by
    simpa [Metric.mem_closedBall] using hR hxmem
  rw [dist_zero_right] at hdist
  linarith

/-! ## 3. The four row splits -/

lemma k1pinQA_split {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (hWae : ∀ z, Wa (-z) = Wa z) (hWbe : ∀ z, Wb (-z) = Wb z) (N : ℕ) (z : E3) :
    pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z
      = rowSum (ellH v μ) fu N Wa z + k1Row (ellH v μ) N (k1ChatWt (ellH v μ) Wb) z := by
  simp only [pinQA, rowSum, k1Row, k1cfun, k1ChatWt]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [k1latChr_labVec]
  push_cast
  rw [chat_eq_kinFT_of_even hWae (kmomLab (ellH v μ) N k)]
  simp only [kmomLab, kmomInt]
  ring_nf

lemma k1pinQB_split {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (N : ℕ) (w : E3) :
    pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N) w
      = k1RowCut (ellH v μ) fu N (k1ChiHatWt (ellH v μ) Wa) w
        + k1Row (ellH v μ) N (k1ChiHatWt (ellH v μ) Wb) w := by
  simp only [pinQB, k1RowCut, k1Row, k1ChiHatWt, k1cfun]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [k1latChr_labVec, kmomLab, kmomInt]
  push_cast
  ring_nf

lemma k1pinQC_split {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (N : ℕ) (y : E3) :
    pinQC v μ N (k1cfun fu Wa Wb (ellH v μ) N) y
      = k1RowCutM (ellH v μ) fu N (k1ChiHatWt (ellH v μ) Wa) y
        + k1RowM (ellH v μ) N (k1ChiHatWt (ellH v μ) Wb) y := by
  simp only [pinQC, k1RowCutM, k1RowM, k1ChiHatWt, k1cfun]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [kmomLab, kmomInt]
  push_cast
  ring_nf

lemma k1pinQD_split {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (N : ℕ) :
    pinQD v μ N (k1cfun fu Wa Wb (ellH v μ) N)
      = k1RowCut (ellH v μ) fu N (k1ChiHatSqWt (ellH v μ) Wa) 0
        + k1Row (ellH v μ) N (k1ChiHatSqWt (ellH v μ) Wb) 0 := by
  simp only [pinQD, k1RowCut, k1Row, k1ChiHatSqWt, k1cfun]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [k1latChr_labVec, kmomLab, kmomInt]
  simp only [inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  push_cast
  ring_nf


/-! ## 4. The four error functions and the kernel decomposition -/

noncomputable def k1ErrA (v : E3 → ℝ) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) : E3 → ℂ :=
  fun z => pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z - latPer3 (ellH v μ) (Wa + Wb) z

noncomputable def k1ErrB (v : E3 → ℝ) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) : E3 → ℂ :=
  fun w => pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N) w - pinQBl (ellH v μ) (Wa + Wb) w

noncomputable def k1ErrC (v : E3 → ℝ) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) : E3 → ℂ :=
  fun y => pinQC v μ N (k1cfun fu Wa Wb (ellH v μ) N) y - pinQCl (ellH v μ) (Wa + Wb) y

noncomputable def k1ErrD (v : E3 → ℝ) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) : ℂ :=
  pinQD v μ N (k1cfun fu Wa Wb (ellH v μ) N) - pinQDl (ellH v μ) (Wa + Wb)

/-- **The kernel decomposition.**  The difference of the truncated and the limit pair kernel is
the sum of the four row errors, weighted by the `χ`, `θ` factors. -/
lemma k1Kernel_decomp {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) (w y : E3) :
    K1exp v μ N (k1cfun fu Wa Wb (ellH v μ) N) w y - K1lim (ellH v μ) (Wa + Wb) w y
      = ((ellH v μ) ^ 3)⁻¹ *
        (((Submission.BoseGases.chiScale (ellH v μ) w : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (ellH v μ) y : ℝ) : ℂ)
            * k1ErrA v μ fu N Wa Wb (w - y)
          - ((Submission.BoseGases.chiScale (ellH v μ) w : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * k1ErrB v μ fu N Wa Wb w
          - Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
            * ((Submission.BoseGases.chiScale (ellH v μ) y : ℝ) : ℂ)
            * k1ErrC v μ fu N Wa Wb y
          + Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * k1ErrD v μ fu N Wa Wb) := by
  simp only [K1exp, K1lim, latPer3, k1ErrA, k1ErrB, k1ErrC, k1ErrD]
  ring

/-! ## 4b. The kernel difference, the bump bound and periodicity of the first row -/

/-- The kernel difference of the target: `K1exp` at the target's coefficient minus its limit. -/
noncomputable def k1KerDiff (v : E3 → ℝ) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) (w y : E3) : ℂ :=
  K1exp v μ N (k1cfun fu Wa Wb (ellH v μ) N) w y - K1lim (ellH v μ) (Wa + Wb) w y

/-- A uniform bound for the square of the corpus bump (the constant `48/π` of `χ`). -/
noncomputable def k1Chi : ℝ := 48 / Real.pi

lemma k1Chi_pos : 0 < k1Chi := by
  rw [k1Chi]; positivity

lemma chiScale_sq_le_k1Chi (ℓ : ℝ) (x : E3) :
    (Submission.BoseGases.chiScale ℓ x) ^ 2 ≤ k1Chi := by
  rw [k1Chi]
  exact Work.BoseRowQ2.chi_sq_le_48_div_pi' _

/-- The box has volume `ℓ³`. -/
lemma volume_real_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume : Measure E3).real (Work.BoseK15.corpusBox.boxL ℓ) = ℓ ^ 3 := by
  have h : (volume : Measure E3) (Work.BoseK15.corpusBox.boxL ℓ)
      = ENNReal.ofReal (ℓ ^ 3) := by
    rw [corpusBox_boxL_eq_cell hℓ]
    exact Work.BoseFixR.volume_boxL ℓ
  show ((volume : Measure E3) (Work.BoseK15.corpusBox.boxL ℓ)).toReal = ℓ ^ 3
  rw [h, ENNReal.toReal_ofReal (by positivity)]

/-- `pinQA` is invariant under the lattice translations. -/
lemma pinQA_add_latVec {v : E3 → ℝ} {μ : ℝ} (N : ℕ) {c : Lab N → ℝ} (m : Fin 3 → ℤ) (z : E3) :
    pinQA v μ N c (z + ellH v μ • latVec m) = pinQA v μ N c z := by
  have hℓ : (ellH v μ) ≠ 0 := ne_of_gt (ellH_pos v μ)
  simp only [pinQA]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact LatFourier.exp_I_inner_add_latVec hℓ (labVec N k) m z

/-- The first row error is invariant under the lattice translations (both of its terms are). -/
lemma k1ErrA_periodic {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) (m : Fin 3 → ℤ) (z : E3) :
    k1ErrA v μ fu N Wa Wb (z + ellH v μ • latVec m) = k1ErrA v μ fu N Wa Wb z := by
  simp only [k1ErrA]
  rw [pinQA_add_latVec, latPer3_add_latVec]

/-! ## 5. Majorant bounds for the row weights -/

/-- The `χ̂`-row weight decays (at least) at order `52` on the lattice. -/
lemma k1ChiHatWt_majorant {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖k1ChiHatWt ℓ W n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := chat_abs_le_uniform (W := W)
  obtain ⟨Cm, hCm0, hCm⟩ := hatChi_decay_52
  refine ⟨B * Cm, mul_nonneg hB0 hCm0, fun n => ?_⟩
  have hsmul : ℓ • kmomInt ℓ n = Work.BoseB4.vec n := by
    rw [kmomInt, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
  have h1 : ‖k1ChiHatWt ℓ W n‖ = |Work.BoseFixR.chat W (kmomInt ℓ n)|
      * |Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n)| := by
    rw [k1ChiHatWt, norm_mul]
    simp
  rw [h1, hsmul]
  calc |Work.BoseFixR.chat W (kmomInt ℓ n)|
        * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)|
      ≤ B * (Cm * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :=
        mul_le_mul (hB _) (hCm _) (abs_nonneg _) hB0
    _ = B * Cm * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by ring

/-- The `θθ`-row weight decays (at least) at order `52` on the lattice. -/
lemma k1ChiHatSqWt_majorant {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖k1ChiHatSqWt ℓ W n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := chat_abs_le_uniform (W := W)
  obtain ⟨Cm, hCm0, hCm⟩ := hatChi_decay_52
  refine ⟨B * Cm ^ 2, by positivity, fun n => ?_⟩
  have hsmul : ℓ • kmomInt ℓ n = Work.BoseB4.vec n := by
    rw [kmomInt, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
  set x : ℝ := 1 + ‖Work.BoseB4.vec n‖ ^ 2 with hx
  have hx1 : 1 ≤ x := by rw [hx]; exact le_add_of_nonneg_right (sq_nonneg _)
  have h1 : ‖k1ChiHatSqWt ℓ W n‖ = |Work.BoseFixR.chat W (kmomInt ℓ n)|
      * |Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n)| ^ 2 := by
    rw [k1ChiHatSqWt, norm_mul, norm_pow]
    simp
  rw [h1, hsmul]
  have h2 : |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)| ^ 2
      ≤ (Cm * (x ^ 52)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hCm _) 2
  have h4 : ((x ^ 52)⁻¹) ^ 2 ≤ (x ^ 52)⁻¹ := by
    have hinv : (x ^ 52)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hx1)
    calc ((x ^ 52)⁻¹) ^ 2 = (x ^ 52)⁻¹ * (x ^ 52)⁻¹ := by ring
      _ ≤ (x ^ 52)⁻¹ * 1 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (x ^ 52)⁻¹ := mul_one _
  calc |Work.BoseFixR.chat W (kmomInt ℓ n)|
        * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)| ^ 2
      ≤ B * (Cm * (x ^ 52)⁻¹) ^ 2 :=
        mul_le_mul (hB _) h2 (by positivity) hB0
    _ = B * Cm ^ 2 * ((x ^ 52)⁻¹) ^ 2 := by ring
    _ ≤ B * Cm ^ 2 * (x ^ 52)⁻¹ :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

/-! ## 6. Wrappers for the lattice tail statements -/

/-- The cut `χχ`-row converges in `L²` to `ℓ³ latPer` (the proved sibling). -/
lemma k1RowSum_L2 {ℓ R : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut) {W : E3 → ℝ}
    (hWm : AEStronglyMeasurable W volume) (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C)
    (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ, ‖rowSum ℓ fu N' W z - latPer3 ℓ W z‖ ^ 2) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := latRowSum_tendsto_L2 (ℓ := ℓ) (R := R) hℓ fu hWm hWb hWs ε hε
  exact ⟨N, fun N' hN' => by
    simpa only [rowSum, latPer3, LatFourier.latPer, latChr, kmomLab, kmomInt] using hN N' hN'⟩

/-- The un-cut `χχ`-row converges in `L²` to `ℓ³ latPer` (the proved sibling). -/
lemma k1CubeSum_L2 {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWm : AEStronglyMeasurable W volume) (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C)
    (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
        ‖k1Row ℓ N' (k1KinWt ℓ W) z - latPer3 ℓ W z‖ ^ 2) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := latCubeSum_tendsto_L2 (ℓ := ℓ) (R := R) hℓ hWm hWb hWs ε hε
  exact ⟨N, fun N' hN' => by
    simpa only [k1Row, k1KinWt, latPer3, LatFourier.latPer, latChr, kmomLab, kmomInt] using hN N' hN'⟩

/-- The finite lattice row converges to its `tsum` limit (uniform in the position). -/
lemma k1Row_tendsto {ℓ : ℝ} (hℓ : 0 < ℓ) {F : (Fin 3 → ℤ) → ℂ}
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ z : E3,
      ‖k1Row ℓ N' F z - k1RowLim ℓ F z‖ ≤ ε :=
  latticeRow_tail_le hℓ hF

/-- The ball tail of the lattice weights is arbitrarily small. -/
lemma k1BallTail_le {ℓ : ℝ} (hℓ : 0 < ℓ) {F : (Fin 3 → ℤ) → ℂ}
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∑' n : Fin 3 → ℤ, if (N' : ℝ) ≤ ‖latVec n‖ then ‖F n‖ else 0) ≤ ε :=
  latticeBall_tail_le hℓ hF

/-- The ball tail is monotone in the threshold. -/
lemma k1BallTail_mono {F : (Fin 3 → ℤ) → ℂ} {ρ ρ' : ℝ} (h : ρ ≤ ρ')
    (hsum : Summable (fun n : Fin 3 → ℤ => if ρ' ≤ ‖latVec n‖ then ‖F n‖ else 0))
    (hsum' : Summable (fun n : Fin 3 → ℤ => if ρ ≤ ‖latVec n‖ then ‖F n‖ else 0)) :
    (∑' n : Fin 3 → ℤ, if ρ' ≤ ‖latVec n‖ then ‖F n‖ else 0)
      ≤ ∑' n : Fin 3 → ℤ, if ρ ≤ ‖latVec n‖ then ‖F n‖ else 0 := by
  refine Summable.tsum_le_tsum (fun n => ?_) hsum hsum'
  by_cases hn' : ρ' ≤ ‖latVec n‖
  · have hn : ρ ≤ ‖latVec n‖ := le_trans h hn'
    rw [if_pos hn', if_pos hn]
  · rw [if_neg hn']
    split <;> positivity

/-! ## 7. The annulus estimate for the cut rows -/

lemma k1norm_latChr (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ‖latChr ℓ n z‖ = 1 := by
  rw [latChr, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `uvCut` equals `1` for lattice momenta inside the ball of radius `N/4`. -/
lemma k1uvCut_eq_one {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut) {N : ℕ} (hN : 1 ≤ N)
    {k : Lab N} (hk : ‖latVec (labVec N k)‖ ≤ (N : ℝ) / 4) :
    uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) = 1 := by
  have huvRad : 0 < uvRad ℓ N := by
    rw [uvRad]
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have huvRad_eq : uvRad ℓ N = (2 * Real.pi / ℓ) * ((N : ℝ) / 4) := by
    rw [uvRad]; ring
  have hnorm : ‖kmomLab ℓ N k‖ = (2 * Real.pi / ℓ) * ‖latVec (labVec N k)‖ := by
    rw [show kmomLab ℓ N k = kmomInt ℓ (labVec N k) from rfl,
      LatFourier.kmomInt_eq_smul_latVec, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hle : ‖kmomLab ℓ N k‖ ≤ uvRad ℓ N := by
    rw [hnorm, huvRad_eq]
    exact mul_le_mul_of_nonneg_left hk (by positivity)
  rw [uvCut]
  exact fu.one _ ((div_le_one huvRad).mpr hle)

/-- The annulus estimate: the difference of the un-cut and the cut generic row is bounded by the
lattice tail outside the ball of radius `N/4` (only the modes where the cut is active survive). -/
lemma k1Row_sub_cut_le {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut) {N : ℕ}
    (hN : 1 ≤ N) {F : (Fin 3 → ℤ) → ℂ}
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) (z : E3) :
    ‖k1Row ℓ N F z - k1RowCut ℓ fu N F z‖
      ≤ ∑' n : Fin 3 → ℤ, (if (N : ℝ) / 4 ≤ ‖latVec n‖ then ‖F n‖ else 0) := by
  obtain ⟨C, hC0, hC⟩ := hF
  -- the difference
  have hdiff : k1Row ℓ N F z - k1RowCut ℓ fu N F z
      = ∑ k : Lab N, (((1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)
          * F (labVec N k) * latChr ℓ (labVec N k) z := by
    simp only [k1Row, k1RowCut, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  -- summability of the tail family
  set gfun : (Fin 3 → ℤ) → ℝ :=
    fun n => (if (N : ℝ) / 4 ≤ ‖latVec n‖ then ‖F n‖ else 0) with hgfun
  have hsumm : Summable gfun := by
    rw [hgfun]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_vec_inv_one_add_norm_sq (k := 52) (by norm_num)).mul_left C)
    by_cases h : (N : ℝ) / 4 ≤ ‖latVec n‖
    · rw [if_pos h]
      exact hC n
    · rw [if_neg h]
      exact mul_nonneg hC0 (by positivity)
  rw [hdiff]
  calc ‖∑ k : Lab N, (((1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)
          * F (labVec N k) * latChr ℓ (labVec N k) z‖
      ≤ ∑ k : Lab N, ‖(((1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)
          * F (labVec N k) * latChr ℓ (labVec N k) z‖ := norm_sum_le _ _
    _ ≤ ∑ k : Lab N, gfun (labVec N k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        by_cases hk : ‖latVec (labVec N k)‖ ≤ (N : ℝ) / 4
        · have huv := k1uvCut_eq_one hℓ fu hN hk
          have hz : ‖(((1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)
              * F (labVec N k) * latChr ℓ (labVec N k) z‖ = 0 := by
            rw [huv]
            simp
          rw [hz, hgfun]
          simp only []
          split <;> positivity
        · have hlt : (N : ℝ) / 4 < ‖latVec (labVec N k)‖ := lt_of_not_ge hk
          have hgv : gfun (labVec N k) = ‖F (labVec N k)‖ := by
            rw [hgfun]
            simp only []
            rw [if_pos (le_of_lt hlt)]
          rw [hgv]
          have hu0 : 0 ≤ uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) := by rw [uvCut]; exact fu.nonneg _
          have hu1 : uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) ≤ 1 := by rw [uvCut]; exact fu.le_one _
          have hle1 : ‖(((1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)‖ ≤ 1 := by
            have h2 : ‖(((1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)‖
                = |(1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k)| := by
              have hsq : ‖(((1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)‖ ^ 2
                  = |(1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k)| ^ 2 := by
                rw [Complex.sq_norm, Complex.normSq_ofReal, sq_abs]
                ring
              nlinarith [hsq, norm_nonneg (((1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ),
                abs_nonneg ((1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k))]
            rw [h2, abs_le]
            exact ⟨by linarith, by linarith⟩
          calc ‖(((1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)
                * F (labVec N k) * latChr ℓ (labVec N k) z‖
              = ‖(((1 : ℝ) - uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)‖
                  * ‖F (labVec N k)‖ := by
                  rw [norm_mul, norm_mul, k1norm_latChr, mul_one]
            _ ≤ 1 * ‖F (labVec N k)‖ :=
                mul_le_mul_of_nonneg_right hle1 (norm_nonneg _)
            _ = ‖F (labVec N k)‖ := one_mul _
    _ = ∑ n ∈ Work.BoseRowQ2.cube N, gfun n := by
        have h1 : (∑ k : Lab N, gfun (labVec N k))
            = ∑ n ∈ Finset.univ.image (labVec N), gfun n :=
          (Finset.sum_image (s := Finset.univ) (f := gfun) (g := labVec N)
            (fun a _ b _ hab => Work.BoseRowQ2.labVec_inj' N hab)).symm
        rw [h1, Work.BoseRowQ2.image_labVec_eq_cube]
    _ ≤ ∑' n : Fin 3 → ℤ, gfun n :=
        Summable.sum_le_tsum (Work.BoseRowQ2.cube N) (fun i _ => by positivity) hsumm

end Work.BoseBoxFock
