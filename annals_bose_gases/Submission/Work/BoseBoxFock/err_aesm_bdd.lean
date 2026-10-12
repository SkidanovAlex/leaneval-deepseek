import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1pairingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
## Auxiliary lemmas for `err_aesm_bdd`

The four rows `k1ErrA … k1ErrD` of the `K1exp`-vs-`K1lim` error are differences of a *finite*
lattice sum (`pinQA … pinQD`, continuous in the position variable, hence a.e. strongly
measurable) and of a *lattice series* (`latPer3`, or one of the absolutely convergent `χ̂`-series
`pinQBl/pinQCl/pinQDl`).  This file collects the two kinds of facts needed for the statement:

* measurability:  the periodisation `∑'_m W(· + ℓ•latVec m)` is a.e. strongly measurable as soon
  as `W` is (each translated summand is, and `AEStronglyMeasurable.tsum` is unconditional), and the
  three `χ̂`-series are a.e. strongly measurable (each summand is continuous in the position);
* boundedness:  the `χ̂`-series are dominated by the summable lattice majorant
  `C·(1+‖vec n‖²)^{-52}` (uniformly in the position, the phase being unimodular), while the `χχ`
  row is bounded on the box-ball `‖z‖ ≤ √3 ℓ` by the proved `latPer_bdd_of_norm_le`.
-/

/-- `‖e^{ir}‖ = 1`. -/
lemma errBdd_norm_exp_I (r : ℝ) : ‖Complex.exp (Complex.I * ((r : ℝ) : ℂ))‖ = 1 := by
  rw [show Complex.I * ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) * Complex.I by ring,
    Complex.norm_exp_ofReal_mul_I]

/-- `‖e^{-ir}‖ = 1`. -/
lemma errBdd_norm_exp_neg_I (r : ℝ) : ‖Complex.exp (-(Complex.I * ((r : ℝ) : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * ((r : ℝ) : ℂ)) = ((-r : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- The norm of a real cast in `ℂ` (with `K` fixed, unlike `RCLike.norm_ofReal`). -/
lemma errBdd_norm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have hsq : ‖((r : ℝ) : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal, sq_abs]
    ring
  nlinarith [hsq, norm_nonneg (((r : ℝ) : ℂ)), abs_nonneg r]

/-- The pointwise form of the difference of two functions. -/
lemma errBdd_sub_apply_eq {f g : E3 → ℂ} : (f - g : E3 → ℂ) = fun z => f z - g z := by
  funext z; rfl

/-- A uniform bound for the corpus bump `χ̂` (its order-`52` decay, at `p = 0`). -/
lemma errBdd_hatChi_bdd :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : E3, |Work.BoseK15.corpusBox.hatChi p| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hatChi_decay_52
  refine ⟨C, hC0, fun p => ?_⟩
  have h1 : ((1 + ‖p‖ ^ 2) ^ 52)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (le_add_of_nonneg_right (by positivity)))
  calc |Work.BoseK15.corpusBox.hatChi p| ≤ C * ((1 + ‖p‖ ^ 2) ^ 52)⁻¹ := hC p
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left h1 hC0
    _ = C := mul_one C

/-- The lattice periodisation of an a.e. strongly measurable weight is a.e. strongly measurable:
each translated summand is, and `AEStronglyMeasurable.tsum` needs no summability. -/
lemma errBdd_latPer_aesm {ℓ : ℝ} {W : E3 → ℝ} (hWm : AEStronglyMeasurable W volume) :
    AEStronglyMeasurable (LatFourier.latPer ℓ W) volume := by
  change AEStronglyMeasurable (fun z : E3 => LatFourier.latPer ℓ W z) volume
  have hterm : ∀ m : Fin 3 → ℤ,
      AEStronglyMeasurable (fun z : E3 => (W (z + ℓ • latVec m) : ℂ)) volume := by
    intro m
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hWm.comp_measurePreserving (by
        simpa [add_comm] using
          measurePreserving_add_left (volume : Measure E3) (ℓ • latVec m)))
  have h : AEStronglyMeasurable
      (fun z : E3 => ∑' m : Fin 3 → ℤ, (W (z + ℓ • latVec m) : ℂ)) volume :=
    AEStronglyMeasurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) hterm
  simpa only [LatFourier.latPer] using h

/-- `latPer3 = ℓ³ · latPer` is a.e. strongly measurable. -/
lemma errBdd_latPer3_aesm {ℓ : ℝ} {W : E3 → ℝ} (hWm : AEStronglyMeasurable W volume) :
    AEStronglyMeasurable (latPer3 ℓ W) volume := by
  change AEStronglyMeasurable (fun z : E3 => latPer3 ℓ W z) volume
  have hc : AEStronglyMeasurable (fun _ : E3 => (((ℓ ^ 3 : ℝ)) : ℂ)) volume :=
    continuous_const.aestronglyMeasurable
  have h : AEStronglyMeasurable
      (fun z : E3 => (((ℓ ^ 3 : ℝ)) : ℂ) * LatFourier.latPer ℓ W z) volume :=
    hc.mul (errBdd_latPer_aesm hWm)
  simpa only [latPer3] using h

/-- The periodisation is bounded on the box-ball (the proved `latPer_bdd_of_norm_le`). -/
lemma errBdd_latPer3_bdd {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : E3, ‖z‖ ≤ Real.sqrt 3 * ℓ → ‖latPer3 ℓ W z‖ ≤ D := by
  obtain ⟨D, hD0, hD⟩ := latPer_bdd_of_norm_le hℓ hWb hWs
  refine ⟨‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ * D, mul_nonneg (norm_nonneg _) hD0, fun z hz => ?_⟩
  rw [latPer3, norm_mul]
  exact mul_le_mul_of_nonneg_left (hD z hz) (norm_nonneg _)

/-- **The lattice series bound.**  A family dominated by the summable lattice majorant
`C·(1+‖vec n‖²)^{-52}` has, multiplied by *any* unimodular phase, a `tsum` bounded by a constant
independent of the phase. -/
lemma errBdd_tsum_bdd {F : (Fin 3 → ℤ) → ℂ}
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (φ : (Fin 3 → ℤ) → ℂ), (∀ n : Fin 3 → ℤ, ‖φ n‖ = 1) →
      ‖∑' n : Fin 3 → ℤ, F n * φ n‖ ≤ C₀ := by
  obtain ⟨C, hC0, hC⟩ := hF
  have hsumm : Summable (fun n : Fin 3 → ℤ =>
      C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :=
    (summable_vec_inv_one_add_norm_sq (k := 52) (by norm_num)).mul_left C
  refine ⟨∑' n : Fin 3 → ℤ, C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹,
    tsum_nonneg (fun n => mul_nonneg hC0 (by positivity)), ?_⟩
  intro φ hφ
  have hle : ∀ n : Fin 3 → ℤ,
      ‖F n * φ n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
    intro n
    rw [norm_mul, hφ n, mul_one]
    exact hC n
  have hsumm' : Summable (fun n : Fin 3 → ℤ => ‖F n * φ n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hsumm
  exact (norm_tsum_le_tsum_norm hsumm').trans (Summable.tsum_le_tsum hle hsumm' hsumm)

/-- The `tsum` with a `+`-phase is a.e. strongly measurable. -/
lemma errBdd_tsum_exp_aesm (ℓ : ℝ) (F : (Fin 3 → ℤ) → ℂ) :
    AEStronglyMeasurable (fun w : E3 => ∑' n : Fin 3 → ℤ,
      F n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))) volume := by
  refine AEStronglyMeasurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ))
    (fun n => ?_)
  have hcont : Continuous (fun w : E3 =>
      F n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))) :=
    Continuous.mul continuous_const (Complex.continuous_exp.comp (Continuous.mul continuous_const
      (Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_id))))
  exact hcont.aestronglyMeasurable

/-- The `tsum` with a `−`-phase is a.e. strongly measurable. -/
lemma errBdd_tsum_neg_exp_aesm (ℓ : ℝ) (F : (Fin 3 → ℤ) → ℂ) :
    AEStronglyMeasurable (fun y : E3 => ∑' n : Fin 3 → ℤ,
      F n * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))) volume := by
  refine AEStronglyMeasurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ))
    (fun n => ?_)
  have hcont : Continuous (fun y : E3 =>
      F n * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))) :=
    Continuous.mul continuous_const (Complex.continuous_exp.comp (Continuous.neg
      (Continuous.mul continuous_const (Complex.continuous_ofReal.comp
        (Continuous.inner continuous_const continuous_id)))))
  exact hcont.aestronglyMeasurable

/-- `pinQBl` is a.e. strongly measurable. -/
lemma errBdd_pinQBl_aesm {ℓ : ℝ} {W : E3 → ℝ} :
    AEStronglyMeasurable (pinQBl ℓ W) volume := by
  change AEStronglyMeasurable (fun w : E3 => pinQBl ℓ W w) volume
  have h := errBdd_tsum_exp_aesm ℓ (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ))
  simpa only [pinQBl] using h

/-- `pinQCl` is a.e. strongly measurable. -/
lemma errBdd_pinQCl_aesm {ℓ : ℝ} {W : E3 → ℝ} :
    AEStronglyMeasurable (pinQCl ℓ W) volume := by
  change AEStronglyMeasurable (fun y : E3 => pinQCl ℓ W y) volume
  have h := errBdd_tsum_neg_exp_aesm ℓ (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ))
  simpa only [pinQCl] using h

/-- The lattice weight of the `χ̂`-rows, dominated by `B·Cm·(1+‖vec n‖²)^{-52}`. -/
lemma errBdd_chatHat1_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)‖
        ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := chat_abs_le_uniform (W := W)
  obtain ⟨Cm, hCm0, hCm⟩ := hatChi_decay_52
  refine ⟨B * Cm, mul_nonneg hB0 hCm0, fun n => ?_⟩
  have hsmul : ℓ • kmomInt ℓ n = Work.BoseB4.vec n := by
    rw [kmomInt, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
  have hnorm : ‖((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)‖
      = |Work.BoseFixR.chat W (kmomInt ℓ n)|
        * |Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n)| := by
    simp only [norm_mul, errBdd_norm_ofReal]
  rw [hnorm, hsmul]
  calc |Work.BoseFixR.chat W (kmomInt ℓ n)| * |Work.BoseK15.corpusBox.hatChi
        (Work.BoseB4.vec n)|
      ≤ B * (Cm * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :=
        mul_le_mul (hB _) (hCm _) (abs_nonneg _) hB0
    _ = B * Cm * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by ring

/-- The lattice weight of the `θθ`-row, dominated by `B·Cm²·(1+‖vec n‖²)^{-52}`. -/
lemma errBdd_chatHat2_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 2‖
        ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := chat_abs_le_uniform (W := W)
  obtain ⟨Cm, hCm0, hCm⟩ := hatChi_decay_52
  refine ⟨B * Cm ^ 2, by positivity, fun n => ?_⟩
  have hsmul : ℓ • kmomInt ℓ n = Work.BoseB4.vec n := by
    rw [kmomInt, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
  have hnorm : ‖((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
      * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 2‖
      = |Work.BoseFixR.chat W (kmomInt ℓ n)|
        * |Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n)| ^ 2 := by
    simp only [norm_mul, norm_pow, errBdd_norm_ofReal]
  rw [hnorm, hsmul]
  have hx1 : (1 : ℝ) ≤ 1 + ‖Work.BoseB4.vec n‖ ^ 2 := le_add_of_nonneg_right (by positivity)
  have hy1 : ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ hx1)
  have hy0 : 0 ≤ ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by positivity
  have hy : (((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) ^ 2
      ≤ ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
    simpa [pow_two] using mul_le_of_le_one_right hy0 hy1
  calc |Work.BoseFixR.chat W (kmomInt ℓ n)| * |Work.BoseK15.corpusBox.hatChi
        (Work.BoseB4.vec n)| ^ 2
      ≤ B * (Cm * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) ^ 2 :=
        mul_le_mul (hB _) (pow_le_pow_left₀ (abs_nonneg _) (hCm _) 2) (by positivity) hB0
    _ = B * Cm ^ 2 * (((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) ^ 2 := by ring
    _ ≤ B * Cm ^ 2 * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ :=
        mul_le_mul_of_nonneg_left hy (by positivity)

/-- `pinQBl` is bounded, uniformly in the position. -/
lemma errBdd_pinQBl_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : E3, ‖pinQBl ℓ W w‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := errBdd_chatHat1_bdd hℓ W
  obtain ⟨C₀, hC₀0, hC₀⟩ := errBdd_tsum_bdd ⟨C, hC0, hC⟩
  refine ⟨C₀, hC₀0, fun w => ?_⟩
  have h := hC₀ (fun n : Fin 3 → ℤ =>
      Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ)))
    (fun n => errBdd_norm_exp_I _)
  simpa only [pinQBl] using h

/-- `pinQCl` is bounded, uniformly in the position. -/
lemma errBdd_pinQCl_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E3, ‖pinQCl ℓ W y‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := errBdd_chatHat1_bdd hℓ W
  obtain ⟨C₀, hC₀0, hC₀⟩ := errBdd_tsum_bdd ⟨C, hC0, hC⟩
  refine ⟨C₀, hC₀0, fun y => ?_⟩
  have h := hC₀ (fun n : Fin 3 → ℤ =>
      Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ))))
    (fun n => errBdd_norm_exp_neg_I _)
  simpa only [pinQCl] using h

/-- `pinQDl` (a constant) is bounded. -/
lemma errBdd_pinQDl_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖pinQDl ℓ W‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := errBdd_chatHat2_bdd hℓ W
  obtain ⟨C₀, hC₀0, hC₀⟩ := errBdd_tsum_bdd ⟨C, hC0, hC⟩
  refine ⟨C₀, hC₀0, ?_⟩
  have h := hC₀ (fun _ : Fin 3 → ℤ => (1 : ℂ)) (fun n => by simp)
  simpa only [pinQDl, mul_one] using h

/-- The finite-sum bound: a lattice row with coefficients bounded by `B` and a weight bounded by
`V` is bounded by `#Lab N · B · V`. -/
lemma errBdd_finset_bdd {N : ℕ} {c : Lab N → ℝ} {B V : ℝ} (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hc : ∀ k : Lab N, |c k| ≤ B) (F : Lab N → ℂ) (hF : ∀ k : Lab N, ‖F k‖ ≤ V) :
    ‖∑ k : Lab N, (c k : ℂ) * F k‖ ≤ (Fintype.card (Lab N) : ℝ) * (B * V) := by
  calc ‖∑ k : Lab N, (c k : ℂ) * F k‖
      ≤ ∑ k : Lab N, ‖(c k : ℂ) * F k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Lab N, B * V := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        simp only [norm_mul, errBdd_norm_ofReal]
        exact mul_le_mul (hc k) (hF k) (norm_nonneg _) hB
    _ = (Fintype.card (Lab N) : ℝ) * (B * V) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The `χχ` row is continuous in the position (finite sum of characters). -/
lemma errBdd_pinQA_cont {v : E3 → ℝ} {μ : ℝ} {N : ℕ} (c : Lab N → ℝ) :
    Continuous (pinQA v μ N c) := by
  change Continuous (fun z : E3 => pinQA v μ N c z)
  simp only [pinQA]
  refine continuous_finsetSum _ (fun k _ => ?_)
  refine Continuous.mul continuous_const ?_
  refine Complex.continuous_exp.comp ?_
  refine Continuous.mul continuous_const ?_
  exact Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_id)

/-- The first `χ̂` row is continuous in the position. -/
lemma errBdd_pinQB_cont {v : E3 → ℝ} {μ : ℝ} {N : ℕ} (c : Lab N → ℝ) :
    Continuous (pinQB v μ N c) := by
  change Continuous (fun w : E3 => pinQB v μ N c w)
  simp only [pinQB]
  refine continuous_finsetSum _ (fun k _ => ?_)
  refine Continuous.mul (Continuous.mul continuous_const continuous_const) ?_
  refine Complex.continuous_exp.comp ?_
  refine Continuous.mul continuous_const ?_
  exact Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_id)

/-- The second `χ̂` row is continuous in the position. -/
lemma errBdd_pinQC_cont {v : E3 → ℝ} {μ : ℝ} {N : ℕ} (c : Lab N → ℝ) :
    Continuous (pinQC v μ N c) := by
  change Continuous (fun y : E3 => pinQC v μ N c y)
  simp only [pinQC]
  refine continuous_finsetSum _ (fun k _ => ?_)
  refine Continuous.mul (Continuous.mul continuous_const continuous_const) ?_
  refine Complex.continuous_exp.comp ?_
  refine Continuous.neg ?_
  refine Continuous.mul continuous_const ?_
  exact Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_id)

/-- The `χχ` row is a.e. strongly measurable. -/
lemma errBdd_pinQA_aesm {v : E3 → ℝ} {μ : ℝ} {N : ℕ} (c : Lab N → ℝ) :
    AEStronglyMeasurable (fun z : E3 => pinQA v μ N c z) volume :=
  (errBdd_pinQA_cont c).aestronglyMeasurable

/-- The first `χ̂` row is a.e. strongly measurable. -/
lemma errBdd_pinQB_aesm {v : E3 → ℝ} {μ : ℝ} {N : ℕ} (c : Lab N → ℝ) :
    AEStronglyMeasurable (fun w : E3 => pinQB v μ N c w) volume :=
  (errBdd_pinQB_cont c).aestronglyMeasurable

/-- The second `χ̂` row is a.e. strongly measurable. -/
lemma errBdd_pinQC_aesm {v : E3 → ℝ} {μ : ℝ} {N : ℕ} (c : Lab N → ℝ) :
    AEStronglyMeasurable (fun y : E3 => pinQC v μ N c y) volume :=
  (errBdd_pinQC_cont c).aestronglyMeasurable

/-- The `χχ` row is bounded (uniformly in the position). -/
lemma errBdd_pinQA_bdd {v : E3 → ℝ} {μ : ℝ} {N : ℕ} {c : Lab N → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hc : ∀ k : Lab N, |c k| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, ‖pinQA v μ N c z‖ ≤ C := by
  refine ⟨(Fintype.card (Lab N) : ℝ) * B, mul_nonneg (by positivity) hB, fun z => ?_⟩
  have h := errBdd_finset_bdd (N := N) (B := B) (V := 1) hB (by norm_num) hc
    (fun k : Lab N => Complex.exp
      (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) z : ℝ) : ℂ)))
    (fun k => le_of_eq (errBdd_norm_exp_I _))
  rw [mul_one] at h
  simpa only [pinQA] using h

/-- The first `χ̂` row is bounded (uniformly in the position). -/
lemma errBdd_pinQB_bdd {v : E3 → ℝ} {μ : ℝ} {N : ℕ} {c : Lab N → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hc : ∀ k : Lab N, |c k| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : E3, ‖pinQB v μ N c w‖ ≤ C := by
  obtain ⟨Ch, hCh0, hCh⟩ := errBdd_hatChi_bdd
  refine ⟨(Fintype.card (Lab N) : ℝ) * (B * Ch), mul_nonneg (by positivity)
    (mul_nonneg hB hCh0), fun w => ?_⟩
  have hF : ∀ k : Lab N, ‖((Work.BoseK15.corpusBox.hatChi
        (ellH v μ • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
      * Complex.exp (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) w : ℝ) : ℂ))‖ ≤ Ch := by
    intro k
    simp only [norm_mul, errBdd_norm_exp_I, errBdd_norm_ofReal, mul_one]
    exact hCh _
  have h := errBdd_finset_bdd (N := N) (B := B) (V := Ch) hB hCh0 hc _ hF
  simpa only [pinQB, mul_assoc] using h

/-- The second `χ̂` row is bounded (uniformly in the position). -/
lemma errBdd_pinQC_bdd {v : E3 → ℝ} {μ : ℝ} {N : ℕ} {c : Lab N → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hc : ∀ k : Lab N, |c k| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E3, ‖pinQC v μ N c y‖ ≤ C := by
  obtain ⟨Ch, hCh0, hCh⟩ := errBdd_hatChi_bdd
  refine ⟨(Fintype.card (Lab N) : ℝ) * (B * Ch), mul_nonneg (by positivity)
    (mul_nonneg hB hCh0), fun y => ?_⟩
  have hF : ∀ k : Lab N, ‖((Work.BoseK15.corpusBox.hatChi
        (ellH v μ • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
      * Complex.exp (-(Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) y : ℝ) : ℂ)))‖ ≤ Ch := by
    intro k
    simp only [norm_mul, errBdd_norm_exp_neg_I, errBdd_norm_ofReal, mul_one]
    exact hCh _
  have h := errBdd_finset_bdd (N := N) (B := B) (V := Ch) hB hCh0 hc _ hF
  simpa only [pinQC, mul_assoc] using h

/-- The `θθ` row (a constant) is bounded. -/
lemma errBdd_pinQD_bdd {v : E3 → ℝ} {μ : ℝ} {N : ℕ} {c : Lab N → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hc : ∀ k : Lab N, |c k| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖pinQD v μ N c‖ ≤ C := by
  obtain ⟨Ch, hCh0, hCh⟩ := errBdd_hatChi_bdd
  refine ⟨(Fintype.card (Lab N) : ℝ) * (B * Ch ^ 2),
    mul_nonneg (by positivity) (mul_nonneg hB (pow_nonneg hCh0 2)), ?_⟩
  have hF : ∀ k : Lab N, ‖(((Work.BoseK15.corpusBox.hatChi
      (ellH v μ • kmomLab (ellH v μ) N k) : ℝ) : ℂ)) ^ 2‖ ≤ Ch ^ 2 := by
    intro k
    simp only [norm_pow, errBdd_norm_ofReal]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCh _) 2
  have h := errBdd_finset_bdd (N := N) (B := B) (V := Ch ^ 2) hB (pow_nonneg hCh0 2) hc _ hF
  simpa only [pinQD] using h

theorem err_aesm_bdd {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWam : MeasureTheory.AEStronglyMeasurable Wa MeasureTheory.volume)
    (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C) (hWas : HasCompactSupport Wa)
    (hWbm : MeasureTheory.AEStronglyMeasurable Wb MeasureTheory.volume)
    (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C) (hWbs : HasCompactSupport Wb) :
    (MeasureTheory.AEStronglyMeasurable (Work.BoseBoxFock.k1ErrA v μ fu N Wa Wb) MeasureTheory.volume
        ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : EuclideanSpace ℝ (Fin 3),
            ‖z‖ ≤ Real.sqrt 3 * Work.BoseBoxFock.ellH v μ →
              ‖Work.BoseBoxFock.k1ErrA v μ fu N Wa Wb z‖ ≤ C)
    ∧ (MeasureTheory.AEStronglyMeasurable (Work.BoseBoxFock.k1ErrB v μ fu N Wa Wb) MeasureTheory.volume
        ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EuclideanSpace ℝ (Fin 3),
            ‖Work.BoseBoxFock.k1ErrB v μ fu N Wa Wb w‖ ≤ C)
    ∧ (MeasureTheory.AEStronglyMeasurable (Work.BoseBoxFock.k1ErrC v μ fu N Wa Wb) MeasureTheory.volume
        ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ y : EuclideanSpace ℝ (Fin 3),
            ‖Work.BoseBoxFock.k1ErrC v μ fu N Wa Wb y‖ ≤ C)
    ∧ (∃ C : ℝ, 0 ≤ C ∧ ‖Work.BoseBoxFock.k1ErrD v μ fu N Wa Wb‖ ≤ C) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨Ca, hCa⟩ := hWab
  obtain ⟨Cb, hCb⟩ := hWbb
  obtain ⟨Ra, hRa⟩ := k1ExistsRadius hWas
  obtain ⟨Rb, hRb⟩ := k1ExistsRadius hWbs
  obtain ⟨Ba, hBa0, hBa⟩ := chat_abs_le_uniform (W := Wa)
  obtain ⟨Bb, hBb0, hBb⟩ := chat_abs_le_uniform (W := Wb)
  -- the combined weight `Wa + Wb`
  have hsum_meas : AEStronglyMeasurable (Wa + Wb) volume := hWam.add hWbm
  have hsum_bdd : ∃ C : ℝ, ∀ x : E3, ‖(Wa + Wb) x‖ ≤ C := by
    refine ⟨Ca + Cb, fun x => ?_⟩
    have hx : (Wa + Wb) x = Wa x + Wb x := rfl
    rw [hx]
    exact le_trans (norm_add_le _ _) (add_le_add (hCa x) (hCb x))
  have hsum_supp : ∃ R : ℝ, ∀ x : E3, R < ‖x‖ → (Wa + Wb) x = 0 := by
    refine ⟨max Ra Rb, fun x hx => ?_⟩
    have h1 : Wa x = 0 := hRa x (lt_of_le_of_lt (le_max_left _ _) hx)
    have h2 : Wb x = 0 := hRb x (lt_of_le_of_lt (le_max_right _ _) hx)
    have hx' : (Wa + Wb) x = Wa x + Wb x := rfl
    rw [hx', h1, h2, add_zero]
  -- the coefficient bound `|k1cfun| ≤ Ba + Bb`
  have hcoef : ∀ k : Lab N, |k1cfun fu Wa Wb (ellH v μ) N k| ≤ Ba + Bb := by
    intro k
    have hu0 : 0 ≤ uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k) := by
      rw [uvCut]; exact fu.nonneg _
    have hu1 : uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k) ≤ 1 := by
      rw [uvCut]; exact fu.le_one _
    have hA : |uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
        * Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)| ≤ Ba := by
      rw [abs_mul, abs_of_nonneg hu0]
      calc uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
            * |Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)|
          ≤ 1 * Ba := mul_le_mul hu1 (hBa _) (abs_nonneg _) (by norm_num)
        _ = Ba := one_mul Ba
    calc |k1cfun fu Wa Wb (ellH v μ) N k|
        = |uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
            * Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)
            + Work.BoseFixR.chat Wb (kmomLab (ellH v μ) N k)| := rfl
      _ ≤ |uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
            * Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)|
            + |Work.BoseFixR.chat Wb (kmomLab (ellH v μ) N k)| := abs_add_le _ _
      _ ≤ Ba + Bb := add_le_add hA (hBb _)
  have hBnn : 0 ≤ Ba + Bb := add_nonneg hBa0 hBb0
  -- a.e. strong measurability of the four rows
  have hA_aesm : AEStronglyMeasurable (k1ErrA v μ fu N Wa Wb) volume := by
    have h1 : AEStronglyMeasurable
        (fun z : E3 => pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z) volume :=
      errBdd_pinQA_aesm _
    have h2 : AEStronglyMeasurable (fun z : E3 => latPer3 (ellH v μ) (Wa + Wb) z) volume :=
      errBdd_latPer3_aesm hsum_meas
    have h3 : AEStronglyMeasurable (fun z : E3 =>
        pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z
          - latPer3 (ellH v μ) (Wa + Wb) z) volume := by
      have h4 : AEStronglyMeasurable
          ((fun z : E3 => pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z)
            - (fun z : E3 => latPer3 (ellH v μ) (Wa + Wb) z)) volume := h1.sub h2
      rwa [errBdd_sub_apply_eq] at h4
    have hfun : (k1ErrA v μ fu N Wa Wb : E3 → ℂ) = fun z : E3 =>
        pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z
          - latPer3 (ellH v μ) (Wa + Wb) z := by
      funext z; rw [k1ErrA]
    rw [hfun]
    exact h3
  have hB_aesm : AEStronglyMeasurable (k1ErrB v μ fu N Wa Wb) volume := by
    have h1 : AEStronglyMeasurable
        (fun w : E3 => pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N) w) volume :=
      errBdd_pinQB_aesm _
    have h2 : AEStronglyMeasurable (fun w : E3 => pinQBl (ellH v μ) (Wa + Wb) w) volume :=
      errBdd_pinQBl_aesm
    have h3 : AEStronglyMeasurable (fun w : E3 =>
        pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N) w
          - pinQBl (ellH v μ) (Wa + Wb) w) volume := by
      have h4 : AEStronglyMeasurable
          ((fun w : E3 => pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N) w)
            - (fun w : E3 => pinQBl (ellH v μ) (Wa + Wb) w)) volume := h1.sub h2
      rwa [errBdd_sub_apply_eq] at h4
    have hfun : (k1ErrB v μ fu N Wa Wb : E3 → ℂ) = fun w : E3 =>
        pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N) w
          - pinQBl (ellH v μ) (Wa + Wb) w := by
      funext w; rw [k1ErrB]
    rw [hfun]
    exact h3
  have hC_aesm : AEStronglyMeasurable (k1ErrC v μ fu N Wa Wb) volume := by
    have h1 : AEStronglyMeasurable
        (fun y : E3 => pinQC v μ N (k1cfun fu Wa Wb (ellH v μ) N) y) volume :=
      errBdd_pinQC_aesm _
    have h2 : AEStronglyMeasurable (fun y : E3 => pinQCl (ellH v μ) (Wa + Wb) y) volume :=
      errBdd_pinQCl_aesm
    have h3 : AEStronglyMeasurable (fun y : E3 =>
        pinQC v μ N (k1cfun fu Wa Wb (ellH v μ) N) y
          - pinQCl (ellH v μ) (Wa + Wb) y) volume := by
      have h4 : AEStronglyMeasurable
          ((fun y : E3 => pinQC v μ N (k1cfun fu Wa Wb (ellH v μ) N) y)
            - (fun y : E3 => pinQCl (ellH v μ) (Wa + Wb) y)) volume := h1.sub h2
      rwa [errBdd_sub_apply_eq] at h4
    have hfun : (k1ErrC v μ fu N Wa Wb : E3 → ℂ) = fun y : E3 =>
        pinQC v μ N (k1cfun fu Wa Wb (ellH v μ) N) y
          - pinQCl (ellH v μ) (Wa + Wb) y := by
      funext y; rw [k1ErrC]
    rw [hfun]
    exact h3
  -- the bounds
  obtain ⟨CA, hCA0, hCAb⟩ := errBdd_pinQA_bdd (v := v) (μ := μ) (N := N)
    (c := k1cfun fu Wa Wb (ellH v μ) N) (B := Ba + Bb) hBnn hcoef
  obtain ⟨Rs, hRs⟩ := hsum_supp
  obtain ⟨DA, hDA0, hDA⟩ := errBdd_latPer3_bdd hℓ hsum_bdd hRs
  obtain ⟨CB1, hCB10, hCB1⟩ := errBdd_pinQB_bdd (v := v) (μ := μ) (N := N)
    (c := k1cfun fu Wa Wb (ellH v μ) N) (B := Ba + Bb) hBnn hcoef
  obtain ⟨CB2, hCB20, hCB2⟩ := errBdd_pinQBl_bdd hℓ (Wa + Wb)
  obtain ⟨CC1, hCC10, hCC1⟩ := errBdd_pinQC_bdd (v := v) (μ := μ) (N := N)
    (c := k1cfun fu Wa Wb (ellH v μ) N) (B := Ba + Bb) hBnn hcoef
  obtain ⟨CC2, hCC20, hCC2⟩ := errBdd_pinQCl_bdd hℓ (Wa + Wb)
  obtain ⟨CD1, hCD10, hCD1⟩ := errBdd_pinQD_bdd (v := v) (μ := μ) (N := N)
    (c := k1cfun fu Wa Wb (ellH v μ) N) (B := Ba + Bb) hBnn hcoef
  obtain ⟨CD2, hCD20, hCD2⟩ := errBdd_pinQDl_bdd hℓ (Wa + Wb)
  have hA_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, ‖z‖ ≤ Real.sqrt 3 * ellH v μ →
      ‖k1ErrA v μ fu N Wa Wb z‖ ≤ C := by
    refine ⟨CA + DA, add_nonneg hCA0 hDA0, fun z hz => ?_⟩
    calc ‖k1ErrA v μ fu N Wa Wb z‖
        = ‖pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z
            - latPer3 (ellH v μ) (Wa + Wb) z‖ := rfl
      _ ≤ ‖pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z‖
            + ‖latPer3 (ellH v μ) (Wa + Wb) z‖ := norm_sub_le _ _
      _ ≤ CA + DA := add_le_add (hCAb z) (hDA z hz)
  have hB_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : E3, ‖k1ErrB v μ fu N Wa Wb w‖ ≤ C := by
    refine ⟨CB1 + CB2, add_nonneg hCB10 hCB20, fun w => ?_⟩
    calc ‖k1ErrB v μ fu N Wa Wb w‖
        = ‖pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N) w
            - pinQBl (ellH v μ) (Wa + Wb) w‖ := rfl
      _ ≤ ‖pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N) w‖
            + ‖pinQBl (ellH v μ) (Wa + Wb) w‖ := norm_sub_le _ _
      _ ≤ CB1 + CB2 := add_le_add (hCB1 w) (hCB2 w)
  have hC_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E3, ‖k1ErrC v μ fu N Wa Wb y‖ ≤ C := by
    refine ⟨CC1 + CC2, add_nonneg hCC10 hCC20, fun y => ?_⟩
    calc ‖k1ErrC v μ fu N Wa Wb y‖
        = ‖pinQC v μ N (k1cfun fu Wa Wb (ellH v μ) N) y
            - pinQCl (ellH v μ) (Wa + Wb) y‖ := rfl
      _ ≤ ‖pinQC v μ N (k1cfun fu Wa Wb (ellH v μ) N) y‖
            + ‖pinQCl (ellH v μ) (Wa + Wb) y‖ := norm_sub_le _ _
      _ ≤ CC1 + CC2 := add_le_add (hCC1 y) (hCC2 y)
  have hD_bdd : ∃ C : ℝ, 0 ≤ C ∧ ‖k1ErrD v μ fu N Wa Wb‖ ≤ C := by
    refine ⟨CD1 + CD2, add_nonneg hCD10 hCD20, ?_⟩
    calc ‖k1ErrD v μ fu N Wa Wb‖
        = ‖pinQD v μ N (k1cfun fu Wa Wb (ellH v μ) N)
            - pinQDl (ellH v μ) (Wa + Wb)‖ := rfl
      _ ≤ ‖pinQD v μ N (k1cfun fu Wa Wb (ellH v μ) N)‖
            + ‖pinQDl (ellH v μ) (Wa + Wb)‖ := norm_sub_le _ _
      _ ≤ CD1 + CD2 := add_le_add hCD1 hCD2
  exact ⟨⟨hA_aesm, hA_bdd⟩, ⟨hB_aesm, hB_bdd⟩, ⟨hC_aesm, hC_bdd⟩, hD_bdd⟩

end

end Work.BoseBoxFock
