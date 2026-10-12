import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.MiddleU_eq_four_integral`

The **integral form** of the four-channel value of the `univ`-summed cubic middle kernel
`MiddleU` (`PCFU/MiddleU_eq_four`, PROVED).  The pointwise identity

    `MiddleU(x, y, u) = ℓ^{-9/2}·(ChAU(y,x,u) − ChBU(y,x,u) − ChCU(y,x,u) + ChDU(y,x,u))`

is integrated against the two-slot test function `Θ(x)·θ(x i)·Θ(x[i↦y][j↦u])`, giving

    `∫ Θ(x)θ(x i)MiddleU(x_j, y, u)Θ(x[i↦y][j↦u]) = ℓ^{-9/2}·(chAint − chBint − chCint + chDint)`,

where `chAint`, …, `chDint` are exactly the four channel integrals collected in
`PCFU/ChWordChains`.

The proof is the pointwise identity plus **linearity of the Bochner integral**: the four channel
integrands are measurable (products/finite sums of the continuous frames `Ksfr`, `KfrU`, `KχfrU`,
the bump `χ_Λ`, the indicator `θ_Λ`, the measurable state `Θ` and the parametrised integral
`∫_w χ_Λ(w)Ksfr(x+w)KfrU(u+w)`, which is measurable by
`StronglyMeasurable.integral_prod_right'`), uniformly bounded on the box-support, and supported in
the finite-measure set `abox n ℓ × (acube ℓ × acube ℓ)`; hence integrable
(`integrable_of_bounded_support`), and `integral_add`/`integral_sub` may be applied.

Everything here is `sorry`-free.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

open Work.BoseB4 Work.BoseBoxFock

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary one-particle facts -/

/-- `‖θ_Λ(z)‖ ≤ 1`. -/
private lemma norm_thetaFun_le' (ℓ : ℝ) (z : E3) :
    ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ ≤ 1 := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hz]

/-- `θ_Λ(z) ≠ 0` forces `z ∈ Λ(ℓ)`. -/
private lemma mem_boxL_of_thetaFun_ne_zero (ℓ : ℝ) (z : E3)
    (h : Work.BoseK15.corpusBox.thetaFun ℓ z ≠ 0) : z ∈ Work.BoseK15.corpusBox.boxL ℓ := by
  by_contra hz
  exact h (by rw [Work.BoseB4.BoxData.thetaFun_apply, if_neg hz])

/-- `θ_Λ(z) ≠ 0` forces `z ∈ acube ℓ`. -/
private lemma mem_acube_of_theta {ℓ : ℝ} (hℓ : 0 < ℓ) (z : E3)
    (h : Work.BoseK15.corpusBox.thetaFun ℓ z ≠ 0) : z ∈ Submission.BoseGases.acube ℓ := by
  rw [← corpusBox_boxL_eq_acube hℓ]
  exact mem_boxL_of_thetaFun_ne_zero ℓ z h

/-- `χ_Λ(z) ≠ 0` forces `z ∈ acube ℓ`. -/
private lemma mem_acube_of_chiLam_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3}
    (h : Work.BoseK15.corpusBox.chiLam ℓ z ≠ 0) : z ∈ Submission.BoseGases.acube ℓ := by
  rw [← corpusBox_boxL_eq_acube hℓ]
  exact Work.BoseB4.BoxData.chiLam_supp Work.BoseK15.corpusBox hℓ (Function.mem_support.mpr h)

/-- `w ↦ ‖χ_Λ(w)‖` is integrable (`χ_Λ` is continuous with compact support). -/
private lemma norm_chilam_integrable (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Integrable (fun w : E3 => ‖((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)‖) :=
  ((Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ ℓ)).integrable_of_hasCompactSupport
      (Work.BoseBoxFock.hasCompactSupport_chiLam_complex ℓ hℓ)).norm

/-! ## 2. Uniform bounds on the four channels -/

/-- The inner `w`-integral of the `(C)`-channel is uniformly bounded. -/
private lemma norm_innerCU_le (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x u : E3) :
    ‖∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * KfrU v h μ fu N (u + w)‖
      ≤ (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hχnorm : Integrable (fun w : E3 =>
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖) :=
    norm_chilam_integrable (ellH v μ) (ellH_pos v μ)
  have hA0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| :=
    Finset.sum_nonneg (fun s _ => abs_nonneg _)
  calc ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Ksfr v fc μ N (x + w) * KfrU v h μ fu N (u + w)‖
      ≤ ∫ w : E3, (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k|)
          * ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _)
          (hχnorm.const_mul ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
            * (∑ k : Lab N, |W1h v h μ fu N k|)))
          (Filter.Eventually.of_forall fun w => ?_)
        beta_reduce
        rw [norm_mul, norm_mul]
        have h1 : ‖Ksfr v fc μ N (x + w)‖
            ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| := norm_Ksfr_le (x + w)
        have h2 : ‖KfrU v h μ fu N (u + w)‖ ≤ ∑ k : Lab N, |W1h v h μ fu N k| :=
          norm_KfrU_le v h μ fu N (u + w)
        have hAB : ‖Ksfr v fc μ N (x + w)‖ * ‖KfrU v h μ fu N (u + w)‖
            ≤ (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
              * (∑ k : Lab N, |W1h v h μ fu N k|) :=
          mul_le_mul h1 h2 (norm_nonneg _) hA0
        calc ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * ‖Ksfr v fc μ N (x + w)‖ * ‖KfrU v h μ fu N (u + w)‖
            = ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * (‖Ksfr v fc μ N (x + w)‖ * ‖KfrU v h μ fu N (u + w)‖) := by ring
          _ ≤ ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
                * (∑ k : Lab N, |W1h v h μ fu N k|)) :=
              mul_le_mul_of_nonneg_left hAB (norm_nonneg _)
          _ = (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
              * (∑ k : Lab N, |W1h v h μ fu N k|)
              * ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by ring
    _ = (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
        rw [MeasureTheory.integral_const_mul]

/-- The inner `w`-integral of the `(D)`-channel is uniformly bounded. -/
private lemma norm_innerDU_le (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x : E3) :
    ‖∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * KχfrU v h μ fu N w‖
      ≤ (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hχnorm : Integrable (fun w : E3 =>
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖) :=
    norm_chilam_integrable (ellH v μ) (ellH_pos v μ)
  have hA0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| :=
    Finset.sum_nonneg (fun s _ => abs_nonneg _)
  calc ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Ksfr v fc μ N (x + w) * KχfrU v h μ fu N w‖
      ≤ ∫ w : E3, (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)
          * ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _)
          (hχnorm.const_mul ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
            * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)))
          (Filter.Eventually.of_forall fun w => ?_)
        beta_reduce
        rw [norm_mul, norm_mul]
        have h1 : ‖Ksfr v fc μ N (x + w)‖
            ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| := norm_Ksfr_le (x + w)
        have h2 : ‖KχfrU v h μ fu N w‖
            ≤ ∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k| :=
          norm_KχfrU_le v h μ fu N w
        have hAB : ‖Ksfr v fc μ N (x + w)‖ * ‖KχfrU v h μ fu N w‖
            ≤ (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
              * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|) :=
          mul_le_mul h1 h2 (norm_nonneg _) hA0
        calc ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * ‖Ksfr v fc μ N (x + w)‖ * ‖KχfrU v h μ fu N w‖
            = ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * (‖Ksfr v fc μ N (x + w)‖ * ‖KχfrU v h μ fu N w‖) := by ring
          _ ≤ ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖
              * ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
                * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)) :=
              mul_le_mul_of_nonneg_left hAB (norm_nonneg _)
          _ = (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
              * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)
              * ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by ring
    _ = (∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ := by
        rw [MeasureTheory.integral_const_mul]

/-- The `(A)`-channel is uniformly bounded on `E³ × E³ × E³`. -/
private lemma exists_norm_ChAU_le (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ y x u : E3, ‖ChAU v h fc fu μ N y x u‖ ≤ C := by
  refine ⟨(∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
      * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * 1
      * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
      * (∑ k : Lab N, |W1h v h μ fu N k|), fun y x u => ?_⟩
  rw [ChAU, norm_mul, norm_mul, norm_mul, norm_mul]
  gcongr
  · exact norm_Ksfr_le (x - y)
  · exact norm_chiLam_le (ellH v μ) y
  · exact norm_thetaFun_le' (ellH v μ) x
  · exact norm_chiLam_le (ellH v μ) u
  · exact norm_KfrU_le v h μ fu N (y - u)

/-- The `(B)`-channel is uniformly bounded on `E³ × E³ × E³`. -/
private lemma exists_norm_ChBU_le (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ y x u : E3, ‖ChBU v h fc fu μ N y x u‖ ≤ C := by
  refine ⟨(∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
      * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * 1 * 1
      * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|), fun y x u => ?_⟩
  rw [ChBU, norm_mul, norm_mul, norm_mul, norm_mul]
  gcongr
  · exact norm_Ksfr_le (x - y)
  · exact norm_chiLam_le (ellH v μ) y
  · exact norm_thetaFun_le' (ellH v μ) x
  · exact norm_thetaFun_le' (ellH v μ) u
  · exact norm_KχfrU_le v h μ fu N y

/-- The `(C)`-channel is uniformly bounded on `E³ × E³ × E³`. -/
private lemma exists_norm_ChCU_le (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ y x u : E3, ‖ChCU v h fc fu μ N y x u‖ ≤ C := by
  refine ⟨1 * 1 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
      * |(ellH v μ) ^ (-(3 : ℤ))|
      * ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖),
    fun y x u => ?_⟩
  rw [ChCU, norm_mul, norm_mul, norm_mul, norm_mul]
  have hA0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| :=
    Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hI0 : 0 ≤ ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ :=
    integral_nonneg (fun w => norm_nonneg _)
  gcongr
  · exact norm_thetaFun_le' (ellH v μ) y
  · exact norm_thetaFun_le' (ellH v μ) x
  · exact norm_chiLam_le (ellH v μ) u
  · exact le_of_eq (RCLike.norm_ofReal _)
  · exact norm_innerCU_le v h fc fu μ N x u

/-- The `(D)`-channel is uniformly bounded on `E³ × E³ × E³`. -/
private lemma exists_norm_ChDU_le (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ y x u : E3, ‖ChDU v h fc fu μ N y x u‖ ≤ C := by
  refine ⟨1 * 1 * 1 * |(ellH v μ) ^ (-(3 : ℤ))|
      * ((∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s|)
          * (∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|)
          * ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖),
    fun y x u => ?_⟩
  rw [ChDU, norm_mul, norm_mul, norm_mul, norm_mul]
  have hA0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab N), |fLh v fc μ N s| :=
    Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hI0 : 0 ≤ ∫ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)‖ :=
    integral_nonneg (fun w => norm_nonneg _)
  gcongr
  · exact norm_thetaFun_le' (ellH v μ) y
  · exact norm_thetaFun_le' (ellH v μ) x
  · exact norm_thetaFun_le' (ellH v μ) u
  · exact le_of_eq (RCLike.norm_ofReal _)
  · exact norm_innerDU_le v h fc fu μ N x

/-! ## 3. Measurability of the four channels -/

/-- Measurability of the two-slot update map. -/
private lemma measurable_update₂ {n : ℕ} (i j : Fin n) :
    Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      Function.update (Function.update q.1 i q.2.1) j q.2.2) := by
  refine measurable_pi_iff.mpr (fun m => ?_)
  have hfun : (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      Function.update (Function.update q.1 i q.2.1) j q.2.2 m)
      = fun q => if m = j then q.2.2 else if m = i then q.2.1 else q.1 m := by
    funext q
    rw [Function.update_apply, Function.update_apply]
  rw [hfun]
  by_cases hmj : m = j
  · rw [show (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        if m = j then q.2.2 else if m = i then q.2.1 else q.1 m) = fun q => q.2.2 from by
      funext q; rw [if_pos hmj]]
    exact measurable_snd.snd
  · rw [show (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        if m = j then q.2.2 else if m = i then q.2.1 else q.1 m)
        = fun q => if m = i then q.2.1 else q.1 m from by funext q; rw [if_neg hmj]]
    by_cases hmi : m = i
    · rw [show (fun q : Submission.BoseGases.X n × (E3 × E3) =>
          if m = i then q.2.1 else q.1 m) = fun q => q.2.1 from by funext q; rw [if_pos hmi]]
      exact measurable_snd.fst
    · rw [show (fun q : Submission.BoseGases.X n × (E3 × E3) =>
          if m = i then q.2.1 else q.1 m) = fun q => q.1 m from by funext q; rw [if_neg hmi]]
      exact (measurable_pi_apply m).comp measurable_fst

private lemma measurable_ChAU_local {n : ℕ} {j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ChAU v h fc fu μ N q.2.1 (q.1 j) q.2.2) := by
  have hKs : Measurable (fun z : E3 => Ksfr v fc μ N z) := continuous_Ksfr.measurable
  have hKf : Measurable (fun z : E3 => KfrU v h μ fu N z) := (continuous_KfrU v h μ fu N).measurable
  have hχ : Measurable (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ _)).measurable
  have hθ : Measurable (fun z : E3 => Work.BoseK15.corpusBox.thetaFun (ellH v μ) z) :=
    measurable_thetaFun (ellH_pos v μ)
  unfold ChAU
  refine Measurable.mul ?_ ?_
  · refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ ?_
      · refine Measurable.mul ?_ ?_
        · exact hKs.comp (by fun_prop)
        · exact hχ.comp (by fun_prop)
      · exact hθ.comp (by fun_prop)
    · exact hχ.comp (by fun_prop)
  · exact hKf.comp (by fun_prop)

private lemma measurable_ChBU_local {n : ℕ} {j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2) := by
  have hKs : Measurable (fun z : E3 => Ksfr v fc μ N z) := continuous_Ksfr.measurable
  have hKf : Measurable (fun z : E3 => KχfrU v h μ fu N z) := (continuous_KχfrU v h μ fu N).measurable
  have hχ : Measurable (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ _)).measurable
  have hθ : Measurable (fun z : E3 => Work.BoseK15.corpusBox.thetaFun (ellH v μ) z) :=
    measurable_thetaFun (ellH_pos v μ)
  unfold ChBU
  refine Measurable.mul ?_ ?_
  · refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ ?_
      · refine Measurable.mul ?_ ?_
        · exact hKs.comp (by fun_prop)
        · exact hχ.comp (by fun_prop)
      · exact hθ.comp (by fun_prop)
    · exact hθ.comp (by fun_prop)
  · exact hKf.comp (by fun_prop)

private lemma measurable_ChCU_local {n : ℕ} {j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2) := by
  have hKs : Continuous (fun z : E3 => Ksfr v fc μ N z) := continuous_Ksfr
  have hKf : Continuous (fun z : E3 => KfrU v h μ fu N z) := continuous_KfrU v h μ fu N
  have hχ : Continuous (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ _)
  have hθ : Measurable (fun z : E3 => Work.BoseK15.corpusBox.thetaFun (ellH v μ) z) :=
    measurable_thetaFun (ellH_pos v μ)
  have hF : Continuous (fun z : (Submission.BoseGases.X n × (E3 × E3)) × E3 =>
      (Work.BoseK15.corpusBox.chiLam (ellH v μ) z.2 : ℂ) * Ksfr v fc μ N (z.1.1 j + z.2)
        * KfrU v h μ fu N (z.1.2.2 + z.2)) := by
    refine Continuous.mul ?_ ?_
    · refine Continuous.mul ?_ ?_
      · exact hχ.comp (by fun_prop : Continuous
          (fun z : (Submission.BoseGases.X n × (E3 × E3)) × E3 => z.2))
      · exact hKs.comp (by fun_prop)
    · exact hKf.comp (by fun_prop)
  have hint : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) => ∫ w : E3,
      (Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℂ) * Ksfr v fc μ N (q.1 j + w)
        * KfrU v h μ fu N (q.2.2 + w)) :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))).measurable
  unfold ChCU
  refine Measurable.mul ?_ ?_
  · refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ ?_
      · refine Measurable.mul ?_ ?_
        · exact hθ.comp (by fun_prop)
        · exact hθ.comp (by fun_prop)
      · exact hχ.measurable.comp (by fun_prop)
    · exact measurable_const
  · exact hint

private lemma measurable_ChDU_local {n : ℕ} {j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ChDU v h fc fu μ N q.2.1 (q.1 j) q.2.2) := by
  have hKs : Continuous (fun z : E3 => Ksfr v fc μ N z) := continuous_Ksfr
  have hKf : Continuous (fun z : E3 => KχfrU v h μ fu N z) := continuous_KχfrU v h μ fu N
  have hχ : Continuous (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ _)
  have hθ : Measurable (fun z : E3 => Work.BoseK15.corpusBox.thetaFun (ellH v μ) z) :=
    measurable_thetaFun (ellH_pos v μ)
  have hF : Continuous (fun z : (Submission.BoseGases.X n × (E3 × E3)) × E3 =>
      (Work.BoseK15.corpusBox.chiLam (ellH v μ) z.2 : ℂ) * Ksfr v fc μ N (z.1.1 j + z.2)
        * KχfrU v h μ fu N z.2) := by
    refine Continuous.mul ?_ ?_
    · refine Continuous.mul ?_ ?_
      · exact hχ.comp (by fun_prop : Continuous
          (fun z : (Submission.BoseGases.X n × (E3 × E3)) × E3 => z.2))
      · exact hKs.comp (by fun_prop)
    · exact hKf.comp (by fun_prop : Continuous
        (fun z : (Submission.BoseGases.X n × (E3 × E3)) × E3 => z.2))
  have hint : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) => ∫ w : E3,
      (Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℂ) * Ksfr v fc μ N (q.1 j + w)
        * KχfrU v h μ fu N w) :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))).measurable
  unfold ChDU
  refine Measurable.mul ?_ ?_
  · refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ ?_
      · refine Measurable.mul ?_ ?_
        · exact hθ.comp (by fun_prop)
        · exact hθ.comp (by fun_prop)
      · exact hθ.comp (by fun_prop)
    · exact measurable_const
  · exact hint


/-! ## 4. The four channel integrands -/

/-- The `(A)`-channel integrand (the integrand of `chAint`). -/
private def intA {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) : Submission.BoseGases.X n × (E3 × E3) → ℂ :=
  fun q => ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChAU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

/-- The `(B)`-channel integrand (the integrand of `chBint`). -/
private def intB {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) : Submission.BoseGases.X n × (E3 × E3) → ℂ :=
  fun q => ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

/-- The `(C)`-channel integrand (the integrand of `chCint`). -/
private def intC {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) : Submission.BoseGases.X n × (E3 × E3) → ℂ :=
  fun q => ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

/-- The `(D)`-channel integrand (the integrand of `chDint`). -/
private def intD {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) : Submission.BoseGases.X n × (E3 × E3) → ℂ :=
  fun q => ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChDU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

private lemma chAint_eq_intA {n : ℕ} {i j : Fin n} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ) :
    (∫ q : Submission.BoseGases.X n × (E3 × E3), intA v h fc fu μ N i j Θ q)
      = chAint v h fc fu μ N i j Θ := rfl

private lemma chBint_eq_intB {n : ℕ} {i j : Fin n} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ) :
    (∫ q : Submission.BoseGases.X n × (E3 × E3), intB v h fc fu μ N i j Θ q)
      = chBint v h fc fu μ N i j Θ := rfl

private lemma chCint_eq_intC {n : ℕ} {i j : Fin n} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ) :
    (∫ q : Submission.BoseGases.X n × (E3 × E3), intC v h fc fu μ N i j Θ q)
      = chCint v h fc fu μ N i j Θ := rfl

private lemma chDint_eq_intD {n : ℕ} {i j : Fin n} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ) :
    (∫ q : Submission.BoseGases.X n × (E3 × E3), intD v h fc fu μ N i j Θ q)
      = chDint v h fc fu μ N i j Θ := rfl

/-! ## 5. The box of finite measure and support containment -/

/-- The finite-measure set carrying all four channel integrands. -/
private def suppSet {n : ℕ} (ℓ : ℝ) : Set (Submission.BoseGases.X n × (E3 × E3)) :=
  Submission.BoseGases.abox n ℓ ×ˢ (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)

private lemma suppSet_lt_top {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume : Measure (Submission.BoseGases.X n × (E3 × E3))) (suppSet (n := n) ℓ) < ⊤ := by
  rw [suppSet]
  change ((volume : Measure (Submission.BoseGases.X n)).prod
    ((volume : Measure E3).prod (volume : Measure E3)))
    (Submission.BoseGases.abox n ℓ ×ˢ (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ))
    < ⊤
  rw [Measure.prod_prod, Measure.prod_prod,
    Submission.BoseGases.abox_volume n ℓ (le_of_lt hℓ),
    Submission.BoseGases.acube_volume ℓ (le_of_lt hℓ)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

private lemma support_intA {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    Function.support (intA v h fc fu μ N i j Θ) ⊆ suppSet (n := n) (ellH v μ) := by
  intro q hq
  rw [Function.mem_support] at hq
  simp only [suppSet, Set.mem_prod]
  have hθ1 : Θ q.1 ≠ 0 := by
    intro h0
    exact hq (by rw [intA, h0]; simp)
  have hA : ChAU v h fc fu μ N q.2.1 (q.1 j) q.2.2 ≠ 0 := by
    intro h0
    exact hq (by rw [intA, h0]; ring)
  have hχ1c : ((Work.BoseK15.corpusBox.chiLam (ellH v μ) q.2.1 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    exact hA (by rw [ChAU, h0]; ring)
  have hχ2c : ((Work.BoseK15.corpusBox.chiLam (ellH v μ) q.2.2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    exact hA (by rw [ChAU, h0]; ring)
  have hχ1 : Work.BoseK15.corpusBox.chiLam (ellH v μ) q.2.1 ≠ 0 := by
    intro h0; exact hχ1c (by rw [h0]; simp)
  have hχ2 : Work.BoseK15.corpusBox.chiLam (ellH v μ) q.2.2 ≠ 0 := by
    intro h0; exact hχ2c (by rw [h0]; simp)
  exact ⟨hΘs (Function.mem_support.mpr hθ1),
    mem_acube_of_chiLam_ne_zero (ellH_pos v μ) hχ1,
    mem_acube_of_chiLam_ne_zero (ellH_pos v μ) hχ2⟩

private lemma support_intB {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    Function.support (intB v h fc fu μ N i j Θ) ⊆ suppSet (n := n) (ellH v μ) := by
  intro q hq
  rw [Function.mem_support] at hq
  simp only [suppSet, Set.mem_prod]
  have hθ1 : Θ q.1 ≠ 0 := by
    intro h0
    exact hq (by rw [intB, h0]; simp)
  have hB : ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2 ≠ 0 := by
    intro h0
    exact hq (by rw [intB, h0]; ring)
  have hχ1c : ((Work.BoseK15.corpusBox.chiLam (ellH v μ) q.2.1 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    exact hB (by rw [ChBU, h0]; ring)
  have hθ2 : Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.2 ≠ 0 := by
    intro h0
    exact hB (by rw [ChBU, h0]; ring)
  have hχ1 : Work.BoseK15.corpusBox.chiLam (ellH v μ) q.2.1 ≠ 0 := by
    intro h0; exact hχ1c (by rw [h0]; simp)
  exact ⟨hΘs (Function.mem_support.mpr hθ1),
    mem_acube_of_chiLam_ne_zero (ellH_pos v μ) hχ1,
    mem_acube_of_theta (ellH_pos v μ) q.2.2 hθ2⟩

private lemma support_intC {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    Function.support (intC v h fc fu μ N i j Θ) ⊆ suppSet (n := n) (ellH v μ) := by
  intro q hq
  rw [Function.mem_support] at hq
  simp only [suppSet, Set.mem_prod]
  have hθ1 : Θ q.1 ≠ 0 := by
    intro h0
    exact hq (by rw [intC, h0]; simp)
  have hC : ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2 ≠ 0 := by
    intro h0
    exact hq (by rw [intC, h0]; ring)
  have hθy : Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.1 ≠ 0 := by
    intro h0
    exact hC (by rw [ChCU, h0]; ring)
  have hχ2c : ((Work.BoseK15.corpusBox.chiLam (ellH v μ) q.2.2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    exact hC (by rw [ChCU, h0]; ring)
  have hχ2 : Work.BoseK15.corpusBox.chiLam (ellH v μ) q.2.2 ≠ 0 := by
    intro h0; exact hχ2c (by rw [h0]; simp)
  exact ⟨hΘs (Function.mem_support.mpr hθ1),
    mem_acube_of_theta (ellH_pos v μ) q.2.1 hθy,
    mem_acube_of_chiLam_ne_zero (ellH_pos v μ) hχ2⟩

private lemma support_intD {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    Function.support (intD v h fc fu μ N i j Θ) ⊆ suppSet (n := n) (ellH v μ) := by
  intro q hq
  rw [Function.mem_support] at hq
  simp only [suppSet, Set.mem_prod]
  have hθ1 : Θ q.1 ≠ 0 := by
    intro h0
    exact hq (by rw [intD, h0]; simp)
  have hD : ChDU v h fc fu μ N q.2.1 (q.1 j) q.2.2 ≠ 0 := by
    intro h0
    exact hq (by rw [intD, h0]; ring)
  have hθy : Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.1 ≠ 0 := by
    intro h0
    exact hD (by rw [ChDU, h0]; ring)
  have hθu : Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.2 ≠ 0 := by
    intro h0
    exact hD (by rw [ChDU, h0]; ring)
  exact ⟨hΘs (Function.mem_support.mpr hθ1),
    mem_acube_of_theta (ellH_pos v μ) q.2.1 hθy,
    mem_acube_of_theta (ellH_pos v μ) q.2.2 hθu⟩

/-! ## 6. Integrability of the four channel integrands -/

private lemma measurable_intA {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ) :
    Measurable (intA v h fc fu μ N i j Θ) := by
  have h1 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ q.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hΘm.comp measurable_fst)
  have h2 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)) :=
    (measurable_thetaFun (ellH_pos v μ)).comp
      ((measurable_pi_apply i).comp measurable_fst)
  have h3 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ChAU v h fc fu μ N q.2.1 (q.1 j) q.2.2) :=
    measurable_ChAU_local v h fc fu μ N
  have h4 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hΘm.comp (measurable_update₂ i j))
  show Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChAU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
  exact ((h1.mul h2).mul h3).mul h4

private lemma measurable_intB {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ) :
    Measurable (intB v h fc fu μ N i j Θ) := by
  have h1 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ q.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hΘm.comp measurable_fst)
  have h2 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)) :=
    (measurable_thetaFun (ellH_pos v μ)).comp
      ((measurable_pi_apply i).comp measurable_fst)
  have h3 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2) :=
    measurable_ChBU_local v h fc fu μ N
  have h4 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hΘm.comp (measurable_update₂ i j))
  show Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
  exact ((h1.mul h2).mul h3).mul h4

private lemma measurable_intC {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ) :
    Measurable (intC v h fc fu μ N i j Θ) := by
  have h1 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ q.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hΘm.comp measurable_fst)
  have h2 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)) :=
    (measurable_thetaFun (ellH_pos v μ)).comp
      ((measurable_pi_apply i).comp measurable_fst)
  have h3 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2) :=
    measurable_ChCU_local v h fc fu μ N
  have h4 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hΘm.comp (measurable_update₂ i j))
  show Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
  exact ((h1.mul h2).mul h3).mul h4

private lemma measurable_intD {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ) :
    Measurable (intD v h fc fu μ N i j Θ) := by
  have h1 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ q.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hΘm.comp measurable_fst)
  have h2 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)) :=
    (measurable_thetaFun (ellH_pos v μ)).comp
      ((measurable_pi_apply i).comp measurable_fst)
  have h3 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ChDU v h fc fu μ N q.2.1 (q.1 j) q.2.2) :=
    measurable_ChDU_local v h fc fu μ N
  have h4 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hΘm.comp (measurable_update₂ i j))
  show Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChDU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
  exact ((h1.mul h2).mul h3).mul h4

/-- Common shape of the four channel bounds. -/
private lemma bound_int_of_bound_Ch {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (Ch : E3 → E3 → E3 → ℂ) (hCh : ∃ C : ℝ, ∀ y x u, ‖Ch y x u‖ ≤ C)
    (f : Submission.BoseGases.X n × (E3 × E3) → ℂ)
    (hf : f = fun q => ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * Ch q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)) :
    ∃ C : ℝ, ∀ q, ‖f q‖ ≤ C := by
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  obtain ⟨CA, hCA⟩ := hCh
  have hCΘ0 : 0 ≤ CΘ := le_trans (abs_nonneg (Θ 0)) (hCΘ 0)
  have hCA0 : 0 ≤ CA := le_trans (norm_nonneg (Ch 0 0 0)) (hCA 0 0 0)
  refine ⟨CΘ * 1 * CA * CΘ, fun q => ?_⟩
  rw [hf]
  rw [norm_mul, norm_mul, norm_mul]
  have h1 : ‖((Θ q.1 : ℝ) : ℂ)‖ ≤ CΘ :=
    le_trans (le_of_eq (RCLike.norm_ofReal (Θ q.1))) (hCΘ q.1)
  have h2 : ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)‖ ≤ 1 :=
    norm_thetaFun_le' (ellH v μ) (q.1 i)
  have h3 : ‖Ch q.2.1 (q.1 j) q.2.2‖ ≤ CA := hCA _ _ _
  have h4 : ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖ ≤ CΘ :=
    le_trans (le_of_eq (RCLike.norm_ofReal (Θ _))) (hCΘ _)
  have h12 : ‖((Θ q.1 : ℝ) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)‖
      ≤ CΘ * 1 := mul_le_mul h1 h2 (norm_nonneg _) hCΘ0
  have h34 : ‖Ch q.2.1 (q.1 j) q.2.2‖
      * ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖ ≤ CA * CΘ :=
    mul_le_mul h3 h4 (norm_nonneg _) hCA0
  calc ‖((Θ q.1 : ℝ) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)‖
        * ‖Ch q.2.1 (q.1 j) q.2.2‖
        * ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖
      = (‖((Θ q.1 : ℝ) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)‖)
        * (‖Ch q.2.1 (q.1 j) q.2.2‖
          * ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖) := by ring
    _ ≤ (CΘ * 1) * (CA * CΘ) := mul_le_mul h12 h34 (by positivity) (by positivity)
    _ = CΘ * 1 * CA * CΘ := by ring

private lemma norm_intA_le {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C) :
    ∃ C : ℝ, ∀ q, ‖intA v h fc fu μ N i j Θ q‖ ≤ C :=
  bound_int_of_bound_Ch v h fc fu μ N Θ hΘb (ChAU v h fc fu μ N) (exists_norm_ChAU_le v h fc fu μ N)
    _ rfl

private lemma norm_intB_le {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C) :
    ∃ C : ℝ, ∀ q, ‖intB v h fc fu μ N i j Θ q‖ ≤ C :=
  bound_int_of_bound_Ch v h fc fu μ N Θ hΘb (ChBU v h fc fu μ N) (exists_norm_ChBU_le v h fc fu μ N)
    _ rfl

private lemma norm_intC_le {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C) :
    ∃ C : ℝ, ∀ q, ‖intC v h fc fu μ N i j Θ q‖ ≤ C :=
  bound_int_of_bound_Ch v h fc fu μ N Θ hΘb (ChCU v h fc fu μ N) (exists_norm_ChCU_le v h fc fu μ N)
    _ rfl

private lemma norm_intD_le {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C) :
    ∃ C : ℝ, ∀ q, ‖intD v h fc fu μ N i j Θ q‖ ≤ C :=
  bound_int_of_bound_Ch v h fc fu μ N Θ hΘb (ChDU v h fc fu μ N) (exists_norm_ChDU_le v h fc fu μ N)
    _ rfl

private lemma integrable_intA {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    Integrable (intA v h fc fu μ N i j Θ) := by
  obtain ⟨C, hC⟩ := norm_intA_le v h fc fu μ N Θ hΘb
  refine integrable_of_bounded_support (suppSet_lt_top (n := n) (ellH_pos v μ))
    (measurable_intA v h fc fu μ N Θ hΘm) hC (fun q hq => ?_)
  by_contra hx
  exact hq (support_intA v h fc fu μ N Θ hΘs (Function.mem_support.mpr hx))

private lemma integrable_intB {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    Integrable (intB v h fc fu μ N i j Θ) := by
  obtain ⟨C, hC⟩ := norm_intB_le v h fc fu μ N Θ hΘb
  refine integrable_of_bounded_support (suppSet_lt_top (n := n) (ellH_pos v μ))
    (measurable_intB v h fc fu μ N Θ hΘm) hC (fun q hq => ?_)
  by_contra hx
  exact hq (support_intB v h fc fu μ N Θ hΘs (Function.mem_support.mpr hx))

private lemma integrable_intC {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    Integrable (intC v h fc fu μ N i j Θ) := by
  obtain ⟨C, hC⟩ := norm_intC_le v h fc fu μ N Θ hΘb
  refine integrable_of_bounded_support (suppSet_lt_top (n := n) (ellH_pos v μ))
    (measurable_intC v h fc fu μ N Θ hΘm) hC (fun q hq => ?_)
  by_contra hx
  exact hq (support_intC v h fc fu μ N Θ hΘs (Function.mem_support.mpr hx))

private lemma integrable_intD {n : ℕ} {i j : Fin n}
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    Integrable (intD v h fc fu μ N i j Θ) := by
  obtain ⟨C, hC⟩ := norm_intD_le v h fc fu μ N Θ hΘb
  refine integrable_of_bounded_support (suppSet_lt_top (n := n) (ellH_pos v μ))
    (measurable_intD v h fc fu μ N Θ hΘm) hC (fun q hq => ?_)
  by_contra hx
  exact hq (support_intD v h fc fu μ N Θ hΘs (Function.mem_support.mpr hx))

theorem MiddleU_eq_four_integral {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hsub : ∀ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      Work.BoseBoxFock.fLh v fc μ N s ≠ 0 →
      ∀ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        Work.BoseBoxFock.W1h v h μ fu N k ≠ 0 →
      Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N (s - k)
        = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s
          - Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = (((Work.BoseBoxFock.ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ)
          * (Work.BoseBoxFock.PCFU.chAint v h fc fu μ N i j Θ
              - Work.BoseBoxFock.PCFU.chBint v h fc fu μ N i j Θ
              - Work.BoseBoxFock.PCFU.chCint v h fc fu μ N i j Θ
              + Work.BoseBoxFock.PCFU.chDint v h fc fu μ N i j Θ) := by
  classical
  -- ## integrability of the four channel integrands
  have hIA := integrable_intA (i := i) (j := j) v h fc fu μ N Θ hΘm hΘb hΘs
  have hIB := integrable_intB (i := i) (j := j) v h fc fu μ N Θ hΘm hΘb hΘs
  have hIC := integrable_intC (i := i) (j := j) v h fc fu μ N Θ hΘm hΘb hΘs
  have hID := integrable_intD (i := i) (j := j) v h fc fu μ N Θ hΘm hΘb hΘs
  have hIAB : Integrable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      intA v h fc fu μ N i j Θ q - intB v h fc fu μ N i j Θ q) := hIA.sub hIB
  have hIABC : Integrable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      intA v h fc fu μ N i j Θ q - intB v h fc fu μ N i j Θ q
        - intC v h fc fu μ N i j Θ q) := hIAB.sub hIC
  -- ## the pointwise four-channel identity
  have hpt : ∀ q : Submission.BoseGases.X n × (E3 × E3),
      ((Θ q.1 : ℝ) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
        * MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
        * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
      = ((ellH v μ ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ) *
        (intA v h fc fu μ N i j Θ q - intB v h fc fu μ N i j Θ q
          - intC v h fc fu μ N i j Θ q + intD v h fc fu μ N i j Θ q) := by
    intro q
    rw [MiddleU_eq_four v h fc fu μ N (q.1 j) q.2.1 q.2.2 hsub]
    simp only [intA, intB, intC, intD]
    ring
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall hpt)) ?_
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [integral_add hIABC hID, integral_sub hIAB hIC, integral_sub hIA hIB,
    chAint_eq_intA, chBint_eq_intB, chCint_eq_intC, chDint_eq_intD]

end Work.BoseBoxFock.PCFU
