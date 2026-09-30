import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.wt_defs
import Submission.Work.BMF.wt_lem
import Submission.Work.BMF.wt_aux
import Submission.Work.BMF.wt_num

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Finset Real Complex MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace
open BoundedMultiplicativeFunctions

namespace Work.BMF

/-! ## Elementary facts about the character `eC` -/

lemma continuous_eC : Continuous eC := by
  unfold eC; fun_prop

lemma norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  rw [Complex.norm_exp]
  simp

private lemma eC_add (u v : ℝ) : eC (u + v) = eC u * eC v := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma poly_eval_shift (P : ℝ[X]) (θ x : ℝ) :
    (P + Polynomial.C θ * Polynomial.X).eval x = P.eval x + θ * x := by
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

lemma eC_shift (P : ℝ[X]) (θ x : ℝ) :
    eC (-((P + Polynomial.C θ * Polynomial.X).eval x))
      = eC (-(P.eval x)) * eC (x * (-θ)) := by
  rw [poly_eval_shift]
  have h : -(P.eval x + θ * x) = -(P.eval x) + x * (-θ) := by ring
  rw [h, eC_add]

lemma Kphi_nonneg : 0 ≤ Kphi := by
  rw [Kphi]; exact integral_nonneg (fun x => abs_nonneg _)

/-! ## Two reusable estimates -/

/-- The Fourier upper bound. -/
lemma fourier_upper_bound (B af cf Ξ cη H : ℝ) (hB : 0 < B) (hac : af ≤ cf) (hΞ : 0 ≤ Ξ)
    (hcη : 0 ≤ cη)
    (b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ 1) (A0 B0 : ℕ)
    (hcard : ((Finset.Icc A0 B0).card : ℝ) ≤ H + 1)
    (hFS : ∀ ξ : ℝ, |ξ| ≤ Ξ → ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖ < cη) :
    ‖∫ ξ, FT (Wt B af cf) ξ * (∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ))‖
      ≤ cη * (∫ ξ in Set.Icc (-Ξ) Ξ, ‖FT (Wt B af cf) ξ‖)
        + (H + 1) * (∫ ξ in {ξ : ℝ | Ξ < |ξ|}, ‖FT (Wt B af cf) ξ‖) := by
  have hFSb : ∀ ξ : ℝ, ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖ ≤ H + 1 := by
    intro ξ
    have h1 : ∀ n : ℕ, ‖b n * eC (n * ξ)‖ ≤ 1 := by
      intro n
      rw [norm_mul, norm_eC, mul_one]
      exact hb n
    calc ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖
        ≤ ∑ n ∈ Finset.Icc A0 B0, ‖b n * eC (n * ξ)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Icc A0 B0, (1 : ℝ) := Finset.sum_le_sum (fun n _ => h1 n)
      _ = ((Finset.Icc A0 B0).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ H + 1 := hcard
  have hFScont : Continuous (fun ξ : ℝ => ∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)) := by
    refine continuous_finset_sum _ (fun n _ => ?_)
    exact (continuous_eC.comp (continuous_const.mul continuous_id)).const_mul (b n)
  have hGint : Integrable (fun ξ : ℝ =>
      ‖FT (Wt B af cf) ξ‖ * ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖) := by
    refine ((integrable_FT_Wt B af cf hB hac).norm.mul_const (H + 1)).mono'
      (((stronglyMeasurable_FT (Wt B af cf)
        (continuous_Wt B af cf).stronglyMeasurable).norm).mul hFScont.stronglyMeasurable.norm).aestronglyMeasurable
      (Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hFSb ξ) (norm_nonneg _)
  have hmeas : MeasurableSet (Set.Icc (-Ξ) Ξ) := measurableSet_Icc
  have hsplit : ∫ ξ, ‖FT (Wt B af cf) ξ‖ * ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖
      = (∫ ξ in Set.Icc (-Ξ) Ξ,
            ‖FT (Wt B af cf) ξ‖ * ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖)
        + (∫ ξ in (Set.Icc (-Ξ) Ξ)ᶜ,
            ‖FT (Wt B af cf) ξ‖ * ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖) :=
    (MeasureTheory.integral_add_compl hmeas hGint).symm
  have hcompl : (Set.Icc (-Ξ) Ξ)ᶜ = {ξ : ℝ | Ξ < |ξ|} := by
    ext ξ
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra h'
      exact h (abs_le.1 (le_of_not_gt h'))
    · rintro h ⟨h1, h2⟩
      exact absurd (abs_le.2 ⟨h1, h2⟩) (not_le.mpr h)
  have hnear : (∫ ξ in Set.Icc (-Ξ) Ξ,
        ‖FT (Wt B af cf) ξ‖ * ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖)
      ≤ cη * (∫ ξ in Set.Icc (-Ξ) Ξ, ‖FT (Wt B af cf) ξ‖) := by
    calc (∫ ξ in Set.Icc (-Ξ) Ξ,
          ‖FT (Wt B af cf) ξ‖ * ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖)
        ≤ ∫ ξ in Set.Icc (-Ξ) Ξ, cη * ‖FT (Wt B af cf) ξ‖ := by
          refine MeasureTheory.setIntegral_mono_on hGint.integrableOn
            (((integrable_FT_Wt B af cf hB hac).norm.const_mul cη).integrableOn) hmeas
            (fun ξ hξ => ?_)
          have hξ' : |ξ| ≤ Ξ := by
            rw [Set.mem_Icc] at hξ
            exact abs_le.2 hξ
          calc ‖FT (Wt B af cf) ξ‖ * ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖
              ≤ ‖FT (Wt B af cf) ξ‖ * cη :=
                mul_le_mul_of_nonneg_left (le_of_lt (hFS ξ hξ')) (norm_nonneg _)
            _ = cη * ‖FT (Wt B af cf) ξ‖ := by ring
      _ = cη * (∫ ξ in Set.Icc (-Ξ) Ξ, ‖FT (Wt B af cf) ξ‖) := by
          rw [MeasureTheory.integral_const_mul]
  have hfar : (∫ ξ in (Set.Icc (-Ξ) Ξ)ᶜ,
        ‖FT (Wt B af cf) ξ‖ * ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖)
      ≤ (H + 1) * (∫ ξ in {ξ : ℝ | Ξ < |ξ|}, ‖FT (Wt B af cf) ξ‖) := by
    rw [hcompl]
    calc (∫ ξ in {ξ : ℝ | Ξ < |ξ|},
          ‖FT (Wt B af cf) ξ‖ * ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖)
        ≤ ∫ ξ in {ξ : ℝ | Ξ < |ξ|}, ‖FT (Wt B af cf) ξ‖ * (H + 1) := by
          refine MeasureTheory.setIntegral_mono_on hGint.integrableOn
            (((integrable_FT_Wt B af cf hB hac).norm.mul_const (H + 1)).integrableOn)
            (by measurability) (fun ξ _ => ?_)
          exact mul_le_mul_of_nonneg_left (hFSb ξ) (norm_nonneg _)
      _ = (∫ ξ in {ξ : ℝ | Ξ < |ξ|}, ‖FT (Wt B af cf) ξ‖) * (H + 1) := by
          rw [MeasureTheory.integral_mul_const]
      _ = (H + 1) * (∫ ξ in {ξ : ℝ | Ξ < |ξ|}, ‖FT (Wt B af cf) ξ‖) := by ring
  calc ‖∫ ξ, FT (Wt B af cf) ξ * (∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ))‖
      ≤ ∫ ξ, ‖FT (Wt B af cf) ξ * (∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ ξ, ‖FT (Wt B af cf) ξ‖ * ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖ := by
        refine integral_congr_ae (Eventually.of_forall (fun ξ => ?_))
        simp only [norm_mul]
    _ = _ := hsplit
    _ ≤ cη * (∫ ξ in Set.Icc (-Ξ) Ξ, ‖FT (Wt B af cf) ξ‖)
          + (H + 1) * (∫ ξ in {ξ : ℝ | Ξ < |ξ|}, ‖FT (Wt B af cf) ξ‖) := by
        linarith [hnear, hfar]

/-- The discretisation error of the trapezoidal weight. -/
lemma weight_error_le (B af cf : ℝ) (hB : 0 < B) (hac : af ≤ cf) (b : ℕ → ℂ)
    (hb : ∀ n, ‖b n‖ ≤ 1) (A0 C0 B0 : ℕ) (hA0C0 : A0 ≤ C0) (hC0B0 : C0 ≤ B0) :
    ‖(∑ n ∈ Finset.Icc A0 C0, b n) - (∑ n ∈ Finset.Icc A0 B0, b n * Wt B af cf (n : ℝ))‖
      ≤ (∑ n ∈ Finset.Icc A0 C0, (1 - Wf B af cf (n : ℝ)))
        + (∑ n ∈ Finset.Icc (C0 + 1) B0, |Wf B af cf (n : ℝ)|) := by
  have hsplit : (∑ n ∈ Finset.Icc A0 B0, b n * Wt B af cf (n : ℝ))
      = (∑ n ∈ Finset.Icc A0 C0, b n * Wt B af cf (n : ℝ))
        + (∑ n ∈ Finset.Icc (C0 + 1) B0, b n * Wt B af cf (n : ℝ)) := by
    rw [← Finset.sum_union]
    · congr 1; ext n; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    · rw [Finset.disjoint_left]; intro n hn1 hn2
      simp only [Finset.mem_Icc] at hn1 hn2; omega
  have hE1 : ‖∑ n ∈ Finset.Icc A0 C0, b n * (Wt B af cf (n : ℝ) - 1)‖
      ≤ ∑ n ∈ Finset.Icc A0 C0, (1 - Wf B af cf (n : ℝ)) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun n _ => ?_))
    have h1 : ‖Wt B af cf (n : ℝ) - 1‖ = 1 - Wf B af cf (n : ℝ) := by
      have h2 : Wt B af cf (n : ℝ) - 1 = ((Wf B af cf (n : ℝ) - 1 : ℝ) : ℂ) := by
        unfold Wt; push_cast; ring
      rw [h2, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos (by linarith [Wf_le_one B af cf (n : ℝ) hB hac])]
      ring
    calc ‖b n * (Wt B af cf (n : ℝ) - 1)‖ = ‖b n‖ * (1 - Wf B af cf (n : ℝ)) := by
          rw [norm_mul, h1]
      _ ≤ 1 * (1 - Wf B af cf (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (hb n) (by linarith [Wf_le_one B af cf (n : ℝ) hB hac])
      _ = 1 - Wf B af cf (n : ℝ) := by ring
  have hE2 : ‖∑ n ∈ Finset.Icc (C0 + 1) B0, b n * Wt B af cf (n : ℝ)‖
      ≤ ∑ n ∈ Finset.Icc (C0 + 1) B0, |Wf B af cf (n : ℝ)| := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun n _ => ?_))
    calc ‖b n * Wt B af cf (n : ℝ)‖ = ‖b n‖ * |Wf B af cf (n : ℝ)| := by
          rw [norm_mul, norm_Wt]
      _ ≤ 1 * |Wf B af cf (n : ℝ)| := mul_le_mul_of_nonneg_right (hb n) (abs_nonneg _)
      _ = |Wf B af cf (n : ℝ)| := by ring
  have hmain : (∑ n ∈ Finset.Icc A0 C0, b n) - (∑ n ∈ Finset.Icc A0 B0, b n * Wt B af cf (n : ℝ))
      = - (∑ n ∈ Finset.Icc A0 C0, b n * (Wt B af cf (n : ℝ) - 1))
        - (∑ n ∈ Finset.Icc (C0 + 1) B0, b n * Wt B af cf (n : ℝ)) := by
    rw [hsplit]
    have h3 : (∑ n ∈ Finset.Icc A0 C0, b n * (Wt B af cf (n : ℝ) - 1))
        = (∑ n ∈ Finset.Icc A0 C0, b n * Wt B af cf (n : ℝ))
          - (∑ n ∈ Finset.Icc A0 C0, b n) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun n _ => ?_); ring
    rw [h3]; ring
  rw [hmain]
  have h4 := norm_sub_le (- (∑ n ∈ Finset.Icc A0 C0, b n * (Wt B af cf (n : ℝ) - 1)))
    (∑ n ∈ Finset.Icc (C0 + 1) B0, b n * Wt B af cf (n : ℝ))
  simp only [norm_neg] at h4
  linarith [h4, hE1, hE2]

theorem completion_of_sums :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (η' : ℝ) (hη' : 0 < η') (_hη'₁ : η' ≤ 1)
      (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (P : ℝ[X]) (y z H : ℝ),
      1 ≤ H → 1 ≤ y → y ≤ z → z - y ≤ H →
      η' * H ≤ ‖∑ n ∈ natIcc y z, a n * eC (-(P.eval (n : ℝ)))‖ →
      ∃ θ : ℝ, |θ| ≤ C / (η' ^ 2 * H) ∧ c * η' ^ 4 * H ≤
        ‖∑ n ∈ natIcc y (y + H), a n * eC (-((P + Polynomial.C θ * Polynomial.X).eval (n : ℝ)))‖ := by
  refine ⟨256 * (Kphi + 1) + 64, 1 / (1000 * Real.sqrt (Kphi + 1)), ?_, ?_, ?_⟩
  · have h := Kphi_nonneg; linarith
  · have h := Kphi_nonneg
    have h2 : 0 < Real.sqrt (Kphi + 1) := Real.sqrt_pos.mpr (by linarith)
    positivity
  · intro η' hη' hη'1 a ha P y z H hH hy hyz hyzH hcorr
    set A0 : ℕ := ⌈y⌉₊ with hA0def
    set C0 : ℕ := ⌊z⌋₊ with hC0def
    set B0 : ℕ := ⌊y + H⌋₊ with hB0def
    have hK : 0 ≤ Kphi := Kphi_nonneg
    have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
    have hηHpos : 0 < η' * H := mul_pos hη' hHpos
    have hz0 : 0 ≤ z := le_trans (by linarith : (0 : ℝ) ≤ y) hyz
    have hzH0 : 0 ≤ y + H := by linarith
    have hA0R : y ≤ (A0 : ℝ) := by rw [hA0def]; exact Nat.le_ceil y
    have hC0R : (C0 : ℝ) ≤ z := by rw [hC0def]; exact Nat.floor_le hz0
    have hB0R : (B0 : ℝ) ≤ y + H := by rw [hB0def]; exact Nat.floor_le hzH0
    have hA0C0 : A0 ≤ C0 := by
      by_contra h
      push_neg at h
      have hemp : Finset.Icc A0 C0 = ∅ := Finset.Icc_eq_empty_iff.mpr (not_le.mpr h)
      have h2 : η' * H ≤ 0 := by
        have h3 := hcorr
        rw [natIcc, hemp, Finset.sum_empty, norm_zero] at h3
        exact h3
      linarith
    have hC0B0 : C0 ≤ B0 := by
      have h1 : z ≤ y + H := by linarith
      exact Nat.floor_le_floor h1
    have hcard : ((Finset.Icc A0 B0).card : ℝ) ≤ H + 1 := by
      have h1 : (B0 : ℝ) ≤ (A0 : ℝ) + H := by linarith
      have h2 : B0 ≤ A0 + ⌊H⌋₊ := by
        have h3 : B0 ≤ ⌊(A0 : ℝ) + H⌋₊ := Nat.le_floor h1
        rw [add_comm (A0 : ℝ) H, Nat.floor_add_natCast (by linarith : (0 : ℝ) ≤ H)] at h3
        omega
      have h4 : B0 + 1 - A0 ≤ ⌊H⌋₊ + 1 := by omega
      rw [Nat.card_Icc]
      calc ((B0 + 1 - A0 : ℕ) : ℝ) ≤ ((⌊H⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h4
        _ = (⌊H⌋₊ : ℝ) + 1 := by push_cast; ring
        _ ≤ H + 1 := by linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ H)]
    set b : ℕ → ℂ := fun n => a n * eC (-(P.eval (n : ℝ))) with hbdef
    have hbval : ∀ n, b n = a n * eC (-(P.eval (n : ℝ))) := fun n => by rw [hbdef]
    have hbnorm : ∀ n, ‖b n‖ ≤ 1 := by
      intro n
      rw [hbval n, norm_mul, norm_eC, mul_one]
      exact ha n
    have hS_I : η' * H ≤ ‖∑ n ∈ Finset.Icc A0 C0, b n‖ := by
      have h := hcorr
      rw [natIcc] at h
      simpa only [hbval] using h
    have hsum_shift : ∀ θ : ℝ,
        (∑ n ∈ natIcc y (y + H), a n * eC (-((P + Polynomial.C θ * Polynomial.X).eval (n : ℝ))))
          = ∑ n ∈ Finset.Icc A0 B0, b n * eC (n * (-θ)) := by
      intro θ
      rw [natIcc]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [eC_shift P θ (n : ℝ), hbval n]
      ring
    set Ξ : ℝ := (256 * (Kphi + 1) + 64) / (η' ^ 2 * H) with hΞdef
    have hΞpos : 0 < Ξ := by rw [hΞdef]; positivity
    set cη : ℝ := (1 / (1000 * Real.sqrt (Kphi + 1))) * η' ^ 4 * H with hcηdef
    have hcηpos : 0 < cη := by
      rw [hcηdef]
      have h2 : 0 < Real.sqrt (Kphi + 1) := Real.sqrt_pos.mpr (by linarith [hK])
      positivity
    by_contra hcon
    have hcon' : ∀ θ : ℝ, |θ| ≤ Ξ →
        ¬ (cη ≤ ‖∑ n ∈ natIcc y (y + H),
            a n * eC (-((P + Polynomial.C θ * Polynomial.X).eval (n : ℝ)))‖) := by
      intro θ h1 h2
      refine hcon ⟨θ, h1, ?_⟩
      rw [hcηdef] at h2
      exact h2
    have hFS : ∀ ξ : ℝ, |ξ| ≤ Ξ → ‖∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ)‖ < cη := by
      intro ξ hξ
      have h1 := hcon' (-ξ) (by simpa using hξ)
      rw [hsum_shift (-ξ)] at h1
      simpa using h1
    by_cases hcase : η' * H ≤ 100
    · -- ===== CASE 1 : η' H ≤ 100 =====
      set af : ℝ := (A0 : ℝ) - 1/2 with hafdef
      set cf : ℝ := (C0 : ℝ) + 1/2 with hcfdef
      have hac : af ≤ cf := by
        rw [hafdef, hcfdef]
        linarith [show (A0 : ℝ) ≤ (C0 : ℝ) from by exact_mod_cast hA0C0]
      set near : ℝ := ∫ ξ in Set.Icc (-Ξ) Ξ, ‖FT (Wt 1 af cf) ξ‖ with hneardef
      set far : ℝ := ∫ ξ in {ξ : ℝ | Ξ < |ξ|}, ‖FT (Wt 1 af cf) ξ‖ with hfardef
      set A : ℝ := ∫ t, ‖Wt 1 af cf t‖ with hAdef
      set D : ℝ := (2 * Kphi / 1) / (4 * Real.pi ^ 2) with hDdef
      have hCA : (C0 : ℝ) - (A0 : ℝ) ≤ H := by linarith
      have hAnum : A ≤ H + 3 := by
        have h1 : A ≤ (cf - af) + 1 + 1 := by
          rw [hAdef]; exact integral_Wt_le 1 af cf one_pos hac
        have h2 : cf - af = (C0 : ℝ) - (A0 : ℝ) + 1 := by rw [hafdef, hcfdef]; ring
        linarith
      have hDnum : D = Kphi / (2 * Real.pi ^ 2) := by rw [hDdef]; ring_nf
      have hnearnum : near ≤ 4 * Real.sqrt (A * D) := by
        rw [hneardef, hAdef, hDdef]
        exact setIntegral_FT_norm_le_sqrt 1 af cf Ξ one_pos hac
      have hfarnum : far ≤ 2 * D / ((256 * (Kphi + 1) + 64) / (η' ^ 2 * H)) := by
        have h := setIntegral_FT_norm_tail_le 1 af cf Ξ one_pos hac hΞpos
        rw [← hfardef, hΞdef] at h
        exact h
      have hupp : ‖∫ ξ, FT (Wt 1 af cf) ξ * (∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ))‖
          ≤ cη * near + (H + 1) * far := by
        have h := fourier_upper_bound 1 af cf Ξ cη H one_pos hac hΞpos.le hcηpos.le
          b hbnorm A0 B0 hcard hFS
        rw [← hneardef, ← hfardef] at h
        exact h
      have hlow : η' * H ≤ ‖∫ ξ, FT (Wt 1 af cf) ξ * (∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ))‖ := by
        calc η' * H ≤ ‖∑ n ∈ Finset.Icc A0 C0, b n‖ := hS_I
          _ = ‖∑ n ∈ Finset.Icc A0 B0, b n * Wt 1 af cf (n : ℝ)‖ := by
              rw [Wt_one_int_sum b A0 C0 B0 hA0C0 hC0B0]
          _ = ‖∫ ξ, FT (Wt 1 af cf) ξ * (∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ))‖ := by
              rw [Wt_identity b A0 B0 1 af cf one_pos hac]
      have hnum := case1_bounds Kphi η' H A D near far hK hη' hη'1 hH hcase
        hAnum hDnum hnearnum hfarnum
      have hnum' : cη * near + (H + 1) * far < η' * H := by rw [hcηdef]; exact hnum
      linarith [hlow, hupp, hnum']
    · -- ===== CASE 2 : 100 < η' H =====
      push_neg at hcase
      set B : ℝ := η' * H / 16 with hBdef
      set af : ℝ := (A0 : ℝ) with hafdef
      set cf : ℝ := (C0 : ℝ) with hcfdef
      have hBpos : 0 < B := by rw [hBdef]; positivity
      have hac : af ≤ cf := by
        rw [hafdef, hcfdef]
        exact_mod_cast hA0C0
      set Err : ℝ := 3 / 2 * B + 3 with hErrdef
      have hErrpos : 0 < Err := by rw [hErrdef]; linarith [hBpos]
      set near : ℝ := ∫ ξ in Set.Icc (-Ξ) Ξ, ‖FT (Wt B af cf) ξ‖ with hneardef
      set far : ℝ := ∫ ξ in {ξ : ℝ | Ξ < |ξ|}, ‖FT (Wt B af cf) ξ‖ with hfardef
      set A : ℝ := ∫ t, ‖Wt B af cf t‖ with hAdef
      set D : ℝ := (2 * Kphi / B) / (4 * Real.pi ^ 2) with hDdef
      have hCA : (C0 : ℝ) - (A0 : ℝ) ≤ H := by linarith
      have hAnum : A ≤ H + η' * H / 16 + 1 := by
        have h1 : A ≤ (cf - af) + B + 1 := by
          rw [hAdef]; exact integral_Wt_le B af cf hBpos hac
        have h2 : cf - af = (C0 : ℝ) - (A0 : ℝ) := by rw [hafdef, hcfdef]
        linarith
      have hDnum : D = (2 * Kphi / (η' * H / 16)) / (4 * Real.pi ^ 2) := by
        rw [hDdef, hBdef]
      have hnearnum : near ≤ 4 * Real.sqrt (A * D) := by
        rw [hneardef, hAdef, hDdef]
        exact setIntegral_FT_norm_le_sqrt B af cf Ξ hBpos hac
      have hfarnum : far ≤ 2 * D / ((256 * (Kphi + 1) + 64) / (η' ^ 2 * H)) := by
        have h := setIntegral_FT_norm_tail_le B af cf Ξ hBpos hac hΞpos
        rw [← hfardef, hΞdef] at h
        exact h
      have hErrnum : Err ≤ 3 / 2 * (η' * H / 16) + 3 := by rw [hErrdef, hBdef]
      have herr : ‖∑ n ∈ Finset.Icc A0 C0, b n‖
          ≤ ‖∑ n ∈ Finset.Icc A0 B0, b n * Wt B af cf (n : ℝ)‖ + Err := by
        have h1 := weight_error_le B af cf hBpos hac b hbnorm A0 C0 B0 hA0C0 hC0B0
        have h2 := Wf_sum_error_bound B hBpos A0 C0 B0 hA0C0 hC0B0
        have h3 : ‖∑ n ∈ Finset.Icc A0 C0, b n‖
            ≤ ‖∑ n ∈ Finset.Icc A0 B0, b n * Wt B af cf (n : ℝ)‖
              + ‖(∑ n ∈ Finset.Icc A0 C0, b n)
                - (∑ n ∈ Finset.Icc A0 B0, b n * Wt B af cf (n : ℝ))‖ := by
          have h4 : (∑ n ∈ Finset.Icc A0 C0, b n)
              = (∑ n ∈ Finset.Icc A0 B0, b n * Wt B af cf (n : ℝ))
                + ((∑ n ∈ Finset.Icc A0 C0, b n)
                  - (∑ n ∈ Finset.Icc A0 B0, b n * Wt B af cf (n : ℝ))) := by ring
          calc ‖∑ n ∈ Finset.Icc A0 C0, b n‖
              = ‖(∑ n ∈ Finset.Icc A0 B0, b n * Wt B af cf (n : ℝ))
                  + ((∑ n ∈ Finset.Icc A0 C0, b n)
                    - (∑ n ∈ Finset.Icc A0 B0, b n * Wt B af cf (n : ℝ)))‖ :=
                congrArg norm h4
            _ ≤ _ := norm_add_le _ _
        rw [hErrdef]
        linarith [h1, h2, h3]
      have hupp : ‖∫ ξ, FT (Wt B af cf) ξ * (∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ))‖
          ≤ cη * near + (H + 1) * far := by
        have h := fourier_upper_bound B af cf Ξ cη H hBpos hac hΞpos.le hcηpos.le
          b hbnorm A0 B0 hcard hFS
        rw [← hneardef, ← hfardef] at h
        exact h
      have hlow : η' * H ≤ ‖∫ ξ, FT (Wt B af cf) ξ * (∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ))‖ + Err := by
        calc η' * H ≤ ‖∑ n ∈ Finset.Icc A0 C0, b n‖ := hS_I
          _ ≤ ‖∑ n ∈ Finset.Icc A0 B0, b n * Wt B af cf (n : ℝ)‖ + Err := herr
          _ = ‖∫ ξ, FT (Wt B af cf) ξ * (∑ n ∈ Finset.Icc A0 B0, b n * eC (n * ξ))‖ + Err := by
              rw [Wt_identity b A0 B0 B af cf hBpos hac]
      have hnum := case2_bounds Kphi η' H A D near far Err hK hη' hη'1 hH hcase
        hAnum hDnum hnearnum hfarnum hErrnum
      have hnum' : cη * near + (H + 1) * far + 2 * Err < η' * H := by rw [hcηdef]; exact hnum
      have hl : η' * H ≤ cη * near + (H + 1) * far + Err := by linarith [hlow, hupp]
      linarith [hl, hnum', hErrpos]

end Work.BMF
