/-
# Linearity of the two-dimensional Fourier coefficient `coeff2`

`Work.KMTPlan.A6.coeff2 σ p₁ p₂ = ∫₀¹ ∫₀¹ σ(x,y) e(-p₁x - p₂y) dx dy`
(`Work.KMTPlan.A6.SymToolbox`) is the `(p₁,p₂)`-th Fourier coefficient of the symbol `σ` on the
unit square.  As a function of `σ` it is *linear* on the class of symbols whose two sections are
integrable; in particular

  `coeff2 σ₁ p₁ p₂ - coeff2 σ₂ p₁ p₂ = coeff2 (fun x y => σ₁ x y - σ₂ x y) p₁ p₂`.

This module proves that statement for symbols that are jointly **measurable and bounded** — which
is the case for the two §6 model-approximation symbols `symC` (the symbol of the concrete clamped
column) and `symM` (the symbol of the model column, an integral in `t` of a jointly continuous
family).  Consequently the coefficient kernel of `symC - symM` is the difference of the two
coefficient kernels.

The proof is the elementary two-variable version of additivity of the integral.  Writing the
interval integrals as integrals against `volume.restrict (Ioc 0 1)`, additivity at the inner level
is `integral_sub` applied to the two sections `y ↦ σᵢ x y · e(-p₁x - p₂y)` (integrable because they
are measurable and bounded), and at the outer level `integral_sub` applied to the two parametric
integrals `x ↦ ∫ y, σᵢ x y · e(-p₁x - p₂y)` (measurable by
`StronglyMeasurable.integral_prod_right`, bounded by the same constants).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.colSmall_eq_bilinOp_symC
import Submission.Work.KMTPlan.A6.lowModel_eq_bilinOp_symM

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory intervalIntegral
open Work.KMTAreas.A7
open scoped BigOperators ENNReal

noncomputable section

/-! ## Elementary facts about `eeC`, `symSeq`, `symSeq2` and `halfSym` -/

/-- The character `e(x) = exp (2 π i x)` is continuous. -/
lemma continuous_eeC : Continuous eeC := by unfold eeC; fun_prop

/-- The symbol `symSeq κ` of a summable kernel is bounded by the `ℓ¹` mass of the kernel. -/
lemma norm_symSeq_le {κ : ℤ → ℂ} (hκ : Summable fun j : ℤ => ‖κ j‖) (x : ℝ) :
    ‖symSeq κ x‖ ≤ ∑' j : ℤ, ‖κ j‖ := by
  have hF : Summable (fun j : ℤ => κ j * eeC ((j : ℝ) * x)) :=
    Summable.of_norm_bounded hκ (fun j => by rw [norm_mul, norm_eeC, mul_one])
  rw [symSeq]
  calc ‖∑' j : ℤ, κ j * eeC ((j : ℝ) * x)‖
      ≤ ∑' j : ℤ, ‖κ j * eeC ((j : ℝ) * x)‖ := norm_tsum_le_tsum_norm hF.norm
    _ = ∑' j : ℤ, ‖κ j‖ := tsum_congr (fun j => by rw [norm_mul, norm_eeC, mul_one])

/-- The symbol `symSeq2 K` of a summable two-dimensional kernel is bounded by the `ℓ¹` mass. -/
lemma norm_symSeq2_le {K : ℤ → ℤ → ℂ} (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    (x y : ℝ) :
    ‖symSeq2 K x y‖ ≤ ∑' p : ℤ × ℤ, ‖K p.1 p.2‖ := by
  have hF : Summable (fun p : ℤ × ℤ => K p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y)) :=
    Summable.of_norm_bounded hK (fun p => by rw [norm_mul, norm_eeC, mul_one])
  have htsum : (∑' p : ℤ × ℤ, K p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y))
      = ∑' p : ℤ, ∑' r : ℤ, K p r * eeC ((p : ℝ) * x + (r : ℝ) * y) :=
    Summable.tsum_prod hF
  rw [symSeq2, ← htsum]
  calc ‖∑' p : ℤ × ℤ, K p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y)‖
      ≤ ∑' p : ℤ × ℤ, ‖K p.1 p.2 * eeC ((p.1 : ℝ) * x + (p.2 : ℝ) * y)‖ :=
        norm_tsum_le_tsum_norm hF.norm
    _ = ∑' p : ℤ × ℤ, ‖K p.1 p.2‖ :=
        tsum_congr (fun p => by rw [norm_mul, norm_eeC, mul_one])

/-- The sequence symbol of a fixed kernel is measurable. -/
lemma measurable_symSeq (κ : ℤ → ℂ) : Measurable (symSeq κ) := by
  rw [show symSeq κ = fun x : ℝ => ∑' j : ℤ, κ j * eeC ((j : ℝ) * x) from by
    funext x; rw [symSeq]]
  exact Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j =>
    ((continuous_const.mul (continuous_eeC.comp (by fun_prop))).measurable))

/-- The two-dimensional sequence symbol is jointly measurable (no summability needed). -/
lemma measurable_symSeq2 (K : ℤ → ℤ → ℂ) :
    Measurable (fun q : ℝ × ℝ => symSeq2 K q.1 q.2) := by
  rw [show (fun q : ℝ × ℝ => symSeq2 K q.1 q.2) = fun q : ℝ × ℝ =>
      ∑' p : ℤ, ∑' r : ℤ, K p r * eeC ((p : ℝ) * q.1 + (r : ℝ) * q.2) from by
    funext q; rw [symSeq2]]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun p => ?_)
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun r => ?_)
  exact ((continuous_eeC.comp (by fun_prop : Continuous fun q : ℝ × ℝ =>
    (p : ℝ) * q.1 + (r : ℝ) * q.2)).measurable).const_mul _

/-- Joint measurability of `(x,t) ↦ symSeq (κ t) x` for a family measurable in `t`. -/
lemma measurable_symSeq_family (κ : ℝ → ℤ → ℂ)
    (hκ : ∀ j : ℤ, Measurable fun t : ℝ => κ t j) :
    Measurable (fun q : ℝ × ℝ => symSeq (κ q.2) q.1) := by
  rw [show (fun q : ℝ × ℝ => symSeq (κ q.2) q.1) = fun q : ℝ × ℝ =>
      ∑' j : ℤ, κ q.2 j * eeC ((j : ℝ) * q.1) from by funext q; rw [symSeq]]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j => ?_)
  have h1 : Measurable (fun q : ℝ × ℝ => κ q.2 j) := (hκ j).comp measurable_snd
  have h2 : Measurable (fun q : ℝ × ℝ => eeC ((j : ℝ) * q.1)) :=
    (continuous_eeC.comp (by fun_prop : Continuous fun q : ℝ × ℝ => (j : ℝ) * q.1)).measurable
  exact h1.mul h2

/-- Joint measurability of `(x,y,t) ↦ symSeq (κ t) x` for a family measurable in `t`. -/
lemma measurable_symSeq_family3 (κ : ℝ → ℤ → ℂ)
    (hκ : ∀ j : ℤ, Measurable fun t : ℝ => κ t j) :
    Measurable (fun w : (ℝ × ℝ) × ℝ => symSeq (κ w.2) w.1.1) := by
  rw [show (fun w : (ℝ × ℝ) × ℝ => symSeq (κ w.2) w.1.1) = fun w : (ℝ × ℝ) × ℝ =>
      ∑' j : ℤ, κ w.2 j * eeC ((j : ℝ) * w.1.1) from by funext w; rw [symSeq]]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j => ?_)
  have h1 : Measurable (fun w : (ℝ × ℝ) × ℝ => κ w.2 j) := (hκ j).comp measurable_snd
  have h2 : Measurable (fun w : (ℝ × ℝ) × ℝ => eeC ((j : ℝ) * w.1.1)) :=
    (continuous_eeC.comp (by fun_prop : Continuous fun w : (ℝ × ℝ) × ℝ =>
      (j : ℝ) * w.1.1)).measurable
  exact h1.mul h2

/-- Joint measurability of `(x,y,t) ↦ symSeq (κ t) y` for a family measurable in `t`. -/
lemma measurable_symSeq_family3' (κ : ℝ → ℤ → ℂ)
    (hκ : ∀ j : ℤ, Measurable fun t : ℝ => κ t j) :
    Measurable (fun w : (ℝ × ℝ) × ℝ => symSeq (κ w.2) w.1.2) := by
  rw [show (fun w : (ℝ × ℝ) × ℝ => symSeq (κ w.2) w.1.2) = fun w : (ℝ × ℝ) × ℝ =>
      ∑' j : ℤ, κ w.2 j * eeC ((j : ℝ) * w.1.2) from by funext w; rw [symSeq]]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j => ?_)
  have h1 : Measurable (fun w : (ℝ × ℝ) × ℝ => κ w.2 j) := (hκ j).comp measurable_snd
  have h2 : Measurable (fun w : (ℝ × ℝ) × ℝ => eeC ((j : ℝ) * w.1.2)) :=
    (continuous_eeC.comp (by fun_prop : Continuous fun w : (ℝ × ℝ) × ℝ =>
      (j : ℝ) * w.1.2)).measurable
  exact h1.mul h2

/-- The halved-average symbol `halfSym N P` is continuous. -/
lemma continuous_halfSym (N : ℕ) (P : Polynomial ℤ) :
    Continuous (fun q : ℝ × ℝ => halfSym N P q.1 q.2) := by
  simp only [halfSym]
  refine continuous_const.mul (continuous_finsetSum _ (fun n _ => ?_))
  exact continuous_eeC.comp (by fun_prop)

/-- The halved-average symbol is bounded by `N⁻¹` times the number of terms. -/
lemma norm_halfSym_le (N : ℕ) (P : Polynomial ℤ) (x y : ℝ) :
    ‖halfSym N P x y‖ ≤ ‖((N : ℂ))⁻¹‖ * ((Finset.Ioc (N / 2) N).card : ℝ) := by
  simp only [halfSym, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖∑ n ∈ Finset.Ioc (N / 2) N,
        eeC ((n : ℝ) * x + ((P.eval (n : ℤ) : ℤ) : ℝ) * y)‖
      ≤ ∑ n ∈ Finset.Ioc (N / 2) N,
          ‖eeC ((n : ℝ) * x + ((P.eval (n : ℤ) : ℤ) : ℝ) * y)‖ := norm_sum_le _ _
    _ = ((Finset.Ioc (N / 2) N).card : ℝ) := by
        simp only [norm_eeC, Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ## Measurability and boundedness of the two symbols of §6 -/

/-- The concrete symbol `symC` is jointly measurable. -/
lemma measurable_symC (ρ : ℝ) (P : Polynomial ℤ) (N l₁ l₂ k₁ k₂ : ℕ) :
    Measurable (fun z : ℝ × ℝ => symC ρ P N l₁ l₂ k₁ k₂ z.1 z.2) := by
  simp only [symC]
  exact (((measurable_symSeq _).comp measurable_fst).mul
    ((measurable_symSeq _).comp measurable_snd)).mul (continuous_halfSym N P).measurable

/-- The concrete symbol `symC` is bounded. -/
lemma exists_bound_symC (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (N l₁ l₂ k₁ k₂ : ℕ) :
    ∃ C : ℝ, ∀ x y : ℝ, ‖symC ρ P N l₁ l₂ k₁ k₂ x y‖ ≤ C := by
  refine ⟨(∑' j : ℤ, ‖tmKer ρ l₁ (varphiN N k₁) j‖)
      * (∑' j : ℤ, ‖tmKer ρ l₂ (varphitildeN P.natDegree N k₂) j‖)
      * (‖((N : ℂ))⁻¹‖ * ((Finset.Ioc (N / 2) N).card : ℝ)), fun x y => ?_⟩
  simp only [symC, norm_mul]
  refine mul_le_mul (mul_le_mul ?_ ?_ (norm_nonneg _)
      (tsum_nonneg (fun _ => norm_nonneg _))) ?_ (norm_nonneg _)
    (mul_nonneg (tsum_nonneg (fun _ => norm_nonneg _))
      (tsum_nonneg (fun _ => norm_nonneg _)))
  · exact norm_symSeq_le (cesb_summable_tmKer_varphiN ρ hρ hρ1 l₁ N k₁) x
  · exact norm_symSeq_le (cesb_summable_tmKer_varphitildeN ρ hρ hρ1 l₂ P.natDegree N k₂) y
  · exact norm_halfSym_le N P x y

/-- The model symbol `symM` is jointly measurable. -/
lemma measurable_symM (ρ : ℝ) (P : Polynomial ℤ) (N l₁ l₂ k₁ k₂ : ℕ) :
    Measurable (fun z : ℝ × ℝ => symM ρ P N l₁ l₂ k₁ k₂ z.1 z.2) := by
  have hG : Measurable (fun w : (ℝ × ℝ) × ℝ =>
      symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) w.1.1 w.1.2
        * symSeq (tmKer ρ l₁ (varphiNt N k₁ w.2)) w.1.1
        * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ w.2)) w.1.2) := by
    have hA : Measurable (fun w : (ℝ × ℝ) × ℝ =>
        symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) w.1.1 w.1.2) :=
      (measurable_symSeq2 _).comp measurable_fst
    have hB : Measurable (fun w : (ℝ × ℝ) × ℝ =>
        symSeq (tmKer ρ l₁ (varphiNt N k₁ w.2)) w.1.1) :=
      measurable_symSeq_family3 (fun t : ℝ => tmKer ρ l₁ (varphiNt N k₁ t))
        (fun j => measurable_tmKer_varphiNt ρ l₁ N k₁ j)
    have hC : Measurable (fun w : (ℝ × ℝ) × ℝ =>
        symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ w.2)) w.1.2) :=
      measurable_symSeq_family3' (fun t : ℝ => tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t))
        (fun j => measurable_tmKer_varphitildeNt ρ P l₂ N k₂ j)
    exact (hA.mul hB).mul hC
  have hsingle : StronglyMeasurable (fun z : ℝ × ℝ => ∫ t in Set.Ioc (1 / 2 : ℝ) 1,
      symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) z.1 z.2
        * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) z.1
        * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) z.2) :=
    StronglyMeasurable.integral_prod_right (f := fun z : ℝ × ℝ => fun t : ℝ =>
      symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) z.1 z.2
        * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) z.1
        * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) z.2)
      (ν := volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) hG.stronglyMeasurable
  have hSm : StronglyMeasurable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
      symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) z.1 z.2
        * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) z.1
        * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) z.2) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using hsingle
  simpa only [symM] using hSm.measurable

/-- The model symbol `symM` is bounded. -/
lemma exists_bound_symM (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (N l₁ l₂ k₁ k₂ : ℕ) :
    ∃ C : ℝ, ∀ x y : ℝ, ‖symM ρ P N l₁ l₂ k₁ k₂ x y‖ ≤ C := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := uniform_tmKer_varphiNt ρ l₁ N k₁
  obtain ⟨B₂, hB₂0, hB₂⟩ := uniform_tmKer_varphitildeNt ρ P l₂ N k₂
  have hK : Summable (fun p : ℤ × ℤ => ‖arithKerM ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) :=
    summable_arithKerM ρ P l₁ l₂ k₁ k₂
  refine ⟨(∑' p : ℤ × ℤ, ‖arithKerM ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) * B₁ * B₂
    * |(1 : ℝ) - 1 / 2|, fun x y => ?_⟩
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => ?_)
  rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
  have hIcc : t ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
  simp only [symM, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul (norm_symSeq2_le hK x y)
      (le_trans (norm_symSeq_le (hB₁ t hIcc).1 x) (hB₁ t hIcc).2)
      (norm_nonneg _) (tsum_nonneg (fun _ => norm_nonneg _)))
    (le_trans (norm_symSeq_le (hB₂ t hIcc).1 y) (hB₂ t hIcc).2)
    (norm_nonneg _) (mul_nonneg (tsum_nonneg (fun _ => norm_nonneg _)) hB₁0)

/-! ## Linearity of `coeff2` -/

/-- **Linearity of `coeff2`** on jointly measurable, bounded symbols. -/
theorem coeff2_sub_of_meas_bdd (σ₁ σ₂ : ℝ → ℝ → ℂ) (p₁ p₂ : ℤ) (C₁ C₂ : ℝ)
    (hm₁ : Measurable fun z : ℝ × ℝ => σ₁ z.1 z.2)
    (hb₁ : ∀ x y, ‖σ₁ x y‖ ≤ C₁)
    (hm₂ : Measurable fun z : ℝ × ℝ => σ₂ z.1 z.2)
    (hb₂ : ∀ x y, ‖σ₂ x y‖ ≤ C₂) :
    coeff2 σ₁ p₁ p₂ - coeff2 σ₂ p₁ p₂
      = coeff2 (fun x y => σ₁ x y - σ₂ x y) p₁ p₂ := by
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  set F₁ : ℝ → ℝ → ℂ := fun x y => σ₁ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) with hF₁
  set F₂ : ℝ → ℝ → ℂ := fun x y => σ₂ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) with hF₂
  have hmF₁ : Measurable (fun z : ℝ × ℝ => F₁ z.1 z.2) := by
    simp only [hF₁]
    exact hm₁.mul (continuous_eeC.comp (by fun_prop)).measurable
  have hmF₂ : Measurable (fun z : ℝ × ℝ => F₂ z.1 z.2) := by
    simp only [hF₂]
    exact hm₂.mul (continuous_eeC.comp (by fun_prop)).measurable
  have hbF₁ : ∀ x y : ℝ, ‖F₁ x y‖ ≤ C₁ := by
    intro x y; simp only [hF₁, norm_mul, norm_eeC, mul_one]; exact hb₁ x y
  have hbF₂ : ∀ x y : ℝ, ‖F₂ x y‖ ≤ C₂ := by
    intro x y; simp only [hF₂, norm_mul, norm_eeC, mul_one]; exact hb₂ x y
  have hmx₁ : ∀ x : ℝ, Measurable (fun y : ℝ => F₁ x y) := fun x =>
    hmF₁.comp (measurable_const.prodMk measurable_id)
  have hmx₂ : ∀ x : ℝ, Measurable (fun y : ℝ => F₂ x y) := fun x =>
    hmF₂.comp (measurable_const.prodMk measurable_id)
  have hI₁ : ∀ x : ℝ, Integrable (fun y : ℝ => F₁ x y) μ := fun x =>
    Integrable.of_bound (hmx₁ x).aestronglyMeasurable C₁ (ae_of_all _ (fun y => hbF₁ x y))
  have hI₂ : ∀ x : ℝ, Integrable (fun y : ℝ => F₂ x y) μ := fun x =>
    Integrable.of_bound (hmx₂ x).aestronglyMeasurable C₂ (ae_of_all _ (fun y => hbF₂ x y))
  have hmJ₁ : Measurable (fun x : ℝ => ∫ y, F₁ x y ∂μ) :=
    ((hmF₁.stronglyMeasurable).integral_prod_right (f := F₁) (ν := μ)).measurable
  have hmJ₂ : Measurable (fun x : ℝ => ∫ y, F₂ x y ∂μ) :=
    ((hmF₂.stronglyMeasurable).integral_prod_right (f := F₂) (ν := μ)).measurable
  have hbJ₁ : ∀ x : ℝ, ‖∫ y, F₁ x y ∂μ‖ ≤ C₁ := by
    intro x
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C₁) (f := F₁ x) (fun y _ => hbF₁ x y)
    simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
    simpa using h
  have hbJ₂ : ∀ x : ℝ, ‖∫ y, F₂ x y ∂μ‖ ≤ C₂ := by
    intro x
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C₂) (f := F₂ x) (fun y _ => hbF₂ x y)
    simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
    simpa using h
  have hJ₁ : Integrable (fun x : ℝ => ∫ y, F₁ x y ∂μ) μ :=
    Integrable.of_bound hmJ₁.aestronglyMeasurable C₁ (ae_of_all _ hbJ₁)
  have hJ₂ : Integrable (fun x : ℝ => ∫ y, F₂ x y ∂μ) μ :=
    Integrable.of_bound hmJ₂.aestronglyMeasurable C₂ (ae_of_all _ hbJ₂)
  have hc₁ : coeff2 σ₁ p₁ p₂ = ∫ x, ∫ y, F₁ x y ∂μ ∂μ := by
    simp only [coeff2, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hF₁, hμ]
  have hc₂ : coeff2 σ₂ p₁ p₂ = ∫ x, ∫ y, F₂ x y ∂μ ∂μ := by
    simp only [coeff2, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hF₂, hμ]
  have hcd : coeff2 (fun x y => σ₁ x y - σ₂ x y) p₁ p₂
      = ∫ x, ∫ y, (F₁ x y - F₂ x y) ∂μ ∂μ := by
    simp only [coeff2, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hF₁, hF₂]
    ring
  calc coeff2 σ₁ p₁ p₂ - coeff2 σ₂ p₁ p₂
      = (∫ x, ∫ y, F₁ x y ∂μ ∂μ) - (∫ x, ∫ y, F₂ x y ∂μ ∂μ) := by rw [hc₁, hc₂]
    _ = ∫ x, ((∫ y, F₁ x y ∂μ) - (∫ y, F₂ x y ∂μ)) ∂μ := (integral_sub hJ₁ hJ₂).symm
    _ = ∫ x, ∫ y, (F₁ x y - F₂ x y) ∂μ ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          exact (integral_sub (hI₁ x) (hI₂ x)).symm
    _ = coeff2 (fun x y => σ₁ x y - σ₂ x y) p₁ p₂ := hcd.symm

/-! ## The requested identity -/

theorem coeff2_sub_symC_symM (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (N l₁ l₂ k₁ k₂ : ℕ) (p₁ p₂ : ℤ) :
    Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symC ρ P N l₁ l₂ k₁ k₂) p₁ p₂
        - Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symM ρ P N l₁ l₂ k₁ k₂) p₁ p₂
      = Work.KMTPlan.A6.coeff2
          (fun x y => Work.KMTPlan.A6.symC ρ P N l₁ l₂ k₁ k₂ x y
            - Work.KMTPlan.A6.symM ρ P N l₁ l₂ k₁ k₂ x y) p₁ p₂ := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_symC ρ hρ hρ1 P N l₁ l₂ k₁ k₂
  obtain ⟨C₂, hC₂⟩ := exists_bound_symM ρ hρ hρ1 P N l₁ l₂ k₁ k₂
  exact coeff2_sub_of_meas_bdd _ _ p₁ p₂ C₁ C₂
    (measurable_symC ρ P N l₁ l₂ k₁ k₂) hC₁
    (measurable_symM ρ P N l₁ l₂ k₁ k₂) hC₂

end

end Work.KMTPlan.A6
