import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.LHS_ae_congr
import Submission.Work.BoseBoxFock.enorm_integral_conj_mul_sq_le
import Submission.Work.BoseDict.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open Filter
open scoped ENNReal

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ## The two-coordinate splitting -/

/-- The insertion of the two coordinates `i ≠ j`. -/
def bII1Ins {n : ℕ} (i j : Fin n) (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) (a b : E3) :
    Fin n → E3 :=
  fun k => if h : k = i then a else if h' : k = j then b else x' ⟨k, h, h'⟩

lemma bII1Ins_ne {n : ℕ} {i j k : Fin n} (hi : k ≠ i) (hj : k ≠ j)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) (a b : E3) :
    bII1Ins i j x' a b k = x' ⟨k, hi, hj⟩ := by
  rw [bII1Ins]
  exact dif_neg hi |>.trans (dif_neg hj)

@[simp] lemma bII1Ins_i {n : ℕ} {i j : Fin n} (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3)
    (a b : E3) : bII1Ins i j x' a b i = a := by
  rw [bII1Ins, dif_pos rfl]

@[simp] lemma bII1Ins_j {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) (a b : E3) : bII1Ins i j x' a b j = b := by
  rw [bII1Ins, dif_neg hij.symm, dif_pos rfl]

lemma bII1Ins_update {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) (a b y u : E3) :
    Function.update (Function.update (bII1Ins i j x' a b) i y) j u = bII1Ins i j x' y u := by
  funext k
  rw [Function.update_apply, Function.update_apply]
  by_cases hk : k = i
  · rw [if_neg (fun h => hij (hk.symm.trans h)), if_pos hk, bII1Ins, dif_pos hk]
  · rw [if_neg hk]
    by_cases hk' : k = j
    · rw [if_pos hk', bII1Ins, dif_neg hk, dif_pos hk']
    · rw [if_neg hk', bII1Ins_ne hk hk', bII1Ins, dif_neg hk, dif_neg hk']

/-- Measurability of the insertion, in complete generality. -/
lemma measurable_bII1Ins_comp {n : ℕ} {Y : Type*} [MeasurableSpace Y] (i j : Fin n)
    {x' : Y → {k : Fin n // k ≠ i ∧ k ≠ j} → E3} {a b : Y → E3}
    (hx' : Measurable x') (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun y => bII1Ins i j (x' y) (a y) (b y)) := by
  rw [measurable_pi_iff]
  intro k
  by_cases hk : k = i
  · simpa only [bII1Ins, dif_pos hk] using ha
  · by_cases hkj : k = j
    · simpa only [bII1Ins, dif_neg hk, dif_pos hkj] using hb
    · simp only [bII1Ins, dif_neg hk, dif_neg hkj]
      change Measurable (fun y : Y => x' y ⟨k, hk, hkj⟩)
      exact (measurable_pi_apply (⟨k, hk, hkj⟩ : {k : Fin n // k ≠ i ∧ k ≠ j})).comp hx'

/-! ## The Cauchy–Schwarz split of the integrand -/

/-- `λ x = ‖A (x i)‖ * ‖A (x j)‖`, the modulus of the two `A`-factors. -/
def bII1Lam {n : ℕ} (A : E3 → ℂ) (i j : Fin n) (x : Fin n → E3) : ℝ :=
  ‖A (x i)‖ * ‖A (x j)‖

/-- The first Cauchy–Schwarz factor: `conj (Θ x) A (x i) A (x j) / λ x`. -/
def bII1H1 {n : ℕ} (Θ : (Fin n → E3) → ℂ) (A : E3 → ℂ) (i j : Fin n) (x : Fin n → E3) : ℂ :=
  (starRingEnd ℂ (Θ x) * A (x i) * A (x j)) / ((bII1Lam A i j x : ℝ) : ℂ)

/-- The second Cauchy–Schwarz factor: `λ x · Θ (x[i↦y][j↦u])`. -/
def bII1L2 {n : ℕ} (Θ : (Fin n → E3) → ℂ) (A : E3 → ℂ) (i j : Fin n) (y u : E3)
    (x : Fin n → E3) : ℂ :=
  ((bII1Lam A i j x : ℝ) : ℂ) * Θ (Function.update (Function.update x i y) j u)

/-- The substituted integrand: `‖Θ (x' , y, u)‖²`. -/
def bII1F {n : ℕ} (Θ : (Fin n → E3) → ℂ) (i j : Fin n)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) (y u : E3) : ℝ≥0∞ :=
  ‖Θ (bII1Ins i j x' y u)‖ₑ ^ 2

/-- The `x'`-fibre `L²` mass of `Θ`: `∫⁻ x', ‖Θ (x' , y, u)‖²`. -/
def bII1S {n : ℕ} (Θ : (Fin n → E3) → ℂ) (i j : Fin n) (y u : E3) : ℝ≥0∞ :=
  ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3, bII1F Θ i j x' y u

lemma bII1Lam_nonneg {n : ℕ} (A : E3 → ℂ) (i j : Fin n) (x : Fin n → E3) :
    0 ≤ bII1Lam A i j x := by
  rw [bII1Lam]; positivity

/-- The pointwise identity making the Cauchy–Schwarz split an identity. -/
lemma bII1H1_mul_bII1L2 {n : ℕ} (Θ : (Fin n → E3) → ℂ) (A : E3 → ℂ) (i j : Fin n)
    (y u : E3) (x : Fin n → E3) :
    bII1H1 Θ A i j x * bII1L2 Θ A i j y u x
      = (starRingEnd ℂ) (Θ x) * A (x i) * A (x j)
          * Θ (Function.update (Function.update x i y) j u) := by
  have hc : 0 ≤ bII1Lam A i j x := bII1Lam_nonneg A i j x
  rcases eq_or_lt_of_le hc with h | h
  · have h0 : A (x i) = 0 ∨ A (x j) = 0 := by
      rw [bII1Lam] at h
      rcases mul_eq_zero.mp h.symm with h1 | h2
      · exact Or.inl (norm_eq_zero.mp h1)
      · exact Or.inr (norm_eq_zero.mp h2)
    rw [bII1H1, bII1L2, ← h]
    rcases h0 with hA | hA <;> simp [hA]
  · rw [bII1H1, bII1L2]
    have hne : ((bII1Lam A i j x : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt h
    rw [← mul_assoc, div_mul_cancel₀ _ hne]

/-- The modulus of the first factor is at most `‖Θ x‖`. -/
lemma norm_bII1H1_le {n : ℕ} (Θ : (Fin n → E3) → ℂ) (A : E3 → ℂ) (i j : Fin n)
    (x : Fin n → E3) : ‖bII1H1 Θ A i j x‖ ≤ ‖Θ x‖ := by
  rw [bII1H1, norm_div, norm_mul, norm_mul]
  have hstar : ‖(starRingEnd ℂ) (Θ x)‖ = ‖Θ x‖ := by simp
  rw [hstar]
  have hc : (0:ℝ) ≤ bII1Lam A i j x := bII1Lam_nonneg A i j x
  have hcn : ‖((bII1Lam A i j x : ℝ) : ℂ)‖ = bII1Lam A i j x := by
    simp [abs_of_nonneg hc]
  rw [hcn, bII1Lam]
  rcases eq_or_lt_of_le
    (mul_nonneg (norm_nonneg (A (x i))) (norm_nonneg (A (x j)))) with h | h
  · rw [← h]; simp
  · rw [show ‖Θ x‖ * ‖A (x i)‖ * ‖A (x j)‖ / (‖A (x i)‖ * ‖A (x j)‖)
        = ‖Θ x‖ * (‖A (x i)‖ * ‖A (x j)‖) / (‖A (x i)‖ * ‖A (x j)‖) by ring,
      mul_div_assoc, div_self (ne_of_gt h), mul_one]

lemma enorm_bII1H1_le {n : ℕ} (Θ : (Fin n → E3) → ℂ) (A : E3 → ℂ) (i j : Fin n)
    (x : Fin n → E3) : ‖bII1H1 Θ A i j x‖ₑ ≤ ‖Θ x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_bII1H1_le Θ A i j x)

lemma enorm_bII1H1_sq_le {n : ℕ} (Θ : (Fin n → E3) → ℂ) (A : E3 → ℂ) (i j : Fin n)
    (x : Fin n → E3) : ‖bII1H1 Θ A i j x‖ₑ ^ 2 ≤ ‖Θ x‖ₑ ^ 2 :=
  pow_le_pow_left' (enorm_bII1H1_le Θ A i j x) 2

lemma enorm_bII1L2 {n : ℕ} (Θ : (Fin n → E3) → ℂ) (A : E3 → ℂ) (i j : Fin n) (y u : E3)
    (x : Fin n → E3) :
    ‖bII1L2 Θ A i j y u x‖ₑ ^ 2
      = ‖A (x i)‖ₑ ^ 2 * ‖A (x j)‖ₑ ^ 2
        * ‖Θ (Function.update (Function.update x i y) j u)‖ₑ ^ 2 := by
  rw [bII1L2, enorm_mul]
  have hlam : ‖((bII1Lam A i j x : ℝ) : ℂ)‖ₑ = ‖A (x i)‖ₑ * ‖A (x j)‖ₑ := by
    rw [bII1Lam, ← ofReal_norm]
    rw [show ‖(((‖A (x i)‖ * ‖A (x j)‖ : ℝ)) : ℂ)‖ = ‖A (x i)‖ * ‖A (x j)‖ by
      simp [abs_of_nonneg (norm_nonneg _)]]
    rw [ENNReal.ofReal_mul (norm_nonneg (A (x i))), ← ofReal_norm, ← ofReal_norm]
  rw [hlam]
  ring

lemma enorm_bII1L2_ins {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (Θ : (Fin n → E3) → ℂ) (A : E3 → ℂ)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) (a b y u : E3) :
    ‖bII1L2 Θ A i j y u (bII1Ins i j x' a b)‖ₑ ^ 2
      = (‖A a‖ₑ ^ 2 * ‖A b‖ₑ ^ 2) * ‖Θ (bII1Ins i j x' y u)‖ₑ ^ 2 := by
  rw [enorm_bII1L2, bII1Ins_i, bII1Ins_j hij, bII1Ins_update hij]

/-! ## Measurability of the composed integrand -/

lemma measurable_bII1H1 {n : ℕ} {Θ : (Fin n → E3) → ℂ} {A : E3 → ℂ}
    (hΘ : Measurable Θ) (hA : Measurable A) (i j : Fin n) :
    Measurable (bII1H1 Θ A i j) := by
  unfold bII1H1 bII1Lam
  fun_prop

lemma aemeasurable_bII1H1_star {n : ℕ} {Θ : (Fin n → E3) → ℂ} {A : E3 → ℂ}
    (hΘ : Measurable Θ) (hA : Measurable A) (i j : Fin n) :
    AEMeasurable (fun x : Fin n → E3 => starRingEnd ℂ (bII1H1 Θ A i j x)) :=
  ((Complex.continuous_conj.measurable.comp (measurable_bII1H1 hΘ hA i j))).aemeasurable

lemma aemeasurable_bII1L2 {n : ℕ} {Θ : (Fin n → E3) → ℂ} {A : E3 → ℂ}
    (hΘ : Measurable Θ) (hA : Measurable A) (i j : Fin n) (y u : E3) :
    AEMeasurable (fun x : Fin n → E3 => bII1L2 Θ A i j y u x) := by
  unfold bII1L2 bII1Lam
  fun_prop

lemma aemeasurable_bII1L2_sq {n : ℕ} {Θ : (Fin n → E3) → ℂ} {A : E3 → ℂ}
    (hΘ : Measurable Θ) (hA : Measurable A) (i j : Fin n) (y u : E3) :
    AEMeasurable (fun x : Fin n → E3 => ‖bII1L2 Θ A i j y u x‖ₑ ^ 2) :=
  (aemeasurable_bII1L2 hΘ hA i j y u).enorm.pow_const 2

lemma aemeasurable_substIntegrand {n : ℕ} {Θ : (Fin n → E3) → ℂ} {A : E3 → ℂ}
    (hΘ : Measurable Θ) (hA : Measurable A) (i j : Fin n) (y u : E3) :
    AEMeasurable (fun x : Fin n → E3 => ‖A (x i)‖ₑ ^ 2 * ‖A (x j)‖ₑ ^ 2
      * ‖Θ (Function.update (Function.update x i y) j u)‖ₑ ^ 2) := by
  fun_prop

/-- Joint measurability of `(x', y, u) ↦ ‖Θ (x' , y, u)‖²` in the nesting `W × (E3 × E3)`. -/
lemma measurable_bII1F {n : ℕ} {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) (i j : Fin n) :
    Measurable (fun p : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × (E3 × E3) =>
      bII1F Θ i j p.1 p.2.1 p.2.2) := by
  have h := measurable_bII1Ins_comp (Y := ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × (E3 × E3))
    i j (x' := fun p => p.1) (a := fun p => p.2.1) (b := fun p => p.2.2)
    (by fun_prop) (by fun_prop) (by fun_prop)
  exact (hΘ.comp h).enorm.pow_const 2

/-- AEMeasurability of `(x', y, u) ↦ ‖Θ (x' , y, u)‖²` (as a product-space function). -/
lemma aemeasurable_bII1F_joint {n : ℕ} {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ)
    (i j : Fin n) : AEMeasurable (fun p : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × (E3 × E3) =>
      bII1F Θ i j p.1 p.2.1 p.2.2) :=
  (measurable_bII1F hΘ i j).aemeasurable

/-- The `(y,u)`-joint measurability of `bII1S` in the nesting `(y,u)`. -/
lemma aemeasurable_bII1S_pair {n : ℕ} {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) (i j : Fin n) :
    AEMeasurable (fun q : E3 × E3 => bII1S Θ i j q.1 q.2) :=
  AEMeasurable.lintegral_prod_right'
    (μ := (volume : Measure (E3 × E3)))
    (ν := (volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3)))
    (f := fun q : (E3 × E3) × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) =>
      bII1F Θ i j q.2 q.1.1 q.1.2)
    (by
      have h := measurable_bII1Ins_comp (Y := (E3 × E3) × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3))
        i j (x' := fun q => q.2) (a := fun q => q.1.1) (b := fun q => q.1.2)
        (by fun_prop) (by fun_prop) (by fun_prop)
      exact ((hΘ.comp h).enorm.pow_const 2).aemeasurable)

/-- The `(y,u)`-joint measurability of `bII1S` in the nesting `(u,y)`. -/
lemma aemeasurable_bII1S_swap {n : ℕ} {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) (i j : Fin n) :
    AEMeasurable (fun q : E3 × E3 => bII1S Θ i j q.2 q.1) :=
  AEMeasurable.lintegral_prod_right'
    (μ := (volume : Measure (E3 × E3)))
    (ν := (volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3)))
    (f := fun q : (E3 × E3) × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) =>
      bII1F Θ i j q.2 q.1.2 q.1.1)
    (by
      have h := measurable_bII1Ins_comp (Y := (E3 × E3) × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3))
        i j (x' := fun q => q.2) (a := fun q => q.1.2) (b := fun q => q.1.1)
        (by fun_prop) (by fun_prop) (by fun_prop)
      exact ((hΘ.comp h).enorm.pow_const 2).aemeasurable)

lemma aemeasurable_bII1S_int {n : ℕ} {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) (i j : Fin n) :
    AEMeasurable (fun u : E3 => ∫⁻ y : E3, bII1S Θ i j y u) :=
  AEMeasurable.lintegral_prod_right (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
    (f := fun u y => bII1S Θ i j y u) (aemeasurable_bII1S_swap hΘ i j)

lemma aemeasurable_bII1S_fix {n : ℕ} {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) (i j : Fin n)
    (u : E3) : AEMeasurable (fun y : E3 => bII1S Θ i j y u) :=
  AEMeasurable.lintegral_prod_right'
    (μ := (volume : Measure E3)) (ν := (volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3)))
    (f := fun q : E3 × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) => bII1F Θ i j q.2 q.1 u)
    (by
      have h := measurable_bII1Ins_comp (Y := E3 × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3))
        i j (x' := fun q => q.2) (a := fun q => q.1) (b := fun _ => u)
        (by fun_prop) (by fun_prop) measurable_const
      exact ((hΘ.comp h).enorm.pow_const 2).aemeasurable)

lemma aemeasurable_bII1F_fix {n : ℕ} {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) (i j : Fin n)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) :
    AEMeasurable (fun p : E3 × E3 => bII1F Θ i j x' p.1 p.2) := by
  have h := measurable_bII1Ins_comp (Y := E3 × E3) i j (x' := fun _ => x')
    (a := fun p => p.1) (b := fun p => p.2) measurable_const (by fun_prop) (by fun_prop)
  exact ((hΘ.comp h).enorm.pow_const 2).aemeasurable

lemma aemeasurable_bII1F_x' {n : ℕ} {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) (i j : Fin n)
    (y u : E3) : AEMeasurable (fun x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3 =>
      bII1F Θ i j x' y u) := by
  have h := measurable_bII1Ins_comp (Y := {k : Fin n // k ≠ i ∧ k ≠ j} → E3) i j
    (x' := fun p => p) (a := fun _ => y) (b := fun _ => u) measurable_id measurable_const
    measurable_const
  exact ((hΘ.comp h).enorm.pow_const 2).aemeasurable

lemma aemeasurable_bII1F_fixX {n : ℕ} {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) (i j : Fin n)
    (u : E3) : AEMeasurable (fun q : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3 =>
      bII1F Θ i j q.1 q.2 u) := by
  have h := measurable_bII1Ins_comp
    (Y := ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) i j (x' := fun q => q.1)
    (a := fun q => q.2) (b := fun _ => u) measurable_fst measurable_snd measurable_const
  exact ((hΘ.comp h).enorm.pow_const 2).aemeasurable

/-- Measurability of `(x', u) ↦ ∫⁻ y, ‖Θ (x' , y, u)‖²`, the form needed for the outer swap. -/
lemma aemeasurable_bII1F_int {n : ℕ} {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) (i j : Fin n)
    (u : E3) : AEMeasurable (fun x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3 =>
      ∫⁻ y : E3, bII1F Θ i j x' y u) :=
  AEMeasurable.lintegral_prod_right'
    (μ := (volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3))) (ν := (volume : Measure E3))
    (f := fun q : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3 => bII1F Θ i j q.1 q.2 u)
    (aemeasurable_bII1F_fixX hΘ i j u)

/-- Measurability of `(x', u) ↦ ∫⁻ y, ‖Θ (x' , y, u)‖²` jointly in `(x', u)`. -/
lemma aemeasurable_bII1F_int2 {n : ℕ} {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) (i j : Fin n) :
    AEMeasurable (fun q : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3 =>
      ∫⁻ y : E3, bII1F Θ i j q.1 y q.2) :=
  AEMeasurable.lintegral_prod_right'
    (μ := (volume : Measure (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3)))
    (ν := (volume : Measure E3))
    (f := fun q : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3 =>
      bII1F Θ i j q.1.1 q.2 q.1.2)
    (by
      have h := measurable_bII1Ins_comp
        (Y := (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3)
        i j (x' := fun q => q.1.1) (a := fun q => q.2) (b := fun q => q.1.2)
        (by fun_prop) (by fun_prop) (by fun_prop)
      exact ((hΘ.comp h).enorm.pow_const 2).aemeasurable)


/-! ## The `L²` computations -/

/-- The `(a,b)`-double integral of the `A`-weights. -/
lemma lintegral_double_A {A : E3 → ℂ} (hA : Measurable A) (c : ℝ≥0∞) :
    (∫⁻ a : E3, ∫⁻ b : E3, (‖A a‖ₑ ^ 2 * ‖A b‖ₑ ^ 2) * c)
      = (∫⁻ a : E3, ‖A a‖ₑ ^ 2) * (∫⁻ b : E3, ‖A b‖ₑ ^ 2) * c := by
  have hf : AEMeasurable (fun q : E3 × E3 => (‖A q.1‖ₑ ^ 2 * ‖A q.2‖ₑ ^ 2) * c)
      (volume.prod volume) := by fun_prop
  have hf2 : AEMeasurable (fun q : E3 × E3 => ‖A q.1‖ₑ ^ 2 * ‖A q.2‖ₑ ^ 2)
      (volume.prod volume) := by fun_prop
  rw [lintegral_lintegral (f := fun a b : E3 => (‖A a‖ₑ ^ 2 * ‖A b‖ₑ ^ 2) * c) ?_]
  · rw [lintegral_mul_const'' c hf2]
    rw [lintegral_prod (f := fun q : E3 × E3 => ‖A q.1‖ₑ ^ 2 * ‖A q.2‖ₑ ^ 2) hf2]
    simp only []
    rw [lintegral_lintegral_mul (f := fun a : E3 => ‖A a‖ₑ ^ 2)
      (g := fun b : E3 => ‖A b‖ₑ ^ 2) (by fun_prop) (by fun_prop)]
  · exact hf

lemma lintegral_bII1L2 {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (hsubst : ∀ (g : (Fin n → E3) → ℝ≥0∞), AEMeasurable g →
      (∫⁻ x, g x) = ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3, ∫⁻ a, ∫⁻ b,
        g (bII1Ins i j x' a b))
    {Θ : (Fin n → E3) → ℂ} {A : E3 → ℂ} (hΘ : Measurable Θ) (hA : Measurable A) (y u : E3) :
    (∫⁻ x : Fin n → E3, ‖bII1L2 Θ A i j y u x‖ₑ ^ 2)
      = (∫⁻ a : E3, ‖A a‖ₑ ^ 2) ^ 2 * bII1S Θ i j y u := by
  rw [lintegral_congr (fun x => enorm_bII1L2 Θ A i j y u x)]
  rw [hsubst _ (aemeasurable_substIntegrand hΘ hA i j y u)]
  have hpt : ∀ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3,
      (∫⁻ a : E3, ∫⁻ b : E3, ‖A (bII1Ins i j x' a b i)‖ₑ ^ 2
          * ‖A (bII1Ins i j x' a b j)‖ₑ ^ 2
          * ‖Θ (Function.update (Function.update (bII1Ins i j x' a b) i y) j u)‖ₑ ^ 2)
        = (∫⁻ a : E3, ‖A a‖ₑ ^ 2) * (∫⁻ b : E3, ‖A b‖ₑ ^ 2) * bII1F Θ i j x' y u := by
    intro x'
    rw [show (∫⁻ a : E3, ∫⁻ b : E3, ‖A (bII1Ins i j x' a b i)‖ₑ ^ 2
            * ‖A (bII1Ins i j x' a b j)‖ₑ ^ 2
            * ‖Θ (Function.update (Function.update (bII1Ins i j x' a b) i y) j u)‖ₑ ^ 2)
          = ∫⁻ a : E3, ∫⁻ b : E3,
              (‖A a‖ₑ ^ 2 * ‖A b‖ₑ ^ 2) * bII1F Θ i j x' y u from by
      refine lintegral_congr fun a => ?_
      refine lintegral_congr fun b => ?_
      show ‖A (bII1Ins i j x' a b i)‖ₑ ^ 2 * ‖A (bII1Ins i j x' a b j)‖ₑ ^ 2
          * ‖Θ (Function.update (Function.update (bII1Ins i j x' a b) i y) j u)‖ₑ ^ 2
        = (‖A a‖ₑ ^ 2 * ‖A b‖ₑ ^ 2) * bII1F Θ i j x' y u
      rw [bII1Ins_i, bII1Ins_j hij, bII1Ins_update hij]
      rfl]
    exact lintegral_double_A hA (bII1F Θ i j x' y u)
  rw [lintegral_congr hpt]
  rw [lintegral_const_mul'' ((∫⁻ a : E3, ‖A a‖ₑ ^ 2) * (∫⁻ b : E3, ‖A b‖ₑ ^ 2))
    (aemeasurable_bII1F_x' hΘ i j y u)]
  rw [show (∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3, bII1F Θ i j x' y u)
      = bII1S Θ i j y u from rfl]
  ring

/-- The `x'`-fibre mass integrates to `‖Θ‖²`. -/
lemma lintegral_bII1S {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (hsubst : ∀ (g : (Fin n → E3) → ℝ≥0∞), AEMeasurable g →
      (∫⁻ x, g x) = ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3, ∫⁻ a, ∫⁻ b,
        g (bII1Ins i j x' a b))
    {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) :
    (∫⁻ u : E3, ∫⁻ y : E3, bII1S Θ i j y u) = ∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2 := by
  have h1 : (∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2)
      = ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3, ∫⁻ y : E3, ∫⁻ u : E3,
          bII1F Θ i j x' y u := by
    rw [hsubst (fun x => ‖Θ x‖ₑ ^ 2) ((hΘ.enorm.pow_const 2).aemeasurable)]
    rfl
  rw [h1]
  have s1 : (∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3, ∫⁻ y : E3, ∫⁻ u : E3,
        bII1F Θ i j x' y u)
      = ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3, ∫⁻ u : E3, ∫⁻ y : E3,
          bII1F Θ i j x' y u := by
    refine lintegral_congr_ae (Eventually.of_forall (fun x' => ?_))
    exact lintegral_lintegral_swap (aemeasurable_bII1F_fix hΘ i j x')
  have s2 : (∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3, ∫⁻ u : E3, ∫⁻ y : E3,
        bII1F Θ i j x' y u)
      = ∫⁻ u : E3, ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3, ∫⁻ y : E3,
          bII1F Θ i j x' y u :=
    lintegral_lintegral_swap (μ := (volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3)))
      (ν := (volume : Measure E3)) (f := fun x' u => ∫⁻ y : E3, bII1F Θ i j x' y u)
      (aemeasurable_bII1F_int2 hΘ i j)
  have s3 : (∫⁻ u : E3, ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3, ∫⁻ y : E3,
        bII1F Θ i j x' y u)
      = ∫⁻ u : E3, ∫⁻ y : E3, ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3,
          bII1F Θ i j x' y u := by
    refine lintegral_congr_ae (Eventually.of_forall (fun u => ?_))
    exact lintegral_lintegral_swap (f := fun x' y => bII1F Θ i j x' y u)
      (by
        have h := measurable_bII1Ins_comp
          (Y := ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) i j (x' := fun q => q.1)
          (a := fun q => q.2) (b := fun _ => u) measurable_fst measurable_snd measurable_const
        exact ((hΘ.comp h).enorm.pow_const 2).aemeasurable)
  rw [s1, s2, s3]
  rfl

/-! ## The pointwise Cauchy–Schwarz bound -/

/-- Cauchy–Schwarz in the `x`-integral, with the `A`-weighted split of the integrand. -/
lemma enorm_integral_le_bII1 {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (hsubst : ∀ (g : (Fin n → E3) → ℝ≥0∞), AEMeasurable g →
      (∫⁻ x, g x) = ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3, ∫⁻ a, ∫⁻ b,
        g (bII1Ins i j x' a b))
    {Θ : (Fin n → E3) → ℂ} {A : E3 → ℂ} (hΘ : Measurable Θ) (hA : Measurable A) (y u : E3) :
    ‖∫ x : Fin n → E3, (starRingEnd ℂ) (Θ x) * A (x i) * A (x j)
        * Θ (Function.update (Function.update x i y) j u)‖ₑ ^ 2
      ≤ (∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2)
        * ((∫⁻ a : E3, ‖A a‖ₑ ^ 2) ^ 2 * bII1S Θ i j y u) := by
  have hCS := enorm_integral_conj_mul_sq_le (μ := (volume : Measure (Fin n → E3)))
    (v := fun x => starRingEnd ℂ (bII1H1 Θ A i j x))
    (Λ := fun x => bII1L2 Θ A i j y u x)
    (aemeasurable_bII1H1_star hΘ hA i j) (aemeasurable_bII1L2 hΘ hA i j y u)
  have hint : (∫ z, (starRingEnd ℂ) ((starRingEnd ℂ) (bII1H1 Θ A i j z))
        * bII1L2 Θ A i j y u z)
      = ∫ z, ((starRingEnd ℂ) (Θ z) * A (z i) * A (z j)
          * Θ (Function.update (Function.update z i y) j u)) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show (starRingEnd ℂ) ((starRingEnd ℂ) (bII1H1 Θ A i j z)) * bII1L2 Θ A i j y u z
      = (starRingEnd ℂ) (Θ z) * A (z i) * A (z j)
          * Θ (Function.update (Function.update z i y) j u)
    rw [show (starRingEnd ℂ) ((starRingEnd ℂ) (bII1H1 Θ A i j z)) = bII1H1 Θ A i j z
      from star_star (bII1H1 Θ A i j z), bII1H1_mul_bII1L2]
  have hnorm : (∫⁻ z, ‖starRingEnd ℂ (bII1H1 Θ A i j z)‖ₑ ^ 2)
      = ∫⁻ z, ‖bII1H1 Θ A i j z‖ₑ ^ 2 := by
    refine lintegral_congr fun z => ?_
    show ‖starRingEnd ℂ (bII1H1 Θ A i j z)‖ₑ ^ 2 = ‖bII1H1 Θ A i j z‖ₑ ^ 2
    rw [show ‖starRingEnd ℂ (bII1H1 Θ A i j z)‖ₑ = ‖bII1H1 Θ A i j z‖ₑ from by simp]
  rw [hint, hnorm] at hCS
  refine hCS.trans ?_
  refine mul_le_mul' (lintegral_mono (fun z => enorm_bII1H1_sq_le Θ A i j z)) ?_
  rw [lintegral_bII1L2 hij hsubst hΘ hA y u]

/-! ## Passage from `lintegral`s back to the Bochner integral -/

lemma integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) : (∫ a, f a ∂μ) ≤ (∫⁻ a, ENNReal.ofReal (f a) ∂μ).toReal := by
  by_cases h : Integrable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae hf h.1]
  · rw [integral_undef h]; exact ENNReal.toReal_nonneg

lemma integral_le_of_lintegral_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β → ℝ} (hf : ∀ a b, 0 ≤ f a b) {c : ℝ}
    (hc : 0 ≤ c)
    (h : (∫⁻ a, ∫⁻ b, ENNReal.ofReal (f a b) ∂ν ∂μ) ≤ ENNReal.ofReal c) :
    (∫ a, ∫ b, f a b ∂ν ∂μ) ≤ c := by
  have h1 : ∀ a, (∫ b, f a b ∂ν) ≤ (∫⁻ b, ENNReal.ofReal (f a b) ∂ν).toReal :=
    fun a => integral_le_lintegral_ofReal (Eventually.of_forall (hf a))
  have h2 : ∀ a, ENNReal.ofReal (∫ b, f a b ∂ν) ≤ ∫⁻ b, ENNReal.ofReal (f a b) ∂ν :=
    fun a => (ENNReal.ofReal_le_ofReal (h1 a)).trans ENNReal.ofReal_toReal_le
  have htop : (∫⁻ a, ∫⁻ b, ENNReal.ofReal (f a b) ∂ν ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  calc (∫ a, ∫ b, f a b ∂ν ∂μ)
      ≤ (∫⁻ a, ENNReal.ofReal (∫ b, f a b ∂ν) ∂μ).toReal :=
        integral_le_lintegral_ofReal (Eventually.of_forall fun a => integral_nonneg (hf a))
    _ ≤ (∫⁻ a, ∫⁻ b, ENNReal.ofReal (f a b) ∂ν ∂μ).toReal :=
        ENNReal.toReal_mono htop (lintegral_mono h2)
    _ ≤ (ENNReal.ofReal c).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = c := ENNReal.toReal_ofReal hc

/-! ## The bound, measurable case -/

theorem bII1_bound {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (hsubst : ∀ (g : (Fin n → E3) → ℝ≥0∞), AEMeasurable g →
      (∫⁻ x, g x) = ∫⁻ x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3, ∫⁻ a, ∫⁻ b,
        g (bII1Ins p.1 p.2 x' a b))
    {Θ : (Fin n → E3) → ℂ} {A : E3 → ℂ} (hΘ : Measurable Θ) (hA : Measurable A)
    (hΘL : Integrable (fun x => ‖Θ x‖ ^ 2)) (hAL : Integrable (fun x => ‖A x‖ ^ 2)) :
    (∫ u : E3, ∫ y : E3, ‖∫ x : Fin n → E3, (starRingEnd ℂ) (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ^ 2)
      ≤ (∫ x, ‖A x‖ ^ 2) ^ 2 * (∫ x, ‖Θ x‖ ^ 2) ^ 2 := by
  have hKθ : (∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2) = ENNReal.ofReal (∫ x, ‖Θ x‖ ^ 2) :=
    ((MeasureTheory.ofReal_integral_eq_lintegral_ofReal hΘL
        (Eventually.of_forall fun x => sq_nonneg _)).trans
      (lintegral_congr fun x => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm])).symm
  have hKA : (∫⁻ a : E3, ‖A a‖ₑ ^ 2) = ENNReal.ofReal (∫ x, ‖A x‖ ^ 2) :=
    ((MeasureTheory.ofReal_integral_eq_lintegral_ofReal hAL
        (Eventually.of_forall fun x => sq_nonneg _)).trans
      (lintegral_congr fun x => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm])).symm
  refine integral_le_of_lintegral_le (f := fun u y : E3 => ‖∫ x : Fin n → E3,
      (starRingEnd ℂ) (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ^ 2)
    (fun u y => sq_nonneg _) (by positivity) ?_
  have hconv : ∀ y u : E3, ENNReal.ofReal (‖∫ x : Fin n → E3, (starRingEnd ℂ) (Θ x)
      * A (x p.1) * A (x p.2) * Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ^ 2)
      = ‖∫ x : Fin n → E3, (starRingEnd ℂ) (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)‖ₑ ^ 2 := by
    intro y u
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp only [hconv]
  calc (∫⁻ u : E3, ∫⁻ y : E3, ‖∫ x : Fin n → E3, (starRingEnd ℂ) (Θ x) * A (x p.1)
          * A (x p.2) * Θ (Function.update (Function.update x p.1 y) p.2 u)‖ₑ ^ 2)
      ≤ ∫⁻ u : E3, ∫⁻ y : E3, (∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2)
          * ((∫⁻ a : E3, ‖A a‖ₑ ^ 2) ^ 2 * bII1S Θ p.1 p.2 y u) :=
        lintegral_mono fun u => lintegral_mono fun y =>
          enorm_integral_le_bII1 hp hsubst hΘ hA y u
    _ = ((∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2) * (∫⁻ a : E3, ‖A a‖ₑ ^ 2) ^ 2)
          * ∫⁻ u : E3, ∫⁻ y : E3, bII1S Θ p.1 p.2 y u := by
        rw [show (fun u : E3 => ∫⁻ y : E3, (∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2)
              * ((∫⁻ a : E3, ‖A a‖ₑ ^ 2) ^ 2 * bII1S Θ p.1 p.2 y u))
            = fun u : E3 =>
                ((∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2) * (∫⁻ a : E3, ‖A a‖ₑ ^ 2) ^ 2)
                  * ∫⁻ y : E3, bII1S Θ p.1 p.2 y u from by
          funext u
          rw [show (fun y : E3 => (∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2)
                * ((∫⁻ a : E3, ‖A a‖ₑ ^ 2) ^ 2 * bII1S Θ p.1 p.2 y u))
              = fun y : E3 =>
                  ((∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2) * (∫⁻ a : E3, ‖A a‖ₑ ^ 2) ^ 2)
                    * bII1S Θ p.1 p.2 y u from by
            funext y
            rw [mul_assoc]]
          rw [lintegral_const_mul'' (((∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2)
            * (∫⁻ a : E3, ‖A a‖ₑ ^ 2) ^ 2)) (aemeasurable_bII1S_fix hΘ p.1 p.2 u)]]
        rw [lintegral_const_mul'' (((∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2)
          * (∫⁻ a : E3, ‖A a‖ₑ ^ 2) ^ 2)) (aemeasurable_bII1S_int hΘ p.1 p.2)]
    _ = ((∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2) * (∫⁻ a : E3, ‖A a‖ₑ ^ 2) ^ 2)
          * (∫⁻ x : Fin n → E3, ‖Θ x‖ₑ ^ 2) := by
        rw [lintegral_bII1S hp hsubst hΘ]
    _ = ENNReal.ofReal ((∫ x, ‖A x‖ ^ 2) ^ 2 * (∫ x, ‖Θ x‖ ^ 2) ^ 2) := by
        rw [hKθ, hKA]
        rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ ∫ x, ‖A x‖ ^ 2)]
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ∫ x, ‖Θ x‖ ^ 2)]
        rw [← ENNReal.ofReal_mul (by positivity :
          (0:ℝ) ≤ (∫ x, ‖Θ x‖ ^ 2) * (∫ x, ‖A x‖ ^ 2) ^ 2)]
        congr 1
        ring


/-! ## The target -/

theorem blockII1_fibre_L2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘm : MeasureTheory.AEStronglyMeasurable Θ)
    (hΘL : MeasureTheory.Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAm : MeasureTheory.AEStronglyMeasurable A)
    (hAL : MeasureTheory.Integrable (fun x => ‖A x‖ ^ 2)) :
    ∫ u : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        ‖∫ x : Work.BoseDict.Xn n,
          (starRingEnd ℂ) (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ^ 2
      ≤ (∫ x, ‖A x‖ ^ 2) ^ 2 * (∫ x, ‖Θ x‖ ^ 2) ^ 2 := by
  obtain ⟨Θ', hΘ'm, hΘ'eq⟩ := hΘm.aemeasurable
  obtain ⟨A', hA'm, hA'eq⟩ := hAm.aemeasurable
  have hΘ'ae : Θ =ᵐ[(volume : Measure (Work.BoseDict.Xn n))] Θ' :=
    MeasureTheory.ae_iff.mpr hΘ'eq
  have hA'ae : A =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 3)))] A' :=
    MeasureTheory.ae_iff.mpr hA'eq
  have hΘ'L : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n => ‖Θ' x‖ ^ 2) := by
    refine hΘL.congr ?_
    filter_upwards [hΘ'ae] with x hx
    rw [hx]
  have hA'L : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖A' x‖ ^ 2) := by
    refine hAL.congr ?_
    filter_upwards [hA'ae] with x hx
    rw [hx]
  have hA2 : (∫ x : EuclideanSpace ℝ (Fin 3), ‖A x‖ ^ 2)
      = ∫ x : EuclideanSpace ℝ (Fin 3), ‖A' x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hA'ae] with x hx
    rw [hx]
  have hΘ2 : (∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2)
      = ∫ x : Work.BoseDict.Xn n, ‖Θ' x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hΘ'ae] with x hx
    rw [hx]
  rw [LHS_ae_congr p hp hΘ'ae hA'ae, hA2, hΘ2]
  exact bII1_bound p hp (fun g hg => lintegral_insSplit hp g hg) hΘ'm hA'm hΘ'L hA'L

end

end Work.BoseBoxFock
