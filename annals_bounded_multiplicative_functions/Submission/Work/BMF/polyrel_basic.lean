import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.poly_growth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

namespace Work.BMF


/-- `dil` is multiplicative in the dilation factor. -/
lemma dil_mul {a b : ℝ} {P : ℝ[X]} : dil a (dil b P) = dil (a * b) P := by
  rw [dil, dil, dil, Polynomial.comp_assoc]
  congr 1
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc,
    mul_comm (Polynomial.C b) (Polynomial.C a), ← Polynomial.C_mul]

section IntegralOn

lemma IntegralOn.zero (δ : ℝ) : IntegralOn δ (0 : ℝ[X]) := by
  intro n; exact ⟨0, by simp⟩

lemma IntegralOn.add {δ : ℝ} {γ₁ γ₂ : ℝ[X]} (h₁ : IntegralOn δ γ₁) (h₂ : IntegralOn δ γ₂) :
    IntegralOn δ (γ₁ + γ₂) := by
  intro n
  obtain ⟨m₁, hm₁⟩ := h₁ n
  obtain ⟨m₂, hm₂⟩ := h₂ n
  exact ⟨m₁ + m₂, by simp [eval_add, hm₁, hm₂]⟩

lemma IntegralOn.neg {δ : ℝ} {γ : ℝ[X]} (h : IntegralOn δ γ) : IntegralOn δ (-γ) := by
  intro n
  obtain ⟨m, hm⟩ := h n
  exact ⟨-m, by simp [hm]⟩

lemma IntegralOn.sub {δ : ℝ} {γ₁ γ₂ : ℝ[X]} (h₁ : IntegralOn δ γ₁) (h₂ : IntegralOn δ γ₂) :
    IntegralOn δ (γ₁ - γ₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

lemma IntegralOn.int_mul {δ : ℝ} {γ : ℝ[X]} (m : ℤ) (h : IntegralOn δ γ) :
    IntegralOn ((m : ℝ) * δ) γ := by
  intro n
  obtain ⟨k, hk⟩ := h (m * n)
  refine ⟨k, ?_⟩
  rw [← hk]
  congr 1
  push_cast
  ring

lemma IntegralOn.dilate {δ a : ℝ} {γ : ℝ[X]} (h : IntegralOn δ γ) (ha : a ≠ 0) :
    IntegralOn (δ / a) (dil a γ) := by
  intro n
  obtain ⟨m, hm⟩ := h n
  refine ⟨m, ?_⟩
  have key : a * ((δ / a) * n) = δ * n := by field_simp
  rw [dil, eval_comp]
  simp only [eval_mul, eval_C, eval_X]
  rw [key, hm]

end IntegralOn

section Degree

lemma dil_mem_degreeLE {a : ℝ} {k : ℕ} {P : ℝ[X]} (hP : P ∈ degreeLE ℝ (k : WithBot ℕ)) :
    dil a P ∈ degreeLE ℝ (k : WithBot ℕ) := by
  rw [mem_degreeLE] at hP ⊢
  rw [dil]
  rcases eq_or_ne a 0 with rfl | ha
  · have h0 : (Polynomial.C (0:ℝ) * Polynomial.X) = 0 := by simp
    rw [h0, Polynomial.comp_zero]
    exact le_trans Polynomial.degree_C_le (by simp)
  · have hq : (Polynomial.C a * Polynomial.X).degree = (1 : WithBot ℕ) := by
      simpa using Polynomial.degree_C_mul_X_pow 1 ha
    have hpos : (0 : WithBot ℕ) < (Polynomial.C a * Polynomial.X).degree := by rw [hq]; norm_num
    rw [Polynomial.degree_comp (p := P) (q := Polynomial.C a * Polynomial.X) hpos, hq, mul_one]
    exact hP

end Degree

section PolyRelConst

/-- Constant produced by `PolyRel.trans`. -/
noncomputable def transConst (k : ℕ) (C₁ C₂ : ℝ) : ℝ :=
  C₁ + C₁ * C₂ + C₂ * (((k : ℝ) + 1) * ((k : ℝ) * (C₁ * C₁ + C₁ + 1) + 1) ^ k) + 1

lemma transConst_pos {k : ℕ} {C₁ C₂ : ℝ} (h₁ : 0 < C₁) (h₂ : 0 < C₂) :
    0 < transConst k C₁ C₂ := by
  have hG : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) * (C₁ * C₁ + C₁ + 1) + 1) ^ k := by positivity
  unfold transConst
  nlinarith [h₁, h₂, mul_nonneg h₂.le hG, mul_nonneg h₁.le h₂.le]

lemma le_transConst_self {k : ℕ} {C₁ C₂ : ℝ} (h₁ : 0 < C₁) (h₂ : 0 < C₂) :
    C₁ ≤ transConst k C₁ C₂ := by
  have hG : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) * (C₁ * C₁ + C₁ + 1) + 1) ^ k := by positivity
  unfold transConst
  nlinarith [h₁, h₂, mul_nonneg h₂.le hG, mul_nonneg h₁.le h₂.le]

lemma mul_le_transConst {k : ℕ} {C₁ C₂ : ℝ} (h₁ : 0 < C₁) (h₂ : 0 < C₂) :
    C₁ * C₂ ≤ transConst k C₁ C₂ := by
  have hG : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) * (C₁ * C₁ + C₁ + 1) + 1) ^ k := by positivity
  unfold transConst
  nlinarith [h₁, h₂, mul_nonneg h₂.le hG]

lemma add_mul_self_le_transConst {k : ℕ} {C₁ C₂ : ℝ} (h₁ : 0 < C₁) (h₂ : 0 < C₂) :
    C₁ + C₂ * C₁ ≤ transConst k C₁ C₂ := by
  have hG : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) * (C₁ * C₁ + C₁ + 1) + 1) ^ k := by positivity
  unfold transConst
  nlinarith [h₁, h₂, mul_nonneg h₂.le hG]

lemma add_mul_le_transConst {k : ℕ} {C₁ C₂ : ℝ} (h₁ : 0 < C₁) (h₂ : 0 < C₂) :
    C₁ + C₂ * (((k : ℝ) + 1) * ((k : ℝ) * (C₁ * C₁ + C₁ + 1) + 1) ^ k) ≤ transConst k C₁ C₂ := by
  have hG : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) * (C₁ * C₁ + C₁ + 1) + 1) ^ k := by positivity
  unfold transConst
  nlinarith [h₁, h₂, mul_nonneg h₁.le h₂.le]

/-- Constant produced by `PolyRel.symm`. -/
noncomputable def symmConst (k : ℕ) (C : ℝ) : ℝ :=
  C + C * C + C * (((k : ℝ) + 1) * ((k : ℝ) * (2 * C + 1) + 1) ^ k) + 1


lemma symmConst_pos {k : ℕ} {C : ℝ} (hC : 0 < C) : 0 < symmConst k C := by
  have hG : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) * (2 * C + 1) + 1) ^ k := by positivity
  unfold symmConst
  nlinarith [hC, mul_nonneg hC.le hG, mul_nonneg hC.le hC.le]

lemma symmConst_ge_self {k : ℕ} {C : ℝ} (hC : 0 < C) : C ≤ symmConst k C := by
  have hG : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) * (2 * C + 1) + 1) ^ k := by positivity
  unfold symmConst
  nlinarith [hC, mul_nonneg hC.le hG, mul_nonneg hC.le hC.le]

lemma sq_le_symmConst {k : ℕ} {C : ℝ} (hC : 0 < C) : C * C ≤ symmConst k C := by
  have hG : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) * (2 * C + 1) + 1) ^ k := by positivity
  unfold symmConst
  nlinarith [hC, mul_nonneg hC.le hG]

lemma mul_le_symmConst {k : ℕ} {C : ℝ} (hC : 0 < C) :
    C * (((k : ℝ) + 1) * ((k : ℝ) * (2 * C + 1) + 1) ^ k) ≤ symmConst k C := by
  have hG : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) * (2 * C + 1) + 1) ^ k := by positivity
  unfold symmConst
  nlinarith [hC, mul_nonneg hC.le hC.le]

end PolyRelConst

section PolyRel

variable {k : ℕ} {C C₁ C₂ C' δ : ℝ} {x₁ L₁ x₂ L₂ x₃ L₃ : ℝ} {P₁ P₂ P₃ : ℝ[X]} {a : ℝ}

lemma PolyRel.mono (h : PolyRel k C δ x₁ L₁ P₁ x₂ L₂ P₂) (hCC' : C ≤ C')
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    PolyRel k C' δ x₁ L₁ P₁ x₂ L₂ P₂ := by
  obtain ⟨h1, h2, h3, ε, γ, hε, hγ, heq, hbdd, hint⟩ := h
  exact ⟨le_trans h1 (by nlinarith), le_trans h2 (by nlinarith), le_trans h3 (by nlinarith),
    ε, γ, hε, hγ, heq, fun t ht => le_trans (hbdd t ht) hCC', hint⟩

/-- Dilation invariance: pushing forward by `(1/a)_*` keeps the constant. -/
lemma PolyRel.dilate (h : PolyRel k C δ x₁ L₁ P₁ x₂ L₂ P₂) (ha : 0 < a) :
    PolyRel k C (δ / a) (x₁ / a) (L₁ / a) (dil a P₁) (x₂ / a) (L₂ / a) (dil a P₂) := by
  obtain ⟨h1, h2, h3, ε, γ, hε, hγ, heq, hbdd, hint⟩ := h
  have ha' : a ≠ 0 := ne_of_gt ha
  refine ⟨?_, ?_, ?_, dil a ε, dil a γ, dil_mem_degreeLE hε, dil_mem_degreeLE hγ, ?_, ?_, ?_⟩
  · rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h1 (le_of_lt ha)
  · rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h2 (le_of_lt ha)
  · rw [← sub_div, abs_div, abs_of_pos ha, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right h3 (le_of_lt ha)
  · rw [heq]; simp only [dil, Polynomial.add_comp]
  · intro t ht
    rw [dil, eval_comp]
    simp only [eval_mul, eval_C, eval_X]
    refine hbdd (a * t) ?_
    rw [Set.mem_Icc] at ht ⊢
    constructor
    · have h := (div_le_iff₀ ha).mp ht.1
      nlinarith [h, ha]
    · have h := ht.2
      rw [← add_div] at h
      rw [le_div_iff₀ ha] at h
      nlinarith [h, ha]
  · simpa [dil] using hint.dilate ha'

/-- Sparsification: replacing `δ` by an integer multiple keeps the constant. -/
lemma PolyRel.sparsify (m : ℕ) (h : PolyRel k C δ x₁ L₁ P₁ x₂ L₂ P₂) :
    PolyRel k C ((m : ℝ) * δ) x₁ L₁ P₁ x₂ L₂ P₂ := by
  obtain ⟨h1, h2, h3, ε, γ, hε, hγ, heq, hbdd, hint⟩ := h
  exact ⟨h1, h2, h3, ε, γ, hε, hγ, heq, hbdd, hint.int_mul m⟩

/-- Symmetry of `~_δ`. -/
lemma PolyRel.symm (h : PolyRel k C δ x₁ L₁ P₁ x₂ L₂ P₂) (hC : 0 < C) (hL₁ : 0 < L₁)
    (hL₂ : 0 < L₂) :
    PolyRel k (symmConst k C) δ x₂ L₂ P₂ x₁ L₁ P₁ := by
  obtain ⟨h1, h2, h3, ε, γ, hε, hγ, heq, hbdd, hint⟩ := h
  have hC' : C ≤ symmConst k C := symmConst_ge_self hC
  have hsq : C * C ≤ symmConst k C := sq_le_symmConst hC
  have hbig : C * (((k : ℝ) + 1) * ((k : ℝ) * (2 * C + 1) + 1) ^ k) ≤ symmConst k C :=
    mul_le_symmConst hC
  refine ⟨?_, ?_, ?_, -ε, -γ, Submodule.neg_mem _ hε, Submodule.neg_mem _ hγ, ?_, ?_, hint.neg⟩
  · nlinarith [h2, hC', hL₁]
  · nlinarith [h1, hC', hL₂]
  · have h3' : |x₂ - x₁| ≤ C * C * L₂ := by
      rw [abs_sub_comm]
      nlinarith [h3, h1, hC, hL₂]
    nlinarith [h3', hsq, hL₂]
  · show P₂ = -ε + P₁ + -γ
    rw [heq]; ring
  · intro t ht
    rw [eval_neg, abs_neg]
    have hb : |t - x₁| ≤ 2 * C * L₁ := by
      rw [Set.mem_Icc] at ht
      have h2' : |t - x₂| ≤ L₂ := by
        rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have htri : |t - x₁| ≤ |t - x₂| + |x₂ - x₁| := by
        rw [show t - x₁ = (t - x₂) + (x₂ - x₁) by ring]; exact abs_add_le _ _
      have h3' : |x₂ - x₁| ≤ C * L₁ := by simpa [abs_sub_comm] using h3
      nlinarith [htri, h2', h3', hC, h2, hL₁]
    have hpg := poly_growth k C (2 * C) x₁ L₁ hL₁ (le_of_lt hC) (by positivity) ε hε hbdd t hb
    linarith [hpg, hbig]

/-- Transitivity of `~_δ`. -/
lemma PolyRel.trans (h₁ : PolyRel k C₁ δ x₁ L₁ P₁ x₂ L₂ P₂) (h₂ : PolyRel k C₂ δ x₂ L₂ P₂ x₃ L₃ P₃)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃) :
    PolyRel k (transConst k C₁ C₂) δ x₁ L₁ P₁ x₃ L₃ P₃ := by
  obtain ⟨h11, h12, h13, ε₁, γ₁, hε₁, hγ₁, heq₁, hb₁, hi₁⟩ := h₁
  obtain ⟨h21, h22, h23, ε₂, γ₂, hε₂, hγ₂, heq₂, hb₂, hi₂⟩ := h₂
  have hC₁C₂ : C₁ * C₂ ≤ transConst k C₁ C₂ := mul_le_transConst hC₁ hC₂
  refine ⟨?_, ?_, ?_, ε₁ + ε₂, γ₁ + γ₂, Submodule.add_mem _ hε₁ hε₂, Submodule.add_mem _ hγ₁ hγ₂, ?_, ?_, hi₁.add hi₂⟩
  · calc L₁ ≤ C₁ * L₂ := h11
      _ ≤ C₁ * (C₂ * L₃) := by nlinarith [hC₁, h21]
      _ = C₁ * C₂ * L₃ := by ring
      _ ≤ transConst k C₁ C₂ * L₃ := by nlinarith [hC₁C₂, hL₃]
  · calc L₃ ≤ C₂ * L₂ := h22
      _ ≤ C₂ * (C₁ * L₁) := by nlinarith [hC₂, h12]
      _ = C₁ * C₂ * L₁ := by ring
      _ ≤ transConst k C₁ C₂ * L₁ := by nlinarith [hC₁C₂, hL₁]
  · have h3 : |x₁ - x₃| ≤ C₁ * L₁ + C₂ * (C₁ * L₁) := by
      have htri : |x₁ - x₃| ≤ |x₁ - x₂| + |x₂ - x₃| := by
        rw [show x₁ - x₃ = (x₁ - x₂) + (x₂ - x₃) by ring]; exact abs_add_le _ _
      nlinarith [htri, h13, h23, h12, hC₂, hL₁]
    nlinarith [h3, add_mul_self_le_transConst (k := k) hC₁ hC₂, hL₁]
  · show P₁ = ε₁ + ε₂ + P₃ + (γ₁ + γ₂)
    rw [heq₁, heq₂]; ring
  · intro t ht
    rw [eval_add]
    have hG : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) * (C₁ * C₁ + C₁ + 1) + 1) ^ k := by positivity
    have hb₂' : |ε₂.eval t| ≤ C₂ * (((k : ℝ) + 1) * ((k : ℝ) * (C₁ * C₁ + C₁ + 1) + 1) ^ k) := by
      have hdist : |t - x₂| ≤ (C₁ * C₁ + C₁) * L₂ := by
        rw [Set.mem_Icc] at ht
        have ht1 : |t - x₁| ≤ L₁ := by rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have htri : |t - x₂| ≤ |t - x₁| + |x₁ - x₂| := by
          rw [show t - x₂ = (t - x₁) + (x₁ - x₂) by ring]; exact abs_add_le _ _
        nlinarith [htri, ht1, h13, h11, hC₁, hL₂]
      have h := poly_growth k C₂ (C₁ * C₁ + C₁) x₂ L₂ hL₂ (le_of_lt hC₂) (by positivity)
        ε₂ hε₂ hb₂ t hdist
      rwa [mul_assoc] at h
    calc |ε₁.eval t + ε₂.eval t| ≤ |ε₁.eval t| + |ε₂.eval t| := abs_add_le _ _
      _ ≤ C₁ + C₂ * (((k : ℝ) + 1) * ((k : ℝ) * (C₁ * C₁ + C₁ + 1) + 1) ^ k) := by
          linarith [hb₁ t ht, hb₂']
      _ ≤ transConst k C₁ C₂ := add_mul_le_transConst (k := k) hC₁ hC₂

end PolyRel

end Work.BMF
