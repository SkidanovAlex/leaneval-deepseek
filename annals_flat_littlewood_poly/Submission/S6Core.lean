import Mathlib
import ChallengeDeps
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.Sec3_c_expand
import Submission.Sec3_c_bridge
import Submission.ArcFamily
import Submission.S5_defs
import Submission.S5_TheoremSine
import Submission.Sec3Cos
import Submission.QCover
import Submission.Consts
import Submission.F_Psum_stable
import Submission.TrigObservation

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

open FlatLittlewoodPoly

namespace Submission
namespace Flat

lemma eθ_re' (x : ℝ) : (Sec3.eθ x).re = Real.cos x := by
  unfold Sec3.eθ
  rw [Complex.exp_ofReal_mul_I]
  rw [Complex.add_re]
  rw [Complex.ofReal_re]
  rw [Complex.mul_re]
  rw [Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

lemma eθ_im' (x : ℝ) : (Sec3.eθ x).im = Real.sin x := by
  unfold Sec3.eθ
  rw [Complex.exp_ofReal_mul_I]
  rw [Complex.add_im]
  rw [Complex.ofReal_im]
  rw [Complex.mul_im]
  rw [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

lemma eθ_conj (x : ℝ) : starRingEnd ℂ (Sec3.eθ x) = Sec3.eθ (-x) := by
  unfold Sec3.eθ
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma eθ_add_neg (x : ℝ) : Sec3.eθ x + Sec3.eθ (-x) = ((2 * Real.cos x : ℝ) : ℂ) := by
  rw [← eθ_conj x]
  rw [Complex.add_conj]
  congr 1
  rw [eθ_re']

lemma eθ_sub_neg (x : ℝ) : Sec3.eθ x - Sec3.eθ (-x) = ((2 * Real.sin x : ℝ) : ℂ) * Complex.I := by
  rw [← eθ_conj x]
  rw [Complex.sub_conj]
  congr 1
  rw [eθ_im']

lemma eθ_neg_inv (x : ℝ) : Sec3.eθ (-x) = (Sec3.eθ x)⁻¹ := by
  unfold Sec3.eθ
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

lemma eθ_nat (n : ℕ) (x : ℝ) : Sec3.eθ ((n : ℝ) * x) = (Sec3.eθ x) ^ n :=
  Sec3BridgeAux.eθ_nat_mul n x

/-- `re` distributes over finite sums. -/
lemma sum_re {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum Complex.reAddGroupHom f s

/-- `im` distributes over finite sums. -/
lemma sum_im {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im :=
  map_sum Complex.imAddGroupHom f s

/-- For `a.im = 0`: `re(a·w) = a.re·w.re`. -/
lemma re_mul_of_im_zero (a w : ℂ) (ha : a.im = 0) : (a * w).re = a.re * w.re := by
  rw [Complex.mul_re, ha]
  ring

/-- For `a.im = 0`: `im(a·w) = a.re·w.im`. -/
lemma im_mul_of_im_zero (a w : ℂ) (ha : a.im = 0) : (a * w).im = a.re * w.im := by
  rw [Complex.mul_im, ha]
  ring

/-- For real `r`: `re(↑r·w) = r·w.re`, `im(↑r·w) = r·w.im`. -/
lemma re_ofReal_mul (r : ℝ) (w : ℂ) : ((r : ℂ) * w).re = r * w.re := by
  rw [Complex.mul_re]
  simp

lemma im_ofReal_mul (r : ℝ) (w : ℂ) : ((r : ℂ) * w).im = r * w.im := by
  rw [Complex.mul_im]
  simp

/-- Coefficients of `P s` below `2^s` are ±1 (complex); they have zero im part. -/
lemma coeff_Ps_im {s j : ℕ} (hj : j < 2 ^ s) : ((RudinShapiro.P s).coeff j).im = 0 := by
  rcases RudinShapiro.P_coeff_mem s j hj with h | h <;> rw [h] <;> norm_num



/-- All Rudin-Shapiro prefix coefficients are real. -/
lemma coeff_P_im_all (s j : ℕ) : ((RudinShapiro.P s).coeff j).im = 0 := by
  by_cases hj : j < 2 ^ s
  · rcases RudinShapiro.P_coeff_mem s j hj with h | h <;> rw [h] <;> norm_num
  · have hge : 2 ^ s ≤ j := le_of_not_gt hj
    rw [RudinShapiro.coeff_P_ge s j hge]
    norm_num

/-- Frequencies of the first cosine block. -/
def freq1 (t r : ℕ) : ℝ := 2 * ((Sec3H.T t + r : ℕ) : ℝ)
/-- Frequencies of the second cosine block. -/
def freq2 (t r : ℕ) : ℝ := 2 * ((2 * Sec3H.T t + r : ℕ) : ℝ)

lemma nat_freq1 (t r : ℕ) : ((2 * (Sec3H.T t + r) : ℕ) : ℝ) = freq1 t r := by
  unfold freq1
  push_cast
  ring

lemma nat_freq2 (t r : ℕ) : ((2 * (2 * Sec3H.T t + r) : ℕ) : ℝ) = freq2 t r := by
  unfold freq2
  push_cast
  ring

/-- Cosine positions `C'₁ := {T+r: r<2^t}`. -/
def C1 (t : ℕ) : Finset ℕ := (Finset.range (2 ^ t)).image (fun r => Sec3H.T t + r)
/-- Cosine positions `C'₂ := {2T+r: r<2^t}`. -/
def C2 (t : ℕ) : Finset ℕ := (Finset.range (2 ^ t)).image (fun r => 2 * Sec3H.T t + r)
/-- `C' = C'₁ ∪ C'₂`. -/
def Cp (t : ℕ) : Finset ℕ := C1 t ∪ C2 t

lemma mem_C1_iff {t : ℕ} (j : ℕ) : j ∈ C1 t ↔ ∃ r : ℕ, r < 2 ^ t ∧ j = Sec3H.T t + r := by
  unfold C1
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨r, hr, hrj⟩
    exact ⟨r, Finset.mem_range.mp hr, hrj.symm⟩
  · rintro ⟨r, hr, hrj⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, hrj.symm⟩

lemma mem_C2_iff {t : ℕ} (j : ℕ) : j ∈ C2 t ↔ ∃ r : ℕ, r < 2 ^ t ∧ j = 2 * Sec3H.T t + r := by
  unfold C2
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨r, hr, hrj⟩
    exact ⟨r, Finset.mem_range.mp hr, hrj.symm⟩
  · rintro ⟨r, hr, hrj⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, hrj.symm⟩

/-- `C1 t` and `C2 t` are disjoint. -/
lemma C1_disjoint_C2 (t : ℕ) : Disjoint (C1 t) (C2 t) := by
  rw [Finset.disjoint_left]
  intro j hj1 hj2
  rcases (mem_C1_iff (t := t) j).mp hj1 with ⟨r1, hr1, hrj1⟩
  rcases (mem_C2_iff (t := t) j).mp hj2 with ⟨r2, hr2, hrj2⟩
  have hT : 2 ^ t ≤ Sec3H.T t := by
    unfold Sec3H.T
    exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega : t ≤ t + 10)
  omega

/-- `Cp t ⊆ Icc 1 q` when `m_t ≤ q`. -/
lemma Cp_subset_Icc {t q : ℕ} (hm : Sec3.m_t t ≤ q) : Cp t ⊆ Finset.Icc 1 q := by
  intro j hj
  rw [Finset.mem_Icc]
  rw [Cp, Finset.mem_union] at hj
  rcases hj with h | h
  · rcases (mem_C1_iff (t := t) j).mp h with ⟨r, hr, hrj⟩
    subst j
    have hTpos : (0 : ℕ) < Sec3H.T t := by
      unfold Sec3H.T
      positivity
    have hle : Sec3H.T t + r ≤ Sec3.m_t t := by
      unfold Sec3.m_t Sec3H.T
      have hpow : 2 ^ (t + 10) ≤ 2 ^ (t + 11) := by
        exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
      omega
    omega
  · rcases (mem_C2_iff (t := t) j).mp h with ⟨r, hr, hrj⟩
    subst j
    have hTpos : (0 : ℕ) < Sec3H.T t := by
      unfold Sec3H.T
      positivity
    have hle : 2 * Sec3H.T t + r ≤ Sec3.m_t t := by
      unfold Sec3.m_t Sec3H.T
      have hpow : 2 ^ (t + 11) = 2 * 2 ^ (t + 10) := by
        rw [show t + 11 = (t + 10) + 1 by omega, pow_succ]
        ring
      omega
    omega

/-- The assembled polynomial (degree `4q`). -/
def flatPoly (t s q : ℕ) (eps : Fin q → ℝ) : ℂ[X] :=
  Polynomial.X ^ (2 * q) +
  (∑ r ∈ Finset.range (2 ^ t),
      Polynomial.C ((RudinShapiro.P t).coeff r) *
        (Polynomial.X ^ (2 * q + 2 * (Sec3H.T t + r)) +
          Polynomial.X ^ (2 * q - 2 * (Sec3H.T t + r)))) +
  (∑ r ∈ Finset.range (2 ^ t),
      Polynomial.C ((RudinShapiro.Q t).coeff r) *
        (Polynomial.X ^ (2 * q + 2 * (2 * Sec3H.T t + r)) +
          Polynomial.X ^ (2 * q - 2 * (2 * Sec3H.T t + r)))) +
  (∑ j ∈ (Finset.Icc 1 q) \ Cp t,
      Polynomial.C ((RudinShapiro.P s).coeff j) *
        (Polynomial.X ^ (2 * q + 2 * j) - Polynomial.X ^ (2 * q - 2 * j))) +
  (∑ i : Fin q, Polynomial.C ((eps i : ℝ) : ℂ) *
      (Polynomial.X ^ (2 * q + (2 * i.1 + 1)) - Polynomial.X ^ (2 * q - (2 * i.1 + 1))))

/-- The inner function: `P.eval(eθ θ) = eθ(2qθ)·inner`. -/
def flatInner (t s q : ℕ) (eps : Fin q → ℝ) (θ : ℝ) : ℂ :=
  (1 : ℂ) +
  (∑ r ∈ Finset.range (2 ^ t),
      (RudinShapiro.P t).coeff r *
        (Sec3.eθ (freq1 t r * θ) + Sec3.eθ (-(freq1 t r * θ)))) +
  (∑ r ∈ Finset.range (2 ^ t),
      (RudinShapiro.Q t).coeff r *
        (Sec3.eθ (freq2 t r * θ) + Sec3.eθ (-(freq2 t r * θ)))) +
  (∑ j ∈ (Finset.Icc 1 q) \ Cp t,
      (RudinShapiro.P s).coeff j *
        (Sec3.eθ (2 * (j : ℝ) * θ) - Sec3.eθ (-(2 * (j : ℝ) * θ)))) +
  (∑ i : Fin q, (eps i : ℂ) *
      (Sec3.eθ (S5.freq i.1 * θ) - Sec3.eθ (-(S5.freq i.1 * θ))))

/-! ### evaluation identities -/

lemma eval_shift_add1 (t q r : ℕ) (θ : ℝ) :
    (Sec3.eθ θ) ^ (2 * q + 2 * (Sec3H.T t + r)) =
      (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ (freq1 t r * θ) := by
  rw [pow_add]
  congr 1
  rw [← eθ_nat (2 * (Sec3H.T t + r)) θ]
  congr 1
  rw [nat_freq1 t r]

lemma eval_shift_sub1 (t q r : ℕ) (θ : ℝ) (hle : 2 * (Sec3H.T t + r) ≤ 2 * q) :
    (Sec3.eθ θ) ^ (2 * q - 2 * (Sec3H.T t + r)) =
      (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ (-(freq1 t r * θ)) := by
  have hpowadd : (Sec3.eθ θ) ^ (2 * q - 2 * (Sec3H.T t + r)) * (Sec3.eθ θ) ^ (2 * (Sec3H.T t + r)) =
      (Sec3.eθ θ) ^ (2 * q) := by
    rw [← pow_add]
    congr 1
    omega
  have hne : (Sec3.eθ θ) ^ (2 * (Sec3H.T t + r)) ≠ 0 :=
    pow_ne_zero _ (Complex.exp_ne_zero _)
  calc
    (Sec3.eθ θ) ^ (2 * q - 2 * (Sec3H.T t + r))
        = (Sec3.eθ θ) ^ (2 * q - 2 * (Sec3H.T t + r)) *
            ((Sec3.eθ θ) ^ (2 * (Sec3H.T t + r)) * ((Sec3.eθ θ) ^ (2 * (Sec3H.T t + r)))⁻¹) := by
            field_simp [hne]
    _ = (Sec3.eθ θ) ^ (2 * q) * ((Sec3.eθ θ) ^ (2 * (Sec3H.T t + r)))⁻¹ := by
            rw [← mul_assoc]
            rw [hpowadd]
    _ = (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ (-(freq1 t r * θ)) := by
            rw [← eθ_nat (2 * (Sec3H.T t + r)) θ]
            rw [← eθ_neg_inv (((2 * (Sec3H.T t + r) : ℕ) : ℝ) * θ)]
            congr 1
            rw [nat_freq1 t r]

lemma eval_shift_add2 (t q r : ℕ) (θ : ℝ) :
    (Sec3.eθ θ) ^ (2 * q + 2 * (2 * Sec3H.T t + r)) =
      (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ (freq2 t r * θ) := by
  rw [pow_add]
  congr 1
  rw [← eθ_nat (2 * (2 * Sec3H.T t + r)) θ]
  congr 1
  rw [nat_freq2 t r]

lemma eval_shift_sub2 (t q r : ℕ) (θ : ℝ) (hle : 2 * (2 * Sec3H.T t + r) ≤ 2 * q) :
    (Sec3.eθ θ) ^ (2 * q - 2 * (2 * Sec3H.T t + r)) =
      (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ (-(freq2 t r * θ)) := by
  have hpowadd : (Sec3.eθ θ) ^ (2 * q - 2 * (2 * Sec3H.T t + r)) *
      (Sec3.eθ θ) ^ (2 * (2 * Sec3H.T t + r)) = (Sec3.eθ θ) ^ (2 * q) := by
    rw [← pow_add]
    congr 1
    omega
  have hne : (Sec3.eθ θ) ^ (2 * (2 * Sec3H.T t + r)) ≠ 0 :=
    pow_ne_zero _ (Complex.exp_ne_zero _)
  calc
    (Sec3.eθ θ) ^ (2 * q - 2 * (2 * Sec3H.T t + r))
        = (Sec3.eθ θ) ^ (2 * q - 2 * (2 * Sec3H.T t + r)) *
            ((Sec3.eθ θ) ^ (2 * (2 * Sec3H.T t + r)) * ((Sec3.eθ θ) ^ (2 * (2 * Sec3H.T t + r)))⁻¹) := by
            field_simp [hne]
    _ = (Sec3.eθ θ) ^ (2 * q) * ((Sec3.eθ θ) ^ (2 * (2 * Sec3H.T t + r)))⁻¹ := by
            rw [← mul_assoc]
            rw [hpowadd]
    _ = (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ (-(freq2 t r * θ)) := by
            rw [← eθ_nat (2 * (2 * Sec3H.T t + r)) θ]
            rw [← eθ_neg_inv (((2 * (2 * Sec3H.T t + r) : ℕ) : ℝ) * θ)]
            congr 1
            rw [nat_freq2 t r]

/-- `((2*j:ℕ):ℝ) = 2*(j:ℝ)`. -/
lemma nat_two_mul (j : ℕ) : ((2 * j : ℕ) : ℝ) = 2 * (j : ℝ) := by
  push_cast
  ring

/-- `((2*r+1:ℕ):ℝ) = S5.freq r`. -/
lemma nat_freqO (r : ℕ) : (((2 * r + 1 : ℕ) : ℝ)) = S5.freq r := by
  unfold S5.freq
  push_cast
  ring

/-- First block evaluation. -/
lemma eval_block1 (t q : ℕ) (hm : ∀ r : ℕ, r < 2 ^ t → Sec3H.T t + r ≤ q) (θ : ℝ) :
    (∑ r ∈ Finset.range (2 ^ t),
        Polynomial.C ((RudinShapiro.P t).coeff r) *
          (Polynomial.X ^ (2 * q + 2 * (Sec3H.T t + r)) +
            Polynomial.X ^ (2 * q - 2 * (Sec3H.T t + r)))).eval (Sec3.eθ θ)
      = (Sec3.eθ θ) ^ (2 * q) *
          (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.P t).coeff r *
            (Sec3.eθ (freq1 t r * θ) + Sec3.eθ (-(freq1 t r * θ)))) := by
  rw [Polynomial.eval_finsetSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hle : 2 * (Sec3H.T t + r) ≤ 2 * q := by
    have h1 : Sec3H.T t + r ≤ q := hm r (Finset.mem_range.mp hr)
    omega
  calc
    Polynomial.eval (Sec3.eθ θ) (Polynomial.C ((RudinShapiro.P t).coeff r) *
        (Polynomial.X ^ (2 * q + 2 * (Sec3H.T t + r)) +
          Polynomial.X ^ (2 * q - 2 * (Sec3H.T t + r))))
        = (RudinShapiro.P t).coeff r *
            ((Sec3.eθ θ) ^ (2 * q + 2 * (Sec3H.T t + r)) +
              (Sec3.eθ θ) ^ (2 * q - 2 * (Sec3H.T t + r))) := by
          simp
    _ = (Sec3.eθ θ) ^ (2 * q) * ((RudinShapiro.P t).coeff r *
          (Sec3.eθ (freq1 t r * θ) + Sec3.eθ (-(freq1 t r * θ)))) := by
          rw [eval_shift_add1 t q r θ]
          rw [eval_shift_sub1 t q r θ hle]
          ring

/-- Second block evaluation. -/
lemma eval_block2 (t q : ℕ) (hm : ∀ r : ℕ, r < 2 ^ t → 2 * Sec3H.T t + r ≤ q) (θ : ℝ) :
    (∑ r ∈ Finset.range (2 ^ t),
        Polynomial.C ((RudinShapiro.Q t).coeff r) *
          (Polynomial.X ^ (2 * q + 2 * (2 * Sec3H.T t + r)) +
            Polynomial.X ^ (2 * q - 2 * (2 * Sec3H.T t + r)))).eval (Sec3.eθ θ)
      = (Sec3.eθ θ) ^ (2 * q) *
          (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.Q t).coeff r *
            (Sec3.eθ (freq2 t r * θ) + Sec3.eθ (-(freq2 t r * θ)))) := by
  rw [Polynomial.eval_finsetSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hle : 2 * (2 * Sec3H.T t + r) ≤ 2 * q := by
    have h1 : 2 * Sec3H.T t + r ≤ q := hm r (Finset.mem_range.mp hr)
    omega
  calc
    Polynomial.eval (Sec3.eθ θ) (Polynomial.C ((RudinShapiro.Q t).coeff r) *
        (Polynomial.X ^ (2 * q + 2 * (2 * Sec3H.T t + r)) +
          Polynomial.X ^ (2 * q - 2 * (2 * Sec3H.T t + r))))
        = (RudinShapiro.Q t).coeff r *
            ((Sec3.eθ θ) ^ (2 * q + 2 * (2 * Sec3H.T t + r)) +
              (Sec3.eθ θ) ^ (2 * q - 2 * (2 * Sec3H.T t + r))) := by
          simp
    _ = (Sec3.eθ θ) ^ (2 * q) * ((RudinShapiro.Q t).coeff r *
          (Sec3.eθ (freq2 t r * θ) + Sec3.eθ (-(freq2 t r * θ)))) := by
          rw [eval_shift_add2 t q r θ]
          rw [eval_shift_sub2 t q r θ hle]
          ring

/-- Even-sine block evaluation. -/
lemma eval_blockE (t s q : ℕ) (θ : ℝ) :
    (∑ j ∈ (Finset.Icc 1 q) \ Cp t,
        Polynomial.C ((RudinShapiro.P s).coeff j) *
          (Polynomial.X ^ (2 * q + 2 * j) - Polynomial.X ^ (2 * q - 2 * j))).eval (Sec3.eθ θ)
      = (Sec3.eθ θ) ^ (2 * q) *
          (∑ j ∈ (Finset.Icc 1 q) \ Cp t, (RudinShapiro.P s).coeff j *
            (Sec3.eθ (2 * (j : ℝ) * θ) - Sec3.eθ (-(2 * (j : ℝ) * θ)))) := by
  rw [Polynomial.eval_finsetSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjq : j ≤ q := by
    rcases Finset.mem_sdiff.mp hj with ⟨hji, _⟩
    exact (Finset.mem_Icc.mp hji).2
  have hle : 2 * j ≤ 2 * q := by omega
  have he1 : (Sec3.eθ θ) ^ (2 * q + 2 * j) = (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ ((2 * (j : ℝ)) * θ) := by
    rw [pow_add]
    congr 1
    rw [← eθ_nat (2 * j) θ]
    congr 1
    rw [nat_two_mul j]
  have he2 : (Sec3.eθ θ) ^ (2 * q - 2 * j) = (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ (-(2 * (j : ℝ) * θ)) := by
    have hpowadd : (Sec3.eθ θ) ^ (2 * q - 2 * j) * (Sec3.eθ θ) ^ (2 * j) = (Sec3.eθ θ) ^ (2 * q) := by
      rw [← pow_add]
      congr 1
      omega
    have hne : (Sec3.eθ θ) ^ (2 * j) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
    calc
      (Sec3.eθ θ) ^ (2 * q - 2 * j)
          = (Sec3.eθ θ) ^ (2 * q - 2 * j) * ((Sec3.eθ θ) ^ (2 * j) * ((Sec3.eθ θ) ^ (2 * j))⁻¹) := by
              field_simp [hne]
      _ = (Sec3.eθ θ) ^ (2 * q) * ((Sec3.eθ θ) ^ (2 * j))⁻¹ := by
              rw [← mul_assoc]
              rw [hpowadd]
      _ = (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ (-(2 * (j : ℝ) * θ)) := by
              rw [← eθ_nat (2 * j) θ]
              rw [← eθ_neg_inv (((2 * j : ℕ) : ℝ) * θ)]
              congr 1
              rw [nat_two_mul j]
  calc
    Polynomial.eval (Sec3.eθ θ) (Polynomial.C ((RudinShapiro.P s).coeff j) *
        (Polynomial.X ^ (2 * q + 2 * j) - Polynomial.X ^ (2 * q - 2 * j)))
        = (RudinShapiro.P s).coeff j *
            ((Sec3.eθ θ) ^ (2 * q + 2 * j) - (Sec3.eθ θ) ^ (2 * q - 2 * j)) := by
          simp
    _ = (Sec3.eθ θ) ^ (2 * q) * ((RudinShapiro.P s).coeff j *
          (Sec3.eθ (2 * (j : ℝ) * θ) - Sec3.eθ (-(2 * (j : ℝ) * θ)))) := by
          rw [he1, he2]
          ring

/-- Odd-sine block evaluation. -/
lemma eval_blockO (q : ℕ) (eps : Fin q → ℝ) (θ : ℝ) :
    (∑ i : Fin q, Polynomial.C ((eps i : ℝ) : ℂ) *
        (Polynomial.X ^ (2 * q + (2 * i.1 + 1)) - Polynomial.X ^ (2 * q - (2 * i.1 + 1)))).eval (Sec3.eθ θ)
      = (Sec3.eθ θ) ^ (2 * q) *
          (∑ i : Fin q, (eps i : ℂ) *
            (Sec3.eθ (S5.freq i.1 * θ) - Sec3.eθ (-(S5.freq i.1 * θ)))) := by
  rw [Polynomial.eval_finsetSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he1 : (Sec3.eθ θ) ^ (2 * q + (2 * i.1 + 1)) =
      (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ (S5.freq i.1 * θ) := by
    rw [pow_add]
    congr 1
    rw [← eθ_nat (2 * i.1 + 1) θ]
    congr 1
    rw [nat_freqO i.1]
  have he2 : (Sec3.eθ θ) ^ (2 * q - (2 * i.1 + 1)) =
      (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ (-(S5.freq i.1 * θ)) := by
    have hpowadd : (Sec3.eθ θ) ^ (2 * q - (2 * i.1 + 1)) * (Sec3.eθ θ) ^ (2 * i.1 + 1) =
        (Sec3.eθ θ) ^ (2 * q) := by
      rw [← pow_add]
      congr 1
      omega
    have hne : (Sec3.eθ θ) ^ (2 * i.1 + 1) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
    calc
      (Sec3.eθ θ) ^ (2 * q - (2 * i.1 + 1))
          = (Sec3.eθ θ) ^ (2 * q - (2 * i.1 + 1)) *
              ((Sec3.eθ θ) ^ (2 * i.1 + 1) * ((Sec3.eθ θ) ^ (2 * i.1 + 1))⁻¹) := by
              field_simp [hne]
      _ = (Sec3.eθ θ) ^ (2 * q) * ((Sec3.eθ θ) ^ (2 * i.1 + 1))⁻¹ := by
              rw [← mul_assoc]
              rw [hpowadd]
      _ = (Sec3.eθ θ) ^ (2 * q) * Sec3.eθ (-(S5.freq i.1 * θ)) := by
              rw [← eθ_nat (2 * i.1 + 1) θ]
              rw [← eθ_neg_inv (((2 * i.1 + 1 : ℕ) : ℝ) * θ)]
              congr 1
              rw [nat_freqO i.1]
  calc
    Polynomial.eval (Sec3.eθ θ) (Polynomial.C ((eps i : ℝ) : ℂ) *
        (Polynomial.X ^ (2 * q + (2 * i.1 + 1)) - Polynomial.X ^ (2 * q - (2 * i.1 + 1))))
        = (eps i : ℂ) *
            ((Sec3.eθ θ) ^ (2 * q + (2 * i.1 + 1)) - (Sec3.eθ θ) ^ (2 * q - (2 * i.1 + 1))) := by
          simp
    _ = (Sec3.eθ θ) ^ (2 * q) * ((eps i : ℂ) *
          (Sec3.eθ (S5.freq i.1 * θ) - Sec3.eθ (-(S5.freq i.1 * θ)))) := by
          rw [he1, he2]
          ring

/-! ### Main eval identity -/

lemma flatPoly_eval (t s q : ℕ) (eps : Fin q → ℝ)
    (hm1 : ∀ r : ℕ, r < 2 ^ t → Sec3H.T t + r ≤ q)
    (hm2 : ∀ r : ℕ, r < 2 ^ t → 2 * Sec3H.T t + r ≤ q) (θ : ℝ) :
    (flatPoly t s q eps).eval (Sec3.eθ θ) =
      (Sec3.eθ θ) ^ (2 * q) * flatInner t s q eps θ := by
  unfold flatPoly flatInner
  repeat rw [Polynomial.eval_add]
  rw [eval_block1 t q hm1 θ]
  rw [eval_block2 t q hm2 θ]
  rw [eval_blockE t s q θ]
  rw [eval_blockO q eps θ]
  simp
  ring

/-! ### Rudin–Shapiro prefix coefficient identities -/

/-- For `r < 2^t`: `(Q (s+1)).coeff r = (P t).coeff r` whenever `t ≤ s`. -/
lemma coeff_Q_stable_P (t s : ℕ) (r : ℕ) (hts : t ≤ s) (hr : r < 2 ^ t) :
    (RudinShapiro.Q (s + 1)).coeff r = (RudinShapiro.P t).coeff r := by
  have hrs : r < 2 ^ s := lt_of_lt_of_le hr (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hts)
  calc
    (RudinShapiro.Q (s + 1)).coeff r = (RudinShapiro.P s).coeff r :=
      RudinShapiro.coeff_Q_extend s r hrs
    _ = (RudinShapiro.P t).coeff r := RudinShapiro.coeff_P_stable hts hr

/-- Coefficients of `P s` at `T + r` (`r < 2^t`) equal those of `P t`,
provided `s ≥ t + 11`. -/
lemma coeff_P_level_T {t s r : ℕ} (hr : r < 2 ^ t) (hts : t + 11 ≤ s) :
    (RudinShapiro.P s).coeff (Sec3H.T t + r) = (RudinShapiro.P t).coeff r := by
  have hT : Sec3H.T t = 2 ^ (t + 10) := rfl
  have hi1 : Sec3H.T t + r < 2 ^ (t + 11) := by
    rw [hT]
    have hle : 2 ^ (t + 10) + (2 ^ t - 1) < 2 ^ (t + 11) := by
      have hA : 2 ^ t ≤ 2 ^ (t + 10) := by
        exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
      have hB : 2 ^ (t + 10) + 2 ^ (t + 10) = 2 ^ (t + 11) := by
        rw [show t + 11 = (t + 10) + 1 by omega, pow_succ]
        ring
      omega
    omega
  have hstab : (RudinShapiro.P s).coeff (Sec3H.T t + r) = (RudinShapiro.P (t + 11)).coeff (Sec3H.T t + r) :=
    RudinShapiro.coeff_P_stable hts hi1
  have htop : (RudinShapiro.P (t + 11)).coeff (Sec3H.T t + r) = (RudinShapiro.Q (t + 10)).coeff r := by
    rw [hT]
    have hp : (t + 10) + 1 = t + 11 := by omega
    rw [← hp]
    exact RudinShapiro.coeff_P_top (t + 10) r
  have hq : (RudinShapiro.Q (t + 10)).coeff r = (RudinShapiro.P t).coeff r := by
    exact coeff_Q_stable_P t (t + 9) r (by omega) hr
  exact hstab.trans (htop.trans hq)

/-- Coefficients of `P s` at `2T + r` (`r < 2^t`) equal those of `P t`,
provided `s ≥ t + 12`. -/
lemma coeff_P_level_twoT {t s r : ℕ} (hr : r < 2 ^ t) (hts : t + 12 ≤ s) :
    (RudinShapiro.P s).coeff (2 * Sec3H.T t + r) = (RudinShapiro.P t).coeff r := by
  have hT : 2 * Sec3H.T t = 2 ^ (t + 11) := by
    unfold Sec3H.T
    rw [show t + 11 = (t + 10) + 1 by omega, pow_succ]
    ring
  have hi1 : 2 * Sec3H.T t + r < 2 ^ (t + 12) := by
    rw [hT]
    have hle : 2 ^ (t + 11) + (2 ^ t - 1) < 2 ^ (t + 12) := by
      have hA : 2 ^ t ≤ 2 ^ (t + 11) := by
        exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
      have hB : 2 ^ (t + 11) + 2 ^ (t + 11) = 2 ^ (t + 12) := by
        rw [show t + 12 = (t + 11) + 1 by omega, pow_succ]
        ring
      omega
    omega
  have hstab : (RudinShapiro.P s).coeff (2 * Sec3H.T t + r) = (RudinShapiro.P (t + 12)).coeff (2 * Sec3H.T t + r) :=
    RudinShapiro.coeff_P_stable hts hi1
  have htop : (RudinShapiro.P (t + 12)).coeff (2 * Sec3H.T t + r) = (RudinShapiro.Q (t + 11)).coeff r := by
    rw [hT]
    have hp : (t + 11) + 1 = t + 12 := by omega
    rw [← hp]
    exact RudinShapiro.coeff_P_top (t + 11) r
  have hq : (RudinShapiro.Q (t + 11)).coeff r = (RudinShapiro.P t).coeff r := by
    exact coeff_Q_stable_P t (t + 10) r (by omega) hr
  exact hstab.trans (htop.trans hq)

/-- `Σ_{j < q+1} p j z^j = p 0 z^0 + Σ_{j ∈ Icc 1 q} p j z^j`. -/
lemma sum_range_head (z : ℂ) (p : ℕ → ℂ) (q : ℕ) :
    (∑ j ∈ Finset.range (q + 1), p j * z ^ j) =
      p 0 * z ^ 0 + (∑ j ∈ Finset.Icc 1 q, p j * z ^ j) := by
  have hmem : (0 : ℕ) ∈ Finset.range (q + 1) := by simp
  have hsum := Finset.sum_erase_add (s := Finset.range (q + 1)) (a := 0) (f := fun j => p j * z ^ j) hmem
  have hset : (Finset.range (q + 1)).erase 0 = Finset.Icc 1 q := by
    ext j
    simp [Finset.mem_range, Finset.mem_Icc, Finset.mem_erase]
    omega
  rw [hset] at hsum
  rw [add_comm] at hsum
  exact hsum.symm

/-! ### `s_e` equals the residual sine sum -/

/-- `C1 t` as an image-sum: `Σ_{j∈C1} f j = Σ_{r<2^t} f (T+r)`. -/
lemma sum_C1_image (t : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ C1 t, f j) = ∑ r ∈ Finset.range (2 ^ t), f (Sec3H.T t + r) := by
  unfold C1
  rw [Finset.sum_image]
  · intro r hr r' hr' h
    dsimp at h
    omega

/-- `C2 t` as an image-sum: `Σ_{j∈C2} f j = Σ_{r<2^t} f (2T+r)`. -/
lemma sum_C2_image (t : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ C2 t, f j) = ∑ r ∈ Finset.range (2 ^ t), f (2 * Sec3H.T t + r) := by
  unfold C2
  rw [Finset.sum_image]
  · intro r hr r' hr' h
    dsimp at h
    omega

/-- `C1 ∪ C2` = `Cp`. -/
lemma C1_union_C2 (t : ℕ) : C1 t ∪ C2 t = Cp t := by
  rfl

/-- `Σ_{j ∈ Cp t} f j = Σ_{C1} + Σ_{C2}`. -/
lemma sum_Cp_image (t : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ Cp t, f j) = (∑ j ∈ C1 t, f j) + (∑ j ∈ C2 t, f j) := by
  rw [← C1_union_C2]
  exact Finset.sum_union (C1_disjoint_C2 t)

/-- `Σ_{Icc 1 q} f = Σ_{Cp} + Σ_{(Icc1q)\Cp}` when `Cp ⊆ Icc 1 q`. -/
lemma sum_Icc_sdiff (t q : ℕ) (hm : Sec3.m_t t ≤ q) (f : ℕ → ℂ) :
    (∑ j ∈ Finset.Icc 1 q, f j) = (∑ j ∈ Cp t, f j) + (∑ j ∈ (Finset.Icc 1 q) \ Cp t, f j) := by
  have hsub : Cp t ⊆ Finset.Icc 1 q := Cp_subset_Icc (t := t) (q := q) hm
  have hs := Finset.sum_sdiff (s₁ := Cp t) (s₂ := Finset.Icc 1 q) (f := f) hsub
  rw [add_comm] at hs
  exact hs.symm

/-- `z^T · P_t.eval z = Σ_{r<2^t} (P t).coeff r·z^(T+r)`. -/
lemma zpow_P_eval_T (t : ℕ) (z : ℂ) :
    z ^ Sec3H.T t * (RudinShapiro.P t).eval z =
      ∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.P t).coeff r * z ^ (Sec3H.T t + r) :=
  Sec3.CosExpandAux.zpow_mul_eval_eq_sum (p := RudinShapiro.P t) (n := 2 ^ t)
    (A := Sec3H.T t) (z := z) (Sec3.CosExpandAux.P_natDegree_lt t)

/-- `z^(2T) · P_t.eval z = Σ_{r<2^t} (P t).coeff r·z^(2T+r)`. -/
lemma zpow_P_eval_twoT (t : ℕ) (z : ℂ) :
    z ^ (2 * Sec3H.T t) * (RudinShapiro.P t).eval z =
      ∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.P t).coeff r * z ^ (2 * Sec3H.T t + r) :=
  Sec3.CosExpandAux.zpow_mul_eval_eq_sum (p := RudinShapiro.P t) (n := 2 ^ t)
    (A := 2 * Sec3H.T t) (z := z) (Sec3.CosExpandAux.P_natDegree_lt t)

/-- `Psum s (q+1)` evaluated at `z`. -/
lemma Psum_eval_range (s q : ℕ) (z : ℂ) :
    (RudinShapiro.Psum s (q + 1)).eval z =
      (∑ j ∈ Finset.range (q + 1), (RudinShapiro.P s).coeff j * z ^ j) := by
  simpa using RudinShapiro.eval_Psum s (q + 1) z

/-- `seval` = constant term plus residual sine positions. -/
lemma seval_eq (t s q : ℕ) (hs : t + 12 ≤ s) (hm : Sec3.m_t t ≤ q) (θ : ℝ) :
    Sec3.seval s t q θ =
      (RudinShapiro.P s).coeff 0 * (Sec3.zθ θ) ^ 0 +
        (∑ j ∈ (Finset.Icc 1 q) \ Cp t, (RudinShapiro.P s).coeff j * (Sec3.zθ θ) ^ j) := by
  let z : ℂ := Sec3.zθ θ
  let p : ℕ → ℂ := fun j => (RudinShapiro.P s).coeff j
  have hs1 : t + 11 ≤ s := by omega
  have hseval :
      Sec3.seval s t q θ =
        (∑ j ∈ Finset.range (q + 1), p j * z ^ j)
          - (∑ j ∈ Cp t, p j * z ^ j) := by
    unfold Sec3.seval
    dsimp
    simp [z, p]
    rw [Psum_eval_range]
    have h1a : (∑ r ∈ Finset.range (2 ^ t),
          (RudinShapiro.P t).coeff r * z ^ (2 ^ (t + 10) + r)) =
        (∑ j ∈ C1 t, p j * z ^ j) := by
      rw [sum_C1_image t (fun j => p j * z ^ j)]
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      exact (coeff_P_level_T (Finset.mem_range.mp hr) hs1).symm
    have h2a : (∑ r ∈ Finset.range (2 ^ t),
          (RudinShapiro.P t).coeff r * z ^ (2 * 2 ^ (t + 10) + r)) =
        (∑ j ∈ C2 t, p j * z ^ j) := by
      rw [sum_C2_image t (fun j => p j * z ^ j)]
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      exact (coeff_P_level_twoT (Finset.mem_range.mp hr) hs).symm
    have hz1 : z ^ 2 ^ (t + 10) * (RudinShapiro.P t).eval z =
        (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.P t).coeff r * z ^ (2 ^ (t + 10) + r)) := by
      simpa [Sec3H.T] using (zpow_P_eval_T t z)
    have hz2 : z ^ (2 * 2 ^ (t + 10)) * (RudinShapiro.P t).eval z =
        (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.P t).coeff r * z ^ (2 * 2 ^ (t + 10) + r)) := by
      simpa [Sec3H.T] using (zpow_P_eval_twoT t z)
    rw [hz1]
    rw [hz2]
    rw [h1a]
    rw [h2a]
    rw [sum_Cp_image t (fun j => p j * z ^ j)]
    ring
  rw [hseval]
  rw [sum_range_head z p q]
  rw [sum_Icc_sdiff t q hm (fun j => p j * z ^ j)]
  ring

/-- `zθ θ ^ j = eθ (2*(j:ℝ)*θ)`. -/
lemma zθ_pow (j : ℕ) (θ : ℝ) : (Sec3.zθ θ) ^ j = Sec3.eθ (2 * (j : ℝ) * θ) := by
  unfold Sec3.zθ
  rw [← eθ_nat j (2 * θ)]
  congr 1
  ring

/-- `s_e` (im of `seval`) equals the residual sine sum. -/
lemma s_e_eq (t s q : ℕ) (hs : t + 12 ≤ s) (hm : Sec3.m_t t ≤ q) (θ : ℝ) :
    Sec3.s_e s t q θ =
      (∑ j ∈ (Finset.Icc 1 q) \ Cp t,
        ((RudinShapiro.P s).coeff j).re * Real.sin (2 * (j : ℝ) * θ)) := by
  unfold Sec3.s_e
  rw [seval_eq t s q hs hm θ]
  rw [Complex.add_im]
  rw [sum_im]
  have hp0 : ((RudinShapiro.P s).coeff 0 * (Sec3.zθ θ) ^ 0).im = 0 := by
    rw [show (Sec3.zθ θ) ^ 0 = (1 : ℂ) by simp]
    rw [mul_one]
    exact coeff_P_im_all s 0
  rw [hp0, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  rw [zθ_pow j θ]
  rw [im_mul_of_im_zero ((RudinShapiro.P s).coeff j) (Sec3.eθ (2 * (j : ℝ) * θ)) (coeff_P_im_all s j)]
  rw [eθ_im']


/-- `sOdd` equals the sum over `Fin q` with `S5.freq` arguments. -/
lemma sOdd_eq (q : ℕ) (eps : Fin q → ℝ) (θ : ℝ) :
    S5.sOdd q eps θ = (∑ i : Fin q, eps i * Real.sin (S5.freq i.1 * θ)) := by
  simp [S5.sOdd, S5.oddSin]

/-! ### `re`/`im` of the cosine blocks -/

/-- `re` of the first cosine block. -/
lemma re_cosblock1 (t : ℕ) (θ : ℝ) :
    (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.P t).coeff r *
        (Sec3.eθ (freq1 t r * θ) + Sec3.eθ (-(freq1 t r * θ)))).re
      = 2 * (∑ r ∈ Finset.range (2 ^ t),
          ((RudinShapiro.P t).coeff r).re * Real.cos (freq1 t r * θ)) := by
  rw [sum_re]
  calc
    (∑ r ∈ Finset.range (2 ^ t),
        (((RudinShapiro.P t).coeff r) * (Sec3.eθ (freq1 t r * θ) + Sec3.eθ (-(freq1 t r * θ)))).re)
        = ∑ r ∈ Finset.range (2 ^ t),
            2 * (((RudinShapiro.P t).coeff r).re * Real.cos (freq1 t r * θ)) := by
          apply Finset.sum_congr rfl
          intro r hr
          have ha : ((RudinShapiro.P t).coeff r).im = 0 := Sec3.CosExpandAux.coeff_P_im t r
          have hw : (Sec3.eθ (freq1 t r * θ) + Sec3.eθ (-(freq1 t r * θ))).re = 2 * Real.cos (freq1 t r * θ) := by
            rw [eθ_add_neg (freq1 t r * θ)]
            exact Complex.ofReal_re (2 * Real.cos (freq1 t r * θ))
          rw [re_mul_of_im_zero ((RudinShapiro.P t).coeff r)
              (Sec3.eθ (freq1 t r * θ) + Sec3.eθ (-(freq1 t r * θ))) ha]
          rw [hw]
          ring
    _ = 2 * (∑ r ∈ Finset.range (2 ^ t),
          ((RudinShapiro.P t).coeff r).re * Real.cos (freq1 t r * θ)) := by
          rw [Finset.mul_sum]

/-- `re` of the second cosine block. -/
lemma re_cosblock2 (t : ℕ) (θ : ℝ) :
    (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.Q t).coeff r *
        (Sec3.eθ (freq2 t r * θ) + Sec3.eθ (-(freq2 t r * θ)))).re
      = 2 * (∑ r ∈ Finset.range (2 ^ t),
          ((RudinShapiro.Q t).coeff r).re * Real.cos (freq2 t r * θ)) := by
  rw [sum_re]
  calc
    (∑ r ∈ Finset.range (2 ^ t),
        (((RudinShapiro.Q t).coeff r) * (Sec3.eθ (freq2 t r * θ) + Sec3.eθ (-(freq2 t r * θ)))).re)
        = ∑ r ∈ Finset.range (2 ^ t),
            2 * (((RudinShapiro.Q t).coeff r).re * Real.cos (freq2 t r * θ)) := by
          apply Finset.sum_congr rfl
          intro r hr
          have ha : ((RudinShapiro.Q t).coeff r).im = 0 := Sec3.CosExpandAux.coeff_Q_im t r
          have hw : (Sec3.eθ (freq2 t r * θ) + Sec3.eθ (-(freq2 t r * θ))).re = 2 * Real.cos (freq2 t r * θ) := by
            rw [eθ_add_neg (freq2 t r * θ)]
            exact Complex.ofReal_re (2 * Real.cos (freq2 t r * θ))
          rw [re_mul_of_im_zero ((RudinShapiro.Q t).coeff r)
              (Sec3.eθ (freq2 t r * θ) + Sec3.eθ (-(freq2 t r * θ))) ha]
          rw [hw]
          ring
    _ = 2 * (∑ r ∈ Finset.range (2 ^ t),
          ((RudinShapiro.Q t).coeff r).re * Real.cos (freq2 t r * θ)) := by
          rw [Finset.mul_sum]

/-- `im` of the first cosine block is zero. -/
lemma im_cosblock1 (t : ℕ) (θ : ℝ) :
    (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.P t).coeff r *
        (Sec3.eθ (freq1 t r * θ) + Sec3.eθ (-(freq1 t r * θ)))).im = 0 := by
  rw [sum_im]
  apply Finset.sum_eq_zero
  intro r hr
  have ha : ((RudinShapiro.P t).coeff r).im = 0 := Sec3.CosExpandAux.coeff_P_im t r
  have hw : (Sec3.eθ (freq1 t r * θ) + Sec3.eθ (-(freq1 t r * θ))).im = 0 := by
    rw [eθ_add_neg (freq1 t r * θ)]
    exact Complex.ofReal_im (2 * Real.cos (freq1 t r * θ))
  rw [im_mul_of_im_zero ((RudinShapiro.P t).coeff r)
      (Sec3.eθ (freq1 t r * θ) + Sec3.eθ (-(freq1 t r * θ))) ha]
  rw [hw]
  ring

/-- `im` of the second cosine block is zero. -/
lemma im_cosblock2 (t : ℕ) (θ : ℝ) :
    (∑ r ∈ Finset.range (2 ^ t), (RudinShapiro.Q t).coeff r *
        (Sec3.eθ (freq2 t r * θ) + Sec3.eθ (-(freq2 t r * θ)))).im = 0 := by
  rw [sum_im]
  apply Finset.sum_eq_zero
  intro r hr
  have ha : ((RudinShapiro.Q t).coeff r).im = 0 := Sec3.CosExpandAux.coeff_Q_im t r
  have hw : (Sec3.eθ (freq2 t r * θ) + Sec3.eθ (-(freq2 t r * θ))).im = 0 := by
    rw [eθ_add_neg (freq2 t r * θ)]
    exact Complex.ofReal_im (2 * Real.cos (freq2 t r * θ))
  rw [im_mul_of_im_zero ((RudinShapiro.Q t).coeff r)
      (Sec3.eθ (freq2 t r * θ) + Sec3.eθ (-(freq2 t r * θ))) ha]
  rw [hw]
  ring

/-! ### `re`/`im` of the sine-type blocks -/

/-- `re` of the even-sine block is zero. -/
lemma re_evenblock (t s q : ℕ) (θ : ℝ) :
    (∑ j ∈ (Finset.Icc 1 q) \ Cp t, (RudinShapiro.P s).coeff j *
        (Sec3.eθ (2 * (j : ℝ) * θ) - Sec3.eθ (-(2 * (j : ℝ) * θ)))).re = 0 := by
  rw [sum_re]
  apply Finset.sum_eq_zero
  intro j hj
  have hw : Sec3.eθ (2 * (j : ℝ) * θ) - Sec3.eθ (-(2 * (j : ℝ) * θ)) =
      ((2 * Real.sin (2 * (j : ℝ) * θ) : ℝ) : ℂ) * Complex.I :=
    eθ_sub_neg (2 * (j : ℝ) * θ)
  rw [hw]
  rw [re_mul_of_im_zero ((RudinShapiro.P s).coeff j)
      (((2 * Real.sin (2 * (j : ℝ) * θ) : ℝ) : ℂ) * Complex.I) (coeff_P_im_all s j)]
  rw [re_ofReal_mul]
  simp [Complex.I_re]

/-- `im` of the even-sine block equals twice the `s_e`-sum. -/
lemma im_evenblock (t s q : ℕ) (θ : ℝ) :
    (∑ j ∈ (Finset.Icc 1 q) \ Cp t, (RudinShapiro.P s).coeff j *
        (Sec3.eθ (2 * (j : ℝ) * θ) - Sec3.eθ (-(2 * (j : ℝ) * θ)))).im
      = 2 * (∑ j ∈ (Finset.Icc 1 q) \ Cp t,
          ((RudinShapiro.P s).coeff j).re * Real.sin (2 * (j : ℝ) * θ)) := by
  rw [sum_im]
  calc
    (∑ j ∈ (Finset.Icc 1 q) \ Cp t,
        (((RudinShapiro.P s).coeff j) * (Sec3.eθ (2 * (j : ℝ) * θ) - Sec3.eθ (-(2 * (j : ℝ) * θ)))).im)
        = ∑ j ∈ (Finset.Icc 1 q) \ Cp t,
            2 * (((RudinShapiro.P s).coeff j).re * Real.sin (2 * (j : ℝ) * θ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [eθ_sub_neg (2 * (j : ℝ) * θ)]
          rw [im_mul_of_im_zero ((RudinShapiro.P s).coeff j)
              (((2 * Real.sin (2 * (j : ℝ) * θ) : ℝ) : ℂ) * Complex.I) (coeff_P_im_all s j)]
          rw [im_ofReal_mul]
          simp [Complex.I_im]
          ring
    _ = 2 * (∑ j ∈ (Finset.Icc 1 q) \ Cp t,
          ((RudinShapiro.P s).coeff j).re * Real.sin (2 * (j : ℝ) * θ)) := by
          rw [Finset.mul_sum]

/-- `re` of the odd block is zero. -/
lemma re_oddblock (q : ℕ) (eps : Fin q → ℝ) (θ : ℝ) :
    (∑ i : Fin q, (eps i : ℂ) *
        (Sec3.eθ (S5.freq i.1 * θ) - Sec3.eθ (-(S5.freq i.1 * θ)))).re = 0 := by
  rw [sum_re]
  apply Finset.sum_eq_zero
  intro i hi
  rw [eθ_sub_neg (S5.freq i.1 * θ)]
  rw [re_ofReal_mul]
  rw [re_ofReal_mul]
  rw [Complex.I_re]
  ring

/-- `im` of the odd block equals `2·sOdd`. -/
lemma im_oddblock (q : ℕ) (eps : Fin q → ℝ) (θ : ℝ) :
    (∑ i : Fin q, (eps i : ℂ) *
        (Sec3.eθ (S5.freq i.1 * θ) - Sec3.eθ (-(S5.freq i.1 * θ)))).im
      = 2 * S5.sOdd q eps θ := by
  rw [sum_im]
  calc
    (∑ i : Fin q,
        (((eps i : ℂ) * (Sec3.eθ (S5.freq i.1 * θ) - Sec3.eθ (-(S5.freq i.1 * θ)))).im))
        = ∑ i : Fin q, 2 * (eps i * Real.sin (S5.freq i.1 * θ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [eθ_sub_neg (S5.freq i.1 * θ)]
          rw [im_ofReal_mul]
          rw [im_ofReal_mul]
          rw [Complex.I_im]
          ring
    _ = 2 * (∑ i : Fin q, eps i * Real.sin (S5.freq i.1 * θ)) := by
          rw [Finset.mul_sum]
    _ = 2 * S5.sOdd q eps θ := by
          rw [sOdd_eq]

/-- `c = (Σ_r (P t).coeff r re·cos freq1) + (Σ_r (Q t).coeff r re·cos freq2)`. -/
lemma c_eq_cos_freq (t : ℕ) (θ : ℝ) :
    Sec3.c t θ =
      (∑ r ∈ Finset.range (2 ^ t),
          ((RudinShapiro.P t).coeff r).re * Real.cos (freq1 t r * θ)) +
      (∑ r ∈ Finset.range (2 ^ t),
          ((RudinShapiro.Q t).coeff r).re * Real.cos (freq2 t r * θ)) := by
  rw [Sec3.c_eq_cos_sum t θ]
  congr 2 <;> apply Finset.sum_congr rfl <;> intro r hr <;> congr 1 <;> rfl

/-- The real part of the inner function is `1 + 2c`. -/
lemma flatInner_re (t s q : ℕ) (eps : Fin q → ℝ) (θ : ℝ) :
    (flatInner t s q eps θ).re = 1 + 2 * Sec3.c t θ := by
  unfold flatInner
  repeat rw [Complex.add_re]
  rw [re_cosblock1 t θ]
  rw [re_cosblock2 t θ]
  rw [re_evenblock t s q θ]
  rw [re_oddblock q eps θ]
  rw [c_eq_cos_freq t θ]
  norm_num
  ring

/-- The imaginary part of the inner function is `2(s_e + s_o)`. -/
lemma flatInner_im (t s q : ℕ) (eps : Fin q → ℝ) (hs : t + 12 ≤ s)
    (hm : Sec3.m_t t ≤ q) (θ : ℝ) :
    (flatInner t s q eps θ).im = 2 * (Sec3.s_e s t q θ + S5.sOdd q eps θ) := by
  unfold flatInner
  repeat rw [Complex.add_im]
  rw [im_cosblock1 t θ]
  rw [im_cosblock2 t θ]
  rw [im_evenblock t s q θ]
  rw [im_oddblock q eps θ]
  rw [s_e_eq t s q hs hm θ]
  norm_num
  ring

/-- The inner function equals `(1+2c) + i·2(s_e+s_o)`. -/
lemma flatInner_eq (t s q : ℕ) (eps : Fin q → ℝ) (hs : t + 12 ≤ s)
    (hm : Sec3.m_t t ≤ q) (θ : ℝ) :
    flatInner t s q eps θ =
      (((1 + 2 * Sec3.c t θ) : ℝ) : ℂ) +
        (((2 * (Sec3.s_e s t q θ + S5.sOdd q eps θ)) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [flatInner_re t s q eps θ]
    rw [Complex.add_re]
    rw [Complex.ofReal_re]
    rw [Complex.mul_re]
    rw [Complex.ofReal_im]
    rw [Complex.I_re]
    norm_num
  · rw [flatInner_im t s q eps hs hm θ]
    rw [Complex.add_im]
    rw [Complex.ofReal_im]
    rw [Complex.mul_im]
    rw [Complex.ofReal_re]
    rw [Complex.I_im]
    norm_num












/-! ### Analytic assembly: bounds on `flatPoly` from bounds on `c`,`s_e`,`s_o` -/

/-- Every unit complex number is `eθ θ`. -/
lemma exists_theta_of_unit (z : ℂ) (hz : ‖z‖ = 1) : ∃ θ : ℝ, z = Sec3.eθ θ := by
  refine ⟨z.arg, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I z
  have hz' : ((‖z‖ : ℝ) : ℂ) = 1 := by
    rw [hz]
    norm_num
  rw [hz'] at h
  simpa [Sec3.eθ] using h.symm

/-- `‖w‖ ≤ |w.re| + |w.im|`. -/
lemma norm_le_abs_re_add_abs_im (w : ℂ) : ‖w‖ ≤ |w.re| + |w.im| := by
  have hsq : ‖w‖ ^ 2 ≤ (|w.re| + |w.im|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_abs w.re, sq_abs w.im, abs_nonneg w.re, abs_nonneg w.im]
  have h1 : ‖w‖ ≤ Real.sqrt ((|w.re| + |w.im|) ^ 2) :=
    (Real.le_sqrt (norm_nonneg w) (by positivity : 0 ≤ (|w.re| + |w.im|) ^ 2)).mpr hsq
  have hnn : 0 ≤ |w.re| + |w.im| := by positivity
  have h2 : Real.sqrt ((|w.re| + |w.im|) ^ 2) ≤ |w.re| + |w.im| := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]
  exact le_trans h1 h2

/-- Lower bound via the real part. -/
lemma norm_ge_abs_re (w : ℂ) : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w

/-- Lower bound via the imaginary part. -/
lemma norm_ge_abs_im (w : ℂ) : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w

/-- Multiplying by `eθ(2qθ)` does not change norms (unit factor). -/
lemma norm_eval_eq_inner (t s q : ℕ) (eps : Fin q → ℝ)
    (hm1 : ∀ r : ℕ, r < 2 ^ t → Sec3H.T t + r ≤ q)
    (hm2 : ∀ r : ℕ, r < 2 ^ t → 2 * Sec3H.T t + r ≤ q) (θ : ℝ) :
    ‖(flatPoly t s q eps).eval (Sec3.eθ θ)‖ = ‖flatInner t s q eps θ‖ := by
  rw [flatPoly_eval t s q eps hm1 hm2 θ]
  rw [norm_mul]
  have hz : ‖(Sec3.eθ θ) ^ (2 * q)‖ = 1 := by
    rw [norm_pow, Sec3.norm_eθ]
    norm_num
  rw [hz, one_mul]

/-- Coefficient of a monomial sum at `m` is the filtered sum of coefficients. -/
lemma coeff_sum_monomial {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (e : ι → ℕ) (m : ℕ) :
    (∑ i ∈ s, Polynomial.C (c i) * Polynomial.X ^ (e i)).coeff m =
      ∑ i ∈ s, if e i = m then c i else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      rw [Polynomial.coeff_add]
      rw [Polynomial.coeff_C_mul_X_pow]
      rw [ih]
      rw [Finset.sum_insert has]
      congr 1
      by_cases h : e a = m
      · simp [h]
      · have h2 : ¬ m = e a := by intro hm; exact h hm.symm
        simp [h, h2]

/-- `coeff (X^(2q)) m = if m = 2q then 1 else 0`. -/
lemma coeff_X_pow_twoq (q m : ℕ) :
    (Polynomial.X ^ (2 * q) : ℂ[X]).coeff m = if m = 2 * q then (1 : ℂ) else 0 := by
  by_cases h : m = 2 * q
  · simp [h]
  · simp [h]


/-! ### Quadrant reduction for `c` and `|s_o|` -/

/-! ### Quadrant reduction for `c` and `|s_o|` -/

/-- `|sOdd|` is `2π`-periodic. -/
lemma sOdd_abs_periodic (q : ℕ) (eps : Fin q → ℝ) (θ : ℝ) :
    |S5.sOdd q eps (θ + 2 * Real.pi)| = |S5.sOdd q eps θ| := by
  rw [S5.sOdd_periodic q eps θ]

/-- `c` is invariant under `θ ↦ θ + (k : ℝ)·2π` for every integer `k`. -/
lemma c_int_two_pi (t : ℕ) (k : ℤ) (θ : ℝ) :
    Sec3.c t (θ + (k : ℝ) * (2 * Real.pi)) = Sec3.c t θ := by
  have hper : Function.Periodic (fun x : ℝ => Sec3.c t x) (2 * Real.pi) := by
    intro x
    exact Sec3H.c_periodic t x
  simpa using hper.int_mul k θ

/-- Every real is `2π`-congruent to `[0, 2π)`. -/
lemma period_reduce_c_sOdd (t q : ℕ) (eps : Fin q → ℝ) (θ : ℝ) :
    ∃ φ : ℝ, φ ∈ Set.Ico 0 (2 * Real.pi) ∧ Sec3.c t φ = Sec3.c t θ ∧
      |S5.sOdd q eps θ| = |S5.sOdd q eps φ| := by
  let a := θ / (2 * Real.pi)
  let qz : ℤ := Int.floor a
  let φ : ℝ := Int.fract a * (2 * Real.pi)
  have h2pi : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hφeq : φ + (qz : ℝ) * (2 * Real.pi) = θ := by
    dsimp [φ, qz, a]
    rw [Int.fract]
    field_simp [ne_of_gt h2pi]
    ring
  refine ⟨φ, ?mem, ?c, ?so⟩
  · have hf0 : 0 ≤ Int.fract a := Int.fract_nonneg a
    have hf1 : Int.fract a < 1 := Int.fract_lt_one a
    constructor
    · dsimp [φ]
      exact mul_nonneg hf0 (by nlinarith)
    · dsimp [φ]
      simpa using (mul_lt_mul_of_pos_right hf1 h2pi)
  · have hval : Sec3.c t θ = Sec3.c t φ := by
      rw [← hφeq]
      exact c_int_two_pi t qz φ
    exact hval.symm
  · have hper : Function.Periodic (fun x : ℝ => |S5.sOdd q eps x|) (2 * Real.pi) := by
      intro x
      exact sOdd_abs_periodic q eps x
    have hval : |S5.sOdd q eps (φ + (qz : ℝ) * (2 * Real.pi))| = |S5.sOdd q eps φ| := by
      simpa using hper.int_mul qz φ
    rw [← hφeq]
    exact hval

/-- Quadrant reduction preserving both `c` and `|s_o|`. -/
lemma reduce_to_quadrant_c_sOdd (t q : ℕ) (eps : Fin q → ℝ) (θ : ℝ) :
    ∃ φ : ℝ, φ ∈ Set.Icc 0 (Real.pi / 2) ∧ Sec3.c t φ = Sec3.c t θ ∧
      |S5.sOdd q eps θ| = |S5.sOdd q eps φ| := by
  rcases period_reduce_c_sOdd t q eps θ with ⟨φ, hφmem, hφc, hφso⟩
  rcases hφmem with ⟨hφ0, hφlt⟩
  by_cases hA : φ ≤ Real.pi / 2
  · refine ⟨φ, ⟨hφ0, hA⟩, hφc, hφso⟩
  · have hφA : Real.pi / 2 < φ := lt_of_not_ge hA
    by_cases hB : φ ≤ Real.pi
    · let g := Real.pi - φ
      have hgm : g ∈ Set.Icc 0 (Real.pi / 2) := by
        dsimp [g]
        constructor <;> linarith
      have hgc : Sec3.c t g = Sec3.c t θ := by
        dsimp [g]
        rw [Sec3H.c_pi_sub t φ]
        exact hφc
      have hgs : |S5.sOdd q eps θ| = |S5.sOdd q eps g| := by
        dsimp [g]
        rw [hφso]
        rw [← S5.sOdd_pi_sub q eps φ]
      refine ⟨g, hgm, hgc, hgs⟩
    · have hφB : Real.pi < φ := lt_of_not_ge hB
      by_cases hC : φ ≤ 3 * Real.pi / 2
      · let g := φ - Real.pi
        have hgm : g ∈ Set.Icc 0 (Real.pi / 2) := by
          dsimp [g]
          constructor <;> linarith
        have hgc : Sec3.c t g = Sec3.c t θ := by
          dsimp [g]
          have h1 : Sec3.c t (φ - Real.pi) = Sec3.c t φ := by
            have hcadd : Sec3.c t ((φ - Real.pi) + Real.pi) = Sec3.c t (φ - Real.pi) :=
              Sec3H.c_add_pi t (φ - Real.pi)
            rw [← hcadd]
            congr 1
            ring
          rw [h1]
          exact hφc
        have hgs : |S5.sOdd q eps θ| = |S5.sOdd q eps g| := by
          dsimp [g]
          rw [hφso]
          have h := S5.sOdd_pi_add q eps (φ - Real.pi)
          have hφ' : Real.pi + (φ - Real.pi) = φ := by ring
          rw [hφ'] at h
          rw [h, abs_neg]
        refine ⟨g, hgm, hgc, hgs⟩
      · let g := 2 * Real.pi - φ
        have hgm : g ∈ Set.Icc 0 (Real.pi / 2) := by
          dsimp [g]
          constructor <;> linarith
        have hgc : Sec3.c t g = Sec3.c t θ := by
          dsimp [g]
          have h1 : Sec3.c t (2 * Real.pi - φ) = Sec3.c t φ := by
            have h2 := Sec3H.c_periodic t (-φ)
            -- c(−φ + 2π) = c(−φ); 2π − φ = (−φ) + 2π
            have h2' : Sec3.c t (2 * Real.pi - φ) = Sec3.c t (-φ) := by
              simpa [sub_eq_add_neg, add_comm] using h2
            rw [h2']
            exact Sec3H.c_neg t φ
          rw [h1]
          exact hφc
        have hgs : |S5.sOdd q eps θ| = |S5.sOdd q eps g| := by
          dsimp [g]
          rw [hφso]
          have h1 : S5.sOdd q eps φ = S5.sOdd q eps (-(2 * Real.pi - φ) + 2 * Real.pi) := by
            congr 1
            ring
          rw [h1]
          have hper : S5.sOdd q eps (-(2 * Real.pi - φ) + 2 * Real.pi) =
              S5.sOdd q eps (-(2 * Real.pi - φ)) := S5.sOdd_periodic q eps (-(2 * Real.pi - φ))
          rw [hper]
          have hneg : S5.sOdd q eps (-(2 * Real.pi - φ)) = -S5.sOdd q eps (2 * Real.pi - φ) :=
            S5.sOdd_neg q eps (2 * Real.pi - φ)
          rw [hneg, abs_neg]
        refine ⟨g, hgm, hgc, hgs⟩


/-! ### Misc: `mt` conversions and real-absolute-value helpers -/

/-- `Sec3.m_t` and `mt` are the same. -/
lemma mt_eq_mt (a : ℕ) : Sec3.m_t a = mt a := by
  rfl

/-- `|1 + 2x| ≤ 1 + 2|x|`. -/
lemma abs_one_add_two_mul_le (x : ℝ) : |1 + 2 * x| ≤ 1 + 2 * |x| := by
  have h := abs_add_le (1 : ℝ) (2 * x)
  have h1 : |(1 : ℝ)| = 1 := by norm_num
  have h2 : |2 * x| = 2 * |x| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

/-- `|a + b| ≥ |a| − |b|`. -/
lemma abs_add_ge_sub (a b : ℝ) : |a| - |b| ≤ |a + b| := by
  have h := abs_add_le (a + b) (-b)
  have h1 : |(a + b) + -b| = |a| := by
    congr 1
    ring
  have h2 : |-b| = |b| := abs_neg b
  have h3 : |a| ≤ |a + b| + |b| := by
    simpa [h1, h2] using h
  linarith

end Flat

