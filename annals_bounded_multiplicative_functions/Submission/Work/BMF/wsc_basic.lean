import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Infrastructure for the self-contained inverse Weyl inequality (`weyl_structure_b`)

Basic lemmas about the character `eC`, the "distance to integer" predicate `MonApprox`,
the internal degree-`d` inverse Weyl statement `InverseWeyl`, the induction hypothesis
`TInvWeyl`, and elementary coefficient computations for polynomials.
-/

namespace Work.BMF
namespace WSC

open Polynomial Finset Real Complex

/-! ## The character `eC` -/

lemma norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  rw [eC, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

lemma eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  rw [eC, eC, eC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eC_neg (a : ℝ) : eC (-a) = star (eC a) := by
  rw [eC, eC]
  have h : star (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)))
      = Complex.exp (star (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ))) := by
    rw [Complex.star_def, ← Complex.exp_conj]
  rw [h]
  congr 1
  simp [Complex.conj_ofReal]

lemma eC_sub (a b : ℝ) : eC (a - b) = eC a * star (eC b) := by
  rw [sub_eq_add_neg, eC_add, eC_neg]

@[simp] lemma eC_zero : eC 0 = 1 := by simp [eC]

lemma eC_int (m : ℤ) : eC (m : ℝ) = 1 := by
  rw [eC]
  have h : (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ))
      = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

lemma eC_nat (m : ℕ) : eC (m : ℝ) = 1 := by
  simpa using eC_int (m : ℤ)

lemma norm_eC_sub_one_le (u : ℝ) : ‖eC u - 1‖ ≤ 4 * Real.pi * |u| := by
  have h2 : eC u - 1 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((u : ℝ) : ℂ)) - 1 := rfl
  rw [h2]
  have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I * ((u : ℝ) : ℂ))‖ = 2 * Real.pi * |u| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
    simp
  by_cases h : ‖(2 * (Real.pi : ℂ) * Complex.I * ((u : ℝ) : ℂ))‖ ≤ 1
  · have := Complex.norm_exp_sub_one_le h
    rw [hnorm] at this
    linarith
  · push Not at h
    have hre : (2 * (Real.pi : ℂ) * Complex.I * ((u : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    have h3 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((u : ℝ) : ℂ)) - 1‖ ≤ 2 := by
      calc ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((u : ℝ) : ℂ)) - 1‖
          ≤ ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((u : ℝ) : ℂ))‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ = Real.exp ((2 * (Real.pi : ℂ) * Complex.I * ((u : ℝ) : ℂ)).re) + 1 := by
              rw [Complex.norm_exp]; norm_num
        _ = 2 := by rw [hre]; norm_num
    rw [hnorm] at h
    linarith

lemma norm_eC_sub_le (a b : ℝ) : ‖eC a - eC b‖ ≤ 4 * Real.pi * |a - b| := by
  have h1 : eC a - eC b = eC b * (eC (a - b) - 1) := by
    rw [mul_sub, mul_one, ← eC_add, add_comm]
    congr 1
    ring_nf
  rw [h1, norm_mul, norm_eC, one_mul]
  exact norm_eC_sub_one_le (a - b)

/-! ## Powers and the geometric series -/

lemma eC_nat_mul (n : ℕ) (b : ℝ) : eC ((n : ℝ) * b) = (eC b) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℝ) * b = (k : ℝ) * b + b by push_cast; ring, eC_add, ih,
        pow_succ]

lemma norm_exp_I_sub_one (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (x / 2)| := by
  have hre : (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := Complex.exp_ofReal_mul_I_re x
  have him : (Complex.exp ((x : ℂ) * Complex.I)).im = Real.sin x := Complex.exp_ofReal_mul_I_im x
  have hsq : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ^ 2 = 4 * (Real.sin (x / 2)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, hre, him]
    have hc : Real.cos x = 1 - 2 * (Real.sin (x / 2)) ^ 2 := by
      have h := Real.cos_two_mul (x / 2)
      rw [show 2 * (x / 2) = x by ring] at h
      rw [h]
      nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    have hs : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
      have h := Real.sin_two_mul (x / 2)
      rw [show 2 * (x / 2) = x by ring] at h
      rw [h]
    rw [hc, hs]
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  rw [← Real.sqrt_sq (norm_nonneg _), hsq,
    show (4 : ℝ) * (Real.sin (x / 2)) ^ 2 = (2 * Real.sin (x / 2)) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_mul, abs_two]

lemma norm_eC_sub_one_eq (b : ℝ) : ‖eC b - 1‖ = 2 * |Real.sin (Real.pi * b)| := by
  have h : eC b = Complex.exp (((2 * Real.pi * b : ℝ) : ℂ) * Complex.I) := by
    rw [eC]; push_cast; ring_nf
  rw [h, norm_exp_I_sub_one]
  congr 2
  ring

lemma norm_eC_sub_one_ge (b : ℝ) (hb : |b| ≤ 1 / 2) : 4 * |b| ≤ ‖eC b - 1‖ := by
  rw [norm_eC_sub_one_eq]
  have h1 : |Real.pi * b| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, hb]
  have h2 := Real.mul_abs_le_abs_sin h1
  rw [abs_mul, abs_of_pos Real.pi_pos] at h2
  have h3 : 2 / Real.pi * (Real.pi * |b|) = 2 * |b| := by field_simp
  rw [h3] at h2
  linarith

/-- A non-zero linear phase of small size has an exponential sum of size at most
`1/(2 * ‖θ‖)`. -/
lemma geom_sum_bound (θ : ℝ) (m : ℤ) (hm : |θ - m| ≤ 1 / 2) (hm0 : θ ≠ (m : ℝ)) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, eC ((n : ℝ) * θ)‖ ≤ 1 / (2 * |θ - m|) := by
  have hb_ne : θ - (m : ℝ) ≠ 0 := sub_ne_zero.mpr hm0
  have hsum : (∑ n ∈ Finset.range N, eC ((n : ℝ) * θ))
      = ∑ n ∈ Finset.range N, (eC (θ - m)) ^ n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [show (n : ℝ) * θ = (n : ℝ) * (θ - m) + (n : ℝ) * (m : ℝ) by ring, eC_add, eC_nat_mul]
    have : ((n : ℝ) * (m : ℝ)) = (((n : ℕ) * m : ℤ) : ℝ) := by push_cast; ring
    rw [this, eC_int, mul_one]
  rw [hsum]
  have hzpos : 0 < ‖eC (θ - m) - 1‖ := by
    have h1 := norm_eC_sub_one_ge (θ - m) hm
    have h2 : 0 < |θ - m| := abs_pos.mpr hb_ne
    linarith
  have hkey : (∑ n ∈ Finset.range N, (eC (θ - m)) ^ n) * (eC (θ - m) - 1)
      = (eC (θ - m)) ^ N - 1 := geom_sum_mul _ _
  have h1 : ‖∑ n ∈ Finset.range N, (eC (θ - m)) ^ n‖ * ‖eC (θ - m) - 1‖ ≤ 2 := by
    rw [← norm_mul, hkey]
    calc ‖(eC (θ - m)) ^ N - 1‖ ≤ ‖(eC (θ - m)) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_eC]; norm_num
  have h2 : ‖∑ n ∈ Finset.range N, (eC (θ - m)) ^ n‖ ≤ 2 / ‖eC (θ - m) - 1‖ :=
    (le_div_iff₀ hzpos).mpr h1
  have h3 : 2 / ‖eC (θ - m) - 1‖ ≤ 1 / (2 * |θ - m|) := by
    have hbpos : 0 < |θ - m| := abs_pos.mpr hb_ne
    have hN2 : 0 < 2 * |θ - m| := by linarith
    have hle : 2 * |θ - m| ≤ ‖eC (θ - m) - 1‖ / 2 := by
      have h4 := norm_eC_sub_one_ge (θ - m) hm
      linarith
    have h5 := one_div_le_one_div_of_le hN2 hle
    rw [show 2 / ‖eC (θ - m) - 1‖ = 1 / (‖eC (θ - m) - 1‖ / 2) by ring]
    exact h5
  linarith

/-- A polynomial of `natDegree ≤ 1` is its constant plus linear term. -/
lemma eval_of_natDegree_le_one (g : ℝ[X]) (hg : g.natDegree ≤ 1) (n : ℕ) :
    g.eval (n : ℝ) = g.coeff 0 + (n : ℝ) * g.coeff 1 := by
  have h : g = Polynomial.C (g.coeff 0) + Polynomial.C (g.coeff 1) * Polynomial.X := by
    ext i
    match i with
    | 0 => simp
    | 1 => simp
    | (k + 2) =>
        have h1 : g.coeff (k + 2) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [h1]
  rw [h, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  simp
  ring

/-! ## `MonApprox` and the internal inverse Weyl statement -/

/-- `q * x` is within `ε` of an integer. -/
def MonApprox (q : ℕ) (x ε : ℝ) : Prop := ∃ m : ℤ, |(q : ℝ) * x - m| ≤ ε

lemma MonApprox.mono {q : ℕ} {x ε ε' : ℝ} (h : MonApprox q x ε) (hε : ε ≤ ε') :
    MonApprox q x ε' :=
  ⟨h.choose, le_trans h.choose_spec hε⟩

/-- **Internal inverse Weyl statement at degree `d`.** If a real polynomial `g` of
`natDegree ≤ d` has an exponential sum of size at least `δ N` over `[0, N)`, then there is a
common denominator `q ≤ Q` which puts every coefficient of `g` (degrees `1, …, d`) within
`C / N^l` of an integer multiple of `1/q`. -/
def InverseWeyl (d : ℕ) (δ : ℝ) (Q : ℕ) (C : ℝ) : Prop :=
  0 < C ∧ ∀ g : ℝ[X], g.natDegree ≤ d → ∀ N : ℕ, 1 ≤ N →
    δ * (N : ℝ) ≤ ‖∑ n ∈ Finset.range N, eC (g.eval (n : ℝ))‖ →
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧
      ∀ l ∈ Finset.Icc 1 d, MonApprox q (g.coeff l) (C / (N : ℝ) ^ l)

/-- The induction hypothesis: the internal inverse Weyl statement holds at degree `d` for
every `0 < δ ≤ 1`. -/
def TInvWeyl (d : ℕ) : Prop := ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ Q C, InverseWeyl d δ Q C

lemma MonApprox.mul_nat {q : ℕ} {x ε : ℝ} (h : MonApprox q x ε) (c : ℕ) :
    MonApprox (q * c) x ((c : ℝ) * ε) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m * c, ?_⟩
  have : (((q * c : ℕ) : ℝ) * x - ((m * c : ℤ) : ℝ))
      = (c : ℝ) * ((q : ℝ) * x - (m : ℝ)) := by push_cast; ring
  rw [this, abs_mul, abs_of_nonneg (Nat.cast_nonneg c)]
  exact mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg c)

lemma MonApprox.one_half (x : ℝ) : MonApprox 1 x (1 / 2) :=
  ⟨round x, by simpa using abs_sub_round x⟩

open Classical in
/-- The set of `n ∈ [1, N)` with `‖α n‖ ≤ ε` (in the sense of `MonApprox 1`). -/
noncomputable def goodSet (α ε : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n : ℕ => 1 ≤ n ∧ ∃ m : ℤ, |α * ((n : ℕ) : ℝ) - (m : ℝ)| ≤ ε)

/-- An explicit "large enough" scale governing the descent step: the descent may shorten the
interval to a `1/descentScale`-fraction of its original length. -/
noncomputable def descentScale (d : ℕ) (q : ℕ) (Cd δ : ℝ) : ℝ :=
  4 * 10 ^ 6 * (Cd + 1) * (q : ℝ) ^ (d + 2) * (((d + 1).factorial : ℕ) : ℝ) ^ (d + 2) / δ + 4

lemma MonApprox.mul_pow_inv {q : ℕ} {c ε : ℝ} (Q : ℕ) (j : ℕ)
    (h : MonApprox q (((Q : ℝ) ^ j) * c) ε) : MonApprox (q * Q ^ j) c ε := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have : (((q * Q ^ j : ℕ)) : ℝ) * c - (m : ℝ) = (q : ℝ) * (((Q : ℝ) ^ j) * c) - (m : ℝ) := by
    push_cast; ring
  rw [this]; exact hm

lemma MonApprox.sum_int {ι : Type*} (s : Finset ι) {q : ℕ} (x ε : ι → ℝ)
    (w : ι → ℤ) (h : ∀ i ∈ s, MonApprox q (x i) (ε i)) :
    MonApprox q (∑ i ∈ s, (w i : ℝ) * x i) (∑ i ∈ s, |(w i : ℝ)| * ε i) := by
  classical
  set m : ι → ℤ := fun i => if hi : i ∈ s then (h i hi).choose else 0 with hm
  refine ⟨∑ i ∈ s, w i * m i, ?_⟩
  have hkey : ∀ i ∈ s, |(q : ℝ) * x i - (m i : ℝ)| ≤ ε i := by
    intro i hi
    have hmi : m i = (h i hi).choose := by simp only [hm]; rw [dite_eq_left hi]
    rw [hmi]; exact (h i hi).choose_spec
  have hsplit : (q : ℝ) * (∑ i ∈ s, (w i : ℝ) * x i) - ((∑ i ∈ s, w i * m i : ℤ) : ℝ)
      = ∑ i ∈ s, (w i : ℝ) * ((q : ℝ) * x i - (m i : ℝ)) := by
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsplit]
  calc ‖∑ i ∈ s, (w i : ℝ) * ((q : ℝ) * x i - (m i : ℝ))‖
      ≤ ∑ i ∈ s, ‖(w i : ℝ) * ((q : ℝ) * x i - (m i : ℝ))‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, |(w i : ℝ)| * ‖(q : ℝ) * x i - (m i : ℝ)‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_mul, Real.norm_eq_abs]
    _ ≤ ∑ i ∈ s, |(w i : ℝ)| * ε i :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hkey i hi) (abs_nonneg _)

lemma descentScale_mono_nat {d : ℕ} {q q' : ℕ} {Cd Cd' : ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hCd : 0 ≤ Cd) (hq : (q : ℝ) ≤ (q' : ℝ)) (hC : Cd ≤ Cd') :
    descentScale d q Cd δ ≤ descentScale d q' Cd' δ := by
  unfold descentScale
  have hA : 4 * 10 ^ 6 * (Cd + 1) * (q : ℝ) ^ (d + 2) * (((d + 1).factorial : ℕ) : ℝ) ^ (d + 2)
      ≤ 4 * 10 ^ 6 * (Cd' + 1) * (q' : ℝ) ^ (d + 2)
        * (((d + 1).factorial : ℕ) : ℝ) ^ (d + 2) := by
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have h1 := pow_le_pow_left₀ hq0 hq (d + 2)
    have h2 : Cd + 1 ≤ Cd' + 1 := by linarith
    have h3 : (Cd + 1) * (q : ℝ) ^ (d + 2) ≤ (Cd' + 1) * (q' : ℝ) ^ (d + 2) :=
      mul_le_mul h2 h1 (by positivity) (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 4 * 10 ^ 6)
    have h5 := mul_le_mul_of_nonneg_right h4
      (by positivity : (0 : ℝ) ≤ (((d + 1).factorial : ℕ) : ℝ) ^ (d + 2))
    linarith [h4, h5]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have h2 := mul_le_mul_of_nonneg_right hA (by positivity : (0 : ℝ) ≤ δ⁻¹)
  linarith

lemma descentScale_aux (d : ℕ) (q : ℕ) (Cd δ : ℝ) (hCd : 0 ≤ Cd) (hδ : 0 < δ) :
    0 ≤ 4 * 10 ^ 6 * (Cd + 1) * (q : ℝ) ^ (d + 2)
      * (((d + 1).factorial : ℕ) : ℝ) ^ (d + 2) / δ :=
  div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4 * 10^6)
    (by linarith)) (by positivity)) (by positivity)) (le_of_lt hδ)

lemma descentScale_pos (d : ℕ) (q : ℕ) (Cd δ : ℝ) (hCd : 0 ≤ Cd) (hδ : 0 < δ) :
    0 < descentScale d q Cd δ := by
  unfold descentScale
  have := descentScale_aux d q Cd δ hCd hδ
  linarith

lemma le_descentScale (d : ℕ) (q : ℕ) (Cd δ : ℝ) (hCd : 0 ≤ Cd) (hδ : 0 < δ) :
    4 ≤ descentScale d q Cd δ := by
  unfold descentScale
  have := descentScale_aux d q Cd δ hCd hδ
  linarith

/-- Division is monotone for positive denominators. -/
lemma div_le_div_of_pos {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d :=
  (div_le_iff₀ hb).mpr (by
    have h' : a ≤ (c * b) / d := (le_div_iff₀ hd).mpr h
    calc a ≤ (c * b) / d := h'
      _ = (c / d) * b := by ring)

/-! ## Elementary coefficient computations -/

lemma natDegree_le_of_mem_degreeLE {k : ℕ} {g : ℝ[X]}
    (h : g ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ)) : g.natDegree ≤ k :=
  Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp h)

/-- The coefficient of a "dilation" `p(cX)`. -/
lemma coeff_comp_C_mul_X (p : ℝ[X]) (c : ℝ) (j : ℕ) :
    (p.comp (C c * X)).coeff j = c ^ j * p.coeff j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add]
      ring
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.pow_comp, Polynomial.X_comp, mul_pow]
      by_cases h : j = n
      · subst h
        simp only [Polynomial.coeff_C_mul, ← Polynomial.C_pow, Polynomial.coeff_X_pow, ↓reduceIte,
          mul_one]
        ring
      · have hl : (C a * (C c ^ n * X ^ n)).coeff j = 0 := by
          rw [Polynomial.coeff_C_mul, ← Polynomial.C_pow, Polynomial.coeff_C_mul,
            Polynomial.coeff_X_pow]
          simp [h]
        have hr : (C a * X ^ n).coeff j = 0 := by
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
          simp [h]
        rw [hl, hr, mul_zero]

/-- Coefficients of `g(cX + b)`: they are `c^j` times the Taylor coefficients of `g` at `b`. -/
lemma coeff_comp_C_mul_X_add_C (g : ℝ[X]) (c b : ℝ) (j : ℕ) :
    (g.comp (C c * X + C b)).coeff j = c ^ j * (Polynomial.taylor b g).coeff j := by
  have hcomp : g.comp (C c * X + C b) = (Polynomial.taylor b g).comp (C c * X) := by
    rw [Polynomial.taylor_apply, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
      Polynomial.C_comp]
  rw [hcomp, coeff_comp_C_mul_X]

/-- Taylor coefficients of a polynomial: triangular expansion via the leading behaviour. -/
lemma taylor_coeff_eq (g : ℝ[X]) (b : ℝ) (d : ℕ) (hgd : g.natDegree ≤ d) (j : ℕ) :
    (Polynomial.taylor b g).coeff j =
      ∑ i ∈ Finset.Icc j d, g.coeff i * b ^ (i - j) * (i.choose j : ℝ) := by
  have key : (Polynomial.taylor b g).coeff j =
      ∑ i ∈ g.support, g.coeff i * b ^ (i - j) * (i.choose j : ℝ) := by
    rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_apply, Polynomial.sum_def,
        Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.eval_monomial]
    ring
  rw [key]
  have hsub : g.support ⊆ Finset.range (d + 1) := by
    intro i hi
    rw [Finset.mem_range]
    have := Polynomial.le_natDegree_of_mem_supp i hi
    omega
  have hzero : ∀ x ∈ Finset.range (d + 1), x ∉ g.support →
      g.coeff x * b ^ (x - j) * (x.choose j : ℝ) = 0 := by
    intro x _ hxs
    have hc : g.coeff x = 0 := by
      by_contra h
      exact hxs (Polynomial.mem_support_iff.mpr h)
    simp [hc]
  rw [Finset.sum_subset hsub hzero]
  symm
  apply Finset.sum_subset
  · intro x hx; rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
  · intro x hx hxnot
    rw [Finset.mem_range] at hx
    have hxj : x < j := by
      by_contra h
      push Not at h
      exact hxnot (by rw [Finset.mem_Icc]; omega)
    simp [Nat.choose_eq_zero_of_lt hxj]

end WSC
end Work.BMF
