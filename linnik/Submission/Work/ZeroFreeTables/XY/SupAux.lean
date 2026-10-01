/-
# ZeroFreeTables — SupAux
-/
import Mathlib
import Submission.Commons.Algebra.BigOperators.sum_range_mul_eq

open Finset Complex

namespace Work.ZeroFreeTables.XY

lemma I_pow_even (n : ℕ) : (Complex.I : ℂ)^(2*n) = ((((-1:ℝ)):ℂ))^n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1) = 2*k+2 by ring, pow_add, ih,
        show (Complex.I:ℂ)^2 = -1 from by rw [pow_two, Complex.I_mul_I],
        show ((-1:ℂ)) = ((((-1:ℝ)):ℂ)) from by norm_num, ← pow_succ]

lemma I_pow_odd (n : ℕ) : (Complex.I : ℂ)^(2*n+1) = ((((-1:ℝ)):ℂ))^n * Complex.I := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1)+1 = (2*k+1)+2 by ring, pow_add, ih,
        show (Complex.I:ℂ)^2 = -1 from by rw [pow_two, Complex.I_mul_I],
        show ((-1:ℂ)) = ((((-1:ℝ)):ℂ)) from by norm_num]
    ring

lemma uI_pow_even (u : ℂ) (m : ℕ) : (u * Complex.I)^(2*m) = u^(2*m) * ((((-1:ℝ)):ℂ))^m := by
  rw [mul_pow, I_pow_even]

lemma uI_pow_odd (u : ℂ) (m : ℕ) :
    (u * Complex.I)^(2*m+1) = u^(2*m+1) * ((((-1:ℝ)):ℂ))^m * Complex.I := by
  rw [mul_pow, I_pow_odd]; ring

noncomputable def cosTaylor (u : ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), (-1:ℝ)^j * u^(2*j) / (Nat.factorial (2*j) : ℝ)

noncomputable def sinTaylor (u : ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), (-1:ℝ)^j * u^(2*j+1) / (Nat.factorial (2*j+1) : ℝ)

lemma sum_re (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  rw [← Complex.coe_reAddGroupHom]
  exact map_sum Complex.reAddGroupHom f s

lemma sum_im (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  rw [← Complex.coe_imAddGroupHom]
  exact map_sum Complex.imAddGroupHom f s

lemma natCast_re (n : ℕ) : ((n:ℂ)).re = n := by
  rw [← Complex.ofReal_natCast n, Complex.ofReal_re]

lemma natCast_im (n : ℕ) : ((n:ℂ)).im = 0 := by
  rw [← Complex.ofReal_natCast n, Complex.ofReal_im]

lemma ofReal_pow_re (a : ℝ) (n : ℕ) : (((a:ℂ)^n)).re = a^n := by
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma ofReal_pow_im (a : ℝ) (n : ℕ) : (((a:ℂ)^n)).im = 0 := by
  rw [← Complex.ofReal_pow, Complex.ofReal_im]

/-- The `(2K+2)`-term exponential Taylor sum at `u * I` splits into the cosine and sine
Taylor sums. -/
lemma exp_sum_split (u : ℝ) (K : ℕ) :
    (∑ m ∈ Finset.range (2*(K+1)), ((u:ℂ)*Complex.I)^m / (Nat.factorial m : ℂ))
      = ((cosTaylor u K : ℝ) : ℂ) + ((sinTaylor u K : ℝ) : ℂ) * Complex.I := by
  rw [Commons.Algebra.BigOperators.sum_range_mul_eq
        (fun m => ((u:ℂ)*Complex.I)^m / (Nat.factorial m : ℂ)) 2 (K+1)]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.zero_add]
  unfold cosTaylor sinTaylor
  rw [Complex.ofReal_sum, Complex.ofReal_sum]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [uI_pow_even]; push_cast; ring
  · have hterm : ∀ b : ℕ, ((u:ℂ)*Complex.I)^(1+2*b) / (Nat.factorial (1+2*b) : ℂ)
        = ((((-1:ℝ)^b * u^(2*b+1) / (Nat.factorial (2*b+1) : ℝ) : ℝ)) : ℂ) * Complex.I := by
      intro b
      rw [show 1+2*b = 2*b+1 by ring, uI_pow_odd]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_mul]

lemma re_exp_sum (u : ℝ) (K : ℕ) :
    (∑ m ∈ Finset.range (2*(K+1)), ((u:ℂ)*Complex.I)^m / (Nat.factorial m : ℂ)).re
      = cosTaylor u K := by
  rw [exp_sum_split, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
      neg_zero, add_zero]

lemma im_exp_sum (u : ℝ) (K : ℕ) :
    (∑ m ∈ Finset.range (2*(K+1)), ((u:ℂ)*Complex.I)^m / (Nat.factorial m : ℂ)).im
      = sinTaylor u K := by
  rw [exp_sum_split, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
      zero_add]

theorem cosTaylor_bound (u : ℝ) (K : ℕ) (h : |u| ≤ (K:ℝ) + 1) :
    |Real.cos u - cosTaylor u K| ≤ 2 * |u|^(2*K+2) / (Nat.factorial (2*K+2) : ℝ) := by
  have hnorm : ‖((u:ℂ) * Complex.I)‖ = |u| := by
    rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb : ‖((u:ℂ) * Complex.I)‖ / ((Nat.succ (2*K+2) : ℕ) : ℝ) ≤ 1/2 := by
    rw [hnorm]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ((Nat.succ (2*K+2) : ℕ) : ℝ))]
    push_cast
    linarith [abs_nonneg u, h]
  have hexp := Complex.exp_bound' (x := (u:ℂ)*Complex.I) (n := 2*K+2) hb
  have h1 : Real.cos u = (Complex.exp ((u:ℂ)*Complex.I)).re := by
    rw [Complex.exp_ofReal_mul_I, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
        Complex.ofReal_im, neg_zero, add_zero]
  have h2 : cosTaylor u K
      = (∑ m ∈ Finset.range (2*K+2), ((u:ℂ)*Complex.I)^m / (Nat.factorial m : ℂ)).re := by
    rw [show 2*K+2 = 2*(K+1) by ring, re_exp_sum]
  have hmain : |(Complex.exp ((u:ℂ)*Complex.I)
        - ∑ m ∈ Finset.range (2*K+2), ((u:ℂ)*Complex.I)^m / (Nat.factorial m : ℂ)).re|
      ≤ 2 * |u|^(2*K+2) / (Nat.factorial (2*K+2) : ℝ) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    calc ‖Complex.exp ((u:ℂ)*Complex.I)
          - ∑ m ∈ Finset.range (2*K+2), ((u:ℂ)*Complex.I)^m / (Nat.factorial m : ℂ)‖
        ≤ ‖((u:ℂ) * Complex.I)‖ ^ (2*K+2) / (Nat.factorial (2*K+2) : ℝ) * 2 := hexp
      _ = 2 * |u|^(2*K+2) / (Nat.factorial (2*K+2) : ℝ) := by rw [hnorm]; ring
  rw [h1, h2, ← Complex.sub_re]
  exact hmain

theorem sinTaylor_bound (u : ℝ) (K : ℕ) (h : |u| ≤ (K:ℝ) + 1) :
    |Real.sin u - sinTaylor u K| ≤ 2 * |u|^(2*K+2) / (Nat.factorial (2*K+2) : ℝ) := by
  have hnorm : ‖((u:ℂ) * Complex.I)‖ = |u| := by
    rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb : ‖((u:ℂ) * Complex.I)‖ / ((Nat.succ (2*K+2) : ℕ) : ℝ) ≤ 1/2 := by
    rw [hnorm]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ((Nat.succ (2*K+2) : ℕ) : ℝ))]
    push_cast
    linarith [abs_nonneg u, h]
  have hexp := Complex.exp_bound' (x := (u:ℂ)*Complex.I) (n := 2*K+2) hb
  have h1 : Real.sin u = (Complex.exp ((u:ℂ)*Complex.I)).im := by
    rw [Complex.exp_ofReal_mul_I, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
        Complex.ofReal_re, zero_add]
  have h2 : sinTaylor u K
      = (∑ m ∈ Finset.range (2*K+2), ((u:ℂ)*Complex.I)^m / (Nat.factorial m : ℂ)).im := by
    rw [show 2*K+2 = 2*(K+1) by ring, im_exp_sum]
  have hmain : |(Complex.exp ((u:ℂ)*Complex.I)
        - ∑ m ∈ Finset.range (2*K+2), ((u:ℂ)*Complex.I)^m / (Nat.factorial m : ℂ)).im|
      ≤ 2 * |u|^(2*K+2) / (Nat.factorial (2*K+2) : ℝ) := by
    refine (Complex.abs_im_le_norm _).trans ?_
    calc ‖Complex.exp ((u:ℂ)*Complex.I)
          - ∑ m ∈ Finset.range (2*K+2), ((u:ℂ)*Complex.I)^m / (Nat.factorial m : ℂ)‖
        ≤ ‖((u:ℂ) * Complex.I)‖ ^ (2*K+2) / (Nat.factorial (2*K+2) : ℝ) * 2 := hexp
      _ = 2 * |u|^(2*K+2) / (Nat.factorial (2*K+2) : ℝ) := by rw [hnorm]; ring
  rw [h1, h2, ← Complex.sub_im]
  exact hmain

/-! ## Rational bounds for the exponentials used in the grid evaluation -/

theorem exp_one_bounds : (2718281828:ℝ)/1000000000 ≤ Real.exp 1 ∧ Real.exp 1 ≤ (2718281829:ℝ)/1000000000 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) 14
    norm_num at h
    linarith
  · have h := Real.exp_bound' (x := 1) (by norm_num) (by norm_num) (n := 14) (by norm_num)
    norm_num at h
    linarith

theorem exp_half_bounds : (1648721270:ℝ)/1000000000 ≤ Real.exp (1/2) ∧ Real.exp (1/2) ≤ (1648721271:ℝ)/1000000000 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := 1/2) (by norm_num) 12
    norm_num at h
    linarith
  · have h := Real.exp_bound' (x := 1/2) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    norm_num at h
    linarith

theorem exp_1_5_bounds : (4481689067:ℝ)/1000000000 ≤ Real.exp (3/2) ∧ Real.exp (3/2) ≤ (4481689073:ℝ)/1000000000 := by
  rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.exp_add]
  obtain ⟨h1,h2⟩ := exp_one_bounds
  obtain ⟨h3,h4⟩ := exp_half_bounds
  constructor
  · nlinarith [Real.exp_pos (1:ℝ), Real.exp_pos (1/2:ℝ)]
  · nlinarith [Real.exp_pos (1:ℝ), Real.exp_pos (1/2:ℝ)]

theorem exp_723_bounds : (2060605764:ℝ)/1000000000 ≤ Real.exp (723/1000) ∧ Real.exp (723/1000) ≤ (2060605765:ℝ)/1000000000 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := 723/1000) (by norm_num) 12
    norm_num at h
    linarith
  · have h := Real.exp_bound' (x := 723/1000) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    norm_num at h
    linarith

theorem exp_558_bounds : (1747174654:ℝ)/1000000000 ≤ Real.exp (558/1000) ∧ Real.exp (558/1000) ≤ (1747174655:ℝ)/1000000000 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := 558/1000) (by norm_num) 12
    norm_num at h
    linarith
  · have h := Real.exp_bound' (x := 558/1000) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    norm_num at h
    linarith

theorem exp_482_bounds : (1619309785:ℝ)/1000000000 ≤ Real.exp (482/1000) ∧ Real.exp (482/1000) ≤ (1619309786:ℝ)/1000000000 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := 482/1000) (by norm_num) 12
    norm_num at h
    linarith
  · have h := Real.exp_bound' (x := 482/1000) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    norm_num at h
    linarith

theorem exp_6405_bounds : (1897429356:ℝ)/1000000000 ≤ Real.exp (6405/10000) ∧ Real.exp (6405/10000) ≤ (1897429357:ℝ)/1000000000 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := 6405/10000) (by norm_num) 12
    norm_num at h
    linarith
  · have h := Real.exp_bound' (x := 6405/10000) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    norm_num at h
    linarith

theorem exp_6675_bounds : (1949357829:ℝ)/1000000000 ≤ Real.exp (6675/10000) ∧ Real.exp (6675/10000) ≤ (1949357830:ℝ)/1000000000 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := 6675/10000) (by norm_num) 12
    norm_num at h
    linarith
  · have h := Real.exp_bound' (x := 6675/10000) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    norm_num at h
    linarith

theorem exp_612_bounds : (1844115944:ℝ)/1000000000 ≤ Real.exp (612/1000) ∧ Real.exp (612/1000) ≤ (1844115945:ℝ)/1000000000 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := 612/1000) (by norm_num) 12
    norm_num at h
    linarith
  · have h := Real.exp_bound' (x := 612/1000) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    norm_num at h
    linarith

end Work.ZeroFreeTables.XY
