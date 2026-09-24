import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive
import Submission.Commons.NumberTheory.DirichletCharacter.interval_sum_bound

open scoped BigOperators ComplexConjugate
open Complex
set_option autoImplicit false

namespace Commons.NumberTheory.Linnik



private lemma stdAddChar_norm (q : ℕ) [NeZero q] (a : ZMod q) : ‖ZMod.stdAddChar a‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe (ZMod.toCircle a)

private lemma stdAddChar_ne_one_of_ne_zero (q : ℕ) [NeZero q] {k : ZMod q} (hk : k ≠ 0) :
    ZMod.stdAddChar k ≠ 1 := by
  intro h
  exact hk (ZMod.injective_stdAddChar (by simp [← h]))

private lemma geomSum_norm_le {w : ℂ} (hw1 : w ≠ 1) (hwn : ‖w‖ ≤ 1) (x : ℕ) :
    ‖∑ i ∈ Finset.range x, w ^ i‖ ≤ 2 / ‖w - 1‖ := by
  rw [geom_sum_eq hw1]
  rw [norm_div]
  have hnum : ‖w ^ x - 1‖ ≤ 2 := by
    have hpow : ‖w ^ x‖ ≤ 1 := by
      calc ‖w ^ x‖ ≤ ‖w‖ ^ x := norm_pow_le w x
      _ ≤ 1 := by exact pow_le_one₀ (norm_nonneg w) hwn (n := x)
    have hsub : ‖w ^ x - 1‖ ≤ ‖w ^ x‖ + ‖(1 : ℂ)‖ := norm_sub_le (w ^ x) (1 : ℂ)
    rw [norm_one] at hsub
    linarith
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg (w - 1)) : _)

private lemma charGeomSum_le {q : ℕ} [NeZero q] (x : ℕ) (k : ZMod q) (hk : k ≠ 0) :
    ‖∑ n ∈ Finset.range x, ZMod.stdAddChar (k * (n : ZMod q))‖
      ≤ 2 / ‖1 - ZMod.stdAddChar k‖ := by
  have hw1 : ZMod.stdAddChar k ≠ 1 := stdAddChar_ne_one_of_ne_zero q hk
  have hpow (n : ℕ) : ZMod.stdAddChar (k * (n : ZMod q)) = (ZMod.stdAddChar k) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        ZMod.stdAddChar (k * ((n + 1 : ℕ) : ZMod q))
            = ZMod.stdAddChar (k * ((n : ZMod q) + 1)) := by congr 1; norm_num
        _ = ZMod.stdAddChar (k * (n : ZMod q) + k * 1) := by rw [mul_add]
        _ = ZMod.stdAddChar (k * (n : ZMod q) + k) := by rw [mul_one]
        _ = ZMod.stdAddChar (k * (n : ZMod q)) * ZMod.stdAddChar k := AddChar.map_add_eq_mul _ _ _
        _ = (ZMod.stdAddChar k) ^ n * ZMod.stdAddChar k := by rw [ih]
        _ = (ZMod.stdAddChar k) ^ (n + 1) := by rw [pow_succ]
  calc
    ‖∑ n ∈ Finset.range x, ZMod.stdAddChar (k * (n : ZMod q))‖
        = ‖∑ n ∈ Finset.range x, (ZMod.stdAddChar k) ^ n‖ := by
          apply congrArg norm
          apply Finset.sum_congr rfl
          intro n _
          exact hpow n
    _ ≤ 2 / ‖1 - ZMod.stdAddChar k‖ := by
          rw [norm_sub_rev]
          exact geomSum_norm_le (w := ZMod.stdAddChar k) hw1 (by rw [stdAddChar_norm q k]) x

private lemma fourier_pointwise {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (z : ZMod q) :
    (χ z : ℂ) = (q : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar *
      (∑ k : ZMod q, (χ⁻¹ (-k) : ℂ) * ZMod.stdAddChar (k * z)) := by
  let Φ : ZMod q → ℂ := fun a => (χ a : ℂ)
  let τ : ℂ := gaussSum χ ZMod.stdAddChar
  have hsym : ZMod.dft.symm (ZMod.dft Φ) = Φ := ZMod.dft.symm_apply_apply Φ
  calc
    (χ z : ℂ) = ZMod.dft.symm (ZMod.dft Φ) z := by
      exact (congrFun hsym z).symm
    _ = (q : ℂ)⁻¹ • (∑ j : ZMod q, ZMod.stdAddChar (j * z) • ZMod.dft Φ j) := by
      rw [ZMod.invDFT_apply]
    _ = (q : ℂ)⁻¹ • (∑ j : ZMod q, ZMod.stdAddChar (j * z) • ((χ⁻¹ (-j) : ℂ) * τ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      change ZMod.dft (fun a : ZMod q => (χ a : ℂ)) j = (χ⁻¹ (-j) : ℂ) * τ
      simpa [τ] using (DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum (χ := χ) hχ j)
    _ = (q : ℂ)⁻¹ * τ * (∑ j : ZMod q, (χ⁻¹ (-j) : ℂ) * ZMod.stdAddChar (j * z)) := by
      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, τ]
    _ = (q : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar *
        (∑ j : ZMod q, (χ⁻¹ (-j) : ℂ) * ZMod.stdAddChar (j * z)) := by
      simp [τ]

private lemma partialSum_fourier {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (x : ℕ) :
    (∑ n ∈ Finset.range x, (χ (n : ZMod q) : ℂ))
      = (q : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar *
        (∑ k : ZMod q, (χ⁻¹ (-k) : ℂ) *
          (∑ n ∈ Finset.range x, ZMod.stdAddChar (k * (n : ZMod q)))) := by
  let c : ℂ := (q : ℂ)⁻¹
  let τ : ℂ := gaussSum χ ZMod.stdAddChar
  let A : ZMod q → ℕ → ℂ := fun k n => (χ⁻¹ (-k) : ℂ) * ZMod.stdAddChar (k * (n : ZMod q))
  have h1 : (∑ n ∈ Finset.range x, (χ (n : ZMod q) : ℂ))
      = (∑ n ∈ Finset.range x, (c * τ * (∑ k : ZMod q, A k n))) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    calc
      (χ (n : ZMod q) : ℂ) = (q : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar *
          (∑ k : ZMod q, (χ⁻¹ (-k) : ℂ) * ZMod.stdAddChar (k * (n : ZMod q))) :=
        fourier_pointwise hχ (n : ZMod q)
      _ = c * τ * (∑ k : ZMod q, A k n) := by
        simp [c, τ, A, mul_assoc, mul_comm]
  have h2 : (∑ n ∈ Finset.range x, (c * τ * (∑ k : ZMod q, A k n)))
      = c * τ * (∑ n ∈ Finset.range x, ∑ k : ZMod q, A k n) := by
    exact (Finset.mul_sum (a := c * τ) (s := Finset.range x)
      (f := fun n => ∑ k : ZMod q, A k n)).symm
  have h3 : (c * τ * (∑ n ∈ Finset.range x, ∑ k : ZMod q, A k n))
      = c * τ * (∑ k : ZMod q, ∑ n ∈ Finset.range x, A k n) := by
    congr 1
    exact Finset.sum_comm
  have h4 : (∑ k : ZMod q, ∑ n ∈ Finset.range x, A k n)
      = (∑ k : ZMod q, (χ⁻¹ (-k) : ℂ) *
          (∑ n ∈ Finset.range x, ZMod.stdAddChar (k * (n : ZMod q)))) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact (Finset.mul_sum (a := (χ⁻¹ (-k) : ℂ)) (s := Finset.range x)
      (f := fun n => ZMod.stdAddChar (k * (n : ZMod q)))).symm.trans (by rfl)
  calc
    (∑ n ∈ Finset.range x, (χ (n : ZMod q) : ℂ)) = ∑ n ∈ Finset.range x, (c * τ * (∑ k : ZMod q, A k n)) := h1
    _ = c * τ * (∑ n ∈ Finset.range x, ∑ k : ZMod q, A k n) := h2
    _ = c * τ * (∑ k : ZMod q, ∑ n ∈ Finset.range x, A k n) := h3
    _ = c * τ * (∑ k : ZMod q, (χ⁻¹ (-k) : ℂ) *
          (∑ n ∈ Finset.range x, ZMod.stdAddChar (k * (n : ZMod q)))) := by
      rw [h4]
    _ = (q : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar *
        (∑ k : ZMod q, (χ⁻¹ (-k) : ℂ) *
          (∑ n ∈ Finset.range x, ZMod.stdAddChar (k * (n : ZMod q)))) := by
      simp [c, τ]

private lemma stdAddChar_nat_eq_exp {q : ℕ} [NeZero q] (a : ℕ) :
    ZMod.stdAddChar (a : ZMod q) = Complex.exp (Complex.I * (((2 * Real.pi * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ)) := by
  rw [show (a : ZMod q) = ((a : ℤ) : ZMod q) by norm_num]
  rw [ZMod.stdAddChar_coe (a : ℤ)]
  congr 1
  norm_num
  ring_nf

private lemma norm_one_sub_exp (θ : ℝ) : ‖1 - Complex.exp (Complex.I * (θ : ℂ))‖ = 2 * |Real.sin (θ / 2)| := by
  rw [← norm_sub_rev]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs]
  rw [abs_mul]
  congr 1
  norm_num

private lemma pi_mul_div_le_pi_div_two {q a : ℕ} (hqpos : 0 < q) (ha2 : 2 * a ≤ q) :
    Real.pi * (a : ℝ) / (q : ℝ) ≤ Real.pi / 2 := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have htwo : (2 : ℝ) * (a : ℝ) ≤ (q : ℝ) := by exact_mod_cast ha2
  have hdiv : (a : ℝ) ≤ (q : ℝ) / 2 := by nlinarith
  have hmul : Real.pi * (a : ℝ) ≤ Real.pi * ((q : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left hdiv Real.pi_pos.le
  rw [div_le_iff₀ hq]
  nlinarith

private lemma sin_pi_mul_ge_two_mul {q a : ℕ} (ha1 : 1 ≤ a) (ha2 : 2 * a ≤ q) :
    (2 * (a : ℝ)) / (q : ℝ) ≤ Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) := by
  have hqpos : 0 < q := by omega
  have hq : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hx : (0 : ℝ) ≤ Real.pi * (a : ℝ) / (q : ℝ) := by positivity
  have hx' : Real.pi * (a : ℝ) / (q : ℝ) ≤ Real.pi / 2 := pi_mul_div_le_pi_div_two hqpos ha2
  have hj := Real.mul_le_sin hx hx'
  have hmul : (2 / Real.pi) * (Real.pi * (a : ℝ) / (q : ℝ)) = 2 * (a : ℝ) / (q : ℝ) := by
    field_simp [Real.pi_ne_zero, (show (q : ℝ) ≠ 0 by positivity)]
  rwa [hmul] at hj

private lemma norm_char_ge_lo {q : ℕ} [NeZero q] {a : ℕ} (ha1 : 1 ≤ a) (ha2 : 2 * a ≤ q) :
    (4 * (a : ℝ) / (q : ℝ)) ≤ ‖1 - ZMod.stdAddChar (a : ZMod q)‖ := by
  let θ : ℝ := 2 * Real.pi * (a : ℝ) / (q : ℝ)
  have hstd : ZMod.stdAddChar (a : ZMod q) = Complex.exp (Complex.I * (θ : ℂ)) := by
    dsimp [θ]
    exact stdAddChar_nat_eq_exp (q := q) a
  rw [hstd]
  rw [norm_one_sub_exp]
  have hqpos : 0 < q := by omega
  have hsin := sin_pi_mul_ge_two_mul (q := q) (a := a) ha1 ha2
  have hθ : θ / 2 = Real.pi * (a : ℝ) / (q : ℝ) := by dsimp [θ]; ring
  have hx : (0 : ℝ) ≤ θ / 2 := by rw [hθ]; positivity
  have hx_le_pi : θ / 2 ≤ Real.pi := by
    rw [hθ]
    have hx' : Real.pi * (a : ℝ) / (q : ℝ) ≤ Real.pi / 2 := pi_mul_div_le_pi_div_two hqpos ha2
    linarith
  have hnonneg : 0 ≤ Real.sin (θ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi hx hx_le_pi
  calc
    (4 * (a : ℝ)) / (q : ℝ) = 2 * ((2 * (a : ℝ)) / (q : ℝ)) := by ring
    _ ≤ 2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hsin (by norm_num)
    _ = 2 * Real.sin (θ / 2) := by rw [← hθ]
    _ = 2 * |Real.sin (θ / 2)| := by rw [abs_of_nonneg hnonneg]

private lemma norm_char_ge_hi {q : ℕ} [NeZero q] {a : ℕ} (ha1 : 1 ≤ a) (haq : a < q) (hq2a : q ≤ 2 * a) :
    (4 * (((q - a) : ℕ) : ℝ) / (q : ℝ)) ≤ ‖1 - ZMod.stdAddChar (a : ZMod q)‖ := by
  let b : ℕ := q - a
  let θ : ℝ := 2 * Real.pi * (a : ℝ) / (q : ℝ)
  have hb1 : 1 ≤ b := by dsimp [b]; omega
  have hb2 : 2 * b ≤ q := by dsimp [b]; omega
  have hqpos : 0 < q := by omega
  have hq : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hstd : ZMod.stdAddChar (a : ZMod q) = Complex.exp (Complex.I * (θ : ℂ)) := by
    dsimp [θ]
    exact stdAddChar_nat_eq_exp (q := q) a
  rw [hstd]
  rw [norm_one_sub_exp]
  have hθ : θ / 2 = Real.pi * (a : ℝ) / (q : ℝ) := by dsimp [θ]; ring
  have hx : (0 : ℝ) ≤ θ / 2 := by rw [hθ]; positivity
  have hx_le_pi : θ / 2 ≤ Real.pi := by
    rw [hθ]
    have haq' : (a : ℝ) ≤ (q : ℝ) := by exact_mod_cast (le_of_lt haq)
    have hπ : Real.pi * (a : ℝ) ≤ Real.pi * (q : ℝ) :=
      mul_le_mul_of_nonneg_left haq' Real.pi_pos.le
    rw [div_le_iff₀ hq]
    exact hπ
  have hnonneg : 0 ≤ Real.sin (θ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi hx hx_le_pi
  have hsinb := sin_pi_mul_ge_two_mul (q := q) (a := b) hb1 hb2
  have hπb : Real.pi * (b : ℝ) / (q : ℝ) = Real.pi - θ / 2 := by
    rw [hθ]
    dsimp [b, θ]
    have hcast : (((q - a) : ℕ) : ℝ) = (q : ℝ) - (a : ℝ) := by
      exact Nat.cast_sub (le_of_lt haq)
    rw [hcast]
    field_simp [Real.pi_ne_zero, (show (q : ℝ) ≠ 0 by positivity)]
  calc
    (4 * (((q - a) : ℕ) : ℝ)) / (q : ℝ) = 4 * (b : ℝ) / (q : ℝ) := by dsimp [b]
    _ = 2 * (2 * (b : ℝ) / (q : ℝ)) := by ring
    _ ≤ 2 * Real.sin (Real.pi * (b : ℝ) / (q : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hsinb (by norm_num)
    _ = 2 * Real.sin (Real.pi - θ / 2) := by
      congr 1
      rw [hπb]
    _ = 2 * Real.sin (θ / 2) := by rw [Real.sin_pi_sub]
    _ = 2 * |Real.sin (θ / 2)| := by rw [abs_of_nonneg hnonneg]


private lemma cast_nat_pos_of_sub {q a : ℕ} (haq : a < q) : 0 < (((q - a) : ℕ) : ℝ) := by
  exact_mod_cast (Nat.sub_pos_of_lt haq)

private lemma cast_nat_ne_zero_of_sub {q a : ℕ} (haq : a < q) : (((q - a) : ℕ) : ℝ) ≠ 0 := by
  exact ne_of_gt (cast_nat_pos_of_sub haq)

private lemma charTerm_le_lo {q : ℕ} [NeZero q] {a : ℕ} (ha1 : 1 ≤ a) (ha2 : 2 * a ≤ q) :
    2 / ‖1 - ZMod.stdAddChar (a : ZMod q)‖ ≤ (q : ℝ) / (2 * (a : ℝ)) := by
  have hne0 : (a : ZMod q) ≠ 0 := by
    intro h
    have hm : a % q = 0 := by
      have hiff := (ZMod.natCast_eq_natCast_iff' a 0 q).mp (by simpa using h)
      simpa using hiff
    have hmod : a % q = a := by
      exact Nat.mod_eq_of_lt (by omega : a < q)
    omega
  have hw1 : ZMod.stdAddChar (a : ZMod q) ≠ 1 := stdAddChar_ne_one_of_ne_zero q hne0
  have hDpos : 0 < ‖1 - ZMod.stdAddChar (a : ZMod q)‖ := by
    exact (norm_pos_iff.mpr (sub_ne_zero.mpr hw1.symm))
  have hq : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have h2apos : 0 < 2 * (a : ℝ) := by positivity
  have hge := norm_char_ge_lo (q := q) (a := a) ha1 ha2
  have hqD : (q : ℝ) * ‖1 - ZMod.stdAddChar (a : ZMod q)‖ ≥ 4 * (a : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hge hq.le
    field_simp at hm
    nlinarith
  exact (div_le_div_iff₀ hDpos h2apos).mpr (by nlinarith)

private lemma charTerm_le_hi {q : ℕ} [NeZero q] {a : ℕ} (ha1 : 1 ≤ a) (haq : a < q) (hq2a : q ≤ 2 * a) :
    2 / ‖1 - ZMod.stdAddChar (a : ZMod q)‖ ≤ (q : ℝ) / (2 * (((q - a) : ℕ) : ℝ)) := by
  have hne0 : (a : ZMod q) ≠ 0 := by
    intro h
    have hm : a % q = 0 := by
      have hiff := (ZMod.natCast_eq_natCast_iff' a 0 q).mp (by simpa using h)
      simpa using hiff
    have hmod : a % q = a := Nat.mod_eq_of_lt haq
    omega
  have hw1 : ZMod.stdAddChar (a : ZMod q) ≠ 1 := stdAddChar_ne_one_of_ne_zero q hne0
  have hDpos : 0 < ‖1 - ZMod.stdAddChar (a : ZMod q)‖ := by
    exact (norm_pos_iff.mpr (sub_ne_zero.mpr hw1.symm))
  have hq : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hA : 0 < (((q - a) : ℕ) : ℝ) := cast_nat_pos_of_sub haq
  have h2Apos : 0 < 2 * (((q - a) : ℕ) : ℝ) := by nlinarith
  have hge := norm_char_ge_hi (q := q) (a := a) ha1 haq hq2a
  have hqD : (q : ℝ) * ‖1 - ZMod.stdAddChar (a : ZMod q)‖ ≥ 4 * (((q - a) : ℕ) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hge hq.le
    field_simp at hm
    nlinarith
  exact (div_le_div_iff₀ hDpos h2Apos).mpr (by nlinarith)

private lemma charTerm_bound_both {q : ℕ} [NeZero q] {a : ℕ} (ha1 : 1 ≤ a) (haq : a < q) :
    2 / ‖1 - ZMod.stdAddChar (a : ZMod q)‖
      ≤ (q : ℝ) / (2 * (a : ℝ)) + (q : ℝ) / (2 * (((q - a) : ℕ) : ℝ)) := by
  by_cases h : 2 * a ≤ q
  · have hterm := charTerm_le_lo (q := q) (a := a) ha1 h
    have hnonneg : 0 ≤ (q : ℝ) / (2 * (((q - a) : ℕ) : ℝ)) := by
      have hA : 0 < (((q - a) : ℕ) : ℝ) := cast_nat_pos_of_sub haq
      positivity
    linarith
  · have h2a : q ≤ 2 * a := by omega
    have hterm := charTerm_le_hi (q := q) (a := a) ha1 haq h2a
    have hnonneg : 0 ≤ (q : ℝ) / (2 * (a : ℝ)) := by positivity
    linarith

private lemma sum_Icc_inv_eq_harmonic (N : ℕ) :
    (∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ)) = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  norm_num

private lemma harmonic_Icc_le_one_add_log (N : ℕ) :
    (∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
  rw [sum_Icc_inv_eq_harmonic]
  exact harmonic_le_one_add_log N

private lemma sum_comp_sub {q : ℕ} {f : ℕ → ℝ} (hq : 2 ≤ q) :
    (∑ a ∈ Finset.Icc 1 (q - 1), f (q - a)) = (∑ b ∈ Finset.Icc 1 (q - 1), f b) := by
  classical
  refine Finset.sum_bij (s := Finset.Icc 1 (q - 1)) (t := Finset.Icc 1 (q - 1))
    (fun a _ => q - a) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    constructor <;> omega
  · intro a ha b hb h
    rw [Finset.mem_Icc] at ha hb
    omega
  · intro b hb
    rw [Finset.mem_Icc] at hb
    refine ⟨q - b, ?mem, ?eq⟩
    · rw [Finset.mem_Icc]
      constructor <;> omega
    · omega
  · intro a ha
    rfl

private lemma denomSum_le {q : ℕ} (hq2 : 2 ≤ q) :
    (∑ a ∈ Finset.Icc 1 (q - 1),
        ((q : ℝ) / (2 * (a : ℝ)) + (q : ℝ) / (2 * (((q - a) : ℕ) : ℝ))))
      ≤ (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  let H : ℝ := ∑ j ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (j : ℝ)
  let g : ℕ → ℝ := fun j => (q : ℝ) / (2 * (j : ℝ))
  have hg (j : ℕ) : g j = (q : ℝ) / 2 * ((1 : ℝ) / (j : ℝ)) := by
    dsimp [g]
    ring
  have hsplit :
      (∑ a ∈ Finset.Icc 1 (q - 1),
          ((q : ℝ) / (2 * (a : ℝ)) + (q : ℝ) / (2 * (((q - a) : ℕ) : ℝ))))
        = (∑ a ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (2 * (a : ℝ)))
          + (∑ a ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (2 * (((q - a) : ℕ) : ℝ))) := by
    rw [Finset.sum_add_distrib]
  have hleft : (∑ a ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (2 * (a : ℝ)))
      = (q : ℝ) / 2 * H := by
    calc
      (∑ a ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (2 * (a : ℝ)))
          = (∑ a ∈ Finset.Icc 1 (q - 1), (q : ℝ) / 2 * ((1 : ℝ) / (a : ℝ))) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
      _ = (q : ℝ) / 2 * (∑ a ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (a : ℝ)) := by
            rw [Finset.mul_sum]
      _ = (q : ℝ) / 2 * H := by rfl
  have hright : (∑ a ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (2 * (((q - a) : ℕ) : ℝ)))
      = (q : ℝ) / 2 * H := by
    calc
      (∑ a ∈ Finset.Icc 1 (q - 1), g (q - a)) = (∑ b ∈ Finset.Icc 1 (q - 1), g b) := sum_comp_sub (q := q) hq2
      _ = (∑ b ∈ Finset.Icc 1 (q - 1), (q : ℝ) / 2 * ((1 : ℝ) / (b : ℝ))) := by
            apply Finset.sum_congr rfl
            intro b hb
            exact hg b
      _ = (q : ℝ) / 2 * (∑ b ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (b : ℝ)) := by
            rw [Finset.mul_sum]
      _ = (q : ℝ) / 2 * H := by rfl
  have hH : H ≤ 1 + Real.log ((q - 1 : ℕ) : ℝ) := by
    dsimp [H]
    exact harmonic_Icc_le_one_add_log (q - 1)
  have hlog : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    have hq1 : 0 < ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q - 1)
    exact Real.log_le_log hq1 (by exact_mod_cast (by omega : q - 1 ≤ q))
  calc
    (∑ a ∈ Finset.Icc 1 (q - 1),
        ((q : ℝ) / (2 * (a : ℝ)) + (q : ℝ) / (2 * (((q - a) : ℕ) : ℝ))))
        = (∑ a ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (2 * (a : ℝ)))
          + (∑ a ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (2 * (((q - a) : ℕ) : ℝ))) := hsplit
    _ = (q : ℝ) / 2 * H + (q : ℝ) / 2 * H := by rw [hleft, hright]
    _ = (q : ℝ) * H := by ring
    _ ≤ (q : ℝ) * (1 + Real.log ((q - 1 : ℕ) : ℝ)) := by
      have hq : 0 ≤ (q : ℝ) := by exact_mod_cast (by omega : 0 ≤ q)
      exact mul_le_mul_of_nonneg_left hH hq
    _ ≤ (q : ℝ) * (1 + Real.log (q : ℝ)) := by
      have hq : 0 ≤ (q : ℝ) := by exact_mod_cast (by omega : 0 ≤ q)
      exact mul_le_mul_of_nonneg_left (by linarith) hq

/-- Partial character sum `∑_{n < x} χ(n)`. -/
private noncomputable def partialCharSum (q : ℕ) (χ : DirichletCharacter ℂ q) (x : ℕ) : ℂ :=
  ∑ n ∈ Finset.range x, (χ (n : ZMod q) : ℂ)

/-- Character-geometric partial sum at frequency `k`. -/
private noncomputable def geoSum (q : ℕ) [NeZero q] (x : ℕ) (k : ZMod q) : ℂ :=
  ∑ n ∈ Finset.range x, ZMod.stdAddChar (k * (n : ZMod q))

private lemma charTerm_sum_bound {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) :
    (∑ a ∈ Finset.Icc 1 (q - 1), 2 / ‖1 - ZMod.stdAddChar (a : ZMod q)‖)
      ≤ (∑ a ∈ Finset.Icc 1 (q - 1),
          ((q : ℝ) / (2 * (a : ℝ)) + (q : ℝ) / (2 * (((q - a) : ℕ) : ℝ)))) := by
  refine Finset.sum_le_sum ?_
  intro a ha
  rw [Finset.mem_Icc] at ha
  exact charTerm_bound_both (q := q) (a := a) ha.1 (by omega)

/-- `∑_{k ≠ 0} ‖G k‖ ≤ ∑_{a = 1}^{q-1} 2 / ‖1 - e(a)‖` where `e(a) = stdAddChar a`. -/
private lemma geoSum_nonzero_sum_le {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (x : ℕ) :
    (∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), ‖geoSum q x k‖)
      ≤ (∑ a ∈ Finset.Icc 1 (q - 1), 2 / ‖1 - ZMod.stdAddChar (a : ZMod q)‖) := by
  calc
    (∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), ‖geoSum q x k‖)
        = (∑ a ∈ Finset.Icc 1 (q - 1), ‖geoSum q x (a : ZMod q)‖) := by
          refine Finset.sum_bij (s := (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0))
            (t := Finset.Icc 1 (q - 1)) (fun k _ => k.val) ?_ ?_ ?_ ?_
          · intro k hk
            rw [Finset.mem_filter] at hk
            have hval : k.val ≠ 0 := by
              intro h
              apply hk.2
              rw [← (ZMod.natCast_zmod_val k)]
              simp [h]
            have hval_lt : k.val < q := ZMod.val_lt k
            rw [Finset.mem_Icc]
            constructor
            · exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hval)
            · omega
          · intro k hk l hl hkl
            apply ZMod.val_injective
            exact hkl
          · intro b hb
            rw [Finset.mem_Icc] at hb
            have hb_lt_q : b < q := lt_of_le_of_lt hb.2 (Nat.sub_lt (by omega : 0 < q) (by norm_num))
            refine ⟨(b : ZMod q), ?_, ?_⟩
            · rw [Finset.mem_filter]
              constructor
              · simp
              · intro h
                have h' : (b : ZMod q) = ((0 : ℕ) : ZMod q) := by simpa using h
                have hm : b % q = 0 := by
                  have hiff := (ZMod.natCast_eq_natCast_iff' b 0 q).mp h'
                  simpa using hiff
                have hmod : b % q = b := Nat.mod_eq_of_lt hb_lt_q
                omega
            · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt_q]
          · intro k hk
            congr 1
            rw [ZMod.natCast_zmod_val]
    _ ≤ (∑ a ∈ Finset.Icc 1 (q - 1), 2 / ‖1 - ZMod.stdAddChar (a : ZMod q)‖) := by
          refine Finset.sum_le_sum ?_
          intro a ha
          rw [Finset.mem_Icc] at ha
          have ha_lt_q : a < q := lt_of_le_of_lt ha.2 (Nat.sub_lt (by omega : 0 < q) (by norm_num))
          have hk : (a : ZMod q) ≠ 0 := by
            intro h
            have h' : (a : ZMod q) = ((0 : ℕ) : ZMod q) := by simpa using h
            have hm : a % q = 0 := by
              have hiff := (ZMod.natCast_eq_natCast_iff' a 0 q).mp h'
              simpa using hiff
            have hmod : a % q = a := Nat.mod_eq_of_lt ha_lt_q
            omega
          have hb := charGeomSum_le (q := q) (x := x) (k := (a : ZMod q)) hk
          exact hb

private lemma norm_inv_natCast (q : ℕ) : ‖((q : ℂ)⁻¹)‖ = (q : ℝ)⁻¹ := by
  rw [norm_inv, Complex.norm_natCast]

private lemma gaussSum_norm_eq_sqrt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt (q : ℝ) := by
  have hsq : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) :=
    Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive χ hχ
  have hs : Real.sqrt (‖gaussSum χ ZMod.stdAddChar‖ ^ 2) = ‖gaussSum χ ZMod.stdAddChar‖ := by
    rw [Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (norm_nonneg _)
  calc
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt (‖gaussSum χ ZMod.stdAddChar‖ ^ 2) := hs.symm
    _ = Real.sqrt (q : ℝ) := by rw [hsq]

private lemma inv_char_zero_of_two_le {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) {χ : DirichletCharacter ℂ q} :
    (χ⁻¹ (0 : ZMod q) : ℂ) = 0 := by
  have h0 : ¬ IsUnit (0 : ZMod q) := by
    intro h
    have h' : IsUnit (((0 : ℕ) : ZMod q)) := by simpa using h
    have hc : (0 : ℕ).Coprime q := (ZMod.isUnit_iff_coprime (m := 0) (n := q)).mp h'
    have hq1 : q = 1 := (Nat.coprime_zero_left q).mp hc
    omega
  exact MulChar.map_nonunit χ⁻¹ h0


private lemma norm_partialCharSum_le {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (x : ℕ) :
    ‖partialCharSum q χ x‖ ≤ ‖gaussSum χ ZMod.stdAddChar‖ * ‖(q : ℂ)⁻¹‖ *
      (∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), ‖geoSum q x k‖) := by
  let τ : ℂ := gaussSum χ ZMod.stdAddChar
  let T : ℂ := ∑ k : ZMod q, (χ⁻¹ (-k) : ℂ) * geoSum q x k
  let w : ZMod q → ℝ := fun k => ‖(χ⁻¹ (-k) : ℂ)‖ * ‖geoSum q x k‖
  have hfw : partialCharSum q χ x = (q : ℂ)⁻¹ * τ * T := by
    have h := partialSum_fourier hχ x
    dsimp [partialCharSum, τ, T]
    simpa [geoSum] using h
  have hw0 : w (0 : ZMod q) = 0 := by
    dsimp [w]
    have hz : (χ⁻¹ (0 : ZMod q) : ℂ) = 0 := inv_char_zero_of_two_le hq2
    simp [hz]
  have hw_eq : (∑ k : ZMod q, w k) = ∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), w k := by
    calc
      (∑ k : ZMod q, w k) = ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0, w k := by
        rw [← Finset.sum_erase (s := (Finset.univ : Finset (ZMod q))) (a := 0) (f := w) hw0]
      _ = ∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), w k := by
        congr 1
        ext k
        simp
  have hw_le : (∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), w k)
      ≤ (∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), ‖geoSum q x k‖) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    dsimp [w]
    have hn1 : ‖(χ⁻¹ (-k) : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ⁻¹ (-k)
    calc
      ‖(χ⁻¹ (-k) : ℂ)‖ * ‖geoSum q x k‖ ≤ 1 * ‖geoSum q x k‖ := by
        exact mul_le_mul_of_nonneg_right hn1 (norm_nonneg _)
      _ = ‖geoSum q x k‖ := by simp
  have hnormT : ‖T‖ ≤ ∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), ‖geoSum q x k‖ := by
    calc
      ‖T‖ ≤ ∑ k : ZMod q, ‖(χ⁻¹ (-k) : ℂ) * geoSum q x k‖ := by
        dsimp [T]
        exact norm_sum_le (Finset.univ) (fun k => (χ⁻¹ (-k) : ℂ) * geoSum q x k)
      _ ≤ ∑ k : ZMod q, w k := by
        refine Finset.sum_le_sum ?_
        intro k hk
        dsimp [w]
        exact norm_mul_le _ _
      _ ≤ ∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), ‖geoSum q x k‖ := by
        rw [hw_eq]
        exact hw_le
  calc
    ‖partialCharSum q χ x‖ = ‖(q : ℂ)⁻¹ * τ * T‖ := by rw [hfw]
    _ ≤ ‖(q : ℂ)⁻¹ * τ‖ * ‖T‖ := norm_mul_le _ _
    _ ≤ (‖(q : ℂ)⁻¹‖ * ‖τ‖) * ‖T‖ := by
      exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖(q : ℂ)⁻¹‖ * ‖τ‖ * ‖T‖ := by ring
    _ ≤ ‖gaussSum χ ZMod.stdAddChar‖ * ‖(q : ℂ)⁻¹‖ *
        (∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), ‖geoSum q x k‖) := by
      dsimp [τ]
      have hle1 : ‖T‖ ≤ (∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), ‖geoSum q x k‖) := hnormT
      have hnonneg : 0 ≤ ‖(q : ℂ)⁻¹‖ * ‖gaussSum χ ZMod.stdAddChar‖ := by positivity
      nlinarith

private lemma partialCharSum_bound {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (x : ℕ) :
    ‖partialCharSum q χ x‖ ≤ Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < q))
  have hsq : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hsum : (∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), ‖geoSum q x k‖)
      ≤ (q : ℝ) * (1 + Real.log (q : ℝ)) := by
    exact ((geoSum_nonzero_sum_le hq2 x).trans (charTerm_sum_bound hq2)).trans (denomSum_le hq2)
  calc
    ‖partialCharSum q χ x‖ ≤ ‖gaussSum χ ZMod.stdAddChar‖ * ‖(q : ℂ)⁻¹‖ *
        (∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), ‖geoSum q x k‖) :=
      norm_partialCharSum_le hq2 hχ x
    _ = Real.sqrt (q : ℝ) * (q : ℝ)⁻¹ *
        (∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => k ≠ 0), ‖geoSum q x k‖) := by
      rw [gaussSum_norm_eq_sqrt hχ]
      rw [norm_inv_natCast]
    _ ≤ Real.sqrt (q : ℝ) * (q : ℝ)⁻¹ * ((q : ℝ) * (1 + Real.log (q : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hsum (mul_nonneg hsq (inv_nonneg.mpr (le_of_lt (by
        exact_mod_cast (by omega : 0 < q)))))
    _ = Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) := by
      field_simp [hqne]

/-- **Pólya–Vinogradov inequality**: for a primitive nonprincipal Dirichlet character
`χ mod q`, every partial sum of `χ` is bounded by `C · √q · log(q + 2)` for an
absolute constant `C`. -/
theorem polyaVinogradov :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → χ.IsPrimitive → ∀ x : ℕ,
        ‖∑ n ∈ Finset.range x, (χ (n : ZMod q) : ℂ)‖ ≤
          C * Real.sqrt (q : ℝ) * Real.log ((q : ℝ) + 2) := by
  refine ⟨4, by norm_num, ?_⟩
  intro q hq_ne χ hχ1 hprim x
  by_cases hq1 : q = 1
  · subst q
    exfalso
    exact hχ1 (DirichletCharacter.level_one χ)
  · have hq2 : 2 ≤ q := by
      by_cases hq0 : q = 0
      · exact False.elim (NeZero.ne q hq0)
      · omega
    have hlog_le_2log : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) + 2) := by
      have hqpos_nat : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      exact Real.log_le_log (by exact_mod_cast hqpos_nat)
        (by exact_mod_cast (by omega : q ≤ q + 2))
    have hone_le : 1 ≤ Real.log ((q : ℝ) + 2) := by
      have hpos4 : 0 < (4 : ℝ) := by norm_num
      have hle4 : Real.exp 1 ≤ 4 := by
        exact le_trans (le_of_lt Real.exp_one_lt_three) (by norm_num)
      have hlog4 : 1 ≤ Real.log 4 := by
        have hme : Real.log (Real.exp 1) ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) hle4
        rwa [Real.log_exp] at hme
      have h4le : (4 : ℝ) ≤ (q : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ q + 2)
      have hlog_le : Real.log 4 ≤ Real.log ((q : ℝ) + 2) := Real.log_le_log hpos4 h4le
      linarith
    have hb := partialCharSum_bound (q := q) hq2 hprim x
    have hS : ‖∑ n ∈ Finset.range x, (χ (n : ZMod q) : ℂ)‖ = ‖partialCharSum q χ x‖ := by
      rfl
    rw [hS]
    calc
      ‖partialCharSum q χ x‖ ≤ Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) := hb
      _ ≤ Real.sqrt (q : ℝ) * (2 * Real.log ((q : ℝ) + 2)) := by
        have h : 1 + Real.log (q : ℝ) ≤ 2 * Real.log ((q : ℝ) + 2) := by
          nlinarith [hlog_le_2log, hone_le]
        exact mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
      _ ≤ 4 * Real.sqrt (q : ℝ) * Real.log ((q : ℝ) + 2) := by
        have hlognn : 0 ≤ Real.log ((q : ℝ) + 2) := by linarith
        nlinarith [Real.sqrt_nonneg (q : ℝ)]