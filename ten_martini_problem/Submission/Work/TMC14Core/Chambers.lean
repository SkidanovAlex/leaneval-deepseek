import Submission.Work.TMC14Core.Rat
import Submission.Work.TMC14Core.blochDet

/-!
# TMC14Core: Chambers' formula

`tr A_q(θ,z) = Δ(z) + 2(-λ)^q(-1)^{p(q-1)} cos(2πqθ)` for `gcd(p,q) = 1`,
where `Δ` is the discriminant of the rational approximant `p/q`.

The proof goes through the polynomial transfer matrices `SM`: multiplying the `j`-th
transfer matrix by `X = e^{2πiθ}` makes it a *polynomial* matrix of degree `≤ 2`, so the
product `iterPoly q` is a polynomial of degree `≤ 2q` whose value at `X = e^{2πiθ}` is
`X^q · tr A_q(θ,z)`.  The `p/q`-periodicity of `tr A_q` then gives `P(Xω) = ω^q P(X)`,
which pins the Fourier support of `tr A_q` to `{-q,0,q}`; the two extreme coefficients
are `∏(-λω^{±j}) = (-λ)^q(-1)^{p(q-1)}`.  The middle coefficient is `Δ(z)`, evaluated at
`θ = 1/(4q)` where the oscillatory term vanishes.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini
open Polynomial

noncomputable section

namespace Work.TMC14Core

/-- `t(θ) = e^{2πiθ}`. -/
def ee (θ : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))

theorem ee_ne_zero (θ : ℝ) : ee θ ≠ 0 := Complex.exp_ne_zero _

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, ← Complex.exp_add]; congr 1; push_cast; ring

theorem two_cos_eq (θ : ℝ) :
    ((2 : ℝ) : ℂ) * (Real.cos (2 * Real.pi * θ) : ℂ) = ee θ + (ee θ)⁻¹ := by
  have hexp : ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I
      = 2 * Real.pi * Complex.I * (θ : ℂ) := by push_cast; ring
  have hmain : ((2 : ℝ) : ℂ) * Complex.cos ((2 * Real.pi * θ : ℝ) : ℂ)
      = Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)
        + Complex.exp (-(((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)) := by
    push_cast
    simp only [Complex.cos]
    ring
  rw [Complex.ofReal_cos, hmain, hexp, ee, ← Complex.exp_neg]

/-- `X · tmC lam z (θ + j p/q)`, as a polynomial matrix in `X = e^{2πiθ}`. -/
def SM (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℂ[X] :=
  !![C z * X - C (lam : ℂ) * (C ((om p q) ^ j) * X ^ 2 + C (((om p q) ^ j)⁻¹)), -X; X, 0]

/-- `∏_{j<n} SM j`, the polynomial version of the `n`-step transfer matrix, scaled by `X^n`. -/
def iterPoly (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ[X]
  | 0 => 1
  | n + 1 => SM p q lam z n * iterPoly p q lam z n

/-- The polynomial whose value at `X = e^{2πiθ}` is `X^q tr A_q(θ,z)`. -/
def Pcham (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) : ℂ[X] := (iterPoly p q lam z q).trace


/-- The evaluation ring homomorphism at `e^{2πiθ}`. -/
abbrev ev (θ : ℝ) : ℂ[X] →+* ℂ := Polynomial.evalRingHom (ee θ)

theorem ee_nat_mul (x : ℝ) (n : ℕ) : ee ((n : ℝ) * x) = (ee x) ^ n := by
  rw [ee, ee, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem ee_om (p : ℤ) (q : ℕ) (j : ℕ) : ee ((j : ℝ) * ((p : ℝ) / (q : ℝ))) = (om p q) ^ j := by
  rw [ee_nat_mul]
  congr 1
  rw [om, ee]
  congr 1
  push_cast
  ring

/-- `(0,0)`-entry of the transfer matrix, written with exponentials. -/
theorem tmC00 (lam : ℝ) (z : ℂ) (y : ℝ) :
    (tmC lam z y) 0 0 = z - (lam : ℂ) * (ee y + (ee y)⁻¹) := by
  rw [tmC]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero]
  have h : ((2 * lam * Real.cos (2 * Real.pi * y) : ℝ) : ℂ) = (lam : ℂ) * (ee y + (ee y)⁻¹) := by
    rw [show ((2 * lam * Real.cos (2 * Real.pi * y) : ℝ) : ℂ)
        = (lam : ℂ) * (((2 : ℝ) : ℂ) * (Real.cos (2 * Real.pi * y) : ℂ)) from by push_cast; ring,
      two_cos_eq y]
  rw [h]

theorem trace_map_eval (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ[X]) :
    (M.map (ev θ)).trace = (M.trace).eval (ee θ) := by
  simp [Matrix.trace_fin_two, Matrix.map_apply, Polynomial.eval_add]

/-- Multiplying the `j`-th transfer matrix by `X = e^{2πiθ}` makes it polynomial. -/
theorem SM_map (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (θ : ℝ) (j : ℕ) :
    (SM p q lam z j).map (ev θ)
      = (ee θ) • tmC lam z (θ + (j : ℝ) * ((p : ℝ) / (q : ℝ))) := by
  ext i j'
  fin_cases i <;> fin_cases j'
  · -- (0,0)
    show (ev θ) ((SM p q lam z j) 0 0)
        = ee θ * (tmC lam z (θ + (j:ℝ)*((p:ℝ)/(q:ℝ)))) 0 0
    simp only [SM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero]
    rw [show (ev θ) = Polynomial.eval (ee θ) from rfl]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_pow]
    rw [tmC00, ee_add, ee_om p q j]
    have hne : ee θ ≠ 0 := Complex.exp_ne_zero _
    field_simp
  · -- (0,1)
    show (ev θ) ((SM p q lam z j) 0 1)
        = ee θ * (tmC lam z (θ + (j:ℝ)*((p:ℝ)/(q:ℝ)))) 0 1
    simp only [SM, tmC, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    rw [show (ev θ) = Polynomial.eval (ee θ) from rfl]
    simp
  · -- (1,0)
    show (ev θ) ((SM p q lam z j) 1 0)
        = ee θ * (tmC lam z (θ + (j:ℝ)*((p:ℝ)/(q:ℝ)))) 1 0
    simp only [SM, tmC, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    rw [show (ev θ) = Polynomial.eval (ee θ) from rfl]
    simp
  · -- (1,1)
    show (ev θ) ((SM p q lam z j) 1 1)
        = ee θ * (tmC lam z (θ + (j:ℝ)*((p:ℝ)/(q:ℝ)))) 1 1
    simp only [SM, tmC, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    rw [show (ev θ) = Polynomial.eval (ee θ) from rfl]
    simp

theorem iterPoly_map (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) (θ : ℝ) :
    (iterPoly p q lam z n).map (ev θ)
      = (ee θ) ^ n • (iterC ((p : ℝ) / (q : ℝ)) lam z n θ) := by
  induction n with
  | zero => simp [iterPoly, iterC]
  | succ n ih =>
    rw [iterPoly, Matrix.map_mul, SM_map p q lam z θ n, ih, iterC_succ, pow_succ,
      smul_mul_smul_comm, mul_comm (ee θ) ((ee θ) ^ n)]

/-- `Pcham` evaluated at `X = e^{2πiθ}` is `(e^{2πiθ})^q tr A_q(θ,z)`. -/
theorem Pcham_eval (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (θ : ℝ) :
    (Pcham p q lam z).eval (ee θ) = (ee θ) ^ q * trAq p q lam z θ := by
  rw [Pcham, trAq]
  have h := trace_map_eval θ (iterPoly p q lam z q)
  rw [iterPoly_map p q lam z q θ, Matrix.trace_smul, smul_eq_mul] at h
  rw [← h, Matrix.trace_fin_two]


/-! ## 3. Degrees and extreme coefficients of the polynomial transfer matrices -/

theorem SM_00_eq (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) :
    (SM p q lam z n) 0 0
      = C z * X - C (lam * (om p q) ^ n) * X ^ 2 - C (lam * ((om p q) ^ n)⁻¹) := by
  simp only [SM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero]
  rw [mul_add, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul]
  ring

theorem SM_01_eq (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) : (SM p q lam z n) 0 1 = -X := by
  simp [SM]

theorem SM_10_eq (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) : (SM p q lam z n) 1 0 = X := by
  simp [SM]

theorem SM_11_eq (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) : (SM p q lam z n) 1 1 = 0 := by
  simp [SM]

theorem SM_natDegree (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) (i j : Fin 2) :
    ((SM p q lam z n) i j).natDegree ≤ (if i = j then 2 else 1) := by
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Fin.reduceEq, reduceIte]
  · rw [SM_00_eq, Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
    simp only [show N ≠ 1 by omega, show N ≠ 2 by omega, show N ≠ 0 by omega, if_false]
    ring
  · rw [SM_01_eq, Polynomial.natDegree_neg]
    exact Polynomial.natDegree_X_le
  · rw [SM_10_eq]
    exact Polynomial.natDegree_X_le
  · rw [SM_11_eq]
    simp

theorem SM_coeff_two (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) :
    ((SM p q lam z n) 0 0).coeff 2 = -(lam : ℂ) * (om p q) ^ n := by
  rw [SM_00_eq, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
  simp

theorem SM_coeff_zero (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) :
    ((SM p q lam z n) 0 0).coeff 0 = -(lam : ℂ) * ((om p q) ^ n)⁻¹ := by
  rw [SM_00_eq, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
  simp

theorem SM_coeff_one (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) :
    ((SM p q lam z n) 0 1).coeff 1 = -1 := by
  rw [SM_01_eq, Polynomial.coeff_neg, Polynomial.coeff_X, if_pos rfl]

theorem matrix_one_apply_fin2 (i j : Fin 2) :
    (1 : Matrix (Fin 2) (Fin 2) ℂ[X]) i j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp

theorem SM_deg00 (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) :
    ((SM p q lam z n) 0 0).natDegree ≤ 2 := by
  simpa using SM_natDegree p q lam z n 0 0

theorem SM_deg01 (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) :
    ((SM p q lam z n) 0 1).natDegree ≤ 1 := by
  simpa using SM_natDegree p q lam z n 0 1

theorem SM_deg10 (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) :
    ((SM p q lam z n) 1 0).natDegree ≤ 1 := by
  simpa using SM_natDegree p q lam z n 1 0

theorem SM_deg11 (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) :
    ((SM p q lam z n) 1 1).natDegree = 0 := by
  rw [SM_11_eq, Polynomial.natDegree_zero]

/-- The coefficient of `X^{m+k}` in `(C c * X^k) * P`. -/
theorem coeff_C_X_pow_mul (c : ℂ) (k m : ℕ) (P : ℂ[X]) :
    ((C c * X ^ k) * P).coeff (m + k) = c * P.coeff m := by
  rw [mul_assoc, Polynomial.coeff_C_mul]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show X ^ (k + 1) * P = X * (X ^ k * P) from by rw [pow_succ]; ring,
      show m + (k + 1) = m + k + 1 from by ring, Polynomial.coeff_X_mul, ih]

/-- Degree bound for the polynomial transfer matrix product (loose form). -/
theorem iterPoly_natDegree_le (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) (i j : Fin 2) :
    ((iterPoly p q lam z n) i j).natDegree ≤ 2 * n := by
  induction n generalizing i j with
  | zero =>
    rw [iterPoly, matrix_one_apply_fin2]
    by_cases h : i = j
    · simp [h, Polynomial.natDegree_one]
    · simp [h, Polynomial.natDegree_zero]
  | succ n ih =>
    rw [iterPoly, Matrix.mul_apply, Fin.sum_univ_two]
    have h00 := SM_deg00 p q lam z n
    have h01 := SM_deg01 p q lam z n
    have h10 := SM_deg10 p q lam z n
    have h11 := SM_deg11 p q lam z n
    have f0 := ih 0 j
    have f1 := ih 1 j
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_) <;>
      refine le_trans Polynomial.natDegree_mul_le ?_ <;>
      fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] at h00 h01 h10 h11 f0 f1 ⊢ <;>
      omega

theorem Pcham_natDegree (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (hq : 1 ≤ q) :
    (Pcham p q lam z).natDegree ≤ 2 * q := by
  rw [Pcham, Matrix.trace_fin_two]
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · exact iterPoly_natDegree_le p q lam z q 0 0
  · exact iterPoly_natDegree_le p q lam z q 1 1

/-! ## 4. The extreme Fourier coefficients of `tr A_q` -/

theorem om_pow_q (p : ℤ) (q : ℕ) : (om p q) ^ q = 1 := by
  rw [om, ← Complex.exp_nat_mul]
  rw [show ((q : ℂ) * (2 * Real.pi * Complex.I * (p : ℂ) / (q : ℂ)))
      = ((q : ℂ) / (q : ℂ)) * (2 * Real.pi * Complex.I * (p : ℂ)) by ring]
  by_cases hq : (q : ℂ) = 0
  · simp [hq]
  · rw [div_self hq, one_mul, mul_comm (2 * Real.pi * Complex.I) (p : ℂ), Complex.exp_int_mul,
      Complex.exp_two_pi_mul_I]
    exact one_zpow p

theorem om_pow_eq_one_iff (p : ℤ) (q : ℕ) (hpq : Nat.Coprime p.natAbs q) (hq : 0 < q)
    (m : ℕ) : (om p q) ^ m = 1 ↔ q ∣ m := by
  constructor
  · intro h
    rw [om, ← Complex.exp_nat_mul] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have h6 : (2 * Real.pi * Complex.I) * ((m : ℂ) * ((p : ℂ) / (q : ℂ)))
        = (2 * Real.pi * Complex.I) * (n : ℂ) := by
      have h' := hn
      rw [mul_comm (n : ℂ) (2 * Real.pi * Complex.I)] at h'
      rw [← h']
      ring
    have h5 : (m : ℂ) * ((p : ℂ) / (q : ℂ)) = (n : ℂ) :=
      mul_left_cancel₀ Complex.two_pi_I_ne_zero h6
    have h7 : (m : ℂ) * (p : ℂ) = (n : ℂ) * (q : ℂ) := by
      have h' := congrArg (· * (q : ℂ)) h5
      rw [mul_assoc, div_mul_cancel₀ _ hq0] at h'
      exact h'
    have h8 : ((m : ℤ) * p) = (n * (q : ℤ)) := by
      have h' : (((m : ℤ) * p : ℤ) : ℂ) = ((n * (q : ℤ) : ℤ) : ℂ) := by
        push_cast
        rw [h7]
      exact Int.cast_injective h'
    have h9 : (q : ℤ) ∣ (m : ℤ) * (p.natAbs : ℤ) := by
      have hd : (q : ℤ) ∣ (m : ℤ) * p := ⟨n, by rw [mul_comm (q : ℤ) n]; exact h8⟩
      rcases Int.natAbs_eq p with hp | hp
      · rwa [hp] at hd
      · obtain ⟨c, hc⟩ := hd
        rw [hp] at hc
        refine ⟨-c, ?_⟩
        linear_combination -hc
    have h10 : (q : ℕ) ∣ m * p.natAbs := by
      rw [← Int.natCast_dvd_natCast]
      simpa using h9
    exact hpq.symm.dvd_of_dvd_mul_left (by rwa [mul_comm] at h10)
  · intro h
    obtain ⟨k, hk⟩ := h
    rw [hk, pow_mul, om_pow_q, one_pow]

theorem om_pow_half (p : ℤ) (q : ℕ) (hq1 : 1 ≤ q) :
    (om p q) ^ (q * (q - 1) / 2) = (-1 : ℂ) ^ (p * ((q : ℤ) - 1)) := by
  have hqsub : (((q - 1 : ℕ)) : ℂ) = (q : ℂ) - 1 := by
    rw [Nat.cast_sub hq1]; norm_num
  have hdiv : (q * (q - 1) / 2) * 2 = q * (q - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self q).two_dvd
  have hk : (((q * (q - 1) / 2 : ℕ) : ℂ)) * 2 = (q : ℂ) * ((q : ℂ) - 1) := by
    rw [show (((q * (q - 1) / 2 : ℕ) : ℂ)) * 2
        = (((q * (q - 1) / 2) * 2 : ℕ) : ℂ) from by rw [Nat.cast_mul]; norm_num, hdiv,
      Nat.cast_mul, hqsub]
  rw [om, ← Complex.exp_nat_mul,
    show ((q * (q - 1) / 2 : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (p : ℂ) / (q : ℂ))
      = (((p * ((q : ℤ) - 1)) : ℤ) : ℂ) * (Real.pi * Complex.I) from by
    have hq0 : (q : ℂ) ≠ 0 := by
      have : q ≠ 0 := by omega
      exact_mod_cast this
    rw [show (2 * Real.pi * Complex.I * (p : ℂ) / (q : ℂ))
        = (2 * Real.pi * Complex.I * (p : ℂ)) / (q : ℂ) by ring, ← mul_div_assoc, div_eq_iff hq0]
    push_cast [hqsub]
    linear_combination (Real.pi * Complex.I * (p : ℂ)) * hk,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem prod_om (p : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    ∏ j ∈ Finset.range q, (om p q) ^ j = (-1 : ℂ) ^ (p * ((q : ℤ) - 1)) := by
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id, om_pow_half p q hq]

theorem chamCoef_eq (p : ℤ) (q : ℕ) (lam : ℝ) (hq : 1 ≤ q) :
    chamCoef p q lam = 2 * ∏ j ∈ Finset.range q, (-(lam : ℂ) * (om p q) ^ j) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, prod_om p q hq]
  rw [chamCoef]
  ring

theorem chamCoef_eq' (p : ℤ) (q : ℕ) (lam : ℝ) (hq : 1 ≤ q) :
    chamCoef p q lam = 2 * ∏ j ∈ Finset.range q, (-(lam : ℂ) * ((om p q) ^ j)⁻¹) := by
  have h1 : ∏ j ∈ Finset.range q, ((om p q) ^ j)⁻¹ = (-1 : ℂ) ^ (p * ((q : ℤ) - 1)) := by
    rw [Finset.prod_inv_distrib, prod_om p q hq]
    have h2 : ((-1 : ℂ) ^ (p * ((q : ℤ) - 1))) * ((-1 : ℂ) ^ (p * ((q : ℤ) - 1))) = 1 := by
      rw [← zpow_add₀ (show (-1 : ℂ) ≠ 0 by norm_num),
        show p * ((q : ℤ) - 1) + p * ((q : ℤ) - 1) = 2 * (p * ((q : ℤ) - 1)) by ring,
        show (2 : ℤ) * (p * ((q : ℤ) - 1)) = 2 * (p * ((q : ℤ) - 1)) from rfl, zpow_mul,
        show (-1 : ℂ) ^ (2 : ℤ) = 1 by norm_num, one_zpow]
    exact inv_eq_of_mul_eq_one_right h2
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, h1, chamCoef]
  ring


/-! ## 5. Chambers' formula -/

theorem ee_int (n : ℤ) : ee ((n : ℝ)) = 1 := by
  rw [ee, show 2 * Real.pi * Complex.I * ((n : ℝ) : ℂ)
      = (n : ℂ) * (2 * Real.pi * Complex.I) from by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_two_pi_mul_I]
  exact one_zpow n

theorem ee_eq_iff_int (a b : ℝ) : ee a = ee b ↔ ∃ n : ℤ, a = b + n := by
  constructor
  · intro h
    rw [ee, ee] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    refine ⟨n, ?_⟩
    have h2 : (2 * Real.pi * Complex.I) * (a : ℂ) = (2 * Real.pi * Complex.I) * ((b : ℂ) + n) := by
      linear_combination hn
    have h3 := mul_left_cancel₀ Complex.two_pi_I_ne_zero h2
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    rw [ee_add, ee_int, mul_one]

theorem ee_injOn (a b : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 2) (hb : 0 < b) (hb' : b ≤ 1 / 2)
    (h : ee a = ee b) : a = b := by
  obtain ⟨n, hn⟩ := (ee_eq_iff_int a b).mp h
  have hn' : (n : ℝ) = a - b := by linarith
  have h1 : -(1 : ℤ) < n := by
    have : (-1 : ℝ) < (n : ℝ) := by rw [hn']; linarith
    exact_mod_cast this
  have h2 : n < 1 := by
    have : (n : ℝ) < 1 := by rw [hn']; linarith
    exact_mod_cast this
  have hn0 : n = 0 := by omega
  rw [hn0] at hn
  push_cast at hn
  linarith

theorem ee_range_infinite : (Set.range (fun n : ℕ => ee (1 / ((n : ℝ) + 2)))).Infinite := by
  apply Set.infinite_range_of_injective
  intro a b hab
  have ha : 0 < 1 / ((a : ℝ) + 2) := by positivity
  have hb : 0 < 1 / ((b : ℝ) + 2) := by positivity
  have ha' : 1 / ((a : ℝ) + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ (a : ℝ))]
  have hb' : 1 / ((b : ℝ) + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ))]
  have h := ee_injOn _ _ ha ha' hb hb' hab
  have h2 : ((a : ℝ) + 2) = ((b : ℝ) + 2) := by
    simpa [one_div] using congrArg (fun x : ℝ => x⁻¹) h
  exact_mod_cast (by linarith : (a : ℝ) = b)

theorem Pcham_period (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (hq : q ≠ 0) (θ : ℝ) :
    (Pcham p q lam z).eval (ee θ * om p q) = (om p q) ^ q * (Pcham p q lam z).eval (ee θ) := by
  have h1 : ee θ * om p q = ee (θ + (p : ℝ) / (q : ℝ)) := by
    rw [ee_add]
    congr 1
    rw [show om p q = ee ((p : ℝ) / (q : ℝ)) from by
      have := ee_om p q 1
      simpa using this.symm]
  rw [h1, Pcham_eval, Pcham_eval, trAq_period p q lam z θ hq, ← h1, mul_pow]
  ring

theorem Pcham_coeff_mul (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ)
    (hpq : Nat.Coprime p.natAbs q) (hq : 1 ≤ q) (m : ℕ) (hm : m ≤ 2 * q) :
    (Pcham p q lam z).coeff m * ((om p q) ^ m - (om p q) ^ q) = 0 := by
  have hqne : q ≠ 0 := by omega
  have hnd := Pcham_natDegree p q lam z hq
  set R : ℂ[X] := ∑ m ∈ Finset.range (2 * q + 1),
      C ((Pcham p q lam z).coeff m * ((om p q) ^ m - (om p q) ^ q)) * X ^ m with hR
  have hroot : ∀ θ : ℝ, R.IsRoot (ee θ) := by
    intro θ
    rw [Polynomial.IsRoot.def, hR, Polynomial.eval_finsetSum]
    have hsum : (∑ m ∈ Finset.range (2 * q + 1), Polynomial.eval (ee θ)
        (C ((Pcham p q lam z).coeff m * ((om p q) ^ m - (om p q) ^ q)) * X ^ m))
        = (Pcham p q lam z).eval (ee θ * om p q) - (om p q) ^ q * (Pcham p q lam z).eval (ee θ) := by
      have e1 : (Pcham p q lam z).eval (ee θ * om p q)
          = ∑ m ∈ Finset.range (2 * q + 1), (Pcham p q lam z).coeff m * (ee θ * om p q) ^ m :=
        Polynomial.eval_eq_sum_range' (by omega) _
      have e2 : (Pcham p q lam z).eval (ee θ)
          = ∑ m ∈ Finset.range (2 * q + 1), (Pcham p q lam z).coeff m * (ee θ) ^ m :=
        Polynomial.eval_eq_sum_range' (by omega) _
      rw [e1, e2, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        mul_pow]
      ring
    rw [hsum, Pcham_period p q lam z hqne θ, sub_self]
  have hinf : Set.Infinite {t : ℂ | R.IsRoot t} :=
    Set.Infinite.mono (by rintro t ⟨n, rfl⟩; exact hroot _) ee_range_infinite
  have hR0 : R = 0 := Polynomial.eq_zero_of_infinite_isRoot R hinf
  have hcoeff : (R).coeff m = (Pcham p q lam z).coeff m * ((om p q) ^ m - (om p q) ^ q) := by
    rw [hR, Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b hb hne
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (fun h => hne h.symm)]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [← hcoeff, hR0, Polynomial.coeff_zero]

theorem Pcham_coeff_vanishing (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ)
    (hpq : Nat.Coprime p.natAbs q) (hq : 1 ≤ q) (m : ℕ) (hm : m ≤ 2 * q) (hmq : ¬ q ∣ m) :
    (Pcham p q lam z).coeff m = 0 := by
  have h := Pcham_coeff_mul p q lam z hpq hq m hm
  rcases mul_eq_zero.mp h with h1 | h2
  · exact h1
  · exfalso
    have h3 : (om p q) ^ m = 1 := by
      have h4 : (om p q) ^ q = 1 := om_pow_q p q
      rw [h4] at h2
      exact sub_eq_zero.mp h2
    exact hmq ((om_pow_eq_one_iff p q hpq (by omega) m).mp h3)


/-- The top coefficient of the `(0,0)` entry of `iterPoly n`. -/
theorem iterPoly_coeff_top (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) :
    ∀ n, 1 ≤ n → ((iterPoly p q lam z n) 0 0).coeff (2 * n)
      = ∏ j ∈ Finset.range n, (-(lam : ℂ) * (om p q) ^ j) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn
    rcases eq_or_lt_of_le hn with h1 | h1
    · have hn0 : n = 0 := by omega
      subst hn0
      have hbase : iterPoly p q lam z 1 = SM p q lam z 0 := by
        rw [iterPoly, iterPoly]
        ext i j
        simp [matrix_one_apply_fin2]
      rw [hbase, SM_00_eq, Finset.prod_range_one]
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
      norm_num
    · have b00 := iterPoly_natDegree_le p q lam z n 0 0
      have htop := ih (by omega)
      rw [iterPoly, Matrix.mul_apply, Fin.sum_univ_two, Polynomial.coeff_add]
      have h2 : ((SM p q lam z n) 0 1 * (iterPoly p q lam z n) 1 0).coeff (2 * (n + 1)) = 0 := by
        have hb : ((SM p q lam z n) 0 1 * (iterPoly p q lam z n) 1 0).natDegree < 2 * (n + 1) := by
          calc ((SM p q lam z n) 0 1 * (iterPoly p q lam z n) 1 0).natDegree
              ≤ ((SM p q lam z n) 0 1).natDegree + ((iterPoly p q lam z n) 1 0).natDegree :=
                Polynomial.natDegree_mul_le
            _ ≤ 1 + 2 * n := by
                have s := SM_deg01 p q lam z n
                have t := iterPoly_natDegree_le p q lam z n 1 0
                omega
            _ < 2 * (n + 1) := by omega
        exact Polynomial.coeff_eq_zero_of_natDegree_lt hb
      have hsplit : (SM p q lam z n) 0 0
          = C (-(lam : ℂ) * (om p q) ^ n) * X ^ 2 + (C z * X - C ((lam : ℂ) * ((om p q) ^ n)⁻¹)) := by
        rw [SM_00_eq, show (-(lam : ℂ) * (om p q) ^ n) = -(lam * (om p q) ^ n) from by ring,
          Polynomial.C_neg]
        ring
      have h1' : ((SM p q lam z n) 0 0 * (iterPoly p q lam z n) 0 0).coeff (2 * (n + 1))
          = (-(lam : ℂ) * (om p q) ^ n) * ((iterPoly p q lam z n) 0 0).coeff (2 * n) := by
        rw [hsplit, add_mul, Polynomial.coeff_add,
          show 2 * (n + 1) = 2 * n + 2 from by ring, coeff_C_X_pow_mul]
        have hrest : ((C z * X - C ((lam : ℂ) * ((om p q) ^ n)⁻¹)) * (iterPoly p q lam z n) 0 0).coeff (2 * n + 2) = 0 := by
          have h3 : ((C z * X - C ((lam : ℂ) * ((om p q) ^ n)⁻¹) : ℂ[X])).natDegree ≤ 1 := by
            rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
            intro N hN
            rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
            simp only [show N ≠ 1 by omega, show N ≠ 0 by omega, if_false]
            ring
          have hb : ((C z * X - C ((lam : ℂ) * ((om p q) ^ n)⁻¹)) * (iterPoly p q lam z n) 0 0).natDegree < 2 * n + 2 := by
            calc ((C z * X - C ((lam : ℂ) * ((om p q) ^ n)⁻¹)) * (iterPoly p q lam z n) 0 0).natDegree
                ≤ ((C z * X - C ((lam : ℂ) * ((om p q) ^ n)⁻¹) : ℂ[X])).natDegree
                  + ((iterPoly p q lam z n) 0 0).natDegree := Polynomial.natDegree_mul_le
              _ ≤ 1 + 2 * n := by
                  have t := iterPoly_natDegree_le p q lam z n 0 0
                  omega
              _ < 2 * n + 2 := by omega
          exact Polynomial.coeff_eq_zero_of_natDegree_lt hb
        rw [hrest, add_zero]
      rw [h1', h2, add_zero, Finset.prod_range_succ, mul_comm, htop]

/-- The bottom coefficient of the `(0,0)` entry of `iterPoly n`. -/
theorem iterPoly_coeff_bot (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) :
    ∀ n, 1 ≤ n → ((iterPoly p q lam z n) 0 0).coeff 0
      = ∏ j ∈ Finset.range n, (-(lam : ℂ) * ((om p q) ^ j)⁻¹) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn
    rcases eq_or_lt_of_le hn with h1 | h1
    · have hn0 : n = 0 := by omega
      subst hn0
      have hbase : iterPoly p q lam z 1 = SM p q lam z 0 := by
        rw [iterPoly, iterPoly]
        ext i j
        simp [matrix_one_apply_fin2]
      rw [hbase, SM_00_eq, Finset.prod_range_one]
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
      norm_num
    · have hbot := ih (by omega)
      rw [iterPoly, Matrix.mul_apply, Fin.sum_univ_two, Polynomial.coeff_add]
      have h2 : ((SM p q lam z n) 0 1 * (iterPoly p q lam z n) 1 0).coeff 0 = 0 := by
        rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul, SM_01_eq,
          Polynomial.eval_neg, Polynomial.eval_X, neg_zero, zero_mul]
      have h1' : ((SM p q lam z n) 0 0 * (iterPoly p q lam z n) 0 0).coeff 0
          = (-(lam : ℂ) * ((om p q) ^ n)⁻¹) * ((iterPoly p q lam z n) 0 0).coeff 0 := by
        rw [SM_00_eq, show C z * X - C ((lam : ℂ) * (om p q) ^ n) * X ^ 2 - C ((lam : ℂ) * ((om p q) ^ n)⁻¹)
            = C (-(lam : ℂ) * ((om p q) ^ n)⁻¹) + (C z * X - C ((lam : ℂ) * (om p q) ^ n) * X ^ 2) from by
              rw [show (-(lam : ℂ) * ((om p q) ^ n)⁻¹) = -(lam * ((om p q) ^ n)⁻¹) from by ring,
                Polynomial.C_neg]; ring,
          add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul]
        have hrest : ((C z * X - C ((lam : ℂ) * (om p q) ^ n) * X ^ 2) * (iterPoly p q lam z n) 0 0).coeff 0 = 0 := by
          rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul, Polynomial.eval_sub,
            Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_mul,
            Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_zero,
            zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, sub_zero, zero_mul]
        rw [hrest, add_zero]
      rw [h1', h2, add_zero, Finset.prod_range_succ, mul_comm, hbot]


/-- Tight degree bounds for the `(0,1)` and `(1,1)` entries of `iterPoly n` (`n ≥ 1`). -/
theorem iterPoly_natDegree_tight (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) :
    ∀ n, 1 ≤ n →
      ((iterPoly p q lam z n) 0 1).natDegree ≤ 2 * n - 1 ∧
      ((iterPoly p q lam z n) 1 1).natDegree ≤ 2 * n - 2 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn
    rcases eq_or_lt_of_le hn with h1 | h1
    · have hn0 : n = 0 := by omega
      subst hn0
      have hbase : iterPoly p q lam z 1 = SM p q lam z 0 := by
        rw [iterPoly, iterPoly]
        ext i j
        simp [matrix_one_apply_fin2]
      refine ⟨?_, ?_⟩
      · rw [hbase]; simpa using SM_deg01 p q lam z 0
      · rw [hbase]; simpa using SM_deg11 p q lam z 0
    · obtain ⟨t01, t11⟩ := ih (by omega)
      have s00 := SM_deg00 p q lam z n
      have s01 := SM_deg01 p q lam z n
      have s10 := SM_deg10 p q lam z n
      have s11 := SM_deg11 p q lam z n
      have u00 := iterPoly_natDegree_le p q lam z n 0 0
      have u10 := iterPoly_natDegree_le p q lam z n 1 0
      constructor
      · rw [iterPoly, Matrix.mul_apply, Fin.sum_univ_two]
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_) <;>
          refine le_trans Polynomial.natDegree_mul_le ?_ <;> omega
      · rw [iterPoly, Matrix.mul_apply, Fin.sum_univ_two]
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_) <;>
          refine le_trans Polynomial.natDegree_mul_le ?_ <;> omega

theorem iterPoly_coeff11_bot (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) :
    ∀ n, 1 ≤ n → ((iterPoly p q lam z n) 1 1).coeff 0 = 0 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn
    rcases eq_or_lt_of_le hn with h1 | h1
    · have hn0 : n = 0 := by omega
      subst hn0
      have hbase : iterPoly p q lam z 1 = SM p q lam z 0 := by
        rw [iterPoly, iterPoly]
        ext i j
        simp [matrix_one_apply_fin2]
      rw [hbase, SM_11_eq, Polynomial.coeff_zero]
    · have h2 : ((SM p q lam z n) 1 0 * (iterPoly p q lam z n) 0 1).coeff 0 = 0 := by
        rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul, SM_10_eq,
          Polynomial.eval_X, zero_mul]
      have h3 : ((SM p q lam z n) 1 1 * (iterPoly p q lam z n) 1 1).coeff 0 = 0 := by
        rw [SM_11_eq, zero_mul, Polynomial.coeff_zero]
      rw [iterPoly, Matrix.mul_apply, Fin.sum_univ_two, Polynomial.coeff_add, h2, h3, add_zero]

/-- The extreme coefficients of `Pcham`. -/
theorem Pcham_coeff_top (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (hq : 1 ≤ q) :
    (Pcham p q lam z).coeff (2 * q) = ∏ j ∈ Finset.range q, (-(lam : ℂ) * (om p q) ^ j) := by
  obtain ⟨t01, t11⟩ := iterPoly_natDegree_tight p q lam z q hq
  rw [Pcham, Matrix.trace_fin_two, Polynomial.coeff_add, iterPoly_coeff_top p q lam z q hq]
  have : ((iterPoly p q lam z q) 1 1).coeff (2 * q) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [this, add_zero]

theorem Pcham_coeff_bot (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (hq : 1 ≤ q) :
    (Pcham p q lam z).coeff 0 = ∏ j ∈ Finset.range q, (-(lam : ℂ) * ((om p q) ^ j)⁻¹) := by
  rw [Pcham, Matrix.trace_fin_two, Polynomial.coeff_add, iterPoly_coeff_bot p q lam z q hq,
    iterPoly_coeff11_bot p q lam z q hq, add_zero]


/-! ## 6. Chambers' formula for `tr A_q` -/

theorem ee_neg (x : ℝ) : ee (-x) = (ee x)⁻¹ := by
  rw [ee, ee, ← Complex.exp_neg]; congr 1; push_cast; ring

theorem trAq_chambers (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (hpq : Nat.Coprime p.natAbs q)
    (hq : 1 ≤ q) :
    ∀ θ : ℝ, trAq p q lam z θ
      = trAq p q lam z (1 / (4 * (q : ℝ)))
        + chamCoef p q lam * (Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℂ) := by
  have hq0 : q ≠ 0 := by omega
  have htop := Pcham_coeff_top p q lam z hq
  have hbot := Pcham_coeff_bot p q lam z hq
  have hc2 : chamCoef p q lam / 2 = ∏ j ∈ Finset.range q, (-(lam : ℂ) * (om p q) ^ j) := by
    rw [chamCoef_eq p q lam hq]; ring
  have hc0 : chamCoef p q lam / 2 = ∏ j ∈ Finset.range q, (-(lam : ℂ) * ((om p q) ^ j)⁻¹) := by
    rw [chamCoef_eq' p q lam hq]; ring
  have hvan : ∀ m : ℕ, m ≤ 2 * q → m ≠ 0 → m ≠ q → m ≠ 2 * q →
      (Pcham p q lam z).coeff m = 0 := by
    intro m hm2 hm0 hmq hm2q
    refine Pcham_coeff_vanishing p q lam z hpq hq m hm2 (fun hd => ?_)
    obtain ⟨k, hk⟩ := hd
    have hk' : m = q * k := by rw [hk]
    have hk2 : k ≤ 2 := by
      have hqk : q * k ≤ q * 2 := by omega
      exact Nat.le_of_mul_le_mul_left hqk (by omega : 0 < q)
    interval_cases k
    · omega
    · omega
    · omega
  set cq : ℂ := (Pcham p q lam z).coeff q with hcq
  have hpoly : Pcham p q lam z = C (chamCoef p q lam / 2)
      + C (chamCoef p q lam / 2) * X ^ (2 * q) + C cq * X ^ q := by
    ext m
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X_pow]
    by_cases hm0 : m = 0
    · rw [hm0, hbot, ← hc0]
      simp [show ¬ ((0 : ℕ) = 2 * q) by omega, show ¬ ((0 : ℕ) = q) by omega]
    by_cases hmq : m = q
    · rw [hmq]
      simp only [Polynomial.coeff_C, Polynomial.coeff_C_mul_X_pow,
        if_neg (show ¬ ((q : ℕ) = 0) by omega), if_neg (show ¬ ((q : ℕ) = 2 * q) by omega),
        if_pos rfl, add_zero, zero_add]
      exact hcq.symm
    by_cases hm2q : m = 2 * q
    · rw [hm2q, htop, ← hc2]
      simp [show ¬ ((2 * q : ℕ) = q) by omega, show ¬ ((2 * q : ℕ) = 0) by omega]
    · by_cases hm2 : m ≤ 2 * q
      · rw [hvan m hm2 hm0 hmq hm2q]
        simp [hm0, hmq, hm2q]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (by have := Pcham_natDegree p q lam z hq; omega)]
        simp [hm0, hmq, hm2q]
  have hsum : ∀ t : ℂ, (Pcham p q lam z).eval t
      = chamCoef p q lam / 2 + (chamCoef p q lam / 2) * t ^ (2 * q) + cq * t ^ q := by
    intro t
    rw [hpoly]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
  have hmain : ∀ θ : ℝ, trAq p q lam z θ
      = cq + chamCoef p q lam * (Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℂ) := by
    intro θ
    have hpe := Pcham_eval p q lam z θ
    rw [hsum] at hpe
    have hne : (ee θ) ^ q ≠ 0 := pow_ne_zero _ (ee_ne_zero θ)
    have hcancel : trAq p q lam z θ
        = ((ee θ) ^ q)⁻¹ * (chamCoef p q lam / 2 + (chamCoef p q lam / 2) * (ee θ) ^ (2 * q)
            + cq * (ee θ) ^ q) := by
      rw [hpe, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    have hqθ : (ee θ) ^ q = ee ((q : ℝ) * θ) := (ee_nat_mul θ q).symm
    have hexp : (ee θ) ^ (2 * q) = (ee ((q : ℝ) * θ)) ^ 2 := by
      rw [show 2 * q = q * 2 from by ring, pow_mul, hqθ]
    have hcos2 : (2 : ℂ) * ((Real.cos (2 * Real.pi * (q : ℝ) * θ)) : ℂ)
        = (ee ((q : ℝ) * θ))⁻¹ + ee ((q : ℝ) * θ) := by
      have h := two_cos_eq ((q : ℝ) * θ)
      rw [show 2 * Real.pi * ((q : ℝ) * θ) = 2 * Real.pi * (q : ℝ) * θ from by ring] at h
      rw [show (ee ((q : ℝ) * θ))⁻¹ + ee ((q : ℝ) * θ)
        = ee ((q : ℝ) * θ) + (ee ((q : ℝ) * θ))⁻¹ from add_comm _ _, ← h]
      norm_num
    have hne2 : ee ((q : ℝ) * θ) ≠ 0 := ee_ne_zero _
    rw [hcancel, hqθ, hexp,
      show chamCoef p q lam * ((Real.cos (2 * Real.pi * (q : ℝ) * θ)) : ℂ)
        = (chamCoef p q lam / 2) * ((ee ((q : ℝ) * θ))⁻¹ + ee ((q : ℝ) * θ)) from by
          rw [← hcos2]; ring]
    field_simp
    ring
  have hquarter : trAq p q lam z (1 / (4 * (q : ℝ))) = cq := by
    have h := hmain (1 / (4 * (q : ℝ)))
    have hcos : Real.cos (2 * Real.pi * (q : ℝ) * (1 / (4 * (q : ℝ)))) = 0 := by
      rw [show 2 * Real.pi * (q : ℝ) * (1 / (4 * (q : ℝ))) = Real.pi / 2 from by
        field_simp; ring]
      exact Real.cos_pi_div_two
    rw [hcos] at h
    simpa using h
  intro θ
  rw [hmain θ, hquarter]


/-! ## 7. Chambers' formula with the discriminant `disc` -/

theorem disc_eval (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (hq : 1 ≤ q) :
    (disc p q lam).eval z = trAq p q lam z (1 / (4 * (q : ℝ))) := by
  have hq0 : 0 < q := by omega
  rw [disc, Polynomial.eval_add, Polynomial.eval_C, Matrix.eval_charpoly]
  rw [show Matrix.scalar (Fin q) z = z • (1 : Matrix (Fin q) (Fin q) ℂ) from by
    ext i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply]
    by_cases h : i = j <;> simp [h]]
  rw [blochDet p q lam (1 / (4 * (q : ℝ))) 0 z hq0]
  simp

/-- **Chambers' formula.**  For `gcd(p,q) = 1`, the trace of the `q`-step transfer
matrix is `Δ(z) + 2(-λ)^q(-1)^{p(q-1)} cos(2πqθ)`. -/
theorem chambers (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (hpq : Nat.Coprime p.natAbs q)
    (hq : 1 ≤ q) :
    ∀ θ : ℝ, trAq p q lam z θ
      = (disc p q lam).eval z
        + chamCoef p q lam * (Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℂ) := by
  intro θ
  rw [trAq_chambers p q lam z hpq hq θ, disc_eval p q lam z hq]

/-- The determinant form of Chambers' formula. -/
theorem blochMat_chambers (p : ℤ) (q : ℕ) (lam θ k : ℝ) (z : ℂ)
    (hpq : Nat.Coprime p.natAbs q) (hq : 1 ≤ q) :
    (z • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMat p q lam θ k).det
      = (disc p q lam).eval z
        + chamCoef p q lam * (Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℂ)
        - 2 * Real.cos (2 * Real.pi * k) := by
  rw [blochDet p q lam θ k z (by omega), chambers p q lam z hpq hq θ]

end Work.TMC14Core
