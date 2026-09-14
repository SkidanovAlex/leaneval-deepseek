import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Polynomial Finset

noncomputable section

namespace Commons.Analysis.Polynomial

namespace BernsteinAux

def rho (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
def zeta (N : ℕ) (i : ℕ) : ℂ := Complex.exp (Complex.I * Real.pi / N) * rho N ^ i

lemma rho_ne_zero (N : ℕ) : rho N ≠ 0 := Complex.exp_ne_zero _
lemma rho_prim (N : ℕ) (hN : 0 < N) : IsPrimitiveRoot (rho N) N :=
  Complex.isPrimitiveRoot_exp N hN.ne'

lemma zeta_pow (N : ℕ) (hN : 0 < N) (i : ℕ) : zeta N i ^ N = -1 := by
  unfold zeta
  rw [mul_pow]
  have hp : ((rho N) ^ i) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, (rho_prim N hN).pow_eq_one, one_pow]
  rw [hp, mul_one]
  have h2 : (Complex.exp (Complex.I * Real.pi / N)) ^ N = Complex.exp (Real.pi * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  rw [h2, Complex.exp_pi_mul_I]

lemma zeta_injOn (N : ℕ) (hN : 0 < N) : Set.InjOn (zeta N) (Set.Iio N) := by
  intro i hi j hj hij
  simp only [Set.mem_Iio] at hi hj
  unfold zeta at hij
  have hne : Complex.exp (Complex.I * Real.pi / N) ≠ 0 := Complex.exp_ne_zero _
  have hpow : (rho N) ^ i = (rho N) ^ j := mul_left_cancel₀ hne hij
  have hrn : (rho N) ≠ 0 := rho_ne_zero N
  rcases le_total j i with hji | hij'
  · have hdd : (rho N) ^ (i - j) * (rho N) ^ j = (rho N) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hji, hpow]
    have h1 : (rho N) ^ (i - j) = 1 :=
      mul_right_cancel₀ (pow_ne_zero j hrn) (by rw [hdd]; ring)
    have hdvd : N ∣ (i - j) := ((rho_prim N hN).pow_eq_one_iff_dvd _).mp h1
    have hlt : i - j < N := lt_of_le_of_lt (Nat.sub_le _ _) hi
    have : i - j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · have hdd : (rho N) ^ (j - i) * (rho N) ^ i = (rho N) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hij', hpow]
    have h1 : (rho N) ^ (j - i) = 1 :=
      mul_right_cancel₀ (pow_ne_zero i hrn) (by rw [hdd]; ring)
    have hdvd : N ∣ (j - i) := ((rho_prim N hN).pow_eq_one_iff_dvd _).mp h1
    have hlt : j - i < N := lt_of_le_of_lt (Nat.sub_le _ _) hj
    have : j - i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega

def Q (N : ℕ) : ℂ[X] := X^N + 1

lemma Q_natDegree (N : ℕ) (hN : 0 < N) : (Q N).natDegree = N := by
  unfold Q
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow N
  · rw [natDegree_one, natDegree_X_pow]; omega

lemma Q_eval_zeta (N : ℕ) (hN : 0 < N) (i : ℕ) : (Q N).eval (zeta N i) = 0 := by
  unfold Q
  simp only [eval_add, eval_pow, eval_X, eval_one]
  rw [zeta_pow N hN i]; ring

lemma Q_deriv (N : ℕ) (hN : 0 < N) : (Q N).derivative = C (N:ℂ) * X^(N-1) := by
  unfold Q
  rw [derivative_add, derivative_one, add_zero, derivative_X_pow]

lemma Q_deriv_eval_zeta (N : ℕ) (hN : 0 < N) (i : ℕ) :
    (Q N).derivative.eval (zeta N i) = (N:ℂ) * (zeta N i)^(N-1) := by
  rw [Q_deriv N hN]
  simp [eval_mul, eval_C, eval_pow, eval_X]

def S (N : ℕ) (i : ℕ) : ℂ[X] := (Q N) /ₘ (X - C (zeta N i))

lemma Q_eq_mul_S (N : ℕ) (hN : 0 < N) (i : ℕ) : (X - C (zeta N i)) * S N i = Q N := by
  unfold S
  have hm := modByMonic_add_div (Q N) (X - C (zeta N i))
  rw [modByMonic_X_sub_C_eq_C_eval, Q_eval_zeta N hN i, C_0, zero_add] at hm
  exact hm

lemma S_eval_zeta_ne (N : ℕ) (hN : 0 < N) {i j : ℕ} (hij : zeta N i ≠ zeta N j) :
    (S N i).eval (zeta N j) = 0 := by
  have h := congrArg (fun p : ℂ[X] => p.eval (zeta N j)) (Q_eq_mul_S N hN i)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h
  rw [Q_eval_zeta N hN j] at h
  have : zeta N j - zeta N i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd h1 this
  · exact h2

lemma S_eval_zeta_self (N : ℕ) (hN : 0 < N) (i : ℕ) :
    (S N i).eval (zeta N i) = (Q N).derivative.eval (zeta N i) := by
  have h := congrArg derivative (Q_eq_mul_S N hN i)
  rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at h
  have h2 := congrArg (fun p : ℂ[X] => p.eval (zeta N i)) h
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C] at h2
  rw [show zeta N i - zeta N i = 0 by ring, zero_mul, add_zero] at h2
  exact h2

lemma S_natDegree (N : ℕ) (hN : 0 < N) (i : ℕ) : (S N i).natDegree = N - 1 := by
  unfold S
  rw [natDegree_divByMonic _ (monic_X_sub_C _), Q_natDegree N hN, natDegree_X_sub_C]

end BernsteinAux

namespace BernsteinAux

/-- Lagrange basis at the roots of X^N+1. -/
def Lb (N : ℕ) (i : Fin N) : ℂ[X] :=
  C (((Q N).derivative.eval (zeta N (i:ℕ)))⁻¹) * S N (i:ℕ)

lemma Q_deriv_eval_zeta_ne_zero (N : ℕ) (hN : 0 < N) (i : ℕ) :
    (Q N).derivative.eval (zeta N i) ≠ 0 := by
  rw [Q_deriv_eval_zeta N hN i]
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hz : zeta N i ≠ 0 := by
    intro h
    have := zeta_pow N hN i
    rw [h, zero_pow hN.ne'] at this
    exact absurd this.symm (by norm_num)
  exact mul_ne_zero hNc (pow_ne_zero _ hz)

lemma Lb_eval_self (N : ℕ) (hN : 0 < N) (i : Fin N) :
    (Lb N i).eval (zeta N (i:ℕ)) = 1 := by
  unfold Lb
  rw [eval_mul, eval_C, S_eval_zeta_self N hN (i:ℕ),
      inv_mul_cancel₀ (Q_deriv_eval_zeta_ne_zero N hN (i:ℕ))]

lemma Lb_eval_ne (N : ℕ) (hN : 0 < N) {i j : Fin N} (hij : i ≠ j) :
    (Lb N i).eval (zeta N (j:ℕ)) = 0 := by
  unfold Lb
  rw [eval_mul, eval_C, S_eval_zeta_ne N hN, mul_zero]
  intro hcon
  exact hij (Fin.ext (zeta_injOn N hN i.isLt j.isLt hcon))

lemma Lb_natDegree_le (N : ℕ) (hN : 0 < N) (i : Fin N) : (Lb N i).natDegree ≤ N - 1 := by
  unfold Lb
  calc (C _ * S N (i:ℕ)).natDegree ≤ (C (((Q N).derivative.eval (zeta N (i:ℕ)))⁻¹)).natDegree
        + (S N (i:ℕ)).natDegree := natDegree_mul_le
    _ = 0 + (N-1) := by rw [natDegree_C, S_natDegree N hN]
    _ = N - 1 := by ring

/-- the key interpolation identity -/
lemma interpolation (N : ℕ) (hN : 0 < N) (R : ℂ[X]) (hdeg : R.natDegree ≤ N) :
    R = C (R.coeff N) * Q N + ∑ i : Fin N, C (R.eval (zeta N (i:ℕ))) * Lb N i := by
  have key : R - C (R.coeff N) * Q N
      = ∑ i : Fin N, C (R.eval (zeta N (i:ℕ))) * Lb N i := by
    refine eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset (Fin N))
      (fun (i : Fin N) _ (j : Fin N) _ hij => Fin.ext (zeta_injOn N hN i.isLt j.isLt hij)) ?_ ?_ ?_
    · rw [Finset.card_univ, Fintype.card_fin]
      -- degree bound for R - C c * Q
      have hRX : (R - C (R.coeff N) * X^N).degree < (N : WithBot ℕ) := by
        rw [degree_lt_iff_coeff_zero]
        intro m hm
        rw [coeff_sub, coeff_C_mul, coeff_X_pow]
        by_cases h : m = N
        · subst h; rw [if_pos rfl]; ring
        · rw [if_neg h, mul_zero, sub_zero]
          exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))
      have heq : R - C (R.coeff N) * Q N = (R - C (R.coeff N) * X^N) - C (R.coeff N) := by
        rw [Q]; ring
      rw [heq]
      calc ((R - C (R.coeff N) * X^N) - C (R.coeff N)).degree
          ≤ max (R - C (R.coeff N) * X^N).degree (C (R.coeff N)).degree := degree_sub_le _ _
        _ < (N : WithBot ℕ) := max_lt hRX (lt_of_le_of_lt degree_C_le (by exact_mod_cast hN))
    · rw [Finset.card_univ, Fintype.card_fin]
      -- degree bound for the sum
      rw [degree_lt_iff_coeff_zero]
      intro m hm
      rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [coeff_C_mul]
      have : (Lb N i).coeff m = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (Lb_natDegree_le N hN i) (by omega))
      rw [this, mul_zero]
    · -- evaluation
      intro j _
      rw [eval_sub, eval_mul, eval_C, Q_eval_zeta N hN (j:ℕ), mul_zero, sub_zero]
      rw [eval_finsetSum]
      rw [Finset.sum_eq_single j]
      · rw [eval_mul, eval_C, Lb_eval_self N hN j, mul_one]
      · intro i _ hij; rw [eval_mul, eval_C, Lb_eval_ne N hN hij, mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [← key]; abel

end BernsteinAux

namespace BernsteinAux

lemma zeta_ne_one (N : ℕ) (hN : 0 < N) (i : ℕ) : zeta N i ≠ 1 := by
  intro h
  have := zeta_pow N hN i
  rw [h, one_pow] at this
  exact absurd this (by norm_num)

lemma one_sub_zeta_ne_zero (N : ℕ) (hN : 0 < N) (i : ℕ) : 1 - zeta N i ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm (zeta_ne_one N hN i))

lemma S_eval_one (N : ℕ) (hN : 0 < N) (i : ℕ) :
    (S N i).eval 1 = 2 * (1 - zeta N i)⁻¹ := by
  have h := congrArg (fun p : ℂ[X] => p.eval 1) (Q_eq_mul_S N hN i)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h
  unfold Q at h
  simp only [eval_add, eval_pow, eval_X, eval_one, one_pow] at h
  have hz := one_sub_zeta_ne_zero N hN i
  have h' : (1 - zeta N i) * (S N i).eval 1 = 2 := by rw [h]; norm_num
  rw [← h', mul_comm ((1:ℂ) - zeta N i) ((S N i).eval 1), mul_assoc,
    mul_inv_cancel₀ hz, mul_one]

lemma Q_deriv_eval_one (N : ℕ) (hN : 0 < N) : (Q N).derivative.eval 1 = (N:ℂ) := by
  rw [Q_deriv N hN]
  simp [eval_mul, eval_C, eval_pow, eval_X]

lemma S_deriv_eval_one (N : ℕ) (hN : 0 < N) (i : ℕ) :
    (S N i).derivative.eval 1 = ((N:ℂ) - 2 * (1 - zeta N i)⁻¹) * (1 - zeta N i)⁻¹ := by
  have h := congrArg derivative (Q_eq_mul_S N hN i)
  rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at h
  have h2 := congrArg (fun p : ℂ[X] => p.eval 1) h
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C] at h2
  rw [Q_deriv_eval_one N hN, S_eval_one N hN i] at h2
  have hz := one_sub_zeta_ne_zero N hN i
  rw [show ((N:ℂ) - 2 * (1 - zeta N i)⁻¹) * (1 - zeta N i)⁻¹
        = ((N:ℂ) - 2 * (1 - zeta N i)⁻¹) / (1 - zeta N i) by rw [div_eq_mul_inv]]
  rw [eq_div_iff hz, mul_comm]
  rw [← h2]; ring

end BernsteinAux

namespace BernsteinAux

lemma Lb_eval_one (N : ℕ) (hN : 0 < N) (i : Fin N) :
    (Lb N i).eval 1 = ((Q N).derivative.eval (zeta N (i:ℕ)))⁻¹ * (2 * (1 - zeta N (i:ℕ))⁻¹) := by
  unfold Lb
  rw [eval_mul, eval_C, S_eval_one N hN (i:ℕ)]

lemma Lb_deriv_eval_one (N : ℕ) (hN : 0 < N) (i : Fin N) :
    (Lb N i).derivative.eval 1
      = ((Q N).derivative.eval (zeta N (i:ℕ)))⁻¹
        * (((N:ℂ) - 2 * (1 - zeta N (i:ℕ))⁻¹) * (1 - zeta N (i:ℕ))⁻¹) := by
  unfold Lb
  rw [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C,
    S_deriv_eval_one N hN (i:ℕ)]

lemma zeta_ne_zero (N : ℕ) (hN : 0 < N) (i : ℕ) : zeta N i ≠ 0 := by
  intro h
  have := zeta_pow N hN i
  rw [h, zero_pow hN.ne'] at this
  exact absurd this.symm (by norm_num)

lemma theta_mul_zeta (N : ℕ) (hN : 0 < N) (i : ℕ) :
    (Q N).derivative.eval (zeta N i) * zeta N i = -(N:ℂ) := by
  rw [Q_deriv_eval_zeta N hN i, mul_assoc]
  have h : (zeta N i) ^ (N-1) * zeta N i = (zeta N i)^N := by
    rw [← pow_succ]; congr 1; omega
  rw [h, zeta_pow N hN i]; ring

lemma theta_inv (N : ℕ) (hN : 0 < N) (i : ℕ) :
    ((Q N).derivative.eval (zeta N i))⁻¹ = -(N:ℂ)⁻¹ * zeta N i := by
  have hz : zeta N i ≠ 0 := zeta_ne_zero N hN i
  have h := theta_mul_zeta N hN i
  have hTheta : (Q N).derivative.eval (zeta N i) = -(N:ℂ) * (zeta N i)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hz]; exact h
  rw [hTheta, mul_inv, inv_neg, inv_inv]

end BernsteinAux

namespace BernsteinAux

lemma Q_eval_one (N : ℕ) : (Q N).eval 1 = 2 := by
  unfold Q; simp only [eval_add, eval_pow, eval_X, eval_one, one_pow]; norm_num

lemma interpolation_eval_one (N : ℕ) (hN : 0 < N) (R : ℂ[X]) (hdeg : R.natDegree ≤ N) :
    R.eval 1 = 2 * R.coeff N
      + ∑ i : Fin N, R.eval (zeta N (i:ℕ)) * ((Q N).derivative.eval (zeta N (i:ℕ)))⁻¹
          * (2 * (1 - zeta N (i:ℕ))⁻¹) := by
  calc R.eval 1
      = (C (R.coeff N) * Q N + ∑ i : Fin N, C (R.eval (zeta N (i:ℕ))) * Lb N i).eval 1 := by
        conv_lhs => rw [interpolation N hN R hdeg]
    _ = 2 * R.coeff N
      + ∑ i : Fin N, R.eval (zeta N (i:ℕ)) * ((Q N).derivative.eval (zeta N (i:ℕ)))⁻¹
          * (2 * (1 - zeta N (i:ℕ))⁻¹) := by
        rw [eval_add, eval_mul, eval_C, eval_finsetSum, Q_eval_one N]
        congr 1
        · ring
        · apply Finset.sum_congr rfl; intro i _
          rw [eval_mul, eval_C, Lb_eval_one N hN i]; ring

lemma interpolation_deriv_eval_one (N : ℕ) (hN : 0 < N) (R : ℂ[X]) (hdeg : R.natDegree ≤ N) :
    R.derivative.eval 1 = (N:ℂ) * R.coeff N
      + ∑ i : Fin N, R.eval (zeta N (i:ℕ)) * ((Q N).derivative.eval (zeta N (i:ℕ)))⁻¹
          * (((N:ℂ) - 2 * (1 - zeta N (i:ℕ))⁻¹) * (1 - zeta N (i:ℕ))⁻¹) := by
  calc R.derivative.eval 1
      = (C (R.coeff N) * Q N + ∑ i : Fin N, C (R.eval (zeta N (i:ℕ))) * Lb N i).derivative.eval 1 := by
        conv_lhs => rw [interpolation N hN R hdeg]
    _ = (N:ℂ) * R.coeff N
      + ∑ i : Fin N, R.eval (zeta N (i:ℕ)) * ((Q N).derivative.eval (zeta N (i:ℕ)))⁻¹
          * (((N:ℂ) - 2 * (1 - zeta N (i:ℕ))⁻¹) * (1 - zeta N (i:ℕ))⁻¹) := by
        rw [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, derivative_sum,
          eval_add, eval_finsetSum, eval_mul, eval_C, Q_deriv_eval_one N hN]
        congr 1
        · ring
        · apply Finset.sum_congr rfl; intro i _
          rw [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C,
            Lb_deriv_eval_one N hN i]; ring

theorem sum_id (n : ℕ) (hn : 0 < n) (R : ℂ[X]) (hdeg : R.natDegree ≤ 2*n) :
    ∑ i : Fin (2*n), zeta (2*n) (i:ℕ) * R.eval (zeta (2*n) (i:ℕ))
        * ((1 - zeta (2*n) (i:ℕ))⁻¹)^2
      = (n:ℂ) * (R.derivative.eval 1 - (n:ℂ) * R.eval 1) := by
  have hN : 0 < 2*n := by omega
  have h1 := interpolation_eval_one (2*n) hN R hdeg
  have h2 := interpolation_deriv_eval_one (2*n) hN R hdeg
  have hAA : (∑ i : Fin (2*n), R.eval (zeta (2*n) (i:ℕ))
        * ((Q (2*n)).derivative.eval (zeta (2*n) (i:ℕ)))⁻¹ * (2 * (1 - zeta (2*n) (i:ℕ))⁻¹))
      = 2 * (∑ i : Fin (2*n), R.eval (zeta (2*n) (i:ℕ))
        * ((Q (2*n)).derivative.eval (zeta (2*n) (i:ℕ)))⁻¹ * (1 - zeta (2*n) (i:ℕ))⁻¹) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hBB : (∑ i : Fin (2*n), R.eval (zeta (2*n) (i:ℕ))
        * ((Q (2*n)).derivative.eval (zeta (2*n) (i:ℕ)))⁻¹
        * ((((2*n:ℕ):ℂ) - 2 * (1 - zeta (2*n) (i:ℕ))⁻¹) * (1 - zeta (2*n) (i:ℕ))⁻¹))
      = (((2*n:ℕ):ℂ)) * (∑ i : Fin (2*n), R.eval (zeta (2*n) (i:ℕ))
        * ((Q (2*n)).derivative.eval (zeta (2*n) (i:ℕ)))⁻¹ * (1 - zeta (2*n) (i:ℕ))⁻¹)
        - 2 * (∑ i : Fin (2*n), R.eval (zeta (2*n) (i:ℕ))
        * ((Q (2*n)).derivative.eval (zeta (2*n) (i:ℕ)))⁻¹ * ((1 - zeta (2*n) (i:ℕ))⁻¹)^2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  have e1 : R.eval 1 = 2 * R.coeff (2*n) + 2 * (∑ i : Fin (2*n), R.eval (zeta (2*n) (i:ℕ))
        * ((Q (2*n)).derivative.eval (zeta (2*n) (i:ℕ)))⁻¹ * (1 - zeta (2*n) (i:ℕ))⁻¹) := by
    rw [h1, hAA]
  have e2 : R.derivative.eval 1 = (((2*n:ℕ):ℂ)) * R.coeff (2*n)
      + ((((2*n:ℕ):ℂ)) * (∑ i : Fin (2*n), R.eval (zeta (2*n) (i:ℕ))
        * ((Q (2*n)).derivative.eval (zeta (2*n) (i:ℕ)))⁻¹ * (1 - zeta (2*n) (i:ℕ))⁻¹)
        - 2 * (∑ i : Fin (2*n), R.eval (zeta (2*n) (i:ℕ))
        * ((Q (2*n)).derivative.eval (zeta (2*n) (i:ℕ)))⁻¹ * ((1 - zeta (2*n) (i:ℕ))⁻¹)^2)) := by
    rw [h2, hBB]
  have e4 : (∑ i : Fin (2*n), zeta (2*n) (i:ℕ) * R.eval (zeta (2*n) (i:ℕ))
        * ((1 - zeta (2*n) (i:ℕ))⁻¹)^2)
      = -(((2*n:ℕ):ℂ)) * (∑ i : Fin (2*n), R.eval (zeta (2*n) (i:ℕ))
        * ((Q (2*n)).derivative.eval (zeta (2*n) (i:ℕ)))⁻¹ * ((1 - zeta (2*n) (i:ℕ))⁻¹)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    have hΘ : ((Q (2*n)).derivative.eval (zeta (2*n) (i:ℕ)))⁻¹
        = -(((2*n:ℕ):ℂ))⁻¹ * zeta (2*n) (i:ℕ) := theta_inv (2*n) hN (i:ℕ)
    have h2n : (((2*n:ℕ):ℂ)) ≠ 0 := by exact_mod_cast (by omega : 2*n ≠ 0)
    rw [hΘ]; field_simp
  rw [e4, e1, e2]; push_cast; ring

end BernsteinAux

namespace BernsteinAux

lemma zeta_eq_exp (N : ℕ) (hN : 0 < N) (i : ℕ) :
    zeta N i = Complex.exp (Complex.I * (((2 * i + 1 : ℝ) * Real.pi) / (N : ℝ))) := by
  unfold zeta rho
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp
  ring

lemma zeta_norm_one (N : ℕ) (hN : 0 < N) (i : ℕ) : Complex.normSq (zeta N i) = 1 := by
  rw [zeta_eq_exp N hN i, Complex.normSq_apply]
  rw [Complex.exp_re, Complex.exp_im]
  have h1 : (Complex.I * (((2 * i + 1 : ℝ) * Real.pi) / (N : ℝ))).re = 0 := by simp
  have h2 : (Complex.I * (((2 * i + 1 : ℝ) * Real.pi) / (N : ℝ))).im
      = ((2 * i + 1 : ℝ) * Real.pi) / (N : ℝ) := by simp
  rw [h1, h2, Real.exp_zero]
  have := Real.cos_sq_add_sin_sq (((2 * i + 1 : ℝ) * Real.pi) / (N : ℝ))
  nlinarith [this]

/-- the Riesz coefficients -/
def ccoef (n : ℕ) (i : Fin (2*n)) : ℂ :=
  Complex.I * (zeta (2*n) (i:ℕ))^(n+1) * ((1 - zeta (2*n) (i:ℕ))⁻¹)^2 / (n:ℂ)

end BernsteinAux

namespace BernsteinAux

lemma zeta_zpow_ne_zero (N : ℕ) (hN : 0 < N) (i : ℕ) (m : ℤ) :
    (zeta N i : ℂ) ^ m ≠ 0 := zpow_ne_zero m (zeta_ne_zero N hN i)

theorem scalar_riesz (n : ℕ) (hn : 0 < n) (m : ℤ) (hm1 : -(n:ℤ) ≤ m) (hm2 : m ≤ (n:ℤ)) :
    ∑ i : Fin (2*n), ccoef n i * (zeta (2*n) (i:ℕ)) ^ m = Complex.I * (m:ℂ) := by
  have hN : 0 < 2*n := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k:ℤ) = (n:ℤ) + m := ⟨_, Int.toNat_of_nonneg (by omega)⟩
  have hk_le : k ≤ 2*n := by omega
  have hsum := sum_id n hn (X^k) (by rw [natDegree_X_pow]; exact hk_le)
  simp only [eval_pow, eval_X, derivative_pow, derivative_X, eval_mul, eval_C, eval_one,
    one_pow, mul_one] at hsum
  -- hsum : ∑ i, z_i * z_i^k * W_i^2 = n * (k - n)
  have hkc : (k:ℂ) - (n:ℂ) = (m:ℂ) := by
    have : (k:ℤ) - (n:ℤ) = m := by omega
    exact_mod_cast this
  rw [hkc] at hsum
  have hgoal : (∑ i : Fin (2*n), ccoef n i * (zeta (2*n) (i:ℕ)) ^ m)
      = (Complex.I / (n:ℂ)) * (∑ i : Fin (2*n), zeta (2*n) (i:ℕ) * (zeta (2*n) (i:ℕ))^k
          * ((1 - zeta (2*n) (i:ℕ))⁻¹)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    unfold ccoef
    have hz : (zeta (2*n) (i:ℕ) : ℂ) ≠ 0 := zeta_ne_zero (2*n) hN (i:ℕ)
    have h1 : ((zeta (2*n) (i:ℕ))^(n+1) : ℂ) = (zeta (2*n) (i:ℕ))^((n+1:ℕ):ℤ) := by rw [zpow_natCast]
    have h2 : ((zeta (2*n) (i:ℕ))^k : ℂ) = (zeta (2*n) (i:ℕ))^((k:ℕ):ℤ) := by rw [zpow_natCast]
    have h3 : (zeta (2*n) (i:ℕ) : ℂ)^((n+1:ℕ):ℤ) * (zeta (2*n) (i:ℕ))^m
        = (zeta (2*n) (i:ℕ))^((k:ℕ):ℤ) * (zeta (2*n) (i:ℕ)) := by
      rw [← zpow_add₀ hz]
      rw [show ((n+1:ℕ):ℤ) + m = ((k:ℕ):ℤ) + 1 by omega, zpow_add₀ hz, zpow_one]
    rw [h1, h2]
    rw [show (Complex.I * (zeta (2*n) (i:ℕ))^((n+1:ℕ):ℤ) * ((1 - zeta (2*n) (i:ℕ))⁻¹)^2
          / (n:ℂ) * (zeta (2*n) (i:ℕ))^m)
        = (Complex.I / (n:ℂ)) * ((zeta (2*n) (i:ℕ))^((n+1:ℕ):ℤ) * (zeta (2*n) (i:ℕ))^m
          * ((1 - zeta (2*n) (i:ℕ))⁻¹)^2) by ring]
    rw [h3]; ring

  rw [hgoal, hsum]
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end BernsteinAux

namespace BernsteinAux

lemma normSq_pow (z : ℂ) (k : ℕ) : Complex.normSq (z^k) = (Complex.normSq z)^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Complex.normSq_mul, ih, pow_succ]

lemma zeta_norm (N : ℕ) (hN : 0 < N) (i : ℕ) : ‖zeta N i‖ = 1 := by
  have h : ‖zeta N i‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, zeta_norm_one N hN i]
  nlinarith [norm_nonneg (zeta N i)]

lemma star_zeta (N : ℕ) (hN : 0 < N) (i : ℕ) :
    (starRingEnd ℂ) (zeta N i) = (zeta N i)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [mul_comm, Complex.mul_conj, zeta_norm_one N hN i]
  norm_num

lemma star_inv_one_sub (N : ℕ) (hN : 0 < N) (i : ℕ) :
    (starRingEnd ℂ) ((1 - zeta N i)⁻¹) = -(zeta N i) * (1 - zeta N i)⁻¹ := by
  rw [Complex.conj_inv, map_sub, map_one, star_zeta N hN i]
  have hz : zeta N i ≠ 0 := zeta_ne_zero N hN i
  have h1 : (1 : ℂ) - zeta N i ≠ 0 := one_sub_zeta_ne_zero N hN i
  have h2 : (1 : ℂ) - (zeta N i)⁻¹ ≠ 0 := by
    intro h
    exact zeta_ne_one N hN i (inv_eq_one.mp (eq_of_sub_eq_zero h).symm)
  field_simp
  rw [show (1:ℂ) - zeta N i = -(zeta N i - 1) by ring, neg_div,
    div_self (sub_ne_zero.mpr (zeta_ne_one N hN i))]

lemma normSq_inv_one_sub (N : ℕ) (hN : 0 < N) (i : ℕ) :
    Complex.normSq ((1 - zeta N i)⁻¹) = -(zeta N i * ((1 - zeta N i)⁻¹)^2).re := by
  have h := Complex.mul_conj ((1 - zeta N i)⁻¹)
  rw [star_inv_one_sub N hN i] at h
  have h2 : ((1 - zeta N i)⁻¹) * (-(zeta N i) * (1 - zeta N i)⁻¹)
      = -(zeta N i * ((1 - zeta N i)⁻¹)^2) := by ring
  rw [h2] at h
  have := congrArg Complex.re h
  rw [Complex.ofReal_re] at this
  exact this.symm

lemma norm_ccoeff (n : ℕ) (hn : 0 < n) (i : Fin (2*n)) :
    ‖ccoef n i‖ = Complex.normSq ((1 - zeta (2*n) (i:ℕ))⁻¹) / (n:ℝ) := by
  have hN : 0 < 2*n := by omega
  unfold ccoef
  rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, norm_pow,
      zeta_norm (2*n) hN (i:ℕ), one_pow, one_mul, norm_pow, Complex.norm_natCast,
      ← Complex.normSq_eq_norm_sq]

lemma sum_abs_ccoeff (n : ℕ) (hn : 0 < n) :
    ∑ i : Fin (2*n), ‖ccoef n i‖ = (n:ℝ) := by
  have hN : 0 < 2*n := by omega
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum := sum_id n hn (1 : ℂ[X]) (by simp)
  simp only [eval_one, mul_one, derivative_one, eval_zero, mul_zero, sub_zero] at hsum
  have hsum' : (∑ x : Fin (2*n), zeta (2*n) (x:ℕ) * ((1 - zeta (2*n) (x:ℕ))⁻¹)^2)
      = -((n:ℂ)^2) := by rw [hsum]; ring
  rw [show (∑ i : Fin (2*n), ‖ccoef n i‖)
      = (∑ i : Fin (2*n), (-(zeta (2*n) (i:ℕ) * ((1 - zeta (2*n) (i:ℕ))⁻¹)^2)).re)
        / (n:ℝ) from ?_]
  · rw [← Complex.re_sum, Finset.sum_neg_distrib, hsum', neg_neg]
    have hpq : ((n:ℂ)^2).re = (n:ℝ)^2 := by rw [sq, Complex.mul_re]; simp; ring
    rw [hpq]
    field_simp
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [norm_ccoeff n hn i, normSq_inv_one_sub (2*n) hN (i:ℕ), Complex.neg_re]

end BernsteinAux

namespace BernsteinAux

def θi (n : ℕ) (i : ℕ) : ℝ := (2*(i:ℝ) + 1) * Real.pi / (2*(n:ℝ))

lemma zeta_eq_exp_theta (n : ℕ) (hn : 0 < n) (i : ℕ) :
    zeta (2*n) i = Complex.exp (Complex.I * θi n i) := by
  rw [zeta_eq_exp (2*n) (by omega) i]
  congr 1
  unfold θi
  push_cast
  field_simp

lemma exp_theta_zpow (n : ℕ) (hn : 0 < n) (i : ℕ) (m : ℤ) :
    Complex.exp (Complex.I * m * θi n i) = (zeta (2*n) i) ^ m := by
  rw [zeta_eq_exp_theta n hn i]
  rw [show Complex.I * (m:ℂ) * θi n i = (m:ℂ) * (Complex.I * θi n i) by ring]
  rw [← Complex.exp_int_mul]

lemma exp_theta_zpow_k (n : ℕ) (hn : 0 < n) (i k : ℕ) :
    Complex.exp ((Complex.I * (((k:ℤ):ℂ) - ((n:ℤ):ℂ))) * θi n i)
      = (zeta (2*n) i) ^ ((k:ℤ) - (n:ℤ)) := by
  have h : (Complex.I * (((k:ℤ):ℂ) - ((n:ℤ):ℂ))) = (Complex.I * ((((k:ℤ)-(n:ℤ)):ℤ):ℂ)) := by
    congr 1; exact (Int.cast_sub (k:ℤ) (n:ℤ)).symm
  rw [h, zeta_eq_exp_theta n hn i]
  rw [show (Complex.I * ((((k:ℤ)-(n:ℤ)):ℤ):ℂ)) * θi n i
        = ((((k:ℤ)-(n:ℤ))):ℤ) * (Complex.I * θi n i) by ring]
  rw [Complex.exp_int_mul]

lemma riesz_formula (n : ℕ) (hn : 0 < n) (θ₀ : ℝ) (a : Fin (2*n+1) → ℂ) :
    ∑ i : Fin (2*n), ccoef n i
        * (∑ k : Fin (2*n+1), a k
            * Complex.exp (Complex.I * (((k:ℕ):ℤ) - (n:ℤ)) * (θ₀ + θi n (i:ℕ))))
      = ∑ k : Fin (2*n+1), a k * (Complex.I * (((k:ℕ):ℤ) - (n:ℤ)))
          * Complex.exp (Complex.I * (((k:ℕ):ℤ) - (n:ℤ)) * θ₀) := by
  have hswap : (∑ i : Fin (2*n), ccoef n i
        * (∑ k : Fin (2*n+1), a k
            * Complex.exp (Complex.I * (((k:ℕ):ℤ) - (n:ℤ)) * (θ₀ + θi n (i:ℕ)))))
      = ∑ k : Fin (2*n+1), ∑ i : Fin (2*n), ccoef n i * (a k
            * Complex.exp (Complex.I * (((k:ℕ):ℤ) - (n:ℤ)) * (θ₀ + θi n (i:ℕ)))) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro k _
  have hm1 : -(n:ℤ) ≤ ((k:ℕ):ℤ) - (n:ℤ) := by have := k.isLt; omega
  have hm2 : ((k:ℕ):ℤ) - (n:ℤ) ≤ (n:ℤ) := by have := k.isLt; omega
  have key : (∑ i : Fin (2*n), ccoef n i * (a k
        * Complex.exp (Complex.I * (((k:ℕ):ℤ) - (n:ℤ)) * (θ₀ + θi n (i:ℕ)))))
      = a k * Complex.exp (Complex.I * (((k:ℕ):ℤ) - (n:ℤ)) * θ₀)
        * (∑ i : Fin (2*n), ccoef n i * (zeta (2*n) (i:ℕ)) ^ (((k:ℕ):ℤ) - (n:ℤ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [show Complex.exp (Complex.I * (((k:ℕ):ℤ) - (n:ℤ)) * (θ₀ + θi n (i:ℕ)))
        = Complex.exp (Complex.I * (((k:ℕ):ℤ) - (n:ℤ)) * θ₀)
          * Complex.exp (Complex.I * (((k:ℕ):ℤ) - (n:ℤ)) * θi n (i:ℕ)) by
      rw [← Complex.exp_add]; congr 1; ring]
    rw [exp_theta_zpow_k n hn (i:ℕ) (k:ℕ)]
    ring
  rw [key, scalar_riesz n hn (((k:ℕ):ℤ) - (n:ℤ)) hm1 hm2]
  rw [Int.cast_sub]; ring

end BernsteinAux

namespace BernsteinAux

noncomputable def cP (n : ℕ) (p : ℝ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (n+1), C ((p.coeff k : ℂ) / (2:ℂ)^k) * X^(n-k) * (X^2+1)^k

lemma cP_eval (n : ℕ) (p : ℝ[X]) (hdeg : p.natDegree ≤ n) (θ : ℝ) :
    (cP n p).eval (Complex.exp (Complex.I * θ))
      = Complex.exp (Complex.I * (n:ℂ) * θ) * ((p.eval (Real.cos θ) : ℝ) : ℂ) := by
  have hze : Complex.exp (Complex.I * θ) ≠ 0 := Complex.exp_ne_zero _
  have hexp1 : Complex.exp (Complex.I * θ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [show Complex.I * θ = (θ:ℂ) * Complex.I by ring, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  have hexp2 : Complex.exp (-(Complex.I * θ)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [show -(Complex.I * θ) = ((-θ:ℝ):ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    rw [show Complex.cos ((-θ:ℝ):ℂ) = (Real.cos θ : ℂ) by
          rw [show ((-θ:ℝ):ℂ) = -(θ:ℂ) by push_cast; ring, Complex.cos_neg, ← Complex.ofReal_cos],
        show Complex.sin ((-θ:ℝ):ℂ) = -(Real.sin θ : ℂ) by
          rw [show ((-θ:ℝ):ℂ) = -(θ:ℂ) by push_cast; ring, Complex.sin_neg, ← Complex.ofReal_sin]]
    ring
  have hsum2 : Complex.exp (Complex.I * θ) + Complex.exp (-(Complex.I * θ))
      = (2:ℂ) * (Real.cos θ : ℂ) := by rw [hexp1, hexp2]; ring
  have hz : Complex.exp (Complex.I * θ) ^ 2 + 1
      = Complex.exp (Complex.I * θ) * ((2:ℂ) * (Real.cos θ : ℂ)) := by
    have hinv : (Complex.exp (Complex.I * θ))⁻¹ = Complex.exp (-(Complex.I * θ)) :=
      (Complex.exp_neg _).symm
    calc Complex.exp (Complex.I * θ) ^ 2 + 1
        = Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * θ) + 1 := by rw [sq]
      _ = Complex.exp (Complex.I * θ) * (Complex.exp (Complex.I * θ)
            + (Complex.exp (Complex.I * θ))⁻¹) := by
          rw [mul_add, mul_inv_cancel₀ hze]
      _ = Complex.exp (Complex.I * θ) * ((2:ℂ) * (Real.cos θ : ℂ)) := by rw [hinv, hsum2]
  have hzn : Complex.exp (Complex.I * θ) ^ n = Complex.exp (Complex.I * (n:ℂ) * θ) := by
    rw [← Complex.exp_nat_mul]
    congr 1; ring
  have hpc : p.eval (Real.cos θ) = ∑ k ∈ Finset.range (n+1), p.coeff k * (Real.cos θ)^k := by
    rw [eval_eq_sum_range' (by omega : p.natDegree < n+1)]
  unfold cP
  rw [eval_finsetSum, hpc, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hk' : k ≤ n := by omega
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one]
  rw [hz, mul_pow]
  rw [show (↑(p.coeff k) / 2 ^ k) * Complex.exp (Complex.I * ↑θ) ^ (n - k)
        * (Complex.exp (Complex.I * ↑θ) ^ k * (2 * ↑(Real.cos θ)) ^ k)
      = (↑(p.coeff k) / 2 ^ k) * (Complex.exp (Complex.I * ↑θ) ^ (n - k)
        * Complex.exp (Complex.I * ↑θ) ^ k) * (2 * ↑(Real.cos θ)) ^ k by ring]
  rw [← pow_add, Nat.sub_add_cancel hk', ← hzn]
  have h2k : ((2:ℂ)^k) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Complex.ofReal_mul, Complex.ofReal_pow, mul_pow]
  field_simp

end BernsteinAux

namespace BernsteinAux

lemma cP_natDegree_le (n : ℕ) (p : ℝ[X]) : (cP n p).natDegree ≤ 2*n := by
  unfold cP
  refine (natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨by omega, fun k hk => ?_⟩
  rw [Finset.mem_range] at hk
  have hk' : k ≤ n := by omega
  have hX2 : ((X^2+1 : ℂ[X])).natDegree ≤ 2 := by
    rw [show (X^2+1 : ℂ[X]) = X^2 + C (1:ℂ) by simp]
    rw [natDegree_eq_of_degree_eq_some (degree_X_pow_add_C (show 0 < 2 by norm_num) (1:ℂ))]
  have hCd : (C ((p.coeff k : ℂ) / (2:ℂ)^k) : ℂ[X]).natDegree ≤ 0 := by rw [natDegree_C]
  calc (C ((p.coeff k : ℂ) / (2:ℂ)^k) * X^(n-k) * (X^2+1)^k : ℂ[X]).natDegree
      ≤ (C ((p.coeff k : ℂ) / (2:ℂ)^k) * X^(n-k) : ℂ[X]).natDegree
        + ((X^2+1)^k : ℂ[X]).natDegree := natDegree_mul_le
    _ ≤ ((C ((p.coeff k : ℂ) / (2:ℂ)^k) : ℂ[X]).natDegree + (X^(n-k) : ℂ[X]).natDegree)
        + k * (X^2+1 : ℂ[X]).natDegree := by
        apply add_le_add
        · exact natDegree_mul_le
        · exact natDegree_pow_le
    _ ≤ (0 + (n-k)) + k*2 := by
        apply add_le_add
        · apply add_le_add
          · exact hCd
          · rw [natDegree_X_pow]
        · calc k * (X^2+1 : ℂ[X]).natDegree ≤ k * 2 := Nat.mul_le_mul_left k hX2
            _ = k*2 := rfl
    _ ≤ 2*n := by omega

end BernsteinAux

namespace BernsteinAux

lemma hS_eq (n : ℕ) (hn : 0 < n) (p : ℝ[X]) (hdeg : p.natDegree ≤ n) (θ : ℝ) :
    (∑ k : Fin (2*n+1), (cP n p).coeff (k:ℕ)
        * Complex.exp (Complex.I * ((((k:ℤ):ℂ) - ((n:ℤ):ℂ)) * θ)))
      = ((p.eval (Real.cos θ) : ℝ) : ℂ) := by
  have hE : Complex.exp (Complex.I * (n:ℂ) * θ) ≠ 0 := Complex.exp_ne_zero _
  have hker : ∀ k : Fin (2*n+1),
      Complex.exp (Complex.I * ((((k:ℤ):ℂ) - ((n:ℤ):ℂ)) * θ))
      = (Complex.exp (Complex.I * θ))^(k:ℕ) * (Complex.exp (Complex.I * (n:ℂ) * θ))⁻¹ := by
    intro k
    rw [show Complex.I * ((((k:ℤ):ℂ) - ((n:ℤ):ℂ)) * θ)
        = (k:ℂ) * (Complex.I * θ) + -(Complex.I * (n:ℂ) * θ) by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_neg, Complex.exp_nat_mul]
  calc (∑ k : Fin (2*n+1), (cP n p).coeff (k:ℕ)
          * Complex.exp (Complex.I * ((((k:ℤ):ℂ) - ((n:ℤ):ℂ)) * θ)))
      = (Complex.exp (Complex.I * (n:ℂ) * θ))⁻¹
        * (∑ k : Fin (2*n+1), (cP n p).coeff (k:ℕ) * (Complex.exp (Complex.I * θ))^(k:ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        rw [hker k]; ring
    _ = (Complex.exp (Complex.I * (n:ℂ) * θ))⁻¹ * (cP n p).eval (Complex.exp (Complex.I * θ)) := by
        congr 1
        rw [eval_eq_sum_range' (by have := cP_natDegree_le n p; omega : (cP n p).natDegree < 2*n+1)]
        exact Fin.sum_univ_eq_sum_range
          (fun i => (cP n p).coeff i * (Complex.exp (Complex.I * θ))^i) (2*n+1)
    _ = (Complex.exp (Complex.I * (n:ℂ) * θ))⁻¹
        * (Complex.exp (Complex.I * (n:ℂ) * θ) * ((p.eval (Real.cos θ) : ℝ) : ℂ)) := by
        rw [cP_eval n p hdeg θ]
    _ = ((p.eval (Real.cos θ) : ℝ) : ℂ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hE, one_mul]

end BernsteinAux

namespace BernsteinAux

def mc (n k : ℕ) : ℂ := ((k:ℤ):ℂ) - ((n:ℤ):ℂ)

lemma hS'_deriv (n : ℕ) (hn : 0 < n) (p : ℝ[X]) (hdeg : p.natDegree ≤ n) (θ₀ : ℝ) :
    (∑ k : Fin (2*n+1), (cP n p).coeff (k:ℕ) * (Complex.I * mc n (k:ℕ))
        * Complex.exp (Complex.I * (mc n (k:ℕ) * θ₀)))
      = -(((p.derivative.eval (Real.cos θ₀) * Real.sin θ₀ : ℝ)) : ℂ) := by
  have hterm : ∀ k : Fin (2*n+1),
      HasDerivAt (fun θ : ℝ => (cP n p).coeff (k:ℕ) * Complex.exp (Complex.I * (mc n (k:ℕ) * θ)))
        ((cP n p).coeff (k:ℕ) * (Complex.I * mc n (k:ℕ))
          * Complex.exp (Complex.I * (mc n (k:ℕ) * θ₀))) θ₀ := by
    intro k
    have hc : HasDerivAt (fun θ : ℝ => Complex.I * (mc n (k:ℕ) * θ))
        (Complex.I * mc n (k:ℕ)) θ₀ := by
      have h := ((hasDerivAt_id θ₀).ofReal_comp).const_mul (Complex.I * mc n (k:ℕ))
      simpa [mul_assoc, mul_comm, mul_left_comm] using h
    have h2 := hc.cexp.const_mul ((cP n p).coeff (k:ℕ))
    simpa [mul_assoc, mul_comm, mul_left_comm] using h2
  have hderiv : HasDerivAt (∑ k ∈ (Finset.univ : Finset (Fin (2*n+1))), fun θ : ℝ => (cP n p).coeff (k:ℕ)
        * Complex.exp (Complex.I * (mc n (k:ℕ) * θ)))
      (∑ k : Fin (2*n+1), (cP n p).coeff (k:ℕ) * (Complex.I * mc n (k:ℕ))
        * Complex.exp (Complex.I * (mc n (k:ℕ) * θ₀))) θ₀ :=
    HasDerivAt.sum (fun k _ => hterm k)
  have heq : (∑ k ∈ (Finset.univ : Finset (Fin (2*n+1))), fun θ : ℝ => (cP n p).coeff (k:ℕ)
        * Complex.exp (Complex.I * (mc n (k:ℕ) * θ)))
      =ᶠ[nhds θ₀] (fun θ : ℝ => ((p.eval (Real.cos θ) : ℝ) : ℂ)) :=
    Filter.Eventually.of_forall (fun θ => by
      rw [Finset.sum_apply]; exact hS_eq n hn p hdeg θ)
  have hg : HasDerivAt (fun θ : ℝ => p.eval (Real.cos θ))
      (p.derivative.eval (Real.cos θ₀) * (-Real.sin θ₀)) θ₀ :=
    (Polynomial.hasDerivAt p (Real.cos θ₀)).comp θ₀ (Real.hasDerivAt_cos θ₀)
  rw [← hderiv.deriv, heq.deriv_eq, (hg.ofReal_comp).deriv]
  push_cast; ring

lemma riesz_poly (n : ℕ) (hn : 0 < n) (p : ℝ[X]) (hdeg : p.natDegree ≤ n) (θ₀ : ℝ) :
    ∑ i : Fin (2*n), ccoef n i * ((p.eval (Real.cos (θ₀ + θi n (i:ℕ))) : ℝ) : ℂ)
      = -(((p.derivative.eval (Real.cos θ₀) * Real.sin θ₀ : ℝ)) : ℂ) := by
  have h2 : (∑ i : Fin (2*n), ccoef n i * ((p.eval (Real.cos (θ₀ + θi n (i:ℕ))) : ℝ) : ℂ))
      = ∑ i : Fin (2*n), ccoef n i * (∑ k : Fin (2*n+1), (cP n p).coeff (k:ℕ)
          * Complex.exp (Complex.I * ((((k:ℤ):ℂ) - ((n:ℤ):ℂ)) * ((θ₀ + θi n (i:ℕ)) : ℂ)))) := by
    apply Finset.sum_congr rfl; intro i _
    rw [show (↑θ₀ + ↑(θi n (i:ℕ)) : ℂ) = ↑(θ₀ + θi n (i:ℕ)) by push_cast; ring]
    rw [hS_eq n hn p hdeg (θ₀ + θi n (i:ℕ))]
  have h3 : (∑ i : Fin (2*n), ccoef n i * (∑ k : Fin (2*n+1), (cP n p).coeff (k:ℕ)
          * Complex.exp (Complex.I * ((((k:ℤ):ℂ) - ((n:ℤ):ℂ)) * ((θ₀ + θi n (i:ℕ)) : ℂ)))))
      = ∑ i : Fin (2*n), ccoef n i * (∑ k : Fin (2*n+1), (cP n p).coeff (k:ℕ)
          * Complex.exp (Complex.I * ((((k:ℤ):ℂ) - ((n:ℤ):ℂ)) * (θ₀ + θi n (i:ℕ))))) := by
    apply Finset.sum_congr rfl; intro i _
    apply congrArg (fun t => ccoef n i * t)
    apply Finset.sum_congr rfl; intro k _
    apply congrArg (fun t => (cP n p).coeff (k:ℕ) * Complex.exp (Complex.I * t))
    rw [show (↑θ₀ + ↑(θi n (i:ℕ)) : ℂ) = ↑(θ₀ + θi n (i:ℕ)) by push_cast; ring]
  rw [h2, h3]
  simp only [← mul_assoc]
  rw [riesz_formula n hn θ₀ (fun k : Fin (2*n+1) => (cP n p).coeff (k:ℕ))]
  simpa only [mc, ← mul_assoc] using hS'_deriv n hn p hdeg θ₀

end BernsteinAux


open BernsteinAux

theorem bernstein_deriv_sqrt_le (n : ℕ) (p : Polynomial ℝ)
    (hdeg : p.degree ≤ n) (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.derivative.eval x| * Real.sqrt (1 - x ^ 2) ≤ (n : ℝ) := by
  intro x hx
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have hp : p = C (p.coeff 0) := eq_C_of_degree_le_zero hdeg
    rw [hp, derivative_C]
    simp
  · have hnat : p.natDegree ≤ n := by rw [natDegree_le_iff_degree_le]; exact hdeg
    set θ₀ : ℝ := Real.arccos x
    have hcos : Real.cos θ₀ = x := Real.cos_arccos hx.1 hx.2
    have hsin : Real.sin θ₀ = Real.sqrt (1 - x^2) := Real.sin_arccos x
    have hb : ∀ i : Fin (2*n), |p.eval (Real.cos (θ₀ + θi n (i:ℕ)))| ≤ 1 := fun i =>
      h _ (Set.mem_Icc.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    have hbound : ‖(∑ i : Fin (2*n), ccoef n i
        * ((p.eval (Real.cos (θ₀ + θi n (i:ℕ))) : ℝ) : ℂ))‖ ≤ (n:ℝ) := by
      calc ‖(∑ i : Fin (2*n), ccoef n i
            * ((p.eval (Real.cos (θ₀ + θi n (i:ℕ))) : ℝ) : ℂ))‖
          ≤ ∑ i : Fin (2*n), ‖ccoef n i
              * ((p.eval (Real.cos (θ₀ + θi n (i:ℕ))) : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ = ∑ i : Fin (2*n), ‖ccoef n i‖ * |p.eval (Real.cos (θ₀ + θi n (i:ℕ)))| := by
            apply Finset.sum_congr rfl; intro i _
            rw [norm_mul]
            congr 1
            exact RCLike.norm_ofReal _
        _ ≤ ∑ i : Fin (2*n), ‖ccoef n i‖ * 1 := by
            apply Finset.sum_le_sum; intro i _
            exact mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)
        _ = (∑ i : Fin (2*n), ‖ccoef n i‖) := by
            rw [Finset.sum_congr rfl (fun i _ => mul_one _)]
        _ = (n:ℝ) := sum_abs_ccoeff n hn
    rw [riesz_poly n hn p hnat θ₀, norm_neg, hcos, hsin] at hbound
    have h1 : ‖((p.derivative.eval x * Real.sqrt (1 - x^2) : ℝ) : ℂ)‖
        = |p.derivative.eval x| * Real.sqrt (1 - x^2) := by
      rw [show |p.derivative.eval x| * Real.sqrt (1 - x^2)
          = |p.derivative.eval x * Real.sqrt (1 - x^2)| by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]]
      exact RCLike.norm_ofReal _
    rwa [h1] at hbound

end Commons.Analysis.Polynomial