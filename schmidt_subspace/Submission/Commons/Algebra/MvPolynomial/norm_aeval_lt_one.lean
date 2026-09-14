import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Norm bound for the evaluation of an auxiliary polynomial

This file proves `Commons.Algebra.MvPolynomial.norm_aeval_lt_one`, the estimate used in the
proof of Schmidt's subspace theorem which bounds the size of `aeval u G` in terms of the
size of the coefficients of `G`, the growth of the points `u`, and the "degree window"
conditions satisfied by the exponents of `G`.

The mathematical content is the following.  Suppose:
* `u (h,k)` has norm at most `C0 * Q h ^ (γ k)`,
* every exponent `J` in the support of `G` has `∑ k, J (h,k) ≤ d h` for each `h`,
* the normalized exponents `∑ h, J (h,k) / d h` are all within `m/N ± (m*W + nu)`,
* `D ≤ d h * log (Q h) ≤ (1+Θ) * D`.
Then the logarithm of each monomial of `aeval u G` is at most
`log Bnd + (∑ h, d h) * log C0` plus a negative multiple of `D`, so that the total
number of terms (`card * Bnd`) is absorbed and `‖aeval u G‖ < 1`.

## Main results

* `Commons.Algebra.MvPolynomial.norm_aeval_lt_one`
-/

namespace Commons.Algebra.MvPolynomial

open Finset

/-- Norm bound for `aeval` on monomials.  The norm of the evaluation of `G` at `u` is at most
the sum over the support of the coefficients times the products of the norms of the `u i`
raised to the exponents of the respective monomials. -/
theorem norm_aeval_le_sum {σ : Type*} [Fintype σ] (u : σ → ℂ) (G : MvPolynomial σ ℂ) :
    ‖MvPolynomial.aeval u G‖ ≤ ∑ J ∈ G.support, ‖G.coeff J‖ * ∏ i, ‖u i‖ ^ (J i) := by
  have hprod (J : σ →₀ ℕ) : ‖J.prod (fun q n => u q ^ n)‖ = ∏ i, ‖u i‖ ^ (J i) := by
    rw [Finsupp.prod, norm_prod]
    rw [show ∏ i, ‖u i‖ ^ (J i) = ∏ i ∈ J.support, ‖u i‖ ^ (J i) by
      rw [Finset.prod_subset (s₁ := J.support) (s₂ := Finset.univ)
            (fun i _ => Finset.mem_univ i) (fun i _ hi => by
              rw [Finsupp.notMem_support_iff] at hi; rw [hi]; simp)]]
    exact Finset.prod_congr rfl fun i _ => by rw [norm_pow]
  have haeval : MvPolynomial.aeval u G
      = ∑ J ∈ G.support, G.coeff J * (J.prod fun q n => u q ^ n) := by
    conv_lhs => rw [G.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [MvPolynomial.aeval_monomial]
    simp
  rw [haeval]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun J _ => ?_)
  rw [norm_mul, hprod J]

/-- The product over all pairs `i = (h,k)` of `(C0 * Q h ^ γ k) ^ b (h,k)` equals
`C0 ^ (∑ i, b i)` times the product over `h` of `Q h` raised to `∑ k, γ k * b (h,k)`. -/
theorem prod_mul_rpow_pow (m N : ℕ) (b : Fin m × Fin N → ℕ) (C0 : ℝ) (Q : Fin m → ℝ)
    (γ : Fin N → ℝ) (hQ : ∀ h, 0 < Q h) :
    ∏ i : Fin m × Fin N, (C0 * Q i.1 ^ γ i.2) ^ (b i) =
      C0 ^ (∑ i, b i) * ∏ h, Q h ^ (∑ k, γ k * (b (h, k) : ℝ)) := by
  have step1 : ∏ i : Fin m × Fin N, (C0 * Q i.1 ^ γ i.2) ^ (b i)
      = (∏ i : Fin m × Fin N, C0 ^ (b i))
        * ∏ i : Fin m × Fin N, (Q i.1 ^ γ i.2) ^ (b i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
  rw [step1, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [Real.rpow_sum_of_pos (hQ h) (fun k => γ k * (b (h, k) : ℝ)) Finset.univ]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Real.rpow_mul_natCast (le_of_lt (hQ h))]

/-- A product of real powers of positive reals is the exponential of the corresponding sum
of logarithms. -/
theorem prod_rpow_eq_exp_sum_log {ι : Type*} (s : Finset ι) (Q : ι → ℝ)
    (hQ : ∀ i ∈ s, 0 < Q i) (X : ι → ℝ) :
    ∏ i ∈ s, Q i ^ X i = Real.exp (∑ i ∈ s, Real.log (Q i) * X i) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Real.rpow_def_of_pos (hQ i hi)]

/-- Sum bound for column weights: if each `C k` lies in the window `m/N ± (m*W + nu)` and
`∑ k, γ k ≤ -ε`, then `∑ k, γ k * C k ≤ -(m/N)*ε + (m*W+nu) * ∑ k, |γ k|`. -/
theorem sum_mul_le_col_bound {m N : ℕ} (hN : 0 < N) (γ : Fin N → ℝ) (ε W nu : ℝ)
    (hγ : ∑ k, γ k ≤ -ε) (C : Fin N → ℝ)
    (hlo : ∀ k, (m : ℝ) / (N : ℝ) - ((m : ℝ) * W + nu) ≤ C k)
    (hhi : ∀ k, C k ≤ (m : ℝ) / (N : ℝ) + ((m : ℝ) * W + nu)) :
    ∑ k, γ k * C k ≤ -((m : ℝ) / (N : ℝ)) * ε + ((m : ℝ) * W + nu) * ∑ k, |γ k| := by
  have hpt : ∀ k, γ k * C k ≤ γ k * ((m:ℝ)/(N:ℝ)) + |γ k| * ((m:ℝ)*W + nu) := by
    intro k
    rcases lt_or_ge (γ k) 0 with hk | hk
    · have h1 : γ k * C k ≤ γ k * ((m:ℝ)/(N:ℝ) - ((m:ℝ)*W + nu)) :=
        mul_le_mul_of_nonpos_left (hlo k) (le_of_lt hk)
      rw [mul_sub] at h1
      have h2 : γ k * ((m:ℝ)*W + nu) = -(|γ k| * ((m:ℝ)*W + nu)) := by
        rw [abs_of_neg hk]; ring
      linarith [h1, h2.le, h2.ge]
    · have h1 : γ k * C k ≤ γ k * ((m:ℝ)/(N:ℝ) + ((m:ℝ)*W + nu)) :=
        mul_le_mul_of_nonneg_left (hhi k) hk
      rw [mul_add] at h1
      have h2 : γ k * ((m:ℝ)*W + nu) = |γ k| * ((m:ℝ)*W + nu) := by rw [abs_of_nonneg hk]
      linarith [h1, h2.le, h2.ge]
  calc ∑ k, γ k * C k ≤ ∑ k, (γ k * ((m:ℝ)/(N:ℝ)) + |γ k| * ((m:ℝ)*W + nu)) :=
        Finset.sum_le_sum fun k _ => hpt k
    _ = (∑ k, γ k) * ((m:ℝ)/(N:ℝ)) + (∑ k, |γ k|) * ((m:ℝ)*W + nu) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    _ ≤ (-ε) * ((m:ℝ)/(N:ℝ)) + (∑ k, |γ k|) * ((m:ℝ)*W + nu) := by
        have hmn : 0 ≤ (m:ℝ)/(N:ℝ) := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_right hγ hmn) le_rfl
    _ = -((m:ℝ)/(N:ℝ)) * ε + ((m:ℝ) * W + nu) * ∑ k, |γ k| := by ring

/-- Bound on the positive part of a weighted sum by the total weight: if `C k ≥ 0` for all `k`
and `∑ k, C k ≤ m`, then `∑ k ∈ {k | 0 ≤ γ k}, γ k * C k ≤ (∑ k, |γ k|) * m`. -/
theorem sum_filter_nonneg_mul_le {m N : ℕ} (γ C : Fin N → ℝ) (hC : ∀ k, 0 ≤ C k)
    (hsum : ∑ k, C k ≤ (m : ℝ)) :
    ∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * C k ≤ (∑ k, |γ k|) * (m : ℝ) := by
  have hS : ∀ k, γ k ≤ ∑ k' : Fin N, |γ k'| := fun k => by
    calc γ k ≤ |γ k| := le_abs_self _
      _ ≤ ∑ k' : Fin N, |γ k'| :=
          Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin N => |γ i|)
            (fun i _ => abs_nonneg (γ i)) (Finset.mem_univ k)
  calc ∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * C k
      ≤ ∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), (∑ k' : Fin N, |γ k'|) * C k := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_right (hS k) (hC k)
    _ = (∑ k, |γ k|) * ∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), C k := by
        rw [Finset.mul_sum]
    _ ≤ (∑ k, |γ k|) * ∑ k, C k := by
        refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun k _ => abs_nonneg (γ k))
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => hC k)
    _ ≤ (∑ k, |γ k|) * (m:ℝ) :=
        mul_le_mul_of_nonneg_left hsum (Finset.sum_nonneg fun k _ => abs_nonneg (γ k))

/-- If the rows `∑ k, b h k` are bounded by `d h ≥ 1`, then the total column sum of the
normalized weights `b h k / d h` is at most the number of rows. -/
theorem sum_div_le_card {m N : ℕ} (d : Fin m → ℕ) (hd : ∀ h, 1 ≤ d h) (b : Fin m → Fin N → ℝ)
    (hrow : ∀ h, ∑ k, b h k ≤ (d h : ℝ)) :
    ∑ k, ∑ h, b h k / (d h : ℝ) ≤ (m : ℝ) := by
  have hdpos : ∀ h, (0:ℝ) < (d h : ℝ) := fun h => by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hd h))
  rw [Finset.sum_comm]
  calc ∑ h, ∑ k, b h k / (d h : ℝ) = ∑ h, (∑ k, b h k) / (d h : ℝ) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.sum_div]
    _ ≤ ∑ _h : Fin m, (1:ℝ) := by
        refine Finset.sum_le_sum fun h _ => ?_
        rw [div_le_one (hdpos h)]
        exact hrow h
    _ = (m : ℝ) := by simp

/-- If `D ≤ d h * log (Q h) ≤ (1+Θ) * D` and `b h k ≥ 0`, then the weighted average
`∑ h, b h k * log (Q h)` is trapped between `D * ∑ h, b h k / d h` and
`(1+Θ) * D * ∑ h, b h k / d h`. -/
theorem mul_log_bounds {m N : ℕ} (d : Fin m → ℕ) (hd : ∀ h, 1 ≤ d h) (Q : Fin m → ℝ)
    (D Θ : ℝ) (hDlo : ∀ h, D ≤ (d h : ℝ) * Real.log (Q h))
    (hDhi : ∀ h, (d h : ℝ) * Real.log (Q h) ≤ (1 + Θ) * D)
    (b : Fin m → Fin N → ℝ) (hb : ∀ h k, 0 ≤ b h k) (k : Fin N) :
    D * (∑ h, b h k / (d h : ℝ)) ≤ ∑ h, b h k * Real.log (Q h) ∧
      ∑ h, b h k * Real.log (Q h) ≤ (1 + Θ) * D * (∑ h, b h k / (d h : ℝ)) := by
  have hdpos : ∀ h, (0:ℝ) < (d h : ℝ) := fun h => by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hd h))
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun h _ => ?_
    have h1 : D / (d h : ℝ) ≤ Real.log (Q h) := by
      rw [div_le_iff₀ (hdpos h)]
      linarith [hDlo h]
    calc D * (b h k / (d h : ℝ)) = b h k * (D / (d h : ℝ)) := by ring
      _ ≤ b h k * Real.log (Q h) := mul_le_mul_of_nonneg_left h1 (hb h k)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun h _ => ?_
    have h1 : Real.log (Q h) ≤ (1 + Θ) * D / (d h : ℝ) := by
      rw [le_div_iff₀ (hdpos h)]
      linarith [hDhi h]
    calc b h k * Real.log (Q h) ≤ b h k * ((1 + Θ) * D / (d h : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (hb h k)
      _ = (1 + Θ) * D * (b h k / (d h : ℝ)) := by ring

theorem norm_aeval_lt_one {m N : ℕ} (hN : 0 < N) (d : Fin m → ℕ) (hd : ∀ h, 1 ≤ d h)
    (γ : Fin N → ℝ) (ε : ℝ) (hε : 0 < ε) (hγ : ∑ k, γ k ≤ -ε)
    (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h)
    (D Θ W nu Bnd C0 : ℝ) (hD : 0 < D) (hΘ : 0 ≤ Θ) (hW : 0 ≤ W) (hnu : 0 ≤ nu)
    (hBnd : 0 ≤ Bnd) (hC0 : 1 ≤ C0)
    (hDlo : ∀ h, D ≤ (d h : ℝ) * Real.log (Q h))
    (hDhi : ∀ h, (d h : ℝ) * Real.log (Q h) ≤ (1 + Θ) * D)
    (u : Fin m × Fin N → ℂ) (hu : ∀ q, ‖u q‖ ≤ C0 * Q q.1 ^ (γ q.2))
    (G : MvPolynomial (Fin m × Fin N) ℂ)
    (hcoeff : ∀ J ∈ G.support, ‖G.coeff J‖ ≤ Bnd)
    (hdeg : ∀ J ∈ G.support, ∀ h : Fin m, ∑ k, J (h, k) ≤ d h)
    (hwin : ∀ J ∈ G.support, ∀ k : Fin N,
      |(∑ h : Fin m, (J (h, k) : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)| ≤ (m : ℝ) * W + nu)
    (hbig : 2 * (N : ℝ) * (Real.log ((G.support.card : ℝ) * Bnd) + (∑ h, d h) * Real.log C0)
      < D * ε * (m : ℝ))
    (hsmall : ((m : ℝ) * W + nu + Θ * (m : ℝ)) * (∑ k, |γ k|) < ε * (m : ℝ) / (2 * (N : ℝ))) :
    ‖MvPolynomial.aeval u G‖ < 1 := by
  classical
  by_cases hG : G = 0
  · rw [hG, map_zero, norm_zero]; norm_num
  have hdpos : ∀ h, (0:ℝ) < (d h : ℝ) := fun h => by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hd h))
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  -- abbreviations
  set Sg : ℝ := ∑ k, |γ k| with hSg
  set cc : ℝ := ((m:ℝ) * W + nu + Θ * (m:ℝ)) * Sg with hcc
  set bdd : ℝ := D * (-((m:ℝ) / (N:ℝ)) * ε + cc) with hbdd
  set xv : ℝ := D * ε * (m:ℝ) / (2 * (N:ℝ)) with hxv
  -- `cc` is below `ε * m / (2N)`
  have hcc_lt : cc < ε * (m:ℝ) / (2 * (N:ℝ)) := by
    rw [hcc]; exact hsmall
  -- hence `bdd < -xv`
  have hbdd_lt : bdd < -xv := by
    have h2 : -((m:ℝ) / (N:ℝ)) * ε + ε * (m:ℝ) / (2 * (N:ℝ))
        = -(ε * (m:ℝ) / (2 * (N:ℝ))) := by
      have hNn : (N:ℝ) ≠ 0 := ne_of_gt hNpos
      field_simp
      ring
    rw [hbdd, hxv]
    have h1 : D * (-((m:ℝ) / (N:ℝ)) * ε + cc) < D * (-(ε * (m:ℝ) / (2 * (N:ℝ)))) := by
      refine mul_lt_mul_of_pos_left ?_ hD
      rw [← h2]
      exact add_lt_add_right hcc_lt _
    refine lt_of_lt_of_le h1 ?_
    rw [show D * (-(ε * (m:ℝ) / (2 * (N:ℝ)))) = -(D * ε * (m:ℝ) / (2 * (N:ℝ))) by ring]
  -- the key logarithmic estimate for a single exponent vector
  have hlog : ∀ J ∈ G.support,
      ∑ h, Real.log (Q h) * (∑ k, γ k * (J (h, k) : ℝ)) ≤ bdd := by
    intro J hJ
    set Bk : Fin N → ℝ := fun k => ∑ h, (J (h, k) : ℝ) * Real.log (Q h) with hBk
    set Ck : Fin N → ℝ := fun k => ∑ h, (J (h, k) : ℝ) / (d h : ℝ) with hCk
    have hCnn : ∀ k, 0 ≤ Ck k := by
      intro k
      rw [hCk]
      exact Finset.sum_nonneg fun h _ => div_nonneg (Nat.cast_nonneg _) (le_of_lt (hdpos h))
    have hClo : ∀ k, (m:ℝ)/(N:ℝ) - ((m:ℝ)*W + nu) ≤ Ck k := by
      intro k
      have h := (abs_le.mp (hwin J hJ k)).1
      rw [hCk]
      linarith
    have hChi : ∀ k, Ck k ≤ (m:ℝ)/(N:ℝ) + ((m:ℝ)*W + nu) := by
      intro k
      have h := (abs_le.mp (hwin J hJ k)).2
      rw [hCk]
      linarith
    have hCsum : ∑ k, Ck k ≤ (m : ℝ) := by
      rw [hCk]
      refine sum_div_le_card d hd (fun h k => (J (h, k) : ℝ)) fun h => ?_
      rw [← Nat.cast_sum]
      exact_mod_cast hdeg J hJ h
    have hBkb : ∀ k, D * Ck k ≤ Bk k ∧ Bk k ≤ (1+Θ)*D*Ck k := by
      intro k
      rw [hBk, hCk]
      exact mul_log_bounds d hd Q D Θ hDlo hDhi (fun h k => (J (h, k) : ℝ))
        (fun h k => Nat.cast_nonneg _) k
    have h1 : ∑ h, Real.log (Q h) * (∑ k, γ k * (J (h, k) : ℝ)) = ∑ k, γ k * Bk k := by
      rw [hBk]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact Finset.sum_congr rfl fun h _ => by ring
    have hpart1 : ∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * Bk k
        ≤ (1+Θ)*D * (∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * Ck k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' : 0 ≤ γ k := (Finset.mem_filter.mp hk).2
      calc γ k * Bk k ≤ γ k * ((1+Θ)*D*Ck k) := mul_le_mul_of_nonneg_left (hBkb k).2 hk'
        _ = (1+Θ)*D*(γ k * Ck k) := by ring
    have hpart2 : ∑ k ∈ Finset.univ.filter (fun k => ¬ (0 ≤ γ k)), γ k * Bk k
        ≤ D * (∑ k ∈ Finset.univ.filter (fun k => ¬ (0 ≤ γ k)), γ k * Ck k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' : γ k < 0 := not_le.mp (Finset.mem_filter.mp hk).2
      calc γ k * Bk k ≤ γ k * (D*Ck k) := mul_le_mul_of_nonpos_left (hBkb k).1 (le_of_lt hk')
        _ = D*(γ k * Ck k) := by ring
    have hsplit : ∑ k, γ k * Bk k
        = (∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * Bk k)
          + (∑ k ∈ Finset.univ.filter (fun k => ¬ (0 ≤ γ k)), γ k * Bk k) := by
      rw [Finset.sum_filter_add_sum_filter_not]
    have hA12 : (∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * Ck k)
          + (∑ k ∈ Finset.univ.filter (fun k => ¬ (0 ≤ γ k)), γ k * Ck k)
        = ∑ k, γ k * Ck k := by
      rw [Finset.sum_filter_add_sum_filter_not]
    have hA1 : ∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * Ck k ≤ Sg * (m:ℝ) := by
      have := sum_filter_nonneg_mul_le γ Ck hCnn hCsum
      simpa [hSg] using this
    have hAcol : ∑ k, γ k * Ck k ≤ -((m:ℝ)/(N:ℝ))*ε + ((m:ℝ)*W + nu) * Sg := by
      have := sum_mul_le_col_bound hN γ ε W nu hγ Ck hClo hChi
      simpa [hSg] using this
    calc ∑ h, Real.log (Q h) * (∑ k, γ k * (J (h, k) : ℝ))
        = ∑ k, γ k * Bk k := h1
      _ = (∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * Bk k)
          + (∑ k ∈ Finset.univ.filter (fun k => ¬ (0 ≤ γ k)), γ k * Bk k) := hsplit
      _ ≤ (1+Θ)*D * (∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * Ck k)
          + D * (∑ k ∈ Finset.univ.filter (fun k => ¬ (0 ≤ γ k)), γ k * Ck k) :=
            add_le_add hpart1 hpart2
      _ = D * ((∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * Ck k)
          + (∑ k ∈ Finset.univ.filter (fun k => ¬ (0 ≤ γ k)), γ k * Ck k))
          + Θ*D * (∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * Ck k) := by ring
      _ = D * (∑ k, γ k * Ck k)
          + Θ*D * (∑ k ∈ Finset.univ.filter (fun k => 0 ≤ γ k), γ k * Ck k) := by rw [hA12]
      _ ≤ D * (-((m:ℝ)/(N:ℝ))*ε + ((m:ℝ)*W + nu) * Sg) + Θ*D*(Sg*(m:ℝ)) :=
            add_le_add (mul_le_mul_of_nonneg_left hAcol (le_of_lt hD))
              (mul_le_mul_of_nonneg_left hA1 (mul_nonneg hΘ (le_of_lt hD)))
      _ = bdd := by rw [hbdd, hcc]; ring
  -- bound each term of the evaluation
  have hterm : ∀ J ∈ G.support, ‖G.coeff J‖ * ∏ i : Fin m × Fin N, ‖u i‖ ^ (J i)
      ≤ Bnd * C0 ^ (∑ h, d h) * Real.exp bdd := by
    intro J hJ
    have hpb : ∏ i : Fin m × Fin N, ‖u i‖ ^ (J i) ≤ C0 ^ (∑ h, d h) * Real.exp bdd := by
      have h1 : ∏ i : Fin m × Fin N, ‖u i‖ ^ (J i)
          ≤ ∏ i : Fin m × Fin N, (C0 * Q i.1 ^ (γ i.2)) ^ (J i) := by
        refine Finset.prod_le_prod (fun i _ => pow_nonneg (norm_nonneg _) _) fun i _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (hu i) (J i)
      rw [prod_mul_rpow_pow m N J C0 Q γ hQ] at h1
      have h3 : C0 ^ (∑ i : Fin m × Fin N, J i) ≤ C0 ^ (∑ h, d h) := by
        refine pow_le_pow_right₀ hC0 ?_
        rw [Fintype.sum_prod_type]
        exact Finset.sum_le_sum fun h _ => hdeg J hJ h
      have h4 : ∏ h, Q h ^ (∑ k, γ k * (J (h, k) : ℝ)) ≤ Real.exp bdd := by
        rw [prod_rpow_eq_exp_sum_log (s := Finset.univ) (Q := Q) (hQ := fun h _ => hQ h)
          (X := fun h => ∑ k, γ k * (J (h, k) : ℝ))]
        exact Real.exp_le_exp.mpr (hlog J hJ)
      exact le_trans h1 (mul_le_mul h3 h4
        (Finset.prod_nonneg fun h _ => Real.rpow_nonneg (le_of_lt (hQ h)) _)
        (pow_nonneg (le_trans zero_le_one hC0) _))
    calc ‖G.coeff J‖ * ∏ i, ‖u i‖ ^ (J i)
        ≤ Bnd * (C0 ^ (∑ h, d h) * Real.exp bdd) :=
          mul_le_mul (hcoeff J hJ) hpb
            (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _) hBnd
      _ = Bnd * C0 ^ (∑ h, d h) * Real.exp bdd := by ring
  -- positivity data
  have hcardpos : 0 < G.support.card := Finset.card_pos.mpr (MvPolynomial.support_nonempty.mpr hG)
  have hcardpos' : (0:ℝ) < (G.support.card : ℝ) := by exact_mod_cast hcardpos
  have hBndpos : 0 < Bnd := by
    obtain ⟨J, hJ⟩ := Finset.card_pos.mp hcardpos
    have hco : G.coeff J ≠ 0 := MvPolynomial.mem_support_iff.mp hJ
    have h1 : 0 < ‖G.coeff J‖ := norm_pos_iff.mpr hco
    linarith [hcoeff J hJ]
  have hC0powpos : 0 < C0 ^ (∑ h, d h) := pow_pos (lt_of_lt_of_le zero_lt_one hC0) _
  have hPpos : 0 < (G.support.card : ℝ) * Bnd * C0 ^ (∑ h, d h) * Real.exp (-xv) :=
    mul_pos (mul_pos (mul_pos hcardpos' hBndpos) hC0powpos) (Real.exp_pos _)
  -- the whole prefactor is at most one
  have hPle : (G.support.card : ℝ) * Bnd * C0 ^ (∑ h, d h) * Real.exp (-xv) ≤ 1 := by
    have hlogP : Real.log ((G.support.card : ℝ) * Bnd * C0 ^ (∑ h, d h) * Real.exp (-xv))
        = Real.log ((G.support.card : ℝ) * Bnd) + (∑ h, d h) * Real.log C0 + (-xv) := by
      have h1 : (G.support.card : ℝ) * Bnd * C0 ^ (∑ h, d h) * Real.exp (-xv)
          = ((G.support.card : ℝ) * Bnd) * (C0 ^ (∑ h, d h) * Real.exp (-xv)) := by ring
      rw [h1, Real.log_mul (ne_of_gt (mul_pos hcardpos' hBndpos)) (ne_of_gt (mul_pos hC0powpos (Real.exp_pos _)))]
      rw [Real.log_mul (ne_of_gt hC0powpos) (ne_of_gt (Real.exp_pos _))]
      rw [Real.log_pow, Real.log_exp]
      ring
    have hlt : Real.log ((G.support.card : ℝ) * Bnd) + (∑ h, d h) * Real.log C0 < xv := by
      rw [hxv, lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (N:ℝ))]
      linarith [hbig]
    have h1 : Real.log ((G.support.card : ℝ) * Bnd * C0 ^ (∑ h, d h) * Real.exp (-xv)) < 0 := by
      rw [hlogP]; linarith
    calc (G.support.card : ℝ) * Bnd * C0 ^ (∑ h, d h) * Real.exp (-xv)
        = Real.exp (Real.log ((G.support.card : ℝ) * Bnd * C0 ^ (∑ h, d h) * Real.exp (-xv))) :=
          (Real.exp_log hPpos).symm
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (le_of_lt h1)
      _ = 1 := Real.exp_zero
  calc ‖MvPolynomial.aeval u G‖
      ≤ ∑ J ∈ G.support, ‖G.coeff J‖ * ∏ i, ‖u i‖ ^ (J i) := norm_aeval_le_sum u G
    _ ≤ ∑ J ∈ G.support, Bnd * C0 ^ (∑ h, d h) * Real.exp bdd := Finset.sum_le_sum hterm
    _ = (G.support.card : ℝ) * (Bnd * C0 ^ (∑ h, d h) * Real.exp bdd) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ < (G.support.card : ℝ) * (Bnd * C0 ^ (∑ h, d h) * Real.exp (-xv)) := by
        refine mul_lt_mul_of_pos_left ?_ hcardpos'
        exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hbdd_lt) (mul_pos hBndpos hC0powpos)
    _ ≤ 1 := by
        rw [show (G.support.card : ℝ) * (Bnd * C0 ^ (∑ h, d h) * Real.exp (-xv))
            = (G.support.card : ℝ) * Bnd * C0 ^ (∑ h, d h) * Real.exp (-xv) by ring]
        exact hPle

end Commons.Algebra.MvPolynomial