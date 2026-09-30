import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The growth bound for `Θ(z;k,l,m)` (Baker–Wüstholz, Crelle 442 (1993), §12)

`Θ(z;k,l,m) = (1/m!) (d/dz)^m Δ(z;k)^l`, where `Δ(z;k) = (z+1)⋯(z+k)/k!`.

The two classical inputs are

* `‖Δ(z;k)‖ ≤ (e (1 + |z|/k))^k`, i.e. `|Δ|` grows at most like `(e(1+|z|/k))^k`; and
* Cauchy's estimate at radius `1`, which bounds the `m`-th Taylor coefficient of a polynomial
  by the supremum of the polynomial on the circle of radius `1` — uniformly in `m`.

Combining them with `‖w‖ ≤ ‖z‖ + 1` for `‖w - z‖ = 1` and `e(1 + (b+1)/k) ≤ 2e(1 + b/k) ≤ e³(1+b/k)`
gives the stated `(e³(1 + |z|/k))^{kl}` bound.
-/

namespace Work.BW

open Complex

/-- The `m`-th analytic derivative of the polynomial function of `P` is the formal `m`-th
derivative of `P`, evaluated at the point. -/
private lemma iteratedDeriv_poly_eval (P : Polynomial ℂ) (m : ℕ) :
    iteratedDeriv m (fun w => P.eval w) = fun w => (Polynomial.derivative^[m] P).eval w := by
  induction m with
  | zero => ext w; simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    ext w
    simp

/-- **Cauchy's estimate at radius `1`.** Every Taylor coefficient of `P` at `z` is bounded by
`C`, provided `‖P‖ ≤ C` on the circle `‖w - z‖ = 1`. In particular the bound is uniform in `m`. -/
private lemma norm_taylor_coeff_le (P : Polynomial ℂ) (m : ℕ) (z : ℂ) (C : ℝ)
    (hC : ∀ w ∈ Metric.sphere z 1, ‖P.eval w‖ ≤ C) :
    ‖(Polynomial.taylor z P).coeff m‖ ≤ C := by
  have hf : DiffContOnCl ℂ (fun w => P.eval w) (Metric.ball z 1) := P.differentiable.diffContOnCl
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (F := ℂ) m
    (by norm_num : (0:ℝ) < 1) hf hC
  have h3 : (Polynomial.derivative^[m] P).eval z
      = ((m.factorial : ℂ)) * (Polynomial.taylor z P).coeff m := by
    have h : (m.factorial • Polynomial.hasseDeriv m) P = Polynomial.derivative^[m] P :=
      congr_fun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) m) P
    rw [← h, LinearMap.smul_apply, Polynomial.eval_smul, nsmul_eq_mul, ← Polynomial.taylor_coeff]
  have hm : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hkey : (m.factorial : ℝ) * ‖(Polynomial.taylor z P).coeff m‖ ≤ (m.factorial : ℝ) * C := by
    have h := hcau
    rw [show iteratedDeriv m (fun w => P.eval w) z = (Polynomial.derivative^[m] P).eval z from
      congr_fun (iteratedDeriv_poly_eval P m) z] at h
    rw [h3, norm_mul, Complex.norm_natCast, one_pow, div_one] at h
    exact h
  exact le_of_mul_le_mul_left hkey hm

/-- `Δ(z;k) = (k!)⁻¹ ∏_{i<k} (z + i + 1)`, the explicit form of the polynomial `Δ(·;k)`. -/
private lemma Delta_eq (z : ℂ) (k : ℕ) :
    Delta z k = ((k.factorial : ℂ))⁻¹ * ∏ i ∈ Finset.range k, (z + ((i : ℂ) + 1)) := by
  rw [Delta, deltaPoly, Polynomial.qsmul_eq_C_mul, map_mul, Polynomial.aeval_C]
  congr 1
  · push_cast; ring
  · rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C]
    push_cast
    ring

/-- `‖Δ(z;k)‖ ≤ (e(1 + |z|/k))^k`. -/
private lemma norm_Delta_le_aux (z : ℂ) (k : ℕ) :
    ‖Delta z k‖ ≤ (Real.exp 1 * (1 + ‖z‖ / (k : ℝ)))^k := by
  have hprod : ‖∏ i ∈ Finset.range k, (z + ((i : ℂ) + 1))‖ ≤ (‖z‖ + k)^k := by
    calc ‖∏ i ∈ Finset.range k, (z + ((i : ℂ) + 1))‖
        ≤ ∏ i ∈ Finset.range k, ‖z + ((i : ℂ) + 1)‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ i ∈ Finset.range k, (‖z‖ + k) := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => ?_)
          have hik : (i : ℝ) + 1 ≤ (k : ℝ) := by
            have : i + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
            exact_mod_cast this
          have hnorm : ‖((i : ℂ) + 1)‖ = (i : ℝ) + 1 := by
            rw [show (i : ℂ) + 1 = ((i + 1 : ℕ) : ℂ) by push_cast; ring]
            rw [Complex.norm_natCast]; push_cast; ring
          calc ‖z + ((i : ℂ) + 1)‖ ≤ ‖z‖ + ‖((i : ℂ) + 1)‖ := norm_add_le _ _
            _ = ‖z‖ + ((i : ℝ) + 1) := by rw [hnorm]
            _ ≤ ‖z‖ + (k : ℝ) := by linarith
      _ = (‖z‖ + k)^k := by rw [Finset.prod_const, Finset.card_range]
  have hbound : ‖Delta z k‖ ≤ ((k.factorial : ℝ))⁻¹ * (‖z‖ + k)^k := by
    rw [Delta_eq, norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    simp [Delta, deltaPoly]
  · have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hfact : ((k:ℝ))^k ≤ Real.exp (k:ℝ) * ((k.factorial:ℝ)) := by
      have h := Real.pow_div_factorial_le_exp (k:ℝ) (Nat.cast_nonneg k) k
      rwa [div_le_iff₀ (by positivity : (0:ℝ) < ((k.factorial:ℝ)))] at h
    have h3 : ((k.factorial:ℝ))⁻¹ ≤ Real.exp (k:ℝ) / ((k:ℝ)^k) := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [hfact]
    have hstep : ((k.factorial:ℝ))⁻¹ * (‖z‖ + k)^k
        ≤ (Real.exp (k:ℝ) / ((k:ℝ)^k)) * (‖z‖ + k)^k :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have hfinal : (Real.exp (k:ℝ) / ((k:ℝ)^k)) * (‖z‖ + k)^k
        = (Real.exp 1 * (1 + ‖z‖ / (k:ℝ)))^k := by
      have hexp : Real.exp (k:ℝ) = (Real.exp 1)^k := by
        rw [← Real.exp_nat_mul]; norm_num
      have hdiv : (‖z‖ + (k:ℝ)) / (k:ℝ) = 1 + ‖z‖ / (k:ℝ) := by
        rw [add_div, div_self (ne_of_gt hkpos)]; ring
      rw [hexp, div_mul_eq_mul_div, ← mul_pow, ← div_pow, mul_div_assoc, hdiv, mul_pow]
    calc ‖Delta z k‖ ≤ ((k.factorial : ℝ))⁻¹ * (‖z‖ + k)^k := hbound
      _ ≤ (Real.exp (k:ℝ) / ((k:ℝ)^k)) * (‖z‖ + k)^k := hstep
      _ = (Real.exp 1 * (1 + ‖z‖ / (k:ℝ)))^k := hfinal

/-- `1/k ≤ 1` for every natural number `k` (with `1/0 = 0`). -/
private lemma one_div_natCast_le_one (k : ℕ) : (1:ℝ)/(k:ℝ) ≤ 1 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; simp
  · have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    rw [div_le_iff₀ hkpos, one_mul]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hk

/-- On the circle `‖w - z‖ = 1`, the `l`-th power of `Δ` is bounded by `(e³(1+|z|/k))^{kl}`. -/
private lemma norm_Delta_pow_le_aux (z w : ℂ) (k l : ℕ) (hw : ‖w - z‖ = 1) :
    ‖Delta w k ^ l‖ ≤ (Real.exp 3 * (1 + ‖z‖ / (k : ℝ))) ^ (k * l) := by
  have hwz : ‖w‖ ≤ ‖z‖ + 1 := by
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ = ‖z‖ + 1 := by rw [hw]; ring
  have hbase : Real.exp 1 * (1 + ‖w‖ / (k:ℝ)) ≤ Real.exp 3 * (1 + ‖z‖ / (k:ℝ)) := by
    have hd1 : ‖w‖/(k:ℝ) ≤ (‖z‖ + 1)/(k:ℝ) :=
      div_le_div_of_nonneg_right hwz (by positivity)
    have hd2 : (‖z‖ + 1)/(k:ℝ) = ‖z‖/(k:ℝ) + 1/(k:ℝ) := by rw [add_div]
    have h1k : (1:ℝ)/(k:ℝ) ≤ 1 := one_div_natCast_le_one k
    have hz : (0:ℝ) ≤ ‖z‖/(k:ℝ) := by positivity
    have h2 : (1:ℝ) + ‖w‖/(k:ℝ) ≤ 2 * (1 + ‖z‖/(k:ℝ)) := by
      nlinarith [hd1, hd2, h1k, hz]
    have hE : Real.exp 2 * Real.exp 1 = Real.exp 3 := by
      rw [← Real.exp_add]; norm_num
    have he2 : (2:ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    have h2e : 2 * Real.exp 1 ≤ Real.exp 3 :=
      (mul_le_mul_of_nonneg_right he2 (Real.exp_pos 1).le).trans_eq hE
    calc Real.exp 1 * (1 + ‖w‖/(k:ℝ))
        ≤ Real.exp 1 * (2 * (1 + ‖z‖/(k:ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le
      _ = (2 * Real.exp 1) * (1 + ‖z‖/(k:ℝ)) := by ring
      _ ≤ Real.exp 3 * (1 + ‖z‖/(k:ℝ)) :=
          mul_le_mul_of_nonneg_right h2e (by positivity)
  calc ‖Delta w k ^ l‖ = ‖Delta w k‖^l := norm_pow _ _
    _ ≤ ((Real.exp 1 * (1 + ‖w‖ / (k:ℝ)))^k)^l :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_Delta_le_aux w k) l
    _ = (Real.exp 1 * (1 + ‖w‖ / (k:ℝ)))^(k*l) := by rw [pow_mul]
    _ ≤ (Real.exp 3 * (1 + ‖z‖ / (k:ℝ)))^(k*l) :=
        pow_le_pow_left₀ (by positivity) hbase (k * l)

/-- `Θ(z;k,l,m)` is the `m`-th Taylor coefficient at `z` of `Δ(·;k)^l`. -/
private lemma Theta_eq_taylor_coeff (z : ℂ) (k l m : ℕ) :
    Theta z k l m
      = (Polynomial.taylor z ((deltaPoly k ^ l).map (algebraMap ℚ ℂ))).coeff m := by
  rw [Theta, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, ← Polynomial.hasseDeriv_map,
    Polynomial.taylor_coeff]

theorem norm_Theta_le (z : ℂ) (k l m : ℕ) :
    ‖Theta z k l m‖ ≤ (Real.exp 3 * (1 + ‖z‖ / (k : ℝ))) ^ (k * l) := by
  rw [Theta_eq_taylor_coeff z k l m]
  refine norm_taylor_coeff_le ((deltaPoly k ^ l).map (algebraMap ℚ ℂ)) m z _ ?_
  intro w hw
  have hw' : ‖w - z‖ = 1 := by
    have := Metric.mem_sphere.mp hw
    rwa [dist_eq_norm] at this
  have h1 : ((deltaPoly k ^ l).map (algebraMap ℚ ℂ)).eval w = Delta w k ^ l := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, Delta, Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map]
  rw [h1]
  exact norm_Delta_pow_le_aux z w k l hw'

end Work.BW
