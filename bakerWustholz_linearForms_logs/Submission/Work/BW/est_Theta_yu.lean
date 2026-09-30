import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.Theta_eq_taylor_coeff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # The growth bound for `Θ(z;k,l,m)` (BW §12, Yu [33] Lemma 1.6)

`Θ(z;k,l,m) = (1/m!) (d/dz)^m Δ(z;k)^l` is the `m`-th Taylor coefficient at `z` of the
polynomial `Δ(·;k)^l = (k!)^{-l} ∏_{i=1}^k (X + z + i)^l`.

* Cauchy's estimate on the circle `‖w - z‖ = 1` bounds every Taylor coefficient by the
  supremum of the polynomial on that circle, uniformly in `m`.
* On that circle `‖w + i‖ ≤ ‖z‖ + 1 + i`, and the AM–GM inequality for the arithmetic
  progression `‖z‖+2, …, ‖z‖+k+1` gives `∏_{i=1}^k (‖z‖+1+i) ≤ (‖z‖ + (k+3)/2)^k`.
* Hence `‖Θ(z;k,l,m)‖ ≤ (‖z‖ + (k+3)/2)^{kl} / (k!)^l`, and the elementary inequality
  `((‖z‖+(k+3)/2)·k/(e(‖z‖+k)))^k ≤ k!` finishes the job. -/

namespace Work.BW

open Complex Polynomial

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

/-- **Cauchy's estimate.** Every Taylor coefficient of `P` at `z` is bounded by `C / ρ^m`,
provided `‖P‖ ≤ C` on the circle `‖w - z‖ = ρ`. In particular the bound is uniform in `m`. -/
private lemma norm_taylor_coeff_le (P : Polynomial ℂ) (m : ℕ) (z : ℂ) {ρ C : ℝ} (hρ : 0 < ρ)
    (hC : ∀ w ∈ Metric.sphere z ρ, ‖P.eval w‖ ≤ C) :
    ‖(Polynomial.taylor z P).coeff m‖ ≤ C / ρ ^ m := by
  have hf : DiffContOnCl ℂ (fun w => P.eval w) (Metric.ball z ρ) := P.differentiable.diffContOnCl
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (F := ℂ) m hρ hf hC
  have h3 : (Polynomial.derivative^[m] P).eval z
      = ((m.factorial : ℂ)) * (Polynomial.taylor z P).coeff m := by
    have h : (m.factorial • Polynomial.hasseDeriv m) P = Polynomial.derivative^[m] P :=
      congr_fun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) m) P
    rw [← h, LinearMap.smul_apply, Polynomial.eval_smul, nsmul_eq_mul, ← Polynomial.taylor_coeff]
  rw [show iteratedDeriv m (fun w => P.eval w) z = (Polynomial.derivative^[m] P).eval z from
    congr_fun (iteratedDeriv_poly_eval P m) z, h3, norm_mul, Complex.norm_natCast,
    mul_div_assoc] at hcau
  exact le_of_mul_le_mul_left hcau (by positivity : (0:ℝ) < (m.factorial : ℝ))

/-- `Δ(z;k) = (k!)⁻¹ ∏_{i<k} (z + i + 1)`, the explicit form of the polynomial `Δ(·;k)`. -/
private lemma Delta_eq_prod (z : ℂ) (k : ℕ) :
    Delta z k = ((k.factorial : ℂ))⁻¹ * ∏ i ∈ Finset.range k, (z + ((i : ℂ) + 1)) := by
  rw [Delta, deltaPoly, Polynomial.qsmul_eq_C_mul, map_mul, Polynomial.aeval_C]
  congr 1
  · push_cast; ring
  · rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C]
    push_cast
    ring

/-- **AM–GM for an arithmetic progression.** `∏_{i<k} (x + i + 1) ≤ (x + (k+1)/2)^k` for
`x ≥ 0`. Proved by induction on `k`; the induction step is Bernoulli's inequality. -/
private lemma prod_range_add_one_le (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    ∏ i ∈ Finset.range k, (x + ((i : ℝ) + 1)) ≤ (x + ((k : ℝ) + 1) / 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ]
    have hstep : (x + ((k : ℝ) + 1) / 2) ^ k * (x + ((k : ℝ) + 1))
        ≤ (x + ((k : ℝ) + 2) / 2) ^ (k + 1) := by
      set a : ℝ := x + ((k : ℝ) + 1) / 2 with ha
      have ha0 : 0 < a := by
        rw [ha]
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      have heq1 : x + ((k : ℝ) + 1) = a + ((k : ℝ) + 1) / 2 := by rw [ha]; ring
      have heq2 : x + ((k : ℝ) + 2) / 2 = a + 1 / 2 := by rw [ha]; ring
      rw [heq1, heq2]
      have hb : 1 + ((k : ℝ) + 1) * (1 / (2 * a)) ≤ (1 + 1 / (2 * a)) ^ (k + 1) := by
        have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / (2 * a) by
          have h0 : (0:ℝ) ≤ 1 / (2 * a) := by positivity
          linarith) (k + 1)
        simpa only [Nat.cast_add, Nat.cast_one] using h
      have ha1 : a + 1 / 2 = a * (1 + 1 / (2 * a)) := by
        field_simp
      have ha2 : a ^ k * (a + ((k : ℝ) + 1) / 2)
          = a ^ (k + 1) * (1 + ((k : ℝ) + 1) * (1 / (2 * a))) := by
        rw [pow_succ]
        field_simp
      rw [ha1, mul_pow, ha2]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    calc (∏ i ∈ Finset.range k, (x + ((i : ℝ) + 1))) * (x + ((k : ℝ) + 1))
        ≤ (x + ((k : ℝ) + 1) / 2) ^ k * (x + ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
      _ ≤ (x + ((k : ℝ) + 2) / 2) ^ (k + 1) := hstep
      _ = (x + ((↑(k + 1) : ℝ) + 1) / 2) ^ (k + 1) := by
          congr 1
          push_cast
          ring

/-- **The radius-`1` form of the bound.** For every `m`, `‖Θ(z;k,l,m)‖` is at most the supremum
of `|Δ(·;k)^l|` on the unit circle around `z`, hence
`≤ (‖z‖ + (k+3)/2)^{kl} / (k!)^l`. -/
private lemma Theta_rho_one_bound (z : ℂ) (k l m : ℕ) (_hk : 1 ≤ k) :
    ‖Theta z k l m‖ ≤ (‖z‖ + ((k : ℝ) + 3) / 2) ^ (k * l) / ((k.factorial : ℝ)) ^ l := by
  rw [Theta_eq_taylor_coeff z k l m]
  have hC : ∀ w ∈ Metric.sphere z 1,
      ‖((deltaPoly k ^ l).map (algebraMap ℚ ℂ)).eval w‖
        ≤ (‖z‖ + ((k : ℝ) + 3) / 2) ^ (k * l) / ((k.factorial : ℝ)) ^ l := by
    intro w hw
    have hw' : ‖w - z‖ = 1 := by
      have h := Metric.mem_sphere.mp hw
      rwa [dist_eq_norm] at h
    have hwz : ‖w‖ ≤ ‖z‖ + 1 := by
      calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z‖ + 1 := by rw [hw', add_comm]
    have hev : ((deltaPoly k ^ l).map (algebraMap ℚ ℂ)).eval w = Delta w k ^ l := by
      rw [Polynomial.map_pow, Polynomial.eval_pow, Delta, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map]
    rw [hev, norm_pow]
    have hD : ‖Delta w k‖ ≤ (‖z‖ + ((k : ℝ) + 3) / 2) ^ k / ((k.factorial : ℝ)) := by
      have hprod : ‖∏ i ∈ Finset.range k, (w + ((i : ℂ) + 1))‖
          ≤ (‖z‖ + 1 + ((k : ℝ) + 1) / 2) ^ k := by
        calc ‖∏ i ∈ Finset.range k, (w + ((i : ℂ) + 1))‖
            ≤ ∏ i ∈ Finset.range k, ‖w + ((i : ℂ) + 1)‖ := Finset.norm_prod_le _ _
          _ ≤ ∏ i ∈ Finset.range k, ((‖z‖ + 1) + ((i : ℝ) + 1)) := by
              refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
              calc ‖w + ((i : ℂ) + 1)‖ ≤ ‖w‖ + ‖((i : ℂ) + 1)‖ := norm_add_le _ _
                _ = ‖w‖ + ((i : ℝ) + 1) := by
                    rw [show ((i : ℂ) + 1) = ((i + 1 : ℕ) : ℂ) by push_cast; ring]
                    rw [Complex.norm_natCast]; push_cast; ring
                _ ≤ (‖z‖ + 1) + ((i : ℝ) + 1) := by linarith
          _ ≤ ((‖z‖ + 1) + ((k : ℝ) + 1) / 2) ^ k :=
              prod_range_add_one_le (‖z‖ + 1) (by positivity) k
      calc ‖Delta w k‖
          = ‖((k.factorial : ℂ))⁻¹ * ∏ i ∈ Finset.range k, (w + ((i : ℂ) + 1))‖ := by
              rw [Delta_eq_prod]
        _ = ((k.factorial : ℝ))⁻¹ * ‖∏ i ∈ Finset.range k, (w + ((i : ℂ) + 1))‖ := by
              rw [norm_mul, norm_inv, Complex.norm_natCast]
        _ ≤ ((k.factorial : ℝ))⁻¹ * (‖z‖ + 1 + ((k : ℝ) + 1) / 2) ^ k :=
              mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = (‖z‖ + ((k : ℝ) + 3) / 2) ^ k / ((k.factorial : ℝ)) := by
              rw [inv_mul_eq_div,
                show ‖z‖ + 1 + ((k : ℝ) + 1) / 2 = ‖z‖ + ((k : ℝ) + 3) / 2 by ring]
    calc ‖Delta w k‖ ^ l
        ≤ ((‖z‖ + ((k : ℝ) + 3) / 2) ^ k / ((k.factorial : ℝ))) ^ l :=
          pow_le_pow_left₀ (norm_nonneg _) hD l
      _ = (‖z‖ + ((k : ℝ) + 3) / 2) ^ (k * l) / ((k.factorial : ℝ)) ^ l := by
          rw [div_pow, ← pow_mul]
  have h := norm_taylor_coeff_le ((deltaPoly k ^ l).map (algebraMap ℚ ℂ)) m z
      (by norm_num : (0 : ℝ) < 1) hC
  simpa using h

/-- **The elementary numeric core.** For `b ≥ 0` and `k ≥ 1`,
`((b + (k+3)/2)·k/(e(b+k)))^k ≤ k!`. -/
private lemma key_num_aux (b : ℝ) (hb : 0 ≤ b) (k : ℕ) (hk : 1 ≤ k) :
    ((b + ((k : ℝ) + 3) / 2) * (k : ℝ) / (Real.exp 1 * ((k : ℝ) + b))) ^ k
      ≤ ((k.factorial : ℝ)) := by
  have hE : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  rcases eq_or_lt_of_le hk with hk1 | hk1
  · subst hk1
    norm_num
    rw [div_le_one (by positivity)]
    nlinarith [hE, hb, mul_nonneg hb (show (0:ℝ) ≤ Real.exp 1 - 1 by linarith)]
  · rcases eq_or_lt_of_le (show 2 ≤ k by omega) with hk2 | hk2
    · subst hk2
      norm_num
      rw [div_pow, div_le_iff₀ (by positivity)]
      have hsum : (0:ℝ) ≤ 3 * (b + 2) + 2 * (b + 5 / 2) := by linarith
      have hsub : (0:ℝ) ≤ 3 * (b + 2) - 2 * (b + 5 / 2) := by linarith
      have hsq : (2 * (b + 5 / 2)) ^ 2 ≤ (3 * (b + 2)) ^ 2 := by
        nlinarith [mul_nonneg hsum hsub]
      have h27 : (0:ℝ) ≤ 2 * (Real.exp 1) ^ 2 - 9 := by nlinarith [hE]
      nlinarith [hsq, mul_nonneg h27 (sq_nonneg (b + 2))]
    · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hk3 : (3:ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 3 ≤ k by omega)
      have hC1 : b + ((k : ℝ) + 3) / 2 ≤ (k : ℝ) + b := by linarith
      have hKb : (0:ℝ) < (k : ℝ) + b := by linarith
      have hstep : (b + ((k : ℝ) + 3) / 2) * (k : ℝ) / (Real.exp 1 * ((k : ℝ) + b))
          ≤ (k : ℝ) / Real.exp 1 := by
        have hnum : (b + ((k : ℝ) + 3) / 2) * (k : ℝ) ≤ ((k : ℝ) + b) * (k : ℝ) := by
          nlinarith [hC1, hkpos]
        have h2 : (b + ((k : ℝ) + 3) / 2) * (k : ℝ) / (Real.exp 1 * ((k : ℝ) + b))
            ≤ ((k : ℝ) + b) * (k : ℝ) / (Real.exp 1 * ((k : ℝ) + b)) :=
          div_le_div_of_nonneg_right hnum (by positivity)
        have h3 : ((k : ℝ) + b) * (k : ℝ) / (Real.exp 1 * ((k : ℝ) + b))
            = (k : ℝ) / Real.exp 1 := by
          field_simp
        rwa [h3] at h2
      calc ((b + ((k : ℝ) + 3) / 2) * (k : ℝ) / (Real.exp 1 * ((k : ℝ) + b))) ^ k
          ≤ ((k : ℝ) / Real.exp 1) ^ k := pow_le_pow_left₀ (by positivity) hstep k
        _ = (k : ℝ) ^ k / (Real.exp 1) ^ k := by rw [div_pow]
        _ ≤ ((k.factorial : ℝ)) := by
            have hexp : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
              simpa only [Nat.cast_mul, Nat.cast_one, mul_one] using Real.exp_nat_mul (1:ℝ) k
            have hpf := Real.pow_div_factorial_le_exp (k : ℝ) (by positivity) k
            rw [hexp] at hpf
            rw [div_le_iff₀ (by positivity : (0:ℝ) < (k.factorial : ℝ))] at hpf
            rw [div_le_iff₀ (by positivity : (0:ℝ) < (Real.exp 1) ^ k)]
            exact hpf.trans_eq (mul_comm _ _)

/-- **The elementary numeric core, final form.** For `b ≥ 0` and `k ≥ 1`,
`(b + (k+3)/2)^{kl} / (k!)^l ≤ (e (1 + b/k))^{kl}`. -/
private lemma key_num (b : ℝ) (hb : 0 ≤ b) (k l : ℕ) (hk : 1 ≤ k) :
    (b + ((k : ℝ) + 3) / 2) ^ (k * l) / ((k.factorial : ℝ)) ^ l
      ≤ (Real.exp 1 * (1 + b / k)) ^ (k * l) := by
  have hkey := key_num_aux b hb k hk
  have hEk : (0:ℝ) < (Real.exp 1 * ((k : ℝ) + b)) ^ k := by positivity
  have hmain : ((b + ((k : ℝ) + 3) / 2) * (k : ℝ)) ^ k
      ≤ ((k.factorial : ℝ)) * (Real.exp 1 * ((k : ℝ) + b)) ^ k := by
    have h := hkey
    rw [div_pow] at h
    rwa [div_le_iff₀ hEk] at h
  have hmain2 : (b + ((k : ℝ) + 3) / 2) ^ k
      ≤ ((Real.exp 1 * (1 + b / k)) ^ k) * ((k.factorial : ℝ)) := by
    have hKk : (0:ℝ) < (k : ℝ) ^ k := by positivity
    have hxe : Real.exp 1 * (1 + b / k) = Real.exp 1 * ((k : ℝ) + b) / (k : ℝ) := by
      field_simp
    rw [hxe, div_pow, mul_pow, div_mul_eq_mul_div, le_div_iff₀ hKk]
    have h1 : (b + ((k : ℝ) + 3) / 2) ^ k * (k : ℝ) ^ k
        = ((b + ((k : ℝ) + 3) / 2) * (k : ℝ)) ^ k := by rw [mul_pow]
    rw [h1]
    calc ((b + ((k : ℝ) + 3) / 2) * (k : ℝ)) ^ k
        ≤ ((k.factorial : ℝ)) * (Real.exp 1 * ((k : ℝ) + b)) ^ k := hmain
      _ = (Real.exp 1) ^ k * ((k : ℝ) + b) ^ k * ((k.factorial : ℝ)) := by
            rw [mul_pow]; ring
  have h2 : (b + ((k : ℝ) + 3) / 2) ^ (k * l)
      ≤ (Real.exp 1 * (1 + b / k)) ^ (k * l) * ((k.factorial : ℝ)) ^ l := by
    have h := pow_le_pow_left₀ (by positivity) hmain2 l
    rw [mul_pow, ← pow_mul, ← pow_mul] at h
    exact h
  rw [div_le_iff₀ (by positivity : (0:ℝ) < ((k.factorial : ℝ)) ^ l)]
  exact h2

/-- BW §12, Yu [33] L1.6: `|Θ(z;k,l,m)| ≤ (e(1 + |z|/k))^{kl}`. (Checked numerically on random `k ≤ 6`, `l ≤ 4`, all `m`.) -/
theorem est_Theta_yu (z : ℂ) (k l m : ℕ) (hk : 1 ≤ k) :
    ‖Theta z k l m‖ ≤ (Real.exp 1 * (1 + ‖z‖ / k)) ^ (k * l) :=
  le_trans (Theta_rho_one_bound z k l m hk) (key_num ‖z‖ (norm_nonneg z) k l hk)

end Work.BW
