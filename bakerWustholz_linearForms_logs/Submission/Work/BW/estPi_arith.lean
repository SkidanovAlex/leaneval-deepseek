import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Finite-sum bound: if `q ≤ r - 1` and every `x m ≤ C` with `C ≥ 0`, then
`∑ m, x m ≤ (r - 1) * C`. -/
private lemma sum_le_of_bound {q r : ℕ} {C : ℝ} (hC : 0 ≤ C) (hq : q ≤ r - 1)
    (x : Fin q → ℝ) (hx : ∀ m, x m ≤ C) :
    ∑ m, x m ≤ ((r - 1 : ℕ) : ℝ) * C := by
  calc ∑ m, x m ≤ ∑ _m : Fin q, C := Finset.sum_le_sum (fun m _ => hx m)
    _ = (q : ℝ) * C := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ((r - 1 : ℕ) : ℝ) * C := by
        apply mul_le_mul_of_nonneg_right _ hC
        exact_mod_cast hq

/-- Arithmetic core of `est_Pi` (BW §13): for `h ≥ 3`, `s ≥ 1`, `u ≥ 0` with
`u ≤ s · e^{h+1}/11.7`, one has `log (1 + u) ≤ (h - 1) + s · log 1.7`.

Route (as in the doc comment of `estPi_arith`): split at `u = 3`.
* `u ≤ 3`: `log (1+u) ≤ log 4 = 2 log 2 ≤ 2 ≤ (h-1) + s log 1.7`.
* `u > 3`: `log (1+u) ≤ log u + 1/u ≤ log u + 1/3 ≤ log s + h + 1 - log 11.7 + 1/3`,
  and the tangent line `log s ≤ s log 1.7 - 1 - log(log 1.7)` reduces the claim to
  `log(log 1.7) + log 11.7 ≥ 4/3`, which follows from `log 1.7 ≥ 7/17`,
  `log 11.7 · log 1.7 ≥ 4` and `log 2 ≥ 2/3`. -/
private lemma estPi_core {h : ℕ} {s u : ℝ} (hh : 3 ≤ h) (hs : 1 ≤ s) (hu : 0 ≤ u)
    (hub : u ≤ s * Real.exp ((h:ℝ) + 1) / 11.7) :
    Real.log (1 + u) ≤ ((h:ℝ) - 1) + s * Real.log 1.7 := by
  have hc_pos : 0 < Real.log 1.7 := Real.log_pos (by norm_num)
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hlog2 : (2:ℝ)/3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hcl : (7:ℝ)/17 ≤ Real.log 1.7 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < (1.7:ℝ) by norm_num)
    norm_num at h
    linarith
  have hprod : (4:ℝ) ≤ Real.log 1.7 * 11.7 := by nlinarith [hcl]
  have h43 : (4:ℝ)/3 ≤ Real.log (Real.log 1.7) + Real.log 11.7 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    have h5 : (4:ℝ)/3 ≤ Real.log 4 := by rw [h4]; linarith
    have h6 : Real.log 4 ≤ Real.log (Real.log 1.7) + Real.log 11.7 := by
      rw [← Real.log_mul (ne_of_gt hc_pos) (by norm_num : (11.7:ℝ) ≠ 0)]
      apply Real.log_le_log (by norm_num)
      linarith [hprod]
    linarith
  have hlog4le : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    push_cast; linarith
  rcases lt_or_ge u 3 with hu3 | hu3
  · have h1 : Real.log (1 + u) ≤ Real.log 4 := Real.log_le_log (by linarith) (by linarith)
    have h3 : (3:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
    have h4 : 0 ≤ s * Real.log 1.7 := mul_nonneg hs_pos.le hc_pos.le
    linarith
  · have hu_pos : 0 < u := by linarith
    have h1 : Real.log (1+u) ≤ Real.log u + 1/u := by
      have h1a : Real.log (1+u) = Real.log u + Real.log (1 + 1/u) := by
        rw [← Real.log_mul (ne_of_gt hu_pos) (by positivity)]
        congr 1; field_simp; ring
      rw [h1a]
      have h1b := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/u by positivity)
      linarith
    have h2 : 1/u ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) hu3
    have h3 : Real.log u ≤ Real.log (s * Real.exp ((h:ℝ)+1) / 11.7) := Real.log_le_log hu_pos hub
    have h4 : Real.log (s * Real.exp ((h:ℝ)+1) / 11.7)
        = Real.log s + ((h:ℝ)+1) - Real.log 11.7 := by
      rw [Real.log_div (by positivity) (by norm_num),
        Real.log_mul (ne_of_gt hs_pos) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    have h5 : Real.log s ≤ s * Real.log 1.7 - 1 - Real.log (Real.log 1.7) := by
      have hsc : 0 < s * Real.log 1.7 := mul_pos hs_pos hc_pos
      have h5a := Real.log_le_sub_one_of_pos hsc
      have h5b : Real.log (s * Real.log 1.7) = Real.log s + Real.log (Real.log 1.7) :=
        Real.log_mul (ne_of_gt hs_pos) (ne_of_gt hc_pos)
      linarith
    linarith

/-- Power/exponential assembly: `log (1+u) ≤ (h-1) + (T/N) log 1.7` for `N > 0`, `u ≥ 0`
gives `e^N (1+u)^N ≤ e^{hN} · 1.7^T`. -/
private lemma pow_exp_assemble {h : ℕ} {T : ℝ} {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu : 0 ≤ u)
    (hlog : Real.log (1 + u) ≤ ((h : ℝ) - 1) + (T / (N : ℝ)) * Real.log 1.7) :
    Real.exp (N : ℝ) * (1 + u) ^ N ≤ Real.exp ((h : ℝ) * (N : ℝ)) * 1.7 ^ T := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h1u : 0 < 1 + u := by linarith
  set Y : ℝ := ((h:ℝ)-1) + (T/(N:ℝ)) * Real.log 1.7 with hY
  have hexp : 1 + u ≤ Real.exp Y := (Real.log_le_iff_le_exp h1u).mp hlog
  have hpow : (1 + u)^N ≤ Real.exp (N * Y) := by
    calc (1 + u)^N ≤ (Real.exp Y)^N := pow_le_pow_left₀ (by linarith) hexp N
      _ = Real.exp ((N:ℝ) * Y) := by rw [Real.exp_nat_mul]
  have hYN : (N:ℝ) * Y = (N:ℝ)*((h:ℝ)-1) + T * Real.log 1.7 := by
    rw [hY]; field_simp
  have hexpN : Real.exp (N:ℝ) * Real.exp ((N:ℝ)*Y)
      = Real.exp ((h:ℝ)*(N:ℝ)) * 1.7 ^ T := by
    rw [← Real.exp_add, hYN, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1.7),
      ← Real.exp_add]
    congr 1; ring
  calc Real.exp (N:ℝ) * (1+u)^N
      ≤ Real.exp (N:ℝ) * Real.exp ((N:ℝ)*Y) := by
        apply mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp ((h:ℝ)*(N:ℝ)) * 1.7 ^ T := hexpN

/-- **Arithmetic core of `est_Pi` (BW §13).** Let `ι = Fin q` with `q ≤ r-1`, `x m ≥ 0` with
`x m ≤ e^{h+1}·D`, `T' = ∑ m, t m ≤ T`, and `11.7·r·D ≤ T`, `h ≥ 3`, `r ≥ 2`, `D ≥ 1`. Then
`e^{T'} (1 + (∑ m, x m)/T')^{T'} ≤ e^{h T'} · 1.7^T`.

Route. Put `S := ∑ m, x m ≤ q·e^{h+1}D ≤ (r-1)e^{h+1}D` and `s := T/T'` (the case `T' = 0` is
trivial since `1.7^T ≥ 1`). Divide by `T'`: enough to prove
`log(1+u) ≤ h-1+s·log 1.7` where `u = S/T' ≤ s·e^{h+1}(r-1)/(11.7r) ≤ s·e^{h+1}/11.7`.
Split on `u`: if `u ≤ 4` use `log(1+u) ≤ log 5 ≤ h-1` (`h ≥ 3`).
If `u ≥ 4` use `log(1+u) ≤ log u + 1/u ≤ (h+1+log(s/11.7)) + 1/4` and reduce to
`log s ≤ s·log 1.7 + 0.13`; the tangent bound `log s ≤ s·log 1.7 - 1 - log(log 1.7)`
(at `s = 1/log 1.7`, from the concavity inequality `Real.log_le_sub_one_of_pos` applied to `s·log 1.7`)
plus any lower bound `log 1.7 ≥ 0.41` (`Real.one_sub_inv_le_log_of_pos` on `17/10`) finishes it.
Numerical margin of the final inequality is `≥ 0.71` for `h ≥ 3` (checked over `s ≥ 1`). -/
lemma estPi_arith {h r : ℕ} {D T : ℝ} {q : ℕ} (x : Fin q → ℝ) (t : Fin q → ℕ)
    (hr : 2 ≤ r) (hh : 3 ≤ h) (hD : 1 ≤ D) (hq : q ≤ r - 1)
    (hx0 : ∀ m, 0 ≤ x m) (hx : ∀ m, x m ≤ Real.exp ((h : ℝ) + 1) * D)
    (hT : 11.7 * (r : ℝ) * D ≤ T) (ht : ((∑ m, t m : ℕ) : ℝ) ≤ T) :
    Real.exp ((∑ m, t m : ℕ) : ℝ) * (1 + (∑ m, x m) / ((∑ m, t m : ℕ) : ℝ)) ^ (∑ m, t m) ≤
      Real.exp ((h : ℝ) * ((∑ m, t m : ℕ) : ℝ)) * 1.7 ^ T := by
  set N : ℕ := ∑ m, t m with hN
  set S : ℝ := ∑ m, x m with hS
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hTpos : 0 < T := by
    have : 0 < 11.7 * (r:ℝ) * D := by positivity
    linarith
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg (fun m _ => hx0 m)
  have hSle : S ≤ ((r - 1 : ℕ) : ℝ) * (Real.exp ((h:ℝ)+1) * D) := by
    rw [hS]
    exact sum_le_of_bound (mul_nonneg (Real.exp_pos _).le hDpos.le) hq x hx
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · rw [hN0]
    have h := Real.one_le_rpow (show (1:ℝ) ≤ 1.7 by norm_num) hTpos.le
    simpa using h
  · have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
    have hs : 1 ≤ T / (N:ℝ) := by rw [le_div_iff₀ hNR]; simpa using ht
    have hu : 0 ≤ S / (N:ℝ) := div_nonneg hS0 hNR.le
    have hEpos : 0 < Real.exp ((h:ℝ)+1) := Real.exp_pos _
    have hStop : S ≤ T * Real.exp ((h:ℝ)+1) / 11.7 := by
      have hr1 : ((r-1:ℕ):ℝ) ≤ (r:ℝ) := by exact_mod_cast Nat.sub_le r 1
      have hDle : ((r-1:ℕ):ℝ) * D ≤ T / 11.7 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 11.7)]
        calc ((r-1:ℕ):ℝ) * D * 11.7 = 11.7 * ((r-1:ℕ):ℝ) * D := by ring
          _ ≤ 11.7 * (r:ℝ) * D := by
              apply mul_le_mul_of_nonneg_right _ hDpos.le
              exact mul_le_mul_of_nonneg_left hr1 (by norm_num)
          _ ≤ T := hT
      calc S ≤ ((r-1:ℕ):ℝ) * (Real.exp ((h:ℝ)+1) * D) := hSle
        _ = (((r-1:ℕ):ℝ) * D) * Real.exp ((h:ℝ)+1) := by ring
        _ ≤ (T / 11.7) * Real.exp ((h:ℝ)+1) := mul_le_mul_of_nonneg_right hDle hEpos.le
        _ = T * Real.exp ((h:ℝ)+1) / 11.7 := by ring
    have hub : S / (N:ℝ) ≤ (T / (N:ℝ)) * Real.exp ((h:ℝ)+1) / 11.7 := by
      rw [div_le_iff₀ hNR]
      have heq : (T / (N:ℝ)) * Real.exp ((h:ℝ)+1) / 11.7 * (N:ℝ)
          = T * Real.exp ((h:ℝ)+1) / 11.7 := by
        field_simp
      rw [heq]
      exact hStop
    have hcore := estPi_core (h := h) (s := T/(N:ℝ)) (u := S/(N:ℝ)) hh hs hu hub
    exact pow_exp_assemble hNpos hu hcore

end Work.BW
