import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.norm_Delta_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, fix round 21:05). Your node is `prod_Delta_le`, a new helper (see FIXES_2105.md below). Definitions: Submission.Work.BW.DefsAC. Import proved siblings (est_gamma, …); do not reprove them.

===== FIXES_2105.md =====
# Fixes for two analytic_core split nodes (probes 0927-2105)

**Summary.** Neither node is mis-stated. **Cancel nothing, re-dispatch nothing, change no proved
node.** Add the three helper nodes below as siblings; each is independent of the others.

**Elaboration check.** The helpers are in `bw4/fix/`: `est_gamma_log.lean`, `prod_Delta_le.lean`,
`est_f_ge_half_g.lean`. They were checked on 3.144 against the live workspace:
* scratch file `/tmp/bwfix_2105.lean`, containing `import Mathlib`,
  `import Submission.Work.BW.DefsAC`, `namespace Work.BW`, then the three statements;
* run with `lake env lean` under `systemd-run … MemoryMax=12G`;
* result: **3 `sorry` warnings, no errors.**

## 1. H314 (`est_Pi`): "|γ_M| ≤ 2e^{h+1}D has no plan; `est_gamma` can't be applied"

### Verdict

`est_Pi` is correctly stated and needs **no** bound on `γ·log α`.

**What `est_Pi` bounds.** It bounds `Π(t) = ∏_{m : Fin (r−1)} Δ(γ_{ι m}(λ); t_m)`. The only
input is `|γ_{ι m}(λ)| ≤ e^{h+1}D` for `λ_j ≤ D_j`. That is exactly the **first** conjunct of the
proved `est_gamma` at the same `m : Fin (r−1)`, so it applies directly.

**Proof route.** This is BW p. 39 (the p. 42–43 lines H314 cites belong to (13), not to `est_Pi`):
1. `|Π(t)| ≤ e^{T'}(1 + (r−1)e^{h+1}D/T')^{T'}`, where `T' = Σ_m t_m`.
2. That is `≤ e^{hT'}(1 + e²rD/T')^{T'}`, because `e + e^{h+2}(r−1)D/T' ≤ e^h + e^{h+2}rD/T'`.
3. That is `≤ e^{hT'}(1 + e²rD/T)^T`, since the second factor is monotone in `T'` and `T' ≤ T`.
4. That is `≤ e^{hT'}·1·7^T`, since `T ≥ 11·7rD` and `1 + e²/11·7 = 1·632`.
5. `T' = 0` is trivial.

**No factor 2.** The "2" in H314's `2e^{h+1}D` comes from bounding `|b_kL_{jι}|` and `|b_{ι}L_{jk}|`
separately. Both terms sit in one BH sum `Σ_i |L_{ji}| h'(α_i) ≤ 2^vσ_j`, with `ι m ≠ k`, so there
is no factor 2. `est_gamma`'s proof already does this.

### A genuine interface gap, but for `est21_l` / `est21` / `est22`, not for `est_Pi`

BW's `a(t')` (§17) runs over **all** `n` operators `b_k ∂/∂z_i`, since `ellM_eq_sum_derVec` sums
over `i : Fin n`. It therefore needs `|γ_i(λ) log α_i| ≤ e^{h+1}D` for every `i : Fin n`. The
proved `est_gamma` gives this only for `i = ι m`.

### New helper nodes

* **`est_gamma_log`.** Both bounds for all `i : Fin n`. The proof is identical to `est_gamma`'s;
  for `i = k` the row is `0`.
  * Consumers: `est21_l` (H325's child), and through it `est21` and `est22`.
* **`prod_Delta_le`.** BW §12:
  `∏|Δ(z_m;t_m)| ≤ e^{T'}(1 + Σ|z_m|/T')^{T'}`. This is the one missing analytic step of
  `est_Pi`: each factor is `≤ e^k(1 + |z|/k)^k`, then weighted AM–GM.
  * Consumer: H314. Tell H314 to use `est_gamma.1` plus `prod_Delta_le`, and to drop the `γ_M` plan.
* **`est_f_ge_half_g`.** BW's `|f(s)| > ½|g(s)|` (p. 45) and `|f(s/2)| > ½|g(s/2)|` (p. 46), at
  level `J ≤ I`. This is the shared first step of `est16`, `est18`, `est21` and `est22`.
  * **Margins, integer case.** (14) gives `ln p − (9·2^r − 5)SD`; (15) gives `ln p − (1·007·2^r + 4)SD`.
  * **Margins, half-integer case.** (14) gives `ln p − (9·2^r − 3)SD`; (17) gives `ln p − 6·04·2^r SD`.
  * Both include `kum_J ≤ 2·2SD`.

## Actions

| node | action |
|---|---|
| `est_Pi` (H314) | keep running; message the route above (`est_gamma.1` + `prod_Delta_le`) |
| `est22` (H326) | keep running; message: import `est21_l`, `est17`, `est_f_ge_half_g`; do not derive from `est18` |
| `est21_l` (H325 child) | keep; add `est_gamma_log` as a sibling it may import |
| `est_gamma_log`, `prod_Delta_le`, `est_f_ge_half_g` | dispatch as new leaf nodes |
| proved nodes (`est_gamma`, `num_*`, …) | unchanged |
-/

namespace Work.BW

/-- Weighted AM–GM with natural weights: for nonnegative `x` and natural weights `k` with
nonzero total weight `K = ∑ k`,
`∏ x_i^{k_i} ≤ ((∑ k_i x_i)/K)^K`.

Proved from `Real.geom_mean_le_arith_mean_weighted` (weights `k_i/K`, summing to `1`) by raising
both sides to the `K`-th power. -/
lemma geom_mean_nat_le_arith_mean {ι : Type*} (s : Finset ι) (k : ι → ℕ) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hK : 0 < ∑ i ∈ s, k i) :
    ∏ i ∈ s, x i ^ k i ≤
      ((∑ i ∈ s, (k i : ℝ) * x i) / ((∑ i ∈ s, k i : ℕ) : ℝ)) ^ (∑ i ∈ s, k i) := by
  have hKR : ((∑ i ∈ s, k i : ℕ) : ℝ) = ∑ i ∈ s, (k i : ℝ) := by push_cast; rfl
  have hKpos : (0 : ℝ) < ((∑ i ∈ s, k i : ℕ) : ℝ) := by exact_mod_cast hK
  have hKsum : (0 : ℝ) < ∑ i ∈ s, (k i : ℝ) := by rw [← hKR]; exact hKpos
  have hsumw : ∑ i ∈ s, (k i : ℝ) / ((∑ i ∈ s, k i : ℕ) : ℝ) = 1 := by
    rw [hKR, ← Finset.sum_div]
    exact div_self hKsum.ne'
  have ham := Real.geom_mean_le_arith_mean_weighted s
    (fun i => (k i : ℝ) / ((∑ i ∈ s, k i : ℕ) : ℝ)) x
    (fun i _ => div_nonneg (Nat.cast_nonneg _) hKpos.le) hsumw hx
  have hnn : (0 : ℝ) ≤ ∏ i ∈ s, x i ^ ((k i : ℝ) / ((∑ i ∈ s, k i : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun i hi => Real.rpow_nonneg (hx i hi) _
  have hpow := pow_le_pow_left₀ hnn ham (∑ i ∈ s, k i)
  have hleft : (∏ i ∈ s, x i ^ ((k i : ℝ) / ((∑ i ∈ s, k i : ℕ) : ℝ))) ^ (∑ i ∈ s, k i)
      = ∏ i ∈ s, x i ^ k i := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (hx i hi)]
    rw [div_mul_cancel₀ (k i : ℝ) hKpos.ne']
    rw [Real.rpow_natCast]
  have hright : (∑ i ∈ s, ((k i : ℝ) / ((∑ i ∈ s, k i : ℕ) : ℝ)) * x i) ^ (∑ i ∈ s, k i)
      = ((∑ i ∈ s, (k i : ℝ) * x i) / ((∑ i ∈ s, k i : ℕ) : ℝ)) ^ (∑ i ∈ s, k i) := by
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi; ring
  rw [← hleft, ← hright]
  exact hpow

/-- `(t : ℝ) * (1 + a / t) ≤ t + a` for a natural `t` and `a ≥ 0`. -/
lemma mul_one_add_div_le (t : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (t : ℝ) * (1 + a / (t : ℝ)) ≤ (t : ℝ) + a := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht; simpa using ha
  · have htR : (t : ℝ) ≠ 0 := by positivity
    have hmul : (t : ℝ) * (a / (t : ℝ)) = a := by
      rw [mul_comm, div_mul_cancel₀ a htR]
    rw [mul_add, mul_one, hmul]

/-- BW §12 (p. 37): `|Π(z; t)| = ∏_m |Δ(z_m; t_m)| ≤ e^{T'}(1 + (|z_1|+⋯+|z_q|)/T')^{T'}`, `T' = Σ t_m > 0`. Each factor is `≤ (|z|+k)^k/k! ≤ e^k(1+|z|/k)^k` (`k! ≥ (k/e)^k`); then weighted AM–GM (concavity of `log`). Helper for `est_Pi` (with `|z_m| = |γ_{ι m}| ≤ e^{h+1}D` from the first conjunct of `est_gamma`). -/
theorem prod_Delta_le {q : ℕ} (z : Fin q → ℂ) (t : Fin q → ℕ) (hT : 0 < ∑ m, t m) :
    ‖∏ m, Delta (z m) (t m)‖ ≤
      Real.exp ((∑ m, t m : ℕ) : ℝ) * (1 + (∑ m, ‖z m‖) / ((∑ m, t m : ℕ) : ℝ)) ^ (∑ m, t m) := by
  have hTpos : (0 : ℝ) < ((∑ m, t m : ℕ) : ℝ) := by exact_mod_cast hT
  -- split the exponential factor off each term
  have hexp : ∏ m, Real.exp 1 ^ (t m) = Real.exp ((∑ m, t m : ℕ) : ℝ) := by
    trans ∏ m, Real.exp ((t m : ℕ) : ℝ)
    · apply Finset.prod_congr rfl
      intro m _
      rw [← Real.exp_nat_mul]; simp
    · rw [← Real.exp_sum]
      congr 1
      push_cast
      ring
  have h2 : ∏ m, (Real.exp 1 * (1 + ‖z m‖ / (t m : ℝ))) ^ (t m)
      = Real.exp ((∑ m, t m : ℕ) : ℝ) * ∏ m, (1 + ‖z m‖ / (t m : ℝ)) ^ (t m) := by
    simp only [mul_pow]
    rw [Finset.prod_mul_distrib, hexp]
  -- weighted AM–GM on the remaining factors
  have h3 : ∏ m, (1 + ‖z m‖ / (t m : ℝ)) ^ (t m)
      ≤ (1 + (∑ m, ‖z m‖) / ((∑ m, t m : ℕ) : ℝ)) ^ (∑ m, t m) := by
    have ham := geom_mean_nat_le_arith_mean Finset.univ t (fun m => 1 + ‖z m‖ / (t m : ℝ))
      (fun m _ => by positivity) hT
    have hnum : (∑ m, (t m : ℝ) * (1 + ‖z m‖ / (t m : ℝ)))
        ≤ ((∑ m, t m : ℕ) : ℝ) + ∑ m, ‖z m‖ := by
      calc (∑ m, (t m : ℝ) * (1 + ‖z m‖ / (t m : ℝ)))
          ≤ ∑ m, ((t m : ℝ) + ‖z m‖) :=
            Finset.sum_le_sum (fun m _ => mul_one_add_div_le (t m) (‖z m‖) (norm_nonneg _))
        _ = ((∑ m, t m : ℕ) : ℝ) + ∑ m, ‖z m‖ := by
              rw [Finset.sum_add_distrib]; push_cast; rfl
    calc ∏ m, (1 + ‖z m‖ / (t m : ℝ)) ^ (t m)
        ≤ ((∑ m, (t m : ℝ) * (1 + ‖z m‖ / (t m : ℝ)))
            / ((∑ m, t m : ℕ) : ℝ)) ^ (∑ m, t m) := ham
      _ ≤ ((((∑ m, t m : ℕ) : ℝ) + ∑ m, ‖z m‖)
            / ((∑ m, t m : ℕ) : ℝ)) ^ (∑ m, t m) := by
            apply pow_le_pow_left₀
            · positivity
            · exact div_le_div_of_nonneg_right hnum hTpos.le
      _ = (1 + (∑ m, ‖z m‖) / ((∑ m, t m : ℕ) : ℝ)) ^ (∑ m, t m) := by
            rw [add_div, div_self hTpos.ne']
  calc ‖∏ m, Delta (z m) (t m)‖
      = ∏ m, ‖Delta (z m) (t m)‖ := norm_prod _ _
    _ ≤ ∏ m, (Real.exp 1 * (1 + ‖z m‖ / (t m : ℝ))) ^ (t m) := by
          apply Finset.prod_le_prod₀ (fun m _ => norm_nonneg _)
          intro m _
          exact norm_Delta_le (z m) (t m)
    _ = Real.exp ((∑ m, t m : ℕ) : ℝ) * ∏ m, (1 + ‖z m‖ / (t m : ℝ)) ^ (t m) := h2
    _ ≤ Real.exp ((∑ m, t m : ℕ) : ℝ)
          * (1 + (∑ m, ‖z m‖) / ((∑ m, t m : ℕ) : ℝ)) ^ (∑ m, t m) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le

end Work.BW
