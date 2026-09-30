import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est14
import Submission.Work.BW.est15
import Submission.Work.BW.est17
import Submission.Work.BW.est16_half_arith
import Submission.Work.BW.est_f_ge_half_g_half_arith
import Submission.Work.BW.split_aux
import Submission.Work.BW.num_T
import Submission.Work.BW.num_kum
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, fix round 21:05). Your node is `est_f_ge_half_g`, a new helper (see FIXES_2105.md below). Definitions: Submission.Work.BW.DefsAC. Import proved siblings (est_gamma, …); do not reprove them.

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

## 2. H326 (`est22`): "(22) would not follow from (18) as stated, so it is mis-stated"

### Verdict

`est22` is **correctly stated**. H326's planned route is wrong: (22) is **not** derived from (18)
in BW. The docstring says "from the §17 bound for `f_m(l)` and `est17`".

### The route (BW p. 49–50)

* **Upper bound.** Use the §17 bound
  `log|f_m(l)| ≤ ln p + hT* + (0·282/d + 1·01·2^{-J}|l|/S − 9·2^r)SD`.
  This is **exactly the live node `est21_l`** (H325's child). `est22` should import it rather than
  reprove it. H326's planned `est22_upper` duplicates it.
* **Lower bound.** Use (17) (`est17`):
  `log|g(s/2)| ≥ ln p − 2^r{h(p) + (1 − 1/(2^rd))(dhT* + 0·204SD) + 1·007·2^{-J}|s/2|D + 0·032SD + kum_J}`.
* **Bridge.** Use `|g(s/2)| ≤ 2|f(s/2)|`, the new helper `est_f_ge_half_g`.

### Arithmetic check

Subtract the lower bound from the upper bound and add `log 2`.

**`hT*` terms.** `hT* + (2^r − 1/d)dhT* − hT* = 2^r dhT*`.

**`SD` terms.**
* `0·282/d − 9·2^r + 2^r(0·85 + 0·204 + 0·032) − 0·204/d = −7·914·2^r + 0·078/d`.
* This is `≤ −7·893·2^r − (log 2)/SD` for every `r ≥ 2`, since `0·021·2^r ≥ 0·084 > 0·078`.
* Here `h(p) ≤ 0·85SD` is (12).

**`|l|` term.** `1·01·2^{-J}|l|D = 2^r·1·01·2^{-J}(|l|/2^r)D`.

**`|s|` term.** `2^r·1·007 ≤ 2^r·1·01`.

**`kum_J`.** It carries through unchanged.

So (22) holds exactly as stated.

### New helper node

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

/-- Norm/`exp` glue. If `‖v−w‖ ≤ e^B`, `e^E ≤ ‖w‖` and `2e^B ≤ e^E`, then `‖w‖ ≤ 2‖v‖`:
`‖w‖ ≤ ‖v−w‖ + ‖v‖ ≤ e^B + ‖v‖` while `e^B ≤ e^E/2 ≤ ‖w‖/2`, so `‖w‖/2 ≤ ‖v‖`. This is the
first step of `est16_glue` (`h2`, `h4`), isolated because `est_f_ge_half_g` needs it twice. -/
theorem g_le_two_f {B E : ℝ} {v w : ℂ}
    (h14 : ‖v - w‖ ≤ Real.exp B) (h15 : Real.exp E ≤ ‖w‖)
    (hα : Real.exp B * 2 ≤ Real.exp E) :
    ‖w‖ ≤ 2 * ‖v‖ := by
  have hα' : Real.exp B ≤ Real.exp E / 2 := by linarith
  have hw : ‖w‖ ≤ Real.exp B + ‖v‖ := by
    have h1 : ‖w‖ ≤ ‖w - v‖ + ‖v‖ := by
      calc ‖w‖ = ‖(w - v) + v‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - v‖ + ‖v‖ := norm_add_le _ _
    rw [norm_sub_rev w v] at h1
    linarith
  linarith

/-- BW §15 p. 45 and p. 46 (`|f(s)| > ½|g(s)|` and `|f(s/2)| > ½|g(s/2)|`), at descent level `J ≤ I`: for integer `s` with `2^{-J}|s| ≤ 2^r S`, `|g(s)| ≤ 2|f(s)|`; for `2^{-J}|s| ≤ 4S`, `|g(s/2)| ≤ 2|f(s/2)|`. Trivial if `g = 0`; otherwise `est14` gives `|f − g| ≤ exp(ln p − (9·2^r − 5)SD)` (resp. `− (9·2^r − 3)SD`), while `est15` (resp. `est17`) with (12) and `kum_J ≤ 2·2SD` gives `|g| ≥ exp(ln p − (1·007·2^r + 4)SD)` (resp. `exp(ln p − 6·04·2^r SD)`). Shared step of `est16`, `est18`, `est21`, `est22`. -/
theorem est_f_ge_half_g {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) (μ : Fin r → ℕ) (Tst : ℝ)
    (hTst : Tst ≤ acT K σ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (s : ℤ) :
    (((|s| : ℤ) : ℝ) / 2 ^ J ≤ 2 ^ r * acS K r b v →
        ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ ≤ 2 * ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖) ∧
      (((|s| : ℤ) : ℝ) / 2 ^ J ≤ 4 * acS K r b v →
        ‖acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ ≤
          2 * ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖) := by

  classical
  have hr : 2 ≤ r := H.hr
  have hdNat : 1 ≤ dK K :=
    Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp Module.finrank_pos)
  have hdR : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hdNat
  have h19 : 19 ≤ acH K b v := (acH_lower H).1
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hlog2rd : 0 < Real.log (2 * r * (dK K : ℝ)) := log_2rd_pos hr hdNat
  have hDpos : 0 < acD K σ := pD_pos hr hdNat σ hσ
  have hD0 : 0 ≤ acD K σ := le_of_lt hDpos
  have hSpos : 0 < acS K r b v := by
    have h1 : 0 < pS r (dK K) (acH K b v) := by
      rw [pS]
      have : 0 < acH K b v := by omega
      positivity
    exact_mod_cast h1
  have hTs : (dK K : ℝ) * (acH K b v : ℝ) * Tst ≤ 0.735 * acS K r b v * acD K σ := by
    have h1 := (num_T hr hdNat h19 σ hσ).2.2.1
    have h2 : Tst ≤ (pT r (dK K) σ : ℝ) := hTst
    have h3 : (0 : ℝ) ≤ (dK K : ℝ) * (acH K b v : ℝ) := by positivity
    calc (dK K : ℝ) * (acH K b v : ℝ) * Tst
        ≤ (dK K : ℝ) * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ ≤ 0.735 * acS K r b v * acD K σ := h1
  have hHp : Height.logHeight p ≤ 0.85 * acS K r b v * acD K σ := H.hp12
  have hSD : Real.log 2 ≤ 0.001 * acS K r b v * acD K σ := (num_kum hr hdNat h19 σ hσ J).2.2
  have hkum : kumJ K b v σ J ≤ 2.2 * acS K r b v * acD K σ := by
    rw [kumJ]
    have hJle : (J : ℝ) ≤ 50 * Real.log (2 * r * (dK K : ℝ)) := by
      have h1 : (pI r (dK K) : ℝ) ≤ 50 * Real.log (2 * r * (dK K : ℝ)) := by
        simpa only [pI] using
          Nat.floor_le (show (0 : ℝ) ≤ 50 * Real.log (2 * r * (dK K : ℝ)) by positivity)
      exact le_trans (by exact_mod_cast hJ) h1
    have hSDnn : 0 ≤ acS K r b v * acD K σ := le_of_lt (mul_pos hSpos hDpos)
    calc 0.044 * (J : ℝ) / Real.log (2 * r * (dK K : ℝ)) * acS K r b v * acD K σ
        = (0.044 * (J : ℝ) / Real.log (2 * r * (dK K : ℝ))) *
            (acS K r b v * acD K σ) := by ring
      _ ≤ 2.2 * (acS K r b v * acD K σ) := by
          apply mul_le_mul_of_nonneg_right _ hSDnn
          rw [div_le_iff₀ hlog2rd]
          nlinarith [hJle]
      _ = 2.2 * acS K r b v * acD K σ := by ring
  have hss0 : (0 : ℝ) ≤ ((|s| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg s
  constructor
  · intro hs
    by_cases hg : acg φ α b k L ι v σ p J μ t0 t (s : ℂ) = 0
    · rw [hg, norm_zero]; positivity
    · have h14 := est14 H J hJ μ Tst hTst t0 t ht (s : ℂ)
      have h15 := est15 H J μ Tst hTst t0 t ht s hg
      have hnrm : ‖((s : ℤ) : ℂ)‖ = ((|s| : ℤ) : ℝ) := by simp
      rw [hnrm] at h14
      have harith := est16_half_arith (A := lnp φ p) (h := (acH K b v : ℝ)) (d := (dK K : ℝ))
        (ss := ((|s| : ℤ) : ℝ)) (S := acS K r b v) (D := acD K σ)
        (Tst := Tst) (Hp := Height.logHeight p) (kumJ := kumJ K b v σ J) (r := r) (J := J)
        hr hdR hSpos hD0 hss0 hTs hHp hs hkum hSD
      exact g_le_two_f h14 h15 harith
  · intro hs
    by_cases hg : acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2) = 0
    · rw [hg, norm_zero]; positivity
    · have h14 := est14 H J hJ μ Tst hTst t0 t ht ((s : ℂ) / 2)
      have h17 := est17 H J μ Tst hTst t0 t ht s hg
      have hnrm : ‖((s : ℂ) / 2)‖ = ((|s| : ℤ) : ℝ) / 2 := by
        rw [norm_div]
        have h1 : ‖(s : ℂ)‖ = ((|s| : ℤ) : ℝ) := by simp
        rw [h1]
        norm_num
      rw [hnrm] at h14
      have hss2 : ((|s| : ℤ) : ℝ) / 2 / 2 ^ J ≤ 2 * acS K r b v := by
        have hdd : ((|s| : ℤ) : ℝ) / 2 / 2 ^ J = (((|s| : ℤ) : ℝ) / 2 ^ J) / 2 := by
          rw [div_div, div_div, mul_comm]
        rw [hdd]
        linarith
      have harith := est_f_ge_half_g_half_arith (A := lnp φ p) (h := (acH K b v : ℝ))
        (d := (dK K : ℝ)) (ss := ((|s| : ℤ) : ℝ)) (S := acS K r b v) (D := acD K σ)
        (Tst := Tst) (Hp := Height.logHeight p) (kumJ := kumJ K b v σ J) (r := r) (J := J)
        hr hdR hSpos hD0 hss0 hTs hHp hss2 hkum hSD
      exact g_le_two_f h14 h17 harith


end Work.BW
