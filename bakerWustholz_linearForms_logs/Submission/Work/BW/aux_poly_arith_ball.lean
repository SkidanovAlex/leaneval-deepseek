import Mathlib
import Submission.Work.BW.aux_poly_arith
import Submission.Work.BW.aux_poly_arith_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW phase 5, requests/bw5/ROUTES.md below). Your node is `aux_poly_arith_ball`, part of the Vaaler-FREE Siegel route. It replaces vaalerSection with the inscribed-ellipsoid ball-section bound; the extra loss is d·log(4dN) ≈ 2·10⁻⁷·SD against a real margin of ≈ 0.20·SD in (12). aux_poly's statement is unchanged; its proof switches to siegel_numberField_ball + aux_poly_arith_ball. Import siblings; do not reprove them.

# BW leaves: route decisions for `siegel_numberField` and `ulcm_le_three_pow` (phase 5, 2026-09-28)

**Rules followed.** Everything was read-only. The only Lean runs were scratch
`lake env lean` checks on 3.144 under `MemoryMax=12G`. There was no dispatch and no messaging.

**Sources.**
* BW p. 23 (Lemma 1) and p. 37–45 (§12–15), read from the GDZ scan.
* The live workspace files: `aux_poly`, `aux_poly_arith`, `Mu_ge_Me`, `num_13`, `vaalerSection`
  and its imports, and `ulcm_le_three_pow`.
* The probes from H6 and H362.

**Scripts.** All in the session scratchpad: `mult/auxarith.py` (the (12) recomputation) and
`mult/lcm.py` (Hanson numerics). The checker test harnesses (`Chk.lean`, `Chk2.lean`,
`TestU.lean`, `TestS.lean`) are in `p2/`.

---

## (A) `siegel_numberField`: Vaaler is not needed

### The "0.0003·SD margin" in (12) is an artefact of BW's rounding

BW (p. 41) use `N ≥ 0.99eM`, which gives `M/(N−M) ≤ 0.592`. That comes from
`C(T+r,r) ≤ e^{r−1}(1+T/r)^r`, which throws away a factor `r!/(r^r e^{1−r}) ≈ √(2πr)/e`.

The workspace already proves the sharper bound `3.3·Me ≤ Mu` (`Mu_ge_Me`). With that, the proved
`aux_poly_arith` holds even with the loose coefficient `1.7hT` in place of BW's `1.271hT`.

**Exact evaluation of `aux_poly_arith`'s left side** (`mult/auxarith.py`), taking `σ_j = 1/d`,
which is the worst case:

| r | d | h | ρ = M/(N−M) | LHS / SD | margin to 0.85 SD |
|---|---|---|---|---|---|
| 2 | 1 | 19 | 0.370 | 0.646 | **0.204** |
| 2 | 5 | 19 | 0.369 | 0.646 | 0.204 |
| 3 | 1 | 19 | 0.287 | 0.502 | 0.348 |
| 10 | 1 | 19 | 0.140 | 0.245 | 0.605 |

So (12) has about **0.2·SD** of room, not 0.0003·SD.

### The exact loss of Vaaler-free Siegel lemmas against Bombieri–Vaaler

All heights below are relative to `F`, with `d = [F:ℚ]`. Transporting from `K' = ℚ(α')` to `K`
multiplies by `d/d'`, which turns `d'` into `d`.

* **Ball section (recommended).**
  * **Change.** Keep H6's Bombieri–Vaaler route: Minkowski I on the kernel lattice, the
    `covolumeKernel` duality, and the proved `gramHadamard`. Replace Vaaler's
    `vol(cube ∩ V) ≥ 2^k/√det` by the inscribed ellipsoid, `vol ≥ ω_k/√det`.
  * **Why it costs little.** `λ₁` worsens by the factor `2ω_k^{-1/k} ≤ √(2(k+2)/π) ≤ √(2k)`,
    with `k = d(N−M) ≤ dN`.
  * **Loss:** `(d/2)·log(2dN) ≤ d·log(4dN)`.
* **Box principle with Minkowski I in ideals** (the original "elementary variant").
  * **Change.** Scale row `i` by `c_i ∈ 𝔞_i^{-1}` with `N(c_i𝔞_i) ≤ √|D|` (Minkowski bound). Then
    pigeonhole on the lattice points of `𝒪^N` in a box.
  * **Loss:**
    * `(M/(N−M))·½d·log N`, because the full `log N` replaces the `½ log N`;
    * plus `d log 2` from the differences;
    * plus lattice-point-count error terms.

    The count errors are the Lean pain.
* **Size of either loss inside (12).** In the worst case the new term is
  `d·log(4d·Mu) / SD ≈ 2·10⁻⁷`. As a crude bound, `log N ≤ 0.001hT` (`num_13`) gives
  `≤ 0.00074·SD`. **Either loss fits the 0.2·SD margin by a factor of at least 250.**

**Thunder / Roy–Thunder** give sharper absolute Siegel lemmas, which are not needed here. Their
proofs also use Vaaler-type volume bounds.

**Cheapest route to Vaaler itself**, if someone wants it anyway:
* `vaalerSection` in the workspace has 0 own `sorry` but imports 4 sorried pieces:
  `vaalerPeakedDensity`, `isometricDelta`, `vaalerSliceWeight` and `vaalerFubiniSlice`.
* It can keep running in parallel. **Nothing depends on it any more** if the ball route is taken.

### The ball-route nodes (statements in this directory, elaborated on 3.144: 4 `sorry` warnings, no errors, no clashes)

| node | statement | size (k lines) |
|---|---|---|
| `ballSection` | `ω_k/√det(AᵀA) ≤ vol{x : ‖Ax‖_∞ ≤ 1}`, with `ω_k = π^{k/2}/Γ(k/2+1)` (ellipsoid ⊆ cube section) | 0.5–1.5 |
| `siegel_numberField_ball` | `siegel_numberField` plus `+ d·log(4dN)` | H6's assembly with the Vaaler call swapped (≈ unchanged) |
| `siegel_fintype_ball` | the `Fintype`-indexed form, as `siegel_fintype` | 0.1–0.3 |
| `aux_poly_arith_ball` | `aux_poly_arith` plus `+ d·log(4d·Mu)` on the left | 0.3–0.6 |

**What changes for the dispatched nodes.**
* **`aux_poly` keeps its statement** (`h(p) ≤ 0.85SD`). Its proof switches to the `_ball`
  pair.
* **Nothing downstream changes.**
* **Recommendation.** Dispatch the four `_ball` nodes now, and let H6 re-target its assembly to
  `ballSection`. Keep the Vaaler subtree only as a parallel option.

---

## (B) `ulcm_le_three_pow`: the finite check is cheap in the kernel if done right

### (i) How much slack there is

* **Where the bound is used.** `u(h) = lcm(1..h)` enters only through `Θ`, with `h ≥ 19`.
* **(12).** With the 0.2·SD margin above, (12) would tolerate `log u(h) ≤ c·h` for `c` far above
  `log 3`.
* **(13) is tight.** BW p. 43 budgets `(log u(h) − h)t₀ ≤ 0.1hT`, which is `num_13`'s second
  conjunct. That forces `log u(h) ≤ 1.1h`, so `c ≤ 1.1` (`log 3 = 1.0986`). The `0.203/0.204`
  constants propagate into (15), (16) and §19. A bound like `C·2.9^n` would therefore need
  `log C ≤ 0.67` at `h = 19`.
* **Chebyshev is not enough.** Chebyshev's `ψ(x) < 1.1056x` fails `1.1`.
* **Conclusion.** Re-budgeting (13) would churn dispatched statements. **Keep `3^k`.** The true
  maximum of `ψ(n)/n` is 1.0388, at `n = 113`.

### (ii) Cheapest verified-safe route: keep Hanson for `k ≥ 1024`, and do the finite part with a kernel checker

The heaviness came from how the finite check was done. `decide` over `Finset.lcm` or `norm_num`
over 1000 goals is heavy. A **structurally recursive Boolean checker** whose steps are the
kernel's GMP-accelerated `Nat.ble`, `Nat.lcm` and `Nat.mul`, run with **`decide +kernel`**, is
cheap.
* **This is not `native_decide`.** Axioms: `[propext, Classical.choice, Quot.sound]`.
* **Plain `decide`** hits the elaborator's recursion limit. `+kernel` skips the elaborator
  evaluation.
* **Measured on 3.144**, against the workspace's own `Work.BW.ulcm`:

| file | wall | max RSS |
|---|---|---|
| bare `import Mathlib` | 5.28 s | 6.88 GB |
| + checker for all `k < 4096` | 5.72 s | 6.96 GB |

  **So the checker costs +0.44 s and +77 MB for 4096 cases**, with numbers up to 6500 bits.
* **The complete tested code** is `ulcm_checker_tested.lean`: `ulcmChk`, `ulcm_succ_lcm`,
  `ulcmChk_sound`, `ulcmChk_4096 := by decide +kernel`, and `ulcm_le_three_pow_small`. It is a
  proof, not a stub (0.1k lines).
* **Plug-in.** Replace `ulcm_small` (the `k < 1024` branch) with `ulcm_le_three_pow_small`.
  Because the check now reaches 4096, the analytic Hanson part may start at any `N₀ ≤ 4096`.
* **Hanson's existing crude estimate is already enough above 1024.** It uses
  `log C(n) ≤ log n + log(n+1) + 1 + n·Lw(n)` with `Lw ≤ 1.0826`. (With the sharper
  Stirling/Robbins bounds, the worst-case uniform estimate fails only for `n ∈ [75, 94]`; see
  `mult/lcm.py`. Not needed.)
* **Numerics.** Hanson's `C(n) ≤ 3^n` holds for every `n < 5000`.
* **Same fix for `num_13`.** It only imports `ulcm_le_three_pow`, so it becomes sorry-free once
  that node lands.
-/

namespace Work.BW

/-- `Real.log x ≤ 0.05 * x` for `x ≥ 1600` (from `log x ≤ 2√x` and `√x ≥ 40`). -/
lemma bwLog_le_point05 {x : ℝ} (hx : 1600 ≤ x) : Real.log x ≤ 0.05 * x := by
  have hx0 : 0 < x := by linarith
  have h1 : Real.log x ≤ 2 * Real.sqrt x := by
    have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
    have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hx0.le]; ring
    linarith
  have hs : 40 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    linarith
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hsn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith [hs, hs2, hsn]

/-- The Siegel term of `aux_poly_arith_ball`: `d · log (4 d Mu) ≤ 0.1 r d h D`.

Here `D₀ + 1 ≤ rD` and `D_j + 1 ≤ D` (from `pD0_le`, `pDj_le` of `split_aux`), so that
`Mu ≤ h·(rD)·D^r`, and with `D ≥ 363408 d ≥ 1600` (`D_ge`), `log D ≤ 0.05 D`, `d ≤ D`, we get
`log (4 d Mu) ≤ 3 + 0.05D + h + r + 0.075 rD`, whose `d`-fold is at most `0.1 r d h D`
(`r ≥ 2`, `h ≥ 19`, `D ≥ 1600`).  This is the input that `aux_poly_arith_ball` adds on top of the
`13.4 r d h D` of `aux_poly_arith_core`. -/
lemma log_four_mul_Mu_le {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 2 ≤ r)
    (h : ℕ) (hh : 19 ≤ h) (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (Module.finrank ℚ K : ℝ) ≤ σ j) :
    let d : ℝ := Module.finrank ℚ K
    let D : ℝ := pD r (Module.finrank ℚ K) σ
    let D0 : ℕ := pD0 r (Module.finrank ℚ K) σ
    let Dj : Fin r → ℕ := pDj r (Module.finrank ℚ K) σ
    let Mu : ℕ := h * (D0 + 1) * ∏ j, (Dj j + 1)
    d * Real.log (4 * d * (Mu : ℝ)) ≤ 0.1 * (r : ℝ) * d * (h : ℝ) * D := by
  dsimp only
  have hdn : 1 ≤ Module.finrank ℚ K := by
    have := Module.finrank_pos (R := ℚ) (M := K); omega
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd
  set D : ℝ := pD r (Module.finrank ℚ K) σ with hD
  set Mu : ℕ := h * (pD0 r (Module.finrank ℚ K) σ + 1) *
    ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) with hMu
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hh19 : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hd1 : (1:ℝ) ≤ d := by rw [hd]; exact_mod_cast hdn
  have hd0 : (0:ℝ) < d := by linarith
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hhpos : (0:ℝ) < (h:ℝ) := by linarith
  have hDpos : 0 < D := by rw [hD]; exact pD_pos hr hdn σ hσ
  have hDge : 363408 * d ≤ D := by rw [hd, hD]; exact D_ge hr σ hσ
  have hD1600 : (1600:ℝ) ≤ D := by nlinarith [hDge, hd1]
  have hlogD : Real.log D ≤ 0.05 * D := bwLog_le_point05 hD1600
  have hdD : d ≤ D := by nlinarith [hDge, hd1]
  have hMu_eq : (Mu : ℝ) = (h:ℝ) * ((pD0 r (Module.finrank ℚ K) σ : ℝ) + 1)
      * ∏ j, ((pDj r (Module.finrank ℚ K) σ j : ℝ) + 1) := by
    rw [hMu]; push_cast; ring
  have hD0le : ((pD0 r (Module.finrank ℚ K) σ : ℝ) + 1) ≤ (r:ℝ) * D := by
    have hfl := pD0_le (r := r) (d := Module.finrank ℚ K) hr hdn σ hσ
    rw [← hD] at hfl
    have hL1 : (2:ℝ) ≤ 2 * Real.log (2 * (r:ℝ) * (Module.finrank ℚ K : ℝ)) := by
      have h := log_2rd_ge hr hdn
      linarith
    have h2 : (r:ℝ) * D / (2 * Real.log (2 * (r:ℝ) * (Module.finrank ℚ K : ℝ)))
        ≤ (r:ℝ) * D / 2 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hL1
    have hrD : (2:ℝ) ≤ (r:ℝ) * D := by nlinarith [hr2, hD1600]
    linarith
  have hDjle : ∀ j : Fin r, ((pDj r (Module.finrank ℚ K) σ j : ℝ) + 1) ≤ D := by
    intro j
    have hfl := pDj_le (r := r) (d := Module.finrank ℚ K) hr hdn σ hσ j
    rw [← hD] at hfl
    have hσj : (1:ℝ) ≤ d * σ j := by
      have h2 := hσ j
      rw [div_le_iff₀ hd0] at h2
      linarith
    have hrdσ : (2:ℝ) ≤ (r:ℝ) * d * σ j := by nlinarith [hσj, hr2]
    have h1 : D / ((r:ℝ) * d * σ j) ≤ D / 2 :=
      div_le_div_of_nonneg_left (le_of_lt hDpos) (by norm_num) hrdσ
    have h2 : D / 2 + 1 ≤ D := by linarith
    linarith
  have hpr : ∏ j, ((pDj r (Module.finrank ℚ K) σ j : ℝ) + 1) ≤ D^r := by
    have h1 := prod_le_prod_of_nonneg (s := Finset.univ)
      (f := fun j : Fin r => ((pDj r (Module.finrank ℚ K) σ j : ℝ) + 1))
      (g := fun _ : Fin r => D) (fun j _ => by positivity) (fun j _ => hDjle j)
    simpa [Finset.prod_const, Fintype.card_fin] using h1
  have hprnn : (0:ℝ) ≤ ∏ j, ((pDj r (Module.finrank ℚ K) σ j : ℝ) + 1) :=
    Finset.prod_nonneg (fun j _ => by positivity)
  have hMu_le : (Mu : ℝ) ≤ (h:ℝ) * ((r:ℝ)*D) * D^r := by
    rw [hMu_eq]
    calc (h:ℝ) * ((pD0 r (Module.finrank ℚ K) σ : ℝ) + 1)
          * ∏ j, ((pDj r (Module.finrank ℚ K) σ j : ℝ) + 1)
        = (h:ℝ) * (((pD0 r (Module.finrank ℚ K) σ : ℝ) + 1)
            * ∏ j, ((pDj r (Module.finrank ℚ K) σ j : ℝ) + 1)) := by ring
      _ ≤ (h:ℝ) * (((r:ℝ)*D) * D^r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hD0le hpr hprnn (by positivity)) (le_of_lt hhpos)
      _ = (h:ℝ) * ((r:ℝ)*D) * D^r := by ring
  have h4dMu_le : 4 * d * (Mu:ℝ) ≤ 4 * d * ((h:ℝ) * ((r:ℝ)*D) * D^r) :=
    mul_le_mul_of_nonneg_left hMu_le (by positivity)
  have hpos1 : 0 < 4 * d * (Mu:ℝ) := by positivity
  have hlog_le : Real.log (4 * d * (Mu:ℝ))
      ≤ Real.log (4 * d * ((h:ℝ) * ((r:ℝ)*D) * D^r)) := Real.log_le_log hpos1 h4dMu_le
  have hsplit : Real.log (4 * d * ((h:ℝ) * ((r:ℝ)*D) * D^r))
      = Real.log 4 + Real.log d + Real.log (h:ℝ) + Real.log (r:ℝ)
        + ((r:ℝ)+1) * Real.log D := by
    have e1 : Real.log (4 * d * ((h:ℝ) * ((r:ℝ)*D) * D^r))
        = Real.log (4*d) + Real.log ((h:ℝ) * ((r:ℝ)*D) * D^r) :=
      Real.log_mul (by positivity) (by positivity)
    have e2 : Real.log (4*d) = Real.log 4 + Real.log d :=
      Real.log_mul (by norm_num) (ne_of_gt hd0)
    have e3 : Real.log ((h:ℝ) * ((r:ℝ)*D) * D^r)
        = Real.log ((h:ℝ) * ((r:ℝ)*D)) + Real.log (D^r) :=
      Real.log_mul (by positivity) (by positivity)
    have e4 : Real.log ((h:ℝ) * ((r:ℝ)*D)) = Real.log (h:ℝ) + Real.log ((r:ℝ)*D) :=
      Real.log_mul (ne_of_gt hhpos) (by positivity)
    have e5 : Real.log ((r:ℝ)*D) = Real.log (r:ℝ) + Real.log D :=
      Real.log_mul (ne_of_gt hrpos) (ne_of_gt hDpos)
    have e6 : Real.log (D^r) = (r:ℝ) * Real.log D := Real.log_pow D r
    rw [e1, e2, e3, e4, e5, e6]
    ring
  have hlogMu_le : Real.log (4 * d * (Mu:ℝ))
      ≤ 3 + 0.05 * D + (h:ℝ) + (r:ℝ) + 0.075 * (r:ℝ) * D := by
    have h4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4); linarith
    have hd' : Real.log d ≤ 0.05 * D := le_trans (Real.log_le_log hd0 hdD) hlogD
    have hh' : Real.log (h:ℝ) ≤ (h:ℝ) := by
      have := Real.log_le_sub_one_of_pos hhpos; linarith
    have hr' : Real.log (r:ℝ) ≤ (r:ℝ) := by
      have := Real.log_le_sub_one_of_pos hrpos; linarith
    have hD' : ((r:ℝ) + 1) * Real.log D ≤ 0.075 * (r:ℝ) * D := by
      have h1 : ((r:ℝ) + 1) * Real.log D ≤ ((r:ℝ) + 1) * (0.05 * D) :=
        mul_le_mul_of_nonneg_left hlogD (by linarith)
      nlinarith [h1, hr2, hDpos]
    linarith [hlog_le, hsplit, h4, hd', hh', hr', hD']
  have hrh : (2:ℝ) * 19 ≤ (r:ℝ) * (h:ℝ) := mul_le_mul hr2 hh19 (by norm_num) (by linarith)
  have hrhD : (2:ℝ) * 19 * 1600 ≤ (r:ℝ) * (h:ℝ) * D :=
    mul_le_mul hrh hD1600 (by norm_num) (by positivity)
  have h3d : 3 * d ≤ 0.005 * (r:ℝ) * d * (h:ℝ) * D := by nlinarith [hrhD, hd1]
  have hdD' : 0.05 * d * D ≤ 0.005 * (r:ℝ) * d * (h:ℝ) * D := by nlinarith [hrh, hd1, hDpos]
  have hdh : d * (h:ℝ) ≤ 0.005 * (r:ℝ) * d * (h:ℝ) * D := by nlinarith [hr2, hD1600, hd1]
  have hdr : d * (r:ℝ) ≤ 0.005 * (r:ℝ) * d * (h:ℝ) * D := by nlinarith [hh19, hD1600, hd1]
  have hrD' : 0.075 * (r:ℝ) * d * D ≤ 0.05 * (r:ℝ) * d * (h:ℝ) * D := by
    nlinarith [hh19, hd1, hr2, hDpos]
  calc d * Real.log (4 * d * (Mu:ℝ))
      ≤ d * (3 + 0.05 * D + (h:ℝ) + (r:ℝ) + 0.075 * (r:ℝ) * D) :=
        mul_le_mul_of_nonneg_left hlogMu_le (le_of_lt hd0)
    _ = 3*d + 0.05*d*D + d*(h:ℝ) + d*(r:ℝ) + 0.075*(r:ℝ)*d*D := by ring
    _ ≤ 0.1 * (r:ℝ) * d * (h:ℝ) * D := by linarith [h3d, hdD', hdh, hdr, hrD']


/-- The BW (12) arithmetic of `aux_poly_arith` with the extra Siegel loss `d log(4 d Mu)`
(`d' ≤ d` after transport from `ℚ(α')` to `K`). Recomputed margin: the proved left side is at most
`0.647 SD` (`rho ≤ 0.370` at `r = 2`, falling with `r`), and the new term is below `10⁻⁶ SD`.
Proof: `aux_poly_arith`'s bounds plus `log Mu ≤ 0.001 h T` (`num_13`, fourth conjunct) and
`d log(4d) ≤ 10⁻³ S D`. Size 0.3–0.6k. -/
theorem aux_poly_arith_ball {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 2 ≤ r)
    (h : ℕ) (hh : 19 ≤ h) (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (Module.finrank ℚ K : ℝ) ≤ σ j) :
    let d : ℝ := Module.finrank ℚ K
    let D : ℝ := pD r (Module.finrank ℚ K) σ
    let S : ℕ := pS r (Module.finrank ℚ K) h
    let D0 : ℕ := pD0 r (Module.finrank ℚ K) σ
    let Dj : Fin r → ℕ := pDj r (Module.finrank ℚ K) σ
    let Mu : ℕ := h * (D0 + 1) * ∏ j, (Dj j + 1)
    let Me : ℕ := Fintype.card (AuxEqnIdx r S (pT r (Module.finrank ℚ K) σ))
    let rho : ℝ := (Me : ℝ) / ((Mu : ℝ) - Me)
    (1 / 2) * d * rho * Real.log (Mu : ℝ) + d ^ 2 * ((∑ j, σ j) + (1 / 2) * r * Real.log 2)
      + d * rho * (1.7 * (h : ℝ) * (11.75 * r * D)
          + (D / d) * ((S : ℝ) * (S + 1) / (2 * (S : ℝ) + 1)))
      + d * Real.log (4 * d * (Mu : ℝ))
      ≤ 0.85 * (S : ℝ) * D := by
  dsimp only
  have hcore := aux_poly_arith_core (K := K) hr h hh σ hσ
  dsimp only at hcore
  have hT4 := log_four_mul_Mu_le (K := K) hr h hh σ hσ
  dsimp only at hT4
  have hS : (pS r (Module.finrank ℚ K) h : ℝ) = 16 * (r:ℝ) * (Module.finrank ℚ K : ℝ) * (h:ℝ) := by
    simp only [pS]; push_cast; ring
  have hgoal : 0.85 * (pS r (Module.finrank ℚ K) h : ℝ) * pD r (Module.finrank ℚ K) σ
      = 13.6 * (r:ℝ) * (Module.finrank ℚ K : ℝ) * (h:ℝ) * pD r (Module.finrank ℚ K) σ := by
    rw [hS]; ring
  rw [hgoal]
  have hdn : 1 ≤ Module.finrank ℚ K := by
    have := Module.finrank_pos (R := ℚ) (M := K); omega
  have hR : (0:ℝ) ≤ (r:ℝ) * (Module.finrank ℚ K : ℝ) * (h:ℝ) * pD r (Module.finrank ℚ K) σ := by
    have h := pD_pos hr hdn σ hσ
    positivity
  linarith [hcore, hT4, hR]

end Work.BW
