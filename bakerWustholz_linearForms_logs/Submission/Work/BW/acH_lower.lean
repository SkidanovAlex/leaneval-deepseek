import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.bw_arith_standing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `acH_lower`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

===== SPLIT_analytic_core.md =====
# Split of `analytic_core` (BW §14–20) — 2026-09-27

**Source.** BW, Crelle 442 (1993), pp. 41–59, read from the GDZ scan. The page images are in
this session's scratchpad (`bwpng/p22..p41.png`, OCR in `bwocr/`). In BW's typography the `·`
in `7·2S'`, `9·274`, `5·6S` is a decimal point. For example `R = 7.2 S'`, not `7·2S'`.

**Files.** Everything is in `bw4/split/`:
* `DefsAC.lean`: definitions only, no `sorry`. Install it as `Submission/Work/BW/DefsAC.lean`,
  importing `Submission.Work.BW.analytic_core`, inside `namespace Work.BW`.
* 52 node files, one statement each, each ending `:= by sorry`. They have no import or namespace
  lines. The doc comments carry BW's reference, the proof route and the siblings to reuse.
* `ORDER.txt`: a dependency-respecting order for the node files.

**Elaboration check.** The check was run on 3.144 against the live workspace.
* The scratch file contained, in order:
  * `import Mathlib`;
  * imports of `Submission.Work.BW.{analytic_core, kummer_indep, parity_decomposition, applyDer_Qpoly_span}`;
  * `namespace Work.BW`;
  * `DefsAC`;
  * all 52 nodes.
* Command: `systemd-run --user --scope -q -p MemoryMax=12G … lake env lean`.
* Result: **52 `sorry` warnings, 0 errors.** Nothing in the workspace was touched.

**`analytic_core` itself is unchanged.** `analytic_core_assembly` is the same statement with the
hypotheses bundled as `ACHyp`. The dispatched `analytic_core` is proved from it by `⟨…⟩`.

## 0. Two things BW get wrong in §19–20. Both are fixed in the split.

### (A) The level-J descent estimates fail when `T^{(J)}` is small

**BW's claim** (p. 58): "the extrapolation procedure in §19 goes through without essential change
taking `S^{(J)}` and `T^{(J)}` in place of `S` and `T`", for all `J ≤ I* = 50 log(2rd)`.

**Where it breaks.** The ℐ-bounds contain `S'(T'+1)`. BW replace this by `S'T'` at J = 0, where
`T'` is huge. At level J:
* the `+1` contributes `S' ≈ 2^j ξ^{-rJ} S`;
* this term does not scale with `ST`;
* so it beats the saving `−9·2^r SD` once `ξ^{-rJ} ≳ D`, i.e. once `T^{(J)} = ξ^{rJ}T` has dropped
  to about `r`.

**Concrete case.** At `r = 2`, `d = 1`, `σ = 1` (so `D = 3.6·10⁵`), the half-step ℐ-condition
becomes positive for `J ≥ 23`. This holds in `num.py`/`num2.py` (scratchpad). BW's `I* = 69`.

**The fix.** In that regime the Y-degrees are already 0:
* `D_j < 2^J` for all `j` happens by `J = 18` in the example;
* in general, `2^J ≤ D_j ≤ D/r` implies `ξ^{-rJ}/D ≤ (2ξ^r)^{-J}/r`.

So the split runs each round under the non-degeneracy hypothesis `hnd : ∃ j, 2^J ≤ D_j`. All
§19/§20 numerics are verified with the extra term `q = ξ^{-rJ}/D ≤ min((2ξ^r)^{-J}/r, ξ^{-rJ}/D_min)`.

The degenerate levels are closed by `yfree_contradiction`:
* `Q^{(J)}` is a polynomial in `Y₀` alone of degree `≤ h(D₀+1)`;
* it has `≥ 2⌊2S^{(J)}⌋+1` zeros, each of multiplicity `> ξT^{(J)}`;
* since `S^{(J)}T^{(J)} = ST`, the count exceeds `h(D₀+1)`, so `Q^{(J)} = 0`.

**Consequences.**
* `analytic_core` stays TRUE, and needs no case split in its statement. The assembly inducts on
  J and stops at the first Y-free level.
* This **corrects §2 of `ADJUDICATE_analytic_core.md`**. There I wrote that "no step of §14–20
  uses `D_j ≥ 2^J`". That is false for the literal estimates. The verdict stands, but through
  `yfree_contradiction`, not through running BW's §20 unchanged to `J = I`.

### (B) Small constant slips, corrected in the node statements

| BW | problem | node value |
|---|---|---|
| `log((2S'+1)(S'(2e)^{S'})^{2(T'+1)}) ≤ 3·41 S'(T'+1)` | 3·419 at `S' = 608`, `T' = 0` | 3·42 |
| same with `2·03` (p. 55, 58) | 2·033 at `T' = 0` | 2·04 |

These change the ℐ coefficients downstream:
* 3·412 becomes 3·422;
* the half-step 1·02 becomes 1·021, and its target −0·125 becomes −0·12 (the worst case is
  −0·1215);
* the even-step 2·032 becomes 2·042.

**The 2-adic term.** BW write `2hJ(D₀+1) log 2`. The true contribution is `2dJh(D₀+1) log 2`:
Tijdeman's `q^{2kl}` summed over `v | 2`, which gives `d log 2`. This is `≤ 0·985 · {0·044J/log(2rd)}SD`.
So `kumJ` is defined as BW's right-hand side, which is a valid bound (`num_kum`).

**Everything else is checked.** All other decimals (0·204, 0·205, 1·055, 1·087, 0·226/0·255/0·282,
1·133, −7·893, 16·13, 24·86, 9·274, 6·732, 12·43, 5·368, 0·535, 0·732, 1·87, 1·07, `aI + b^{-I} ≤ 1`)
were re-derived and checked numerically:
* over `r ≤ 1000`, `d ≤ 10⁶` and all `J ≤ I*`;
* each `num*` doc comment states its worst margin.

## 1. Nodes

Sizes are k lines. "Reuse" names H3's proved helpers or siblings.

### Algebra, no analysis

| node | BW | size | reuse / deps |
|---|---|---|---|
| `Qdesc_zero` | def | 0.1 | `Qpoly` |
| `Qval_eq_fAt` | (9) for `s ∈ ℤ` | 0.2 | `Qval_eq_eval_Qpoly` (`s ≥ 0`) |
| `Qdesc_half_split` | (28) on the curve | 0.6–1 | `parity_decomposition` bookkeeping (`hw`, `epsv`, `sum_id`) |
| `Qdesc_parity_ne_zero` | p. 56 choice of ε | 0.3 | `parity_decomposition` |
| `Qdesc_val_mem` | `g(s) ∈ K` | 0.3–0.5 | `eval_prod_X_succ`, `eval_aeval_Y0` |
| `applyDer_Qdesc_span` | L6/L7 at level J, general `t''` | 0.8–1.5 | `applyDer_Qpoly_span`, `Delta_pow_expansion`, `eulerDer_*`, `Qbase` |
| `Qdesc_degreeOf` | `𝒟_j = 2^{-J}D_j` | 0.2 | `Qpoly_degreeOf` (`aeval_degreeOf_le`, `hasseDeriv_deltaPoly_natDegree_le`) |
| `Qpoly_ne_zero` | §12 end, Baker Ch.3 L2 | 1–2 | — |
| `tijdeman_rat` | §12 `q^{2kl}u^mΘ ∈ ℤ` | 0.5–1 | `tijdeman_int` (`q = 1`) |
| `iteratedDeriv_fAt` | §17 chain rule | 0.3–0.5 | — |
| `ellM_eq_sum_derVec` | §17 `a(t')` | 0.1 | — |
| `derVec_mem_span_iota` | §16 first step | 0.3–0.5 | — |

### Parameter facts and decimals

All are pure real arithmetic.

| node | content | size |
|---|---|---|
| `acH_lower` | `h ≥ 19`, `h ≥ 5n`, from `Standing` | 0.5–1 |
| `sigma_ge` | `σ_j ≥ 1/d` | 0.05 |
| `num_D_lower` | `D ≥ 2r^r32^{r+1}d log 2rd`, `D_j ≤ D/r` | 0.2 |
| `num_T` | 6·297, 6·3, 0·735, `S ≥ 608` | 0.3 |
| `num_xi` | 1·87, 0·535, 0·732, `e^{-0·536}`, 1·07 | 0.3–0.5 |
| `ulcm_le_three_pow` | `u(k) ≤ 3^k` (Hanson; shared with `aux_poly`) | 1.5–3 |
| `num_13` | 0·028, 0·1, `μ = 57rd` (0·108/0·007), (11) 0·001 | 0.5–1 |
| `num_kum` | 0·032, 0·044, `log 2 ≤ 0·001SD` | 0.3 |
| `num_17` | 0·06, 0·027 | 0.3 |
| `num20_aJb` | `aJ + b^{-J} ≤ 1` | 0.3 |
| `num19_int` | 𝒥 −0·05, ℐ −2·2·2^r (level J, `q`) | 0.5–1 |
| `num19_half` | −0·105, −0·12 | 0.5 |
| `num20_even` | −3, −4·2^r | 0.4 |
| `num_blaschke_eta` | 0·002, 3·42, 2·04, 16·13, 24·86 | 0.3 |

### Estimates

All are at descent level J, with `|z|, |s|, |l|` scaled by `2^{-J}` and the Kummer term `kumJ`.

| node | BW | size | deps |
|---|---|---|---|
| `est_gamma` | §13, §17 `|γ| ≤ e^{h+1}D` | 0.4 | — |
| `est_Pi` | §13 `|Π| ≤ e^{hT'}1·7^T` | 0.5 | `est_gamma` |
| `est_Theta_yu` | Yu L1.6 | 0.5–1 | — |
| `est13` | (13) | 1–1.5 | `est_Pi`, `est_Theta_yu`, `num_13`, `ulcm_le_three_pow` |
| `est14` | (14) | 0.5–0.8 | `est13` |
| `est15` | (15), product formula over K | 1.5–3 | `Qdesc_val_mem`, `tijdeman_rat`, `LiouvilleAux/product_formula_isolate`, `num_kum` |
| `est16` | (16) | 0.4 | 13, 14, 15 |
| `est17` | (17), half points | 1–2 | as `est15`; `kummer_indep` |
| `est18` | (18) | 0.4 | 13, 14, 17 |
| `est21` | (21) via §17 | 1.5–2.5 | `iteratedDeriv_fAt`, `ellM_eq_sum_derVec`, `derVec_mem_span_iota`, `applyDer_Qdesc_span`, `num_17`, 15 |
| `est22` | (22) | 0.4 | §17 bound, 17 |

**Hint for `est17`.** Avoid building `K'`. Take the norm `∏_{sign choices}(Σ_ε (±ρ)^ε φ(a_ε)) ∈ φ(K)`:
* its `2^r` conjugates obey the same archimedean bounds;
* apply the K-Liouville bound of `est15` to it;
* `kummer_indep` guarantees that the norm is nonzero.

### Complex analysis, generic

| node | BW | size |
|---|---|---|
| `bprod_circle` | `|B| = 1` on `|z| = R` | 0.2 |
| `bprod_real_le` | (23), lacunary (23') | 0.4 |
| `bprod_ratio24` | (24), Stirling | 0.8–1.2 |
| `bprod_ratio25` | (25) | 0.6 |
| `cauchy_blaschke27` | (27) residues + Taylor | 1.5–3 |
| `extrap_core` | the 𝒥/ℐ contradiction, abstract | 0.5–0.8 |

### Analytic steps and assembly

| node | BW | size | deps |
|---|---|---|---|
| `extrap_int_step` | §19 `j → j+1` at level J | 1–1.5 | `extrap_core`, `est16`, `est21`, `bprod_*`, `num19_int`, `num20_aJb`, `num_blaschke_eta`, `num_T`, `num_D_lower` |
| `extrap_half_step` | §19 half-integers | 1–1.5 | `extrap_core`, `est18`, `est22`, `num19_half` |
| `kummer_odd_step` | (29), odd `s` | 0.4–0.6 | `Qdesc_half_split`, `Qdesc_val_mem`, `kummer_indep` |
| `extrap_even_step` | p. 57–58, lacunary `B'` | 1–1.5 | `extrap_core`, `est16`, `est21` at level J+1, `bprod_ratio25`, `num20_even` |
| `descent_round` | one round J → J+1 | 0.3 | the four steps above, `Qdesc_parity_ne_zero`, `num_xi` |
| `descent_base` | J = 0 | 0.2 | `Qval_eq_fAt`, `Qdesc_zero`, `Qpoly_ne_zero`, `extrap_int_step` (pattern of `Qpoly_vanishing_of_hp9`) |
| `yfree_contradiction` | degenerate levels (see §0) | 0.4–0.6 | `Qdesc_degreeOf`, `applyDer_Qdesc_span`; extends `mvpoly_eq_zero_of_ptS_vanishing` / `obstruction_aux` to multiplicities |
| `polyOut_of_inv` | §21 input | 0.3 | `Qdesc_degreeOf`, `applyDer_Qdesc_span` |
| `analytic_core_assembly` | induction on J | 0.2 | base, round, yfree, `polyOut_of_inv` |

**Total ≈ 25–45k lines, central ≈ 32k.** The original estimate was 10–20k. The difference is the
explicit numerics and the Blaschke/residue machinery.

## 2. Order (waves)

**Wave 1, parallel, all leaves.**
* Every `num_*`, `num19_*` and `num20_*` node.
* `acH_lower`, `sigma_ge`, `ulcm_le_three_pow`, `tijdeman_rat`, `Qpoly_ne_zero`.
* `Qdesc_zero`, `Qval_eq_fAt`, `Qdesc_half_split`, `Qdesc_parity_ne_zero`, `Qdesc_val_mem`,
  `Qdesc_degreeOf`, `applyDer_Qdesc_span`.
* `iteratedDeriv_fAt`, `ellM_eq_sum_derVec`, `derVec_mem_span_iota`.
* `est_gamma`, `est_Theta_yu`.
* All `bprod_*`, `cauchy_blaschke27`.

**Wave 2.**
* `est_Pi`, then `est13` and `est14`, then `est15` and `est17`.
* `extrap_core`, which needs `cauchy_blaschke27` and `bprod_circle`.
* `kummer_odd_step`, `yfree_contradiction`, `polyOut_of_inv`.

**Wave 3.** `est16`, `est18`, `est21`, `est22`.

**Wave 4.** `extrap_int_step`, `extrap_half_step`, `extrap_even_step`.

**Wave 5.** `descent_base`, `descent_round`, `analytic_core_assembly`.

**Critical path:** `cauchy_blaschke27` → `extrap_core` → the steps, in parallel with
`est15`/`est17` → `est21` → the steps.

## 3. Notes for the owner (H3)

* **Nothing proved is wasted.**
  * `Qpoly`, `Qval_eq_eval_Qpoly`, `Qpoly_vanishing_of_hp9` and `Qpoly_degreeOf` feed
    `Qdesc_zero`, `Qval_eq_fAt`, `descent_base` and `Qdesc_degreeOf`.
  * `parity_decomposition` feeds `Qdesc_half_split` and `Qdesc_parity_ne_zero`.
  * `applyDer_Qpoly_span` and `Delta_pow_expansion` are the template for `applyDer_Qdesc_span`.
  * `mvpoly_eq_zero_of_ptS_vanishing` is the template for `yfree_contradiction`.
  * `not_polyOut_of_small_degrees` is no longer needed. It remains a correct lemma.
* **Glue in the step nodes.**
  * `S' = ⌊2^j S^{(J)}⌋` and `T' = ⌊(1−ξ)ξ^j T^{(J)}⌋` are floors. The numerics have slack of at
    least 0·05 S'D for this.
  * `R = 7·2 S'`. For the 𝒥-parts, `δ = R − |s| ≥ 5·19 S'`. For the ℐ-parts, `η = 1/3` and
    `κ = 1`, or `κ = ½` at half-integers.
* **Hypotheses the estimates need.** `hJ : J ≤ pI` (the Kummer term `≤ 2·2 SD`) and the order
  bounds `T* ≤ T`.
-/
namespace Work.BW

/-! ### Numerical lemmas

Write `C(n,d) = 18 (n+1)! n^{n+1} (32d)^{n+2} log(2nd)` and
`X(n,d) = log C(n,d) − n log d − log(n+d)` (`Work.BW.Xbw`).  Expanding the logarithm
(`Xbw_expansion`) gives, for `n, d ≥ 1`,

`X(n,d) = log 18 + log((n+1)!) + (n+1) log n + (n+2) log 32 + 2 log d + log log(2nd) − log(n+d)`.
Since `n + d ≤ 2nd` and `log log(2nd) ≥ 0` this yields the basic lower bound
`X(n,d) ≥ log 9 + log((n+1)!) + n log n + (n+2) log 32`, from which `X(n,d) ≥ 19` and `X(n,d) ≥ 5n`
follow by elementary estimates on `log 2, log 6, log 9, log 32` (using `e < 2.72`).  The minimum is
`X(2,1) ≈ 19.85`, so the constant `19` is nearly sharp; the constant `5n` has slack `≈ 9.85`.
-/

/-- `Real.exp k ≤ M` from `2.72 ^ k ≤ M` (using `Real.exp 1 < 2.7182818286 < 2.72`). -/
private lemma expNat_le_of_pow_le {k : ℕ} {M : ℝ} (h : (2.72 : ℝ) ^ k ≤ M) :
    Real.exp (k : ℝ) ≤ M := by
  calc Real.exp (k : ℝ) = (Real.exp 1) ^ k := by rw [Real.exp_one_pow]
    _ ≤ (2.72 : ℝ) ^ k :=
        pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1))
          (by linarith [Real.exp_one_lt_d9]) k
    _ ≤ M := h

/-- `K ≤ log M` from `Real.exp K ≤ M`. -/
private lemma le_log_of_exp_le {K M : ℝ} (hM : 0 < M) (h : Real.exp K ≤ M) :
    K ≤ Real.log M :=
  (Real.le_log_iff_exp_le hM).mpr h

/-- `k ≤ log M` from `2.72 ^ k ≤ M`. -/
private lemma log_ge_of_pow_le {k : ℕ} {M : ℝ} (hM : 0 < M) (h : (2.72 : ℝ) ^ k ≤ M) :
    (k : ℝ) ≤ Real.log M :=
  le_log_of_exp_le hM (expNat_le_of_pow_le h)

private lemma log9_ge_two : (2 : ℝ) ≤ Real.log 9 :=
  log_ge_of_pow_le (k := 2) (M := 9) (by norm_num) (by norm_num)

private lemma log6_ge_one : (1 : ℝ) ≤ Real.log 6 := by
  simpa using log_ge_of_pow_le (k := 1) (M := 6) (by norm_num) (by norm_num)

private lemma log32_ge_three : (3 : ℝ) ≤ Real.log 32 :=
  log_ge_of_pow_le (k := 3) (M := 32) (by norm_num) (by norm_num)

private lemma exp5_le_160 : Real.exp (5 : ℝ) ≤ 160 :=
  expNat_le_of_pow_le (k := 5) (M := 160) (by norm_num)

/-- `19 ≤ log 9 + log 6 + 2 log 2 + 4 log 32`, since `9·6·4·32^4 = 226492416 > e^{19}`. -/
private lemma log_19_sum :
    (19 : ℝ) ≤ Real.log 9 + Real.log 6 + 2 * Real.log 2 + 4 * Real.log 32 := by
  have hexp : Real.exp (19 : ℝ) ≤ 226492416 :=
    expNat_le_of_pow_le (k := 19) (M := 226492416) (by norm_num)
  have hlog : (19 : ℝ) ≤ Real.log 226492416 := le_log_of_exp_le (by norm_num) hexp
  have e1 : Real.log (9 * 6 : ℝ) = Real.log 9 + Real.log 6 :=
    Real.log_mul (by norm_num) (by norm_num)
  have e2 : Real.log ((2 : ℝ) ^ 2) = 2 * Real.log 2 := Real.log_pow 2 2
  have e3 : Real.log ((32 : ℝ) ^ 4) = 4 * Real.log 32 := Real.log_pow 32 4
  have e4 : Real.log (9 * 6 : ℝ) + Real.log ((2 : ℝ) ^ 2) + Real.log ((32 : ℝ) ^ 4)
      = Real.log 226492416 := by
    have hA : (9 * 6 : ℝ) * 2 ^ 2 * 32 ^ 4 = 226492416 := by norm_num
    rw [show Real.log (9 * 6 : ℝ) + Real.log ((2 : ℝ) ^ 2) + Real.log ((32 : ℝ) ^ 4)
          = Real.log (((9 * 6 : ℝ) * 2 ^ 2) * 32 ^ 4) by
        rw [← Real.log_mul (by norm_num) (by norm_num),
            ← Real.log_mul (by norm_num) (by norm_num)]]
    rw [hA]
  linarith

/-- `X(n,d) ≥ log 9 + log((n+1)!) + n log n + (n+2) log 32` for `n ≥ 2`, `d ≥ 1`. -/
private lemma Xbw_lower_main {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    Real.log 9 + Real.log ((n + 1).factorial : ℝ) + (n : ℝ) * Real.log (n : ℝ)
      + ((n : ℝ) + 2) * Real.log 32 ≤ Xbw n d := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hlogd : (0 : ℝ) ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
  have hloglog : (0 : ℝ) ≤ Real.log (Real.log (2 * (n : ℝ) * (d : ℝ))) := by
    apply Real.log_nonneg
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h4 : (4 : ℝ) ≤ 2 * (n : ℝ) * (d : ℝ) := by nlinarith
    linarith [Real.exp_one_lt_three]
  have hnd : Real.log ((n : ℝ) + (d : ℝ))
      ≤ Real.log 2 + Real.log (n : ℝ) + Real.log (d : ℝ) := by
    have h1 : (0 : ℝ) < (n : ℝ) + (d : ℝ) := by linarith
    have h2 : (n : ℝ) + (d : ℝ) ≤ 2 * (n : ℝ) * (d : ℝ) := by nlinarith
    calc Real.log ((n : ℝ) + (d : ℝ)) ≤ Real.log (2 * (n : ℝ) * (d : ℝ)) :=
          Real.log_le_log h1 h2
      _ = Real.log 2 + Real.log (n : ℝ) + Real.log (d : ℝ) := by
            rw [Real.log_mul (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hnne)
                  (ne_of_gt hdpos),
                Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnne]
  have h18 : Real.log 18 = Real.log 9 + Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hmul : ((n : ℝ) + 1) * Real.log (n : ℝ)
      = (n : ℝ) * Real.log (n : ℝ) + Real.log (n : ℝ) := by ring
  rw [Xbw_expansion n d hn1 hd, h18, hmul]
  linarith [hnd, hlogd, hloglog]

/-- `X(n,d) ≥ 19` for `n ≥ 2`, `d ≥ 1`. -/
private lemma Xbw_ge_19 {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) : (19 : ℝ) ≤ Xbw n d := by
  have hmain := Xbw_lower_main hn hd
  have hfac : Real.log 6 ≤ Real.log ((n + 1).factorial : ℝ) := by
    apply Real.log_le_log (by norm_num)
    have h := Nat.factorial_le (m := 3) (n := n + 1) (by omega)
    have h3 : (3 : ℕ).factorial = 6 := by decide
    rw [h3] at h
    exact_mod_cast h
  have hlog2n : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have h0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hml : 2 * Real.log 2 ≤ (n : ℝ) * Real.log (n : ℝ) :=
    mul_le_mul h2n hlog2n h0 (by linarith)
  have hml3 : 4 * Real.log 32 ≤ ((n : ℝ) + 2) * Real.log 32 := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    exact mul_le_mul_of_nonneg_right h4 (Real.log_nonneg (by norm_num))
  linarith [hmain, hfac, hml, hml3, log_19_sum]

/-- `X(n,d) ≥ 5n` for `2 ≤ n ≤ 4`, `d ≥ 1`. -/
private lemma Xbw_ge_5n_small {n d : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4) (hd : 1 ≤ d) :
    (5 : ℝ) * n ≤ Xbw n d := by
  have hmain := Xbw_lower_main hn hd
  have hn1 : 1 ≤ n := by omega
  have hnN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnN0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hnN4 : (n : ℝ) ≤ 4 := by exact_mod_cast hn4
  have hlogn : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg hnN
  have hnfer : (0 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := mul_nonneg hnN0 hlogn
  have hfac : (1 : ℝ) ≤ Real.log ((n + 1).factorial : ℝ) := by
    have h6 : Real.log 6 ≤ Real.log ((n + 1).factorial : ℝ) := by
      apply Real.log_le_log (by norm_num)
      have h := Nat.factorial_le (m := 3) (n := n + 1) (by omega)
      have h3 : (3 : ℕ).factorial = 6 := by decide
      rw [h3] at h
      exact_mod_cast h
    linarith [log6_ge_one]
  have h32n : ((n : ℝ) + 2) * 3 ≤ ((n : ℝ) + 2) * Real.log 32 :=
    mul_le_mul_of_nonneg_left log32_ge_three (by linarith)
  linarith [hmain, log9_ge_two, hfac, hnfer, h32n, hnN4, hnN]

/-- `X(n,d) ≥ 5n` for `n ≥ 5`, `d ≥ 1`. -/
private lemma Xbw_ge_5n_large {n d : ℕ} (hn : 5 ≤ n) (hd : 1 ≤ d) :
    (5 : ℝ) * n ≤ Xbw n d := by
  have hn2 : 2 ≤ n := by omega
  have hmain := Xbw_lower_main hn2 hd
  have h5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnN : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := by linarith
  have hlog32n : (5 : ℝ) ≤ Real.log (32 * (n : ℝ)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h160 : (160 : ℝ) ≤ 32 * (n : ℝ) := by linarith
    linarith [exp5_le_160]
  have hnl : (5 : ℝ) * (n : ℝ) ≤ (n : ℝ) * Real.log (32 * (n : ℝ)) := by
    rw [mul_comm (5 : ℝ) (n : ℝ)]
    exact mul_le_mul_of_nonneg_left hlog32n hnN
  have hsplit : (n : ℝ) * Real.log (n : ℝ) + ((n : ℝ) + 2) * Real.log 32
      = (n : ℝ) * Real.log (32 * (n : ℝ)) + 2 * Real.log 32 := by
    rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hnne]
    ring
  have hfac : (1 : ℝ) ≤ Real.log ((n + 1).factorial : ℝ) := by
    have h6 : Real.log 6 ≤ Real.log ((n + 1).factorial : ℝ) := by
      apply Real.log_le_log (by norm_num)
      have h := Nat.factorial_le (m := 3) (n := n + 1) (by omega)
      have h3 : (3 : ℕ).factorial = 6 := by decide
      rw [h3] at h
      exact_mod_cast h
    linarith [log6_ge_one]
  have h9 : (1 : ℝ) ≤ Real.log 9 := le_trans (by norm_num) log9_ge_two
  have h32 : (1 : ℝ) ≤ Real.log 32 := le_trans (by norm_num) log32_ge_three
  linarith [hmain, hnl, hsplit, hfac, h9, h32]

/-- `X(n,d) ≥ 5n` for `n ≥ 2`, `d ≥ 1`. -/
private lemma Xbw_ge_5n {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) : (5 : ℝ) * n ≤ Xbw n d := by
  by_cases h5 : 5 ≤ n
  · exact Xbw_ge_5n_large h5 hd
  · exact Xbw_ge_5n_small hn (by omega) hd

/-- `1 ≤ dK K = [K : ℚ]`. -/
private lemma one_le_dK (K : Type*) [Field K] [NumberField K] : 1 ≤ dK K := by
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos (R := ℚ) (M := K)
  have : 0 < dK K := hpos
  omega

/-- BW §13 and §17: `h ≥ 19` (from `h'(L) ≥ X(2,1) = log C(2,1) − log 3 > 19`) and `h ≥ (2n+1)(1+log n) ≥ 5n` (from `h'(L) ≥ X(n,d)` of §5 and `k! ≥ k^k e^{-k+1}`). Checked numerically: `⌊X(n,d)⌋ ≥ max(19, 5n)` with equality at `n = 2, d = 1`. -/
theorem acH_lower {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) :
    19 ≤ acH K b v ∧ 5 * n ≤ acH K b v := by
  obtain ⟨hn2, -, -, -, -, -, hXbw, -, -⟩ := H.hst
  have hd1 : 1 ≤ dK K := one_le_dK K
  have h19 : (19 : ℝ) ≤ hL b (dK K) := le_trans (Xbw_ge_19 hn2 hd1) hXbw
  have h5n : (5 : ℝ) * n ≤ hL b (dK K) := le_trans (Xbw_ge_5n hn2 hd1) hXbw
  have hv : (0 : ℝ) ≤ (v : ℝ) * Real.log 2 :=
    mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  constructor
  · show 19 ≤ ⌊hL b (dK K) + (v : ℝ) * Real.log 2⌋₊
    exact Nat.le_floor (by push_cast; linarith)
  · show 5 * n ≤ ⌊hL b (dK K) + (v : ℝ) * Real.log 2⌋₊
    refine Nat.le_floor ?_
    push_cast
    linarith

end Work.BW
