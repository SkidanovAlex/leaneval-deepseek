import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.split_aux
import Submission.Work.BW.ulcm_le_three_pow
import Submission.Work.BW.log_ulcm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `num_13`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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


open Finset

/-! ### Numeric bounds for `exp`/`log` -/

lemma num13_log_17_lt : Real.log 1.7 < 0.532 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ (0.532:ℝ) by norm_num) 7
  have hsum : (1.7:ℝ) < ∑ i ∈ Finset.range 7, (0.532:ℝ) ^ i / ((i.factorial : ℕ) : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

lemma num13_log_three_lt : Real.log 3 < 1.1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ (1.1:ℝ) by norm_num) 9
  have hsum : (3:ℝ) < ∑ i ∈ Finset.range 9, (1.1:ℝ) ^ i / ((i.factorial : ℕ) : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

lemma num13_log_285_le : Real.log 28.5 ≤ 3.35 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ (3.35:ℝ) by norm_num) 14
  have hsum : (28.5:ℝ) ≤ ∑ i ∈ Finset.range 14, (3.35:ℝ) ^ i / ((i.factorial : ℕ) : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

lemma num13_log_le_point05 {x : ℝ} (hx : 1600 ≤ x) : Real.log x ≤ 0.05 * x := by
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

/-! ### Parameter facts -/

lemma num13_log_2rd_ge_1385 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    (1.385:ℝ) ≤ Real.log (2 * r * d) := by
  have h4 : Real.log 4 ≤ Real.log (2 * r * d) :=
    Real.log_le_log (by norm_num) (two_rd_ge_four hr hd)
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  linarith

lemma num13_pD_ge_1600 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) : (1600:ℝ) ≤ pD r d σ := by
  have h := pD_low hr hd σ hσ
  have hL : (4:ℝ)/3 ≤ Real.log (2 * r * d) := log_2rd_ge hr hd
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h1 : (4:ℝ) ≤ (r:ℝ)^r := by
    have h2 : (2:ℝ)^2 ≤ (r:ℝ)^2 := pow_le_pow_left₀ (by norm_num) hr2 2
    have h3 : (r:ℝ)^2 ≤ (r:ℝ)^r := pow_le_pow_right₀ (by linarith) hr
    calc (4:ℝ) = 2^2 := by norm_num
      _ ≤ (r:ℝ)^2 := h2
      _ ≤ (r:ℝ)^r := h3
  have h2 : (32768:ℝ) ≤ (32:ℝ)^(r+1) := by
    have h3 : (3:ℕ) ≤ r+1 := by omega
    calc (32768:ℝ) = 32^3 := by norm_num
      _ ≤ (32:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) h3
  have hnn : (0:ℝ) ≤ 2 * (r:ℝ)^r := by positivity
  have s1 : (8:ℝ) ≤ 2 * (r:ℝ)^r := by linarith
  have s2 : (8*32768:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) := by
    have hh := mul_le_mul s1 h2 (by norm_num) hnn
    simpa using hh
  have hnn2 : (0:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) := by positivity
  have s3 : (8*32768:ℝ) * 1 ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) := by
    have hh := mul_le_mul s2 hd1 (by norm_num) hnn2
    simpa using hh
  have hnn3 : (0:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) := by positivity
  have s4 : (8*32768:ℝ) * ((4:ℝ)/3) ≤
      2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2 * r * d) := by
    have hh := mul_le_mul s3 hL (by norm_num) hnn3
    simpa using hh
  linarith

lemma num13_rD_low {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    (500000:ℝ) * Real.log (2 * r * d) ≤ (r:ℝ) * pD r d σ := by
  have h := pD_low hr hd σ hσ
  have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
  have hkey : (r:ℝ) * (2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2 * r * d))
      = 2 * (r:ℝ)^(r+1) * (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2 * r * d) := by
    rw [pow_succ]; ring
  have hmul : 2 * (r:ℝ)^(r+1) * (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2 * r * d)
      ≤ (r:ℝ) * pD r d σ := by
    have hh := mul_le_mul_of_nonneg_left h hr0
    rwa [hkey] at hh
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h1 : (16:ℝ) ≤ 2 * (r:ℝ)^(r+1) := by
    have h3 : (3:ℕ) ≤ r+1 := by omega
    have h4 : (8:ℝ) ≤ (r:ℝ)^(r+1) := by
      calc (8:ℝ) = 2^3 := by norm_num
        _ ≤ (2:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) h3
        _ ≤ (r:ℝ)^(r+1) := pow_le_pow_left₀ (by norm_num) hr2 (r+1)
    linarith
  have h2 : (32768:ℝ) ≤ (32:ℝ)^(r+1) := by
    have h3 : (3:ℕ) ≤ r+1 := by omega
    calc (32768:ℝ) = 32^3 := by norm_num
      _ ≤ (32:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) h3
  have hcoef : (500000:ℝ) ≤ 2 * (r:ℝ)^(r+1) * (32:ℝ)^(r+1) * (d:ℝ) := by
    have hn1 : (0:ℝ) ≤ 2 * (r:ℝ)^(r+1) := by positivity
    have s2 : (16*32768:ℝ) ≤ 2 * (r:ℝ)^(r+1) * (32:ℝ)^(r+1) := by
      have hh := mul_le_mul h1 h2 (by norm_num) hn1
      simpa using hh
    have hn2 : (0:ℝ) ≤ 2 * (r:ℝ)^(r+1) * (32:ℝ)^(r+1) := by positivity
    have s3 : (16*32768:ℝ) * 1 ≤ 2 * (r:ℝ)^(r+1) * (32:ℝ)^(r+1) * (d:ℝ) := by
      have hh := mul_le_mul s2 hd1 (by norm_num) hn2
      simpa using hh
    linarith
  have hLnn : (0:ℝ) ≤ Real.log (2 * r * d) := le_of_lt (log_2rd_pos hr hd)
  calc (500000:ℝ) * Real.log (2 * r * d)
      ≤ (2 * (r:ℝ)^(r+1) * (32:ℝ)^(r+1) * (d:ℝ)) * Real.log (2 * r * d) :=
        mul_le_mul_of_nonneg_right hcoef hLnn
    _ = 2 * (r:ℝ)^(r+1) * (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2 * r * d) := by ring
    _ ≤ (r:ℝ) * pD r d σ := hmul

lemma num13_rD_ge {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) : (692000:ℝ) ≤ (r:ℝ) * pD r d σ := by
  have h := num13_rD_low hr hd σ hσ
  have hL := num13_log_2rd_ge_1385 hr hd
  nlinarith

lemma num13_r_le_pD {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) : (r:ℝ) ≤ pD r d σ := by
  have h := pD_low hr hd σ hσ
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h1 : (r:ℝ) ≤ 2 * (r:ℝ)^r := by
    have hrr : (r:ℝ)^1 ≤ (r:ℝ)^r := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ r)
    rw [pow_one] at hrr
    linarith [hrr]
  have h2 : (1:ℝ) ≤ (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2 * r * d) := by
    have h32 : (1:ℝ) ≤ (32:ℝ)^(r+1) := one_le_pow₀ (by norm_num)
    have hL : (1:ℝ) ≤ Real.log (2 * r * d) := by linarith [log_2rd_ge hr hd]
    have s1 : (1:ℝ) ≤ (32:ℝ)^(r+1) * (d:ℝ) := by
      have hh := mul_le_mul h32 hd1 (by norm_num) (by norm_num)
      simpa using hh
    have hh := mul_le_mul s1 hL (by norm_num) (by linarith)
    simpa using hh
  have hnn : (0:ℝ) ≤ 2 * (r:ℝ)^r := by positivity
  calc (r:ℝ) ≤ 2 * (r:ℝ)^r := h1
    _ ≤ 2 * (r:ℝ)^r * ((32:ℝ)^(r+1) * (d:ℝ) * Real.log (2 * r * d)) := by nlinarith [h2, hnn]
    _ = 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2 * r * d) := by ring
    _ ≤ pD r d σ := h


lemma num13_hpart {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    (Real.log (57 * (r:ℝ) * (d:ℝ)) + 2 / (57 * (r:ℝ) * (d:ℝ))) * ((pD0 r d σ : ℝ) + 1)
      ≤ 1.728 * (r : ℝ) * pD r d σ := by
  have hLpos : 0 < Real.log (2 * r * d) := log_2rd_pos hr hd
  have hL1385 : (1.385:ℝ) ≤ Real.log (2 * r * d) := num13_log_2rd_ge_1385 hr hd
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hD0 : (pD0 r d σ : ℝ) + 1
      ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d)) + 1 := by
    have h := pD0_le hr hd σ hσ
    linarith
  have hRD : (500000:ℝ) * Real.log (2 * r * d) ≤ (r:ℝ) * pD r d σ :=
    num13_rD_low hr hd σ hσ
  have hlog57 : Real.log (57 * (r:ℝ) * (d:ℝ)) = Real.log 28.5 + Real.log (2 * (r:ℝ) * (d:ℝ)) := by
    have h1 : (57:ℝ) * (r:ℝ) * (d:ℝ) = 28.5 * (2 * (r:ℝ) * (d:ℝ)) := by ring
    rw [h1, Real.log_mul (by norm_num) (by positivity)]
  have hmu : 2 / (57 * (r:ℝ) * (d:ℝ)) ≤ 0.0176 := by
    have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hrd : (2:ℝ) ≤ (r:ℝ) * (d:ℝ) := by
      simpa using mul_le_mul hr2 hd1 (by norm_num) (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hA : Real.log (57 * (r:ℝ) * (d:ℝ)) + 2 / (57 * (r:ℝ) * (d:ℝ))
      ≤ Real.log (2 * (r:ℝ) * (d:ℝ)) + 3.3676 := by
    rw [hlog57]
    have h1 := num13_log_285_le
    linarith
  have hC2 : (3.3676:ℝ) ≤ 2.44 * Real.log (2 * r * d) := by linarith
  have hCdiv : (3.3676:ℝ) / (2 * Real.log (2 * r * d)) ≤ 1.22 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hsum : Real.log (2 * r * d) + (3.3676:ℝ) ≤ 0.008 * ((r:ℝ) * pD r d σ) := by
    have h1 : Real.log (2 * r * d) + 3.3676 ≤ 3.44 * Real.log (2 * r * d) := by linarith
    have h2 : (3.44:ℝ) * Real.log (2 * r * d) ≤ 0.008 * ((r:ℝ) * pD r d σ) := by
      have h3 : (0.008:ℝ) * (500000 * Real.log (2 * r * d))
          ≤ 0.008 * ((r:ℝ) * pD r d σ) := mul_le_mul_of_nonneg_left hRD (by norm_num)
      linarith
    linarith
  have hmul : (Real.log (2 * r * d) + 3.3676)
        * ((r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d)) + 1)
      = (r:ℝ) * pD r d σ / 2 + ((r:ℝ) * pD r d σ) * 3.3676 / (2 * Real.log (2 * r * d))
        + Real.log (2 * r * d) + 3.3676 := by
    field_simp
    ring
  have hmid : ((r:ℝ) * pD r d σ) * 3.3676 / (2 * Real.log (2 * r * d))
      ≤ 1.22 * ((r:ℝ) * pD r d σ) := by
    rw [mul_div_assoc]
    have h1 : ((r:ℝ) * pD r d σ) * (3.3676 / (2 * Real.log (2 * r * d)))
        ≤ ((r:ℝ) * pD r d σ) * 1.22 :=
      mul_le_mul_of_nonneg_left hCdiv (by positivity)
    linarith
  have hchain : (Real.log (2 * r * d) + 3.3676)
        * ((r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d)) + 1)
      ≤ 1.728 * ((r:ℝ) * pD r d σ) := by
    rw [hmul]
    nlinarith [hmid, hsum]
  calc (Real.log (57 * (r:ℝ) * (d:ℝ)) + 2 / (57 * (r:ℝ) * (d:ℝ))) * ((pD0 r d σ : ℝ) + 1)
      ≤ (Real.log (2 * r * d) + 3.3676)
          * ((r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d)) + 1) :=
        mul_le_mul hA hD0 (by positivity) (by linarith)
    _ ≤ 1.728 * ((r:ℝ) * pD r d σ) := hchain
    _ = 1.728 * (r:ℝ) * pD r d σ := by ring

lemma num13_xpart {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    ((pD0 r d σ : ℝ) + 1) ≤ 0.399 * ((r:ℝ) * pD r d σ) := by
  have hLpos : 0 < Real.log (2 * r * d) := log_2rd_pos hr hd
  have hL43 : (4:ℝ)/3 ≤ Real.log (2 * r * d) := log_2rd_ge hr hd
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hD0 : (pD0 r d σ : ℝ) + 1
      ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d)) + 1 := by
    have h := pD0_le hr hd σ hσ
    linarith
  have hRD : (692000:ℝ) ≤ (r:ℝ) * pD r d σ := num13_rD_ge hr hd σ hσ
  have hup : (0:ℝ) < (r:ℝ) * pD r d σ := by positivity
  have h1 : (r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d))
      ≤ 0.375 * ((r:ℝ) * pD r d σ) := by
    rw [div_le_iff₀ (by positivity)]
    have h2L : (1:ℝ) ≤ 0.375 * (2 * Real.log (2 * r * d)) := by linarith
    calc (r:ℝ) * pD r d σ = 1 * ((r:ℝ) * pD r d σ) := by ring
      _ ≤ (0.375 * (2 * Real.log (2 * r * d))) * ((r:ℝ) * pD r d σ) :=
            mul_le_mul_of_nonneg_right h2L (le_of_lt hup)
      _ = 0.375 * ((r:ℝ) * pD r d σ) * (2 * Real.log (2 * r * d)) := by ring
  have h2 : (1:ℝ) ≤ 0.024 * ((r:ℝ) * pD r d σ) := by linarith
  linarith

lemma num13_logN {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    Real.log ((h : ℝ) * (pD0 r d σ + 1) * ∏ j, ((pDj r d σ j : ℝ) + 1))
      ≤ 0.001 * (h : ℝ) * (pT r d σ : ℝ) := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hh19 : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hhpos : (0:ℝ) < (h:ℝ) := by linarith
  have hLpos : 0 < Real.log (2 * r * d) := log_2rd_pos hr hd
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hD1600 : (1600:ℝ) ≤ pD r d σ := num13_pD_ge_1600 hr hd σ hσ
  have hlogD : Real.log (pD r d σ) ≤ 0.05 * pD r d σ := num13_log_le_point05 hD1600
  have hDr : (r:ℝ) ≤ pD r d σ := num13_r_le_pD hr hd σ hσ
  have hlogr : Real.log (r:ℝ) ≤ Real.log (pD r d σ) := Real.log_le_log hrpos hDr
  have hRD : (692000:ℝ) ≤ (r:ℝ) * pD r d σ := num13_rD_ge hr hd σ hσ
  have hT : (11:ℝ) * (r:ℝ) * pD r d σ ≤ (pT r d σ : ℝ) := pT_ge hr hd σ hσ
  have hD0 : (pD0 r d σ : ℝ) + 1
      ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d)) + 1 := by
    have h := pD0_le hr hd σ hσ
    linarith
  have hprod : ∏ j : Fin r, ((pDj r d σ j : ℝ) + 1) ≤ (pD r d σ / (r:ℝ) + 1)^r := by
    have h1 : ∀ j : Fin r, ((pDj r d σ j : ℝ) + 1) ≤ pD r d σ / (r:ℝ) + 1 := by
      intro j
      have := pDj_le_r hr hd σ hσ j
      linarith
    calc ∏ j : Fin r, ((pDj r d σ j : ℝ) + 1)
        ≤ ∏ _j : Fin r, (pD r d σ / (r:ℝ) + 1) :=
          prod_le_prod_of_nonneg (fun j _ => by positivity) (fun j _ => h1 j)
      _ = (pD r d σ / (r:ℝ) + 1)^r := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hA2 : (r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d)) + 1 ≤ (r:ℝ) * pD r d σ := by
    have hL1 : (1:ℝ) ≤ Real.log (2 * r * d) := by linarith [log_2rd_ge hr hd]
    have h2 : (r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d)) ≤ (r:ℝ) * pD r d σ / 2 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    linarith [h2, hRD]
  have hA3 : pD r d σ / (r:ℝ) + 1 ≤ pD r d σ := by
    have h1 : pD r d σ / (r:ℝ) ≤ pD r d σ / 2 :=
      div_le_div_of_nonneg_left (le_of_lt hDpos) (by norm_num) (by linarith)
    linarith [h1, hD1600]
  have hAle : (h:ℝ) * ((pD0 r d σ : ℝ) + 1) * ∏ j : Fin r, ((pDj r d σ j : ℝ) + 1)
      ≤ (h:ℝ) * ((r:ℝ) * pD r d σ) * (pD r d σ)^r := by
    have hh0 : (0:ℝ) ≤ (h:ℝ) := le_of_lt hhpos
    have hstep1 : (h:ℝ) * ((pD0 r d σ : ℝ) + 1) ≤ (h:ℝ) * ((r:ℝ) * pD r d σ) := by
      calc (h:ℝ) * ((pD0 r d σ : ℝ) + 1)
          ≤ (h:ℝ) * ((r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d)) + 1) :=
            mul_le_mul_of_nonneg_left hD0 hh0
        _ ≤ (h:ℝ) * ((r:ℝ) * pD r d σ) := mul_le_mul_of_nonneg_left hA2 hh0
    have hpnn : (0:ℝ) ≤ ∏ j : Fin r, ((pDj r d σ j : ℝ) + 1) :=
      Finset.prod_nonneg (fun j _ => by positivity)
    have hstep2 : ∏ j : Fin r, ((pDj r d σ j : ℝ) + 1) ≤ (pD r d σ)^r := by
      calc ∏ j : Fin r, ((pDj r d σ j : ℝ) + 1) ≤ (pD r d σ / (r:ℝ) + 1)^r := hprod
        _ ≤ (pD r d σ)^r := pow_le_pow_left₀ (by positivity) hA3 r
    have hb : (0:ℝ) ≤ (h:ℝ) * ((r:ℝ) * pD r d σ) :=
      le_of_lt (mul_pos hhpos (mul_pos hrpos hDpos))
    exact mul_le_mul hstep1 hstep2 hpnn hb
  have hApos : 0 < (h:ℝ) * ((pD0 r d σ : ℝ) + 1) * ∏ j : Fin r, ((pDj r d σ j : ℝ) + 1) := by
    have h1 : (0:ℝ) < (h:ℝ) * ((pD0 r d σ : ℝ) + 1) := by positivity
    have h2 : (0:ℝ) < ∏ j : Fin r, ((pDj r d σ j : ℝ) + 1) :=
      Finset.prod_pos (fun j _ => by positivity)
    exact mul_pos h1 h2
  have hBpos : 0 < (h:ℝ) * ((r:ℝ) * pD r d σ) * (pD r d σ)^r :=
    mul_pos (mul_pos hhpos (mul_pos hrpos hDpos)) (pow_pos hDpos r)
  have hlog1 : Real.log ((h:ℝ) * ((r:ℝ) * pD r d σ) * (pD r d σ)^r)
      = Real.log (h:ℝ) + Real.log (r:ℝ) + (1 + (r:ℝ)) * Real.log (pD r d σ) := by
    rw [Real.log_mul (mul_pos hhpos (mul_pos hrpos hDpos)).ne' (pow_pos hDpos r).ne']
    rw [Real.log_mul hhpos.ne' (mul_pos hrpos hDpos).ne']
    rw [Real.log_mul hrpos.ne' hDpos.ne']
    rw [Real.log_pow]
    ring
  have h1 : Real.log (h:ℝ) ≤ 0.0015 * ((h:ℝ) * ((r:ℝ) * pD r d σ)) := by
    have hlogh : Real.log (h:ℝ) ≤ (h:ℝ) := by
      have := Real.log_le_sub_one_of_pos hhpos
      linarith
    have h2 : (1:ℝ) ≤ 0.0015 * ((r:ℝ) * pD r d σ) := by linarith
    have hh0 : (0:ℝ) ≤ (h:ℝ) := le_of_lt hhpos
    nlinarith [hlogh, h2, hh0]
  have h2 : Real.log (r:ℝ) + ((r:ℝ) + 1) * Real.log (pD r d σ)
      ≤ 0.0085 * ((h:ℝ) * ((r:ℝ) * pD r d σ)) := by
    have hDnn : (0:ℝ) ≤ pD r d σ := le_of_lt hDpos
    have h3 : ((r:ℝ) + 2) * Real.log (pD r d σ)
        ≤ ((r:ℝ) + 2) * (0.05 * pD r d σ) :=
      mul_le_mul_of_nonneg_left hlogD (by linarith)
    have h4 : ((r:ℝ) + 2) * (0.05 * pD r d σ) ≤ 0.1 * ((r:ℝ) * pD r d σ) := by
      have h5 : (r:ℝ) + 2 ≤ 2 * (r:ℝ) := by linarith
      have h6 : (0:ℝ) ≤ 0.05 * pD r d σ := mul_nonneg (by norm_num) hDnn
      have h7 : ((r:ℝ) + 2) * (0.05 * pD r d σ) ≤ (2 * (r:ℝ)) * (0.05 * pD r d σ) :=
        mul_le_mul_of_nonneg_right h5 h6
      linarith [h7]
    have h6 : (0.1:ℝ) * ((r:ℝ) * pD r d σ) ≤ 0.0085 * ((h:ℝ) * ((r:ℝ) * pD r d σ)) := by
      have h7 : (0.1:ℝ) ≤ 0.0085 * (h:ℝ) := by linarith
      have h8 : (0:ℝ) ≤ (r:ℝ) * pD r d σ := mul_nonneg (le_of_lt hrpos) hDnn
      have h9 := mul_le_mul_of_nonneg_right h7 h8
      linarith [h9]
    linarith [h3, h4, h6, hlogr]
  calc Real.log ((h : ℝ) * (pD0 r d σ + 1) * ∏ j, ((pDj r d σ j : ℝ) + 1))
      ≤ Real.log ((h:ℝ) * ((r:ℝ) * pD r d σ) * (pD r d σ)^r) :=
        Real.log_le_log hApos hAle
    _ = Real.log (h:ℝ) + Real.log (r:ℝ) + (1 + (r:ℝ)) * Real.log (pD r d σ) := hlog1
    _ ≤ 0.0015 * ((h:ℝ) * ((r:ℝ) * pD r d σ))
        + 0.0085 * ((h:ℝ) * ((r:ℝ) * pD r d σ)) := by linarith [h1, h2]
    _ = 0.01 * ((h:ℝ) * ((r:ℝ) * pD r d σ)) := by ring
    _ ≤ 0.011 * ((h:ℝ) * ((r:ℝ) * pD r d σ)) := by
        have hh0 : (0:ℝ) ≤ (h:ℝ) := le_of_lt hhpos
        have h9 : (0:ℝ) ≤ (r:ℝ) * pD r d σ := mul_nonneg (le_of_lt hrpos) (le_of_lt hDpos)
        have : (0:ℝ) ≤ (h:ℝ) * ((r:ℝ) * pD r d σ) := mul_nonneg hh0 h9
        linarith
    _ ≤ 0.001 * (h : ℝ) * (pT r d σ : ℝ) := by
        have hh0 : (0:ℝ) ≤ 0.001 * (h:ℝ) := by positivity
        have h9 := mul_le_mul_of_nonneg_left hT hh0
        linarith [h9]

/-- BW §13–14 decimals behind (13): `log 1·7 < 0·028h` (`h ≥ 19`); `(log u(h) − h)t₀ ≤ 0·1hT` (from `u(h) ≤ 3^h`); `μ = 57rd` gives `{(log μ + 2/μ)h + |z|/μ}(D₀+1) ≤ (0·108S + 0·007|z|)D/d`; (11) `log N ≤ 0·001hT`. Checked numerically (ratios ≤ 0·993). -/
theorem num_13 {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (t0 : ℕ) (ht0 : (t0 : ℝ) ≤ pT r d σ) (x : ℝ) (hx : 0 ≤ x) :
    Real.log 1.7 < 0.028 * h ∧
      (Real.log (ulcm h) - h) * t0 ≤ 0.1 * h * pT r d σ ∧
      ((Real.log (57 * r * d) + 2 / (57 * r * d)) * h + x / (57 * r * d)) * (pD0 r d σ + 1) ≤
        (0.108 * (pS r d h : ℝ) + 0.007 * x) * pD r d σ / d ∧
      Real.log ((h : ℝ) * (pD0 r d σ + 1) * ∏ j, ((pDj r d σ j : ℝ) + 1)) ≤
        0.001 * h * pT r d σ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h17 := num13_log_17_lt
    have h19 : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
    have h2 : (0.028:ℝ) * 19 ≤ 0.028 * (h:ℝ) := by linarith
    linarith
  · have hlogu : Real.log (ulcm h : ℝ) ≤ (h:ℝ) * 1.1 := by
      have h := log_ulcm_le h hh
      linarith
    have hkey : Real.log (ulcm h) - (h:ℝ) ≤ 0.1 * (h:ℝ) := by linarith
    have ht0nn : (0:ℝ) ≤ (t0:ℝ) := Nat.cast_nonneg _
    calc (Real.log (ulcm h) - (h:ℝ)) * (t0:ℝ)
        ≤ (0.1 * (h:ℝ)) * (t0:ℝ) := mul_le_mul_of_nonneg_right hkey ht0nn
      _ = 0.1 * (h:ℝ) * (t0:ℝ) := by ring
      _ ≤ 0.1 * (h:ℝ) * (pT r d σ : ℝ) := by
          have h2 : (t0:ℝ) ≤ (pT r d σ : ℝ) := ht0
          have h3 : (0:ℝ) ≤ 0.1 * (h:ℝ) := by positivity
          nlinarith [h2, h3]
  · have hpart := num13_hpart hr hd σ hσ
    have xpart := num13_xpart hr hd σ hσ
    have hh0 : (0:ℝ) ≤ (h:ℝ) := by positivity
    have hr0 : (0:ℝ) < (r:ℝ) := by
      have : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
      linarith
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    have hS : (pS r d h : ℝ) = 16 * (r:ℝ) * (d:ℝ) * (h:ℝ) := by
      simp only [pS]; push_cast; ring
    have h1 : (Real.log (57 * (r:ℝ) * (d:ℝ)) + 2 / (57 * (r:ℝ) * (d:ℝ))) * (h:ℝ)
          * ((pD0 r d σ : ℝ) + 1)
        ≤ 1.728 * (r:ℝ) * pD r d σ * (h:ℝ) := by
      have h := mul_le_mul_of_nonneg_right hpart hh0
      linarith [h]
    have h2 : x / (57 * (r:ℝ) * (d:ℝ)) * ((pD0 r d σ : ℝ) + 1)
        ≤ 0.007 * x * pD r d σ / (d:ℝ) := by
      have hstep : x / (57 * (r:ℝ) * (d:ℝ)) * ((pD0 r d σ : ℝ) + 1)
          ≤ x / (57 * (r:ℝ) * (d:ℝ)) * (0.399 * ((r:ℝ) * pD r d σ)) :=
        mul_le_mul_of_nonneg_left xpart (by positivity)
      have hxe : x / (57 * (r:ℝ) * (d:ℝ)) * (0.399 * ((r:ℝ) * pD r d σ))
          = 0.007 * x * pD r d σ / (d:ℝ) := by
        field_simp
        ring
      rw [hxe] at hstep
      exact hstep
    rw [add_mul]
    have hS3 : (0.108:ℝ) * (pS r d h : ℝ) * pD r d σ / (d:ℝ)
        = 1.728 * (r:ℝ) * pD r d σ * (h:ℝ) := by
      rw [hS]; field_simp; ring
    have hRHS : (0.108 * (pS r d h : ℝ) + 0.007 * x) * pD r d σ / (d:ℝ)
        = 0.108 * (pS r d h : ℝ) * pD r d σ / (d:ℝ) + 0.007 * x * pD r d σ / (d:ℝ) := by
      ring
    rw [hRHS, hS3]
    linarith [h1, h2]
  · exact num13_logN hr hd hh σ hσ

end Work.BW
