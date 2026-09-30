import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num_D_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `num_kum`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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

private lemma log2_le_log_2rd {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    Real.log 2 ≤ Real.log (2 * r * d) := by
  have hR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hDd : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h4 : (4:ℝ) ≤ 2 * (r:ℝ) * (d:ℝ) := by nlinarith
  have h := Real.log_le_log (show (0:ℝ) < 4 by norm_num) h4
  have hlog4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [hlog4] at h
  linarith

private lemma log2_le_half_log {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    Real.log 2 ≤ Real.log (2 * r * d) / 2 := by
  have hR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hDd : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h4 : (4:ℝ) ≤ 2 * (r:ℝ) * (d:ℝ) := by nlinarith
  have h := Real.log_le_log (show (0:ℝ) < 4 by norm_num) h4
  have hlog4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [hlog4] at h
  linarith

private lemma core1 {R H D x L : ℝ} (hR : 2 ≤ R) (hH : 0 < H)
    (hL : Real.log 2 ≤ L / 2) (hLpos : 0 < L) (hD : 2048 * L ≤ D)
    (hx : x ≤ R * D / (2 * L)) :
    2 * H * (x + 1) * Real.log 2 ≤ 0.512 * R * H * D := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDnn : 0 ≤ D := by linarith
  have hRDnn : 0 ≤ R * D := by positivity
  have hRD_low : 4096 * L ≤ R * D := by
    have h1 : 2 * D ≤ R * D := mul_le_mul_of_nonneg_right hR hDnn
    linarith
  have key : R * D * Real.log 2 / L + 2 * Real.log 2 ≤ 0.512 * R * D := by
    have he : R * D * Real.log 2 / L + 2 * Real.log 2 =
        (R * D * Real.log 2 + 2 * Real.log 2 * L) / L := by
      field_simp
    rw [he, div_le_iff₀ hLpos]
    have hA : R * D * Real.log 2 ≤ R * D * (L / 2) := mul_le_mul_of_nonneg_left hL hRDnn
    have hB : 2 * Real.log 2 * L ≤ L * L := by
      have h : 2 * Real.log 2 ≤ L := by linarith
      exact mul_le_mul_of_nonneg_right h hLpos.le
    have hC : L * L ≤ L * (0.012 * R * D) := by
      have hLle : L ≤ 0.012 * R * D := by linarith
      exact mul_le_mul_of_nonneg_left hLle hLpos.le
    nlinarith [hA, hB, hC]
  have hstep : 2 * H * (x + 1) * Real.log 2 ≤ 2 * H * (R * D / (2 * L) + 1) * Real.log 2 := by
    have hpos : 0 ≤ 2 * H * Real.log 2 := by positivity
    have hx1 : x + 1 ≤ R * D / (2 * L) + 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hx1 hpos]
  have heq : 2 * H * (R * D / (2 * L) + 1) * Real.log 2 =
      H * (R * D * Real.log 2 / L + 2 * Real.log 2) := by
    field_simp
  rw [heq] at hstep
  have hfin : H * (R * D * Real.log 2 / L + 2 * Real.log 2) ≤ H * (0.512 * R * D) :=
    mul_le_mul_of_nonneg_left key hH.le
  linarith [hstep, hfin]

private lemma core2 {R Dd H D x L Jj : ℝ} (hR : 2 ≤ R) (hDd : 0 < Dd) (hH : 0 < H)
    (hJ : 0 ≤ Jj) (hL : Real.log 2 ≤ L / 2) (hLpos : 0 < L)
    (hl2_07 : Real.log 2 ≤ 0.7) (hD : 2048 * L ≤ D) (hx : x ≤ R * D / (2 * L)) :
    2 * Dd * Jj * H * (x + 1) * Real.log 2 ≤ 0.704 * Jj * R * Dd * H * D / L := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDnn : 0 ≤ D := by linarith
  have hRDnn : 0 ≤ R * D := by positivity
  have hRD_low : 4096 * L ≤ R * D := by
    have h1 : 2 * D ≤ R * D := mul_le_mul_of_nonneg_right hR hDnn
    linarith
  have key : R * D * Real.log 2 / L + 2 * Real.log 2 ≤ 0.704 * R * D / L := by
    have he : R * D * Real.log 2 / L + 2 * Real.log 2 =
        (R * D * Real.log 2 + 2 * Real.log 2 * L) / L := by
      field_simp
    rw [he, div_le_div_iff_of_pos_right hLpos]
    have hA : R * D * Real.log 2 ≤ (R * D) * 0.7 := mul_le_mul_of_nonneg_left hl2_07 hRDnn
    have hB : 2 * Real.log 2 * L ≤ 1.4 * L := by
      have h : 2 * Real.log 2 ≤ 1.4 := by linarith
      exact mul_le_mul_of_nonneg_right h hLpos.le
    have hC : 1.4 * L ≤ 0.004 * (R * D) := by nlinarith [hRD_low, hLpos.le]
    nlinarith [hA, hB, hC]
  have hmain : 2 * (x + 1) * Real.log 2 ≤ 0.704 * R * D / L := by
    have hx1 : x + 1 ≤ R * D / (2 * L) + 1 := by linarith
    have he : 2 * (R * D / (2 * L) + 1) * Real.log 2 =
        R * D * Real.log 2 / L + 2 * Real.log 2 := by
      field_simp
    have hs : 2 * (x + 1) * Real.log 2 ≤ 2 * (R * D / (2 * L) + 1) * Real.log 2 := by
      have hp : 0 ≤ 2 * Real.log 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hx1 hp]
    rw [he] at hs
    linarith [hs, key]
  calc 2 * Dd * Jj * H * (x + 1) * Real.log 2
      = (Dd * Jj * H) * (2 * (x + 1) * Real.log 2) := by ring
    _ ≤ (Dd * Jj * H) * (0.704 * R * D / L) := by
        apply mul_le_mul_of_nonneg_left hmain; positivity
    _ = 0.704 * Jj * R * Dd * H * D / L := by field_simp

private lemma core3 {R Dd H D : ℝ} (hR : 2 ≤ R) (hDd : 1 ≤ Dd) (hH : 19 ≤ H)
    (hD2 : 2048 * Real.log 2 ≤ D) :
    Real.log 2 ≤ 0.016 * R * Dd * H * D := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr0 : 0 < R := by linarith
  have hd0 : 0 < Dd := by linarith
  have hh0 : 0 < H := by linarith
  have s1 : 19 * (2048 * Real.log 2) ≤ H * D := by
    have h := mul_le_mul hH hD2 (by positivity) (le_of_lt hh0)
    linarith [h]
  have s2 : 1 * (19 * (2048 * Real.log 2)) ≤ Dd * (H * D) := by
    have h := mul_le_mul hDd s1 (by positivity) (le_of_lt hd0)
    linarith [h]
  have s3 : 2 * (1 * (19 * (2048 * Real.log 2))) ≤ R * (Dd * (H * D)) := by
    have h := mul_le_mul hR s2 (by positivity) (le_of_lt hr0)
    linarith [h]
  nlinarith [s3, hl2]

/-- BW §15 and §20: the 2-adic terms. `2h(D₀+1) log 2 ≤ 0·032 SD/d` (p. 46) and `2hJ(D₀+1) log 2 ≤ {0·044 J/log(2rd)} SD` (p. 59). The true 2-adic contribution, from `2^{2Jh(D₀+1)}Θ(2^{-J}s;t) ∈ ℤ` summed over `v | 2`, is `2dJh(D₀+1) log 2`; it is `≤ 0·985` of BW's bound, which is why `kumJ` is defined as BW's right-hand side. Also `log 2 ≤ 0·001 SD` (absorbed in 1·055, 1·087, 1·133). -/
theorem num_kum {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (J : ℕ) :
    2 * (h : ℝ) * (pD0 r d σ + 1) * Real.log 2 ≤ 0.032 * (pS r d h : ℝ) * pD r d σ / d ∧
      2 * (d : ℝ) * J * h * (pD0 r d σ + 1) * Real.log 2 ≤
        0.044 * J / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ ∧
      Real.log 2 ≤ 0.001 * (pS r d h : ℝ) * pD r d σ := by
  have hR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hDd : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hH : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hhpos : (0:ℝ) < (h:ℝ) := by linarith
  have hLpos : 0 < Real.log (2 * r * d) := log_2rd_pos hr hd
  have hD_low : 2 * (r:ℝ) ^ r * 32 ^ (r + 1) * (d:ℝ) * Real.log (2 * r * d) ≤ pD r d σ :=
    pD_low hr hd σ hσ
  have h2048 : (2048:ℝ) ≤ 2 * (r:ℝ) ^ r * 32 ^ (r + 1) * (d:ℝ) := by
    have h1 : (1:ℝ) ≤ (r:ℝ) ^ r := one_le_pow₀ (by linarith : (1:ℝ) ≤ (r:ℝ))
    have h2 : (1024:ℝ) ≤ 32 ^ (r + 1) := by
      have h3 : (2:ℕ) ≤ r + 1 := by omega
      calc (1024:ℝ) = 32 ^ 2 := by norm_num
        _ ≤ 32 ^ (r + 1) := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 32) h3
    have hA : (1024:ℝ) ≤ (r:ℝ) ^ r * 32 ^ (r + 1) := by
      have h := mul_le_mul h1 h2 (by norm_num : (0:ℝ) ≤ 1024)
        (by positivity : (0:ℝ) ≤ (r:ℝ) ^ r)
      linarith [h]
    have hB : (1024:ℝ) ≤ (r:ℝ) ^ r * 32 ^ (r + 1) * (d:ℝ) := by
      have h := mul_le_mul hA hDd (by norm_num : (0:ℝ) ≤ 1)
        (by linarith : (0:ℝ) ≤ (r:ℝ) ^ r * 32 ^ (r + 1))
      linarith [h]
    linarith [hB]
  have hDlow : 2048 * Real.log (2 * r * d) ≤ pD r d σ := by
    have h4 : 2048 * Real.log (2 * r * d) ≤
        2 * (r:ℝ) ^ r * 32 ^ (r + 1) * (d:ℝ) * Real.log (2 * r * d) := by
      nlinarith [h2048, hLpos.le]
    linarith
  have hDlog2 : 2048 * Real.log 2 ≤ pD r d σ := by
    nlinarith [hDlow, log2_le_log_2rd hr hd]
  have hx : (pD0 r d σ : ℝ) ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d)) := by
    have h := Nat.floor_le (show (0:ℝ) ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2 * r * d)) by
      have hp := pD_pos hr hd σ hσ
      positivity)
    simpa [pD0] using h
  refine ⟨?_, ?_, ?_⟩
  · have hS : (pS r d h : ℝ) = 16 * (r:ℝ) * (d:ℝ) * (h:ℝ) := by simp [pS]
    have hmain := core1 hR hhpos (log2_le_half_log hr hd) hLpos hDlow hx
    have heq : 0.032 * (pS r d h : ℝ) * pD r d σ / (d:ℝ) =
        0.512 * (r:ℝ) * (h:ℝ) * pD r d σ := by
      rw [hS]
      field_simp
      ring
    rw [heq]
    push_cast
    exact hmain
  · have hS : (pS r d h : ℝ) = 16 * (r:ℝ) * (d:ℝ) * (h:ℝ) := by simp [pS]
    have hmain := core2 hR hdpos hhpos (Nat.cast_nonneg J) (log2_le_half_log hr hd) hLpos
      (by linarith [Real.log_two_lt_d9]) hDlow hx
    have heq : 0.044 * (J:ℝ) / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ =
        0.704 * (J:ℝ) * (r:ℝ) * (d:ℝ) * (h:ℝ) * pD r d σ / Real.log (2 * r * d) := by
      rw [hS]
      field_simp
      ring
    rw [heq]
    push_cast
    exact hmain
  · have hS : (pS r d h : ℝ) = 16 * (r:ℝ) * (d:ℝ) * (h:ℝ) := by simp [pS]
    have heq : 0.001 * (pS r d h : ℝ) * pD r d σ =
        0.016 * (r:ℝ) * (d:ℝ) * (h:ℝ) * pD r d σ := by
      rw [hS]
      ring
    rw [heq]
    exact core3 hR hDd hH hDlog2


end Work.BW
