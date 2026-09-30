import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `num19_int`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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
| `kummer_odd_step` | (29), odd `s` | 1–1.5 | `Qdesc_half_split`, `Qdesc_val_mem`, `kummer_indep` |
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

set_option maxHeartbeats 1000000


namespace Work.BW

private lemma num19_pxi_le_one (r : ℕ) : pxi r ≤ 1 := by
  rw [pxi]
  have h : (0:ℝ) ≤ 0.536 / (r:ℝ) := by positivity
  linarith

private lemma num19_pxi_ge {r : ℕ} (hr : 2 ≤ r) : (0.732:ℝ) ≤ pxi r := by
  rw [pxi]
  have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have h : 0.536 / (r:ℝ) ≤ 0.536/2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hrR
  linarith

private lemma num19_pxi_pos {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r := by linarith [num19_pxi_ge hr]

private lemma num19_pxi_mono {r r₀ : ℕ} (h : r₀ ≤ r) (hr₀ : 1 ≤ r₀) : pxi r₀ ≤ pxi r := by
  rw [pxi, pxi]
  have h1 : (0:ℝ) < r₀ := by exact_mod_cast (by omega : 0 < r₀)
  have h3 : (r₀:ℝ) ≤ r := by exact_mod_cast h
  have : 0.536 / (r:ℝ) ≤ 0.536 / (r₀:ℝ) := div_le_div_of_nonneg_left (by norm_num) h1 h3
  linarith

private lemma num19_pxi_neglog_le {r : ℕ} (hr : 2 ≤ r) : (r:ℝ) * (-Real.log (pxi r)) ≤ 0.68 := by
  have hxpos : 0 < pxi r := num19_pxi_pos hr
  have hlog : -Real.log (pxi r) = 2 * Real.log (Real.sqrt (1/pxi r)) := by
    rw [← Real.log_inv (pxi r)]
    rw [one_div, ← Real.sq_sqrt (show (0:ℝ) ≤ (pxi r)⁻¹ by positivity)]
    rw [Real.log_pow]
    norm_num
  have hle : Real.log (Real.sqrt (1/pxi r)) ≤ Real.sqrt (1/pxi r) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
  have h2 : (r:ℝ) * (-Real.log (pxi r)) ≤ (r:ℝ) * (2 * (Real.sqrt (1/pxi r) - 1)) := by
    rw [hlog]; exact mul_le_mul_of_nonneg_left (by linarith) hr0
  have hwsq : Real.sqrt (pxi r) * Real.sqrt (pxi r) = pxi r := by
    rw [← pow_two]; exact Real.sq_sqrt (le_of_lt hxpos)
  have hwpos : 0 < Real.sqrt (pxi r) := Real.sqrt_pos.mpr hxpos
  have hr1 : (r:ℝ) * (1 - pxi r) = 0.536 := by rw [pxi]; field_simp; ring
  have halg : (r:ℝ) * (2 * (Real.sqrt (1/pxi r) - 1)) = 1.072/(pxi r + Real.sqrt (pxi r)) := by
    have hs : Real.sqrt (1/pxi r) = (Real.sqrt (pxi r))⁻¹ := by rw [one_div, Real.sqrt_inv]
    rw [hs, eq_div_iff (by positivity : pxi r + Real.sqrt (pxi r) ≠ 0)]
    field_simp
    ring_nf
    nlinarith [hwsq, hr1, hwpos]
  have hden : (1.587:ℝ) ≤ pxi r + Real.sqrt (pxi r) := by
    have h1 : (0.732:ℝ) ≤ pxi r := num19_pxi_ge hr
    have h2 : (0.855:ℝ) ≤ Real.sqrt (pxi r) := Real.le_sqrt_of_sq_le (by linarith [h1])
    linarith
  calc (r:ℝ) * (-Real.log (pxi r)) ≤ (r:ℝ) * (2 * (Real.sqrt (1/pxi r) - 1)) := h2
    _ = 1.072/(pxi r + Real.sqrt (pxi r)) := halg
    _ ≤ 1.072/1.587 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    _ ≤ 0.68 := by norm_num

private lemma num19_pxi_pow_r_ge_half {r : ℕ} (hr : 2 ≤ r) : (1/2:ℝ) ≤ pxi r ^ r := by
  have hxpos : 0 < pxi r := num19_pxi_pos hr
  have hge : Real.log (1/2) ≤ Real.log (pxi r ^ r) := by
    rw [Real.log_pow, Real.log_div one_ne_zero two_ne_zero, Real.log_one]
    have hb := num19_pxi_neglog_le hr
    have h2 := Real.log_two_gt_d9
    linarith
  have hpos : 0 < pxi r ^ r := pow_pos hxpos r
  have := Real.exp_le_exp.mpr hge
  rwa [Real.exp_log (by norm_num), Real.exp_log hpos] at this

private lemma num19_exp_neg_ge : (0.585:ℝ) ≤ Real.exp (-0.536) := by
  have h : Real.exp (0.536:ℝ) ≤ 1.7092 := by
    have hb := Real.exp_bound' (x := (0.536:ℝ)) (by norm_num) (by norm_num) (n := 5) (by norm_num)
    norm_num [Finset.sum_range_succ] at hb
    linarith
  have hpos : 0 < Real.exp (0.536:ℝ) := Real.exp_pos _
  have h2 : (1.7092:ℝ)⁻¹ ≤ (Real.exp (0.536:ℝ))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hpos h
  have h3 : (0.585:ℝ) ≤ (1.7092:ℝ)⁻¹ := by norm_num
  rw [Real.exp_neg]
  linarith

private lemma num19_pxi_pow_ge_exp {r : ℕ} (hr : 2 ≤ r) : Real.exp (-0.536) ≤ pxi r ^ (r-1) := by
  have hxpos : 0 < pxi r := num19_pxi_pos hr
  have h1 : -Real.log (pxi r) ≤ 1/pxi r - 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (pxi r)⁻¹ by positivity)
    rw [Real.log_inv] at h
    rw [one_div]; exact h
  have hr1ge : (0:ℝ) ≤ ((r-1:ℕ):ℝ) := by positivity
  have h2 : ((r-1:ℕ):ℝ) * (-Real.log (pxi r)) ≤ ((r-1:ℕ):ℝ) * (1/pxi r - 1) :=
    mul_le_mul_of_nonneg_left h1 hr1ge
  have h3 : ((r-1:ℕ):ℝ) * (1/pxi r - 1) ≤ 0.536 := by
    have hrge1 : 1 ≤ r := by omega
    have hrr : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    have hden : (0:ℝ) < (r:ℝ) - 0.536 := by linarith
    have hx : pxi r = ((r:ℝ) - 0.536)/(r:ℝ) := by rw [pxi]; field_simp
    rw [Nat.cast_sub hrge1, Nat.cast_one, hx]
    rw [one_div, inv_div]
    have key : (r:ℝ)/((r:ℝ) - 0.536) - 1 = 0.536/((r:ℝ) - 0.536) := by field_simp; ring
    rw [key]
    have hcleared : ((r:ℝ) - 1) * 0.536 ≤ 0.536 * ((r:ℝ) - 0.536) := by nlinarith
    calc ((r:ℝ) - 1) * (0.536/((r:ℝ)-0.536)) = (((r:ℝ)-1)*0.536)/((r:ℝ)-0.536) := by ring
      _ ≤ 0.536 := (div_le_iff₀ hden).mpr hcleared
  have h4 : ((r-1:ℕ):ℝ) * (-Real.log (pxi r)) ≤ 0.536 := le_trans h2 h3
  have h5 : Real.log (Real.exp (-0.536)) ≤ Real.log (pxi r ^ (r-1)) := by
    rw [Real.log_exp, Real.log_pow]
    linarith
  exact (Real.log_le_log_iff (Real.exp_pos _) (pow_pos hxpos _)).mp h5

private lemma num19_pxi_pow_j_ge_exp {r j : ℕ} (hr : 2 ≤ r) (hj : j ≤ r - 1) : Real.exp (-0.536) ≤ pxi r ^ j := by
  have hxpos : 0 < pxi r := num19_pxi_pos hr
  have hxle1 : pxi r ≤ 1 := num19_pxi_le_one r
  have hmono : pxi r ^ (r-1) ≤ pxi r ^ j := pow_le_pow_of_le_one (le_of_lt hxpos) hxle1 hj
  linarith [num19_pxi_pow_ge_exp hr]

/-- BW §19 numerics, integer extrapolation step `j → j+1` at descent level `J` (`0 ≤ j ≤ r−2`), in units `S'D` resp. `SD` with `S' = 2^jS^{(J)}`, `T' = [(1−ξ)ξ^jT^{(J)}]`. 𝒥-part (p. 53–54): `2^{-j}(0·735ξ^{j+rJ} + 1·055 + 0·044J/log(2rd)) + 9·275(2ξ^r)^{-J} − 16·13ξ^j ≤ −0·05` (BW's `(1·79/2^j) + 9·275 − 16·13ξ^j ≤ −0·05` at `J = 0`). ℐ-part (p. 54): `3·422·2^j(6·3ξ^j + q) + 0·735ξ^{j+rJ} + 1·133 + 3·03·2^j(2ξ^r)^{-J} + 0·044J/log(2rd) − 9·2^r ≤ −2·2·2^r`, where `q = ξ^{-rJ}/D` accounts for the `+1` in `S'(T'+1)` (BW drop it). Checked numerically for `r ≤ 1000`, `d ≤ 10^6`, all `J ≤ I*`, all `j` (worst margins −0·171 and −2·39·2^r; 3·422 = 3·42 + 0·002 replaces BW's 3·41 + 0·002, see `num_blaschke_eta`). -/
theorem num19_int {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (J : ℕ)
    (hJ : (J : ℝ) ≤ 50 * Real.log (2 * r * d)) (j : ℕ) (hj : j + 2 ≤ r) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ (2 * pxi r ^ r)⁻¹ ^ J / r)
    (hq2 : q ≤ (pxi r ^ r)⁻¹ ^ J / (2 * (r : ℝ) ^ r * 32 ^ (r + 1) * d * Real.log (2 * r * d))) :
    (2 : ℝ)⁻¹ ^ j * (0.735 * pxi r ^ (j + r * J) + 1.055 + 0.044 * J / Real.log (2 * r * d)) +
        9.275 * (2 * pxi r ^ r)⁻¹ ^ J - 16.13 * pxi r ^ j ≤ -0.05 ∧
      3.422 * 2 ^ j * (6.3 * pxi r ^ j + q) + 0.735 * pxi r ^ (j + r * J) + 1.133 +
        3.03 * 2 ^ j * (2 * pxi r ^ r)⁻¹ ^ J + 0.044 * J / Real.log (2 * r * d) - 9 * 2 ^ r ≤
        -2.2 * 2 ^ r := by

  constructor
  · -- ===== J-part =====
    have hx0 : 0 < pxi r := num19_pxi_pos hr
    have hx1 : pxi r ≤ 1 := num19_pxi_le_one r
    have hrd : (1:ℝ) < 2 * (r:ℝ) * (d:ℝ) := by
      have h1 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
      have h2 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      nlinarith
    have hlogpos : 0 < Real.log (2 * (r:ℝ) * (d:ℝ)) := Real.log_pos hrd
    have hcJ : 0.044 * (J:ℝ) / Real.log (2 * (r:ℝ) * (d:ℝ)) ≤ 2.2 := by
      rw [div_le_iff₀ hlogpos]; nlinarith [hJ]
    have hw0 : (0:ℝ) ≤ (2:ℝ)⁻¹ ^ j := by positivity
    have hu1 : pxi r ^ j ≤ 1 := pow_le_one₀ (le_of_lt hx0) hx1
    have hXJ : pxi r ^ (j + r*J) ≤ pxi r ^ j :=
      pow_le_pow_of_le_one (le_of_lt hx0) hx1 (Nat.le_add_right j (r*J))
    have hB1 : 1 ≤ 2 * pxi r ^ r := by have := num19_pxi_pow_r_ge_half hr; linarith
    have hBin : (2 * pxi r ^ r)⁻¹ ^ J ≤ 1 := by
      rw [inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hB1)
    have hwx : (2:ℝ)⁻¹^j * pxi r^j ≤ (2:ℝ)⁻¹^j := by
      simpa using mul_le_mul_of_nonneg_left hu1 hw0
    have hwc : (2:ℝ)⁻¹^j * (0.044 * (J:ℝ) / Real.log (2 * (r:ℝ) * (d:ℝ))) ≤ (2:ℝ)⁻¹^j * 2.2 :=
      mul_le_mul_of_nonneg_left hcJ hw0
    have hXJ' : (2:ℝ)⁻¹^j * (0.735 * pxi r ^ (j + r*J)) ≤ (2:ℝ)⁻¹^j * (0.735 * pxi r ^ j) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hXJ]) hw0
    have hmain : (2 : ℝ)⁻¹ ^ j * (0.735 * pxi r ^ (j + r * J) + 1.055 + 0.044 * J / Real.log (2 * r * d)) +
        9.275 * (2 * pxi r ^ r)⁻¹ ^ J - 16.13 * pxi r ^ j ≤
        3.99 * (2:ℝ)⁻¹^j + 9.275 - 16.13 * pxi r^j := by
      nlinarith [hXJ', hBin, hwx, hwc]
    rcases lt_or_ge j 6 with h6 | h6
    · interval_cases j
      · norm_num at hmain; linarith
      · have hp : (pxi 3)^1 ≤ (pxi r)^1 :=
          pow_le_pow_left₀ (le_of_lt (num19_pxi_pos (by omega))) (num19_pxi_mono (r₀ := 3) (by omega) (by norm_num)) 1
        have h5 : (3.99:ℝ) * (2:ℝ)⁻¹^1 + 9.275 - 16.13 * (pxi 3)^1 ≤ -0.05 := by norm_num [pxi]
        nlinarith [hmain, hp, h5]
      · have hp : (pxi 4)^2 ≤ (pxi r)^2 :=
          pow_le_pow_left₀ (le_of_lt (num19_pxi_pos (by omega))) (num19_pxi_mono (r₀ := 4) (by omega) (by norm_num)) 2
        have h5 : (3.99:ℝ) * (2:ℝ)⁻¹^2 + 9.275 - 16.13 * (pxi 4)^2 ≤ -0.05 := by norm_num [pxi]
        nlinarith [hmain, hp, h5]
      · have hp : (pxi 5)^3 ≤ (pxi r)^3 :=
          pow_le_pow_left₀ (le_of_lt (num19_pxi_pos (by omega))) (num19_pxi_mono (r₀ := 5) (by omega) (by norm_num)) 3
        have h5 : (3.99:ℝ) * (2:ℝ)⁻¹^3 + 9.275 - 16.13 * (pxi 5)^3 ≤ -0.05 := by norm_num [pxi]
        nlinarith [hmain, hp, h5]
      · have hp : (pxi 6)^4 ≤ (pxi r)^4 :=
          pow_le_pow_left₀ (le_of_lt (num19_pxi_pos (by omega))) (num19_pxi_mono (r₀ := 6) (by omega) (by norm_num)) 4
        have h5 : (3.99:ℝ) * (2:ℝ)⁻¹^4 + 9.275 - 16.13 * (pxi 6)^4 ≤ -0.05 := by norm_num [pxi]
        nlinarith [hmain, hp, h5]
      · have hp : (pxi 7)^5 ≤ (pxi r)^5 :=
          pow_le_pow_left₀ (le_of_lt (num19_pxi_pos (by omega))) (num19_pxi_mono (r₀ := 7) (by omega) (by norm_num)) 5
        have h5 : (3.99:ℝ) * (2:ℝ)⁻¹^5 + 9.275 - 16.13 * (pxi 7)^5 ≤ -0.05 := by norm_num [pxi]
        nlinarith [hmain, hp, h5]
    · have hw6 : (2:ℝ)⁻¹^j ≤ (2:ℝ)⁻¹^6 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h6
      have hu : Real.exp (-0.536) ≤ pxi r ^ j := num19_pxi_pow_j_ge_exp hr (by omega)
      have he : (0.585:ℝ) ≤ pxi r^j := le_trans num19_exp_neg_ge hu
      have h64 : (2:ℝ)⁻¹^6 = 1/64 := by norm_num
      rw [h64] at hw6
      nlinarith [hmain, hw6, he]
  · -- ===== I-part =====
    have hx0 : 0 < pxi r := num19_pxi_pos hr
    have hx1 : pxi r ≤ 1 := num19_pxi_le_one r
    have hrd : (1:ℝ) < 2 * (r:ℝ) * (d:ℝ) := by
      have h1 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
      have h2 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      nlinarith
    have hlogpos : 0 < Real.log (2 * (r:ℝ) * (d:ℝ)) := Real.log_pos hrd
    have hcJ : 0.044 * (J:ℝ) / Real.log (2 * (r:ℝ) * (d:ℝ)) ≤ 2.2 := by
      rw [div_le_iff₀ hlogpos]; nlinarith [hJ]
    have hB1 : 1 ≤ 2 * pxi r ^ r := by have := num19_pxi_pow_r_ge_half hr; linarith
    have hBin : (2 * pxi r ^ r)⁻¹ ^ J ≤ 1 := by
      rw [inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hB1)
    rcases eq_or_lt_of_le hr with h2 | hlt
    · -- r = 2
      subst h2
      have hj0 : j = 0 := by omega
      subst hj0
      norm_num at hq1 hq2 hJ ⊢
      rw [pow_mul]
      set A : ℝ := pxi 2 ^ 2 with hA
      set Bin : ℝ := (A⁻¹ * (1/2))^J with hBin
      have hAval : A = 0.535824 := by rw [hA]; norm_num [pxi]
      have hApos : 0 < A := by rw [hAval]; norm_num
      have hA1 : A ≤ 1 := by rw [hAval]; norm_num
      have hBin0 : (0:ℝ) ≤ Bin := by rw [hBin]; positivity
      have hBinle : Bin ≤ 1 := by
        rw [hBin]
        exact pow_le_one₀ (by positivity) (by rw [hAval]; norm_num)
      have hAJ1 : A^J ≤ 1 := pow_le_one₀ (le_of_lt hApos) hA1
      have hL : (1.3862:ℝ) ≤ Real.log (4 * (d:ℝ)) := by
        have h4d : (4:ℝ) ≤ 4 * (d:ℝ) := by
          have : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
          nlinarith
        have h1 : Real.log (4:ℝ) ≤ Real.log (4 * (d:ℝ)) := Real.log_le_log (by norm_num) h4d
        have h3 : (1.3862:ℝ) ≤ Real.log (4:ℝ) := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
          push_cast
          linarith [Real.log_two_gt_d9]
        exact le_trans h3 h1
      have hLpos : 0 < Real.log (4 * (d:ℝ)) := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1.3862) hL
      rcases lt_or_ge J 13 with hJ13 | hJ13
      · -- J ≤ 12
        have h2J : (2:ℝ)^J ≤ 4096 := by
          have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : J ≤ 12)
          norm_num at h; exact h
        have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
        have hD : (363000:ℝ) ≤ 262144 * (d:ℝ) * Real.log (4 * (d:ℝ)) := by
          calc (363000:ℝ) ≤ 262144 * 1 * 1.3862 := by norm_num
            _ ≤ 262144 * (d:ℝ) * Real.log (4 * (d:ℝ)) := by
                have h1 : (262144:ℝ) * 1 ≤ 262144 * (d:ℝ) :=
                  mul_le_mul_of_nonneg_left hd1 (by norm_num)
                have h2 : (262144 * (d:ℝ)) * 1.3862 ≤ (262144 * (d:ℝ)) * Real.log (4 * (d:ℝ)) :=
                  mul_le_mul_of_nonneg_left hL (by positivity)
                calc 262144 * 1 * 1.3862 = (262144 * 1) * 1.3862 := by ring
                  _ ≤ (262144 * (d:ℝ)) * 1.3862 := mul_le_mul_of_nonneg_right h1 (by norm_num)
                  _ ≤ _ := h2
        have hAinv : (A^J)⁻¹ = 2^J * Bin := by
          rw [hBin, ← inv_pow, mul_pow]
          rw [show (2:ℝ)^J * ((A⁻¹)^J * (1/2:ℝ)^J) = (A⁻¹)^J * ((2:ℝ)^J * (1/2:ℝ)^J) by ring]
          rw [show (2:ℝ)^J * (1/2:ℝ)^J = 1 by rw [← mul_pow]; norm_num, mul_one]
        have hq2' : q ≤ (2:ℝ)^J * Bin / 363000 := by
          have h := hq2
          rw [hAinv] at h
          exact le_trans h (div_le_div_of_nonneg_left (by positivity) (by norm_num) hD)
        have hq2'' : 3.422 * q ≤ 0.03862 * Bin := by
          calc 3.422 * q ≤ 3.422 * ((2:ℝ)^J * Bin / 363000) := by linarith [hq2']
            _ = (3.422 * (2:ℝ)^J / 363000) * Bin := by ring
            _ ≤ (3.422 * 4096 / 363000) * Bin := by
                apply mul_le_mul_of_nonneg_right _ hBin0
                exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2J (by norm_num)) (by norm_num)
            _ ≤ 0.03862 * Bin := by
                apply mul_le_mul_of_nonneg_right _ hBin0
                norm_num
        have hcJ12 : 0.044 * (J:ℝ) / Real.log (4 * (d:ℝ)) ≤ 0.381 := by
          rw [div_le_iff₀ hLpos]
          have hJ12 : (J:ℝ) ≤ 12 := by exact_mod_cast (by omega : J ≤ 12)
          nlinarith [hL, hJ12]
        nlinarith [hq2'', hAJ1, hcJ12, hBinle, hBin0]
      · -- J ≥ 13
        have hq1' : q ≤ Bin / 2 := hq1
        have hBin13 : Bin ≤ 0.407 := by
          rw [hBin]
          rw [show A⁻¹ * (1/2:ℝ) = (2 * A)⁻¹ by rw [mul_inv, one_div]; exact mul_comm _ _]
          rw [inv_pow]
          have h1 : (2 * A)^13 ≤ (2 * A)^J :=
            pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 2 * A) (by omega : 13 ≤ J)
          have h2 : (2.4582:ℝ) ≤ (2 * A)^13 := by
            rw [show (2 * A)^13 = (2 * (0.535824:ℝ))^13 by rw [hAval]]
            norm_num
          have hpos : 0 < (2 * A)^J := by rw [hAval]; positivity
          have h3 : ((2 * A)^J)⁻¹ ≤ ((2.4582:ℝ))⁻¹ := by
            rw [inv_le_inv₀ hpos (by norm_num)]; linarith
          have h4 : ((2.4582:ℝ))⁻¹ ≤ 0.407 := by norm_num
          linarith
        have hAJ13 : A^J ≤ 0.001 := by
          have h := pow_le_pow_of_le_one (le_of_lt hApos) hA1 (by omega : 13 ≤ J)
          have h2' : ((0.535824:ℝ))^13 ≤ 0.001 := by norm_num
          calc A^J ≤ A^13 := h
            _ ≤ ((0.535824:ℝ))^13 := by rw [hAval]
            _ ≤ 0.001 := h2'
        have hcJ13 : 0.044 * (J:ℝ) / Real.log (4 * (d:ℝ)) ≤ 2.2 := by
          rw [div_le_iff₀ hLpos]
          nlinarith [hJ]
        have hq1'' : 3.422 * q ≤ 1.711 * Bin := by
          calc 3.422 * q ≤ 3.422 * (Bin/2) := mul_le_mul_of_nonneg_left hq1' (by norm_num)
            _ = 1.711 * Bin := by ring
        nlinarith [hq1'', hBin13, hAJ13, hcJ13, hBin0]
    · -- 3 ≤ r
      have hr3 : 3 ≤ r := by omega
      have hxpow : pxi r ^ (r-2) ≤ 0.83 := by
        rcases eq_or_lt_of_le hr3 with h3 | h4
        · rw [← h3]; norm_num [pxi]
        · have hx86 : (0.866:ℝ) ≤ pxi r := by
            have h : pxi 4 ≤ pxi r := num19_pxi_mono (r₀ := 4) (by omega) (by norm_num)
            have h4' : pxi 4 = 0.866 := by norm_num [pxi]
            rw [h4'] at h; exact h
          have hlog83 : (-0.268:ℝ) ≤ Real.log 0.83 := by
            have hexp : Real.exp (-0.268) ≤ 0.83 := by
              rw [Real.exp_neg]
              have h : (1.268:ℝ) ≤ Real.exp 0.268 := by
                have := Real.add_one_le_exp (0.268:ℝ); linarith
              have hpos : 0 < Real.exp (0.268:ℝ) := Real.exp_pos _
              have h2 : (Real.exp (0.268:ℝ))⁻¹ ≤ (1.268:ℝ)⁻¹ := by
                simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1.268) h
              have h3 : (1.268:ℝ)⁻¹ ≤ 0.83 := by norm_num
              exact le_trans h2 h3
            exact (Real.le_log_iff_exp_le (by norm_num)).mpr hexp
          have hxlog : ((r-2:ℕ):ℝ) * Real.log (pxi r) ≤ -0.268 := by
            have hxle : Real.log (pxi r) ≤ -0.536/(r:ℝ) := by
              have h := Real.log_le_sub_one_of_pos hx0
              have : pxi r - 1 = -0.536/(r:ℝ) := by rw [pxi]; ring
              linarith
            have hr2 : (0:ℝ) ≤ ((r-2:ℕ):ℝ) := by positivity
            have h2 : ((r-2:ℕ):ℝ) * (-0.536/(r:ℝ)) ≤ -0.268 := by
              have hr4 : (4:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 4 ≤ r)
              have hrpos : (0:ℝ) < (r:ℝ) := by linarith
              rw [Nat.cast_sub (by omega : 2 ≤ r), Nat.cast_ofNat]
              have heq : ((r:ℝ) - 2) * (-0.536/(r:ℝ)) = -((0.536*((r:ℝ)-2))/(r:ℝ)) := by ring
              rw [heq, neg_le_neg_iff, le_div_iff₀ hrpos]
              nlinarith
            nlinarith [hxle, hr2]
          exact (Real.log_le_log_iff (pow_pos hx0 _) (by norm_num)).mp (by
            rw [Real.log_pow]; exact le_trans hxlog hlog83)
      have hT : 2^j * pxi r^j ≤ 2^(r-2) * 0.83 := by
        have h2x : (1:ℝ) ≤ 2 * pxi r := by nlinarith [num19_pxi_ge hr]
        have h := pow_le_pow_right₀ h2x (by omega : j ≤ r - 2)
        simp only [mul_pow] at h
        calc 2^j * pxi r^j ≤ 2^(r-2) * pxi r^(r-2) := h
          _ ≤ 2^(r-2) * 0.83 := by apply mul_le_mul_of_nonneg_left hxpow; positivity
      have hS : 2^j * ((2*pxi r^r)⁻¹^J) ≤ 2^(r-2) := by
        have h1 : (2:ℝ)^j ≤ 2^(r-2) := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : j ≤ r - 2)
        calc 2^j * ((2*pxi r^r)⁻¹^J) ≤ 2^j * 1 := mul_le_mul_of_nonneg_left hBin (by positivity)
          _ ≤ 2^(r-2) := by rw [mul_one]; exact h1
      have hq3 : 3.422 * 2^j * q ≤ (3.422/(r:ℝ)) * (2^j * ((2*pxi r^r)⁻¹^J)) := by
        have hr' : (0:ℝ) < (r:ℝ) := by positivity
        calc 3.422 * 2^j * q ≤ 3.422 * 2^j * (((2*pxi r^r)⁻¹^J)/r) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact hq1
          _ = (3.422/(r:ℝ)) * (2^j * ((2*pxi r^r)⁻¹^J)) := by ring
      have hI3 : 21.5586 * (2^j * pxi r^j) + 3.422 * 2^j * q + 0.735 * pxi r ^ (j + r*J) + 1.133 +
          3.03 * (2^j * ((2 * pxi r ^ r)⁻¹ ^ J)) + 0.044 * J / Real.log (2 * r * d) - 9 * 2 ^ r
          ≤ 2^(r-2) * (21.5586 * 0.83 + 3.422/(r:ℝ) + 3.03) + 4.068 - 9*2^r := by
        have h0 : 0.735 * pxi r ^ (j + r*J) ≤ 0.735 := by
          have := pow_le_one₀ (le_of_lt hx0) hx1 (n := j + r*J); nlinarith
        have hA : 21.5586 * (2^j * pxi r^j) ≤ 2^(r-2) * (21.5586 * 0.83) := by
          calc 21.5586 * (2^j * pxi r^j) ≤ 21.5586 * (2^(r-2) * 0.83) :=
                mul_le_mul_of_nonneg_left hT (by norm_num)
            _ = 2^(r-2) * (21.5586 * 0.83) := by ring
        have hB : (3.422/(r:ℝ)) * (2^j * ((2*pxi r^r)⁻¹^J)) ≤ (3.422/(r:ℝ)) * 2^(r-2) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
        have hC : 3.03 * (2^j * ((2*pxi r^r)⁻¹^J)) ≤ 3.03 * 2^(r-2) :=
          mul_le_mul_of_nonneg_left hS (by norm_num)
        nlinarith [hq3, hA, hB, hC, h0, hcJ]
      have hfinal : 2^(r-2) * (21.5586 * 0.83 + 3.422/(r:ℝ) + 3.03) + 4.068 - 9*2^r ≤ -2.2 * 2^r := by
        have hr3' : (3:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr3
        have hle : 3.422/(r:ℝ) ≤ 3.422/3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hr3'
        have h2 : (2:ℝ) ≤ 2^(r-2) := by
          have : (1:ℕ) ≤ r - 2 := by omega
          simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) this
        have hpow : (2:ℝ)^r = 4 * 2^(r-2) := by
          rw [show r = (r-2)+2 by omega, pow_add]; norm_num; ring
        nlinarith [hle, h2, hpow]
      have hkey : 3.422 * 2 ^ j * (6.3 * pxi r ^ j + q) + 0.735 * pxi r ^ (j + r * J) + 1.133 +
          3.03 * 2 ^ j * (2 * pxi r ^ r)⁻¹ ^ J + 0.044 * J / Real.log (2 * r * d) - 9 * 2 ^ r =
        21.5586 * (2^j * pxi r^j) + 3.422 * 2^j * q + 0.735 * pxi r ^ (j + r*J) + 1.133 +
          3.03 * (2^j * ((2 * pxi r ^ r)⁻¹ ^ J)) + 0.044 * J / Real.log (2 * r * d) - 9 * 2 ^ r := by
        ring
      exact le_trans (le_of_eq hkey) (le_trans hI3 hfinal)

end Work.BW
