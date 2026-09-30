import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `num19_half`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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

/-! ### Elementary bounds on `ξ = pxi r = 1 - 0.536/r` and on `exp (-0.536)`.

All of these are pure real arithmetic, valid for `r ≥ 2`. -/

private lemma exp_neg_536_ge : (0.5847 : ℝ) ≤ Real.exp (-0.536) := by
  have h := Real.exp_bound (x := (-0.536:ℝ)) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

private lemma exp_neg_536_le : Real.exp (-0.536) ≤ 0.5851 := by
  have h := Real.exp_bound (x := (-0.536:ℝ)) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.1]

private lemma log_four_ge_one : (1:ℝ) ≤ Real.log 4 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  linarith [Real.exp_one_lt_three]

private lemma pxi_pos (r : ℕ) (hr : 2 ≤ r) : 0 < pxi r := by
  have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  simp only [pxi]
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

private lemma pxi_le_one (r : ℕ) (hr : 2 ≤ r) : pxi r ≤ 1 := by
  simp only [pxi]
  have h : (0:ℝ) ≤ 0.536/(r:ℝ) := by positivity
  linarith

private lemma pxi_pow_r_le (r : ℕ) (hr : 2 ≤ r) : pxi r ^ r ≤ Real.exp (-0.536) := by
  have h2 : (0.536:ℝ) ≤ (r:ℝ) := by
    have : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
    linarith
  simpa only [pxi] using Real.one_sub_div_pow_le_exp_neg (n := r) (t := 0.536) h2

private lemma pxi_pow_pred_lower (r : ℕ) (hr : 2 ≤ r) : Real.exp (-0.536) ≤ pxi r ^ (r-1) := by
  have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hxi_pos : 0 < pxi r := pxi_pos r hr
  have hlog : -(0.536/((r:ℝ)-0.536)) ≤ Real.log (pxi r) := by
    have h1 : (0:ℝ) < 1 - 0.536/(r:ℝ) := by
      rw [sub_pos, div_lt_one hrpos]; linarith
    have h2 : Real.log ((1 - 0.536/(r:ℝ))⁻¹) ≤ (1 - 0.536/(r:ℝ))⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at h2
    have h3 : (1 - 0.536/(r:ℝ))⁻¹ - 1 = 0.536/((r:ℝ)-0.536) := by
      have hne1 : (1 - 0.536/(r:ℝ)) ≠ 0 := ne_of_gt h1
      have hne2 : ((r:ℝ)-0.536) ≠ 0 := by apply ne_of_gt; linarith
      field_simp
      ring
    rw [h3] at h2
    have h4 : (1 - 0.536/(r:ℝ)) = pxi r := by simp only [pxi]
    rw [h4] at h2
    linarith
  rw [← Real.le_log_iff_exp_le (pow_pos hxi_pos _)]
  rw [Real.log_pow]
  have hfac : (0:ℝ) ≤ ((r-1 : ℕ) : ℝ) := by positivity
  have hrk : (0:ℝ) < (r:ℝ) - 0.536 := by linarith
  have hle : ((r-1:ℕ):ℝ) * (0.536/((r:ℝ)-0.536)) ≤ 0.536 := by
    rw [← mul_div_assoc]
    rw [div_le_iff₀ hrk]
    have hc : ((r-1:ℕ):ℝ) = (r:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    have : ((r-1:ℕ):ℝ) ≤ (r:ℝ) - 0.536 := by rw [hc]; linarith
    nlinarith [this]
  nlinarith [hlog, hfac, hle]

private lemma pxi_pow_pred_le (r : ℕ) (hr : 2 ≤ r) : pxi r ^ (r-1) ≤ 0.732 := by
  rcases lt_or_eq_of_le hr with h3 | h2
  · have hxr : pxi r ^ r ≤ 0.5851 := le_trans (pxi_pow_r_le r hr) exp_neg_536_le
    have hxi_ge : (1 - 0.536/3 : ℝ) ≤ pxi r := by
      simp only [pxi]
      have hrR : (3:ℝ) ≤ (r:ℝ) := by exact_mod_cast h3
      have h : 0.536/(r:ℝ) ≤ 0.536/3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hrR
      linarith
    have hpos : 0 < pxi r := pxi_pos r hr
    have hmul : pxi r ^ (r-1) * pxi r = pxi r ^ r := by
      have hr1 : 1 ≤ r := by omega
      rw [← pow_succ, Nat.sub_add_cancel hr1]
    have h1 : pxi r ^ (r-1) * (1 - 0.536/3) ≤ 0.5851 := by
      have h0 : (0:ℝ) ≤ pxi r ^ (r-1) := by positivity
      calc pxi r ^ (r-1) * (1-0.536/3) ≤ pxi r ^ (r-1) * pxi r :=
              mul_le_mul_of_nonneg_left hxi_ge h0
        _ = pxi r ^ r := hmul
        _ ≤ 0.5851 := hxr
    have h0 : (0:ℝ) ≤ pxi r ^ (r-1) := by positivity
    have hge : (0.8:ℝ) ≤ 1 - 0.536/3 := by norm_num
    have hA : 0.8 * pxi r ^ (r-1) ≤ 0.5851 := by
      calc 0.8 * pxi r ^ (r-1) ≤ (1 - 0.536/3) * pxi r ^ (r-1) :=
              mul_le_mul_of_nonneg_right hge h0
        _ = pxi r ^ (r-1) * (1 - 0.536/3) := by ring
        _ ≤ 0.5851 := h1
    nlinarith [hA]
  · subst h2; norm_num [pxi]

private lemma pxi_pow_r_ge (r : ℕ) (hr : 2 ≤ r) : (0.53 : ℝ) ≤ pxi r ^ r := by
  by_cases h5 : r ≤ 5
  · interval_cases r <;> norm_num [pxi]
  · simp only [not_le] at h5
    have hK1 : Real.exp (-0.536) ≤ pxi r ^ (r-1) := pxi_pow_pred_lower r hr
    have hxi6 : (1 - 0.536/6 : ℝ) ≤ pxi r := by
      simp only [pxi]
      have hrR : (6:ℝ) ≤ (r:ℝ) := by exact_mod_cast h5
      have h : 0.536/(r:ℝ) ≤ 0.536/6 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hrR
      linarith
    have hmul : pxi r ^ r = pxi r ^ (r-1) * pxi r := by
      have hr1 : 1 ≤ r := by omega
      rw [← pow_succ, Nat.sub_add_cancel hr1]
    have hstep : (0.53:ℝ) ≤ Real.exp (-0.536) * (1 - 0.536/6) := by
      nlinarith [exp_neg_536_ge]
    calc (0.53:ℝ) ≤ Real.exp (-0.536) * (1 - 0.536/6) := hstep
      _ ≤ pxi r ^ (r-1) * pxi r := by
            apply mul_le_mul hK1 hxi6 (by norm_num) (by positivity)
      _ = pxi r ^ r := hmul.symm

/-- `0.044 * J / L ≤ 0.044 * k / 1.386` when `L ≥ 1.386` and `J ≤ k`. -/
private lemma JL_le (L : ℝ) (hLpos : 0 < L) (hL1386 : (1.386:ℝ) ≤ L) (J k : ℕ) (hk : J ≤ k) :
    0.044 * (J:ℝ) / L ≤ 0.044 * (k:ℝ) / 1.386 := by
  have h1 : 0.044 * (J:ℝ) / L ≤ 0.044 * (k:ℝ) / L := by
    apply div_le_div_of_nonneg_right
    · have : (J:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      linarith
    · exact le_of_lt hLpos
  have h2 : 0.044 * (k:ℝ) / L ≤ 0.044 * (k:ℝ) / 1.386 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hL1386
  linarith

/-- `0.044 * J / L ≤ 2.2` when `J ≤ 50 L`. -/
private lemma JL_le50 (L : ℝ) (hLpos : 0 < L) (J : ℕ) (hJ : (J:ℝ) ≤ 50 * L) :
    0.044 * (J:ℝ) / L ≤ 2.2 := by
  have h1 : (J:ℝ) / L ≤ 50 := by rw [div_le_iff₀ hLpos]; linarith
  have h2 : (0.044:ℝ) * ((J:ℝ)/L) ≤ 0.044 * 50 := mul_le_mul_of_nonneg_left h1 (by norm_num)
  rw [← mul_div_assoc] at h2
  linarith [h2]

/-- BW §19 numerics, half-integer step at level `J` (p. 55–56), in units `2^rSD` with `S' = 2^{r-1}S^{(J)}`, `T' = [(1−ξ)ξ^{r-1}T^{(J)}]`. 𝒥-part: `0·735ξ^{r-1+rJ} + 1·087 + 5·646(2ξ^r)^{-J} + 0·044J/log(2rd) − 12·43ξ^{r-1} ≤ −0·105` (BW: `2{0·735ξ^{r-1} + 6·733 − 12·43ξ^{r-1}}S'D ≤ −0·21S'D`). ℐ-part: `1·021(6·3ξ^{r-1} + q) + 0·735ξ^{r-1+rJ} − 7·893 + 2·525(2ξ^r)^{-J} + 0·044J/log(2rd) ≤ −0·12` (BW: `2{1·02S'(T'+1) + 0·735ξ^{r-1}S'D − 5·368S'D} ≤ −0·25S'D`). The `q` term needs the non-degeneracy bound `q ≤ (2ξ^r)^{-J}/r`; without it the ℐ-part FAILS for large `J` (e.g. `r = 2, d = 1, σ = 1, J ≥ 23`). Checked numerically (worst −0·112, −0·1215 at `J = 0`; the coefficient 1·021 replaces BW's 1·02 because BW's 2·03 fails at `T' = 0`, see `num_blaschke_eta`). -/
theorem num19_half {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (J : ℕ)
    (hJ : (J : ℝ) ≤ 50 * Real.log (2 * r * d)) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ (2 * pxi r ^ r)⁻¹ ^ J / r)
    (hq2 : q ≤ (pxi r ^ r)⁻¹ ^ J / (2 * (r : ℝ) ^ r * 32 ^ (r + 1) * d * Real.log (2 * r * d))) :
    0.735 * pxi r ^ (r - 1 + r * J) + 1.087 + 5.646 * (2 * pxi r ^ r)⁻¹ ^ J +
        0.044 * J / Real.log (2 * r * d) - 12.43 * pxi r ^ (r - 1) ≤ -0.105 ∧
      1.021 * (6.3 * pxi r ^ (r - 1) + q) + 0.735 * pxi r ^ (r - 1 + r * J) - 7.893 +
        2.525 * (2 * pxi r ^ r)⁻¹ ^ J + 0.044 * J / Real.log (2 * r * d) ≤ -0.12 := by
  have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hxi_pos : 0 < pxi r := pxi_pos r hr
  have hxi_nonneg : 0 ≤ pxi r := le_of_lt hxi_pos
  have hxi_le1 : pxi r ≤ 1 := pxi_le_one r hr
  have hK1 : Real.exp (-0.536) ≤ pxi r ^ (r-1) := pxi_pow_pred_lower r hr
  have hK2 : pxi r ^ (r-1) ≤ 0.732 := pxi_pow_pred_le r hr
  have hK3 : pxi r ^ r ≤ 0.5851 := le_trans (pxi_pow_r_le r hr) exp_neg_536_le
  have hK4 : (0.53:ℝ) ≤ pxi r ^ r := pxi_pow_r_ge r hr
  have hx_lo : (0.5847:ℝ) ≤ pxi r ^ (r-1) := le_trans exp_neg_536_ge hK1
  have hb6 : (1.06:ℝ) ≤ 2 * pxi r ^ r := by linarith
  have hbinv : (2 * pxi r ^ r)⁻¹ ≤ (1.06:ℝ)⁻¹ := inv_anti₀ (by norm_num) hb6
  set L : ℝ := Real.log (2 * r * d) with hL
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos; nlinarith [hrR, hdR]
  have hL4 : Real.log 4 ≤ L := by
    rw [hL]; apply Real.log_le_log (by norm_num); nlinarith [hrR, hdR]
  have hL1386 : (1.386:ℝ) ≤ L := by
    have h4 : (1.386:ℝ) ≤ Real.log 4 := by
      have h := Real.log_two_gt_d9
      rw [Real.log_four_eq]; linarith
    linarith
  have hL1 : (1:ℝ) ≤ L := le_trans (by norm_num) hL1386
  set D : ℝ := 2 * (r : ℝ) ^ r * 32 ^ (r + 1) * d * Real.log (2 * r * d) with hDdef
  have hD18 : (2:ℝ)^18 ≤ D := by
    have hrr : (4:ℝ) ≤ (r:ℝ)^r := by
      have hrw : (r:ℝ)^r = (r:ℝ)^(r-2) * (r:ℝ)^2 := by
        rw [← pow_add]; congr 1; omega
      have h1 : (4:ℝ) ≤ (r:ℝ)^2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hrR 2
        norm_num at h ⊢; linarith
      have h2 : (1:ℝ) ≤ (r:ℝ)^(r-2) := one_le_pow₀ (by linarith : (1:ℝ) ≤ (r:ℝ))
      rw [hrw]
      nlinarith [h1, h2, pow_nonneg (by linarith : (0:ℝ) ≤ (r:ℝ)) 2]
    have h32 : (32768:ℝ) ≤ 32^(r+1) := by
      have hrw : (32:ℝ)^(r+1) = 32^3 * 32^(r-2) := by
        rw [← pow_add]; congr 1; omega
      have h1 : (32768:ℝ) ≤ 32^3 := by norm_num
      have h2 : (1:ℝ) ≤ 32^(r-2) := one_le_pow₀ (by norm_num)
      rw [hrw]
      nlinarith [h1, h2]
    have hA : (8:ℝ) ≤ 2 * (r:ℝ)^r := by linarith
    have hkey : (262144:ℝ) ≤ 2 * (r:ℝ)^r * 32^(r+1) := by
      have h := mul_le_mul hA h32 (by positivity) (by positivity)
      norm_num at h
      exact h
    have hkey2 : (262144:ℝ) ≤ 2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) := by
      have h := mul_le_mul hkey hdR (by positivity) (by positivity)
      simpa using h
    have hkey3 : (262144:ℝ) ≤ 2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) * L := by
      have h := mul_le_mul hkey2 hL1 (by positivity) (by positivity)
      simpa using h
    have h218 : (2:ℝ)^18 = 262144 := by norm_num
    rw [hDdef, h218]
    exact hkey3
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num : (0:ℝ) < (2:ℝ)^18) hD18
  have hJc : ∀ J : ℕ, 1 ≤ J → 0.735 * pxi r ^ (r - 1 + r * J) ≤ 0.3148 := by
    intro J hJ1
    have hle : r ≤ r * J := Nat.le_mul_of_pos_right (m := J) r (by omega : 0 < J)
    have hpow : pxi r ^ (r * J) ≤ pxi r ^ r := pow_le_pow_of_le_one hxi_nonneg hxi_le1 hle
    rw [pow_add]
    have h1 : pxi r ^ (r - 1) * pxi r ^ (r * J) ≤ 0.732 * 0.5851 :=
      mul_le_mul hK2 (le_trans hpow hK3) (by positivity) (by norm_num)
    nlinarith [h1]
  have hbpg : ∀ J : ℕ, (2 * pxi r ^ r)⁻¹ ^ J ≤ (1.06:ℝ)⁻¹ ^ J :=
    fun J => pow_le_pow_left₀ (by positivity) hbinv J
  have hterm3 : 1.021 * (6.3 * pxi r ^ (r-1)) ≤ 4.7085 := by nlinarith [hK2]
  have hq03 : 1.021 * q ≤ 0.3 := by
    have hA : q ≤ (2 * pxi r ^ r)⁻¹ ^ J / r := hq1
    have hB : q ≤ (pxi r ^ r)⁻¹ ^ J / D := hq2
    have hD37 : (2:ℝ)^37 ≤ (r:ℝ)^19 * D := by
      have hr19 : (2:ℝ)^19 ≤ (r:ℝ)^19 := pow_le_pow_left₀ (by norm_num) hrR 19
      have h2 : (2:ℝ)^37 = (2:ℝ)^19 * (2:ℝ)^18 := by norm_num
      rw [h2]
      exact mul_le_mul hr19 hD18 (by norm_num) (by positivity)
    have hbase : (1:ℝ) ≤ (2:ℝ)^19 * (pxi r ^ r)^20 := by
      have h2 : (0.53:ℝ)^20 ≤ (pxi r ^ r)^20 := pow_le_pow_left₀ (by norm_num) hK4 20
      have h3 : (1:ℝ) ≤ (2:ℝ)^19 * (0.53:ℝ)^20 := by norm_num
      nlinarith [h2, h3]
    have huv : (((2 * pxi r ^ r)⁻¹)^J)^19 * ((pxi r ^ r)⁻¹)^J ≤ 1 := by
      have hid : (((2 * pxi r ^ r)⁻¹)^J)^19 * ((pxi r ^ r)⁻¹)^J
            = (((2:ℝ)^19 * (pxi r ^ r)^20)⁻¹)^J := by
        have e1 : (((2 * pxi r ^ r)⁻¹)^J)^19 = (((2 * pxi r ^ r)⁻¹)^19)^J := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]
        rw [e1, ← mul_pow, inv_pow, ← mul_inv]
        congr 1
        rw [mul_pow]
        ring
      rw [hid]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hbase)
    have hq20 : q^20 ≤ 1/(2:ℝ)^37 := by
      have hq19 : q^19 ≤ ((2 * pxi r ^ r)⁻¹ ^ J / r)^19 := pow_le_pow_left₀ hq0 hA 19
      have hstep : q^20 ≤ (((2 * pxi r ^ r)⁻¹ ^ J / r)^19) * ((pxi r ^ r)⁻¹ ^ J / D) := by
        calc q^20 = q^19 * q := by ring
          _ ≤ (((2 * pxi r ^ r)⁻¹ ^ J / r)^19) * ((pxi r ^ r)⁻¹ ^ J / D) :=
                mul_le_mul hq19 hB hq0 (by positivity)
      have hid2 : (((2 * pxi r ^ r)⁻¹ ^ J / r)^19) * ((pxi r ^ r)⁻¹ ^ J / D)
            = (((2 * pxi r ^ r)⁻¹) ^ J) ^ 19 * ((pxi r ^ r)⁻¹ ^ J) / ((r:ℝ)^19 * D) := by
        rw [div_pow, div_mul_div_comm]
      calc q^20 ≤ (((2 * pxi r ^ r)⁻¹ ^ J / r)^19) * ((pxi r ^ r)⁻¹ ^ J / D) := hstep
        _ ≤ 1 / ((r:ℝ)^19 * D) := by
              rw [hid2]
              apply div_le_div_of_nonneg_right huv (by positivity)
        _ ≤ 1/(2:ℝ)^37 := by
              apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hD37
    have h1 : (1.021 * q)^20 ≤ (0.3)^20 := by
      rw [mul_pow]
      calc (1.021:ℝ)^20 * q^20 ≤ 1.021^20 * (1/(2:ℝ)^37) :=
              mul_le_mul_of_nonneg_left hq20 (by norm_num)
        _ ≤ (0.3:ℝ)^20 := by norm_num
    exact (pow_le_pow_iff_left₀ (by linarith : (0:ℝ) ≤ 1.021*q) (by norm_num) (by norm_num)).mp h1
  constructor
  · -- ================= conjunct 1 (𝒥) =================
    by_cases hJ0 : J = 0
    · subst hJ0
      have hp0 : pxi r ^ (r - 1 + r * 0) = pxi r ^ (r - 1) := rfl
      rw [hp0, pow_zero]
      simp only [Nat.cast_zero, mul_zero, zero_div, mul_one, add_zero]
      linarith [hx_lo]
    · have hJpos : 1 ≤ J := Nat.one_le_iff_ne_zero.mpr hJ0
      have hth := hJc J hJpos
      have hneg : -12.43 * pxi r ^ (r-1) ≤ -12.43 * 0.5847 := by nlinarith [hx_lo]
      by_cases h12 : J ≤ 12
      · have hp : 5.646 * (2 * pxi r ^ r)⁻¹ ^ J ≤ 5.327 := by
          have hp1 : (2 * pxi r ^ r)⁻¹ ^ J ≤ (1.06:ℝ)⁻¹ := by
            calc (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹^J := hbpg J
              _ ≤ (1.06:ℝ)⁻¹^1 := pow_le_pow_of_le_one (a := (1.06:ℝ)⁻¹) (by norm_num) (by norm_num) hJpos
              _ = (1.06:ℝ)⁻¹ := pow_one _
          calc 5.646 * (2*pxi r^r)⁻¹^J ≤ 5.646 * (1.06:ℝ)⁻¹ := mul_le_mul_of_nonneg_left hp1 (by norm_num)
            _ ≤ 5.327 := by norm_num
        have hJL : 0.044 * (J:ℝ) / L ≤ 0.381 := by
          have ha := JL_le L hLpos hL1386 J 12 h12
          have hb : 0.044 * (12:ℝ) / 1.386 ≤ 0.381 := by norm_num
          linarith
        linarith [hth, hneg, hp, hJL]
      · have h13 : 13 ≤ J := by omega
        have hp : 5.646 * (2 * pxi r ^ r)⁻¹ ^ J ≤ 2.648 := by
          have hp1 : (2 * pxi r ^ r)⁻¹ ^ J ≤ (1.06:ℝ)⁻¹^13 := by
            calc (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹^J := hbpg J
              _ ≤ (1.06:ℝ)⁻¹^13 := pow_le_pow_of_le_one (a := (1.06:ℝ)⁻¹) (by norm_num) (by norm_num) h13
          calc 5.646 * (2*pxi r^r)⁻¹^J ≤ 5.646 * (1.06:ℝ)⁻¹^13 := mul_le_mul_of_nonneg_left hp1 (by norm_num)
            _ ≤ 2.648 := by norm_num
        have hJL : 0.044 * (J:ℝ) / L ≤ 2.2 := JL_le50 L hLpos J hJ
        linarith [hth, hneg, hp, hJL]
  · -- ================= conjunct 2 (ℐ) =================
    by_cases hJ0 : J = 0
    · subst hJ0
      have hp0 : pxi r ^ (r - 1 + r * 0) = pxi r ^ (r - 1) := rfl
      rw [hp0, pow_zero]
      simp only [Nat.cast_zero, mul_zero, zero_div, mul_one, add_zero]
      have hq2' : q ≤ 1 / D := by simpa using hq2
      have hq : q ≤ 0.000005 := by
        have h1 : 1 / D ≤ 1/(2:ℝ)^18 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hD18
        have h2 : (1:ℝ)/(2:ℝ)^18 ≤ 0.000005 := by norm_num
        linarith
      linarith [hK2, hq]
    · have hJpos : 1 ≤ J := Nat.one_le_iff_ne_zero.mpr hJ0
      have hth := hJc J hJpos
      have hbpgJ := hbpg J
      by_cases h1 : J = 1
      · have hp : 2.525 * (2 * pxi r ^ r)⁻¹ ^ J ≤ 2.383 := by
          have hp1 : (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹ ^ 1 := by
            calc (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹^J := hbpgJ
              _ = (1.06:ℝ)⁻¹^1 := by rw [h1]
          calc 2.525 * (2*pxi r^r)⁻¹^J ≤ 2.525 * (1.06:ℝ)⁻¹^1 := mul_le_mul_of_nonneg_left hp1 (by norm_num)
            _ ≤ 2.383 := by norm_num
        have hJL : 0.044 * (J:ℝ) / L ≤ 0.0318 := by
          have ha := JL_le L hLpos hL1386 J 1 (by omega)
          have hb : 0.044 * (1:ℝ) / 1.386 ≤ 0.0318 := by norm_num
          linarith
        linarith [hth, hterm3, hq03, hp, hJL]
      · have hJ2 : 2 ≤ J := by omega
        by_cases h2 : J = 2
        · have hp : 2.525 * (2 * pxi r ^ r)⁻¹ ^ J ≤ 2.248 := by
            have hp1 : (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹ ^ 2 := by
              calc (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹^J := hbpgJ
                _ = (1.06:ℝ)⁻¹^2 := by rw [h2]
            calc 2.525 * (2*pxi r^r)⁻¹^J ≤ 2.525 * (1.06:ℝ)⁻¹^2 := mul_le_mul_of_nonneg_left hp1 (by norm_num)
              _ ≤ 2.248 := by norm_num
          have hJL : 0.044 * (J:ℝ) / L ≤ 0.0635 := by
            have ha := JL_le L hLpos hL1386 J 2 (by omega)
            have hb : 0.044 * (2:ℝ) / 1.386 ≤ 0.0635 := by norm_num
            linarith
          linarith [hth, hterm3, hq03, hp, hJL]
        · have hJ3 : 3 ≤ J := by omega
          by_cases h3 : J = 3
          · have hp : 2.525 * (2 * pxi r ^ r)⁻¹ ^ J ≤ 2.121 := by
              have hp1 : (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹ ^ 3 := by
                calc (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹^J := hbpgJ
                  _ = (1.06:ℝ)⁻¹^3 := by rw [h3]
              calc 2.525 * (2*pxi r^r)⁻¹^J ≤ 2.525 * (1.06:ℝ)⁻¹^3 := mul_le_mul_of_nonneg_left hp1 (by norm_num)
                _ ≤ 2.121 := by norm_num
            have hJL : 0.044 * (J:ℝ) / L ≤ 0.0953 := by
              have ha := JL_le L hLpos hL1386 J 3 (by omega)
              have hb : 0.044 * (3:ℝ) / 1.386 ≤ 0.0953 := by norm_num
              linarith
            linarith [hth, hterm3, hq03, hp, hJL]
          · have hJ4 : 4 ≤ J := by omega
            by_cases h10 : J ≤ 10
            · have hp : 2.525 * (2 * pxi r ^ r)⁻¹ ^ J ≤ 2.001 := by
                have hp1 : (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹ ^ 4 := by
                  calc (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹^J := hbpgJ
                    _ ≤ (1.06:ℝ)⁻¹^4 := pow_le_pow_of_le_one (a := (1.06:ℝ)⁻¹) (by norm_num) (by norm_num) hJ4
                calc 2.525 * (2*pxi r^r)⁻¹^J ≤ 2.525 * (1.06:ℝ)⁻¹^4 := mul_le_mul_of_nonneg_left hp1 (by norm_num)
                  _ ≤ 2.001 := by norm_num
              have hJL : 0.044 * (J:ℝ) / L ≤ 0.3175 := by
                have ha := JL_le L hLpos hL1386 J 10 h10
                have hb : 0.044 * (10:ℝ) / 1.386 ≤ 0.3175 := by norm_num
                linarith
              linarith [hth, hterm3, hq03, hp, hJL]
            · have hJ11 : 11 ≤ J := by omega
              by_cases h30 : J ≤ 30
              · have hp : 2.525 * (2 * pxi r ^ r)⁻¹ ^ J ≤ 1.331 := by
                  have hp1 : (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹ ^ 11 := by
                    calc (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹^J := hbpgJ
                      _ ≤ (1.06:ℝ)⁻¹^11 := pow_le_pow_of_le_one (a := (1.06:ℝ)⁻¹) (by norm_num) (by norm_num) hJ11
                  calc 2.525 * (2*pxi r^r)⁻¹^J ≤ 2.525 * (1.06:ℝ)⁻¹^11 := mul_le_mul_of_nonneg_left hp1 (by norm_num)
                    _ ≤ 1.331 := by norm_num
                have hJL : 0.044 * (J:ℝ) / L ≤ 0.9524 := by
                  have ha := JL_le L hLpos hL1386 J 30 h30
                  have hb : 0.044 * (30:ℝ) / 1.386 ≤ 0.9524 := by norm_num
                  linarith
                linarith [hth, hterm3, hq03, hp, hJL]
              · have hJ31 : 31 ≤ J := by omega
                by_cases h60 : J ≤ 60
                · have hp : 2.525 * (2 * pxi r ^ r)⁻¹ ^ J ≤ 0.415 := by
                    have hp1 : (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹ ^ 31 := by
                      calc (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹^J := hbpgJ
                        _ ≤ (1.06:ℝ)⁻¹^31 := pow_le_pow_of_le_one (a := (1.06:ℝ)⁻¹) (by norm_num) (by norm_num) hJ31
                    calc 2.525 * (2*pxi r^r)⁻¹^J ≤ 2.525 * (1.06:ℝ)⁻¹^31 := mul_le_mul_of_nonneg_left hp1 (by norm_num)
                      _ ≤ 0.415 := by norm_num
                  have hJL : 0.044 * (J:ℝ) / L ≤ 1.9048 := by
                    have ha := JL_le L hLpos hL1386 J 60 h60
                    have hb : 0.044 * (60:ℝ) / 1.386 ≤ 1.9048 := by norm_num
                    linarith
                  linarith [hth, hterm3, hq03, hp, hJL]
                · have hJ61 : 61 ≤ J := by omega
                  have hp : 2.525 * (2 * pxi r ^ r)⁻¹ ^ J ≤ 0.073 := by
                    have hp1 : (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹ ^ 61 := by
                      calc (2*pxi r^r)⁻¹^J ≤ (1.06:ℝ)⁻¹^J := hbpgJ
                        _ ≤ (1.06:ℝ)⁻¹^61 := pow_le_pow_of_le_one (a := (1.06:ℝ)⁻¹) (by norm_num) (by norm_num) hJ61
                    calc 2.525 * (2*pxi r^r)⁻¹^J ≤ 2.525 * (1.06:ℝ)⁻¹^61 := mul_le_mul_of_nonneg_left hp1 (by norm_num)
                      _ ≤ 0.073 := by norm_num
                  have hJL : 0.044 * (J:ℝ) / L ≤ 2.2 := JL_le50 L hLpos J hJ
                  linarith [hth, hterm3, hq03, hp, hJL]

end Work.BW
