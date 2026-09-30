import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `num_blaschke_eta`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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


/-- Auxiliary numeric fact: `Real.log 608 ≤ 6.5`. -/
private lemma log_608_le : Real.log 608 ≤ 6.5 := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]; norm_num
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
  have h19 : Real.log 19 = Real.log 16 + Real.log (19/16) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hlog1916 : Real.log (19/16) ≤ 19/16 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have h608 : Real.log 608 = Real.log 32 + Real.log 19 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [h608, h19, h16, h32]; linarith

/-- Auxiliary: linear upper bound for `Real.log` on `[608, ∞)`. -/
private lemma log_le_lin (x : ℝ) (hx : 608 ≤ x) : Real.log x ≤ 5.5 + x / 608 := by
  have hx608 : 0 < x / 608 := by positivity
  have hprod : x = 608 * (x / 608) := by field_simp
  rw [hprod, Real.log_mul (by norm_num) (ne_of_gt hx608)]
  have hdiv : Real.log (x / 608) ≤ x / 608 - 1 := Real.log_le_sub_one_of_pos hx608
  have h608 := log_608_le
  linarith

/-- BW p. 54–58, the `η = 1/3` factors and the `S'` quantities: for `S' ≥ 608`, `T' ≥ 0`: `log(¾(4π/27)^{-(T'+1)}) ≤ 0·002S'(T'+1)`; `log((2S'+1)(S'(2e)^{S'})^{2(T'+1)}) ≤ 3·42S'(T'+1)`; `log(2S'(S'e^{S'})^{2(T'+1)}) ≤ 2·04S'(T'+1)` (BW's 3·41 and 2·03 are false at `S' = 608`, `T' = 0`: 3·419, 2·033; they hold for large `T'`); and `(23)` gives `(2S'+1)(T'+1) log 3·6 ≥ 2·6·297·log 3·6·x ≥ 16·13x` for `T'+1 ≥ 6·297x/…` (stated as `2 log 3·6 · 6·297 ≥ 16·13`, `2 log 7·2 · 6·297 ≥ 24·86`). -/
theorem num_blaschke_eta (Sp : ℝ) (hS : 608 ≤ Sp) (Tp : ℕ) :
    Real.log (3 / 4 * (4 * Real.pi / 27)⁻¹ ^ (Tp + 1)) ≤ 0.002 * Sp * (Tp + 1) ∧
      Real.log ((2 * Sp + 1) * (Sp * (2 * Real.exp 1) ^ Sp) ^ (2 * (Tp + 1))) ≤
        3.42 * Sp * (Tp + 1) ∧
      Real.log (2 * Sp * (Sp * Real.exp Sp) ^ (2 * (Tp + 1))) ≤ 2.04 * Sp * (Tp + 1) ∧
      16.13 ≤ 2 * 6.297 * Real.log 3.6 ∧ 24.86 ≤ 2 * 6.297 * Real.log 7.2 := by

  have hSp_pos : 0 < Sp := by linarith
  have hn0 : (0:ℝ) ≤ (↑Tp + 1) := by positivity
  have hn : (1:ℝ) ≤ (↑Tp + 1) := by
    have h : (0:ℝ) ≤ (Tp:ℝ) := Nat.cast_nonneg Tp
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1)
    have h34pos : (0:ℝ) < 3/4 := by norm_num
    have hbpos : (0:ℝ) < (4 * Real.pi / 27)⁻¹ := inv_pos.mpr (by positivity)
    rw [Real.log_mul (ne_of_gt h34pos) (ne_of_gt (pow_pos hbpos _)), Real.log_pow]
    push_cast
    have hlog34 : Real.log (3/4) ≤ -0.25 := by
      have h := Real.log_le_sub_one_of_pos h34pos
      linarith
    have hlogb : Real.log ((4 * Real.pi / 27)⁻¹) ≤ 1.216 := by
      have hb_eq : (4 * Real.pi / 27)⁻¹ = 27 / (4 * Real.pi) := by field_simp
      rw [hb_eq]
      have hpos : (0:ℝ) < 27 / (4 * Real.pi) := by positivity
      have hle := Real.log_le_sub_one_of_pos hpos
      have hpi : (3.14:ℝ) < Real.pi := Real.pi_gt_d2
      have hb2 : 27 / (4 * Real.pi) ≤ 2.216 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * Real.pi)]
        nlinarith
      linarith
    have hSp2 : (1.216:ℝ) ≤ 0.002 * Sp := by nlinarith
    nlinarith [hlog34, hlogb, hSp2, hn0]
  · -- (2)
    have h1pos : (0:ℝ) < 2*Sp+1 := by linarith
    have h2pos : (0:ℝ) < Sp * (2 * Real.exp 1) ^ Sp :=
      mul_pos hSp_pos (Real.rpow_pos_of_pos (by positivity) Sp)
    rw [Real.log_mul (ne_of_gt h1pos) (ne_of_gt (pow_pos h2pos _)), Real.log_pow]
    rw [Real.log_mul (ne_of_gt hSp_pos) (ne_of_gt (Real.rpow_pos_of_pos (by positivity) Sp))]
    rw [Real.log_rpow (by positivity : (0:ℝ) < 2 * Real.exp 1) Sp]
    push_cast
    rw [mul_add]
    have hlogSp : Real.log Sp ≤ 5.5 + Sp / 608 := log_le_lin Sp hS
    have hlog2e : Real.log (2 * Real.exp 1) ≤ 1.6931471808 := by
      have h : Real.log (2 * Real.exp 1) = Real.log 2 + 1 := by
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero 1), Real.log_exp]
      rw [h]; linarith [Real.log_two_lt_d9]
    have hlog2Sp1 : Real.log (2*Sp+1) ≤ 6.194 + Sp/608 := by
      have heq : 2*Sp+1 = 2*(Sp + 1/2) := by ring
      rw [heq, Real.log_mul (by norm_num) (by positivity)]
      have hSp_half : (608:ℝ) ≤ Sp + 1/2 := by linarith
      have hlin := log_le_lin (Sp + 1/2) hSp_half
      have h2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
      linarith
    have hb1 : 2*(↑Tp+1) * Real.log Sp ≤ 2*(↑Tp+1) * (5.5 + Sp/608) :=
      mul_le_mul_of_nonneg_left hlogSp (by positivity)
    have hb2 : 2*(↑Tp+1) * (Sp * Real.log (2*Real.exp 1)) ≤
        2*(↑Tp+1) * (Sp * 1.6931471808) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog2e hSp_pos.le) (by positivity)
    have hSpn1 : 608 * (↑Tp+1) ≤ Sp*(↑Tp+1) := mul_le_mul_of_nonneg_right hS hn0
    have hSpn2 : Sp ≤ Sp*(↑Tp+1) := by nlinarith [hSp_pos, hn]
    linarith [hb1, hb2, hlog2Sp1, hSpn1, hSpn2]
  · -- (3)
    have h2Sp : (0:ℝ) < 2*Sp := by linarith
    have hh : (0:ℝ) < Sp * Real.exp Sp := mul_pos hSp_pos (Real.exp_pos Sp)
    rw [Real.log_mul (ne_of_gt h2Sp) (ne_of_gt (pow_pos hh _)), Real.log_pow]
    rw [Real.log_mul (by norm_num) (ne_of_gt hSp_pos)]
    rw [Real.log_mul (ne_of_gt hSp_pos) (Real.exp_ne_zero Sp), Real.log_exp]
    push_cast
    rw [mul_add]
    have hlogSp : Real.log Sp ≤ 5.5 + Sp / 608 := log_le_lin Sp hS
    have hlog2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
    have hSpn1 : 608 * (↑Tp+1) ≤ Sp*(↑Tp+1) := mul_le_mul_of_nonneg_right hS hn0
    have hSpn2 : Sp ≤ Sp*(↑Tp+1) := by nlinarith [hSp_pos, hn]
    have hb1 : 2*(↑Tp+1) * Real.log Sp ≤ 2*(↑Tp+1) * (5.5 + Sp/608) :=
      mul_le_mul_of_nonneg_left hlogSp (by positivity)
    linarith [hlog2, hlogSp, hb1, hSpn1, hSpn2]
  · -- (4)
    have h36 : Real.log 3.6 = Real.log 2 + 2 * Real.log 3 - Real.log 5 := by
      have h1 : (3.6:ℝ) = 18/5 := by norm_num
      rw [h1, Real.log_div (by norm_num : (18:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]
      have h18 : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
        rw [show (18:ℝ) = 2 * 3^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
          Real.log_pow]
        norm_num
      rw [h18]
    rw [h36]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_lt_d9]
  · -- (5)
    have h72 : Real.log 7.2 = 2 * Real.log 2 + 2 * Real.log 3 - Real.log 5 := by
      have h1 : (7.2:ℝ) = 36/5 := by norm_num
      rw [h1, Real.log_div (by norm_num : (36:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]
      have h36 : Real.log 36 = 2 * Real.log 2 + 2 * Real.log 3 := by
        rw [show (36:ℝ) = 2^2 * 3^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
          Real.log_pow, Real.log_pow]
        norm_num
      rw [h36]
    rw [h72]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_lt_d9]


end Work.BW
