import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est13p
import Submission.Work.BW.est14
import Submission.Work.BW.est17
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.num_T
import Submission.Work.BW.num_kum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `est18`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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
  * `;
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

open Complex

private lemma main_arith {P d S D hp kk a0 lg lp X hh Ts : ℝ}
    (hP0 : 0 < P) (hd0 : 0 < d) (hS0 : 0 ≤ S) (hD0 : 0 ≤ D)
    (hp85 : hp ≤ 0.85 * S * D) (hlg : lg ≤ 0.001 * P * (S * D))
    (ha00 : 0 ≤ a0) :
    lp + hh * Ts + 0.204 * (1 / d) * S * D + 1.008 * X * D + lg
      + P * hp + P * ((1 - 1 / (P * d)) * (d * hh * Ts + 0.204 * S * D))
      + P * (1.007 * a0 * D) + P * (0.032 * S * D) + P * kk
      ≤ lp + P * (d * hh * Ts) + P * (1.087 * S * D)
        + 1.008 * X * D + P * (1.008 * a0 * D) + P * kk := by
  have hid : P * ((1 - 1 / (P * d)) * (d * hh * Ts + 0.204 * S * D))
      = P * (d * hh * Ts) + P * (0.204 * S * D) - hh * Ts - 0.204 * (1 / d) * S * D := by
    field_simp
    ring
  rw [hid]
  have hSD : 0 ≤ S * D := mul_nonneg hS0 hD0
  have ha0D : 0 ≤ a0 * D := mul_nonneg ha00 hD0
  have f4 : P * hp ≤ P * (0.85 * S * D) := mul_le_mul_of_nonneg_left hp85 hP0.le
  have f5 : P * (1.007 * a0 * D) ≤ P * (1.008 * a0 * D) := by
    have h : 1.007 * a0 * D ≤ 1.008 * a0 * D := by nlinarith [ha0D]
    exact mul_le_mul_of_nonneg_left h hP0.le
  linarith [hlg, f4, f5, hSD]

private lemma side_arith {P d S D hh Ts hp kk a0 lg : ℝ}
    (hP0 : 0 < P) (hP4 : 4 ≤ P) (hd0 : 0 < d) (hd1 : 1 ≤ d) (hS0 : 0 ≤ S) (hD0 : 0 ≤ D)
    (hp85 : hp ≤ 0.85 * S * D) (hlg : lg ≤ 0.001 * P * (S * D))
    (hk22 : kk ≤ 2.2 * (S * D)) (ha02 : a0 ≤ 2 * S) (ha00 : 0 ≤ a0)
    (hdT : P * d * hh * Ts ≤ 0.735 * P * (S * D)) :
    hh * Ts + 0.205 * (1 / d) * S * D + 1.01 * a0 * D + P * hp
      + P * ((1 - 1 / (P * d)) * (d * hh * Ts + 0.204 * S * D))
      + P * (1.007 * a0 * D) + P * (0.032 * S * D) + P * kk + lg ≤ 9 * P * S * D := by
  have hid : P * ((1 - 1 / (P * d)) * (d * hh * Ts + 0.204 * S * D))
      = P * (d * hh * Ts) + P * (0.204 * S * D) - hh * Ts - 0.204 * (1 / d) * S * D := by
    field_simp
    ring
  rw [hid]
  have hSD : 0 ≤ S * D := mul_nonneg hS0 hD0
  have ha0D : 0 ≤ a0 * D := mul_nonneg ha00 hD0
  have hinv : 1 / d ≤ 1 := by
    rw [div_le_iff₀ hd0]
    linarith
  have f2 : 0.001 * (1 / d) * S * D ≤ 0.001 * S * D := by
    have h : (1 / d) * (S * D) ≤ 1 * (S * D) := mul_le_mul_of_nonneg_right hinv hSD
    linarith [h]
  have f4 : P * hp ≤ P * (0.85 * S * D) := mul_le_mul_of_nonneg_left hp85 hP0.le
  have f6 : 1.01 * a0 * D ≤ 1.01 * (2 * S) * D :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha02 (by norm_num)) hD0
  have f7 : P * (1.007 * a0 * D) ≤ P * (1.007 * (2 * S) * D) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha02 (by norm_num)) hD0) hP0.le
  have f8 : P * kk ≤ P * (2.2 * (S * D)) := mul_le_mul_of_nonneg_left hk22 hP0.le
  have hP4SD : 4 * (S * D) ≤ P * (S * D) := mul_le_mul_of_nonneg_right hP4 hSD
  nlinarith [hlg, f2, f4, f6, f7, f8, hSD, hP4SD, hdT]


/-- BW (18) at level `J` (p. 46, p. 58): for integer `s`, `2^{-J}|s| ≤ 4S`, `g(s/2) ≠ 0`: `log|f(z)/f(s/2)| ≤ 2^r{dhT* + 1·087SD + 1·008·2^{-J}(|z/2^r| + |s/2|)D + kum_J}`. From `est13`, `est14`, `est17`, (12). -/
theorem est18 {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) (μ : Fin r → ℕ) (Tst : ℝ) (hTst : Tst ≤ acT K σ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (s : ℤ)
    (hs : ((|s| : ℤ) : ℝ) / 2 ^ J ≤ 4 * acS K r b v) (hg : acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2) ≠ 0) (z : ℂ) :
    ‖acf φ α b k L ι v σ p J μ t0 t z‖ ≤ ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ *
      Real.exp (2 ^ r * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 1.087 * acS K r b v * acD K σ +
        1.008 * ((‖z‖ / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * acD K σ + kumJ K b v σ J)) := by
  have hr : 2 ≤ r := H.hr
  have hdNat : 1 ≤ dK K := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp Module.finrank_pos)
  have hd1 : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hdNat
  have hd0 : (0 : ℝ) < (dK K : ℝ) := by linarith
  have hP0 : (0 : ℝ) < 2 ^ r := by positivity
  have hP4 : (4 : ℝ) ≤ 2 ^ r := by
    have h : (2:ℝ) ^ 2 ≤ (2:ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
    norm_num at h
    linarith
  have hP1 : (1 : ℝ) ≤ 2 ^ r := by linarith [hP4]
  have h19 : 19 ≤ acH K b v := (acH_lower H).1
  have hhpos : (0 : ℝ) < (acH K b v : ℝ) := by
    have : (0:ℕ) < acH K b v := by omega
    exact_mod_cast this
  have hSpos : (0 : ℝ) < acS K r b v := by
    have : (0:ℕ) < pS r (dK K) (acH K b v) := by
      rw [pS]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) hdNat) (by omega)
    simpa [acS] using (show (0:ℝ) < (pS r (dK K) (acH K b v) : ℝ) by exact_mod_cast this)
  have hS0 : (0 : ℝ) ≤ acS K r b v := le_of_lt hSpos
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hlogpos : 0 < Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
    apply Real.log_pos
    have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [h2, hd1]
  have hDlow := (num_D_lower hr hdNat σ hσ).1
  have hDpos : (0 : ℝ) < acD K σ := by
    have hpos : (0:ℝ) < 2 * (r : ℝ) ^ r * 32 ^ (r + 1) * (dK K : ℝ) * Real.log (2 * r * (dK K)) := by
      have : (0:ℝ) < (r:ℝ) ^ r := by positivity
      positivity
    show (0:ℝ) < pD r (dK K) σ
    linarith [hDlow, hpos]
  have hD0 : (0 : ℝ) ≤ acD K σ := le_of_lt hDpos
  have hSD0 : (0 : ℝ) ≤ acS K r b v * acD K σ := mul_nonneg hS0 hD0
  have hlg : Real.log 2 ≤ 0.001 * 2 ^ r * (acS K r b v * acD K σ) := by
    have h := (num_kum hr hdNat h19 σ hσ J).2.2
    have h1 : 0.001 * acS K r b v * acD K σ ≤ 0.001 * 2 ^ r * (acS K r b v * acD K σ) := by
      nlinarith [hP1, hSD0]
    linarith [h, h1]
  have hk22 : kumJ K b v σ J ≤ 2.2 * (acS K r b v * acD K σ) := by
    have hJle : (J : ℝ) ≤ 50 * Real.log (2 * (r:ℝ) * (dK K:ℝ)) := by
      have h := Nat.floor_le (show (0:ℝ) ≤ 50 * Real.log (2 * (r:ℝ) * (dK K:ℝ)) by positivity)
      have hpi : pI r (dK K) = ⌊50 * Real.log (2 * (r:ℝ) * (dK K:ℝ))⌋₊ := rfl
      rw [hpi] at hJ
      exact le_trans (by exact_mod_cast hJ) h
    have hJD : (J : ℝ) / Real.log (2 * (r:ℝ) * (dK K:ℝ)) ≤ 50 := by
      rw [div_le_iff₀ hlogpos]
      linarith [hJle]
    calc kumJ K b v σ J
        = 0.044 * ((J : ℝ) / Real.log (2 * (r:ℝ) * (dK K:ℝ))) * (acS K r b v * acD K σ) := by
          simp only [kumJ]; ring
      _ ≤ 0.044 * 50 * (acS K r b v * acD K σ) := by
          have h1 := mul_le_mul_of_nonneg_right hJD (by norm_num : (0:ℝ) ≤ 0.044)
          have h2 := mul_le_mul_of_nonneg_right h1 hSD0
          linarith [h2]
      _ = 2.2 * (acS K r b v * acD K σ) := by norm_num
  have hdhT : (dK K : ℝ) * (acH K b v : ℝ) * Tst ≤ 0.735 * (acS K r b v * acD K σ) := by
    have hTtight := (num_T hr hdNat h19 σ hσ).2.2.1
    have h1 : (dK K : ℝ) * (acH K b v : ℝ) * Tst ≤
        (dK K : ℝ) * (acH K b v : ℝ) * acT K σ :=
      mul_le_mul_of_nonneg_left hTst (mul_nonneg hd0.le (le_of_lt hhpos))
    have h2 : acT K σ = (pT r (dK K) σ : ℝ) := rfl
    rw [h2] at h1
    linarith [h1, hTtight]
  have hdT : 2 ^ r * (dK K : ℝ) * (acH K b v : ℝ) * Tst ≤ 0.735 * 2 ^ r * (acS K r b v * acD K σ) := by
    have h := mul_le_mul_of_nonneg_left hdhT hP0.le
    linarith [h]
  have ha02 : ((((|s| : ℤ) : ℝ) / 2) / 2 ^ J) ≤ 2 * acS K r b v := by
    have h : ((|s| : ℤ) : ℝ) / 2 ^ J * (1 / 2) ≤ 4 * acS K r b v * (1 / 2) :=
      mul_le_mul_of_nonneg_right hs (by norm_num : (0:ℝ) ≤ 1/2)
    have e1 : ((|s| : ℤ) : ℝ) / 2 ^ J * (1 / 2) = (((|s| : ℤ) : ℝ) / 2) / 2 ^ J := by ring
    have e2 : 4 * acS K r b v * (1 / 2) = 2 * acS K r b v := by ring
    linarith [h, e1, e2]
  have ha00 : (0 : ℝ) ≤ (((|s| : ℤ) : ℝ) / 2) / 2 ^ J := by positivity
  have hnorm : ‖(s : ℂ) / 2‖ = ((|s| : ℤ) : ℝ) / 2 := by
    rw [norm_div, Complex.norm_intCast, Int.cast_abs]
    norm_num
  have hnorm' : ‖(s : ℂ) / 2‖ / 2 ^ J = (((|s| : ℤ) : ℝ) / 2) / 2 ^ J := by rw [hnorm]
  have hUp := est13p H J μ Tst hTst t0 t ht z
  have hB17 := est17 H J μ Tst hTst t0 t ht s hg
  have hC14 := est14 H J hJ μ Tst hTst t0 t ht ((s : ℂ) / 2)
  rw [hnorm'] at hC14
  have hside := side_arith (P := (2:ℝ)^r) (d := (dK K : ℝ)) (S := acS K r b v)
      (D := acD K σ) (hh := (acH K b v : ℝ)) (Ts := Tst) (hp := Height.logHeight p)
      (kk := kumJ K b v σ J) (a0 := (((|s| : ℤ) : ℝ) / 2) / 2 ^ J) (lg := Real.log 2)
      hP0 hP4 hd0 hd1 hS0 hD0 H.hp12 hlg hk22 ha02 ha00 hdT
  have hBsplit : lnp φ p - 2 ^ r * (Height.logHeight p +
        (1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J)
      = lnp φ p - (2 ^ r * Height.logHeight p
        + 2 ^ r * ((1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ))
        + 2 ^ r * (1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ) + 2 ^ r * (0.032 * acS K r b v * acD K σ)
        + 2 ^ r * kumJ K b v σ J) := by ring
  have hCsplit : lnp φ p + (acH K b v : ℝ) * Tst +
        (0.205 * (1 / (dK K : ℝ)) + 1.01 * ((((|s| : ℤ) : ℝ) / 2) / 2 ^ J) / acS K r b v - 9 * 2 ^ r) *
          (acS K r b v * acD K σ) + Real.log 2
      = lnp φ p + (acH K b v : ℝ) * Tst + 0.205 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ
        + 1.01 * ((((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * acD K σ - 9 * 2 ^ r * (acS K r b v * acD K σ)
        + Real.log 2 := by
    field_simp
    ring
  have hside' : lnp φ p + (acH K b v : ℝ) * Tst +
        (0.205 * (1 / (dK K : ℝ)) + 1.01 * ((((|s| : ℤ) : ℝ) / 2) / 2 ^ J) / acS K r b v - 9 * 2 ^ r) *
          (acS K r b v * acD K σ) + Real.log 2
      ≤ lnp φ p - 2 ^ r * (Height.logHeight p +
        (1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J) := by
    linarith [hside, hCsplit, hBsplit]
  have hmain : (lnp φ p + (acH K b v : ℝ) * Tst + 0.204 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ +
        1.008 * (‖z‖ / 2 ^ J) * acD K σ) + Real.log 2
      ≤ (lnp φ p - 2 ^ r * (Height.logHeight p +
        (1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J))
      + 2 ^ r * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 1.087 * acS K r b v * acD K σ +
        1.008 * ((‖z‖ / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * acD K σ + kumJ K b v σ J) := by
    have h2 : 2 ^ r * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 1.087 * acS K r b v * acD K σ +
        1.008 * ((‖z‖ / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * acD K σ + kumJ K b v σ J)
        = 2 ^ r * ((dK K : ℝ) * (acH K b v : ℝ) * Tst) + 2 ^ r * (1.087 * acS K r b v * acD K σ)
          + 1.008 * (‖z‖ / 2 ^ J) * acD K σ + 2 ^ r * (1.008 * ((((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * acD K σ)
          + 2 ^ r * kumJ K b v σ J := by
      field_simp
      ring
    have hma := main_arith (P := (2:ℝ)^r) (d := (dK K : ℝ)) (S := acS K r b v)
        (D := acD K σ) (hh := (acH K b v : ℝ)) (Ts := Tst) (hp := Height.logHeight p)
        (kk := kumJ K b v σ J) (a0 := (((|s| : ℤ) : ℝ) / 2) / 2 ^ J) (lg := Real.log 2)
        (lp := lnp φ p) (X := ‖z‖ / 2 ^ J) hP0 hd0 hS0 hD0 H.hp12 hlg ha00
    linarith [hma, h2, hBsplit]
  have hLow : Real.exp (lnp φ p - 2 ^ r * (Height.logHeight p +
        (1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J) -
        Real.log 2) ≤ ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ := by
    have htri : ‖acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ ≤
        ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ +
        ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2) - acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ := by
      have h := norm_sub_le (acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2))
        (acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2) - acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2))
      simpa [sub_sub_cancel] using h
    have hexp_le : Real.exp (lnp φ p + (acH K b v : ℝ) * Tst +
        (0.205 * (1 / (dK K : ℝ)) + 1.01 * ((((|s| : ℤ) : ℝ) / 2) / 2 ^ J) / acS K r b v - 9 * 2 ^ r) *
          acS K r b v * acD K σ)
        ≤ Real.exp (lnp φ p - 2 ^ r * (Height.logHeight p +
        (1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J) -
        Real.log 2) := by
      rw [Real.exp_le_exp]
      linarith [hside']
    have hexp2 : Real.exp (lnp φ p - 2 ^ r * (Height.logHeight p +
        (1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J) -
        Real.log 2)
        = Real.exp (lnp φ p - 2 ^ r * (Height.logHeight p +
        (1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J)) / 2 := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    linarith [hB17, hC14, hexp_le, htri, hexp2]
  have hUp' : ‖acf φ α b k L ι v σ p J μ t0 t z‖ ≤
      Real.exp (lnp φ p + (acH K b v : ℝ) * Tst + 0.204 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ +
        1.008 * (‖z‖ / 2 ^ J) * acD K σ) := hUp
  calc ‖acf φ α b k L ι v σ p J μ t0 t z‖
      ≤ Real.exp (lnp φ p + (acH K b v : ℝ) * Tst + 0.204 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ +
          1.008 * (‖z‖ / 2 ^ J) * acD K σ) := hUp'
    _ ≤ Real.exp ((lnp φ p - 2 ^ r * (Height.logHeight p +
          (1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
          1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J) -
          Real.log 2) +
        2 ^ r * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 1.087 * acS K r b v * acD K σ +
          1.008 * ((‖z‖ / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * acD K σ + kumJ K b v σ J)) := by
        rw [Real.exp_le_exp]
        linarith [hmain]
    _ = Real.exp (lnp φ p - 2 ^ r * (Height.logHeight p +
          (1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
          1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J) -
          Real.log 2) *
        Real.exp (2 ^ r * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 1.087 * acS K r b v * acD K σ +
          1.008 * ((‖z‖ / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * acD K σ + kumJ K b v σ J)) :=
        Real.exp_add _ _
    _ ≤ ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ *
        Real.exp (2 ^ r * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 1.087 * acS K r b v * acD K σ +
          1.008 * ((‖z‖ / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * acD K σ + kumJ K b v σ J)) :=
        mul_le_mul_of_nonneg_right hLow (Real.exp_nonneg _)


end Work.BW
