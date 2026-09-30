import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.cauchy_blaschke27
import Submission.Work.BW.jsum_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `extrap_core`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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

open Complex

/-! ## Auxiliary facts about the Blaschke product `F` of BW (27) -/

/-- `F(z) = ∏_{l ∈ Z} β(z;l)^{T'+1}`, the denominator of the integrand of BW (27).
Defined so that the proof can write `Fprod R Z Tp z` for the literal product. -/
noncomputable def Fprod (R : ℝ) (Z : Finset ℤ) (Tp : ℕ) (z : ℂ) : ℂ :=
  ∏ l ∈ Z, bfac R l z ^ (Tp + 1)

/-- BW §18: the Blaschke factor has modulus one on the circle `|z| = R`, for `|l| < R`. -/
lemma norm_bfac_eq_one {R : ℝ} {l : ℤ} {z : ℂ} (hR : 0 < R)
    (hl : ((|l| : ℤ) : ℝ) < R) (hz : ‖z‖ = R) : ‖bfac R l z‖ = 1 := by
  have h3 : ‖((l:ℝ):ℂ)‖ = ((|l|:ℤ):ℝ) := by
    rw [show ‖((l:ℝ):ℂ)‖ = |(l:ℝ)| from by simp, Int.cast_abs]
  have hzl : z - (l:ℂ) ≠ 0 := by
    intro h
    have hz1 : z = (l:ℂ) := sub_eq_zero.mp h
    have h4 : ‖z‖ = ‖((l:ℝ):ℂ)‖ := by rw [hz1, Complex.ofReal_intCast]
    have h5 : ((|l|:ℤ):ℝ) = R := by rw [← h3, ← h4, hz]
    rw [h5] at hl
    exact lt_irrefl _ hl
  have hzlpos : (0:ℝ) < ‖z - (l:ℂ)‖ := norm_pos_iff.mpr hzl
  have hnum : ‖(R:ℂ) * (z - (l:ℂ))‖ = R * ‖z - (l:ℂ)‖ := by
    rw [norm_mul]; congr 1; simp [hR.le]
  have hkey : (R:ℂ)^2 - (l:ℂ) * z = z * (starRingEnd ℂ) (z - (l:ℂ)) := by
    have hzz : z * (starRingEnd ℂ) z = (R:ℂ)^2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, Complex.ofReal_pow]
    rw [map_sub, mul_sub, hzz]
    rw [show (l:ℂ) = ((l:ℝ):ℂ) from (Complex.ofReal_intCast l).symm, Complex.conj_ofReal,
      mul_comm ((l:ℝ):ℂ) z]
  have hden : ‖(R:ℂ)^2 - (l:ℂ) * z‖ = R * ‖z - (l:ℂ)‖ := by
    rw [hkey, norm_mul, Complex.norm_conj, hz]
  rw [bfac, norm_div, hnum, hden]
  exact div_self (by positivity)

/-- `‖F(z)‖ = 1` on the circle `|z| = R`. -/
lemma norm_Fprod_eq_one {R : ℝ} {Z : Finset ℤ} {Tp : ℕ} {z : ℂ} (hR : 0 < R)
    (hZ : ∀ l ∈ Z, ((|l| : ℤ) : ℝ) < R) (hz : ‖z‖ = R) : ‖Fprod R Z Tp z‖ = 1 := by
  rw [Fprod, norm_prod]
  exact Finset.prod_eq_one fun l hl => by
    rw [norm_pow, norm_bfac_eq_one hR (hZ l hl) hz, one_pow]

/-- A single Blaschke factor does not vanish at `s` when `|l| < R`, `‖s‖ < R` and `s ≠ l`. -/
lemma bfac_ne_zero {R : ℝ} {l : ℤ} {s : ℂ} (hR : 0 < R)
    (hl : ((|l| : ℤ) : ℝ) < R) (hs : ‖s‖ < R) (hsl : s ≠ (l : ℂ)) :
    bfac R l s ≠ 0 := by
  have hden : (R : ℂ) ^ 2 - (l : ℂ) * s ≠ 0 := by
    intro h
    have h2 : (R:ℂ)^2 = (l:ℂ) * s := sub_eq_zero.mp h
    have hnorm : ‖(R:ℂ)^2‖ = ‖(l:ℂ) * s‖ := by rw [h2]
    have hRnorm : ‖(R:ℂ)‖ = R := by simp [abs_of_pos hR]
    have hlnorm : ‖(l:ℂ)‖ = ((|l|:ℤ):ℝ) := by rw [Complex.norm_intCast, Int.cast_abs]
    rw [norm_pow, norm_mul, hRnorm, hlnorm] at hnorm
    have hlt : ((|l|:ℤ):ℝ) * ‖s‖ < R * R := by
      rcases eq_or_lt_of_le (norm_nonneg s) with h0 | hpos
      · rw [← h0, mul_zero]; positivity
      · calc ((|l|:ℤ):ℝ) * ‖s‖ < R * ‖s‖ := mul_lt_mul_of_pos_right hl hpos
          _ ≤ R * R := mul_le_mul_of_nonneg_left hs.le hR.le
    nlinarith [hnorm, hlt]
  have hnum : (R : ℂ) * (s - (l : ℂ)) ≠ 0 := by
    refine mul_ne_zero (by simp [hR.ne']) (sub_ne_zero.mpr hsl)
  rw [bfac]
  exact div_ne_zero hnum hden

/-- `F(s) ≠ 0` under the hypotheses of BW §18 on the position of `s` and `Z`. -/
lemma Fprod_ne_zero {R : ℝ} {Z : Finset ℤ} {Tp : ℕ} {s : ℂ} (hR : 0 < R)
    (hZ : ∀ l ∈ Z, ((|l| : ℤ) : ℝ) < R) (hs : ‖s‖ < R) (hsl : ∀ l ∈ Z, s ≠ (l : ℂ)) :
    Fprod R Z Tp s ≠ 0 := by
  rw [Fprod, Finset.prod_ne_zero_iff]
  intro l hl
  exact pow_ne_zero _ (bfac_ne_zero hR (hZ l hl) hs (hsl l hl))

/-- BW §19, `𝓙`-side: the outer circle integral of (27) is bounded by `(R/δ)·‖f s‖·e^U`. -/
lemma norm_outer_le {f : ℂ → ℂ} {R δ U : ℝ} {Z : Finset ℤ} {Tp : ℕ} {s : ℂ}
    (hR : 0 < R) (hδ : 0 < δ) (hsR : ‖s‖ + δ ≤ R)
    (hZ : ∀ l ∈ Z, ((|l| : ℤ) : ℝ) < R)
    (hU : ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ ‖f s‖ * Real.exp U) :
    ‖(2 * Real.pi * Complex.I)⁻¹ *
        (∮ z in C(0, R), f z / ((z - s) * ∏ l ∈ Z, bfac R l z ^ (Tp + 1)))‖
      ≤ R * (‖f s‖ * Real.exp U / δ) := by
  have hsph : ∀ z ∈ Metric.sphere (0:ℂ) R,
      ‖f z / ((z - s) * ∏ l ∈ Z, bfac R l z ^ (Tp + 1))‖ ≤ ‖f s‖ * Real.exp U / δ := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    have hFz : ‖∏ l ∈ Z, bfac R l z ^ (Tp + 1)‖ = 1 := by
      rw [← Fprod]; exact norm_Fprod_eq_one hR hZ hz
    have hzs : δ ≤ ‖z - s‖ := by
      have h1 : ‖z‖ - ‖s‖ ≤ ‖z - s‖ := by
        have := norm_sub_norm_le z s; rw [hz] at this; linarith
      linarith
    rw [norm_div, norm_mul, hFz, mul_one]
    exact div_le_div₀ (by positivity) (hU z hz) hδ hzs
  have hthis := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z => f z / ((z - s) * ∏ l ∈ Z, bfac R l z ^ (Tp + 1)))
    (c := 0) (R := R) (C := ‖f s‖ * Real.exp U / δ) hR.le hsph
  rwa [smul_eq_mul] at hthis

/-- `‖f s / F(s)‖ ≥ ‖f s‖ e^W` from `‖F(s)‖ ≤ e^{-W}`. -/
lemma exp_W_mul_le {f : ℂ → ℂ} {s : ℂ} {W : ℝ} {Fs : ℂ} (hFs : 0 < ‖Fs‖)
    (hW : ‖Fs‖ ≤ Real.exp (-W)) :
    ‖f s‖ * Real.exp W ≤ ‖f s / Fs‖ := by
  have hW' : Real.exp W ≤ ‖Fs‖⁻¹ := by
    have h1 : Real.exp W = (Real.exp (-W))⁻¹ := by rw [Real.exp_neg, inv_inv]
    rw [h1]
    exact inv_anti₀ hFs hW
  rw [norm_div]
  calc ‖f s‖ * Real.exp W ≤ ‖f s‖ * ‖Fs‖⁻¹ := mul_le_mul_of_nonneg_left hW' (norm_nonneg _)
    _ = ‖f s‖ / ‖Fs‖ := by rw [div_eq_mul_inv]

/-- `|Z|(T'+1)·η/(κ-η)·e^{V+Y} < 1/2` from BW's second extrapolation condition. -/
lemma expVY_lt_half {Z : Finset ℤ} {Tp : ℕ} {κ η V Y : ℝ} (hη : 0 < η) (hκη : η < κ)
    (h2 : Real.log ((Z.card : ℝ) * (Tp + 1)) + Real.log (η / (κ - η)) + V + Y
      < -Real.log 2) :
    (Z.card : ℝ) * (Tp + 1) * (η / (κ - η)) * Real.exp (V + Y) < 1 / 2 := by
  have hηκ : 0 < η / (κ - η) := div_pos hη (by linarith)
  rcases Nat.eq_zero_or_pos Z.card with hc | hc
  · rw [hc]; norm_num
  · have hcard : (0:ℝ) < (Z.card : ℝ) := by exact_mod_cast hc
    have hA : (0:ℝ) < (Z.card : ℝ) * (Tp + 1) := by positivity
    have hC : (0:ℝ) < Real.exp (V + Y) := Real.exp_pos _
    have hmain : (0:ℝ) < (Z.card : ℝ) * (Tp + 1) * (η / (κ - η)) * Real.exp (V + Y) := by
      positivity
    have hlog : Real.log ((Z.card : ℝ) * (Tp + 1) * (η / (κ - η)) * Real.exp (V + Y))
        < Real.log (1 / 2) := by
      have hsplit : Real.log ((Z.card : ℝ) * (Tp + 1) * (η / (κ - η)) * Real.exp (V + Y))
          = Real.log ((Z.card : ℝ) * (Tp + 1)) + Real.log (η / (κ - η)) + (V + Y) := by
        rw [Real.log_mul (mul_ne_zero hA.ne' hηκ.ne') hC.ne', Real.log_mul hA.ne' hηκ.ne',
          Real.log_exp]
      rw [hsplit, Real.log_div one_ne_zero two_ne_zero, Real.log_one]
      linarith
    have hexp := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log hmain, Real.exp_log (by norm_num : (0:ℝ) < 1 / 2)] at hexp

/-- `(R/δ)·e^U < e^W/2` from BW's first extrapolation condition. -/
lemma expU_lt_half {R δ U W : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (h1 : Real.log (R / δ) + U - W < -Real.log 2) :
    (R / δ) * Real.exp U < (1 / 2) * Real.exp W := by
  have hRδ : 0 < R / δ := div_pos hR hδ
  have hlog : Real.log (R / δ) + U - W < Real.log (1 / 2) := by
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one]
    linarith
  have hexp : Real.exp (Real.log (R / δ) + U - W) < Real.exp (Real.log (1 / 2)) :=
    Real.exp_lt_exp.mpr hlog
  rw [Real.exp_sub, Real.exp_add, Real.exp_log hRδ,
    Real.exp_log (by norm_num : (0:ℝ) < 1 / 2)] at hexp
  rw [div_lt_iff₀ (Real.exp_pos W)] at hexp
  linarith [hexp]

/-- The extrapolation contradiction of BW §19 in abstract form: with `U` bounding `f` on `|z| = R` (from (16)/(18)), `V` bounding the `f_m(l)` (from (21)/(22)), `|F(s)| ≤ e^{-W}` (from (23)) and `|F(s)| ≤ |F(z)|e^Y` on the `C_l` (from (24)/(25)), the two conditions give `|𝒥|, |ℐ| < ½|f(s)/F(s)|`, contradicting (27) unless `f(s) = 0`. Uses `cauchy_blaschke27`, `bprod_circle`. -/
theorem extrap_core (f : ℂ → ℂ) (hf : Differentiable ℂ f) (R η κ δ : ℝ) (hη : 0 < η)
    (hη' : η < 1 / 2) (Z : Finset ℤ) (hZ : ∀ l ∈ Z, ((|l| : ℤ) : ℝ) + η < R) (Tp : ℕ) (s : ℂ)
    (hδ : 0 < δ) (hsR : ‖s‖ + δ ≤ R) (hκ : η < κ) (hsZ : ∀ l ∈ Z, κ ≤ ‖s - l‖)
    (U V W Y : ℝ)
    (hU : ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ ‖f s‖ * Real.exp U)
    (hV : ∀ l ∈ Z, ∀ m ≤ Tp, ‖taylorC f m l‖ ≤ ‖f s‖ * Real.exp V)
    (hW : ‖∏ l ∈ Z, bfac R l s ^ (Tp + 1)‖ ≤ Real.exp (-W))
    (hY : ∀ l ∈ Z, ∀ z : ℂ, ‖z - l‖ = η →
      ‖∏ l' ∈ Z, bfac R l' s ^ (Tp + 1)‖ ≤ ‖∏ l' ∈ Z, bfac R l' z ^ (Tp + 1)‖ * Real.exp Y)
    (h1 : Real.log (R / δ) + U - W < -Real.log 2)
    (h2 : Real.log ((Z.card : ℝ) * (Tp + 1)) + Real.log (η / (κ - η)) + V + Y < -Real.log 2) :
    f s = 0 := by
  have hR : 0 < R := by linarith [norm_nonneg s, hsR, hδ]
  have hsRlt : ‖s‖ < R := by linarith
  have hZR : ∀ l ∈ Z, ((|l| : ℤ) : ℝ) < R := fun l hl => by have := hZ l hl; linarith
  have hκη : 0 < κ - η := by linarith
  have hη1 : η ≤ 1 := by linarith
  have hsl : ∀ l ∈ Z, s ≠ (l : ℂ) := fun l hl h => by
    have h1 : ‖s - (l:ℂ)‖ = 0 := by rw [h, sub_self, norm_zero]
    have h2 := hsZ l hl
    rw [h1] at h2
    linarith
  have hFsne : Fprod R Z Tp s ≠ 0 := Fprod_ne_zero hR hZR hsRlt hsl
  have hFspos : 0 < ‖Fprod R Z Tp s‖ := norm_pos_iff.mpr hFsne
  have hFsne' : (∏ l ∈ Z, bfac R l s ^ (Tp + 1)) ≠ 0 := hFsne
  have hWpro : ‖Fprod R Z Tp s‖ ≤ Real.exp (-W) := hW
  by_cases hfs : f s = 0
  · exact hfs
  · exfalso
    have hfspos : 0 < ‖f s‖ := norm_pos_iff.mpr hfs
    set IA : ℂ := (2 * Real.pi * Complex.I)⁻¹ *
      (∮ z in C(0, R), f z / ((z - s) * ∏ l ∈ Z, bfac R l z ^ (Tp + 1))) with hIA
    set BJ : ℂ := ∑ l ∈ Z, ∑ m ∈ Finset.range (Tp + 1), taylorC f m l *
      ((2 * Real.pi * Complex.I)⁻¹ *
        ∮ z in C((l : ℂ), η), (z - l) ^ m / ((z - s) * ∏ l' ∈ Z, bfac R l' z ^ (Tp + 1)))
      with hJB
    have hI : ‖IA‖ < (1/2) * ‖f s / Fprod R Z Tp s‖ := by
      have hle : ‖IA‖ ≤ R * (‖f s‖ * Real.exp U / δ) := by
        rw [hIA]
        exact norm_outer_le hR hδ hsR hZR hU
      have hexp1 : (R / δ) * Real.exp U < (1/2) * Real.exp W := expU_lt_half hR hδ h1
      have hc : ‖f s‖ * Real.exp W ≤ ‖f s / Fprod R Z Tp s‖ :=
        exp_W_mul_le hFspos hWpro
      have hb : R * (‖f s‖ * Real.exp U / δ) = ‖f s‖ * ((R / δ) * Real.exp U) := by
        field_simp
      have hnum : R * (‖f s‖ * Real.exp U / δ) < (1/2) * ‖f s / Fprod R Z Tp s‖ := by
        rw [hb]
        calc ‖f s‖ * ((R / δ) * Real.exp U) < ‖f s‖ * ((1/2) * Real.exp W) :=
              mul_lt_mul_of_pos_left hexp1 hfspos
          _ = (1/2) * (‖f s‖ * Real.exp W) := by ring
          _ ≤ (1/2) * ‖f s / Fprod R Z Tp s‖ := mul_le_mul_of_nonneg_left hc (by norm_num)
      exact lt_of_le_of_lt hle hnum
    have hJ : ‖BJ‖ < (1/2) * ‖f s / Fprod R Z Tp s‖ := by
      have hle : ‖BJ‖ ≤ ((Z.card : ℝ) * (Tp + 1) * (η / (κ - η)) * Real.exp (V + Y)) *
          (‖f s‖ / ‖Fprod R Z Tp s‖) := by
        rw [hJB]
        simpa only [Fprod] using
          (jsum_bound f R η κ hη hη1 hκ Z Tp s V Y hsZ hV hY hFsne')
      have hA : (Z.card : ℝ) * (Tp + 1) * (η / (κ - η)) * Real.exp (V + Y) < 1/2 :=
        expVY_lt_half hη hκ h2
      have hx : (0:ℝ) < ‖f s / Fprod R Z Tp s‖ := by
        rw [norm_div]; positivity
      calc ‖BJ‖ ≤ ((Z.card : ℝ) * (Tp + 1) * (η / (κ - η)) * Real.exp (V + Y)) *
              (‖f s‖ / ‖Fprod R Z Tp s‖) := hle
        _ = ((Z.card : ℝ) * (Tp + 1) * (η / (κ - η)) * Real.exp (V + Y)) *
              ‖f s / Fprod R Z Tp s‖ := by rw [norm_div]
        _ < (1/2) * ‖f s / Fprod R Z Tp s‖ := mul_lt_mul_of_pos_right hA hx
    have h27 := cauchy_blaschke27 f hf R η hη hη' Z hZ Tp s hsRlt (fun l hl => by
      have := hsZ l hl; linarith)
    have hcontra : ‖f s / Fprod R Z Tp s‖ < ‖f s / Fprod R Z Tp s‖ := by
      have hx : ‖f s / Fprod R Z Tp s‖ = ‖IA - BJ‖ := by
        have h0 : f s / Fprod R Z Tp s = f s / ∏ l ∈ Z, bfac R l s ^ (Tp + 1) := by rw [Fprod]
        rw [h0, ← h27, hIA, hJB]
      calc ‖f s / Fprod R Z Tp s‖ = ‖IA - BJ‖ := hx
        _ ≤ ‖IA‖ + ‖BJ‖ := norm_sub_le IA BJ
        _ < (1/2) * ‖f s / Fprod R Z Tp s‖ + (1/2) * ‖f s / Fprod R Z Tp s‖ := add_lt_add hI hJ
        _ = ‖f s / Fprod R Z Tp s‖ := by ring
    exact (lt_irrefl _) hcontra

end Work.BW
