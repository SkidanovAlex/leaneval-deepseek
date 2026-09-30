import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `bprod_circle`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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

/-! ### Helper lemmas for `bprod_real_le`

Writing the Blaschke factor on the real axis, pairing `k` with `-k`. -/

/-- `bfac` on the real axis, as a cast of a real number. -/
lemma bfac_ofReal (R : ℝ) (k : ℤ) (x : ℝ) :
    bfac R k (x:ℂ) = ((R*(x - (k:ℝ))/(R^2 - (k:ℝ)*x) : ℝ) : ℂ) := by
  unfold bfac; push_cast; ring

/-- The algebraic core of the pairing bound: for `x², k² ≤ R²`,
`R⁴| x² - k² | ≤ max(x²,k²)(R⁴ - k²x²)`. -/
lemma pair_core (x k R : ℝ) (hx : x^2 ≤ R^2) (hk : k^2 ≤ R^2) :
    R^4 * |x^2 - k^2| ≤ max (x^2) (k^2) * (R^4 - k^2*x^2) := by
  have hx0 : 0 ≤ x^2 := sq_nonneg x
  have hk0 : 0 ≤ k^2 := sq_nonneg k
  rcases le_total (x^2) (k^2) with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]
    have hk4 : (k^2)^2 ≤ (R^2)^2 := pow_le_pow_left₀ hk0 hk 2
    nlinarith [hk4, sq_nonneg x]
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]
    have hx4 : (x^2)^2 ≤ (R^2)^2 := pow_le_pow_left₀ hx0 hx 2
    nlinarith [hx4, sq_nonneg k]

/-- Pairing `k` with `-k`: `|β(x;k)β(x;−k)| ≤ (max(|x|,|k|)/R)²`. -/
lemma pair_aux (R : ℝ) (hR : 0 < R) (x t : ℝ) (hx : |x| ≤ R) (ht : |t| < R) :
    ‖((R*(x-t)/(R^2-t*x) : ℝ) : ℂ) * ((R*(x+t)/(R^2+t*x) : ℝ) : ℂ)‖
      ≤ (max |x| |t| / R)^2 := by
  have hx2 : x^2 ≤ R^2 := by
    have h1 : |x|^2 ≤ R^2 := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [sq_abs] at h1
  have ht2 : t^2 ≤ R^2 := by
    have h1 : |t|^2 ≤ R^2 := pow_le_pow_left₀ (abs_nonneg t) (le_of_lt ht) 2
    rwa [sq_abs] at h1
  have hsmall : abs t * abs x < R^2 := by
    have h3 : abs t * abs x ≤ abs t * R := by nlinarith [abs_nonneg t, hx]
    have h4 : abs t * R < R*R := mul_lt_mul_of_pos_right ht hR
    nlinarith [h3, h4]
  have hA : 0 < R^2 - t*x := by
    have h1 : t*x ≤ abs t * abs x := by
      have hh := le_abs_self (t*x); rwa [abs_mul] at hh
    linarith
  have hB : 0 < R^2 + t*x := by
    have h1 : -(abs t * abs x) ≤ t*x := by
      have hh := neg_abs_le (t*x); rwa [abs_mul] at hh
    linarith
  have hdenpos : 0 < R^4 - t^2*x^2 := by
    have : R^4 - t^2*x^2 = (R^2-t*x)*(R^2+t*x) := by ring
    rw [this]; exact mul_pos hA hB
  have hval : (R*(x-t)/(R^2-t*x)) * (R*(x+t)/(R^2+t*x))
      = R^2*(x^2-t^2)/(R^4-t^2*x^2) := by
    rw [show R^4 - t^2*x^2 = (R^2-t*x)*(R^2+t*x) by ring]
    field_simp
    ring
  have hcast : ‖((R*(x-t)/(R^2-t*x) : ℝ) : ℂ) * ((R*(x+t)/(R^2+t*x) : ℝ) : ℂ)‖
      = |(R*(x-t)/(R^2-t*x)) * (R*(x+t)/(R^2+t*x))| := by
    rw [← Complex.ofReal_mul]; exact RCLike.norm_ofReal _
  rw [hcast, hval]
  have habs : |R^2*(x^2-t^2)/(R^4-t^2*x^2)| = R^2*|x^2-t^2|/(R^4-t^2*x^2) := by
    rw [abs_div, abs_mul, abs_of_pos hdenpos, abs_of_pos (by positivity)]
  rw [habs]
  have hmax : max (|x|^2) (|t|^2) = (max |x| |t|)^2 := by
    rcases le_total |x| |t| with h | h
    · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (abs_nonneg x) h 2)]
    · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ (abs_nonneg t) h 2)]
  have htarget : (max |x| |t| / R)^2 = max (x^2) (t^2)/R^2 := by
    rw [div_pow, ← hmax, sq_abs, sq_abs]
  rw [htarget]
  have hcore := pair_core x t R hx2 ht2
  rw [div_le_div_iff₀ hdenpos (by positivity : (0:ℝ) < R^2)]
  nlinarith [hcore]

/-- `|β(x;k)β(x;−k)| ≤ (max(|x|,|k|)/R)²` for a pair of opposite integers. -/
lemma bfac_pair_bound (R : ℝ) (hR : 0 < R) (x : ℝ) (hx : |x| ≤ R) (k : ℤ)
    (hk : |(k:ℝ)| < R) :
    ‖bfac R k (x:ℂ) * bfac R (-k) (x:ℂ)‖ ≤ (max |x| |(k:ℝ)| / R)^2 := by
  have h1 : bfac R k (x:ℂ) = ((R*(x-(k:ℝ))/(R^2-(k:ℝ)*x) : ℝ):ℂ) := bfac_ofReal R k x
  have h2 : bfac R (-k) (x:ℂ) = ((R*(x+(k:ℝ))/(R^2+(k:ℝ)*x) : ℝ):ℂ) := by
    rw [bfac_ofReal]; push_cast; ring
  rw [h1, h2]
  exact pair_aux R hR x (k:ℝ) hx hk

/-- The `k = 0` factor: `|β(x;0)| = |x|/R`. -/
lemma bfac_zero (R : ℝ) (hR : 0 < R) (x : ℝ) :
    ‖bfac R 0 (x:ℂ)‖ = |x| / R := by
  have h : bfac R 0 (x:ℂ) = ((x/R : ℝ):ℂ) := by
    rw [bfac_ofReal]
    simp only [Int.cast_zero, sub_zero, zero_mul]
    congr 1
    field_simp
  rw [h]
  rw [show ‖((x/R : ℝ):ℂ)‖ = |x/R| from RCLike.norm_ofReal _]
  rw [abs_div, abs_of_pos hR]

/-- Recursion for `bprod`: adjoining the two new indices `±(n+1)`. -/
lemma bprod_peel (R : ℝ) (x : ℂ) (n : ℕ) :
    bprod R (n+1) x = bfac R ((n:ℤ)+1) x * bfac R (-((n:ℤ)+1)) x * bprod R n x := by
  have hR : insert ((n:ℤ)+1) (Finset.Icc (-(n:ℤ)) (n:ℤ))
      = Finset.Icc (-(n:ℤ)) ((n:ℤ)+1) :=
    Finset.insert_Icc_right_eq_Icc_add_one (a := -(n:ℤ)) (b := (n:ℤ)) (by omega)
  have hL : insert (-(n:ℤ) - 1) (Finset.Icc (-(n:ℤ)) ((n:ℤ)+1))
      = Finset.Icc (-(n:ℤ) - 1) ((n:ℤ)+1) :=
    Finset.insert_Icc_left_eq_Icc_sub_one (a := -(n:ℤ)) (b := (n:ℤ)+1) (by omega)
  have h1 : Finset.Icc (-((n+1 : ℕ) : ℤ)) ((n+1 : ℕ) : ℤ)
      = insert (-(n:ℤ)-1) (insert ((n:ℤ)+1) (Finset.Icc (-(n:ℤ)) (n:ℤ))) := by
    rw [show ((n+1 : ℕ) : ℤ) = (n:ℤ)+1 by push_cast; ring]
    rw [show (-((n:ℤ)+1) : ℤ) = -(n:ℤ)-1 by ring]
    rw [← hL, ← hR]
  unfold bprod
  rw [h1]
  rw [Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega)]
  rw [Finset.prod_insert (by simp only [Finset.mem_Icc]; omega)]
  rw [show (-(n:ℤ)-1 : ℤ) = -((n:ℤ)+1) by ring]
  ring

/-- The odd indices in `[-M-2, M+2]` are those in `[-M,M]` together with `±(M+1)` (`M` even). -/
lemma odd_filter_peel (M : ℤ) (hM0 : 0 ≤ M) (hM : Even M) :
    (Finset.Icc (-(M+2)) (M+2)).filter Odd =
      insert (M+1) (insert (-(M+1)) ((Finset.Icc (-M) M).filter Odd)) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
  obtain ⟨s, hs⟩ := hM
  constructor
  · rintro ⟨⟨h1, h2⟩, hodd⟩
    obtain ⟨t, ht⟩ := hodd
    by_cases hk : k = M+1
    · exact Or.inl hk
    by_cases hk2 : k = -(M+1)
    · exact Or.inr (Or.inl hk2)
    · exact Or.inr (Or.inr ⟨⟨by omega, by omega⟩, ⟨t, ht⟩⟩)
  · rintro (hcase | hcase | ⟨⟨h1, h2⟩, hodd⟩)
    · subst hcase
      exact ⟨⟨by omega, by omega⟩, ⟨s, by omega⟩⟩
    · subst hcase
      exact ⟨⟨by omega, by omega⟩, ⟨-s-1, by omega⟩⟩
    · exact ⟨⟨by omega, by omega⟩, hodd⟩

/-- Recursion for `bprodOdd`: adjoining the two new odd indices `±(2m+1)`. -/
lemma bprodOdd_peel (R : ℝ) (x : ℂ) (m : ℕ) :
    bprodOdd R (2*m+2) x
      = bfac R (((2*m+1 : ℕ)):ℤ) x * bfac R (-(((2*m+1:ℕ)):ℤ)) x * bprodOdd R (2*m) x := by
  have hM0 : (0:ℤ) ≤ ((2*m:ℕ):ℤ) := by positivity
  have hMeven : Even (((2*m:ℕ)):ℤ) := by
    refine ⟨(m:ℤ), ?_⟩; push_cast; ring
  have hpeel := odd_filter_peel (((2*m:ℕ)):ℤ) hM0 hMeven
  have hc2 : (((2*m+2:ℕ)):ℤ) = ((2*m:ℕ):ℤ)+2 := by push_cast; ring
  have hc1 : (((2*m+1:ℕ)):ℤ) = ((2*m:ℕ):ℤ)+1 := by push_cast; ring
  unfold bprodOdd
  rw [show (-(((2*m+2:ℕ)):ℤ)) = -(((2*m:ℕ):ℤ)+2) by rw [hc2]]
  rw [hc2]
  rw [hpeel]
  rw [Finset.prod_insert (by
        rw [Finset.mem_insert]
        rintro (h | h)
        · omega
        · rw [Finset.mem_filter, Finset.mem_Icc] at h; omega)]
  rw [Finset.prod_insert (by
        rw [Finset.mem_filter, Finset.mem_Icc]
        rintro ⟨⟨h1, h2⟩, ho⟩
        omega)]
  rw [hc1]; ring

/-- BW (23) and its lacunary analogue (p. 52): for real `|x| ≤ R`, `X < R`: `|B(x;X)| ≤ (max(|x|,X)/R)^{2X+1}` and, for even `X`, `|B'(x;X)| ≤ (max(|x|,X)/R)^X`. (Pairing `k, −k`: `|β(x;k)β(x;−k)| ≤ max(x²,k²)/R²`.) -/
theorem bprod_real_le (R : ℝ) (X : ℕ) (hXR : (X : ℝ) < R) (x : ℝ) (hx : |x| ≤ R) :
    ‖bprod R X x‖ ≤ (max |x| X / R) ^ (2 * X + 1) ∧
      (Even X → ‖bprodOdd R X x‖ ≤ (max |x| X / R) ^ X) := by
  have hR : 0 < R := by
    have h0 : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
    linarith
  set A : ℝ := max |x| (X:ℝ) with hAdef
  have hAx : |x| ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAX : (X:ℝ) ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hA0 : 0 ≤ A := le_trans (abs_nonneg x) hAx
  have hbprod : ∀ n, n ≤ X → ‖bprod R n x‖ ≤ (A/R)^(2*n+1) := by
    intro n
    induction n with
    | zero =>
        intro _
        have hb : bprod R 0 x = bfac R 0 (x:ℂ) := by unfold bprod; simp
        rw [hb, bfac_zero R hR x, show 2*0+1 = 1 by norm_num, pow_one]
        exact div_le_div_of_nonneg_right hAx (le_of_lt hR)
    | succ n ih =>
        intro hn
        have hn' : n ≤ X := by omega
        have hih := ih hn'
        have hkabs : |(((n:ℤ)+1 : ℤ) : ℝ)| = (n:ℝ) + 1 := by
          rw [show ((((n:ℤ)+1 : ℤ)) : ℝ) = (n:ℝ)+1 by push_cast; ring,
              abs_of_nonneg (by positivity)]
        have h1 : ((n:ℝ)+1) ≤ (X:ℝ) := by exact_mod_cast hn
        have hkle : |(((n:ℤ)+1 : ℤ) : ℝ)| < R := by rw [hkabs]; linarith
        have hpair := bfac_pair_bound R hR x hx ((n:ℤ)+1) hkle
        rw [bprod_peel]
        calc ‖bfac R ((n:ℤ)+1) (x:ℂ) * bfac R (-((n:ℤ)+1)) (x:ℂ) * bprod R n x‖
            = ‖bfac R ((n:ℤ)+1) (x:ℂ) * bfac R (-((n:ℤ)+1)) (x:ℂ)‖
                * ‖bprod R n x‖ := by rw [norm_mul]
          _ ≤ (A/R)^2 * (A/R)^(2*n+1) := by
              refine mul_le_mul ?_ hih (norm_nonneg _) (by positivity)
              refine le_trans hpair ?_
              apply pow_le_pow_left₀ (by positivity)
              rw [hkabs]
              exact div_le_div_of_nonneg_right (max_le hAx (le_trans h1 hAX)) (le_of_lt hR)
          _ = (A/R)^(2*(n+1)+1) := by
              rw [show 2*(n+1)+1 = (2*n+1)+2 by ring, pow_add]; ring
  have hodd : ∀ m, 2*m ≤ X → ‖bprodOdd R (2*m) x‖ ≤ (A/R)^(2*m) := by
    intro m
    induction m with
    | zero =>
        intro _
        have hb : bprodOdd R 0 x = 1 := by
          unfold bprodOdd; rw [Finset.prod_filter]; simp [Int.odd_iff]
        rw [hb, show 2*0 = 0 by norm_num, pow_zero]; simp
    | succ m ih =>
        intro hm
        have hm' : 2*m ≤ X := by omega
        have hih := ih hm'
        have hkabs : |(((2*m+1:ℕ):ℤ):ℝ)| = 2*(m:ℝ)+1 := by
          rw [show ((((2*m+1:ℕ)) : ℤ) : ℝ) = 2*(m:ℝ)+1 by push_cast; ring,
              abs_of_nonneg (by positivity)]
        have h1 : 2*(m:ℝ)+1 ≤ (X:ℝ) := by
          have : 2*m+1 ≤ X := by omega
          exact_mod_cast this
        have hkle : |(((2*m+1:ℕ):ℤ):ℝ)| < R := by rw [hkabs]; linarith
        have hpair := bfac_pair_bound R hR x hx (((2*m+1:ℕ):ℤ)) hkle
        rw [show 2*(m+1) = 2*m+2 by ring, bprodOdd_peel]
        calc ‖bfac R (((2*m+1:ℕ):ℤ)) (x:ℂ) * bfac R (-(((2*m+1:ℕ):ℤ))) (x:ℂ)
                * bprodOdd R (2*m) x‖
            = ‖bfac R (((2*m+1:ℕ):ℤ)) (x:ℂ) * bfac R (-(((2*m+1:ℕ):ℤ))) (x:ℂ)‖
                * ‖bprodOdd R (2*m) x‖ := by rw [norm_mul]
          _ ≤ (A/R)^2 * (A/R)^(2*m) := by
              refine mul_le_mul ?_ hih (norm_nonneg _) (by positivity)
              refine le_trans hpair ?_
              apply pow_le_pow_left₀ (by positivity)
              rw [hkabs]
              exact div_le_div_of_nonneg_right (max_le hAx (le_trans h1 hAX)) (le_of_lt hR)
          _ = (A/R)^(2*m+2) := by rw [mul_comm, ← pow_add]
  constructor
  · simpa using hbprod X le_rfl
  · intro hXe
    obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp hXe
    have h2m : 2*m ≤ X := by omega
    have := hodd m h2m
    rw [hm]
    exact this

end Work.BW
