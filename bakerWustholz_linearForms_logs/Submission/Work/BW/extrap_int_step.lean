import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.extrap_core
import Submission.Work.BW.est14
import Submission.Work.BW.est15
import Submission.Work.BW.est16
import Submission.Work.BW.est16_half_arith
import Submission.Work.BW.est16_main_arith
import Submission.Work.BW.est21
import Submission.Work.BW.bprod_real_le
import Submission.Work.BW.bprod_ratio24
import Submission.Work.BW.num19_int
import Submission.Work.BW.num19_int_JP_lo
import Submission.Work.BW.num_T
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.num_xi
import Submission.Work.BW.num_kum
import Submission.Work.BW.num_blaschke_eta
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.fAt_differentiable
import Submission.Work.BW.log_Y24_le
import Submission.Work.BW.extrap_int_h1
import Submission.Work.BW.extrap_int_h2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `extrap_int_step`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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

/-- BW §19 induction step `j → j+1` (`0 ≤ j ≤ r−2`) at descent level `J` (p. 53–54; p. 58 "goes through with S^{(J)}, T^{(J)} in place of S, T"): vanishing of `g^{(J)}(s;t)` for `|s| ≤ 2^jS^{(J)}`, `|t| ≤ ξ^jT^{(J)}` extends to `|s| ≤ 2^{j+1}S^{(J)}`, `|t| ≤ ξ^{j+1}T^{(J)}`. Proof: suppose `g(s;t) ≠ 0`; `extrap_core` with `f = f^{(J)}(·;t)`, `S' = ⌊2^jS^{(J)}⌋`, `R = 7·2S'`, `F = B(z;S')^{T'+1}`, `T' = [(1−ξ)ξ^jT^{(J)}]`, `η = 1/3`, `κ = 1`; `U` from `est16` (`T* = ξ^jT^{(J)}`), `V` from `est21` (`T'' = ξ^{j+1}T^{(J)}`), `W` from `bprod_real_le`, `Y` from `bprod_ratio24`; conditions from `num19_int`, `num20_aJb`, `num_blaschke_eta`, `num_T`. The hypothesis `hnd` (`2^J ≤ D_j` for some `j`, hence `ξ^{-rJ}/D ≤ (2ξ^r)^{-J}/r`) is needed: see `num19_half`. -/
theorem extrap_int_step {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) (hnd : ∃ j, (2 : ℝ) ^ J ≤ (pDj r (dK K) σ j : ℝ))
    (μ : Fin r → ℕ) (j : ℕ) (hj : j + 2 ≤ r)
    (hvan : VanSet (fun i => lamP φ α v L i) (QJ φ b k L ι v σ p J μ) (ballZ (2 ^ j * SJ K r b v J)) 1 (pxi r ^ j * TJ K σ J)) :
    VanSet (fun i => lamP φ α v L i) (QJ φ b k L ι v σ p J μ) (ballZ (2 ^ (j + 1) * SJ K r b v J)) 1 (pxi r ^ (j + 1) * TJ K σ J) := by
  classical
  have hr : 2 ≤ r := H.hr
  have hd1 : 1 ≤ dK K := by
    have hpos : 0 < dK K := by
      haveI : Nontrivial K := inferInstance
      exact Module.finrank_pos (R := ℚ) (M := K)
    omega
  have hσ : ∀ j : Fin r, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hh19 : 19 ≤ acH K b v := (acH_lower H).1
  have hT := num_T hr hd1 hh19 σ hσ
  have hS608 : (608 : ℝ) ≤ (pS r (dK K) (acH K b v) : ℝ) := hT.2.2.2
  have hdhT : (dK K : ℝ) * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) ≤
      0.735 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ := hT.2.2.1
  have hTlow : 6.297 * pD r (dK K) σ ≤ (1 - pxi r) * (pT r (dK K) σ : ℝ) := hT.1
  have hTup : (1 - pxi r) * (pT r (dK K) σ : ℝ) ≤ 6.3 * pD r (dK K) σ := hT.2.1
  have hDlow : 2 * (r : ℝ) ^ r * 32 ^ (r + 1) * (dK K : ℝ) * Real.log (2 * r * (dK K : ℝ)) ≤
      pD r (dK K) σ := (num_D_lower hr hd1 σ hσ).1
  have hxi := num_xi hr
  have hlog2rd : 0 < Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
    apply Real.log_pos
    have h5 : (1 : ℝ) ≤ r := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hr)
    have h6 : (1 : ℝ) ≤ dK K := by exact_mod_cast hd1
    nlinarith
  have hξpos : 0 < pxi r := by
    have h1 : (0.536 : ℝ) / r ≤ 0.268 := by
      rw [div_le_iff₀ (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr))]
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    have h2 : pxi r = 1 - 0.536 / r := rfl
    rw [h2]; linarith
  have hξle1 : pxi r ≤ 1 := by
    have h2 : pxi r = 1 - 0.536 / r := rfl
    rw [h2]
    have : (0 : ℝ) ≤ 0.536 / r := by positivity
    linarith
  have hSD : 0 < (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ := by
    have h1 : 0 < (pS r (dK K) (acH K b v) : ℝ) := by linarith
    have h2 : 0 < pD r (dK K) σ := by
      have h3 : 0 < 2 * (r : ℝ) ^ r * 32 ^ (r + 1) * (dK K : ℝ) * Real.log (2 * r * (dK K : ℝ)) := by
        have : (0 : ℝ) < (r : ℝ) ^ r := by positivity
        positivity
      linarith
    positivity
  have hDpos : 0 < pD r (dK K) σ := by
    have h1 : 0 < (pS r (dK K) (acH K b v) : ℝ) := by linarith
    nlinarith [hSD, h1]
  obtain ⟨j0, hj0⟩ := hnd
  have hDge2J : (2 : ℝ) ^ J ≤ pD r (dK K) σ / r := by
    have h1 : (pDj r (dK K) σ j0 : ℝ) ≤ pD r (dK K) σ / r := (num_D_lower hr hd1 σ hσ).2 j0
    linarith
  rw [VanSet] at hvan ⊢
  intro s hs t0 t ht
  rw [ballZ] at hs
  simp only [Set.mem_setOf_eq] at hs
  rw [Nat.cast_one, div_one]
  change acg φ α b k L ι v σ p J μ t0 t (s : ℂ) = 0
  by_cases hsmall : ((|s| : ℤ) : ℝ) ≤ 2 ^ j * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ))
  · have h1 : s ∈ ballZ (2 ^ j * SJ K r b v J) := by
      rw [ballZ]; simp only [Set.mem_setOf_eq]
      exact hsmall
    have h2 : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ pxi r ^ j * TJ K σ J := by
      refine le_trans ht ?_
      have h4 : pxi r ^ (j + 1) * TJ K σ J =
          pxi r ^ (j + 1) * (pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) := rfl
      have h5 : pxi r ^ j * TJ K σ J =
          pxi r ^ j * (pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) := rfl
      rw [h4, h5, pow_succ]
      have h7 : (0:ℝ) ≤ pxi r ^ j * (pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) := by positivity
      nlinarith [h7, hξle1]
    have h3 := hvan s h1 t0 t h2
    simpa only [acg, Nat.cast_one, div_one] using h3
  · by_contra hg
    have hss : ((|s| : ℤ) : ℝ) ≤ 2 ^ (j + 1) * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ)) := by
      have h1 : 2 ^ (j + 1) * SJ K r b v J =
          2 ^ (j + 1) * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ)) := rfl
      rw [h1] at hs
      exact hs
    have hgt : 2 ^ j * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ)) < ((|s| : ℤ) : ℝ) :=
      not_le.mp hsmall
    have hss_l : ((|s| : ℤ) : ℝ) ≤
        2 ^ (j + 1) * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ) := by
      have h4 : 2 ^ (j + 1) * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ) =
          2 ^ (j + 1) * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ)) := by ring
      rw [h4]; exact hss
    have hss2 : ((|s| : ℤ) : ℝ) ≤
        2 * (2 ^ j * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ))) := by
      have h4 : 2 * (2 ^ j * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ))) =
          2 ^ (j + 1) * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ)) := by ring
      rw [h4]; exact hss
    let Sp : ℕ := ⌊2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ)⌋₊
    let Tp : ℕ := ⌊(1 - pxi r) * pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)⌋₊
    have hSp_def : (Sp : ℝ) = ⌊2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ)⌋₊ := rfl
    have hTp_def : (Tp : ℝ) = ⌊(1 - pxi r) * pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)⌋₊ := rfl
    have hSp_le : (Sp : ℝ) ≤ 2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ) := by
      rw [hSp_def]; exact Nat.floor_le (by positivity)
    have hSp_lt : 2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ) < (Sp : ℝ) + 1 := by
      rw [hSp_def]; exact Nat.lt_floor_add_one _
    have hpow1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hpowξ : (1 : ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_natCast, one_le_inv₀ (by positivity)]
      exact pow_le_one₀ hξpos.le hξle1
    have hSp608 : 608 ≤ Sp := by
      have h1 : (608 : ℝ) ≤ 2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ) := by
        have h4 : (1 : ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) := hpowξ
        have h5 : (608 : ℝ) ≤ (pS r (dK K) (acH K b v) : ℝ) := hS608
        have h6 : (1 : ℝ) * 1 * 608 ≤ 2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) *
            (pS r (dK K) (acH K b v) : ℝ) := by
          apply mul_le_mul (mul_le_mul hpow1 hpowξ (by norm_num) (by positivity)) h5 (by norm_num) (by positivity)
        linarith
      exact Nat.le_floor h1
    have hSp608R : (608 : ℝ) ≤ (Sp : ℝ) := by exact_mod_cast hSp608
    let U : ℝ := (dK K : ℝ) * (acH K b v : ℝ) * pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) +
        1.055 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ +
        1.008 * ((7.2 * (Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * pD r (dK K) σ +
        0.044 * (J : ℝ) / Real.log (2 * r * dK K) * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ
    let V : ℝ := (dK K : ℝ) * (acH K b v : ℝ) * pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) +
        (1.133 - 9 * 2 ^ r) * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ +
        1.01 * (((Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * pD r (dK K) σ +
        0.044 * (J : ℝ) / Real.log (2 * r * dK K) * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ
    let W : ℝ := (2 * (Sp : ℝ) + 1) * ((Tp : ℝ) + 1) *
        (Real.log (7.2 * (Sp : ℝ)) - Real.log (max ((|s| : ℤ) : ℝ) (Sp : ℝ)))
    let Y : ℝ := ((Tp : ℝ) + 1) * Real.log ((2 * Real.pi / 3)⁻¹ * (1 - (1 / 3 : ℝ))⁻¹ ^ 2 *
        (Sp : ℝ) ^ 2 * Real.exp (2 * (Sp : ℝ)) * (max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ))) ^ (2 * (Sp : ℝ) + 1))
    have hSunfold : (pS r (dK K) (acH K b v) : ℝ) = (pS r (dK K) (acH K b v) : ℝ) := rfl
    have hss0 : 0 ≤ ((|s| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg s
    have hSpos : 0 < (pS r (dK K) (acH K b v) : ℝ) := by linarith
    have hs16 : ((|s| : ℤ) : ℝ) / 2 ^ J ≤ 2 ^ r * (pS r (dK K) (acH K b v) : ℝ) := by
      have h2J : (0 : ℝ) < 2 ^ J := by positivity
      have hSnn : (0:ℝ) ≤ (pS r (dK K) (acH K b v) : ℝ) := hSpos.le
      have h2ξ : (1:ℝ) ≤ 2 * pxi r ^ r := by linarith [hxi.2.2.2.2]
      have hξb : pxi r ^ (-((r * J : ℕ) : ℤ)) / 2 ^ J ≤ 1 := by
        have hinv2 : pxi r ^ (-((r * J : ℕ) : ℤ)) / 2 ^ J = ((2 * pxi r ^ r)⁻¹) ^ J := by
          rw [zpow_neg, zpow_natCast, pow_mul, div_eq_mul_inv, ← mul_inv, ← mul_pow, inv_pow,
            show (pxi r ^ r) * 2 = 2 * pxi r ^ r from by ring]
        rw [hinv2]
        apply pow_le_one₀ (by positivity)
        rw [inv_le_one₀ (by positivity)]
        linarith [h2ξ]
      have h2j : (2 : ℝ) ^ (j + 1) ≤ 2 ^ r := by
        apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2); omega
      have h0ξ : (0:ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) / 2 ^ J := by positivity
      have hm : 2 ^ (j + 1) * (pxi r ^ (-((r * J : ℕ) : ℤ)) / 2 ^ J) ≤ 2 ^ r :=
        le_trans (mul_le_mul h2j hξb h0ξ (by positivity)) (by norm_num)
      have hsplit : (2 ^ (j + 1) * (pxi r ^ (-((r * J : ℕ) : ℤ)) *
            (pS r (dK K) (acH K b v) : ℝ))) / 2 ^ J =
          2 ^ (j + 1) * (pxi r ^ (-((r * J : ℕ) : ℤ)) / 2 ^ J) * (pS r (dK K) (acH K b v) : ℝ) := by
        rw [mul_div_assoc]; ring
      calc ((|s| : ℤ) : ℝ) / 2 ^ J
          ≤ (2 ^ (j + 1) * (pxi r ^ (-((r * J : ℕ) : ℤ)) *
              (pS r (dK K) (acH K b v) : ℝ))) / 2 ^ J :=
            div_le_div_of_nonneg_right hss h2J.le
        _ = 2 ^ (j + 1) * (pxi r ^ (-((r * J : ℕ) : ℤ)) / 2 ^ J) *
              (pS r (dK K) (acH K b v) : ℝ) := hsplit
        _ ≤ 2 ^ r * (pS r (dK K) (acH K b v) : ℝ) := mul_le_mul_of_nonneg_right hm hSnn
    have hUval : U = (dK K : ℝ) * (acH K b v : ℝ) * pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) +
        1.055 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ +
        1.008 * ((7.2 * (Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * pD r (dK K) σ +
        0.044 * (J : ℝ) / Real.log (2 * r * dK K) * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ := rfl
    have hVval : V = (dK K : ℝ) * (acH K b v : ℝ) * pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) +
        (1.133 - 9 * 2 ^ r) * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ +
        1.01 * (((Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * pD r (dK K) σ +
        0.044 * (J : ℝ) / Real.log (2 * r * dK K) * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ := rfl
    have hWval : W = (2 * (Sp : ℝ) + 1) * ((Tp : ℝ) + 1) *
        (Real.log (7.2 * (Sp : ℝ)) - Real.log (max ((|s| : ℤ) : ℝ) (Sp : ℝ))) := rfl
    have hYval : Y = ((Tp : ℝ) + 1) * Real.log ((2 * Real.pi / 3)⁻¹ * (1 - (1 / 3 : ℝ))⁻¹ ^ 2 *
        (Sp : ℝ) ^ 2 * Real.exp (2 * (Sp : ℝ)) *
        (max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ))) ^ (2 * (Sp : ℝ) + 1)) := rfl
    have habsS : |(s : ℝ)| = ((|s| : ℤ) : ℝ) := by
      have h2 : (s : ℝ) = ((s : ℤ) : ℝ) := by push_cast; ring
      rw [h2, ← Int.cast_abs]
    have hsnorm : ‖(s : ℂ)‖ = ((|s| : ℤ) : ℝ) := by rw [Complex.norm_intCast, Int.cast_abs]
    -- (i) hU from est16
    have hTst16 : pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) ≤ acT K σ := by
      have h2 : pxi r ^ (j + 1) * pxi r ^ (r * J) ≤ 1 := by
        rw [← pow_add]
        exact pow_le_one₀ hξpos.le hξle1
      have h3 : (0:ℝ) ≤ (pT r (dK K) σ : ℝ) := by simp only [pT]; positivity
      have h4 : (pT r (dK K) σ : ℝ) ≤ acT K σ := le_of_eq rfl
      nlinarith [h2, h3, h4]
    have ht16 : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) := by
      have h1 : pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) = pxi r ^ (j + 1) * TJ K σ J := by
        rw [TJ]; ring
      rw [h1]; exact ht
    have hU : ∀ z : ℂ, ‖z‖ = 7.2 * (Sp : ℝ) →
        ‖acf φ α b k L ι v σ p J μ t0 t z‖ ≤
          ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ * Real.exp U := by
      intro z hz
      have h := est16 H J hJ μ (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) hTst16 t0 t ht16 s hs16 hg z
      rw [hz] at h
      have hstep : (dK K : ℝ) * (acH K b v : ℝ) *
            (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) +
            1.055 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ +
            1.008 * ((7.2 * (Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * pD r (dK K) σ +
            kumJ K b v σ J = U := by
        rw [hUval, kumJ]
        ring_nf
      rw [hstep] at h
      exact h
    -- (ii) hV from est21
    have hTst21 : pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) ≤ acT K σ := by
      have h2 : pxi r ^ j * pxi r ^ (r * J) ≤ 1 := by
        rw [← pow_add]
        exact pow_le_one₀ hξpos.le hξle1
      have h3 : (0:ℝ) ≤ (pT r (dK K) σ : ℝ) := by simp only [pT]; positivity
      have h4 : (pT r (dK K) σ : ℝ) ≤ acT K σ := le_of_eq rfl
      nlinarith [h2, h3, h4]
    have hTpsum : (Tp : ℝ) + pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) ≤
        pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) := by
      have h1 : (Tp : ℝ) ≤ (1 - pxi r) * pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) := by
        rw [hTp_def]
        exact Nat.floor_le (by positivity)
      have h7 : (1 - pxi r) * pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) +
          pxi r * (pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) =
          pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) := by ring
      have h2 : pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) =
          pxi r * (pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) := by
        rw [pow_succ]; ring
      rw [h2]; linarith [h1, h7]
    have hV : ∀ l ∈ Finset.Icc (-(Sp : ℤ)) (Sp : ℤ), ∀ m : ℕ, m ≤ Tp →
        ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m (l : ℂ)‖ ≤
          ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ * Real.exp V := by
      intro l hl m hm
      have hmem : -(Sp : ℤ) ≤ l ∧ l ≤ (Sp : ℤ) := Finset.mem_Icc.mp hl
      have hlm : (|l| : ℤ) ≤ (Sp : ℤ) := abs_le.mpr hmem
      have hlmR : ((|l| : ℤ) : ℝ) ≤ (Sp : ℝ) := by exact_mod_cast hlm
      have hlmS : ((|l| : ℤ) : ℝ) ≤
          2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ) :=
        le_trans hlmR hSp_le
      have hTpnn : (0:ℝ) ≤ (Tp : ℝ) := by positivity
      have hvan21 : ∀ (t0' : ℕ) (t' : Fin (r - 1) → ℕ),
          ((t0' + ∑ m, t' m : ℕ) : ℝ) ≤ (Tp : ℝ) + pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) →
          acg φ α b k L ι v σ p J μ t0' t' (l : ℂ) = 0 := by
        intro t0' t' ht'
        have h1 : ((t0' + ∑ m, t' m : ℕ) : ℝ) ≤ pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) :=
          le_trans ht' hTpsum
        have h2 : l ∈ ballZ (2 ^ j * SJ K r b v J) := by
          rw [ballZ]; simp only [Set.mem_setOf_eq]
          rw [show 2 ^ j * SJ K r b v J =
              2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ) from by
            rw [SJ]; ring]
          exact hlmS
        have h3 : ((t0' + ∑ m, t' m : ℕ) : ℝ) ≤ pxi r ^ j * TJ K σ J := by
          have h5 : pxi r ^ j * TJ K σ J = pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) := by
            rw [TJ]; ring
          rw [h5]; exact h1
        have h6 := hvan l h2 t0' t' h3
        simpa only [acg, Nat.cast_one, div_one] using h6
      have ht21 : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤
          pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) := by
        have he : pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) =
            pxi r ^ (j + 1) * TJ K σ J := by rw [TJ]; ring
        rw [he]; exact ht
      have hmR : (m : ℝ) ≤ (Tp : ℝ) := by exact_mod_cast hm
      have hVE : (dK K : ℝ) * (acH K b v : ℝ) * (pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) =
          (dK K : ℝ) * (acH K b v : ℝ) * pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ) := by ring
      have h := est21 H J hJ μ (pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) hTst21 (Tp : ℝ)
          (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) hTpnn hTpsum (l : ℂ) hvan21 t0 t ht21 m hmR s hs16 hg
      have hl' : ‖(l : ℂ)‖ = ((|l| : ℤ) : ℝ) := by
        rw [Complex.norm_intCast, Int.cast_abs]
      rw [hl'] at h
      have h3 : ((|l| : ℤ) : ℝ) + ((|s| : ℤ) : ℝ) ≤ (Sp : ℝ) + ((|s| : ℤ) : ℝ) := by linarith
      have h4 : (((|l| : ℤ) : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J ≤
          ((Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J :=
        div_le_div_of_nonneg_right h3 (by positivity)
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      have hvv : (dK K : ℝ) * (acH K b v : ℝ) *
            (pxi r ^ j * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) +
            (1.133 - 9 * 2 ^ r) * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ +
            1.01 * (((Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * pD r (dK K) σ + kumJ K b v σ J
          = V := by
        rw [hVval, kumJ]
        ring_nf
      rw [← hvv]
      have h5 : 1.01 * ((((|l| : ℤ) : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * pD r (dK K) σ ≤
          1.01 * (((Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * pD r (dK K) σ := by
        apply mul_le_mul_of_nonneg_right _ hDpos.le
        exact mul_le_mul_of_nonneg_left h4 (by norm_num)
      linarith [h5]
    -- (iii) hW from bprod_real_le
    have hsx : |(s : ℝ)| ≤ 7.2 * (Sp : ℝ) := by
      rw [habsS]
      have h3 : ((|s| : ℤ) : ℝ) ≤ 2 * (Sp : ℝ) + 2 := by linarith [hss2, hSp_lt]
      linarith [h3, hSp608R]
    have hW : ‖∏ l ∈ Finset.Icc (-(Sp : ℤ)) (Sp : ℤ), bfac (7.2 * (Sp : ℝ)) l (s : ℂ) ^ (Tp + 1)‖ ≤
        Real.exp (-W) := by
      have hb := (bprod_real_le (7.2 * (Sp : ℝ)) Sp (by linarith) (s : ℝ) hsx).1
      rw [habsS] at hb
      have h1 : (∏ l ∈ Finset.Icc (-(Sp : ℤ)) (Sp : ℤ), bfac (7.2 * (Sp : ℝ)) l (s : ℂ) ^ (Tp + 1)) =
          (bprod (7.2 * (Sp : ℝ)) Sp (s : ℂ)) ^ (Tp + 1) := by
        rw [bprod, Finset.prod_pow]
      rw [h1, norm_pow]
      have h3 : ((s : ℂ)) = ((s : ℝ) : ℂ) := Complex.ofReal_intCast s
      rw [h3]
      have hb' : ‖bprod (7.2 * (Sp : ℝ)) Sp ((s : ℝ) : ℂ)‖ ≤
          (max ((|s| : ℤ) : ℝ) (Sp : ℝ) / (7.2 * (Sp : ℝ))) ^ (2 * Sp + 1) := hb
      have hApos : 0 < max ((|s| : ℤ) : ℝ) (Sp : ℝ) / (7.2 * (Sp : ℝ)) := by
        have h5 : (0:ℝ) < max ((|s| : ℤ) : ℝ) (Sp : ℝ) :=
          lt_of_lt_of_le (by linarith : (0:ℝ) < (Sp:ℝ)) (le_max_right _ _)
        positivity
      have hAeq : max ((|s| : ℤ) : ℝ) (Sp : ℝ) / (7.2 * (Sp : ℝ)) =
          Real.exp (Real.log (max ((|s| : ℤ) : ℝ) (Sp : ℝ)) - Real.log (7.2 * (Sp : ℝ))) := by
        rw [← Real.exp_log hApos]
        congr 1
        rw [Real.log_div (by positivity) (by positivity)]
      calc ‖bprod (7.2 * (Sp : ℝ)) Sp ((s : ℝ) : ℂ)‖ ^ (Tp + 1)
          ≤ ((max ((|s| : ℤ) : ℝ) (Sp : ℝ) / (7.2 * (Sp : ℝ))) ^ (2 * Sp + 1)) ^ (Tp + 1) :=
            pow_le_pow_left₀ (norm_nonneg _) hb' _
        _ = (max ((|s| : ℤ) : ℝ) (Sp : ℝ) / (7.2 * (Sp : ℝ))) ^ ((2 * Sp + 1) * (Tp + 1)) := by
            rw [pow_mul]
        _ = Real.exp (-W) := by
            rw [hWval, hAeq, ← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
    -- (iv) hY from bprod_ratio24
    have hY : ∀ l ∈ Finset.Icc (-(Sp : ℤ)) (Sp : ℤ), ∀ z : ℂ, ‖z - (l : ℂ)‖ = 1 / 3 →
        ‖∏ l' ∈ Finset.Icc (-(Sp : ℤ)) (Sp : ℤ), bfac (7.2 * (Sp : ℝ)) l' (s : ℂ) ^ (Tp + 1)‖ ≤
          ‖∏ l' ∈ Finset.Icc (-(Sp : ℤ)) (Sp : ℤ), bfac (7.2 * (Sp : ℝ)) l' z ^ (Tp + 1)‖ * Real.exp Y := by
      intro l hl z hz
      have hmem : -(Sp : ℤ) ≤ l ∧ l ≤ (Sp : ℤ) := Finset.mem_Icc.mp hl
      have hlm : (|l| : ℤ) ≤ (Sp : ℤ) := abs_le.mpr hmem
      have hXR : (Sp : ℝ) + 1 / 3 ≤ 7.2 * (Sp : ℝ) := by linarith [hSp608R]
      have hb := bprod_ratio24 (7.2 * (Sp : ℝ)) (1 / 3) (by norm_num) (by norm_num) Sp (by omega)
        hXR l hlm z hz (s : ℝ) hsx
      rw [habsS] at hb
      have h1 : (∏ l' ∈ Finset.Icc (-(Sp : ℤ)) (Sp : ℤ), bfac (7.2 * (Sp : ℝ)) l' (s : ℂ) ^ (Tp + 1)) =
          (bprod (7.2 * (Sp : ℝ)) Sp (s : ℂ)) ^ (Tp + 1) := by rw [bprod, Finset.prod_pow]
      have h2 : (∏ l' ∈ Finset.Icc (-(Sp : ℤ)) (Sp : ℤ), bfac (7.2 * (Sp : ℝ)) l' z ^ (Tp + 1)) =
          (bprod (7.2 * (Sp : ℝ)) Sp z) ^ (Tp + 1) := by rw [bprod, Finset.prod_pow]
      have h3 : ((s : ℂ)) = ((s : ℝ) : ℂ) := Complex.ofReal_intCast s
      rw [h1, h2, norm_pow, norm_pow, h3]
      have hY24eq : (max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ))) ^ (2 * (Sp : ℝ) + 1) =
          (max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ))) ^ (2 * Sp + 1) := by
        rw [show (2 * (Sp : ℝ) + 1) = ((2 * Sp + 1 : ℕ) : ℝ) from by push_cast; ring,
          Real.rpow_natCast]
      have hb' : ‖bprod (7.2 * (Sp : ℝ)) Sp ((s : ℝ) : ℂ)‖ ≤ ‖bprod (7.2 * (Sp : ℝ)) Sp z‖ *
          ((2 * Real.pi * (1 / 3))⁻¹ * (1 - (1 / 3 : ℝ))⁻¹ ^ 2 * (Sp : ℝ) ^ 2 * Real.exp (2 * (Sp : ℝ)) *
            (max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ))) ^ (2 * (Sp : ℝ) + 1)) := by
        rw [hY24eq]
        exact hb
      have hY24pos : 0 < ((2 * Real.pi * (1 / 3))⁻¹ * (1 - (1 / 3 : ℝ))⁻¹ ^ 2 * (Sp : ℝ) ^ 2 *
          Real.exp (2 * (Sp : ℝ)) * (max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ))) ^ (2 * (Sp : ℝ) + 1)) := by
        positivity
      calc ‖bprod (7.2 * (Sp : ℝ)) Sp ((s : ℝ) : ℂ)‖ ^ (Tp + 1)
          ≤ (‖bprod (7.2 * (Sp : ℝ)) Sp z‖ * ((2 * Real.pi * (1 / 3))⁻¹ * (1 - (1 / 3 : ℝ))⁻¹ ^ 2 *
              (Sp : ℝ) ^ 2 * Real.exp (2 * (Sp : ℝ)) *
              (max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ))) ^ (2 * (Sp : ℝ) + 1))) ^ (Tp + 1) :=
            pow_le_pow_left₀ (norm_nonneg _) hb' _
        _ = ‖bprod (7.2 * (Sp : ℝ)) Sp z‖ ^ (Tp + 1) *
              (((2 * Real.pi * (1 / 3))⁻¹ * (1 - (1 / 3 : ℝ))⁻¹ ^ 2 * (Sp : ℝ) ^ 2 *
                Real.exp (2 * (Sp : ℝ)) *
                (max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ))) ^ (2 * (Sp : ℝ) + 1))) ^ (Tp + 1) := mul_pow _ _ _
        _ = ‖bprod (7.2 * (Sp : ℝ)) Sp z‖ ^ (Tp + 1) * Real.exp Y := by
            have key : ((2 * Real.pi * (1 / 3))⁻¹ * (1 - (1 / 3 : ℝ))⁻¹ ^ 2 * (Sp : ℝ) ^ 2 *
                Real.exp (2 * (Sp : ℝ)) *
                (max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ))) ^ (2 * (Sp : ℝ) + 1)) ^ (Tp + 1) = Real.exp Y := by
              rw [hYval, ← Real.exp_log hY24pos, ← Real.exp_nat_mul]
              congr 1
              push_cast
              ring
            rw [key]
    -- ============ the numerical input ============
    have hJ' : (J : ℝ) ≤ 50 * Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
      have h1 : (pI r (dK K) : ℝ) ≤ 50 * Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
        rw [pI]
        exact Nat.floor_le (by positivity)
      exact le_trans (by exact_mod_cast hJ) h1
    let q : ℝ := pxi r ^ (-((r * J : ℕ) : ℤ)) / pD r (dK K) σ
    have hq0 : 0 ≤ q := by
      have h1 : (0:ℝ) < pxi r ^ (-((r * J : ℕ) : ℤ)) := by positivity
      have h2 : (0:ℝ) < pD r (dK K) σ := hDpos
      positivity
    have hq1 : q ≤ ((2 * pxi r ^ r)⁻¹) ^ J / r := by
      have hrpos : (0:ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
      have h3 : (r : ℝ) * 2 ^ J ≤ pD r (dK K) σ := by
        have h5 := (le_div_iff₀ hrpos).mp hDge2J
        linarith
      have h4 : q ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) / ((r : ℝ) * 2 ^ J) := by
        show pxi r ^ (-((r * J : ℕ) : ℤ)) / pD r (dK K) σ ≤
          pxi r ^ (-((r * J : ℕ) : ℤ)) / ((r:ℝ) * 2^J)
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) h3
      have h6 : pxi r ^ (-((r * J : ℕ) : ℤ)) / ((r : ℝ) * 2 ^ J) =
          (pxi r ^ (-((r * J : ℕ) : ℤ)) / 2 ^ J) / r := by
        field_simp
      have hinv2 : pxi r ^ (-((r * J : ℕ) : ℤ)) / 2 ^ J = ((2 * pxi r ^ r)⁻¹) ^ J := by
        rw [zpow_neg, zpow_natCast, pow_mul, div_eq_mul_inv, ← mul_inv, ← mul_pow, inv_pow,
          show (pxi r ^ r) * 2 = 2 * pxi r ^ r from by ring]
      rw [h6, hinv2] at h4
      exact h4
    have hq3 : pxi r ^ (-((r * J : ℕ) : ℤ)) / pD r (dK K) σ ≤ q := le_of_eq rfl
    have hq2 : q ≤ ((pxi r ^ r)⁻¹) ^ J / (2 * (r : ℝ) ^ r * 32 ^ (r + 1) * (dK K : ℝ) *
        Real.log (2 * r * (dK K : ℝ))) := by
      have hDmin : 0 < 2 * (r : ℝ) ^ r * 32 ^ (r + 1) * (dK K : ℝ) * Real.log (2 * r * (dK K : ℝ)) := by
        have h1 : (0:ℝ) < (r:ℝ)^r := by positivity
        have h2 : (0:ℝ) < (dK K:ℝ) := by exact_mod_cast hd1
        have h3 : (0:ℝ) < Real.log (2 * r * (dK K:ℝ)) := hlog2rd
        positivity
      have h4 : q ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) / (2 * (r : ℝ) ^ r * 32 ^ (r + 1) * (dK K : ℝ) *
          Real.log (2 * r * (dK K : ℝ))) := by
        show pxi r ^ (-((r * J : ℕ) : ℤ)) / pD r (dK K) σ ≤ _
        exact div_le_div_of_nonneg_left (by positivity) hDmin hDlow
      have h5 : pxi r ^ (-((r * J : ℕ) : ℤ)) = ((pxi r ^ r)⁻¹) ^ J := by
        rw [zpow_neg, zpow_natCast, pow_mul, inv_pow]
      rw [h5] at h4
      exact h4
    have hI : 3.422 * 2 ^ j * (6.3 * pxi r ^ j + q) + 0.735 * pxi r ^ (j + r * J) + 1.133 +
        3.03 * 2 ^ j * ((2 * pxi r ^ r)⁻¹) ^ J + 0.044 * (J : ℝ) / Real.log (2 * r * dK K) - 9 * 2 ^ r ≤
        -2.2 * 2 ^ r := (num19_int hr hd1 J hJ' j hj q hq0 hq1 hq2).2
    have hJP : 0.735 * pxi r ^ (j + 1 + r * J) + 1.055 + 0.044 * (J : ℝ) / Real.log (2 * r * dK K) +
        9.30 * (2 : ℝ) ^ j * ((2 * pxi r ^ r)⁻¹) ^ J - 16.05 * (2 * pxi r) ^ j ≤ -1 :=
      num19_int_JP_lo hr hd1 J hJ' j hj
    have h1 : Real.log (7.2 * (Sp : ℝ) / (7.2 * (Sp : ℝ) - ‖(s : ℂ)‖)) + U - W < -Real.log 2 := by
      have h := extrap_int_h1 hr hd1 (acH K b v) hh19 σ hσ J hJ' j hj Sp hSp_def Tp hTp_def s hss_l hJP
      have hsnorm : ‖(s : ℂ)‖ = ((|s| : ℤ) : ℝ) := by rw [Complex.norm_intCast, Int.cast_abs]
      rw [hsnorm, hUval, hWval]
      exact h
    have h2 : Real.log (((Finset.Icc (-(Sp : ℤ)) (Sp : ℤ)).card : ℝ) * ((Tp : ℝ) + 1)) +
        Real.log ((1 / 3 : ℝ) / (1 - 1 / 3)) + V + Y < -Real.log 2 := by
      have h := extrap_int_h2 hr hd1 (acH K b v) hh19 σ hσ J hJ' j hj Sp hSp_def Tp hTp_def s hss_l
        q hq0 hq1 hq3 hI
      have hZcard : (((Finset.Icc (-(Sp : ℤ)) (Sp : ℤ)).card : ℝ)) = 2 * (Sp : ℝ) + 1 := by
        have h1 : (((Finset.Icc (-(Sp : ℤ)) (Sp : ℤ)).card : ℤ)) = 2 * (Sp : ℤ) + 1 := by
          rw [Int.card_Icc_of_le (a := -(Sp : ℤ)) (b := (Sp : ℤ)) (by omega)]
          ring
        have h2 : (((Finset.Icc (-(Sp : ℤ)) (Sp : ℤ)).card : ℝ)) =
            ((((Finset.Icc (-(Sp : ℤ)) (Sp : ℤ)).card : ℤ)) : ℝ) := by push_cast; rfl
        rw [h2, h1]
        push_cast
        ring
      rw [hZcard, hVval, hYval]
      have hlog : Real.log ((1 / 3 : ℝ) / (1 - 1 / 3)) = -Real.log 2 := by
        rw [show (1/3 : ℝ) / (1 - 1/3) = 1/2 from by norm_num,
          Real.log_div one_ne_zero (by norm_num), Real.log_one]
        ring
      rw [hlog]
      linarith
    -- ============ the extrapolation core ============
    have hdiff : Differentiable ℂ (fun z : ℂ => acf φ α b k L ι v σ p J μ t0 t z) :=
      fAt_differentiable (ellM φ α b k v L) (QJ φ b k L ι v σ p J μ t0 t)
    have hδ : 0 < 7.2 * (Sp : ℝ) - ‖(s : ℂ)‖ := by
      have h3 : ((|s| : ℤ) : ℝ) ≤ 2 * (Sp : ℝ) + 2 := by linarith [hss2, hSp_lt]
      rw [hsnorm]; linarith [h3, hSp608R]
    have hsR' : ‖(s : ℂ)‖ + (7.2 * (Sp : ℝ) - ‖(s : ℂ)‖) ≤ 7.2 * (Sp : ℝ) := by linarith
    have hsZ : ∀ l ∈ Finset.Icc (-(Sp : ℤ)) (Sp : ℤ), (1 : ℝ) ≤ ‖(s : ℂ) - (l : ℂ)‖ := by
      intro l hl
      have hmem : -(Sp : ℤ) ≤ l ∧ l ≤ (Sp : ℤ) := Finset.mem_Icc.mp hl
      have hlm : (|l| : ℤ) ≤ (Sp : ℤ) := abs_le.mpr hmem
      have hlmR : ((|l| : ℤ) : ℝ) ≤ (Sp : ℝ) := by exact_mod_cast hlm
      have hlt : ((|l| : ℤ) : ℝ) < ((|s| : ℤ) : ℝ) := by
        have h2 : (Sp : ℝ) ≤ 2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) *
            (pS r (dK K) (acH K b v) : ℝ) := hSp_le
        linarith [hgt]
      have hsl : s ≠ l := by
        intro h
        rw [h] at hlt
        exact lt_irrefl _ hlt
      have h3 : ‖(s : ℂ) - (l : ℂ)‖ = ((|s - l| : ℤ) : ℝ) := by
        have h4 : (s : ℂ) - (l : ℂ) = ((s - l : ℤ) : ℂ) := by push_cast; ring
        rw [h4, Complex.norm_intCast, Int.cast_abs]
      have h5 : (1 : ℤ) ≤ |s - l| := Int.one_le_abs (sub_ne_zero.mpr hsl)
      have h6 : (1 : ℝ) ≤ ((|s - l| : ℤ) : ℝ) := by exact_mod_cast h5
      rw [h3]; exact h6
    have hZ : ∀ l ∈ Finset.Icc (-(Sp : ℤ)) (Sp : ℤ), ((|l| : ℤ) : ℝ) + 1 / 3 < 7.2 * (Sp : ℝ) := by
      intro l hl
      have hmem : -(Sp : ℤ) ≤ l ∧ l ≤ (Sp : ℤ) := Finset.mem_Icc.mp hl
      have hlm : (|l| : ℤ) ≤ (Sp : ℤ) := abs_le.mpr hmem
      have hlmR : ((|l| : ℤ) : ℝ) ≤ (Sp : ℝ) := by exact_mod_cast hlm
      linarith [hSp608R]
    -- the auxiliary estimates (14) and (15) at `s`, giving `‖f s‖ > 0`
    have hkum22 : kumJ K b v σ J ≤ 2.2 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ := by
      rw [kumJ]
      have hJle : (J : ℝ) ≤ 50 * Real.log (2 * (r : ℝ) * (dK K : ℝ)) := hJ'
      have hSDnn : 0 ≤ (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ := (mul_pos hSpos hDpos).le
      calc 0.044 * (J : ℝ) / Real.log (2 * (r : ℝ) * (dK K : ℝ)) *
            (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ
          = (0.044 * (J : ℝ) / Real.log (2 * (r : ℝ) * (dK K : ℝ))) *
            ((pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ) := by ring
        _ ≤ 2.2 * ((pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ) := by
            apply mul_le_mul_of_nonneg_right _ hSDnn
            rw [div_le_iff₀ hlog2rd]
            nlinarith
        _ = 2.2 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ := by ring
    have hSD001 : Real.log 2 ≤ 0.001 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ :=
      (num_kum hr hd1 hh19 σ hσ J).2.2
    have hTs16 : (dK K : ℝ) * (acH K b v : ℝ) *
        (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) ≤
        0.735 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ := by
      have h1 : (pxi r ^ (j + 1) * pxi r ^ (r * J)) ≤ 1 := by
        rw [← pow_add]; exact pow_le_one₀ hξpos.le hξle1
      have h2 : (pxi r ^ (j + 1) * pxi r ^ (r * J)) * (pT r (dK K) σ : ℝ) ≤
          1 * (pT r (dK K) σ : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (by simp only [pT]; positivity)
      have h3 : (dK K : ℝ) * (acH K b v : ℝ) * (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) ≤
          (dK K : ℝ) * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) := by
        have h4 : (0:ℝ) ≤ (dK K : ℝ) * (acH K b v : ℝ) := by positivity
        calc (dK K : ℝ) * (acH K b v : ℝ) * (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ))
            = ((dK K : ℝ) * (acH K b v : ℝ)) * ((pxi r ^ (j + 1) * pxi r ^ (r * J)) * (pT r (dK K) σ : ℝ)) := by
              ring
          _ ≤ ((dK K : ℝ) * (acH K b v : ℝ)) * (1 * (pT r (dK K) σ : ℝ)) :=
              mul_le_mul_of_nonneg_left h2 h4
          _ = (dK K : ℝ) * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) := by ring
      linarith [hdhT, h3]
    have hgf : ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ ≤
        2 * ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by
      have h14 := est14 H J hJ μ (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) hTst16 t0 t ht16 (s : ℂ)
      have h15 := est15 H J μ (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) hTst16 t0 t ht16 s hg
      rw [hsnorm] at h14
      have hdR : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd1
      have h0 := est16_half_arith (A := lnp φ p) (h := (acH K b v : ℝ)) (d := (dK K : ℝ))
        (ss := ((|s| : ℤ) : ℝ)) (S := (pS r (dK K) (acH K b v) : ℝ)) (D := pD r (dK K) σ)
        (Tst := pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ))
        (Hp := Height.logHeight p) (kumJ := kumJ K b v σ J) (J := J) (r := r)
        hr hdR hSpos hDpos.le hss0 hTs16 H.hp12 hs16 hkum22 hSD001
      have hmargin : Real.exp (lnp φ p + (acH K b v : ℝ) *
            (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) +
            (0.205 * (1 / (dK K : ℝ)) + 1.01 * (((|s| : ℤ) : ℝ) / 2 ^ J) /
                (pS r (dK K) (acH K b v) : ℝ) - 9 * 2 ^ r) *
              (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ) * 2 ≤
          Real.exp (lnp φ p - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
              ((dK K : ℝ) * (acH K b v : ℝ) *
                (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) +
                0.204 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ) +
              1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * pD r (dK K) σ + kumJ K b v σ J)) := by
        exact h0
      have hsub : 2 * ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ) - acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ ≤
          ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by
        have e1 : 2 * ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ) - acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ ≤
            2 * Real.exp (lnp φ p + (acH K b v : ℝ) *
              (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) +
              (0.205 * (1 / (dK K : ℝ)) + 1.01 * (((|s| : ℤ) : ℝ) / 2 ^ J) /
                  (pS r (dK K) (acH K b v) : ℝ) - 9 * 2 ^ r) *
                (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ) := by
          linarith [h14]
        have e2 : Real.exp (lnp φ p + (acH K b v : ℝ) *
              (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) +
              (0.205 * (1 / (dK K : ℝ)) + 1.01 * (((|s| : ℤ) : ℝ) / 2 ^ J) /
                  (pS r (dK K) (acH K b v) : ℝ) - 9 * 2 ^ r) *
                (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ) * 2 ≤
            Real.exp (lnp φ p - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
                ((dK K : ℝ) * (acH K b v : ℝ) *
                  (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) +
                  0.204 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ) +
                1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * pD r (dK K) σ + kumJ K b v σ J)) := hmargin
        have e3 : Real.exp (lnp φ p - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
                ((dK K : ℝ) * (acH K b v : ℝ) *
                  (pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r (dK K) σ : ℝ)) +
                  0.204 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ) +
                1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * pD r (dK K) σ + kumJ K b v σ J)) ≤
            ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := h15
        linarith [e1, e2, e3]
      have h3 : ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ ≤
          ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ) - acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ +
            ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by
        calc ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖
            = ‖(acg φ α b k L ι v σ p J μ t0 t (s : ℂ) - acf φ α b k L ι v σ p J μ t0 t (s : ℂ)) +
                acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by ring_nf
          _ ≤ ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ) - acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ +
                ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := norm_add_le _ _
          _ = ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ) - acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ +
                ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by rw [norm_sub_rev]
      linarith [hsub, h3]
    have hcore := extrap_core (fun z : ℂ => acf φ α b k L ι v σ p J μ t0 t z) hdiff
        (7.2 * (Sp : ℝ)) (1 / 3) 1 (7.2 * (Sp : ℝ) - ‖(s : ℂ)‖) (by norm_num) (by norm_num)
        (Finset.Icc (-(Sp : ℤ)) (Sp : ℤ)) hZ Tp (s : ℂ) hδ hsR' (by norm_num) hsZ U V W Y
        hU hV hW hY h1 h2
    have hfspos : 0 < ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by
      have hgpos : 0 < ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := norm_pos_iff.mpr hg
      linarith [hgf, hgpos]
    rw [hcore] at hfspos
    simp at hfspos
end Work.BW
