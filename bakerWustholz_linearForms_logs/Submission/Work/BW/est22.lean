import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est21_l
import Submission.Work.BW.est17
import Submission.Work.BW.est_f_ge_half_g
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.num_D_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `est22`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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

-- The proof needs a larger heartbeat budget than the default: the local abbreviations (`SS`, `DD`,
-- …) make some `whnf`/`linarith` steps expensive.
set_option maxHeartbeats 4000000

/-- BW (22) at level `J` (p. 50; p. 58): same hypotheses at `l`, and `g(s/2;t) ≠ 0`, `2^{-J}|s| ≤ 4S`: `log|f_m(l)/f(s/2)| ≤ 2^r{dhT* − 7·893SD + 1·01·2^{-J}(|l/2^r| + |s/2|)D + kum_J}` (the `1/d` terms cancel up to 0·02). From the §17 bound for `f_m(l)` and `est17`. -/
theorem est22 {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) (μ : Fin r → ℕ) (Tst : ℝ)
    (hTst : Tst ≤ acT K σ) (Tp Tpp : ℝ) (hTp : 0 ≤ Tp) (hsum : Tp + Tpp ≤ Tst) (l : ℂ)
    (hvan : ∀ (t0' : ℕ) (t' : Fin (r - 1) → ℕ), ((t0' + ∑ m, t' m : ℕ) : ℝ) ≤ Tp + Tpp →
      acg φ α b k L ι v σ p J μ t0' t' l = 0)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tpp) (m : ℕ)
    (hm : (m : ℝ) ≤ Tp) (s : ℤ) (hs : ((|s| : ℤ) : ℝ) / 2 ^ J ≤ 4 * acS K r b v)
    (hg : acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2) ≠ 0) :
    ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖ ≤ ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ *
      Real.exp (2 ^ r * ((dK K : ℝ) * (acH K b v : ℝ) * Tst - 7.893 * acS K r b v * acD K σ +
        1.01 * ((‖l‖ / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * acD K σ + kumJ K b v σ J)) := by
  -- ## abbreviations
  set SS : ℝ := acS K r b v with hSS
  set DD : ℝ := acD K σ with hDD
  set RR : ℝ := 2 ^ r with hRR
  set HH : ℝ := (acH K b v : ℝ) with hHH
  set hP : ℝ := Height.logHeight p with hhP
  set kJJ : ℝ := kumJ K b v σ J with hkJJ
  set Zl : ℝ := ‖l‖ with hZl
  set sd : ℝ := ((|s| : ℤ) : ℝ) with hsd
  set VV : ℝ := (sd / 2) / 2 ^ J with hVV
  set uL : ℝ := (Zl / 2 ^ J) / SS with huL
  set qq : ℝ := 1 / (dK K : ℝ) with hqq
  set q2 : ℝ := 1 / (RR * (dK K : ℝ)) with hq2
  set HTT : ℝ := HH * Tst with hHTT
  set DHH : ℝ := (dK K : ℝ) * HH * Tst with hDHH
  set CC : ℝ := HTT + (0.282 * qq + 1.01 * uL - 9 * RR) * SS * DD with hCC
  set ZZ : ℝ := RR * (hP + (1 - q2) * (DHH + 0.204 * SS * DD) + 1.007 * VV * DD + 0.032 * SS * DD + kJJ) with hZZ
  set EE : ℝ := RR * ((dK K : ℝ) * HH * Tst - 7.893 * SS * DD + 1.01 * ((Zl / RR + sd / 2) / 2 ^ J) * DD + kJJ) with hEE
  set AA : ℝ := lnp φ p with hAA
  -- ## raw parameter facts
  have hr2 : 2 ≤ r := H.hr
  have hr2r : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hd1 : 1 ≤ dK K := Module.finrank_pos
  have hd1r : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd1
  have hdpos : (0 : ℝ) < (dK K : ℝ) := by linarith
  have h19 : 19 ≤ acH K b v := (acH_lower H).1
  have hSraw : acS K r b v = ((16 * r * dK K * acH K b v : ℕ) : ℝ) := by
    rw [acS, pS]
  have hS608raw : 608 ≤ acS K r b v := by
    rw [hSraw]
    have h1 : 16 * 2 * 1 * 19 ≤ 16 * r * dK K * acH K b v :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (le_refl 16) hr2) hd1) h19
    have h2 : 608 ≤ 16 * r * dK K * acH K b v := by norm_num at h1 ⊢; exact h1
    exact_mod_cast h2
  have hSpos0 : 0 < acS K r b v := by
    rw [hSraw]
    exact_mod_cast (by positivity : (0 : ℕ) < 16 * r * dK K * acH K b v)
  have hRr : (2 : ℝ) ≤ (r : ℝ) ^ r := by
    have h2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    have h3 : (r : ℝ) ≤ (r : ℝ) ^ r := by
      calc (r : ℝ) = (r : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (r : ℝ) ^ r :=
            pow_le_pow_right₀ (by linarith only [hr2r] : (1 : ℝ) ≤ (r : ℝ)) (by omega : 1 ≤ r)
    linarith only [h2, h3]
  have h32 : (32 : ℝ) ≤ 32 ^ (r + 1) := by
    have h3 : (32 : ℝ) ^ 1 ≤ 32 ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    simpa using h3
  have hlogrd : (1 : ℝ) ≤ Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
    have hexp : Real.exp 1 ≤ 2 * (r : ℝ) * (dK K : ℝ) := by
      have := Real.exp_one_lt_three
      nlinarith [hr2r, hd1r]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 * (r : ℝ) * (dK K : ℝ)) := Real.log_le_log (Real.exp_pos 1) hexp
  have hD1raw : 1 ≤ acD K σ := by
    have hDge : 2 * (r : ℝ) ^ r * 32 ^ (r + 1) * (dK K : ℝ) *
        Real.log (2 * (r : ℝ) * (dK K : ℝ)) ≤ acD K σ :=
      (num_D_lower hr2 hd1 σ (fun j => sigma_ge H j)).1
    have hAB : (2 : ℝ) * 2 * (32 * 1) ≤ (2 * (r : ℝ) ^ r) * (32 ^ (r + 1) * (dK K : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hRr (by norm_num))
        (mul_le_mul h32 hd1r (by norm_num) (by positivity)) (by norm_num) (by positivity)
    have hprod : (2 : ℝ) * 2 * (32 * 1) * 1 ≤ 2 * (r : ℝ) ^ r * 32 ^ (r + 1) * (dK K : ℝ) *
        Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
      convert mul_le_mul hAB hlogrd (by norm_num) (by positivity) using 1 <;> ring
    have h128 : (1 : ℝ) ≤ 2 * 2 * (32 * 1) * 1 := by norm_num
    linarith only [hDge, hprod, h128]
  -- ## converted facts
  have hSpos : 0 < SS := by rw [hSS]; exact hSpos0
  have hS608 : 608 ≤ SS := by rw [hSS]; exact hS608raw
  have hD1 : 1 ≤ DD := by rw [hDD]; exact hD1raw
  have hSne : SS ≠ 0 := ne_of_gt hSpos
  have hDn0 : (0 : ℝ) ≤ DD := by linarith only [hD1]
  have hDne : DD ≠ 0 := by linarith only [hD1]
  have hSn0 : (0 : ℝ) ≤ SS := le_of_lt hSpos
  have hTpp0 : 0 ≤ Tpp :=
    le_trans (by positivity : (0 : ℝ) ≤ ((t0 + ∑ m, t m : ℕ) : ℝ)) ht
  have hTst0 : 0 ≤ Tst := by
    have htp : Tp ≤ Tst := by linarith only [hsum, hTpp0]
    exact le_trans hTp htp
  have hHH0 : 0 ≤ HH := by rw [hHH]; positivity
  have hRRn : RR ≠ 0 := by rw [hRR]; positivity
  have h2Jn : (2 : ℝ) ^ J ≠ 0 := by positivity
  have hRRdn : RR * (dK K : ℝ) ≠ 0 := by
    have : (0 : ℝ) < RR * (dK K : ℝ) := by rw [hRR]; positivity
    exact ne_of_gt this
  have hRR4 : 4 ≤ RR := by
    rw [hRR]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr2
  have hRR0 : 0 ≤ RR := by linarith only [hRR4]
  have hlog2 : Real.log 2 ≤ 0.7 := by
    have h := Real.log_two_lt_d9
    linarith only [h]
  -- ## Tst, height and Kummer bounds
  have hTst_le : Tst ≤ 11.75 * (r : ℝ) * DD := by
    have hfl : (pT r (dK K) σ : ℝ) ≤ 11.75 * (r : ℝ) * (pD r (dK K) σ) := by
      rw [pT]; exact Nat.floor_le (by positivity)
    have h1 : Tst ≤ 11.75 * (r : ℝ) * (pD r (dK K) σ) := le_trans hTst hfl
    rwa [show pD r (dK K) σ = DD from hDD.symm] at h1
  have hSSp : SS = ((16 * r * dK K * acH K b v : ℕ) : ℝ) := by rw [hSS]; exact hSraw
  have hfact : (dK K : ℝ) * HH * (11.75 * (r : ℝ) * DD) = 0.734375 * SS * DD := by
    rw [hHH, hSSp]
    push_cast
    ring
  have hDHH_le : DHH ≤ 0.735 * SS * DD := by
    have h1 : DHH ≤ (dK K : ℝ) * HH * (11.75 * (r : ℝ) * DD) := by
      rw [hDHH]
      exact mul_le_mul_of_nonneg_left hTst_le (by rw [hHH]; positivity)
    calc DHH ≤ (dK K : ℝ) * HH * (11.75 * (r : ℝ) * DD) := h1
      _ = 0.734375 * SS * DD := hfact
      _ ≤ 0.735 * SS * DD := by
        have h0 : (0:ℝ) ≤ SS * DD := mul_nonneg hSn0 hDn0
        calc (0.734375:ℝ) * SS * DD = 0.734375 * (SS * DD) := by ring
          _ ≤ 0.735 * (SS * DD) := mul_le_mul_of_nonneg_right (by norm_num) h0
          _ = 0.735 * SS * DD := by ring
  have hHTT_le : HTT ≤ 0.735 * SS * DD := by
    have h1 : HTT ≤ DHH := by
      have hdH : HH * Tst ≤ (dK K : ℝ) * (HH * Tst) := by
        calc HH * Tst = 1 * (HH * Tst) := by ring
          _ ≤ (dK K : ℝ) * (HH * Tst) :=
              mul_le_mul_of_nonneg_right hd1r (mul_nonneg hHH0 hTst0)
      calc HTT = HH * Tst := hHTT
        _ ≤ (dK K : ℝ) * (HH * Tst) := hdH
        _ = DHH := by rw [hDHH]; ring
    linarith [hDHH_le]
  have hhp_le : hP ≤ 0.85 * SS * DD := by rw [hhP, hSS, hDD]; exact H.hp12
  have hkum_le : kJJ ≤ 2.2 * SS * DD := by
    have hlogpos : 0 < Real.log (2 * (r : ℝ) * (dK K : ℝ)) :=
      Real.log_pos (by nlinarith [hr2r, hd1r])
    have hJle : (J : ℝ) ≤ 50 * Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
      have h1 : (pI r (dK K) : ℝ) ≤ 50 * Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
        rw [pI]; exact Nat.floor_le (by positivity)
      calc (J : ℝ) ≤ (pI r (dK K) : ℝ) := by exact_mod_cast hJ
        _ ≤ 50 * Real.log (2 * (r : ℝ) * (dK K : ℝ)) := h1
    have hcoef : 0.044 * (J : ℝ) / Real.log (2 * (r : ℝ) * (dK K : ℝ)) ≤ 2.2 := by
      rw [div_le_iff₀ hlogpos]; nlinarith only [hlogpos, hJle]
    have hsig : 0 ≤ ∏ j, σ j := by
      refine Finset.prod_nonneg (fun j _ => ?_)
      exact le_of_lt (H.hBH.2.2.2.2.1 j)
    have hDnn : 0 ≤ pD r (dK K) σ := by
      rw [pD]
      have h1 : (0:ℝ) ≤ 2 * (r:ℝ)^r := by positivity
      have h2 : (0:ℝ) ≤ (32 * (dK K:ℝ))^(r+1) := by positivity
      have h3 : (0:ℝ) ≤ Real.log (2 * (r:ℝ) * (dK K:ℝ)) := le_of_lt hlogpos
      have h4 : (0:ℝ) ≤ ((2 * (r:ℝ)^r) * (32 * (dK K:ℝ))^(r+1)) *
          Real.log (2 * (r:ℝ) * (dK K:ℝ)) := mul_nonneg (mul_nonneg h1 h2) h3
      exact mul_nonneg h4 hsig
    calc kJJ = kumJ K b v σ J := hkJJ.symm
      _ = 0.044 * (J : ℝ) / Real.log (2 * (r : ℝ) * (dK K : ℝ)) * acS K r b v * acD K σ := by
          rw [kumJ]
      _ = (0.044 * (J : ℝ) / Real.log (2 * (r : ℝ) * (dK K : ℝ))) * (acS K r b v * acD K σ) := by ring
      _ ≤ 2.2 * (acS K r b v * acD K σ) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg (le_of_lt hSpos0) hDnn)
      _ = 2.2 * SS * DD := by rw [hSS, hDD]; ring
  -- ## V, u, q facts
  have hV0 : 0 ≤ VV := by rw [hVV]; positivity
  have hV2 : VV ≤ 2 * SS := by
    have hhs : sd / 2 ^ J ≤ 4 * SS := by rw [hsd, hSS]; exact hs
    have h2J : (0 : ℝ) < 2 ^ J := by positivity
    rw [hVV, div_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * 2 ^ J)]
    have hmul : (sd / 2 ^ J) * 2 ^ J ≤ (4 * SS) * 2 ^ J :=
      mul_le_mul_of_nonneg_right hhs (le_of_lt h2J)
    have heq : (sd / 2 ^ J) * 2 ^ J = sd := div_mul_cancel₀ sd (ne_of_gt h2J)
    linarith only [hmul, heq]
  have huL_eq : uL * SS = Zl / 2 ^ J := by rw [huL]; field_simp
  have hqq_eq : qq * (dK K : ℝ) = 1 := by rw [hqq]; field_simp
  have hq2_eq : q2 * (RR * (dK K : ℝ)) = 1 := by rw [hq2]; field_simp
  have hqq1 : qq ≤ 1 := by rw [hqq, div_le_one hdpos]; exact hd1r
  have hq20 : 0 ≤ q2 := by rw [hq2]; positivity
  -- ## β : CC + ZZ + log 2 ≤ EE
  have hβ : CC + ZZ + Real.log 2 ≤ EE := by
    have hid : EE - (CC + ZZ) = (0.021 * RR - 0.078 * qq) * (SS * DD) +
        RR * (0.85 * SS * DD - hP) + 0.003 * RR * VV * DD := by
      rw [hEE, hCC, hZZ, hHTT, hDHH, hq2, hqq, huL, hVV, hRR]
      field_simp [hSne, hRRn, h2Jn, hdpos.ne', hRRdn]
      ring
    have h2 : 0 ≤ RR * (0.85 * SS * DD - hP) := by nlinarith only [hhp_le, hRR0]
    have h3 : 0 ≤ 0.003 * RR * VV * DD :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 0.003) hRR0) hV0) hDn0
    have h4 : Real.log 2 ≤ (0.021 * RR - 0.078 * qq) * (SS * DD) := by
      have hc : 0.006 ≤ 0.021 * RR - 0.078 * qq := by nlinarith only [hRR4, hqq1]
      have hSD : (608 : ℝ) ≤ SS * DD := by nlinarith only [hS608, hD1]
      have hprod : 0.006 * 608 ≤ (0.021 * RR - 0.078 * qq) * (SS * DD) := by
        nlinarith only [hc, hSD]
      linarith only [hprod, hlog2]
    linarith only [hid, h2, h3, h4]
  -- ## exponent identities
  have hAC : AA + CC = lnp φ p + (acH K b v : ℝ) * Tst + 0.282 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ +
      1.01 * (‖l‖ / 2 ^ J) * acD K σ - 9 * 2 ^ r * acS K r b v * acD K σ := by
    rw [hAA, hCC, hHTT, hqq, huL, hRR, hHH, hSS, hDD]
    field_simp [hSne, hRRn, h2Jn, hdpos.ne']
    ring
  have hAZ : AA - ZZ = lnp φ p - 2 ^ r * (Height.logHeight p +
      (1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
      1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J) := by
    rw [hAA, hZZ, hhP, hq2, hDHH, hVV, hkJJ, hRR, hHH, hSS, hDD, hsd]
  have hEEeq : Real.exp EE = Real.exp (2 ^ r * ((dK K : ℝ) * (acH K b v : ℝ) * Tst - 7.893 * acS K r b v * acD K σ +
      1.01 * ((‖l‖ / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * acD K σ + kumJ K b v σ J)) := by
    rw [hEE, hRR, hHH, hSS, hDD, hkJJ, hZl, hsd]
  -- ## the three estimates
  have h13 : ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖ ≤ Real.exp (AA + CC) := by
    rw [hAC]
    exact est21_l H J hJ μ Tst hTst Tp Tpp hTp hsum l hvan t0 t ht m hm
  have htTst : ((t0 + ∑ mm, t mm : ℕ) : ℝ) ≤ Tst := by linarith only [ht, hsum, hTp]
  have h15 : Real.exp (AA - ZZ) ≤ ‖acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ := by
    rw [hAZ]
    exact est17 H J μ Tst hTst t0 t htTst s hg
  have hB2 : ‖acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ ≤
      2 * ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ :=
    (est_f_ge_half_g H J hJ μ Tst hTst t0 t htTst s).2 hs
  have hf2 : Real.exp (AA - ZZ) / 2 ≤ ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ := by
    linarith only [h15, hB2]
  have hexp : Real.exp (AA - ZZ - Real.log 2) ≤ ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ := by
    have h2exp : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
    have he : Real.exp (AA - ZZ - Real.log 2) = Real.exp (AA - ZZ) / 2 := by
      rw [Real.exp_sub, h2exp]
    rw [he]; exact hf2
  calc ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖
      ≤ Real.exp (AA + CC) := h13
    _ = Real.exp EE * Real.exp (AA + CC - EE) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp EE * Real.exp (AA - ZZ - Real.log 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hβ])) (Real.exp_nonneg EE)
    _ ≤ Real.exp EE * ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg EE)
    _ = ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ * Real.exp EE := by ring
    _ = ‖acf φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ *
        Real.exp (2 ^ r * ((dK K : ℝ) * (acH K b v : ℝ) * Tst - 7.893 * acS K r b v * acD K σ +
          1.01 * ((‖l‖ / 2 ^ r + ((|s| : ℤ) : ℝ) / 2) / 2 ^ J) * acD K σ + kumJ K b v σ J)) := by
        rw [hEEeq]

end Work.BW
