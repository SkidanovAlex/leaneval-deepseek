import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.Qpoly_degreeOf
import Submission.Work.BW.applyDer_Qpoly_span
import Submission.Work.BW.yc_defs
import Submission.Work.BW.yc_roots_mult_eq_zero
import Submission.Work.BW.yc_count
import Submission.Work.BW.yc_hasseDeriv_comp_affine
import Submission.Work.BW.yc_main_identity
import Submission.Work.BW.yc_deriv_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `yfree_contradiction`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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

/-! ### Helpers for `yfree_contradiction`

The degenerate-level argument: at a level `J` where every `D_j < 2^J`, the exponents
`λ_j / 2^J` of `Qdesc` vanish, so `Q^{(J)}_μ(·;t₀,0)` is a polynomial in `Y₀` alone and its curve
values are those of the univariate polynomial `ycQ` (`yc_defs`).  Its `t₀`-th Hasse derivative is
the next twist (`yc_deriv_eq`), so (29) at level `J` says that `ycQ` has a zero of multiplicity
`⌊ξT^{(J)}⌋+1` at each of the `2⌊2S^{(J)}⌋+1` points `s ∈ ballZ (2S^{(J)})`.  Since the degree
bound `h(D₀+1)` is smaller than the product `yc_count`, `ycQ = 0`, and `Q` vanishes on all of
`ℂ` on the curve; being a polynomial in `Y₀` alone it must be zero, contradicting `hne`. -/

open MvPolynomial

/-- A finite sum of univariate polynomials of degree `≤ d` has degree `≤ d`. -/
lemma yc_natDegree_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (d : ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d) : (∑ i ∈ s, f i).natDegree ≤ d := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- `fAt` at a natural argument is evaluation at `ptS`. -/
lemma yc_fAt_natCast {r : ℕ} (ℓ : Fin r → ℂ) (P : MvPolynomial (Fin (r + 1)) ℂ) (s : ℕ) :
    fAt ℓ P (s : ℂ) = MvPolynomial.eval (ptS ℓ s) P := rfl

/-- The `Y₀`-degree bound for the univariate shadow of `Q^{(J)}_μ(·;0)`. -/
lemma ycQ_natDegree {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) :
    (ycQ φ h D0 Dj p J μ 0).natDegree ≤ h * (D0 + 1) := by
  classical
  rw [ycQ]
  refine yc_natDegree_finset_sum_le _ _ _ fun lm _ => ?_
  by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
  · rw [if_pos hc]
    refine Polynomial.natDegree_mul_le.trans ?_
    have hC : (Polynomial.C (φ (p lm) * (ulcm h : ℂ) ^ 0)).natDegree ≤ 0 := by
      rw [Polynomial.natDegree_C]
    have hY : (ycY0 h ((lm.2.1 : ℕ) + 1) 0 (((2 : ℂ) ^ J)⁻¹) ((lm.1 : ℕ) : ℂ)).natDegree
        ≤ h * (D0 + 1) := by
      rw [ycY0]
      refine Polynomial.natDegree_comp_le.trans ?_
      have hp : (ycP h ((lm.2.1 : ℕ) + 1) 0).natDegree ≤ h * (D0 + 1) := by
        rw [ycP, Polynomial.hasseDeriv_zero]
        refine Polynomial.natDegree_map_le.trans ?_
        refine Polynomial.natDegree_pow_le.trans ?_
        refine (Nat.mul_le_mul_left _ (natDegree_deltaPoly_le h)).trans ?_
        refine (Nat.mul_le_mul_right h
          (Nat.succ_le_succ (Nat.lt_succ_iff.mp lm.2.1.isLt))).trans ?_
        exact le_of_eq (Nat.mul_comm _ _)
      have hq : (Polynomial.C (((2 : ℂ) ^ J)⁻¹) * Polynomial.X +
          Polynomial.C ((lm.1 : ℕ) : ℂ)).natDegree ≤ 1 := by
        refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · refine Polynomial.natDegree_mul_le.trans ?_
          simp
        · simp
      calc (ycP h ((lm.2.1 : ℕ) + 1) 0).natDegree *
            (Polynomial.C (((2 : ℂ) ^ J)⁻¹) * Polynomial.X +
              Polynomial.C ((lm.1 : ℕ) : ℂ)).natDegree
          ≤ (h * (D0 + 1)) * 1 := Nat.mul_le_mul hp hq
        _ = h * (D0 + 1) := Nat.mul_one _
    omega
  · rw [if_neg hc]
    simp

/-- At a degenerate level, `Q^{(J)}_μ(·;t₀,t)` is constant in `Y₁,…,Y_r`. -/
lemma yc_yfree {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (hDj : ∀ j, (Dj j : ℝ) < 2 ^ J) (i : Fin r) :
    (Qdesc φ b k L ι h D0 Dj p J μ t0 t).degreeOf i.succ = 0 := by
  classical
  rw [Qdesc]
  refine le_antisymm ?_ (Nat.zero_le _)
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro lm _
  have he : ∀ j, (lm.2.2 j : ℕ) / 2 ^ J = 0 := by
    intro j
    have h1 : (lm.2.2 j : ℕ) ≤ Dj j := Nat.lt_succ_iff.mp (lm.2.2 j).isLt
    have h2 : Dj j < 2 ^ J := by exact_mod_cast hDj j
    exact Nat.div_eq_of_lt (lt_of_le_of_lt h1 h2)
  by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
  · rw [if_pos hc]
    set c : ℂ := φ (p lm) *
      (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) * (ulcm h : ℂ) ^ t0 with hcdef
    set A : MvPolynomial (Fin (r + 1)) ℂ :=
      Polynomial.aeval
        (MvPolynomial.C (((2 : ℂ) ^ J)⁻¹) * MvPolynomial.X (0 : Fin (r + 1)) +
          MvPolynomial.C ((lm.1 : ℕ) : ℂ))
        (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1))) with hAdef
    set B : MvPolynomial (Fin (r + 1)) ℂ :=
      ∏ j : Fin r, MvPolynomial.X j.succ ^ ((lm.2.2 j : ℕ) / 2 ^ J) with hBdef
    have hB1 : B = 1 := by
      rw [hBdef]
      exact Finset.prod_eq_one fun j _ => by rw [he j, pow_zero]
    have hA0 : A.degreeOf i.succ ≤ 0 := by
      rw [hAdef]
      refine (aeval_degreeOf_le i.succ _ _).trans ?_
      have hx : (MvPolynomial.C (((2 : ℂ) ^ J)⁻¹) * MvPolynomial.X (0 : Fin (r + 1)) +
          MvPolynomial.C ((lm.1 : ℕ) : ℂ)).degreeOf i.succ = 0 := by
        refine le_antisymm ?_ (Nat.zero_le _)
        refine (MvPolynomial.degreeOf_add_le _ _ _).trans ?_
        have h1 : (MvPolynomial.C (((2 : ℂ) ^ J)⁻¹) *
            MvPolynomial.X (0 : Fin (r + 1))).degreeOf i.succ ≤ 0 :=
          (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
            (le_of_eq (MvPolynomial.degreeOf_X_of_ne (Fin.succ_ne_zero i)))
        have h2 : (MvPolynomial.C ((lm.1 : ℕ) : ℂ)).degreeOf i.succ ≤ 0 := by
          rw [MvPolynomial.degreeOf_C]
        omega
      rw [hx, Nat.mul_zero]
    rw [hB1, mul_one]
    calc (MvPolynomial.C c * A).degreeOf i.succ
        ≤ (MvPolynomial.C c).degreeOf i.succ + A.degreeOf i.succ :=
          MvPolynomial.degreeOf_mul_le _ _ _
      _ ≤ 0 + 0 := add_le_add (by rw [MvPolynomial.degreeOf_C]) hA0
      _ = 0 := by simp
  · rw [if_neg hc]
    simp

/-- The `2P+1` integer points `-P, …, P`, as complex numbers. -/
def ycPt (P : ℕ) (i : Fin (2 * P + 1)) : ℂ :=
  ((((i : ℕ) : ℤ) - (P : ℤ) : ℤ) : ℂ)

lemma ycPt_injective (P : ℕ) : Function.Injective (ycPt P) := by
  intro i j hij
  have h1 : ((((i : ℕ) : ℤ) - (P : ℤ) : ℤ) : ℂ) =
      (((((j : ℕ) : ℤ) - (P : ℤ) : ℤ)) : ℂ) := hij
  have h1' : (((i : ℕ) : ℤ) - (P : ℤ)) = (((j : ℕ) : ℤ) - (P : ℤ)) := by
    exact_mod_cast h1
  have h2 : (i : ℕ) = (j : ℕ) := by omega
  exact Fin.ext h2

lemma ycPt_ball (P : ℕ) (i : Fin (2 * P + 1)) :
    (((|(((i : ℕ) : ℤ) - (P : ℤ))| : ℤ) : ℝ)) ≤ (P : ℝ) := by
  have habs : |(((i : ℕ) : ℤ) - (P : ℤ))| ≤ (P : ℤ) := by
    rw [abs_le]
    have hi : ((i : ℕ) : ℤ) ≤ 2 * (P : ℤ) := by
      have h := i.isLt
      omega
    constructor <;> omega
  exact_mod_cast habs


/-- Degenerate levels: if every `D_j < 2^J` then `Q^{(J)}_μ(·;0)` is a polynomial in `Y₀` alone (`Qdesc_degreeOf`) of degree `≤ h(D₀+1)`, and (29) at level `J` gives it `2⌊2S^{(J)}⌋+1` integer zeros each of multiplicity `> ξT^{(J)}` (`∂₀^{t₀}` = multiple of `Q^{(J)}(·;t₀,0)`, `applyDer_Qdesc_span`); since `S^{(J)}T^{(J)} = ST` and `ξ^{-rJ} > 11·75rD` when `ξT^{(J)} < 1`, the count exceeds `h(D₀+1)`, so `Q^{(J)}_μ(·;0) = 0`. Extends H3's `mvpoly_eq_zero_of_ptS_vanishing` to multiplicities. This is how BW's construction itself refutes the hypotheses in the small-σ regime (where BW's literal §20 estimates fail for large `J`). -/
theorem yfree_contradiction {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (μ : Fin r → ℕ)
    (hdeg : ∀ j, (pDj r (dK K) σ j : ℝ) < 2 ^ J) (hne : QJ φ b k L ι v σ p J μ 0 0 ≠ 0)
    (hinv : VanSet (fun i => lamP φ α v L i) (QJ φ b k L ι v σ p J μ) (ballZ (2 * SJ K r b v J)) 1 (pxi r * TJ K σ J)) :
    False := by
  classical
  have hr : 2 ≤ r := H.hr
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  -- ### 1.  `σ_j ≥ 1/d` from the basic hypothesis `BH`
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := by
    intro j
    have hF := H.hBH.2.2.2.2.2.1 j
    simp only [hmod] at hF
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hF)
  -- ### 2.  positivity of `ξ`, and of the two floors
  have hξpos : 0 < pxi r := by
    have h1 : (0.536 : ℝ) / r ≤ 0.268 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    simp only [pxi]
    linarith
  have hξnn : 0 ≤ pxi r := le_of_lt hξpos
  have hSJnn : 0 ≤ SJ K r b v J := by
    simp only [SJ, acS]
    exact mul_nonneg (zpow_nonneg hξnn (-((r * J : ℕ) : ℤ))) (Nat.cast_nonneg _)
  have hTJnn : 0 ≤ TJ K σ J := by
    simp only [TJ, acT]
    exact mul_nonneg (zpow_nonneg hξnn (r * J)) (Nat.cast_nonneg _)
  -- ### 3.  the counting inequality, and the degree bound for the shadow
  have hcount := yc_count (K := K) b v σ hr hσ J
  have hdegQ : (ycQ φ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ 0).natDegree <
      (⌊pxi r * TJ K σ J⌋₊ + 1) * (2 * ⌊2 * SJ K r b v J⌋₊ + 1) :=
    lt_of_le_of_lt (ycQ_natDegree φ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ) hcount
  have hfloor : ((⌊2 * SJ K r b v J⌋₊ : ℕ) : ℝ) ≤ 2 * SJ K r b v J :=
    Nat.floor_le (mul_nonneg (by norm_num) hSJnn)
  -- ### 4.  (29) at level `J`: the shadow has a zero of multiplicity `⌊ξT^{(J)}⌋+1`
  --          at each of the points `ycPt`
  have hroot : ∀ (i : Fin (2 * ⌊2 * SJ K r b v J⌋₊ + 1)) (j : ℕ),
      j < ⌊pxi r * TJ K σ J⌋₊ + 1 →
      Polynomial.eval (ycPt ⌊2 * SJ K r b v J⌋₊ i)
        (Polynomial.hasseDeriv j
          (ycQ φ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ 0)) = 0 := by
    intro i j hj
    -- the derivative order is admissible
    have hjcast : (j : ℝ) ≤ pxi r * TJ K σ J := by
      have h1 : (j : ℝ) ≤ ((⌊pxi r * TJ K σ J⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast (Nat.lt_succ_iff.mp hj)
      exact h1.trans (Nat.floor_le (mul_nonneg hξnn hTJnn))
    -- the point lies in the ball `|s| ≤ 2S^{(J)}`
    have hmem : (((i : ℕ) : ℤ) - (⌊2 * SJ K r b v J⌋₊ : ℤ)) ∈ ballZ (2 * SJ K r b v J) := by
      simp only [ballZ, Set.mem_setOf_eq]
      exact le_trans (ycPt_ball ⌊2 * SJ K r b v J⌋₊ i) hfloor
    -- (29) at level `J`
    have hvan := hinv (((i : ℕ) : ℤ) - (⌊2 * SJ K r b v J⌋₊ : ℤ)) hmem j 0
      (by simpa using hjcast)
    -- the `j`-th twist of the shadow vanishes at the point
    have hzero : Polynomial.eval (ycPt ⌊2 * SJ K r b v J⌋₊ i)
        (ycQ φ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ j) = 0 := by
      rw [← yc_main_identity (fun i => lamP φ α v L i) φ b k L ι (acH K b v)
        (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ j hdeg (ycPt ⌊2 * SJ K r b v J⌋₊ i)]
      simp only [QJ, Nat.cast_one, div_one] at hvan
      exact hvan
    -- `yc_deriv_eq` identifies the twist with the Hasse derivative
    have hder := congrArg (Polynomial.eval (ycPt ⌊2 * SJ K r b v J⌋₊ i))
      (yc_deriv_eq (K := K) φ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ j)
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at hder
    rw [hzero, mul_zero] at hder
    exact (mul_eq_zero.mp hder).resolve_left
      (pow_ne_zero _ (by exact_mod_cast ulcm_ne_zero (acH K b v)))
  -- ### 5.  the shadow is zero
  have hQ0 : ycQ φ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ 0 = 0 :=
    yc_roots_mult_eq_zero _ _ _ (ycPt ⌊2 * SJ K r b v J⌋₊)
      (ycPt_injective _) hroot hdegQ
  -- ### 6.  `Q^{(J)}_μ(·;0)` is constant in `Y₁,…,Y_r`
  have hyfree : ∀ j : Fin (r + 1), j ≠ 0 →
      (QJ φ b k L ι v σ p J μ 0 0).degreeOf j = 0 := by
    intro j hj
    revert hj
    refine Fin.cases ?_ (fun i _ => ?_) j
    · intro hj
      exact absurd rfl hj
    · exact yc_yfree φ b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ 0 0 hdeg i
  -- ### 7.  so it vanishes on the whole curve `s ↦ (s, α'^s)`
  have hvan : ∀ s : ℕ, MvPolynomial.eval (ptS (fun i => lamP φ α v L i) s)
      (QJ φ b k L ι v σ p J μ 0 0) = 0 := by
    intro s
    have hmain := yc_main_identity (fun i => lamP φ α v L i) φ b k L ι (acH K b v)
      (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ 0 hdeg (s : ℂ)
    rw [hQ0] at hmain
    simp only [Polynomial.eval_zero] at hmain
    rw [← yc_fAt_natCast (fun i => lamP φ α v L i) (QJ φ b k L ι v σ p J μ 0 0) s]
    exact hmain
  -- ### 8.  a `Y₀`-polynomial vanishing on the curve is zero — contradicting `hne`
  exact hne (mvpoly_eq_zero_of_ptS_vanishing (fun i => lamP φ α v L i)
    (QJ φ b k L ι v σ p J μ 0 0) hyfree (fun s _ => hvan s))

end Work.BW
