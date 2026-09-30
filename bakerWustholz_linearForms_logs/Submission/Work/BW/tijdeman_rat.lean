import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.tijdeman_int
import Submission.Work.BW.ap_factorial_dvd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `tijdeman_rat`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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

open Polynomial

/-! ### The binomial polynomial `C(X, n) = X(X-1)⋯(X-n+1)/n!` -/

/-- The binomial polynomial `binomPoly n = X (X - 1) ⋯ (X - n + 1) / n !` over `ℚ`. -/
noncomputable def binomPoly (n : ℕ) : Polynomial ℚ :=
  Polynomial.C ((n.factorial : ℚ)⁻¹) *
    ∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((i : ℚ)))

lemma binomPoly_eval (n : ℕ) (z : ℚ) :
    (binomPoly n).eval z
      = (n.factorial : ℚ)⁻¹ * ∏ i ∈ Finset.range n, (z - (i : ℚ)) := by
  simp only [binomPoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X]

lemma aeval_rat_eq_eval (z : ℚ) (p : Polynomial ℚ) :
    Polynomial.aeval z p = p.eval z := by
  simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

lemma binomPoly_natDegree_le (n : ℕ) : (binomPoly n).natDegree ≤ n := by
  rw [binomPoly]
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  calc (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((i : ℚ)))).natDegree
      ≤ ∑ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((i : ℚ))).natDegree :=
        Polynomial.natDegree_prod_le _ _
    _ = ∑ _i ∈ Finset.range n, (1 : ℕ) :=
        Finset.sum_congr rfl fun i _ => Polynomial.natDegree_X_sub_C _
    _ = n := by simp

/-- Coercing a finite product of naturals to `ℚ`. -/
lemma cast_prod_nat (s : Finset ℕ) (g : ℕ → ℕ) :
    ((∏ i ∈ s, g i : ℕ) : ℚ) = ∏ i ∈ s, ((g i : ℕ) : ℚ) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul, ih]

/-- `binomPoly n` at a natural number is the binomial coefficient `m.choose n`. -/
lemma binomPoly_eval_nat (n m : ℕ) :
    (binomPoly n).eval (m : ℚ) = (m.choose n : ℚ) := by
  rw [binomPoly_eval]
  rcases lt_or_ge m n with hmn | hnm
  · have hm : m ∈ Finset.range n := Finset.mem_range.mpr hmn
    rw [Finset.prod_eq_zero hm (by simp), Nat.choose_eq_zero_of_lt hmn]
    simp
  · have hfac : (∏ i ∈ Finset.range n, ((m : ℚ) - (i : ℚ)))
        = ((m.descFactorial n : ℕ) : ℚ) := by
      rw [Nat.descFactorial_eq_prod_range, cast_prod_nat]
      exact Finset.prod_congr rfl fun i hi =>
        (Nat.cast_sub (le_trans (Finset.mem_range.mp hi).le hnm)).symm
    rw [hfac, Nat.descFactorial_eq_factorial_mul_choose]
    have hn : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    push_cast
    field_simp

/-- A polynomial of `natDegree ≤ d` vanishing at `0, 1, …, d` is zero. -/
lemma eq_zero_of_eval_range_eq_zero {d : ℕ} {Q : Polynomial ℚ} (hdeg : Q.natDegree ≤ d)
    (h0 : ∀ m ≤ d, Q.eval (m : ℚ) = 0) : Q = 0 := by
  classical
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q
    ((Finset.range (d + 1)).image (fun m : ℕ => (m : ℚ))) ?_ ?_
  · intro y hy
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    exact h0 m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
  · rw [Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h), Finset.card_range]
    omega

/-- **Newton (binomial-basis) expansion of an integer-valued polynomial.**  If `P ∈ ℚ[X]` has
degree at most `d` and takes integral values at every integer, then it is an integral linear
combination of the binomial polynomials `binomPoly n`, `n ≤ d`.  The coefficients are the
iterated forward differences `Δ^n P (0) = ∑_{k ≤ n} (-1)^(n-k) * (n.choose k) * P k`. -/
theorem intVal_binom_expansion_self (d : ℕ) (P : Polynomial ℚ) (hnat : P.natDegree ≤ d)
    (hint : ∀ z : ℤ, ∃ N : ℤ, P.eval (z : ℚ) = (N : ℚ)) :
    ∃ c : ℕ → ℤ, P = ∑ n ∈ Finset.range (d + 1),
      Polynomial.C ((c n : ℚ)) * binomPoly n := by
  classical
  choose N hN using hint
  set f : ℕ → ℚ := fun m => P.eval (m : ℚ) with hf
  have hcZ : ∀ k : ℕ, ∃ M : ℤ, ((fwdDiff (1 : ℕ))^[k] f) 0 = (M : ℚ) := by
    intro k
    rw [fwdDiff_iter_eq_sum_shift]
    refine ⟨∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * N (j : ℤ), ?_⟩
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : f (0 + j • (1 : ℕ)) = (N (j : ℤ) : ℚ) := by
      simp only [zero_add, nsmul_eq_mul, mul_one, Nat.cast_id, hf]
      simpa using hN (j : ℤ)
    rw [h1]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  choose c hc using hcZ
  refine ⟨c, ?_⟩
  have hGN : ∀ m : ℕ, P.eval (m : ℚ)
      = ∑ k ∈ Finset.range (m + 1), (m.choose k : ℚ) * (c k : ℚ) := by
    intro m
    have hgoal : f m
        = ∑ k ∈ Finset.range (m + 1), (m.choose k : ℚ) * (c k : ℚ) := by
      have h1 := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) (f := f) m 0
      simp only [zero_add, nsmul_eq_mul, mul_one, Nat.cast_id] at h1
      rw [h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hc k]
    simpa [hf] using hgoal
  have hSP : (∑ n ∈ Finset.range (d + 1), Polynomial.C ((c n : ℚ)) * binomPoly n) - P = 0 := by
    refine eq_zero_of_eval_range_eq_zero (d := d) ?_ ?_
    · have hsub := Polynomial.natDegree_sub_le
        (∑ n ∈ Finset.range (d + 1), Polynomial.C ((c n : ℚ)) * binomPoly n) P
      refine le_trans hsub (max_le ?_ hnat)
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn => ?_
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      exact le_trans (binomPoly_natDegree_le n) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
    · intro m hm
      rw [Polynomial.eval_sub, Polynomial.eval_finsetSum, sub_eq_zero]
      have h1 : ∀ n : ℕ, ((Polynomial.C ((c n : ℚ)) * binomPoly n)).eval (m : ℚ)
          = (c n : ℚ) * (m.choose n : ℚ) := by
        intro n
        rw [Polynomial.eval_mul, Polynomial.eval_C, binomPoly_eval_nat]
      rw [Finset.sum_congr rfl (fun n _ => h1 n)]
      have hsub : (∑ n ∈ Finset.range (d + 1), (c n : ℚ) * (m.choose n : ℚ))
          = ∑ n ∈ Finset.range (m + 1), (c n : ℚ) * (m.choose n : ℚ) := by
        refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_).symm
        intro n hn hn2
        have hmn : m < n := by
          simp only [Finset.mem_range] at hn2
          omega
        simp [Nat.choose_eq_zero_of_lt hmn]
      rw [hsub, Finset.sum_congr rfl (fun n _ => mul_comm _ _), ← hGN m]
  exact (sub_eq_zero.mp hSP).symm

/-! ### Denominator clearing -/

/-- `∏_{i<n}(x/q - i) = (∏_{i<n}(x - i q))/q^n`. -/
lemma prod_slash (n q : ℕ) (x : ℤ) (hq : (q : ℚ) ≠ 0) :
    (∏ i ∈ Finset.range n, ((x : ℚ) / q - (i : ℚ)))
      = (∏ i ∈ Finset.range n, ((x : ℚ) - (i : ℚ) * (q : ℚ))) / (q : ℚ) ^ n := by
  have hfac : ∀ i ∈ Finset.range n, ((x : ℚ) / q - (i : ℚ))
      = ((x : ℚ) - (i : ℚ) * (q : ℚ)) / (q : ℚ) := by
    intro i _
    field_simp
  rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_range]

lemma prod_nat (n q : ℕ) (x : ℤ) (hq : (q : ℚ) ≠ 0) :
    (∏ i ∈ Finset.range n, ((x : ℚ) - (i : ℚ) * (q : ℚ)))
      = ((((q : ℤ) ^ n * ∏ j ∈ Finset.range n, (x - (j : ℤ) * (q : ℤ)) : ℤ)) : ℚ)
        / (q : ℚ) ^ n := by
  rw [eq_div_iff (pow_ne_zero n hq)]
  push_cast
  ring

/-- `q ^ (2 n)` clears the denominator of the `n`-th binomial coefficient of `x / q`. -/
lemma pow_binomPoly_eval {n : ℕ} {q : ℕ} (hq : 1 ≤ q) (x : ℤ) :
    ∃ N : ℤ, (q : ℚ) ^ (2 * n) * (binomPoly n).eval ((x : ℚ) / q) = (N : ℚ) := by
  have hq0 : (q : ℚ) ≠ 0 := by
    have hqn : (q : ℕ) ≠ 0 := by omega
    exact_mod_cast hqn
  obtain ⟨k, hk⟩ := ap_factorial_dvd n q x
  refine ⟨k, ?_⟩
  have hn : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hqn : (q : ℚ) ^ n ≠ 0 := pow_ne_zero n hq0
  rw [binomPoly_eval, prod_slash n q x hq0, prod_nat n q x hq0, hk]
  have h2 : (q : ℚ) ^ (2 * n) = (q : ℚ) ^ n * (q : ℚ) ^ n := by
    rw [← pow_add]; ring_nf
  rw [h2]
  push_cast
  field_simp

/-- A finite sum of rationals each of which is an integer is an integer. -/
lemma exists_sum_int {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, ∃ N : ℤ, f i = (N : ℚ)) : ∃ N : ℤ, (∑ i ∈ s, f i) = (N : ℚ) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
      obtain ⟨N, hN⟩ := h a (Finset.mem_insert_self a s)
      obtain ⟨M, hM⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      exact ⟨N + M, by rw [Finset.sum_insert ha, hN, hM]; push_cast; ring⟩

/-- **Denominator clearing for integer-valued polynomials.**  If a polynomial `P ∈ ℚ[X]` of
degree at most `d` takes integral values at every integer, then `q ^ (2 d) * P (x / q)` is an
integer for all `x : ℤ` and `q ≥ 1`. -/
theorem intVal_eval_rat (d : ℕ) (P : Polynomial ℚ) (hnat : P.natDegree ≤ d)
    (hint : ∀ z : ℤ, ∃ N : ℤ, P.eval (z : ℚ) = (N : ℚ)) (x : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    ∃ N : ℤ, (q : ℚ) ^ (2 * d) * P.eval ((x : ℚ) / q) = (N : ℚ) := by
  classical
  obtain ⟨c, hc⟩ := intVal_binom_expansion_self d P hnat hint
  have hterm : ∀ n ∈ Finset.range (d + 1), ∃ N : ℤ, (q : ℚ) ^ (2 * d) *
      ((Polynomial.C ((c n : ℚ)) * binomPoly n).eval ((x : ℚ) / q)) = (N : ℚ) := by
    intro n hn
    have hnd : n ≤ d := by
      have := Finset.mem_range.mp hn
      omega
    obtain ⟨M, hM⟩ := pow_binomPoly_eval (n := n) hq x
    refine ⟨c n * (q : ℤ) ^ (2 * d - 2 * n) * M, ?_⟩
    have hq0 : (q : ℚ) ≠ 0 := by
      have hqn : (q : ℕ) ≠ 0 := by omega
      exact_mod_cast hqn
    have hqn : (q : ℚ) ^ (2 * n) ≠ 0 := pow_ne_zero _ hq0
    have hMe : (binomPoly n).eval ((x : ℚ) / q) = (M : ℚ) / (q : ℚ) ^ (2 * n) := by
      rw [← hM]
      field_simp
    rw [Polynomial.eval_mul, Polynomial.eval_C, hMe]
    have h2 : (q : ℚ) ^ (2 * d) = (q : ℚ) ^ (2 * n) * (q : ℚ) ^ (2 * d - 2 * n) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h2]
    push_cast
    field_simp
  obtain ⟨N, hN⟩ := exists_sum_int _ _ hterm
  refine ⟨N, ?_⟩
  rw [hc, Polynomial.eval_finsetSum, Finset.mul_sum, hN]

/-- BW §12 (Tijdeman; Baker): for `q ≥ 1` and `qx ∈ ℤ`, `q^{2kl} u(k)^m Θ(x;k,l,m)` is an integer. Used at `q = 2^J` (resp. `2^{J+1}`) for the 2-adic Kummer term in (15), (17). Generalises the workspace's `tijdeman_int` (`q = 1`). (Checked exactly on `k ≤ 5`, `l ≤ 3`, all `m`, `q ≤ 8`, `|qx| ≤ 12`.) -/
theorem tijdeman_rat (q : ℕ) (hq : 1 ≤ q) (x : ℤ) (k l m : ℕ) :
    ∃ N : ℤ, (q : ℚ) ^ (2 * k * l) * (ulcm k : ℚ) ^ m *
      Polynomial.aeval ((x : ℚ) / q) (Polynomial.hasseDeriv m (deltaPoly k ^ l)) = N := by
  have hP : (Polynomial.C ((ulcm k : ℚ) ^ m) *
      Polynomial.hasseDeriv m (deltaPoly k ^ l)).natDegree ≤ k * l := by
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (Polynomial.natDegree_hasseDeriv_le _ _) ?_
    refine le_trans (Nat.sub_le _ _) ?_
    refine le_trans (Polynomial.natDegree_pow_le (p := deltaPoly k) (n := l)) ?_
    have hdeg : (deltaPoly k).natDegree ≤ k := by
      rw [deltaPoly]
      refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
      calc (∏ i ∈ Finset.range k, (Polynomial.X + Polynomial.C ((i : ℚ) + 1))).natDegree
          ≤ ∑ i ∈ Finset.range k,
              (Polynomial.X + Polynomial.C ((i : ℚ) + 1)).natDegree :=
            Polynomial.natDegree_prod_le _ _
        _ = ∑ _i ∈ Finset.range k, 1 :=
            Finset.sum_congr rfl fun i _ => Polynomial.natDegree_X_add_C _
        _ = k := by simp
    calc l * (deltaPoly k).natDegree ≤ l * k := Nat.mul_le_mul_left _ hdeg
      _ = k * l := Nat.mul_comm _ _
  have hint : ∀ z : ℤ, ∃ N : ℤ,
      (Polynomial.C ((ulcm k : ℚ) ^ m) *
        Polynomial.hasseDeriv m (deltaPoly k ^ l)).eval (z : ℚ) = (N : ℚ) := by
    intro z
    obtain ⟨N, hN⟩ := tijdeman_int z k l m
    refine ⟨N, ?_⟩
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    rw [show (Polynomial.hasseDeriv m (deltaPoly k ^ l)).eval (z : ℚ) = thetaRat z k l m by
      rw [thetaRat, aeval_rat_eq_eval]]
    exact hN
  obtain ⟨N, hN⟩ := intVal_eval_rat (k * l) _ hP hint x q hq
  refine ⟨N, ?_⟩
  rw [show (q : ℚ) ^ (2 * k * l) * (ulcm k : ℚ) ^ m *
        Polynomial.aeval ((x : ℚ) / q) (Polynomial.hasseDeriv m (deltaPoly k ^ l))
      = (q : ℚ) ^ (2 * (k * l)) *
        (Polynomial.C ((ulcm k : ℚ) ^ m) *
          Polynomial.hasseDeriv m (deltaPoly k ^ l)).eval ((x : ℚ) / q) by
    rw [Polynomial.eval_mul, Polynomial.eval_C, aeval_rat_eq_eval,
      show 2 * k * l = 2 * (k * l) by ring]
    ring]
  exact hN


end Work.BW
