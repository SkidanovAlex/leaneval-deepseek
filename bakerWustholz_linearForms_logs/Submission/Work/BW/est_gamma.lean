import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `est_gamma`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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

/-! ### Two elementary facts about the modified height -/

/-- `h'(α) = max(h(α), |log α|/d, 1/d) ≥ 1/d`. -/
lemma modifiedHeight_ge_inv_dK {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (α : K) :
    (1 : ℝ) / (dK K : ℝ) ≤ BakerWustholz.modifiedHeight φ α := by
  simp only [BakerWustholz.modifiedHeight, dK]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- `|log φ(α)| ≤ d · h'(α)`. -/
lemma norm_log_le_dK_mul_modifiedHeight {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (α : K) : ‖Complex.log (φ α)‖ ≤ (dK K : ℝ) * BakerWustholz.modifiedHeight φ α := by
  have hd : 0 < (dK K : ℝ) := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast this
  have hle : ‖Complex.log (φ α)‖ / (dK K : ℝ) ≤ BakerWustholz.modifiedHeight φ α := by
    simp only [BakerWustholz.modifiedHeight, dK]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  calc ‖Complex.log (φ α)‖ = (‖Complex.log (φ α)‖ / (dK K : ℝ)) * (dK K : ℝ) := by field_simp
    _ ≤ BakerWustholz.modifiedHeight φ α * (dK K : ℝ) :=
        mul_le_mul_of_nonneg_right hle (le_of_lt hd)
    _ = (dK K : ℝ) * BakerWustholz.modifiedHeight φ α := by ring

/-- BW §13/§17, the core estimate: for any `X` with `‖X‖ ≤ d·h'(α_{ι m})`,
`‖γ_{ι m} · X‖ ≤ e^{hL} 2^v D ≤ e^{h+1} D`, where `D = pD r d σ` and
`γ_j = γ_j(λ) = ∑ᵢ (b_k ∂L_i/∂z_j − b_j ∂L_i/∂z_k) λ_i`, `λ_i ≤ D_i`.

The proof uses §11's estimate `∑_t |L_{i t}| h'(α_t) ≤ 2^v σ_i` twice: once through
`|L_{i j}| h'(α_j) + |L_{i k}| h'(α_k) ≤ 2^v σ_i` (the two summands are distinct columns of the
same row), which supplies the bound `(|b_k L_{i j}| + |b_j L_{i k}|) λ_i ≤ e^{hL} 2^v d σ_i λ_i`,
and once through `∑_i d σ_i λ_i ≤ D` coming from `λ_i ≤ D_i = ⌊D/(r d σ_i)⌋`. -/
private lemma est_gamma_aux {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (m : Fin (r - 1)) (lm : Fin r → ℕ)
    (hlm : ∀ j, lm j ≤ pDj r (dK K) σ j) (X : ℂ)
    (hX : ‖X‖ ≤ (dK K : ℝ) * BakerWustholz.modifiedHeight φ (α (ι m))) :
    ‖gam b k L (ι m) lm * X‖ ≤ Real.exp ((acH K b v : ℝ) + 1) * pD r (dK K) σ := by
  obtain ⟨hst, hr, hBH, hι, hp0, hp9, hp12, h10⟩ := H
  obtain ⟨hLI, hbspan, hα'ne, hKum, hσpos, hα'hmod, hrow, hkapp⟩ := hBH
  obtain ⟨hιne, hιind⟩ := hι
  obtain ⟨hn2, hαne, hlogind, hgcd, hbk, hmhle, hXbw, hexp1c, hlogc⟩ := hst
  have hd : 0 < (dK K : ℝ) := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast this
  have hd1 : 1 ≤ dK K := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.cast_pos.mp hd))
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
  have hmh_ge : ∀ t : Fin n, (1 : ℝ) / (dK K : ℝ) ≤ BakerWustholz.modifiedHeight φ (α t) :=
    fun t => modifiedHeight_ge_inv_dK φ (α t)
  have hmh_nonneg : ∀ t : Fin n, 0 ≤ BakerWustholz.modifiedHeight φ (α t) := by
    intro t
    exact le_trans (div_nonneg one_pos.le hd.le) (hmh_ge t)
  have hb : ∀ i : Fin n, |((b i : ℤ) : ℝ)| ≤ Real.exp (hL b (dK K)) := by
    intro i
    have habs : |((b i : ℤ) : ℝ)| = ((b i).natAbs : ℝ) := by
      rw [← Int.cast_abs]; congr 1; exact (Int.natCast_natAbs (b i)).symm
    rw [habs]
    have hM : ((b i).natAbs : ℝ) ≤ ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ) := by
      exact_mod_cast Finset.le_sup (f := fun i => (b i).natAbs) (Finset.mem_univ i)
    have hMe : ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ) ≤ Real.exp (hL b (dK K)) := by
      by_cases h : (Finset.univ.sup fun i => (b i).natAbs) = 0
      · simp only [h, Nat.cast_zero]; exact (Real.exp_pos _).le
      · have h1 : 1 ≤ (Finset.univ.sup fun i => (b i).natAbs : ℕ) :=
          Nat.one_le_iff_ne_zero.mpr h
        have hpos : 0 < ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ) := by
          exact_mod_cast h1
        calc ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ)
            = Real.exp (Real.log ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ)) :=
              (Real.exp_log hpos).symm
          _ ≤ Real.exp (hL b (dK K)) := Real.exp_le_exp.mpr (le_max_left _ _)
    linarith
  have hrow' : ∀ i : Fin r,
      ∑ t : Fin n, |((L i t : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α t) ≤
        (2 : ℝ) ^ v * σ i := hrow
  -- §11 applied to the two distinct columns `ι m` and `k` of the row `i`
  have htwo : ∀ i : Fin r,
      |((L i (ι m) : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α (ι m))
        + |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α k) ≤ (2 : ℝ) ^ v * σ i := by
    intro i
    have hpair : |((L i (ι m) : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α (ι m))
        + |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α k)
        ≤ ∑ t : Fin n, |((L i t : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α t) := by
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg (s := ({ι m, k} : Finset (Fin n)))
        (f := fun t => |((L i t : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α t))
        (Finset.subset_univ _) (fun x _ _ => mul_nonneg (abs_nonneg _) (hmh_nonneg x))
      rwa [Finset.sum_insert (by simp [hιne m]), Finset.sum_singleton] at hsub
    exact le_trans hpair (hrow' i)
  -- `D ≥ 0`
  have hDnn : 0 ≤ pD r (dK K) σ := by
    simp only [pD]
    have hlog : 0 ≤ Real.log (2 * ↑r * ↑(dK K)) := by
      apply Real.log_nonneg
      have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      have h2 : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd1
      nlinarith
    have hp : 0 ≤ ∏ j : Fin r, σ j := Finset.prod_nonneg (fun j _ => (hσpos j).le)
    have h1 : (0 : ℝ) ≤ 2 * (r : ℝ) ^ r := by positivity
    have h2 : (0 : ℝ) ≤ (32 * (dK K : ℝ)) ^ (r + 1) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hlog) hp
  -- `λ_i ≤ D_i` summed with the weights `d σ_i` gives at most `D`
  have hsum : (dK K : ℝ) * ∑ i : Fin r, σ i * (lm i : ℝ) ≤ pD r (dK K) σ := by
    have hpoint : ∀ i : Fin r, (dK K : ℝ) * σ i * (lm i : ℝ) ≤ pD r (dK K) σ / r := by
      intro i
      have hσi : 0 < σ i := hσpos i
      have hdσ : 0 < (dK K : ℝ) * σ i := mul_pos hd hσi
      have hfloor : (pDj r (dK K) σ i : ℝ) ≤ pD r (dK K) σ / ((r : ℝ) * dK K * σ i) := by
        rw [pDj]
        exact Nat.floor_le (by positivity)
      have hlm' : (lm i : ℝ) ≤ (pDj r (dK K) σ i : ℝ) := by exact_mod_cast hlm i
      calc (dK K : ℝ) * σ i * (lm i : ℝ)
          ≤ (dK K : ℝ) * σ i * (pDj r (dK K) σ i : ℝ) :=
            mul_le_mul_of_nonneg_left hlm' (le_of_lt hdσ)
        _ ≤ (dK K : ℝ) * σ i * (pD r (dK K) σ / ((r : ℝ) * dK K * σ i)) :=
            mul_le_mul_of_nonneg_left hfloor (le_of_lt hdσ)
        _ = pD r (dK K) σ / r := by
            field_simp
    calc (dK K : ℝ) * ∑ i : Fin r, σ i * (lm i : ℝ)
        = ∑ i : Fin r, (dK K : ℝ) * σ i * (lm i : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ ∑ _i : Fin r, pD r (dK K) σ / r := Finset.sum_le_sum (fun i _ => hpoint i)
      _ = pD r (dK K) σ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  -- `e^{h'(L)} 2^v ≤ e^{h+1}`
  have hexp : Real.exp (hL b (dK K)) * (2 : ℝ) ^ v ≤ Real.exp ((acH K b v : ℝ) + 1) := by
    have h2 : (2 : ℝ) ^ v = Real.exp ((v : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [h2, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hx0 : 0 ≤ hL b (dK K) + (v : ℝ) * Real.log 2 := by
      have h1 : 0 < hL b (dK K) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
      have h2 : 0 ≤ (v : ℝ) * Real.log 2 := by positivity
      linarith
    have hfl := (Nat.floor_lt (a := hL b (dK K) + (v : ℝ) * Real.log 2) hx0
        (n := acH K b v + 1)).mp (Nat.lt_succ_self _)
    simp only [Nat.cast_add, Nat.cast_one] at hfl
    exact le_of_lt hfl
  -- per-summand bound
  have hterm : ∀ i : Fin r,
      |((derVec b k L (ι m) i : ℤ) : ℝ)| * (lm i : ℝ) * ‖X‖
        ≤ Real.exp (hL b (dK K)) * (dK K : ℝ) * (2 : ℝ) ^ v * σ i * (lm i : ℝ) := by
    intro i
    have hscale : (|((L i (ι m) : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|) * ‖X‖
        ≤ (dK K : ℝ) * ((2 : ℝ) ^ v * σ i) := by
      have hmhjk : BakerWustholz.modifiedHeight φ (α (ι m))
          ≤ BakerWustholz.modifiedHeight φ (α k) := hmhle (ι m)
      have step : (|((L i (ι m) : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|) * ‖X‖
          ≤ (|((L i (ι m) : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|)
              * ((dK K : ℝ) * BakerWustholz.modifiedHeight φ (α (ι m))) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      have step2 : (|((L i (ι m) : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|)
            * ((dK K : ℝ) * BakerWustholz.modifiedHeight φ (α (ι m)))
          ≤ (dK K : ℝ) * ((2 : ℝ) ^ v * σ i) := by
        have hk : |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α (ι m))
            ≤ |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α k) :=
          mul_le_mul_of_nonneg_left hmhjk (abs_nonneg _)
        calc (|((L i (ι m) : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|)
              * ((dK K : ℝ) * BakerWustholz.modifiedHeight φ (α (ι m)))
            = (dK K : ℝ) * (|((L i (ι m) : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α (ι m))
                + |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α (ι m))) := by ring
          _ ≤ (dK K : ℝ) * (|((L i (ι m) : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α (ι m))
                + |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α k)) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hd); linarith
          _ ≤ (dK K : ℝ) * ((2 : ℝ) ^ v * σ i) :=
              mul_le_mul_of_nonneg_left (htwo i) (le_of_lt hd)
      exact step.trans step2
    have h1 : |((derVec b k L (ι m) i : ℤ) : ℝ)|
        ≤ Real.exp (hL b (dK K)) * (|((L i (ι m) : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|) := by
      have hcast : ((derVec b k L (ι m) i : ℤ) : ℝ)
          = (b k : ℝ) * (L i (ι m) : ℝ) - (b (ι m) : ℝ) * (L i k : ℝ) := by
        simp only [derVec, Int.cast_sub, Int.cast_mul]
      rw [hcast]
      calc |(b k : ℝ) * (L i (ι m) : ℝ) - (b (ι m) : ℝ) * (L i k : ℝ)|
          ≤ |(b k : ℝ) * (L i (ι m) : ℝ)| + |(b (ι m) : ℝ) * (L i k : ℝ)| := abs_sub _ _
        _ = |(b k : ℝ)| * |(L i (ι m) : ℝ)| + |(b (ι m) : ℝ)| * |(L i k : ℝ)| := by
            rw [abs_mul, abs_mul]
        _ ≤ Real.exp (hL b (dK K)) * |(L i (ι m) : ℝ)|
              + Real.exp (hL b (dK K)) * |(L i k : ℝ)| := by
            gcongr
            · exact hb k
            · exact hb (ι m)
        _ = Real.exp (hL b (dK K)) * (|(L i (ι m) : ℝ)| + |(L i k : ℝ)|) := by ring
    calc |((derVec b k L (ι m) i : ℤ) : ℝ)| * (lm i : ℝ) * ‖X‖
        ≤ (Real.exp (hL b (dK K)) * (|((L i (ι m) : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|))
            * (lm i : ℝ) * ‖X‖ := by gcongr
      _ = Real.exp (hL b (dK K)) * (lm i : ℝ)
            * ((|((L i (ι m) : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|) * ‖X‖) := by ring
      _ ≤ Real.exp (hL b (dK K)) * (lm i : ℝ) * ((dK K : ℝ) * ((2 : ℝ) ^ v * σ i)) := by
          gcongr
      _ = Real.exp (hL b (dK K)) * (dK K : ℝ) * (2 : ℝ) ^ v * σ i * (lm i : ℝ) := by ring
  have hfinal : (∑ i : Fin r,
        Real.exp (hL b (dK K)) * (dK K : ℝ) * (2 : ℝ) ^ v * σ i * (lm i : ℝ))
      = Real.exp (hL b (dK K)) * (2 : ℝ) ^ v
          * ((dK K : ℝ) * ∑ i : Fin r, σ i * (lm i : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [norm_mul]
  have hgnorm : ‖gam b k L (ι m) lm‖
      ≤ ∑ i : Fin r, |((derVec b k L (ι m) i : ℤ) : ℝ)| * (lm i : ℝ) := by
    rw [gam]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_mul, Complex.norm_intCast, Complex.norm_natCast]
  calc ‖gam b k L (ι m) lm‖ * ‖X‖
      ≤ (∑ i : Fin r, |((derVec b k L (ι m) i : ℤ) : ℝ)| * (lm i : ℝ)) * ‖X‖ :=
        mul_le_mul_of_nonneg_right hgnorm (norm_nonneg _)
    _ = ∑ i : Fin r, |((derVec b k L (ι m) i : ℤ) : ℝ)| * (lm i : ℝ) * ‖X‖ := by
        rw [Finset.sum_mul]
    _ ≤ ∑ i : Fin r,
          Real.exp (hL b (dK K)) * (dK K : ℝ) * (2 : ℝ) ^ v * σ i * (lm i : ℝ) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = Real.exp (hL b (dK K)) * (2 : ℝ) ^ v
          * ((dK K : ℝ) * ∑ i : Fin r, σ i * (lm i : ℝ)) := hfinal
    _ ≤ Real.exp (hL b (dK K)) * (2 : ℝ) ^ v * pD r (dK K) σ :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ Real.exp ((acH K b v : ℝ) + 1) * pD r (dK K) σ :=
        mul_le_mul_of_nonneg_right hexp hDnn

/-- BW §13: `|γ_j| ≤ e^{h'(L)} 2^v Σ_i dσ_iλ_i ≤ e^{h+1}D` for `λ_i ≤ D_i`; also `|γ_j log α_j| ≤ e^{h+1}D` (§17, via `h'(α_j) ≤ h'(α_k)` from `Standing`). -/
theorem est_gamma {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (m : Fin (r - 1)) (lm : Fin r → ℕ)
    (hlm : ∀ j, lm j ≤ pDj r (dK K) σ j) :
    ‖gam b k L (ι m) lm‖ ≤ Real.exp ((acH K b v : ℝ) + 1) * acD K σ ∧
      ‖gam b k L (ι m) lm * Complex.log (φ (α (ι m)))‖ ≤ Real.exp ((acH K b v : ℝ) + 1) * acD K σ := by
  have hd : 0 < (dK K : ℝ) := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast this
  have hX1 : ‖(1 : ℂ)‖ ≤ (dK K : ℝ) * BakerWustholz.modifiedHeight φ (α (ι m)) := by
    rw [norm_one]
    have h := mul_le_mul_of_nonneg_left (modifiedHeight_ge_inv_dK φ (α (ι m))) (le_of_lt hd)
    rwa [mul_one_div, div_self (ne_of_gt hd)] at h
  refine ⟨?_, ?_⟩
  · simpa using est_gamma_aux H m lm hlm 1 hX1
  · exact est_gamma_aux H m lm hlm (Complex.log (φ (α (ι m))))
      (norm_log_le_dK_mul_modifiedHeight φ (α (ι m)))

end Work.BW
