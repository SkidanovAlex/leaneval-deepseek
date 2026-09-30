import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.residue_disc
import Submission.Work.BW.analyticAt_taylor_sub
import Submission.Work.BW.bfac_prod_algebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, requests/bw4). Your node is `cauchy_blaschke27`; its doc comment gives BW's reference, proof idea and size, and the design (table, order, H3 reuse notes) is below. Definitions: Submission.Work.BW.DefsAC (imports ACBase, which holds Qpoly and H3's proved helpers; lead-placed, do not edit). All 52 nodes are dispatched in parallel as Submission.Work.BW.<name>. IMPORT siblings; never reprove them or restate them under another name. BW's decimals are corrected where BW slipped (3.42, 2.04, 1.021, −0.12): use the constants in YOUR statement exactly. Numeric nodes: prove with norm_num / interval bounds, never heavy kernel decide or native_decide. If you believe your statement is false, give a concrete counterexample.

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
lemma bw27_norm_intCast_complex (l : ℤ) : ‖(l : ℂ)‖ = ((|l| : ℤ) : ℝ) := by
  rw [Complex.norm_intCast, ← Int.cast_abs]

/-- integer points are at distance at least one. -/
lemma bw27_one_le_norm_sub_intCast {a b : ℤ} (h : a ≠ b) : (1 : ℝ) ≤ ‖(a : ℂ) - (b : ℂ)‖ := by
  have h1 : ((|a - b| : ℤ) : ℝ) ≥ 1 := by
    have := Int.one_le_abs (z := a - b) (sub_ne_zero.mpr h)
    exact_mod_cast this
  rwa [← Int.cast_sub, bw27_norm_intCast_complex]

lemma bw27_differentiableAt_prod_finset {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {z : ℂ}
    (h : ∀ i ∈ s, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ s, f i w) z := by
  have h1 : (fun w : ℂ => ∏ i ∈ s, f i w) = (∏ i ∈ s, f i) := by
    funext w; rw [Finset.prod_apply]
  rw [h1]
  exact DifferentiableAt.finsetProd h

lemma bw27_circleIntegrable_sum_finset {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {c : ℂ} {R : ℝ}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    CircleIntegrable (fun z => ∑ i ∈ s, f i z) c R := by
  have h1 : (fun z : ℂ => ∑ i ∈ s, f i z) = (∑ i ∈ s, f i) := by
    funext w; rw [Finset.sum_apply]
  rw [h1]
  exact CircleIntegrable.sum s h


/-- BW (27): for entire `f`, `F(z) = ∏_{l∈Z} β(z;l)^{T'+1}`, `|s| < R`, `s` outside the discs `|z−l| ≤ η` (`η < ½`, all inside `|z| < R`): `𝒥 − ℐ = f(s)/F(s)` with `𝒥 = (2πi)^{-1}∮_{|z|=R} f/((z−s)F)` and `ℐ = Σ_l Σ_{m ≤ T'} f_m(l)(2πi)^{-1}∮_{C_l} (z−l)^m/((z−s)F)`. Residue formula plus Taylor expansion of `f` at `l` to order `T'`. Mathlib: `circleIntegral`, Cauchy integral formula. -/
theorem cauchy_blaschke27 (f : ℂ → ℂ) (hf : Differentiable ℂ f) (R η : ℝ) (hη : 0 < η)
    (hη' : η < 1 / 2) (Z : Finset ℤ) (hZ : ∀ l ∈ Z, ((|l| : ℤ) : ℝ) + η < R) (Tp : ℕ) (s : ℂ)
    (hsR : ‖s‖ < R) (hsZ : ∀ l ∈ Z, η < ‖s - l‖) :
    (2 * Real.pi * Complex.I)⁻¹ *
        (∮ z in C(0, R), f z / ((z - s) * ∏ l ∈ Z, bfac R l z ^ (Tp + 1))) -
      ∑ l ∈ Z, ∑ m ∈ Finset.range (Tp + 1), taylorC f m l *
        ((2 * Real.pi * Complex.I)⁻¹ *
          ∮ z in C((l : ℂ), η), (z - l) ^ m / ((z - s) * ∏ l' ∈ Z, bfac R l' z ^ (Tp + 1))) =
      f s / ∏ l ∈ Z, bfac R l s ^ (Tp + 1) := by
  classical
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg s) hsR
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hlt : ∀ l ∈ Z, ((|l| : ℤ) : ℝ) < R := fun l hl => by have := hZ l hl; linarith
  have hη2 : η < 1 := by linarith
  -- ### definitions
  set F : ℂ → ℂ := fun z => ∏ l ∈ Z, bfac R l z ^ (Tp + 1) with hFdef
  set Pz : ℂ → ℂ := fun z => ∏ l ∈ Z, (((R : ℂ) ^ 2 - (l : ℂ) * z) / (R : ℂ)) ^ (Tp + 1) with hPdef
  set Y : ℂ → ℂ := fun z => f z * Pz z with hYdef
  set W : ℂ → ℂ := fun z => f z / ((z - s) * F z) with hWdef
  -- ### geometry
  have hgeom : ∀ z : ℂ, ‖z‖ ≤ R → ∀ l ∈ Z, (R : ℂ) ^ 2 - (l : ℂ) * z ≠ 0 := by
    intro z hz l hl hzero
    have hl' := hlt l hl
    have h2 : (l : ℂ) * z = (R : ℂ) ^ 2 := (sub_eq_zero.mp hzero).symm
    have h1 : ‖(l : ℂ) * z‖ = R ^ 2 := by
      rw [h2, norm_pow, Complex.norm_of_nonneg hR.le]
    have h3 : ‖(l : ℂ) * z‖ < R ^ 2 := by
      rw [norm_mul, bw27_norm_intCast_complex]
      calc ((|l| : ℤ) : ℝ) * ‖z‖ ≤ ((|l| : ℤ) : ℝ) * R :=
            mul_le_mul_of_nonneg_left hz (by positivity)
        _ < R * R := by nlinarith
        _ = R ^ 2 := by ring
    linarith
  have hFne : ∀ z : ℂ, ‖z‖ ≤ R → (∀ l ∈ Z, z ≠ (l : ℂ)) → F z ≠ 0 := by
    intro z hz hzZ
    have h := (bfac_prod_algebra R η hR hη Z hZ Tp z hz hzZ).2.1
    simpa [hFdef] using h
  have halg : ∀ z : ℂ, ‖z‖ ≤ R → (∀ l ∈ Z, z ≠ (l : ℂ)) →
      (∏ l ∈ Z, (z - (l : ℂ)) ^ (Tp + 1)) = Pz z * F z := by
    intro z hz hzZ
    have h := (bfac_prod_algebra R η hR hη Z hZ Tp z hz hzZ).2.2
    simpa [hPdef, hFdef] using h
  -- ### differentiability
  have hProd_diff : ∀ z : ℂ, (∀ l ∈ Z, (R : ℂ) ^ 2 - (l : ℂ) * z ≠ 0) →
      DifferentiableAt ℂ (fun w : ℂ => ∏ l ∈ Z, bfac R l w ^ (Tp + 1)) z := by
    intro z hz
    refine bw27_differentiableAt_prod_finset Z (fun l hl => ?_)
    have hb : (fun w : ℂ => bfac R l w ^ (Tp + 1)) =
        fun w : ℂ => (((R : ℂ) * (w - (l : ℂ))) / ((R : ℂ) ^ 2 - (l : ℂ) * w)) ^ (Tp + 1) := by
      funext w; rw [bfac]
    rw [hb]
    exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (R : ℂ) * (w - (l : ℂ))) z).div
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (R : ℂ) ^ 2 - (l : ℂ) * w) z)
      (hz l hl)).pow _
  have hF_diff : ∀ z : ℂ, (∀ l ∈ Z, (R : ℂ) ^ 2 - (l : ℂ) * z ≠ 0) → DifferentiableAt ℂ F z := by
    intro z hz
    rw [hFdef]
    exact hProd_diff z hz
  have hPz_diff_expl : Differentiable ℂ (fun z : ℂ =>
      ∏ l ∈ Z, (((R : ℂ) ^ 2 - (l : ℂ) * z) / (R : ℂ)) ^ (Tp + 1)) := by
    intro z
    refine bw27_differentiableAt_prod_finset Z (fun l hl => ?_)
    refine DifferentiableAt.pow ?_ _
    refine DifferentiableAt.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · exact hRne
  have hP_diff : Differentiable ℂ Pz := by
    rw [hPdef]; exact hPz_diff_expl
  have hY_diff : Differentiable ℂ Y := by
    rw [hYdef]
    exact hf.mul hP_diff
  -- ### residue formula setup
  set Zc : Finset ℂ := Z.image (fun l : ℤ => (l : ℂ)) with hZcdef
  set S : Finset ℂ := insert s Zc with hSdef
  set nn : ℂ → ℕ := fun p => if p = s then 1 else Tp + 1 with hnndef
  set ρs : ℝ := min η ((R - ‖s‖) / 2) with hρsdef
  set ρ : ℂ → ℝ := fun p => if p = s then ρs else η with hρdef
  have hsZc : s ∉ Zc := by
    intro hs
    rw [hZcdef, Finset.mem_image] at hs
    obtain ⟨l, hl, hls⟩ := hs
    have hle := hsZ l hl
    rw [hls] at hle
    simp at hle
    linarith
  have hρs_pos : 0 < ρs := by
    rw [hρsdef]; exact lt_min hη (by linarith)
  have hρs_le_eta : ρs ≤ η := by rw [hρsdef]; exact min_le_left _ _
  have hρs_le_half : ρs ≤ (R - ‖s‖) / 2 := by rw [hρsdef]; exact min_le_right _ _
  have hρ_s : ρ s = ρs := by simp [hρdef]
  have hρ_of_ne : ∀ p : ℂ, p ≠ s → ρ p = η := fun p hp => by simp [hρdef, hp]
  have hnn_s : nn s = 1 := by simp [hnndef]
  have hnn_of_ne : ∀ p : ℂ, p ≠ s → nn p = Tp + 1 := fun p hp => by simp [hnndef, hp]
  have hmem_Zc : ∀ {p : ℂ}, p ∈ Zc ↔ ∃ l ∈ Z, (l : ℂ) = p := by
    intro p; rw [hZcdef, Finset.mem_image]
  have hS_ball : ∀ p ∈ S, p ∈ Metric.ball 0 R := by
    intro p hp
    rw [hSdef, Finset.mem_insert] at hp
    rcases hp with hps | hpZc
    · rw [hps, Metric.mem_ball, dist_zero_right]; exact hsR
    · obtain ⟨l, hl, rfl⟩ := (hmem_Zc.mp hpZc)
      rw [Metric.mem_ball, dist_zero_right, bw27_norm_intCast_complex]
      exact hlt l hl
  have hρ0 : ∀ p ∈ S, 0 < ρ p := by
    intro p hp
    rw [hSdef, Finset.mem_insert] at hp
    rcases hp with hps | hpZc
    · rw [hps, hρ_s]; exact hρs_pos
    · obtain ⟨l, hl, rfl⟩ := (hmem_Zc.mp hpZc)
      have hls : (l : ℂ) ≠ s := fun h => hsZc (by rw [← h]; exact hmem_Zc.mpr ⟨l, hl, rfl⟩)
      rw [hρ_of_ne _ hls]; exact hη
  have hρR : ∀ p ∈ S, Metric.closedBall p (ρ p) ⊆ Metric.ball 0 R := by
    intro p hp z hz
    rw [hSdef, Finset.mem_insert] at hp
    rcases hp with hps | hpZc
    · have hzs : ‖z - s‖ ≤ ρs := by
        rw [hps, hρ_s] at hz
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖z‖ = ‖(z - s) + s‖ := by ring_nf
        _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
        _ ≤ ρs + ‖s‖ := by linarith
        _ ≤ (R - ‖s‖) / 2 + ‖s‖ := by linarith
        _ < R := by linarith
    · obtain ⟨l, hl, rfl⟩ := (hmem_Zc.mp hpZc)
      have hls : (l : ℂ) ≠ s := fun h => hsZc (by rw [← h]; exact hmem_Zc.mpr ⟨l, hl, rfl⟩)
      have hz' : ‖z - (l : ℂ)‖ ≤ η := by
        have h1 : ρ (l : ℂ) = η := hρ_of_ne _ hls
        rw [h1] at hz
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖z‖ = ‖(z - (l : ℂ)) + (l : ℂ)‖ := by ring_nf
        _ ≤ ‖z - (l : ℂ)‖ + ‖(l : ℂ)‖ := norm_add_le _ _
        _ ≤ η + ((|l| : ℤ) : ℝ) := by rw [bw27_norm_intCast_complex]; linarith
        _ < R := by linarith [hZ l hl]
  have hsep : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → ρ p < ‖p - p'‖ := by
    intro p hp p' hp' hne
    rw [hSdef, Finset.mem_insert] at hp hp'
    rcases hp with hps | hpZc
    · rw [hps, hρ_s]
      rcases hp' with hp's | hp'Zc
      · exact absurd (hps.trans hp's.symm) hne
      · obtain ⟨l, hl, rfl⟩ := (hmem_Zc.mp hp'Zc)
        exact lt_of_le_of_lt hρs_le_eta (hsZ l hl)
    · obtain ⟨l, hl, rfl⟩ := (hmem_Zc.mp hpZc)
      have hls : (l : ℂ) ≠ s := fun h => hsZc (by rw [← h]; exact hmem_Zc.mpr ⟨l, hl, rfl⟩)
      rw [hρ_of_ne _ hls]
      rcases hp' with hp's | hp'Zc
      · rw [hp's, norm_sub_rev]
        exact hsZ l hl
      · obtain ⟨l', hl', rfl⟩ := (hmem_Zc.mp hp'Zc)
        have hll' : l ≠ l' := fun h => hne (by rw [h])
        exact lt_of_lt_of_le hη2 (bw27_one_le_norm_sub_intCast hll')
  have hprod : ∀ z : ℂ, z ≠ s → (∀ l ∈ Z, z ≠ (l : ℂ)) →
      (∏ p ∈ S, (z - p) ^ (nn p)) = (z - s) * (∏ l ∈ Z, (z - (l : ℂ)) ^ (Tp + 1)) := by
    intro z hzs hzZ
    rw [hSdef, Finset.prod_insert hsZc, hnn_s, pow_one]
    congr 1
    rw [hZcdef, Finset.prod_image Int.cast_injective.injOn]
    refine Finset.prod_congr rfl (fun l hl => ?_)
    rw [hnn_of_ne _ (fun h => hsZc (by rw [← h]; exact hmem_Zc.mpr ⟨l, hl, rfl⟩))]
  have hYeq : ∀ z ∈ Metric.closedBall 0 R, z ∉ (S : Set ℂ) →
      Y z = W z * (∏ p ∈ S, (z - p) ^ (nn p)) := by
    intro z hz hzS
    have hzs : z ≠ s := fun h => hzS (by rw [h]; exact Finset.mem_insert_self s Zc)
    have hzZc : z ∉ Zc := fun h => hzS (Finset.mem_insert_of_mem h)
    have hzZ : ∀ l ∈ Z, z ≠ (l : ℂ) := fun l hl h => hzZc (hmem_Zc.mpr ⟨l, hl, h.symm⟩)
    have hzR : ‖z‖ ≤ R := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      simpa using hz
    have hFz : F z ≠ 0 := hFne z hzR hzZ
    have halgz : (∏ l ∈ Z, (z - (l : ℂ)) ^ (Tp + 1)) = Pz z * F z := halg z hzR hzZ
    rw [hprod z hzs hzZ, hWdef, hYdef, halgz]
    have hden : (z - s) * F z ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hzs) hFz
    field_simp
  have hres : (∮ z in C(0, R), W z) = ∑ p ∈ S, ∮ z in C(p, ρ p), W z :=
    residue_disc W Y R S nn ρ hR hS_ball hρ0 hρR hsep hY_diff hYeq
  have hsum : ∑ p ∈ S, ∮ z in C(p, ρ p), W z
      = (∮ z in C(s, ρs), W z) + ∑ l ∈ Z, ∮ z in C((l : ℂ), η), W z := by
    rw [hSdef, Finset.sum_insert hsZc, hρ_s, hZcdef, Finset.sum_image Int.cast_injective.injOn]
    congr 1
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [hρ_of_ne _ (fun h => hsZc (by rw [← h]; exact hmem_Zc.mpr ⟨l, hl, rfl⟩))]
  -- ### the pole at `s`
  have hFne_ball_s : ∀ z : ℂ, ‖z - s‖ ≤ ρs → F z ≠ 0 := by
    intro z hz
    have hzR : ‖z‖ ≤ R := by
      have h : ‖z‖ < R := by
        calc ‖z‖ = ‖(z - s) + s‖ := by ring_nf
          _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
          _ ≤ ρs + ‖s‖ := by linarith
          _ ≤ (R - ‖s‖) / 2 + ‖s‖ := by linarith
          _ < R := by linarith
      exact h.le
    refine hFne z hzR (fun l hl hzl => ?_)
    have h2 : ‖s - (l : ℂ)‖ ≤ ρs := by rw [← hzl, norm_sub_rev]; exact hz
    linarith [hsZ l hl, hρs_le_eta]
  have hsint : (∮ z in C(s, ρs), W z) = 2 * Real.pi * Complex.I * (f s / F s) := by
    have hcongr : (∮ z in C(s, ρs), W z) = ∮ z in C(s, ρs), (f z / F z) / (z - s) := by
      refine circleIntegral.integral_congr hρs_pos.le (fun z hz => ?_)
      have h1 : ‖z - s‖ = ρs := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hFz : F z ≠ 0 := hFne_ball_s z (le_of_eq h1)
      have hzs : z ≠ s := by intro h; rw [h, sub_self, norm_zero] at h1; linarith [hρs_pos]
      rw [hWdef]
      field_simp
    rw [hcongr]
    have hFcont : ContinuousOn F (Metric.closedBall s ρs) := by
      intro z hz
      have h1 : ‖z - s‖ ≤ ρs := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hzR : ‖z‖ ≤ R := by
        have h : ‖z‖ < R := by
          calc ‖z‖ = ‖(z - s) + s‖ := by ring_nf
            _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
            _ ≤ ρs + ‖s‖ := by linarith
            _ ≤ (R - ‖s‖) / 2 + ‖s‖ := by linarith
            _ < R := by linarith
        exact h.le
      exact ((hF_diff z (fun l hl => hgeom z hzR l hl)).continuousAt).continuousWithinAt
    refine Complex.circleIntegral_div_sub_of_differentiable_on_off_countable
      Set.countable_empty ?_ ?_ ?_
    · simpa [Metric.mem_ball, dist_eq_norm] using hρs_pos
    · exact hf.continuous.continuousOn.div hFcont (fun z hz => hFne_ball_s z (by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz))
    · intro z hz
      have h1 : ‖z - s‖ < ρs := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hzR : ‖z‖ ≤ R := by
        have h : ‖z‖ < R := by
          calc ‖z‖ = ‖(z - s) + s‖ := by ring_nf
            _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
            _ ≤ ρs + ‖s‖ := by linarith
            _ ≤ (R - ‖s‖) / 2 + ‖s‖ := by linarith
            _ < R := by linarith
        exact h.le
      exact (hf z).div (hF_diff z (fun l hl => hgeom z hzR l hl)) (hFne_ball_s z h1.le)
  -- ### the poles at the integers: Taylor expansion of `f`
  have hperl : ∀ l ∈ Z, (∮ z in C((l : ℂ), η), W z)
      = ∑ m ∈ Finset.range (Tp + 1),
          taylorC f m l * ∮ z in C((l : ℂ), η), (z - (l : ℂ)) ^ m / ((z - s) * F z) := by
    intro l hl
    obtain ⟨Ft, hFt_an, hFt_eq⟩ := analyticAt_taylor_sub (hf.analyticAt (l : ℂ)) (Tp + 1)
    set Poly : ℂ → ℂ := fun z => ∑ i ∈ Finset.range (Tp + 1),
      (z - (l : ℂ)) ^ i / (i.factorial : ℂ) * iteratedDeriv i f (l : ℂ) with hPolydef
    set Wl : ℂ → ℂ := fun z => ∏ l' ∈ Z.erase l, (z - (l' : ℂ)) ^ (Tp + 1) with hWldef
    set ψ : ℂ → ℂ := fun z => Ft z * Pz z / ((z - s) * Wl z) with hψdef
    have sphere_norm : ∀ z : ℂ, ‖z - (l : ℂ)‖ = η → ‖z‖ < R := by
      intro z hz
      calc ‖z‖ = ‖(z - (l : ℂ)) + (l : ℂ)‖ := by ring_nf
        _ ≤ ‖z - (l : ℂ)‖ + ‖(l : ℂ)‖ := norm_add_le _ _
        _ = η + ((|l| : ℤ) : ℝ) := by rw [hz, bw27_norm_intCast_complex]
        _ < R := by linarith [hZ l hl]
    have sphere_ne_Z : ∀ z : ℂ, ‖z - (l : ℂ)‖ = η → ∀ l' ∈ Z, z ≠ (l' : ℂ) := by
      intro z hz l' hl' hzl'
      have h3 : ‖(l : ℂ) - (l' : ℂ)‖ = η := by rw [← hzl', norm_sub_rev]; exact hz
      rcases eq_or_ne l' l with rfl | hne
      · rw [sub_self, norm_zero] at h3; linarith [hη]
      · have h2 : (1 : ℝ) ≤ ‖(l : ℂ) - (l' : ℂ)‖ := bw27_one_le_norm_sub_intCast (Ne.symm hne)
        linarith [hη2]
    have sphere_ne_s : ∀ z : ℂ, ‖z - (l : ℂ)‖ = η → z ≠ s := by
      intro z hz hzs
      have h2 := hsZ l hl
      have h3 : ‖s - (l : ℂ)‖ = η := by rw [← hzs]; exact hz
      linarith
    have sphere_F_ne : ∀ z : ℂ, ‖z - (l : ℂ)‖ = η → F z ≠ 0 := fun z hz =>
      hFne z (le_of_lt (sphere_norm z hz)) (sphere_ne_Z z hz)
    have sphere_Wl_ne : ∀ z : ℂ, ‖z - (l : ℂ)‖ = η → Wl z ≠ 0 := by
      intro z hz
      rw [hWldef]
      refine Finset.prod_ne_zero_iff.mpr (fun l' hl' => pow_ne_zero _ (sub_ne_zero.mpr ?_))
      exact sphere_ne_Z z hz l' (Finset.mem_of_mem_erase hl')
    have hFt_eq' : ∀ w : ℂ, w ≠ (l : ℂ) →
        Ft w = (f w - Poly w) / (w - (l : ℂ)) ^ (Tp + 1) := by
      intro w hw
      have h3 : f w = Poly w + (w - (l : ℂ)) ^ (Tp + 1) * Ft w := by
        rw [hPolydef]; exact hFt_eq w
      have h4 : (w - (l : ℂ)) ^ (Tp + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw)
      rw [h3, add_sub_cancel_left, mul_comm ((w - (l : ℂ)) ^ (Tp + 1)) (Ft w)]
      exact (mul_div_cancel_right₀ (Ft w) h4).symm
    have hFt_diff : ∀ z : ℂ, DifferentiableAt ℂ Ft z := by
      intro z
      by_cases hz : z = (l : ℂ)
      · rw [hz]; exact hFt_an.differentiableAt
      · have hGt : DifferentiableAt ℂ
            (fun w : ℂ => (f w - Poly w) / (w - (l : ℂ)) ^ (Tp + 1)) z := by
          refine DifferentiableAt.div ?_ ?_ (pow_ne_zero _ (sub_ne_zero.mpr hz))
          · refine (hf z).sub ?_
            rw [hPolydef]; fun_prop
          · fun_prop
        refine hGt.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds
          (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hz)] with w hw
        exact hFt_eq' w (by simpa using hw)
    have hψ_diff : ∀ z : ℂ, z ≠ s → (∀ l' ∈ Z.erase l, z ≠ (l' : ℂ)) →
        DifferentiableAt ℂ ψ z := by
      intro z hzs hzl'
      rw [hψdef]
      refine DifferentiableAt.div ?_ ?_ ?_
      · exact (hFt_diff z).mul (hP_diff z)
      · refine DifferentiableAt.mul (differentiableAt_id.sub_const s) ?_
        rw [hWldef]
        exact bw27_differentiableAt_prod_finset (Z.erase l)
          (fun l' hl' => (differentiableAt_id.sub_const _).pow _)
      · refine mul_ne_zero (sub_ne_zero.mpr hzs) ?_
        rw [hWldef]
        exact Finset.prod_ne_zero_iff.mpr (fun l' hl' =>
          pow_ne_zero _ (sub_ne_zero.mpr (hzl' l' hl')))
    have key : ∀ z : ℂ, ‖z - (l : ℂ)‖ = η → W z =
        (∑ m ∈ Finset.range (Tp + 1),
          taylorC f m l * ((z - (l : ℂ)) ^ m / ((z - s) * F z))) + ψ z := by
      intro z hz
      have hzR := sphere_norm z hz
      have hzZ := sphere_ne_Z z hz
      have hzs := sphere_ne_s z hz
      have hFz := sphere_F_ne z hz
      have hPz_ne : Pz z ≠ 0 := by
        rw [hPdef]
        refine Finset.prod_ne_zero_iff.mpr (fun l' hl' => pow_ne_zero _ ?_)
        exact div_ne_zero (hgeom z hzR.le l' hl') hRne
      have hWl_ne := sphere_Wl_ne z hz
      have hV : (∏ l' ∈ Z, (z - (l' : ℂ)) ^ (Tp + 1)) = (z - (l : ℂ)) ^ (Tp + 1) * Wl z := by
        rw [hWldef]
        exact (Finset.mul_prod_erase Z (fun l' => (z - (l' : ℂ)) ^ (Tp + 1)) hl).symm
      have halgz := halg z hzR.le hzZ
      have hFs : F z = (z - (l : ℂ)) ^ (Tp + 1) * Wl z / Pz z := by
        have h4 : Pz z * F z = (z - (l : ℂ)) ^ (Tp + 1) * Wl z := by rw [← halgz, hV]
        have h5 : F z * Pz z = (z - (l : ℂ)) ^ (Tp + 1) * Wl z := by rw [mul_comm]; exact h4
        rw [← h5]
        exact (mul_div_cancel_right₀ (F z) hPz_ne).symm
      have h1 : f z = Poly z + (z - (l : ℂ)) ^ (Tp + 1) * Ft z := by
        rw [hPolydef]; exact hFt_eq z
      have h2 : Poly z = ∑ i ∈ Finset.range (Tp + 1), taylorC f i l * (z - (l : ℂ)) ^ i := by
        rw [hPolydef]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        simp only [taylorC]
        ring
      have hzl : z ≠ (l : ℂ) := by intro h; rw [h, sub_self, norm_zero] at hz; linarith [hη]
      have h3 : (z - (l : ℂ)) ^ (Tp + 1) * Ft z / ((z - s) * F z) = ψ z := by
        rw [hψdef, hFs]
        have h1' : (z - (l : ℂ)) ^ (Tp + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzl)
        have h2' : (z - s) ≠ 0 := sub_ne_zero.mpr hzs
        field_simp
      calc W z = f z / ((z - s) * F z) := rfl
        _ = (Poly z + (z - (l : ℂ)) ^ (Tp + 1) * Ft z) / ((z - s) * F z) := by rw [h1]
        _ = Poly z / ((z - s) * F z) + (z - (l : ℂ)) ^ (Tp + 1) * Ft z / ((z - s) * F z) := by
              rw [add_div]
        _ = (∑ i ∈ Finset.range (Tp + 1), taylorC f i l * (z - (l : ℂ)) ^ i) /
              ((z - s) * F z) + ψ z := by rw [h2, h3]
        _ = (∑ i ∈ Finset.range (Tp + 1),
              taylorC f i l * ((z - (l : ℂ)) ^ i / ((z - s) * F z))) + ψ z := by
              congr 1
              rw [Finset.sum_div]
              exact Finset.sum_congr rfl (fun i hi => by rw [mul_div_assoc])
    have ball_ne_s : ∀ z : ℂ, ‖z - (l : ℂ)‖ ≤ η → z ≠ s := by
      intro z hz hzs
      have h2 := hsZ l hl
      have h3 : ‖s - (l : ℂ)‖ ≤ η := by rw [← hzs]; exact hz
      linarith
    have ball_ne_Z : ∀ z : ℂ, ‖z - (l : ℂ)‖ ≤ η → ∀ l' ∈ Z.erase l, z ≠ (l' : ℂ) := by
      intro z hz l' hl' hzl'
      have hne : l ≠ l' := (Finset.ne_of_mem_erase hl').symm
      have h2 : (1 : ℝ) ≤ ‖(l : ℂ) - (l' : ℂ)‖ := bw27_one_le_norm_sub_intCast hne
      have h3 : ‖(l : ℂ) - (l' : ℂ)‖ ≤ η := by rw [← hzl', norm_sub_rev]; exact hz
      linarith [hη2]
    have hψ_zero : (∮ z in C((l : ℂ), η), ψ z) = 0 := by
      refine circleIntegral_eq_zero_of_differentiable_on_off_countable hη.le Set.countable_empty
        ?_ ?_
      · intro z hz
        have h1 : ‖z - (l : ℂ)‖ ≤ η := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
        exact ((hψ_diff z (ball_ne_s z h1) (ball_ne_Z z h1)).continuousAt).continuousWithinAt
      · intro z hz
        have h1 : ‖z - (l : ℂ)‖ ≤ η := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using Metric.ball_subset_closedBall hz.1
        exact hψ_diff z (ball_ne_s z h1) (ball_ne_Z z h1)
    have hcont_term : ∀ m : ℕ, CircleIntegrable
        (fun z => taylorC f m l * ((z - (l : ℂ)) ^ m / ((z - s) * F z))) ((l : ℂ)) η := by
      intro m
      refine ContinuousOn.circleIntegrable hη.le (ContinuousOn.mul continuousOn_const ?_)
      refine ContinuousOn.div (by fun_prop) ?_ ?_
      · refine ContinuousOn.mul (by fun_prop) (fun z hz => ?_)
        have h1 : ‖z - (l : ℂ)‖ = η := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
        exact ((hF_diff z (fun l' hl' => hgeom z (sphere_norm z h1).le l' hl')).continuousAt
          ).continuousWithinAt
      · intro z hz
        have h1 : ‖z - (l : ℂ)‖ = η := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
        exact mul_ne_zero (sub_ne_zero.mpr (sphere_ne_s z h1)) (sphere_F_ne z h1)
    have hsum_int : (∮ z in C((l : ℂ), η),
          (∑ m ∈ Finset.range (Tp + 1), taylorC f m l * ((z - (l : ℂ)) ^ m / ((z - s) * F z))))
        = ∑ m ∈ Finset.range (Tp + 1),
            taylorC f m l * ∮ z in C((l : ℂ), η), (z - (l : ℂ)) ^ m / ((z - s) * F z) := by
      rw [circleIntegral.integral_fun_sum (fun m _ => hcont_term m)]
      exact Finset.sum_congr rfl (fun m _ => circleIntegral.integral_const_mul _ _ _ _)
    have hψ_int : CircleIntegrable ψ ((l : ℂ)) η := by
      refine ContinuousOn.circleIntegrable hη.le (fun z hz => ?_)
      have h1 : ‖z - (l : ℂ)‖ = η := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      exact ((hψ_diff z (sphere_ne_s z h1)
        (fun l' hl' => sphere_ne_Z z h1 l' (Finset.mem_of_mem_erase hl'))).continuousAt
        ).continuousWithinAt
    calc (∮ z in C((l : ℂ), η), W z)
        = ∮ z in C((l : ℂ), η), ((∑ m ∈ Finset.range (Tp + 1),
              taylorC f m l * ((z - (l : ℂ)) ^ m / ((z - s) * F z))) + ψ z) := by
            refine circleIntegral.integral_congr hη.le (fun z hz => ?_)
            have h1 : ‖z - (l : ℂ)‖ = η := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
            exact key z h1
      _ = (∮ z in C((l : ℂ), η), (∑ m ∈ Finset.range (Tp + 1),
              taylorC f m l * ((z - (l : ℂ)) ^ m / ((z - s) * F z)))) +
            (∮ z in C((l : ℂ), η), ψ z) :=
            circleIntegral.integral_add
              (bw27_circleIntegrable_sum_finset _ (fun m _ => hcont_term m)) hψ_int
      _ = (∑ m ∈ Finset.range (Tp + 1),
            taylorC f m l * ∮ z in C((l : ℂ), η), (z - (l : ℂ)) ^ m / ((z - s) * F z)) + 0 := by
            rw [hsum_int, hψ_zero]
      _ = ∑ m ∈ Finset.range (Tp + 1),
            taylorC f m l * ∮ z in C((l : ℂ), η), (z - (l : ℂ)) ^ m / ((z - s) * F z) := by
            rw [add_zero]
  -- ### assembly
  have hA : (∮ z in C(0, R), W z) =
      (2 * Real.pi * Complex.I) * (f s / F s) +
        (∑ l ∈ Z, ∑ m ∈ Finset.range (Tp + 1), taylorC f m l *
          ∮ z in C((l : ℂ), η), (z - (l : ℂ)) ^ m / ((z - s) * F z)) := by
    rw [hres, hsum, hsint]
    congr 1
    exact Finset.sum_congr rfl (fun l hl => hperl l hl)
  have h2πi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hfin : (2 * Real.pi * Complex.I)⁻¹ * (∮ z in C(0, R), W z) -
      ∑ l ∈ Z, ∑ m ∈ Finset.range (Tp + 1), taylorC f m l *
        ((2 * Real.pi * Complex.I)⁻¹ * ∮ z in C((l : ℂ), η),
          (z - (l : ℂ)) ^ m / ((z - s) * F z))
      = f s / F s := by
    rw [hA]
    have hfac : (∑ l ∈ Z, ∑ m ∈ Finset.range (Tp + 1), taylorC f m l *
        ((2 * Real.pi * Complex.I)⁻¹ * ∮ z in C((l : ℂ), η),
          (z - (l : ℂ)) ^ m / ((z - s) * F z)))
        = (2 * Real.pi * Complex.I)⁻¹ *
          (∑ l ∈ Z, ∑ m ∈ Finset.range (Tp + 1), taylorC f m l *
            ∮ z in C((l : ℂ), η), (z - (l : ℂ)) ^ m / ((z - s) * F z)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m hm => by ring)
    rw [hfac, mul_add, ← mul_assoc, inv_mul_cancel₀ h2πi, one_mul]
    ring
  rw [hWdef, hFdef] at hfin
  exact hfin

end Work.BW
