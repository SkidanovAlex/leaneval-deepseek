import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.multiplicity_prop
import Submission.Work.BW.rank_drop_numerics
import Submission.Work.BW.split_conditions
import Submission.Work.BW.KummerCond_comp
import Submission.Work.BW.exists_denom_multiple
import Submission.Work.BW.Xbw_ge_one
import Submission.Work.BW.h10_log_bound
import Submission.Work.BW.hmod_prod_zpow_le
import Submission.Work.BW.exp_lamP_prod
import Submission.Work.BW.lamP_linearIndependent
import Submission.Work.BW.kappa_rank_drop
import Submission.Work.BW.norm_mul_lt_of_log

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive, multiplicity block). Your node is `group_reduction`. The design is below: find your node in the §2.3 or §3 tables for its content, its dependencies and its size.
Definitions: Submission.Work.BW.Defs and Submission.Work.BW.DefsMult (namespace Work.BW).
All 19 nodes of this block are dispatched in parallel, each as module Submission.Work.BW.<name> with its statement in place. The earlier-dispatched nodes (minkowski_basis, etc.) are also live.
If your proof needs a sibling's result, IMPORT its module and use its statement. Do NOT reprove it, and do not restate it under another name.
Mathlib (pinned) HAS: Lasker (RingTheory/Lasker.lean), associated primes, Krull height, regular sequences (RingTheory/Regular/RegularSequence.lean), the Rees depth theorem (RingTheory/Regular/Depth.lean), graded homogeneous ideals, MvPolynomial weighted homogeneity, and Polynomial.hilbertPoly. It does NOT have Cohen–Macaulay theory, Hilbert–Serre, or multigraded Hilbert polynomials.
Do not weaken numeric constants. If you believe the statement is false, give a concrete counterexample.

===== DESIGN_MULT.md =====
# BW multiplicity block: design (phase 2, 2026-09-27)

This replaces `multiplicity_prop` (BW §10) and `group_reduction` (BW §21) of `bw/DESIGN.md` with a
route through Philippon's zero estimate. The route is P86*, a stepwise form, verified in §1 below.
No other team's Lean was read.

**Sources.**
* Philippon, *Lemmes de zéros dans les groupes algébriques commutatifs*, Bull. SMF 114 (1986)
  355–383. Read in full from the Numdam text (§2–§5).
* BW §10 and §20–21, from the GDZ scan.

**Files in this directory.**
* `DefsMult.lean`: definitions, no `sorry`. Install it as `Submission/Work/BW/DefsMult.lean`,
  importing `Submission.Work.BW.Defs`, in `namespace Work.BW`.
* 19 node statement files. Each ends in `:= by sorry` and has no import or namespace lines.

**Elaboration check.** On 3.144 I built one scratch file: `import Mathlib`,
`import Submission.Work.BW.Defs`, `namespace Work.BW`, then `DefsMult` and all 19 statements. I ran
`systemd-run --user --scope -q -p MemoryMax=12G ~/.elan/bin/lake env lean /tmp/bwmult/Test.lean` in
the workspace. Result: **19 `sorry` warnings, no errors** (Mathlib 5ed2965256). The workspace was
not touched.

---

## 1. P86*: verified

### 1.1 The statement

Take `G = G_a × G_m^N ⊂ (P¹)^{N+1}` and `n = N+1`. Let `A` be the analytic subgroup with Lie
algebra `W`, and let `Σ_1, …, Σ_n` be finite sets, each containing `0`.

**Hypothesis.** `P ≠ 0` has multidegree `D`, and `ord_A P ≥ T_1+⋯+T_n+1` at every point of
`Σ_1+⋯+Σ_n`.

**Conclusion.** There are a connected algebraic subgroup `G' ≠ G` and an index `j ≤ codim G'` with

    C(T_j + ℓ, ℓ) · #((Σ_j + G')/G') · H(G'; D) ≤ H(G; D),     ℓ = dim W − dim(W ∩ Lie G').

This is node `zero_estimate_stepwise`. There it is combined with `subgroup_rayDeg`, which gives
`G' = G_a^ε × ker 𝒵` and bounds `H(G'; D)` below by minors.

### 1.2 Philippon's proof (§5), with the stepwise data marked

The embedding constants are `c_i = 1` here. Def. 4.1 needs formulas of degree `c_i` for
`(h, z) ↦ h + g + Φ(z)`. On each `P¹` factor these are linear:
* `G_a`: `(x₀:x₁) ↦ (x₀ : x₁ + (g+z)x₀)`;
* `G_m`: `(x₀:x₁) ↦ (x₀ : e^{g+z}x₁)`.

A single chart covers `G`. So every `δ^x_{g}P` again has multidegree exactly `D`, and translations
are graded automorphisms of `R`.

**(a) The chain of ideals.** Philippon sets `I_1 = (𝔊, P)` and
`I_r = (𝔊, δ^x_{g}P : |x| ≤ (r−1)T, g ∈ Σ(r−1))`. Stepwise, I set

    I_{r} = (δ^x_{g}P : |x| ≤ T_1+⋯+T_{r−1},  g ∈ Σ_1+⋯+Σ_{r−1}).

Here `𝔊 = 0`, because `G` is dense in `(P¹)^{N+1}`.

Prop 4.3 says `δ^k_g δ^{k'}_{g'} I` and `δ^{k+k'}_{g+g'} I` have the same components meeting `G`.
A multi-index of order `≤ T_1+⋯+T_r` splits into one of order `≤ T_r` and one of order
`≤ T_1+⋯+T_{r−1}`. So, up to components not meeting `G`,

    I_{r+1} = (δ^{T_r}_g I_r : g ∈ Σ_r).                                        (*)

The step-`r` data `(Σ_r, T_r)` enter **only** through (*).

**(b) The chain stops, with a bounded index.** Put `Z_r = G ∩ Z(I_r)` and `d_r = dim Z_r`.
* By the hypothesis, every generator of `I_{n+1}` vanishes at `0 ∈ Σ_1+⋯+Σ_n`. So `Z_{n+1} ∋ 0`
  and `d_{n+1} ≥ 0`.
* `d_0 = n` and `d_1 = n − 1`, since `P ≠ 0` on the irreducible `G`.
* So `n−1 = d_1 ≥ d_2 ≥ ⋯ ≥ d_{n+1} ≥ 0`. There are `n+1` values in `[0, n−1]`, so a first `r ≥ 1`
  with `d_r = d_{r+1}` exists.
* Before `r` the values drop strictly, so **`d_r ≤ n − r`**.

**(c) Philippon's Lemma 5.1 at step r.**
* Some irreducible `V` of dimension `d_r` is a component of both `Z_r` and `Z_{r+1}`. (A component
  of `Z_{r+1}` of dimension `d_r` lies in a component of `Z_r` of dimension `≤ d_r`.)
* By (*) and Prop 4.4, `g + V ⊂ Z(δ^{T_r} I_r)` for every `g ∈ Σ_r`, so `Σ_r ⊂ H_V(T_r)`. This is
  where `Σ_r` and `T_r` enter.
* `H_V(0)` is a finite union of cosets of the stabiliser `G_V`, and `0 ∈ Σ_r` gives
  `G_V ⊂ H_V(T_r)`.
* Take `J' = (δ^x_{g+v}P : |x| ≤ T_1+⋯+T_{r−1}, g ∈ Σ_1+⋯+Σ_{r−1}, v ∈ V)`. Its generators have
  multidegree `D`, whatever the step sizes. Its `G`-part is `H_V(0)`.
* Prop 4.7 (Wüstholz), applied with `T = T_r`, shows that `J'` defines each `σ + G_V^0`,
  `σ ∈ S + S_0`, with length `≥ C(T_r+s, s)`, where `s = codim_A(A ∩ G_V^0)`.
* Prop 3.3 (refined Bezout, with `I₀ = 0` perfect at the points of `G`), Lemma 4.5
  (translation) and `#S ≥ #((Σ_r+G_V)/G_V)` then give the displayed inequality with
  `(Σ_r, T_r)` and `G' = G_V^0`.

**(d) The index is at most the codimension.** `G_V + v ⊂ V` for `v ∈ V`, so
`dim G' ≤ dim V = d_r ≤ n − r`. Hence **`j := r ≤ codim G'`** and `G' ≠ G`.

**(e) Monotone sequences.** With nonincreasing `(Sq m, Tq m)` (step `j` = index `m = j−1`), the
inequality at `j ≤ k` implies it at `m = k−1`. This is exactly Wüstholz's indexing in LNM 1290
Thm 1.1 (codimension `m+1` goes with `(𝒮_m, 𝒯_m)`).

**Verdict.** Every use of `(Σ, T)` in §5 is local to the step at which the chain stabilises, and the
rest of the argument is untouched. **P86* is verified**, conditional only on Philippon's §3–4 (a
published paper, widely used). One caveat: I worked from Numdam's text extraction, with some OCR
noise in the formulas.

The safest fallback is Philippon 2.1 exactly as stated (Σ(n), order nT). That version is **not**
enough for BW; see §4.

---

## 2. Block A: multigraded Hilbert functions and Bezout, without Cohen–Macaulay theory

### 2.1 Pinned Mathlib inventory (5ed2965256, grep scoped to `…/Mathlib`)

| need | status |
|---|---|
| Lasker–Noether | ✓ `RingTheory/Lasker.lean`: `IsLasker`, `IsMinimalPrimaryDecomposition`, `isLasker` |
| associated primes | ✓ `Ideal/AssociatedPrime/*`: `associatedPrimes.finite`, prime filtrations `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime` |
| minimal primes finite | ✓ `Ideal.finite_minimalPrimes_of_isNoetherianRing` |
| gradings | ✓ `MvPolynomial.weightedHomogeneousSubmodule` / `weightedHomogeneousComponent` with any `AddCommMonoid` weights; ✓ `GradedAlgebra/Homogeneous/Ideal` (prime criteria need a linearly ordered index; use `Lex (Fin (N+1) →₀ ℕ)`) |
| Hilbert polynomial | ◐ `RingTheory/Polynomial/HilbertPoly.lean` has only the power-series side (`hilbertPoly p d`); **no Hilbert–Serre**, no graded modules |
| Krull dimension | ✓ `ringKrullDim`, `Ideal.height`, `KrullsHeightTheorem.lean` (`height_le_spanRank_toENat`) |
| regular sequences | ✓ `Regular/RegularSequence.lean` (`RingTheory.Sequence.IsRegular`, permutation lemmas) |
| depth | ◐ only `Depth/Rees.lean`: `ModuleCat.exists_isRegular_tfae` (Ext characterisation) |
| regular local rings | ◐ `RegularLocalRing/Defs.lean`, `Polynomial.lean` (definitions only) |
| Cohen–Macaulay | ✗ (no `CohenMacaulay` anywhere) |
| multigraded Hilbert polynomial, multiprojective Bezout | ✗ |
| Nullstellensatz, `Module.length`, `NoetherNormalization` | ✓ |

### 2.2 Two design decisions

**(i) Single-graded via the ray `tD`.** Philippon only ever evaluates `H(·; d)` at `d = D`, and all
polynomials have multidegree exactly `D`. So define
`H(I; D) := (dim)! · lc(t ↦ dim(R/I)_{tD})` (`rayDeg`), the Hilbert polynomial of the
Segre–Veronese section `⊕_t R_{tD}`. That ring is standard graded and generated by `R_D`. Hence:
* only the **single-graded** Hilbert–Serre theorem is needed (A2);
* Philippon 3.1 becomes the exact sequence `0 → (R/I)_{(t−1)D} →·P (R/I)_{tD} → (R/(I,P))_{tD} → 0`
  (A3a);
* `H(G; D) = (N+1)!∏D_i` is `∏(tD_i+1)` (A3c);
* translation invariance (4.5) is trivial, since translations are graded automorphisms;
* subgroup degrees (B4) come from an explicit character count, with no intersection theory.

**(ii) Cohen–Macaulay is replaced by one local fact.**
* **Where CM is used.** CM enters Philippon only in Prop 3.3's second inequality, via Fact E: `J_b`
  has no embedded component through a point of `G`.
* **It is genuinely needed.** Philippon's Remark after 3.3 gives a counterexample without it.
  Also, embedded primes of dimension `δ` in the last complete intersection sit inside `Z(J')` and
  cannot be avoided by a generic combination: I checked this against the
  `(K:Q)/K` term of the exact sequence.
* **Only one fact is needed.** Here `I₀ = 0`, and by construction `J_b` is, locally at each
  `𝔪 ∈ 𝒰_b`, generated by a regular sequence. So it suffices to know:

  > Macaulay unmixedness in `ℂ[σ]_𝔪`: associated primes of `A/(f)`, for `f` regular, are minimal
  > over `(f)`.

  That follows from:
  * A5a: Matsumura 17.2 in "regular sequence" form, fully elementary (Nakayama plus one
    associated-prime step; no depth invariance);
  * A5b: depth drops by one modulo a regular element, from Mathlib's Rees theorem plus the
    `Ext` long exact sequence;
  * A5c: `ℂ[σ]_𝔪` has a regular sequence of length `|σ|` and dimension `≤ |σ|`, by Krull.

  **No general CM theory, no "regular ⇒ CM", no dimension formula.**
* **Alternatives I rejected.**
  * Chardin- or Nesterenko-style Bezout bounds need Koszul, linkage or Chow-form machinery. They are
    heavier, not lighter.
  * A "top-dimensional part via Lasker" shortcut fails at exactly the last step. The `(K:Q)/K`
    term has dimension `δ` and enters with the wrong sign.
  * Quotienting by `G'` before Bezout turns the problem into BKK mixed volumes, which is worse.

### 2.3 Block A nodes (statements in the `.lean` files)

| node | content | k lines |
|---|---|---|
| `multiHom_assPrime` (A1) | associated primes of `R/I` multihomogeneous | 1.5–3 |
| `rayHilb_poly` (A2) | eventual polynomiality of `t ↦ dim(R/I)_{tD}`, degree `≤ N+1` (Segre–Veronese reduction plus single-graded Hilbert–Serre for f.g. graded modules over `ℂ[z]`) | 4–7 |
| `rayDeg_hyperplane` (A3a) | cut by a non-zerodivisor `P ∈ R_D`: dim −1, `H` unchanged | 1–2 |
| `rayDeg_additive` (A3b) | `H(I) = ∑_{top minimal p} length((R/I)_p)·H(p)` (graded prime filtration) | 3–5 |
| `rayDeg_bot` (A3c) | `H(G;D) = (N+1)!∏D` | 0.5–1 |
| `rayDeg_mono` (A3d) | `I ≤ J`, same dim ⇒ `H(J) ≤ H(I)` | 0.3–0.6 |
| `rayDim_lt_of_lt` (A3e) | strict dimension drop along relevant primes | 1–2 |
| `refined_bezout` (A4) | Philippon 3.3 (second inequality), `I₀ = 0`, `𝒰` = cone points over `G` | 6–10 |
| `regSeq_le_dim_of_ass` (A5a) | regular-sequence length `≤ dim A/p` for `p ∈ Ass` | 1.5–2.5 |
| `regSeq_quotient` (A5b) | `A/(f)` keeps a regular sequence of length `n − \|f\|` | 1.5–3 |
| `mvpoly_local_regSeq` (A5c) | full-length regular sequence in `ℂ[σ]_𝔪`, `dim ≤ \|σ\|` | 1–2 |
| `unmixed_regSeq` (A5d) | Macaulay unmixedness in `ℂ[σ]_𝔪` | 1–2 |
| **block A total** | | **22–40k** |

**Order.**
1. **Wave 1, parallel:** A1, A2, A5a, A5b, A5c.
2. **Then:** A3a–e, which need A2, and A5d, which needs A5a–c.
3. **Then:** A4, which needs A1, A3a/b/e, A5d and Lasker.

The critical path is A2 → A3 → A4, about 12–20k.

---

## 3. Blocks B and C, and the restated nodes

| node | content | k lines | deps |
|---|---|---|---|
| `subgroup_rayDeg` (B4) | closure of `G_a^ε × ker 𝒵`: `dim = N+1−k`; `H ≥ (N+1−k)!·\|Δ_J\|·D₀^ε·∏_{i∉J}D_{i+1}` (count box classes in `ℤ^N/𝒵`; characters independent) | 2–4 | A2 |
| `zero_estimate_stepwise` (B5 = P86*) | §1.1 with explicit subgroup and degree; internally: B1 operators `δ^x_g` (Philippon 4.1–4.4), B2 connected subgroups are `G_a^ε × ker𝒵`, 𝒵 saturated (binomial ideals via character independence), B3 Wüstholz's length bound (4.6–4.7), Lemma 5.1 assembly | 9–16 | A1–A4, B4 |
| `prim_basis_from_minors` (C1) | for the `J` maximising `\|Δ_J\|∏_J a`, a basis with `∏ℛ ≤ 2^{1−ρ}(ρ!)²r^ρ\|Δ_J\|∏_J a` (Cramer gives `∑a\|x\| ≤ r∑_J a\|x\|`; then `minkowski_basis` on the `J`-projection) | 1–2 | `minkowski_basis` (dispatched) |
| `split_conditions` | the half split fits the budgets and satisfies (E0)–(E3) | 2–4 | — |
| `rank_drop_numerics` | (30) for both cases | 1.5–3 | — |
| `multiplicity_prop` (restated) | assembly, below | 3–6 | B5, C1 |
| `group_reduction` (same signature) | BW §21 with the half split | 2–4 | `multiplicity_prop`, numerics |

**Totals.**
* Blocks B and C, including `group_reduction`: **20.5–39k**.
* **The whole replacement of `multiplicity_prop` and `group_reduction`: ≈43–79k, central ≈58k.** This
  is higher than the scoping estimate of 35–65k, because the numerics and assembly are now counted
  as separate nodes.

**`multiplicity_prop` (restated).** The file carries the exact statement.
* **Hypotheses:**
  * the budgets are sums: `∑_{m≤r} Sq m ≤ 𝒮` and `∑ Tq m ≤ 𝒯`, as on BW p. 32; the dispatched draft
    had dropped this;
  * `1 ≤ 𝒟₀`;
  * (E0) `(r+1)𝒟_j < Tq 0 + 1`, which excludes point collisions for `G_a × ker χ`;
  * (E1) for `m < r` and `|e| = m+1`: `(r+1)!/(r−m)!·𝒟^e < (Sq m+1)·C(Tq m+m+1, m+1)`. This
    excludes transversal subgroups (`ℓ = k`). The factor `(r+1)!/(r−m)!` is Philippon's
    normalisation;
  * (E2) `(r+1)!∏𝒟 < (Sq r+1)·C(Tq r+r, r)`, which excludes `0 × 1`;
  * (E3) `(r+1)!∏_{i≥1}𝒟_i < (Sq(r−1)+1)·C(Tq(r−1)+r−1, r−1)`, which excludes `G_a × 1`;
  * `B` is **integral**;
  * `‖∑B_iℓ_i‖ < π/𝒮`.
* **Conclusion:** there is `1 ≤ ρ < r` such that for every `a > 0` there are a primitive `M ∋ B`
  (ℚ-span) and a `ρ`-set `J` with
  * **case `G_a × H'`:** `∏ℛ·(Sq(ρ−1)+1)·C(Tq(ρ−1)+ρ−1, ρ−1) ≤ constA·∏_J a_i𝒟_i`, or
  * **case `0 × H'`:** `∏ℛ·(Sq ρ+1)·C(Tq ρ+ρ, ρ) ≤ constB·𝒟₀∏_J a_i𝒟_i`.
  
  Here `constA = 2^{1−ρ}(ρ!)²r^ρ(r+1)!/(r+1−ρ)!` and `constB = 2^{1−ρ}(ρ!)²r^ρ(r+1)!/(r−ρ)!`.

**Proof plan for `multiplicity_prop`.**
1. **Degree-zero coordinates.** Let `Z = {i ≥ 1 : 𝒟_i < 1}`; then `deg_{Y_i}P = 0` for `i ∈ Z`.
   * Work on `G/T_Z = G_a × G_m^{Z^c}` with `W̄ = π(W)`. This is needed because P86* requires
     `D_i ≥ 1`, and padding with `D_i = 1` would cost up to `2^I/D_i` per coordinate.
   * `ℓ` is unchanged: `dim W − dim(W∩Lie G') = dim W̄ − dim(W̄∩Lie Ḡ')` when `Lie G' ⊇ Lie T_Z`.
   * The conditions for `Ḡ` follow from (E0)–(E1), because `(r'+1)!/(r'−m)! ≤ (r+1)!/(r−m)!`.
   * The quotient's `G_a×1` and `0×1` pull back to legitimate case-A/B outputs with `ρ = r' < r`.
2. **Operators.** `applyDer c t0 t` and the `applyW` family `(e₀, (0,c_m))` span the same operator
   algebra, since the derivations commute.
3. **Apply `zero_estimate_stepwise`** with `D_i = ⌊𝒟_i⌋`, `θ_j = e^{ℓ_j}` and `Σ_m = {0..Sq m}`.
4. **Cases.** For `G' = G_a^ε × ker𝒵`: `ℓ = k−1` iff `B ∈ ℚ𝒵` (then `B^⊥ ⊇ 𝒵^⊥`), and otherwise
   `ℓ = k`.
   * `ℓ = k` is excluded by (E1); with a collision, by (E0).
   * `G_a × 1` is excluded by (E3), and `0 × 1` by (E2).
   * **Collisions** happen only for `ρ = 1`, since `ℓ` is ℚ-independent. If `B ∈ ℚχ`, then
     integral `B = mχ` gives `|sχ(ℓ)| ≤ S|Λ'| < π`, so there is no collision.
5. **Primitive basis.** `prim_basis_from_minors`, with the maximising `J`.

**`group_reduction`: signature unchanged.** It consumes `PolyOut` and `h10`, as dispatched.
* **Data:** `𝒟 = calD`, `𝒮 = calS`, `𝒯 = calT`, **`Sq/Tq = halfSplit`** (`x/2` for step 0, `x/(2r)`
  for later steps), `a = σ`, `ℓ = lamP`, `c_m = derVec b k L (ι m)`.
* **Integral `B`:** clear the denominators of the rational `B` with `b = ∑B_iL_i`. The denominator
  divides a minor of `L`, which is `≤ r!∏(2^v dσ_j)`. `log` of that is `≪ 9·2^r SD`, so (10) still
  gives `hΛ`.
* **Conditions:** `split_conditions`.
* **(30):** `rank_drop_numerics` plus `κ(ρ) = (64nd)^{r−ρ}κ(r)`.

**Recomputed margins** (natural log, `h = 1`, `σ_j ≥ 1/d`; script in the session scratchpad,
`mult/recheck.py`):
* (E1) ≥ 4.8, tightest at `m = 0`, `e = e₀`, `r = 2`, `d = 1`; ≥ 7.7 for large `r`;
* (E0) ≥ 6.5;
* (E2) ≥ 44;
* (E3) ≥ 86;
* (30) case A ≥ 85 and case B ≥ 42.

All margins grow with `r` and `d`, and the checks are `D`-homogeneous and `h`-monotone.

---

## 4. Recheck of the BW §21 finding, and interface impact

**Independent recheck.** I read BW p. 59–60 again and recomputed from `Defs.lean`.
* BW take `𝒮_i = 𝒮/(r+1)` and `𝒯_i = [𝒯/(r+1)]` for all `i`.
* (5) at `m = 0`, `m₀ = 1` reads `𝒮₀(𝒯₀+1) ≥ 𝒟₀ = h(D₀+1)`. Here `𝒮𝒯 = 2ξ·16rdh·11.75rD` and
  `D₀ = ⌊rD/(2log 2rd)⌋`.
* So the ratio is `752ξ·d·r·log(2rd)/(r+1)²`. It drops below 1 at **`r = 7198` (d = 1)**,
  `16707` (d = 2) and `109807` (d = 10). The script's E1 margin changes sign between r = 7197 and
  7199.
* BW only justify `𝒮_m(𝒯_m+1) ≥ 𝒟₀/r`, which covers `m ≥ 1` but not `m = 0`, `m₀ = 1`.
* **Confirmed.**

**Correction to my scoping note.** I had called this condition "necessary". What is necessary is
only `(𝒮+1)(𝒯+1) > 𝒟₀`, which the ratio `752ξ·r·d·log 2rd` satisfies easily. The split-specific
condition is what the estimate's *proof* needs, because its first step sees only `(𝒮₀, 𝒯₀)`. So:
* BW's Proposition cannot be invoked for `r ≥ 7198`;
* BW's final Theorem is not refuted;
* the half split repairs the gap.

`bw/MULTIPLICITY_SCOPING.md` is amended accordingly.

**Which dispatched statements encode the equal split?** None.
* `PolyOut` (Defs) fixes only `𝒮 = 2ξ^{-rI}S`, `𝒯 = ξ^{rI+1}T` and the degree bounds.
* `analytic_core` and `bw_independent` consume or produce `PolyOut` and `BH` only.
* The split lived only in the (undispatched) `group_reduction` doc comment, which is rewritten
  here.

**Interface changes to dispatched nodes: none.**
* `group_reduction` keeps its signature; `analytic_core`, `bw_independent` and `PolyOut` are
  untouched.
* What is new:
  * the definitions file `DefsMult.lean`;
  * the changed `multiplicity_prop` statement (not previously dispatched);
  * `group_reduction`'s proof imports `minkowski_basis` indirectly, through
    `prim_basis_from_minors`.
-/
namespace Work.BW

open Complex

/-- Column form of an integral relation `∑_a B_a L_a = N b`, for any ring. -/
private lemma col_sum_eq {n r : ℕ} {R : Type*} [Ring R] (B : Fin r → ℤ)
    (L : Fin r → Fin n → ℤ) (b : Fin n → ℤ) (N : ℤ)
    (h : ∀ j, ∑ a, B a * L a j = N * b j) (j : Fin n) :
    (∑ i, (B i : R) * (L i j : R)) = (N : R) * (b j : R) := by
  have hcast : ((N * b j : ℤ) : R) = (N : R) * (b j : R) := by push_cast; ring
  rw [← hcast, ← h j, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.cast_mul]

/-- Linearity of `lamP` in the matrix. -/
lemma lamP_lin {K : Type*} [Field K] {n r ρ : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (v : ℕ) (L : Fin r → Fin n → ℤ) (A : Fin ρ → Fin r → ℤ) (j : Fin ρ) :
    lamP φ α v (fun (j' : Fin ρ) (i : Fin n) => ∑ a, A j' a * L a i) j
      = ∑ a, (A j a : ℂ) * lamP φ α v L a := by
  have key : ∀ i : Fin n,
      ((∑ a, A j a * L a i : ℤ) : ℂ) = ∑ a, (A j a : ℂ) * (L a i : ℂ) := by
    intro i
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun a _ => Int.cast_mul _ _
  simp only [lamP, key]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro i _
  ring

/-- BW §21 (same interface as dispatched `PolyOut`/`analytic_core`). Feed `P` into
`multiplicity_prop` with `𝒟 = calD`, `𝒮 = calS`, `𝒯 = calT`, the **half split**
`Sq = halfSplit r 𝒮`, `Tq = halfSplit r 𝒯` (not BW's equal split `𝒮/(r+1)`, which breaks (5) at
`m = 0` for `r ≥ 7198`), weights `a = σ`, `ℓ = lamP`, `c_m = derVec b k L (ι m)`, and `B` an
integral multiple of the rational `B` with `b = ∑ Bᵢ Lᵢ` (the denominator is `≤ r!∏(2^v d σ_j)`,
absorbed by (10)). Conditions from `split_conditions`, (30) from `rank_drop_numerics`; build
`L' = 𝓛 ∘ L`, `α''`, `σ' = ℛ` as in BW p. 59–60. -/
theorem group_reduction {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (hst : Standing φ α b k c)
    (hr : 2 ≤ r) (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) (ι : Fin (r - 1) → Fin n) (hι : IotaOK b k L ι)
    (h10 : Real.log ‖lam φ α b‖ ≤
        -(9 * 2 ^ r * (pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ) *
          pD r (Module.finrank ℚ K) σ))
    (P : MvPolynomial (Fin (r + 1)) ℂ) (hP : PolyOut φ α b k v L ι σ P) :
    ∃ ρ : ℕ, 1 ≤ ρ ∧ ρ < r ∧ ∃ (L' : Fin ρ → Fin n → ℤ) (α'' : Fin ρ → K) (σ' : Fin ρ → ℝ),
      BH φ α b v c ρ L' α'' σ' := by
  classical
  obtain ⟨hn2, hαne, hlogind, hgcd, hbk, hhmax, hXbw, hc1, hc2⟩ := hst
  obtain ⟨hLind, hbspan, hα'exp, hKum, hσpos, hσhmod, hσrow, hσprod⟩ := hBH
  obtain ⟨hPne, hPdeg0, hPdegj, hPvan⟩ := hP
  set dd : ℕ := Module.finrank ℚ K with hdd
  set hh : ℕ := ph (hL b dd) v with hhh
  have hd1 : 1 ≤ dd := by rw [hdd]; exact Module.finrank_pos
  have hdR : (0 : ℝ) < (dd : ℝ) := by exact_mod_cast hd1
  have hbk0 : b ≠ 0 := fun hb => hbk (by simp [hb])
  have hrn : r ≤ n := by
    have h := hLind.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    exact h
  -- `h ≥ 1`, `v log 2 ≤ h + 1`
  have hhL : (1 : ℝ) ≤ hL b dd := le_trans (Xbw_ge_one n dd hn2 hd1) hXbw
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hvlog : (0 : ℝ) ≤ (v : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg v) hlog2
  have hh1 : 1 ≤ hh := by
    rw [hhh, ph]
    apply Nat.le_floor
    push_cast
    linarith
  have hv1 : (v : ℝ) * Real.log 2 ≤ (hh : ℝ) + 1 := by
    rw [hhh, ph]
    have hlt := Nat.lt_floor_add_one (hL b dd + (v : ℝ) * Real.log 2)
    have hnn : (0 : ℝ) ≤ hL b dd := le_trans (le_of_lt (one_div_pos.mpr hdR)) (le_max_right _ _)
    push_cast at hlt ⊢
    linarith
  -- `σ` bounds
  have hσinv : ∀ j : Fin r, 1 / (dd : ℝ) ≤ σ j := by
    intro j
    have h := hσhmod j
    simp only [hmod] at h
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h
  have hmh : ∀ i : Fin n, 1 / (dd : ℝ) ≤ BakerWustholz.modifiedHeight φ (α i) := by
    intro i
    simp only [BakerWustholz.modifiedHeight]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hrowsum : ∀ a : Fin r, (∑ i, |(L a i : ℝ)|) ≤ (dd : ℝ) * (2 : ℝ) ^ v * σ a := by
    intro a
    have h1 : (∑ i, |(L a i : ℝ)|) ≤
        (dd : ℝ) * ∑ i, |(L a i : ℝ)| * BakerWustholz.modifiedHeight φ (α i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hmul : |(L a i : ℝ)| * (1 / (dd : ℝ)) ≤
          |(L a i : ℝ)| * BakerWustholz.modifiedHeight φ (α i) :=
        mul_le_mul_of_nonneg_left (hmh i) (abs_nonneg _)
      have h2 : |(L a i : ℝ)| / (dd : ℝ) ≤
          |(L a i : ℝ)| * BakerWustholz.modifiedHeight φ (α i) := by
        simpa [div_eq_mul_inv] using hmul
      have h3 := (div_le_iff₀ hdR).mp h2
      linarith
    calc (∑ i, |(L a i : ℝ)|) ≤ (dd : ℝ) * ∑ i, |(L a i : ℝ)| * BakerWustholz.modifiedHeight φ (α i) := h1
      _ ≤ (dd : ℝ) * ((2 : ℝ) ^ v * σ a) := by
            apply mul_le_mul_of_nonneg_left (hσrow a) (le_of_lt hdR)
      _ = (dd : ℝ) * (2 : ℝ) ^ v * σ a := by ring
  -- `lamP` rows are `ℚ`-independent
  have hlLind : LinearIndependent ℚ (fun i : Fin r => lamP φ α v L i) :=
    lamP_linearIndependent φ α v L hlogind hLind
  -- `𝒟`, `hdeg`, `h𝒟0`
  have hdeg : ∀ j : Fin (r + 1), (P.degreeOf j : ℝ) ≤ calD r dd hh σ j := by
    intro j
    induction j using Fin.cases with
    | zero => simpa [calD, Fin.cons_zero] using hPdeg0
    | succ i => simpa [calD, Fin.cons_succ] using hPdegj i
  have hD0 : 1 ≤ calD r dd hh σ 0 := by
    simp only [calD, Fin.cons_zero]
    have h2 : (1 : ℝ) ≤ (pD0 r dd σ : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (pD0 r dd σ : ℝ) := Nat.cast_nonneg _
      linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (hh : ℝ) * ((pD0 r dd σ : ℝ) + 1) := by
            exact mul_le_mul (by exact_mod_cast hh1) h2 (by norm_num) (by positivity)
  -- the half split satisfies the exclusion conditions
  obtain ⟨hSa, hTa, hSsum, hTsum, hE0, hE1, hE2, hE3⟩ :=
    split_conditions (r := r) (d := dd) (h := hh) hr hd1 hh1 σ hσinv
  -- the vanishing hypothesis
  have hvan : ∀ s : ℕ, (s : ℝ) ≤ calS r dd hh → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
      ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ calT r dd σ →
      MvPolynomial.eval (ptS (fun i => lamP φ α v L i) s)
        (applyDer (fun m i => (derVec b k L (ι m) i : ℚ)) t0 t P) = 0 := by
    intro s hs t0 t ht
    exact hPvan s hs t0 t ht
  -- the integral relation `∑ B_a L_a = N b`
  obtain ⟨N, B, hNne, hBne, hBrel, hNbound⟩ :=
    exists_denom_multiple (by omega : 1 ≤ r) L b hbk0 hLind hbspan
  -- `B` is annihilated by the `∂*` operators
  have hcB : ∀ m : Fin (r - 1), ∑ i, ((derVec b k L (ι m) i : ℚ) * (B i : ℚ)) = 0 := by
    intro m
    have hcol : ∀ j : Fin n, (∑ i, (B i : ℚ) * (L i j : ℚ)) = (N : ℚ) * (b j : ℚ) :=
      fun j => col_sum_eq B L b N hBrel j
    have hswap : ∀ j : Fin n, (∑ i, (L i j : ℚ) * (B i : ℚ)) =
        (N : ℚ) * (b j : ℚ) := by
      intro j
      rw [show (∑ i, (L i j : ℚ) * (B i : ℚ)) = (∑ i, (B i : ℚ) * (L i j : ℚ)) from
        Finset.sum_congr rfl (fun i _ => by ring)]
      exact hcol j
    have e1 : (∑ i, (b k : ℚ) * (L i (ι m) : ℚ) * (B i : ℚ)) =
        (b k : ℚ) * ((N : ℚ) * (b (ι m) : ℚ)) := by
      trans (b k : ℚ) * ∑ i, (L i (ι m) : ℚ) * (B i : ℚ)
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      · rw [hswap (ι m)]
    have e2 : (∑ i, (b (ι m) : ℚ) * (L i k : ℚ) * (B i : ℚ)) =
        (b (ι m) : ℚ) * ((N : ℚ) * (b k : ℚ)) := by
      trans (b (ι m) : ℚ) * ∑ i, (L i k : ℚ) * (B i : ℚ)
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      · rw [hswap k]
    simp only [derVec]
    push_cast
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, e1, e2]
    ring
  -- the linear form of `B` is `2^{-v} N Λ`
  have hsum_lamP : ∑ i, (B i : ℂ) * lamP φ α v L i =
      (((2 : ℂ) ^ v)⁻¹ * (N : ℂ)) * lam φ α b := by
    simp only [lamP, lam]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    trans (((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α j))) * ∑ i, (L i j : ℂ) * (B i : ℂ)
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · rw [show (∑ i, (L i j : ℂ) * (B i : ℂ)) = (∑ i, (B i : ℂ) * (L i j : ℂ)) from
        Finset.sum_congr rfl (fun i _ => by ring),
        col_sum_eq B L b N hBrel j]
      ring
  have hnorm : ‖(((2 : ℂ) ^ v)⁻¹ * (N : ℂ)) * lam φ α b‖ =
      (N.natAbs : ℝ) * ((2 : ℝ) ^ v)⁻¹ * ‖lam φ α b‖ := by
    have h1 : |(N : ℝ)| = (N.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
    have h2 : ‖((2 : ℂ) ^ v)⁻¹‖ = ((2 : ℝ) ^ v)⁻¹ := by
      rw [norm_inv, norm_pow, Complex.norm_ofNat]
    have h3 : ‖(N : ℂ)‖ = (N.natAbs : ℝ) := by
      rw [Complex.norm_intCast, h1]
    rw [norm_mul, norm_mul, h2, h3]
    ring
  have hcalSpos : (0 : ℝ) < calS r dd hh := by
    have hxi : (0 : ℝ) < pxi r := by
      have : (0.536 : ℝ) / r < 1 := by
        rw [div_lt_one (by exact_mod_cast (by omega : 0 < r))]
        have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
        linarith
      simp only [pxi]; linarith
    have hSpos : (0 : ℝ) < (pS r dd hh : ℝ) := by
      have : 0 < pS r dd hh := by
        simp only [pS]; positivity
      exact_mod_cast this
    have hz : (0 : ℝ) < pxi r ^ (-((r * pI r dd : ℕ) : ℤ)) := zpow_pos hxi _
    simp only [calS]; positivity
  have hNabs_pos : (0 : ℝ) < (N.natAbs : ℝ) := by
    exact_mod_cast (Int.natAbs_pos.mpr hNne)
  have hNb : (N.natAbs : ℝ) ≤
      (r.factorial : ℝ) * ((2 : ℝ) ^ v * (dd : ℝ)) ^ (2 * r) * (∏ j, σ j) ^ 2 := by
    have hℓ : ∏ a : Fin r, ((∑ i, |(L a i : ℝ)|)) ^ 2 ≤
        ∏ a : Fin r, ((dd : ℝ) * (2 : ℝ) ^ v * σ a) ^ 2 := by
      apply Finset.prod_le_prod₀
      · intro a _
        positivity
      · intro a _
        exact pow_le_pow_left₀ (by positivity) (hrowsum a) 2
    have h2 : ∏ a : Fin r, ((dd : ℝ) * (2 : ℝ) ^ v * σ a) ^ 2 =
        ((dd : ℝ) * (2 : ℝ) ^ v) ^ (2 * r) * (∏ a, σ a) ^ 2 := by
      have e1 : ∀ a : Fin r, ((dd : ℝ) * (2 : ℝ) ^ v * σ a) ^ 2 =
          ((dd : ℝ) * (2 : ℝ) ^ v) ^ 2 * (σ a) ^ 2 := fun a => by ring
      simp only [e1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Finset.prod_pow]
      ring
    calc (N.natAbs : ℝ) ≤ (r.factorial : ℝ) * ∏ a, ((∑ i, |(L a i : ℝ)|)) ^ 2 := hNbound
      _ ≤ (r.factorial : ℝ) * ∏ a, ((dd : ℝ) * (2 : ℝ) ^ v * σ a) ^ 2 :=
            mul_le_mul_of_nonneg_left hℓ (by positivity)
      _ = (r.factorial : ℝ) * ((2 : ℝ) ^ v * (dd : ℝ)) ^ (2 * r) * (∏ j, σ j) ^ 2 := by
            rw [h2]; ring
  have hlogb := h10_log_bound (d := dd) (h := hh) (r := r) (v := v)
    hr hd1 hh1 hv1 σ hσinv (N.natAbs : ℝ) hNabs_pos hNb
  have hlamB : ‖∑ i, (B i : ℂ) * lamP φ α v L i‖ < Real.pi / calS r dd hh := by
    rw [hsum_lamP, hnorm]
    rcases eq_or_ne (lam φ α b) 0 with h0 | h0
    · rw [h0, norm_zero, mul_zero]
      exact div_pos Real.pi_pos hcalSpos
    · exact norm_mul_lt_of_log hr hd1 hh1 σ (N.natAbs : ℝ) ‖lam φ α b‖ hNabs_pos
        (norm_pos_iff.mpr h0) hlogb h10
  -- BW §10 (P86* route)
  have hmp := multiplicity_prop (r := r) hr P hPne (calD r dd hh σ) hdeg hD0
      (calS r dd hh) (calT r dd σ) (halfSplit r (calS r dd hh)) (halfSplit r (calT r dd σ))
      hSa hTa hSsum hTsum hE0 hE1 hE2 hE3
      B hBne (fun m i => (derVec b k L (ι m) i : ℚ)) hι.2 hcB
      (fun i => lamP φ α v L i) hlLind hlamB hvan
  obtain ⟨ρ, hρ1, hρr, hmp'⟩ := hmp
  obtain ⟨M, hMPrim, hMB, J, hJcard, hcase⟩ := hmp' σ hσpos
  have hρr' : ρ ≤ r := le_of_lt hρr
  -- rank-drop bound for the new height product
  have hRle : ∏ j, ∑ i, σ i * |(M j i : ℝ)| ≤ (64 * r * dd : ℝ) ^ (r - ρ) * ∏ j, σ j := by
    have hrd := rank_drop_numerics hr hd1 hh1 σ hσinv ρ hρ1 hρr J hJcard
    rcases hcase with hA | hB
    · set F : ℝ := ((halfSplit r (calS r dd hh) (ρ - 1) : ℝ) + 1) *
          ((halfSplit r (calT r dd σ) (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ) with hF
      have hFpos : (0 : ℝ) < F := by
        rw [hF]
        exact mul_pos (by positivity) (by exact_mod_cast Nat.choose_pos (by omega))
      have hA' : (∏ j, ∑ i, σ i * |(M j i : ℝ)|) * F ≤
          constA r ρ * ∏ i ∈ J, (σ i * calD r dd hh σ i.succ) := by
        rw [hF]; simpa only [mul_assoc] using hA
      have hrdA : constA r ρ * ∏ i ∈ J, (σ i * calD r dd hh σ i.succ) ≤
          (64 * r * dd : ℝ) ^ (r - ρ) * (∏ j, σ j) * F := by
        rw [hF]; simpa only [mul_assoc] using hrd.1
      exact le_of_mul_le_mul_right (le_trans hA' hrdA) hFpos
    · set F : ℝ := ((halfSplit r (calS r dd hh) ρ : ℝ) + 1) *
          ((halfSplit r (calT r dd σ) ρ + ρ).choose ρ : ℝ) with hF
      have hFpos : (0 : ℝ) < F := by
        rw [hF]
        exact mul_pos (by positivity) (by exact_mod_cast Nat.choose_pos (by omega))
      have hA' : (∏ j, ∑ i, σ i * |(M j i : ℝ)|) * F ≤
          constB r ρ * calD r dd hh σ 0 * ∏ i ∈ J, (σ i * calD r dd hh σ i.succ) := by
        rw [hF]; simpa only [mul_assoc] using hB
      have hrdA : constB r ρ * calD r dd hh σ 0 * ∏ i ∈ J, (σ i * calD r dd hh σ i.succ) ≤
          (64 * r * dd : ℝ) ^ (r - ρ) * (∏ j, σ j) * F := by
        rw [hF]; simpa only [mul_assoc] using hrd.2
      exact le_of_mul_le_mul_right (le_trans hA' hrdA) hFpos
  -- the reduced basic hypothesis
  set L' : Fin ρ → Fin n → ℤ := fun j i => ∑ a, M j a * L a i with hL'
  set α'' : Fin ρ → K := fun j => ∏ a, (α' a) ^ (M j a) with hα''
  set σ' : Fin ρ → ℝ := fun j => ∑ a, |(M j a : ℝ)| * σ a with hσ''
  refine ⟨ρ, hρ1, hρr, L', α'', σ', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) the new rows are `ℚ`-independent
    have hMl : LinearIndependent ℚ (fun j a => (M j a : ℚ)) := hMPrim.1
    have key : (fun j i => ((L' j i : ℤ) : ℚ)) = fun j i => ∑ a, (M j a : ℚ) * (L a i : ℚ) := by
      funext j i
      simp only [hL', Int.cast_sum]
      exact Finset.sum_congr rfl (fun a _ => Int.cast_mul _ _)
    rw [key]
    let Φ : (Fin r → ℚ) →ₗ[ℚ] (Fin n → ℚ) :=
      { toFun := fun x i => ∑ a, x a * (L a i : ℚ)
        map_add' := by
          intro x y
          ext i
          simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro q x
          ext i
          simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
          apply Finset.sum_congr rfl
          intro a _
          ring }
    have hker : Φ.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      rw [Fintype.linearIndependent_iff] at hLind
      funext a
      exact hLind (fun a => x a) (by ext i; simpa [Φ, smul_eq_mul] using congrFun hx i) a
    exact hMl.map' Φ hker
  · -- (2) `b` lies in the `ℚ`-span of the new rows
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hMB
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun j => β j / (N : ℚ), ?_⟩
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : (∑ j, (β j / (N : ℚ)) * ((L' j i : ℤ) : ℚ)) =
        (N : ℚ)⁻¹ * ∑ j, β j * ((L' j i : ℤ) : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [div_eq_mul_inv]
      ring
    have h2 : (∑ j, β j * ((L' j i : ℤ) : ℚ)) = (∑ a, (B a : ℚ) * (L a i : ℚ)) := by
      simp only [hL', Int.cast_sum, Int.cast_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [show (∑ j, β j * ((M j a : ℚ) * (L a i : ℚ))) =
          (∑ j, (β j * (M j a : ℚ)) * (L a i : ℚ)) from
        Finset.sum_congr rfl (fun j _ => by ring)]
      rw [← Finset.sum_mul]
      congr 1
      have := congrFun hβ a
      simpa [smul_eq_mul] using this
    have h3 : (∑ a, (B a : ℚ) * (L a i : ℚ)) = (N : ℚ) * (b i : ℚ) :=
      col_sum_eq B L b N hBrel i
    rw [h1, h2, h3]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hNne : ((N : ℚ)) ≠ 0), one_mul]
  · -- (3) the new generators and their logarithms
    intro j
    have h := exp_lamP_prod φ α v L M L' α' (fun j i => by rw [hL']) (fun a => (hα'exp a).1)
      (fun a => (hα'exp a).2) j
    rw [hα'']
    exact ⟨h.2, h.1⟩
  · -- (4) Kummer condition
    exact KummerCond_comp (fun a => (hα'exp a).1) hKum M hMPrim
  · -- (5) positivity of the new heights
    intro j
    have hrowne : (fun a => M j a) ≠ 0 :=
      fun h => hMPrim.1.ne_zero j (funext fun a => by simp [h])
    obtain ⟨a0, ha0⟩ : ∃ a, M j a ≠ 0 := by
      by_contra h
      push_neg at h
      exact hrowne (funext fun a => by simp [h a])
    rw [hσ'']
    have h1 : (1 : ℝ) ≤ |(M j a0 : ℝ)| := by
      have h2 : (1 : ℤ) ≤ |M j a0| := Int.one_le_abs ha0
      exact_mod_cast h2
    have h3 : (0 : ℝ) < |(M j a0 : ℝ)| * σ a0 := mul_pos (by linarith) (hσpos a0)
    refine lt_of_lt_of_le h3 (Finset.single_le_sum (f := fun a => |(M j a : ℝ)| * σ a) ?_
      (Finset.mem_univ a0))
    intro a _
    exact mul_nonneg (abs_nonneg _) (le_of_lt (hσpos a))
  · -- (6) the `hmod` bound
    intro j
    have hrowne : (fun a => M j a) ≠ 0 :=
      fun h => hMPrim.1.ne_zero j (funext fun a => by simp [h])
    have h := hmod_prod_zpow_le (r := r) α' (fun a => (hα'exp a).1)
      (fun a => lamP φ α v L a) σ (fun a => M j a) hrowne hσhmod
    have hlin : lamP φ α v L' j = ∑ a, (M j a : ℂ) * lamP φ α v L a := by
      rw [hL']
      exact lamP_lin φ α v L M j
    rw [hlin, hα'', hσ'']
    exact h
  · -- (7) weighted row sums
    intro j
    have h1 : ∀ i, |(L' j i : ℝ)| ≤ ∑ a, |(M j a : ℝ)| * |(L a i : ℝ)| := by
      intro i
      have hcast : ((L' j i : ℤ) : ℝ) = ∑ a, (M j a : ℝ) * (L a i : ℝ) := by
        rw [hL', Int.cast_sum]
        exact Finset.sum_congr rfl (fun a _ => Int.cast_mul _ _)
      rw [hcast]
      calc |∑ a, (M j a : ℝ) * (L a i : ℝ)| ≤ ∑ a, |(M j a : ℝ) * (L a i : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ a, |(M j a : ℝ)| * |(L a i : ℝ)| := by
            apply Finset.sum_congr rfl
            intro a _
            rw [abs_mul]
    have hmhpos : ∀ i, (0 : ℝ) < BakerWustholz.modifiedHeight φ (α i) :=
      fun i => lt_of_lt_of_le (one_div_pos.mpr hdR) (hmh i)
    rw [hσ'']
    calc ∑ i, |(L' j i : ℝ)| * BakerWustholz.modifiedHeight φ (α i)
        ≤ ∑ i, (∑ a, |(M j a : ℝ)| * |(L a i : ℝ)|) *
            BakerWustholz.modifiedHeight φ (α i) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right (h1 i) (le_of_lt (hmhpos i))
      _ = ∑ a, |(M j a : ℝ)| *
            (∑ i, |(L a i : ℝ)| * BakerWustholz.modifiedHeight φ (α i)) := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ ≤ ∑ a, |(M j a : ℝ)| * ((2 : ℝ) ^ v * σ a) :=
          Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hσrow a) (abs_nonneg _))
      _ = (2 : ℝ) ^ v * ∑ a, |(M j a : ℝ)| * σ a := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
  · -- (8) the `kappa` bound
    have h2 : (64 * r * dd : ℝ) ^ (r - ρ) ≤ (64 * n * dd : ℝ) ^ (r - ρ) := by
      apply pow_le_pow_left₀ (by positivity)
      have hrn' : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
      nlinarith [hdR]
    calc ∏ j, σ' j = ∏ j, ∑ a, |(M j a : ℝ)| * σ a := by rw [hσ'']
      _ = ∏ j, ∑ a, σ a * |(M j a : ℝ)| := by
            apply Finset.prod_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ ≤ (64 * r * dd : ℝ) ^ (r - ρ) * ∏ j, σ j := hRle
      _ ≤ (64 * n * dd : ℝ) ^ (r - ρ) * ∏ j, σ j :=
            mul_le_mul_of_nonneg_right h2 (Finset.prod_nonneg (fun j _ => le_of_lt (hσpos j)))
      _ ≤ (64 * n * dd : ℝ) ^ (r - ρ) *
            (kappa n dd r v c * ∏ i, BakerWustholz.modifiedHeight φ (α i)) :=
            mul_le_mul_of_nonneg_left hσprod (by positivity)
      _ = kappa n dd ρ v c * ∏ i, BakerWustholz.modifiedHeight φ (α i) := by
            rw [kappa_rank_drop (c := c) (hρr := hρr') (hrn := hrn)]
            ring

end Work.BW

/-! ## Status of this node (for the project lead)

The proof of `group_reduction` above is complete: it has no `sorry` of its own, it uses only
sibling nodes of this workspace, and it builds (`lake build Submission.Work.BW.group_reduction`).
At the time of writing `#print axioms Work.BW.group_reduction` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`, where the single `sorryAx` is inherited from
other nodes that are still unfinished. The dependency chain, with the current state of each link:

* `Submission.Work.BW.split_conditions` (0.0-0.3k lines of real arithmetic, PROVED, axiom-clean);
* `Submission.Work.BW.rank_drop_numerics` (the §21 (30) check, PROVED, axiom-clean);
* `multiplicity_prop` -- PROVED except for its final assembly, which is still `:= by sorry`
  (`multiplicity_prop.lean:825`); its two ingredients `zero_estimate_stepwise` and
  `prim_basis_from_minors` are both PROVED and axiom-clean;
* `zero_estimate_stepwise` -- PROVED (axiom-clean except through `stab_step`);
* `stab_step` -- PROVED (its own file is `sorry`-free); it inherits its `sorryAx` from
  `refined_bezout` / `sum_minimalPrimes_le`, i.e. from `Submission/Work/BW/RB/A4.lean:258`
  (`Srel_spanned_le`, the dimension-refined generic chain of Philippon 3.3), which is the single
  remaining mathematical gap on this path; `wuestholz_length` and `coset_length` are now clean.

Nothing in *this* file needs changing. As soon as `Srel_spanned_le` and `multiplicity_prop` are
`sorry`-free and their oleans rebuilt, this node becomes axiom-clean and `declare_proven` applies.
-/
