import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.moduleFinite_homPiece
import Submission.Work.BW.rayPoly_eq
import Submission.Work.BW.poly_sub_comp_one
import Submission.Work.BW.weightedHomogeneousComponent_mul_of_mem

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive, multiplicity block). Your node is `rayDeg_hyperplane`. The design is below: find your node in the §2.3 or §3 tables for its content, its dependencies and its size.
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

open MvPolynomial Finsupp

/-! ### Supporting lemmas (helpers for `rayDeg_hyperplane`) -/

/-- **The exact sequence of Philippon 3.1 at `d = D`.** Cutting the multihomogeneous ideal `I` of
`R = ℂ[X_{i0}, X_{i1}]` by a non-zerodivisor `P` of multidegree `D` produces the exact sequence
`0 → (R/I)_{(t-1)D} →·P (R/I)_{tD} → (R/(I,P))_{tD} → 0`, hence the identity of ray Hilbert
functions `dim (R/I)_{tD} = dim (R/(I,P))_{tD} + dim (R/I)_{(t-1)D}` for `t ≥ 1`. -/
private theorem rayHilb_cut_one {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (I : Ideal (MR N)) (hI : MultiHom N I)
    (P : MR N) (hP : P ∈ homPiece N D) (hreg : ∀ f, P * f ∈ I → f ∈ I) (t : ℕ) (ht : 1 ≤ t) :
    rayHilb N D I t = rayHilb N D (I ⊔ Ideal.span {P}) t + rayHilb N D I (t - 1) := by
  set J : Ideal (MR N) := I ⊔ Ideal.span {P} with hJdef
  set A : Submodule ℂ (MR N) := homPiece N (t • D) with hAdef
  set B : Submodule ℂ (MR N) := homPiece N ((t - 1) • D) with hBdef
  set X : Submodule ℂ ↥A := Submodule.comap A.subtype (I.restrictScalars ℂ) with hXdef
  set Y : Submodule ℂ ↥B := Submodule.comap B.subtype (I.restrictScalars ℂ) with hYdef
  set C : Submodule ℂ ↥A := Submodule.comap A.subtype (J.restrictScalars ℂ) with hCdef
  haveI hAfin : Module.Finite ℂ ↥A := by rw [hAdef]; exact moduleFinite_homPiece N (t • D)
  haveI hBfin : Module.Finite ℂ ↥B := by rw [hBdef]; exact moduleFinite_homPiece N ((t - 1) • D)
  -- `(t-1)D + D = tD`
  have hdeg : (t - 1) • D + D = t • D := by
    conv_rhs => rw [← Nat.sub_add_cancel ht]
    rw [add_smul, one_smul]
  have hdeg' : D + (t - 1) • D = t • D := by rw [add_comm D ((t - 1) • D), hdeg]
  -- the map `f ↦ P * f`, from the `(t-1)D` piece to the `tD` piece
  have hmulA : ∀ f : ↥B, P * (f : MR N) ∈ A := by
    intro f
    have hfB : (f : MR N) ∈ homPiece N ((t - 1) • D) := by simpa [hBdef] using f.2
    have hsub : homPiece N (D + (t - 1) • D) = homPiece N (t • D) := congrArg (homPiece N) hdeg'
    have h2 : homPiece N D * homPiece N ((t - 1) • D) ≤ homPiece N (t • D) := by
      rw [← hsub]
      exact weightedHomogeneousSubmodule_mul (mdeg N) D ((t - 1) • D)
    have h3 : P * (f : MR N) ∈ homPiece N (t • D) := h2 (Submodule.mul_mem_mul hP hfB)
    rwa [hAdef]
  let μ : ↥B →ₗ[ℂ] ↥A :=
    { toFun := fun f => ⟨P * (f : MR N), hmulA f⟩
      map_add' := by
        intro f g
        ext
        simp only [Submodule.coe_add]
        rw [mul_add]
      map_smul' := by
        intro c f
        ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [mul_smul_comm] }
  have hμcoe : ∀ w : ↥B, A.subtype (μ w) = P * (w : MR N) := fun w => rfl
  have hμcoe' : ∀ w : ↥B, ((μ w : ↥A) : MR N) = P * (w : MR N) := fun w => rfl
  let ν : ↥B →ₗ[ℂ] (↥A ⧸ X) := X.mkQ.comp μ
  have hνapply : ∀ f, ν f = X.mkQ (μ f) := fun f => rfl
  -- the kernel of `ν` is `Y`
  have hker : ν.ker = Y := by
    ext f
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      have h1 : μ f ∈ X := by
        have h2 : X.mkQ (μ f) = 0 := by rw [← hνapply f]; exact h
        rw [Submodule.mkQ_apply] at h2
        exact (Submodule.Quotient.mk_eq_zero X).mp h2
      have h3 : ((μ f : ↥A) : MR N) ∈ I := by
        have h4 := h1; rw [hXdef, Submodule.mem_comap] at h4; exact h4
      have h5 : P * (f : MR N) ∈ I := by rw [← hμcoe' f]; exact h3
      have h6 : (f : MR N) ∈ I := hreg _ h5
      rw [hYdef, Submodule.mem_comap]; exact h6
    · intro h
      have h1 : (f : MR N) ∈ I := by
        have h2 := h; rw [hYdef, Submodule.mem_comap] at h2; exact h2
      have h2 : P * (f : MR N) ∈ I := Ideal.mul_mem_left I P h1
      refine (Submodule.Quotient.mk_eq_zero X).mpr ?_
      rw [hXdef, Submodule.mem_comap, hμcoe f]
      exact h2
  -- `X ⊔ μ.range = C`, by the graded decomposition
  have hsup : X ⊔ μ.range = C := by
    refine le_antisymm (sup_le ?_ ?_) ?_
    · intro x hx
      have h1 : (x : MR N) ∈ I := by
        have h2 := hx; rw [hXdef, Submodule.mem_comap] at h2; exact h2
      rw [hCdef, Submodule.mem_comap, hJdef]
      exact Ideal.mem_sup_left h1
    · rintro x ⟨f, rfl⟩
      rw [hCdef, Submodule.mem_comap, hJdef, hμcoe f]
      refine Ideal.mem_sup_right ?_
      rw [Ideal.mem_span_singleton']
      exact ⟨(f : MR N), by rw [mul_comm]⟩
    · intro x hx
      have hxJ : (x : MR N) ∈ J := by
        have h2 := hx; rw [hCdef, Submodule.mem_comap] at h2; exact h2
      rw [hJdef, Submodule.mem_sup] at hxJ
      obtain ⟨y, hyI, z, hzP, hyz⟩ := hxJ
      rw [Ideal.mem_span_singleton'] at hzP
      obtain ⟨a, ha⟩ := hzP
      have hxa : (x : MR N) = y + P * a := by rw [← hyz, ← ha]; ring
      have hxhom : (x : MR N).IsWeightedHomogeneous (mdeg N) (t • D) := by
        have h2 : (x : MR N) ∈ homPiece N (t • D) := by simpa [hAdef] using x.2
        exact h2
      have hself : MvPolynomial.weightedHomogeneousComponent (mdeg N) (t • D) (x : MR N) =
          (x : MR N) := MvPolynomial.weightedHomogeneousComponent_eq_self hxhom
      have hcomp : MvPolynomial.weightedHomogeneousComponent (mdeg N) (t • D) (P * a) =
          P * MvPolynomial.weightedHomogeneousComponent (mdeg N) ((t - 1) • D) a := by
        have h := weightedHomogeneousComponent_mul_of_mem hP a ((t - 1) • D)
        rwa [hdeg] at h
      have hdecomp : (x : MR N) =
          MvPolynomial.weightedHomogeneousComponent (mdeg N) (t • D) y +
            P * MvPolynomial.weightedHomogeneousComponent (mdeg N) ((t - 1) • D) a := by
        rw [← hself, hxa, map_add, hcomp]
      have hcyM : MvPolynomial.weightedHomogeneousComponent (mdeg N) (t • D) y ∈ A :=
        MvPolynomial.weightedHomogeneousComponent_mem (mdeg N) y (t • D)
      have hcaM : MvPolynomial.weightedHomogeneousComponent (mdeg N) ((t - 1) • D) a ∈ B :=
        MvPolynomial.weightedHomogeneousComponent_mem (mdeg N) a ((t - 1) • D)
      have hux : (⟨MvPolynomial.weightedHomogeneousComponent (mdeg N) (t • D) y, hcyM⟩ : ↥A) ∈ X := by
        rw [hXdef, Submodule.mem_comap]
        exact hI y hyI (t • D)
      have hwrange : μ ⟨MvPolynomial.weightedHomogeneousComponent (mdeg N) ((t - 1) • D) a, hcaM⟩
          ∈ μ.range := ⟨_, rfl⟩
      have hsum : (⟨MvPolynomial.weightedHomogeneousComponent (mdeg N) (t • D) y, hcyM⟩ : ↥A) +
          μ ⟨MvPolynomial.weightedHomogeneousComponent (mdeg N) ((t - 1) • D) a, hcaM⟩ = x := by
        refine Subtype.ext ?_
        show MvPolynomial.weightedHomogeneousComponent (mdeg N) (t • D) y +
            P * MvPolynomial.weightedHomogeneousComponent (mdeg N) ((t - 1) • D) a = (x : MR N)
        exact hdecomp.symm
      exact Submodule.mem_sup.mpr ⟨_, hux, _, hwrange, hsum⟩
  -- dimension count
  haveI hAq : Module.Finite ℂ (↥A ⧸ X) :=
    Module.Finite.of_surjective X.mkQ (Submodule.mkQ_surjective X)
  have h1 := Submodule.finrank_quotient_add_finrank (M := ↥A ⧸ X) ν.range
  have h2 := LinearMap.finrank_range_add_finrank_ker ν
  have h3 : Module.finrank ℂ (↥B ⧸ Y) = Module.finrank ℂ ↥B - Module.finrank ℂ ↥Y :=
    Submodule.finrank_quotient Y
  have h4 : Module.finrank ℂ ↥Y ≤ Module.finrank ℂ ↥B := by
    have h := Submodule.finrank_mono (le_top : Y ≤ (⊤ : Submodule ℂ ↥B))
    rwa [finrank_top] at h
  have hrange : Submodule.map X.mkQ μ.range = ν.range := by
    rw [show ν = X.mkQ.comp μ from rfl, LinearMap.range_comp]
  have h5 : Module.finrank ℂ ((↥A ⧸ X) ⧸ ν.range) = Module.finrank ℂ (↥A ⧸ C) := by
    rw [← hrange, ← hsup]
    exact (Submodule.quotientQuotientEquivQuotientSup X μ.range).finrank_eq
  have hrayI : rayHilb N D I t = Module.finrank ℂ (↥A ⧸ X) := by
    rw [rayHilb, ← hAdef, ← hXdef]
  have hrayJ : rayHilb N D (I ⊔ Ideal.span {P}) t = Module.finrank ℂ (↥A ⧸ C) := by
    rw [rayHilb, ← hAdef, ← hCdef]
  have hrayB : rayHilb N D I (t - 1) = Module.finrank ℂ (↥B ⧸ Y) := by
    rw [rayHilb, ← hBdef, ← hYdef]
  rw [hrayI, hrayJ, hrayB, hker] at *
  omega

/-- Block A3a (Philippon 1986, 3.1 at `d = D`). Cutting by a non-zerodivisor `P` of multidegree
exactly `D` lowers the ray dimension by one and keeps `H(·; D)`: from the exact sequence
`0 → (R/I)_{(t-1)D} → (R/I)_{tD} → (R/(I,P))_{tD} → 0`. -/
theorem rayDeg_hyperplane {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I : Ideal (MR N)) (hI : MultiHom N I) (P : MR N) (hP : P ∈ homPiece N D)
    (hreg : ∀ f, P * f ∈ I → f ∈ I) (hne : rayPoly N D I ≠ 0) (hpos : 1 ≤ rayDim N D I) :
    rayDim N D (I ⊔ Ideal.span {P}) + 1 = rayDim N D I ∧
      rayDeg N D (I ⊔ Ideal.span {P}) = rayDeg N D I := by
  have hIex : ∃ q : Polynomial ℚ, IsRayPoly N D I q := by
    by_contra h
    exact hne (by rw [rayPoly, dite_eq_right h])
  set q : Polynomial ℚ := rayPoly N D I with hqdef
  have hq : IsRayPoly N D I q := by
    rw [hqdef, rayPoly, dite_eq_left hIex]
    exact Classical.choose_spec hIex
  have hd : 1 ≤ q.natDegree := hpos
  set p : Polynomial ℚ := q - q.comp (Polynomial.X - Polynomial.C 1) with hpdef
  -- `p` is the ray Hilbert polynomial of `I ⊔ (P)`
  have hp : IsRayPoly N D (I ⊔ Ideal.span {P}) p := by
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hq
    rw [IsRayPoly]
    filter_upwards [Filter.eventually_ge_atTop (max T 1 + 1)] with t ht
    have ht1 : 1 ≤ t := by omega
    have hcut := rayHilb_cut_one D I hI P hP hreg t ht1
    have h1 : (rayHilb N D I t : ℚ) = q.eval (t : ℚ) := hT t (by omega)
    have h2 : (rayHilb N D I (t - 1) : ℚ) = q.eval ((t - 1 : ℕ) : ℚ) := hT (t - 1) (by omega)
    have h4 : (rayHilb N D (I ⊔ Ideal.span {P}) t : ℚ) =
        (rayHilb N D I t : ℚ) - (rayHilb N D I (t - 1) : ℚ) := by
      have hcast : ((rayHilb N D I t : ℕ) : ℚ) =
          ((rayHilb N D (I ⊔ Ideal.span {P}) t : ℕ) : ℚ) +
            ((rayHilb N D I (t - 1) : ℕ) : ℚ) := by rw [hcut, Nat.cast_add]
      linarith
    have hpval : p.eval (t : ℚ) = q.eval (t : ℚ) - q.eval ((t - 1 : ℕ) : ℚ) := by
      have hev : (q.comp (Polynomial.X - Polynomial.C 1)).eval (t : ℚ) =
          q.eval ((t - 1 : ℕ) : ℚ) := by
        rw [Polynomial.eval_comp]
        congr 1
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        rw [Nat.cast_sub ht1]
        norm_num
      rw [hpdef, Polynomial.eval_sub, hev]
    rw [hpval, h4, h1, h2]
  have hJpoly : rayPoly N D (I ⊔ Ideal.span {P}) = p := rayPoly_eq hp
  have hpd := poly_sub_comp_one q hd
  constructor
  · have hdimI : rayDim N D I = q.natDegree := by rw [rayDim, ← hqdef]
    have hdimJ : rayDim N D (I ⊔ Ideal.span {P}) = p.natDegree := by rw [rayDim, hJpoly]
    rw [hdimJ, hdimI, hpd.1]
    omega
  · rw [rayDeg, hJpoly, rayDeg, ← hqdef, hpd.1, hpd.2]
    have hnat : q.natDegree.factorial = q.natDegree * (q.natDegree - 1).factorial := by
      conv_lhs => rw [← Nat.sub_add_cancel hd]
      rw [Nat.factorial_succ, Nat.sub_add_cancel hd]
    have hfc : (q.natDegree.factorial : ℚ) =
        (q.natDegree : ℚ) * ((q.natDegree - 1).factorial : ℚ) := by
      rw [hnat, Nat.cast_mul]
    rw [hfc]
    ring

end Work.BW
