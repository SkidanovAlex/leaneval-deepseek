import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.regSeq_le_dim_of_ass
import Submission.Work.BW.regSeq_quotient
import Submission.Work.BW.mvpoly_local_regSeq
import Submission.Work.BW.height_add_krullDim_quotient
import Submission.Work.BW.ass_quot_reg
import Submission.Work.BW.krullDim_quot_add_one_le_of_lt


/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive, multiplicity block). Your node is `unmixed_regSeq`. The design is below: find your node in the §2.3 or §3 tables for its content, its dependencies and its size.
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

/-- `Ideal.ofList l` is the ideal generated by the entries of `l`. -/
private lemma ofList_eq_span_set {R : Type*} [Semiring R] (l : List R) :
    Ideal.ofList l = Ideal.span {x | x ∈ l} := by
  induction l with
  | nil => simp
  | cons r rs ih =>
    rw [Ideal.ofList_cons, ih, ← Ideal.span_union]
    congr 1
    ext x
    simp [or_comm]

/-- Arithmetic: if `a + k ≤ n` in `ℕ∞` and `r + k = n`, then `a ≤ r`. -/
private lemma enat_le_of_add_le {a : ℕ∞} {r k n : ℕ} (hk : r + k = n)
    (h : a + (k : ℕ∞) ≤ (n : ℕ∞)) : a ≤ (r : ℕ∞) := by
  have ha : a ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at h
    exact absurd h (not_le_of_gt (ENat.natCast_lt_top n))
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ha
  rw [← hm, ← Nat.cast_add, ENat.natCast_le_natCast] at h
  rw [← hm, ENat.natCast_le_natCast]
  omega

/-- In `WithBot ℕ∞`, a natural `m` is at most `D + m` when `D ≠ ⊥`. -/
private lemma natCast_le_add_of_ne_bot {D : WithBot ℕ∞} (hD : D ≠ ⊥) (m : ℕ) :
    ((m : ℕ∞) : WithBot ℕ∞) ≤ D + ((m : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hD
  rw [← hd, ← WithBot.coe_add, WithBot.coe_le_coe]
  exact le_add_of_nonneg_left (zero_le : (0 : ℕ∞) ≤ d)

/-- The Krull dimension of a nontrivial quotient is not `bot`. -/
private lemma ringKrullDim_quot_ne_bot {R : Type*} [CommRing R] {I : Ideal R} (h : I ≠ ⊤) :
    ringKrullDim (R ⧸ I) ≠ ⊥ := fun hbot =>
  (not_subsingleton_iff_nontrivial.mpr (Ideal.Quotient.nontrivial_iff.mpr h))
    (ringKrullDim_eq_bot_iff_subsingleton.mp hbot)

/-- Block A5d (Macaulay unmixedness at points of affine space, without Cohen–Macaulay theory).
In `ℂ[σ]_𝔪`, every associated prime of the quotient by a regular sequence `f` is minimal over
`(f)`. From A5a–A5c: `p ∈ Ass` has `ht p ≤ |f|`, while every prime containing `(f)` has height
`≥ |f|`. -/
theorem unmixed_regSeq {σ : Type*} [Fintype σ] (𝔪 : Ideal (MvPolynomial σ ℂ)) [𝔪.IsMaximal]
    (f : List (Localization.AtPrime 𝔪))
    (hf : ∀ x ∈ f, x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime 𝔪) f)
    (p : Ideal (Localization.AtPrime 𝔪))
    (hp : p ∈ associatedPrimes (Localization.AtPrime 𝔪)
      (Localization.AtPrime 𝔪 ⧸ Ideal.span {x | x ∈ f})) :
    p ∈ (Ideal.span {x | x ∈ f}).minimalPrimes := by
  haveI : IsNoetherianRing (Localization.AtPrime 𝔪) := inferInstance
  haveI : IsLocalRing (Localization.AtPrime 𝔪) := inferInstance
  haveI : Nontrivial (Localization.AtPrime 𝔪) := inferInstance
  have hp' : p.IsPrime := hp.1
  -- the ideal generated by `f` is contained in `p`
  have hle : Ideal.span {x | x ∈ f} ≤ p := by
    obtain ⟨y, hy⟩ := (isAssociatedPrime_iff (R := Localization.AtPrime 𝔪)
      (M := Localization.AtPrime 𝔪 ⧸ Ideal.span {x | x ∈ f}) (I := p)).mp hp |>.2
    rw [hy]
    intro r hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    have hann : r ∈ Module.annihilator (Localization.AtPrime 𝔪)
        (Localization.AtPrime 𝔪 ⧸ Ideal.span {x | x ∈ f}) := by
      rw [Ideal.annihilator_quotient]; exact hr
    exact (Module.mem_annihilator.mp hann) y
  -- nontriviality of the quotient
  have hIne : Ideal.span {x | x ∈ f} ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime 𝔪)).ne_top
      (Ideal.span_le.mpr hf)
  haveI hntI : Nontrivial (Localization.AtPrime 𝔪 ⧸ Ideal.span {x | x ∈ f}) :=
    Ideal.Quotient.nontrivial_iff.mpr hIne
  -- A5c: a regular sequence of length `card σ`, plus the dimension bound
  obtain ⟨⟨rs, hrs_len, hrs_mem, hrs_reg⟩, hdimA⟩ := mvpoly_local_regSeq 𝔪
  -- B': dimension of the quotient by the regular sequence
  have hB : ringKrullDim (Localization.AtPrime 𝔪 ⧸ Ideal.span {x | x ∈ f})
      + ((f.length : ℕ∞) : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime 𝔪) := by
    simpa [ofList_eq_span_set] using
      ringKrullDim_add_length_eq_ringKrullDim_of_isRegular (R := Localization.AtPrime 𝔪) f hreg
  -- `|f| ≤ |rs|`
  have hDne : ringKrullDim (Localization.AtPrime 𝔪 ⧸ Ideal.span {x | x ∈ f}) ≠ ⊥ := fun hbot =>
    (not_subsingleton_iff_nontrivial.mpr hntI) (ringKrullDim_eq_bot_iff_subsingleton.mp hbot)
  have hEne : ringKrullDim (Localization.AtPrime 𝔪) ≠ ⊥ := fun hbot =>
    (not_subsingleton_iff_nontrivial.mpr (inferInstance : Nontrivial (Localization.AtPrime 𝔪)))
      (ringKrullDim_eq_bot_iff_subsingleton.mp hbot)
  have hrn : f.length ≤ rs.length := by
    have hstep : ((f.length : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime 𝔪) := by
      rw [← hB]
      exact natCast_le_add_of_ne_bot hDne f.length
    have hstep' : ringKrullDim (Localization.AtPrime 𝔪)
        ≤ ((rs.length : ℕ∞) : WithBot ℕ∞) := by
      simpa [hrs_len] using hdimA
    exact ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp (hstep.trans hstep'))
  -- A5b: a regular sequence modulo `(f)`
  obtain ⟨ss, hss_len, hss_mem, hss_reg⟩ := regSeq_quotient rs f hrs_mem hrs_reg hf hreg hrn
  -- A5a: `dim A/p` is at least the length of that sequence
  have hC : ((ss.length : ℕ∞) : WithBot ℕ∞)
      ≤ ringKrullDim (Localization.AtPrime 𝔪 ⧸ p) :=
    regSeq_le_dim_of_ass (Localization.AtPrime 𝔪 ⧸ Ideal.span {x | x ∈ f})
      ss hss_mem hss_reg p hp
  -- (A): height plus dimension of the quotient
  have hA : ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (Localization.AtPrime 𝔪 ⧸ p)
      ≤ ringKrullDim (Localization.AtPrime 𝔪) :=
    height_add_krullDim_quotient (R := Localization.AtPrime 𝔪) p
  -- hence `ht p ≤ |f|`
  have hpne : p ≠ ⊤ := hp'.ne_top
  haveI hntp : Nontrivial (Localization.AtPrime 𝔪 ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hpne
  have hDpne : ringKrullDim (Localization.AtPrime 𝔪 ⧸ p) ≠ ⊥ := fun hbot =>
    (not_subsingleton_iff_nontrivial.mpr hntp)
      (ringKrullDim_eq_bot_iff_subsingleton.mp hbot)
  have hple : p.height ≤ (f.length : ℕ∞) := by
    obtain ⟨dp, hdp⟩ := WithBot.ne_bot_iff_exists.mp hDpne
    obtain ⟨dI, hdI⟩ := WithBot.ne_bot_iff_exists.mp hDne
    obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hEne
    have hA' : p.height + dp ≤ e := by
      have h := hA
      rw [← hdp, ← he, ← WithBot.coe_add, WithBot.coe_le_coe] at h
      exact h
    have hB' : dI + (f.length : ℕ∞) = e := by
      have h := hB
      rw [← hdI, ← he, ← WithBot.coe_add, WithBot.coe_inj] at h
      exact h
    have hdim' : e ≤ (rs.length : ℕ∞) := by
      have h := hdimA
      rw [← he] at h
      have h3 : (e : WithBot ℕ∞) ≤ ((Fintype.card σ : ℕ∞) : WithBot ℕ∞) := by simpa using h
      have h4 : e ≤ (Fintype.card σ : ℕ∞) := WithBot.coe_le_coe.mp h3
      rwa [← hrs_len] at h4
    have hC' : (ss.length : ℕ∞) ≤ dp := WithBot.coe_le_coe.mp (by rw [hdp]; exact hC)
    rw [hss_len] at hC'
    have hmain : p.height + ((rs.length - f.length : ℕ) : ℕ∞) ≤ (rs.length : ℕ∞) := by
      calc p.height + ((rs.length - f.length : ℕ) : ℕ∞) ≤ p.height + dp := by gcongr
        _ ≤ e := hA'
        _ ≤ (rs.length : ℕ∞) := hdim'
    exact enat_le_of_add_le (by omega) hmain
  -- minimal primes over `(f)` have height `≥ |f|`
  have hIh : (f.length : ℕ∞) ≤ (Ideal.span {x | x ∈ f}).height := by
    rw [Ideal.height_eq_inf_minimalPrimes]
    refine le_iInf₂ fun q hq => ?_
    have hq' : q.IsPrime := hq.isPrime
    have hIq : Ideal.span {x | x ∈ f} ≤ q := hq.le
    have hloc : RingTheory.Sequence.IsRegular (Localization.AtPrime q)
        (f.map (algebraMap (Localization.AtPrime 𝔪) (Localization.AtPrime q))) :=
      RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalization_of_mem
        (Localization.AtPrime q) q hreg.1 fun r hr => hIq (Ideal.subset_span hr)
    have heq := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
      (R := Localization.AtPrime q)
      (f.map (algebraMap (Localization.AtPrime 𝔪) (Localization.AtPrime q))) hloc
    have hdimq : ringKrullDim (Localization.AtPrime q)
        = ((q.height : ℕ∞) : WithBot ℕ∞) :=
      IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)
    have hne' := ringKrullDim_quot_ne_bot
      (R := Localization.AtPrime q) (I := Ideal.ofList
        (f.map (algebraMap (Localization.AtPrime 𝔪) (Localization.AtPrime q))))
      (by simpa [Ideal.mul_top] using hloc.top_ne_smul.symm)
    have hge : ((f.length : ℕ∞) : WithBot ℕ∞) ≤ ((q.height : ℕ∞) : WithBot ℕ∞) := by
      rw [← hdimq, ← heq]
      simpa [List.length_map] using natCast_le_add_of_ne_bot hne' f.length
    exact WithBot.coe_le_coe.mp hge
  exact Ideal.mem_minimalPrimes_of_height_le hle (hple.trans hIh)

end Work.BW
