import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.GradedHilbDefs
import Submission.Work.BW.rayDegAux
import Submission.Work.BW.sandwich_poly
import Submission.Work.BW.poly_natDegree_eventually_le
import Submission.Work.BW.multiHom_assPrime
import Submission.Work.BW.hilb_serre_input
import Submission.Work.BW.exists_graded_prime_series
import Submission.Work.BW.rayPoly_prime_drop


/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive, multiplicity block). Your node is `rayDeg_additive`. The design is below: find your node in the §2.3 or §3 tables for its content, its dependencies and its size.
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

open MvPolynomial

/-! ### Auxiliary lemmas towards `rayDeg_additive` -/

variable {N : ℕ}

theorem castF_nsmul {N : ℕ} (k : ℕ) (x : Fin (N + 1) →₀ ℕ) :
    castF (k • x) = k • castF x := by
  ext i; simp [castF_apply]

theorem castF_single {N : ℕ} (i : Fin (N + 1)) (k : ℕ) :
    castF (Finsupp.single i k) = Finsupp.single i (k : ℤ) := by
  ext j
  by_cases h : i = j
  · subst h; simp [castF_apply]
  · rw [castF_apply, Finsupp.single_eq_of_ne (Ne.symm h)]
    simp [Finsupp.single_eq_of_ne (Ne.symm h)]

/-- The weight of a monomial in the `ℕ^{N+1}`-grading is the cast of its weight in the
`ℤ^{N+1}`-grading. -/
theorem weight_mdeg_eq (N : ℕ) (s : Fin (N + 1) × Fin 2 →₀ ℕ) :
    castF (Finsupp.weight (mdeg N) s) = Finsupp.weight (wZ N) s := by
  induction s using Finsupp.induction with
  | zero => simp [castF_zero]
  | single_add a b f haf hb ih =>
      have h1 : Finsupp.weight (mdeg N) (Finsupp.single a b + f)
          = b • mdeg N a + Finsupp.weight (mdeg N) f := by
        rw [map_add, Finsupp.weight_single]
      have h2 : Finsupp.weight (wZ N) (Finsupp.single a b + f)
          = b • wZ N a + Finsupp.weight (wZ N) f := by
        rw [map_add, Finsupp.weight_single]
      rw [h1, h2, castF_add, castF_nsmul, ih]
      congr 1
      simp [mdeg, wZ, castF_single]

/-- The ray Hilbert function is the Hilbert function of the multigraded quotient. -/
theorem rayHilb_eq_hilbIdeal (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (J : Ideal (MR N)) (t : ℕ) :
    rayHilb N D J t = hilbIdeal N J (castF (t • D)) := by
  rw [rayHilb, hilbIdeal, homPiece_eq_pieceZ]

/-- `cbeta 2 k = k + 1` for `k ≥ -1`. -/
theorem cbeta_two (k : ℤ) (hk : -1 ≤ k) : cbeta 2 k = (k : ℚ) + 1 := by
  rcases eq_or_lt_of_le hk with h | h
  · subst h
    rw [cbeta_of_neg (by norm_num : (-1 : ℤ) < 0)]
    norm_num
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, k = (j : ℤ) := ⟨k.toNat, by omega⟩
    subst hj
    rw [cbeta_pos (by norm_num : (0 : ℕ) < 2) (by omega : (0 : ℤ) ≤ (j : ℤ))]
    rw [Int.toNat_natCast j]
    have h1 : (j + 2 - 1) = j + 1 := by omega
    rw [h1, Nat.choose_one_right]
    push_cast
    ring

/-! ### The ray models -/

/-- The univariate polynomial `t ↦ ∑_v Q_v ∏_i (D_i t - (v_i - 1))`, i.e. the multivariate
"Hilbert polynomial" of `Q` evaluated at `t • D`. -/
noncomputable def rayModel (N : ℕ) (D : Fin (N + 1) →₀ ℕ)
    (Q : MvPolynomial (Fin (N + 1)) ℚ) : Polynomial ℚ :=
  ∑ v ∈ Q.support, Polynomial.C (Q.coeff v) *
    ∏ i, (Polynomial.C ((D i : ℚ)) * Polynomial.X - Polynomial.C ((v i : ℚ) - 1))

/-- The shifted ray model `t ↦ ∑_v Q_v ∏_i (D_i t - (E_i + v_i - 1))`. -/
noncomputable def rayModelS (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (E : Fin (N + 1) →₀ ℕ)
    (Q : MvPolynomial (Fin (N + 1)) ℚ) : Polynomial ℚ :=
  ∑ v ∈ Q.support, Polynomial.C (Q.coeff v) *
    ∏ i, (Polynomial.C ((D i : ℚ)) * Polynomial.X -
      Polynomial.C ((E i : ℚ) + (v i : ℚ) - 1))

theorem rayModel_eval (N : ℕ) (D : Fin (N + 1) →₀ ℕ)
    (Q : MvPolynomial (Fin (N + 1)) ℚ) (t : ℚ) :
    (rayModel N D Q).eval t = ∑ v ∈ Q.support,
      Q.coeff v * ∏ i, ((D i : ℚ) * t - ((v i : ℚ) - 1)) := by
  rw [rayModel, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_C]

theorem rayModelS_eval (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (E : Fin (N + 1) →₀ ℕ)
    (Q : MvPolynomial (Fin (N + 1)) ℚ) (t : ℚ) :
    (rayModelS N D E Q).eval t = ∑ v ∈ Q.support,
      Q.coeff v * ∏ i, ((D i : ℚ) * t - ((E i : ℚ) + (v i : ℚ) - 1)) := by
  rw [rayModelS, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_C]

/-- `kFun` with all multiplicities `2` is the model sum, as soon as the argument is large
enough coordinatewise. -/
theorem kFun_two_eq (N : ℕ) (Q : MvPolynomial (Fin (N + 1)) ℚ) (u : Fin (N + 1) →₀ ℤ)
    (h : ∀ v ∈ Q.support, ∀ i, (v i : ℤ) ≤ u i + 1) :
    kFun N (fun _ => 2) Q u
      = ∑ v ∈ Q.support, Q.coeff v * ∏ i, (((u i : ℚ) - (v i : ℚ)) + 1) := by
  rw [kFun]
  refine Finset.sum_congr rfl fun v hv => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [cbeta_two]
  · push_cast; ring
  · have := h v hv i
    omega




/-! ### Monotonicity of the graded piece dimension -/

/- `finrank_quotient_le_of_le` and `hilbIdeal_anti` live in `Submission.Work.BW.rayDegAux`. -/

/-! ### Step C2: the ray models evaluate the `kFun` along the ray -/

theorem kFun_two_ray (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (Q : MvPolynomial (Fin (N + 1)) ℚ) :
    ∀ᶠ t : ℕ in Filter.atTop,
      kFun N (fun _ => 2) Q (castF (t • D)) = (rayModel N D Q).eval (t : ℚ) := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ, ∀ v ∈ Q.support, ∀ i, v i ≤ T := by
    refine ⟨Q.support.sup (fun (v : Fin (N + 1) →₀ ℕ) =>
      Finset.univ.sup (fun (i : Fin (N + 1)) => v i)), fun v hv i => ?_⟩
    exact le_trans (Finset.le_sup (Finset.mem_univ i))
      (Finset.le_sup (f := fun (v : Fin (N + 1) →₀ ℕ) =>
        Finset.univ.sup (fun (i : Fin (N + 1)) => v i)) hv)
  refine Filter.eventually_atTop.mpr ⟨T + 1, fun t ht => ?_⟩
  rw [kFun_two_eq]
  · rw [rayModel_eval]
    refine Finset.sum_congr rfl fun v hv => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : (castF (t • D)) i = ((t * D i : ℕ) : ℤ) := by simp [castF_apply]
    rw [h1]
    push_cast
    ring
  · intro v hv i
    have hvT := hT v hv i
    have hDi : 1 ≤ D i := hD i
    have h1 : (castF (t • D)) i = ((t * D i : ℕ) : ℤ) := by simp [castF_apply]
    rw [h1]
    have : v i ≤ t * D i := by
      calc v i ≤ T := hvT
        _ ≤ t := by omega
        _ ≤ t * D i := by nlinarith
    omega

theorem kFun_two_rayS (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (E : Fin (N + 1) →₀ ℕ) (Q : MvPolynomial (Fin (N + 1)) ℚ) :
    ∀ᶠ t : ℕ in Filter.atTop,
      kFun N (fun _ => 2) Q (castF (t • D - E)) = (rayModelS N D E Q).eval (t : ℚ) := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ, ∀ v ∈ Q.support, ∀ i, v i ≤ T := by
    refine ⟨Q.support.sup (fun (v : Fin (N + 1) →₀ ℕ) =>
      Finset.univ.sup (fun (i : Fin (N + 1)) => v i)), fun v hv i => ?_⟩
    exact le_trans (Finset.le_sup (Finset.mem_univ i))
      (Finset.le_sup (f := fun (v : Fin (N + 1) →₀ ℕ) =>
        Finset.univ.sup (fun (i : Fin (N + 1)) => v i)) hv)
  obtain ⟨T2, hT2⟩ : ∃ T2 : ℕ, ∀ i, E i ≤ T2 :=
    ⟨Finset.univ.sup E, fun i => Finset.le_sup (Finset.mem_univ i)⟩
  refine Filter.eventually_atTop.mpr ⟨T + T2 + 1, fun t ht => ?_⟩
  have hsub : ∀ i, (t • D - E) i = t * D i - E i := by
    intro i
    rw [Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul]
  have hbig : ∀ i, E i ≤ t * D i := by
    intro i
    have hDi : 1 ≤ D i := hD i
    have h1 : T2 ≤ t := by
      have : T + T2 + 1 ≤ t := ht
      omega
    have h2 : E i ≤ T2 := hT2 i
    calc E i ≤ T2 := h2
      _ ≤ t := h1
      _ ≤ t * D i := by nlinarith
  rw [kFun_two_eq]
  · rw [rayModelS_eval]
    refine Finset.sum_congr rfl fun v hv => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : (castF (t • D - E)) i = ((t * D i - E i : ℕ) : ℤ) := by
      simp only [castF_apply, hsub i]
    rw [h1, Nat.cast_sub (hbig i)]
    push_cast
    ring
  · intro v hv i
    have hvT := hT v hv i
    have h1 : (castF (t • D - E)) i = ((t * D i - E i : ℕ) : ℤ) := by
      simp only [castF_apply, hsub i]
    rw [h1]
    have h3 : T ≤ t := by
      have : T + T2 + 1 ≤ t := ht
      omega
    have h6 : v i ≤ t * D i - E i := by
      have h4 : v i ≤ T := hvT
      have h5 : E i ≤ T2 := hT2 i
      have ht' : T + T2 + 1 ≤ t := ht
      have htD : t ≤ t * D i := by
        have hDi : 1 ≤ D i := hD i
        nlinarith
      omega
    have h7 : (v i : ℤ) ≤ ((t * D i - E i : ℕ) : ℤ) := by exact_mod_cast h6
    linarith [h7]



/-! ### Uniqueness of eventual polynomials -/

theorem eq_of_eventually_eval_eq {p q : Polynomial ℚ}
    (h : ∀ᶠ t : ℕ in Filter.atTop, p.eval (t : ℚ) = q.eval (t : ℚ)) : p = q := by
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  have h0 : ∀ᶠ t : ℕ in Filter.atTop, (p - q).IsRoot (t : ℚ) := by
    filter_upwards [h] with t ht
    rw [Polynomial.IsRoot, Polynomial.eval_sub, ht, sub_self]
  obtain ⟨N₀, hN⟩ := Filter.eventually_atTop.mp h0
  have hfin : {x : ℚ | (p - q).IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hsub
  have hinj : Function.Injective (fun t : ℕ => ((t + N₀ : ℕ) : ℚ)) := by
    intro a b hab
    have h1 : ((a : ℚ) + N₀) = ((b : ℚ) + N₀) := by
      have hh := hab
      push_cast at hh
      exact hh
    have h2 : (a : ℚ) = (b : ℚ) := by linarith
    exact_mod_cast h2
  have hinf : {x : ℚ | (p - q).IsRoot x}.Infinite :=
    (Set.infinite_range_of_injective hinj).mono
      (Set.range_subset_iff.mpr fun t => hN _ (by omega))
  exact hinf hfin

/-! ### The three inputs (interface) -/

/-- Hilbert–Serre input: graded pieces of a quotient by a multihomogeneous ideal are given by the
binomial kernel of a single polynomial. (Provided by `Submission.Work.BW.hilb_serre_poly`.) -/
def HilbSerreInput (N : ℕ) : Prop :=
  ∀ (J : Ideal (MR N)), MultiHom N J →
    ∃ Q : MvPolynomial (Fin (N + 1)) ℚ, ∀ u : Fin (N + 1) →₀ ℤ,
      (hilbIdeal N J u : ℚ) = kFun N (fun _ => 2) Q u

/-- Prime series input. (Provided by `Submission.Work.BW.exists_graded_prime_series`.) -/
def PrimeSeriesInput (N : ℕ) : Prop :=
  ∀ (I : Ideal (MR N)), MultiHom N I →
    ∃ (k : ℕ) (P : Fin k → Ideal (MR N)) (E : Fin k → (Fin (N + 1) →₀ ℕ)),
      (∀ j, (P j).IsPrime) ∧ (∀ j, MultiHom N (P j)) ∧ (∀ j, I ≤ P j) ∧
      (∀ u : Fin (N + 1) →₀ ℤ,
        hilbIdeal N I u = ∑ j, hilbIdeal N (P j) (u - castF (E j))) ∧
      (∀ q ∈ I.minimalPrimes,
        (Finset.univ.filter (fun j : Fin k => P j = q)).card = (primLen I q).toNat)

/-- Eventual monotonicity of the ray function of a multihomogeneous prime `p` along the ray
`t • D` (`D ≥ 1`); supplied by `Submission.Work.BW.hilbIdeal_prime_ray_mono`. -/
def RayMonoAt (N : ℕ) (p : Ideal (MR N)) (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i) : Prop :=
  ∀ (E F : Fin (N + 1) →₀ ℕ), ∀ᶠ t : ℕ in Filter.atTop,
    hilbIdeal N p (castF (t • D) - castF E) ≤
      hilbIdeal N p (castF (t • D) - castF E + castF F)

section Main

variable {N : ℕ} (hs : HilbSerreInput N)

/-- The Hilbert–Serre polynomial of a multihomogeneous ideal. -/
noncomputable def hsPoly (J : Ideal (MR N)) (hJ : MultiHom N J) : MvPolynomial (Fin (N + 1)) ℚ :=
  Classical.choose (hs J hJ)

theorem hsPoly_spec (J : Ideal (MR N)) (hJ : MultiHom N J) (u : Fin (N + 1) →₀ ℤ) :
    (hilbIdeal N J u : ℚ) = kFun N (fun _ => 2) (hsPoly hs J hJ) u :=
  Classical.choose_spec (hs J hJ) u

theorem rayHilb_eventually_model (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (J : Ideal (MR N)) (hJ : MultiHom N J) :
    ∀ᶠ t : ℕ in Filter.atTop,
      (rayHilb N D J t : ℚ) = (rayModel N D (hsPoly hs J hJ)).eval (t : ℚ) := by
  filter_upwards [kFun_two_ray N D hD (hsPoly hs J hJ)] with t ht
  rw [rayHilb_eq_hilbIdeal, hsPoly_spec hs J hJ (castF (t • D)), ht]

theorem rayPoly_eq_model (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (J : Ideal (MR N)) (hJ : MultiHom N J) :
    rayPoly N D J = rayModel N D (hsPoly hs J hJ) := by
  have h := rayHilb_eventually_model hs D hD J hJ
  have hex : ∃ q, IsRayPoly N D J q := ⟨_, h⟩
  have hspec : IsRayPoly N D J (rayPoly N D J) := by
    rw [rayPoly, dif_pos hex]
    exact Classical.choose_spec hex
  refine eq_of_eventually_eval_eq ?_
  filter_upwards [hspec, h] with t ht1 ht2
  rw [← ht1, ht2]

end Main

/-- The ray Hilbert polynomial of a multihomogeneous ideal is the eventual polynomial of its ray
Hilbert function. -/
theorem isRayPoly_rayPoly {N : ℕ} (hs : HilbSerreInput N) (D : Fin (N + 1) →₀ ℕ)
    (hD : ∀ i, 1 ≤ D i) (J : Ideal (MR N)) (hJ : MultiHom N J) :
    IsRayPoly N D J (rayPoly N D J) := by
  rw [rayPoly_eq_model hs D hD J hJ]
  exact rayHilb_eventually_model hs D hD J hJ

/-! ### `finsum` over a proposition-indexed family -/

theorem finsum_over_prop {M : Type*} [AddCommMonoid M] {P : Prop} [Decidable P] (g : M) :
    (∑ᶠ (_ : P), g) = if P then g else 0 := by
  classical
  by_cases h : P
  · rw [if_pos h]
    exact finsum_eq_single (fun _ : P => g) h fun x hx => absurd (Subsingleton.elim x h) hx
  · rw [if_neg h]
    haveI : IsEmpty P := ⟨fun hp => h hp⟩
    exact finsum_of_isEmpty _

theorem finsum_cond_eq_sum {α : Type*} {M : Type*} [AddCommMonoid M] (P : α → Prop)
    [DecidablePred P] (S : Finset α) (hS : ∀ a, P a → a ∈ S) (g : α → M) :
    (∑ᶠ (a : α) (_ : P a), g a) = ∑ a ∈ S, (if P a then g a else 0) := by
  classical
  have hsub : Function.support (fun a : α => ∑ᶠ (_ : P a), g a) ⊆ ↑S := by
    intro a ha
    by_contra hna
    have hPa : ¬ P a := fun hpa => hna (hS a hpa)
    simp only [Function.mem_support] at ha
    exact ha (by rw [finsum_over_prop, if_neg hPa])
  rw [finsum_eq_sum_of_support_subset _ hsub]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [finsum_over_prop]

/-! ### Shift invariance of the ray model -/

theorem castF_sub {N : ℕ} (D E : Fin (N + 1) →₀ ℕ) (t : ℕ) (h : ∀ i, E i ≤ (t • D) i) :
    castF (t • D - E) = castF (t • D) - castF E := by
  ext i
  rw [castF_apply, Finsupp.tsub_apply, Finsupp.sub_apply, castF_apply, castF_apply,
    Nat.cast_sub (h i)]

theorem model_shift_degree {N : ℕ} (hs : HilbSerreInput N)
    (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    {p : Ideal (MR N)} (hpm : MultiHom N p) (hm : RayMonoAt N p D hD)
    (E : Fin (N + 1) →₀ ℕ) :
    (rayModelS N D E (hsPoly hs p hpm)).natDegree = (rayModel N D (hsPoly hs p hpm)).natDegree ∧
    (rayModelS N D E (hsPoly hs p hpm)).leadingCoeff =
      (rayModel N D (hsPoly hs p hpm)).leadingCoeff := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ i, E i ≤ k * D i := by
    refine ⟨∑ i, E i, fun i => ?_⟩
    have h1 : E i ≤ ∑ j, E j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : (∑ j, E j) * 1 ≤ (∑ j, E j) * D i := Nat.mul_le_mul_left _ (hD i)
    rw [Nat.mul_one] at h2
    exact le_trans h1 h2
  refine sandwich_poly (p := rayModelS N D E (hsPoly hs p hpm))
    (q := rayModel N D (hsPoly hs p hpm)) (k := k) ?_ ?_ ?_
  · filter_upwards [kFun_two_rayS N D hD E (hsPoly hs p hpm)] with t ht
    rw [← ht, ← hsPoly_spec hs p hpm (castF (t • D - E))]
    positivity
  · have hsub : ∀ᶠ t : ℕ in Filter.atTop,
        castF (t • D - E) = castF (t • D) - castF E :=
      Filter.eventually_atTop.mpr ⟨k, fun t ht => castF_sub D E t (fun i => by
        have h1 : E i ≤ k * D i := hk i
        have h2 : k * D i ≤ t * D i := Nat.mul_le_mul_right _ ht
        have h3 : (t • D) i = t * D i := by simp [Finsupp.smul_apply, smul_eq_mul]
        rw [h3]; exact le_trans h1 h2)⟩
    have hee : ∀ᶠ t : ℕ in Filter.atTop,
        castF (t • D) - castF E + castF E = castF (t • D) := by
      filter_upwards with t
      ext i
      simp only [Finsupp.add_apply, Finsupp.sub_apply]
      ring
    filter_upwards [kFun_two_rayS N D hD E (hsPoly hs p hpm),
      kFun_two_ray N D hD (hsPoly hs p hpm), hsub, hee, hm E E] with t h1t h2t hsub' hee' hmono
    rw [← h1t, ← h2t, hsub', ← hsPoly_spec hs p hpm (castF (t • D) - castF E),
      ← hsPoly_spec hs p hpm (castF (t • D))]
    rw [hee'] at hmono
    exact Nat.cast_le.mpr hmono
  · have h2shift : ∀ᶠ t : ℕ in Filter.atTop,
        kFun N (fun _ => 2) (hsPoly hs p hpm) (castF ((t + k) • D - E))
          = (rayModelS N D E (hsPoly hs p hpm)).eval ((t + k : ℕ) : ℚ) := by
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (kFun_two_rayS N D hD E (hsPoly hs p hpm))
      exact Filter.eventually_atTop.mpr ⟨M, fun t ht => hM (t + k) (by omega)⟩
    have hkey : ∀ᶠ t : ℕ in Filter.atTop,
        castF (t • D) + castF (k • D - E) = castF ((t + k) • D - E) := by
      filter_upwards with t
      rw [← castF_add]
      congr 1
      ext i
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul]
      have h1 : E i ≤ k * D i := hk i
      rw [Nat.add_mul]
      omega
    filter_upwards [kFun_two_ray N D hD (hsPoly hs p hpm), h2shift, hm 0 (k • D - E), hkey]
      with t h1t h2t hmono hkey'
    rw [← h1t, ← h2t, ← hsPoly_spec hs p hpm (castF (t • D)),
      ← hsPoly_spec hs p hpm (castF ((t + k) • D - E))]
    rw [castF_zero, sub_zero] at hmono
    rw [hkey'] at hmono
    exact Nat.cast_le.mpr hmono

/-! ### The filtration identity for the ray Hilbert polynomial -/

theorem rayPoly_eq_sum_series {N : ℕ} (hs : HilbSerreInput N) (D : Fin (N + 1) →₀ ℕ)
    (hD : ∀ i, 1 ≤ D i) (I : Ideal (MR N)) (hI : MultiHom N I)
    (k : ℕ) (P : Fin k → Ideal (MR N)) (E : Fin k → (Fin (N + 1) →₀ ℕ))
    (hPmh : ∀ j, MultiHom N (P j))
    (hvect : ∀ u : Fin (N + 1) →₀ ℤ,
      hilbIdeal N I u = ∑ j, hilbIdeal N (P j) (u - castF (E j))) :
    rayPoly N D I = ∑ j, rayModelS N D (E j) (hsPoly hs (P j) (hPmh j)) := by
  rw [rayPoly_eq_model hs D hD I hI]
  refine eq_of_eventually_eval_eq ?_
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ j i, E j i ≤ K * D i := by
    refine ⟨∑ j, ∑ i, E j i, fun j i => ?_⟩
    have h1 : E j i ≤ ∑ i, E j i :=
      Finset.single_le_sum (s := Finset.univ) (f := E j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : ∑ i, E j i ≤ ∑ j, ∑ i, E j i :=
      Finset.single_le_sum (s := Finset.univ) (f := fun j => ∑ i, E j i)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h3 : 1 ≤ D i := hD i
    have h4 : (∑ j, ∑ i, E j i) * 1 ≤ (∑ j, ∑ i, E j i) * D i := Nat.mul_le_mul_left _ h3
    rw [Nat.mul_one] at h4
    exact le_trans (le_trans h1 h2) h4
  have hcast : ∀ᶠ t : ℕ in Filter.atTop, ∀ j,
      castF (t • D) - castF (E j) = castF (t • D - E j) := by
    filter_upwards [Filter.eventually_ge_atTop K] with t ht
    intro j
    exact (castF_sub D (E j) t (fun i => by
      have h1 : E j i ≤ K * D i := hK j i
      have h2 : K * D i ≤ t * D i := Nat.mul_le_mul_right _ ht
      have h3 : (t • D) i = t * D i := by simp [Finsupp.smul_apply, smul_eq_mul]
      rw [h3]; exact le_trans h1 h2)).symm
  have hS : ∀ᶠ t : ℕ in Filter.atTop, ∀ j,
      kFun N (fun _ => 2) (hsPoly hs (P j) (hPmh j)) (castF (t • D - E j))
        = (rayModelS N D (E j) (hsPoly hs (P j) (hPmh j))).eval (t : ℚ) := by
    rw [Filter.eventually_all]
    intro j
    exact kFun_two_rayS N D hD (E j) (hsPoly hs (P j) (hPmh j))
  filter_upwards [rayHilb_eventually_model hs D hD I hI, hcast, hS] with t hpoly hcast' hS'
  rw [← hpoly, rayHilb_eq_hilbIdeal, hvect (castF (t • D))]
  push_cast
  rw [Polynomial.eval_finsetSum Finset.univ
    (fun j => rayModelS N D (E j) (hsPoly hs (P j) (hPmh j))) (t : ℚ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcast' j, hsPoly_spec hs (P j) (hPmh j) (castF (t • D - E j)), hS' j]

/-! ### `rayDim` is antitone in the ideal -/

theorem rayDim_le_of_le {N : ℕ} (hs : HilbSerreInput N) (D : Fin (N + 1) →₀ ℕ)
    (hD : ∀ i, 1 ≤ D i) {I J : Ideal (MR N)} (hI : MultiHom N I) (hJ : MultiHom N J)
    (h : I ≤ J) : rayDim N D J ≤ rayDim N D I := by
  have hJ' : ∀ᶠ t : ℕ in Filter.atTop,
      ((rayHilb N D J t : ℕ) : ℚ) = (rayPoly N D J).eval (t : ℚ) :=
    isRayPoly_rayPoly hs D hD J hJ
  have hI' : ∀ᶠ t : ℕ in Filter.atTop,
      ((rayHilb N D I t : ℕ) : ℚ) = (rayPoly N D I).eval (t : ℚ) :=
    isRayPoly_rayPoly hs D hD I hI
  have h1 : ∀ᶠ t : ℕ in Filter.atTop,
      (rayPoly N D J).eval (t : ℚ) ≤ (rayPoly N D I).eval (t : ℚ) := by
    filter_upwards [hJ', hI'] with t htJ htI
    rw [← htJ, ← htI, rayHilb_eq_hilbIdeal, rayHilb_eq_hilbIdeal]
    exact Nat.cast_le.mpr (hilbIdeal_anti N h (castF (t • D)))
  have h2 : ∀ᶠ t : ℕ in Filter.atTop, 0 ≤ (rayPoly N D J).eval (t : ℚ) := by
    filter_upwards [hJ'] with t ht
    rw [← ht]
    exact Nat.cast_nonneg _
  have := poly_natDegree_eventually_le h1 h2
  simpa only [rayDim] using this

/-! ### Finset bookkeeping -/

theorem sum_comp_eq_sum_image {α β : Type*} {M : Type*} [AddCommMonoid M] [DecidableEq β]
    (s : Finset α) (g : α → β) (f : β → M) :
    ∑ a ∈ s, f (g a) = ∑ b ∈ s.image g, (s.filter (fun a => g a = b)).card • f b := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := s.image g)
    (fun a ha => Finset.mem_image_of_mem g ha) (f := fun a => f (g a))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∑ a ∈ s.filter (fun a => g a = b), f (g a)
      = ∑ a ∈ s.filter (fun a => g a = b), f b :=
    Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2]
  rw [h1, Finset.sum_const]

/-! ### Non-minimal primes contribute nothing in the top degree -/

theorem rayPoly_eq_zero_or_rayDim_lt_of_not_minimal {N : ℕ} (hs : HilbSerreInput N)
    (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i) {I p : Ideal (MR N)} (hI : MultiHom N I)
    (hp : p.IsPrime) (hpm : MultiHom N p) (hIp : I ≤ p) (hnotmin : p ∉ I.minimalPrimes) :
    rayPoly N D p = 0 ∨ rayDim N D p < rayDim N D I := by
  classical
  haveI : p.IsPrime := hp
  obtain ⟨q, hqmem, hqp⟩ := Ideal.exists_minimalPrimes_le hIp
  have hql : q < p := lt_of_le_of_ne hqp (fun h => hnotmin (h ▸ hqmem))
  have hqprime : q.IsPrime := Ideal.IsMinimalPrime.isPrime hqmem
  have hqmh : MultiHom N q := by
    have hann : Module.annihilator (MR N) (MR N ⧸ I) = I := Ideal.annihilator_quotient
    have hqmem' : q ∈ (Module.annihilator (MR N) (MR N ⧸ I)).minimalPrimes := by
      rw [hann]
      exact hqmem
    exact multiHom_assPrime I hI q
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
        (MR N) (MR N ⧸ I) hqmem')
  rcases rayPoly_prime_drop D hD q p hqprime hp hqmh hpm hql (rayPoly N D q)
      (isRayPoly_rayPoly hs D hD q hqmh) with h0 | hlt
  · exact Or.inl h0
  · exact Or.inr (lt_of_lt_of_le hlt (rayDim_le_of_le hs D hD hI hqmh (Ideal.IsMinimalPrime.le hqmem)))

/-! ### The leading coefficient of the ray Hilbert polynomial, additively over the series -/

theorem leadingCoeff_rayPoly_eq {N : ℕ} (hs : HilbSerreInput N) (D : Fin (N + 1) →₀ ℕ)
    (hD : ∀ i, 1 ≤ D i) (I : Ideal (MR N)) (hI : MultiHom N I)
    (k : ℕ) (P : Fin k → Ideal (MR N)) (E : Fin k → (Fin (N + 1) →₀ ℕ))
    (hPprime : ∀ j, (P j).IsPrime) (hPmh : ∀ j, MultiHom N (P j)) (hIP : ∀ j, I ≤ P j)
    (hvect : ∀ u : Fin (N + 1) →₀ ℤ,
      hilbIdeal N I u = ∑ j, hilbIdeal N (P j) (u - castF (E j)))
    (hmono : ∀ j, RayMonoAt N (P j) D hD)
    (S : Finset (Ideal (MR N))) (hS : ∀ p, p ∈ S ↔ p ∈ I.minimalPrimes)
    (hcount : ∀ p ∈ I.minimalPrimes,
      (Finset.univ.filter (fun j : Fin k => P j = p)).card = (primLen I p).toNat) :
    (rayPoly N D I).leadingCoeff =
      ∑ p ∈ S, (if rayDim N D p = rayDim N D I then ((primLen I p).toNat : ℚ) *
        (rayPoly N D p).leadingCoeff else 0) := by
  classical
  have hshift : ∀ j, (rayModelS N D (E j) (hsPoly hs (P j) (hPmh j))).natDegree =
        (rayModel N D (hsPoly hs (P j) (hPmh j))).natDegree ∧
      (rayModelS N D (E j) (hsPoly hs (P j) (hPmh j))).leadingCoeff =
        (rayModel N D (hsPoly hs (P j) (hPmh j))).leadingCoeff :=
    fun j => model_shift_degree hs D hD (hPmh j) (hmono j) (E j)
  have hgd : ∀ j, (rayPoly N D (P j)).natDegree =
      (rayModel N D (hsPoly hs (P j) (hPmh j))).natDegree := by
    intro j
    rw [rayPoly_eq_model hs D hD (P j) (hPmh j)]
  have hle : ∀ j, rayDim N D (P j) ≤ rayDim N D I :=
    fun j => rayDim_le_of_le hs D hD hI (hPmh j) (hIP j)
  have hcoeff : (rayPoly N D I).leadingCoeff =
      ∑ j, (if rayDim N D (P j) = rayDim N D I then (rayPoly N D (P j)).leadingCoeff
        else 0) := by
    have hnat : (rayPoly N D I).natDegree = rayDim N D I := rfl
    rw [show (rayPoly N D I).leadingCoeff = (rayPoly N D I).coeff (rayDim N D I) from by
      rw [← Polynomial.coeff_natDegree, hnat]]
    rw [rayPoly_eq_sum_series hs D hD I hI k P E hPmh hvect, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hdj : rayDim N D (P j) = rayDim N D I
    · rw [if_pos hdj]
      have h2 : (rayModelS N D (E j) (hsPoly hs (P j) (hPmh j))).coeff (rayDim N D I) =
          (rayModelS N D (E j) (hsPoly hs (P j) (hPmh j))).leadingCoeff := by
        rw [← Polynomial.coeff_natDegree]
        congr 1
        rw [(hshift j).1, ← hgd j]
        exact hdj.symm
      rw [h2, (hshift j).2, ← rayPoly_eq_model hs D hD (P j) (hPmh j)]
    · rw [if_neg hdj]
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [(hshift j).1, ← hgd j]
      exact lt_of_le_of_ne (hle j) hdj
  have hgroup : ∑ j, (if rayDim N D (P j) = rayDim N D I then (rayPoly N D (P j)).leadingCoeff
        else 0)
      = ∑ p ∈ Finset.univ.image P,
          (Finset.univ.filter (fun j : Fin k => P j = p)).card •
            (if rayDim N D p = rayDim N D I then (rayPoly N D p).leadingCoeff else 0) :=
    sum_comp_eq_sum_image Finset.univ P
      (fun p => if rayDim N D p = rayDim N D I then (rayPoly N D p).leadingCoeff else 0)
  have hkill : ∑ p ∈ Finset.univ.image P,
        (Finset.univ.filter (fun j : Fin k => P j = p)).card •
          (if rayDim N D p = rayDim N D I then (rayPoly N D p).leadingCoeff else 0)
      = ∑ p ∈ Finset.univ.image P ∩ S,
          ((primLen I p).toNat : ℚ) *
            (if rayDim N D p = rayDim N D I then (rayPoly N D p).leadingCoeff else 0) := by
    refine (Finset.sum_subset (s₁ := Finset.univ.image P ∩ S) (s₂ := Finset.univ.image P)
      Finset.inter_subset_left ?_).symm.trans ?_
    · intro p hpH hpNot
      have hpNotS : p ∉ S := fun hpS => hpNot (Finset.mem_inter.mpr ⟨hpH, hpS⟩)
      have hnotmin : p ∉ I.minimalPrimes := fun hmin => hpNotS ((hS p).mpr hmin)
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpH
      have hpprime : p.IsPrime := hj ▸ hPprime j
      have hpmh : MultiHom N p := hj ▸ hPmh j
      have hIp : I ≤ p := hj ▸ hIP j
      have hψ : (if rayDim N D p = rayDim N D I then (rayPoly N D p).leadingCoeff else 0) = 0 := by
        rcases rayPoly_eq_zero_or_rayDim_lt_of_not_minimal hs D hD hI hpprime hpmh hIp hnotmin
          with h0 | hlt
        · by_cases hd : rayDim N D p = rayDim N D I
          · rw [if_pos hd]
            exact Polynomial.leadingCoeff_eq_zero.mpr h0
          · rw [if_neg hd]
        · rw [if_neg (ne_of_lt hlt)]
      rw [hψ, smul_zero]
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hpMin : p ∈ I.minimalPrimes := (hS p).mp (Finset.mem_inter.mp hp).2
      rw [nsmul_eq_mul, hcount p hpMin]
  have hpass : ∑ p ∈ Finset.univ.image P ∩ S,
        ((primLen I p).toNat : ℚ) *
          (if rayDim N D p = rayDim N D I then (rayPoly N D p).leadingCoeff else 0)
      = ∑ p ∈ S, (if rayDim N D p = rayDim N D I then ((primLen I p).toNat : ℚ) *
          (rayPoly N D p).leadingCoeff else 0) := by
    have h1 : ∑ p ∈ Finset.univ.image P ∩ S,
          ((primLen I p).toNat : ℚ) *
            (if rayDim N D p = rayDim N D I then (rayPoly N D p).leadingCoeff else 0)
        = ∑ p ∈ Finset.univ.image P ∩ S,
            (if rayDim N D p = rayDim N D I then ((primLen I p).toNat : ℚ) *
              (rayPoly N D p).leadingCoeff else 0) :=
      Finset.sum_congr rfl fun p _ => by
        by_cases hd : rayDim N D p = rayDim N D I
        · rw [if_pos hd, if_pos hd]
        · rw [if_neg hd, if_neg hd, mul_zero]
    rw [h1]
    refine Finset.sum_subset (s₁ := Finset.univ.image P ∩ S) (s₂ := S)
      Finset.inter_subset_right ?_
    intro p hpS hpNot
    have hpMin : p ∈ I.minimalPrimes := (hS p).mp hpS
    have hnotH : p ∉ Finset.univ.image P := fun hH =>
      hpNot (Finset.mem_inter.mpr ⟨hH, hpS⟩)
    have hzf : (Finset.univ.filter (fun j : Fin k => P j = p)).card = 0 := by
      rw [Finset.card_eq_zero]
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun hjp => hnotH (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hjp⟩)
    have hpz : (primLen I p).toNat = 0 := by
      rw [← hcount p hpMin, hzf]
    by_cases hd : rayDim N D p = rayDim N D I
    · rw [if_pos hd, hpz]
      simp
    · rw [if_neg hd]
  rw [hcoeff, hgroup, hkill, hpass]


/-! ### Ray monotonicity (self-contained; the module `hilbIdeal_prime_ray_mono` clashes with
`quotient_isGrading`, so this proof is inlined here) -/

namespace RayMonoAux

theorem wZ_apply (v : Fin (N + 1) × Fin 2) (i : Fin (N + 1)) :
    (wZ N v : Fin (N + 1) →₀ ℤ) i = if v.1 = i then 1 else 0 := by
  rw [wZ, Finsupp.single_apply]

theorem weight_wZ_apply (m : Fin (N + 1) × Fin 2 →₀ ℕ) (i : Fin (N + 1)) :
    Finsupp.weight (wZ N) m i
      = ∑ v ∈ Finset.univ.filter (fun v : Fin (N + 1) × Fin 2 => v.1 = i), (m v : ℤ) := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply']
  simp only [Finsupp.smul_apply, wZ_apply, nsmul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]

theorem exists_pos_of_weight_pos {m : Fin (N + 1) × Fin 2 →₀ ℕ} {i : Fin (N + 1)}
    (h : 0 < Finsupp.weight (wZ N) m i) : ∃ j : Fin 2, 0 < m (i, j) := by
  classical
  by_contra hc
  push_neg at hc
  have h0 : Finsupp.weight (wZ N) m i = 0 := by
    rw [weight_wZ_apply]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [Finset.mem_filter] at hv
    have hv' : v = (i, v.2) := by ext <;> simp [hv.2]
    have h1 : m (i, v.2) = 0 := by have := hc v.2; omega
    rw [hv', h1, Nat.cast_zero]
  omega

theorem pieceZ_le_of_both_X_mem {I : Ideal (MR N)} {i : Fin (N + 1)}
    (h0 : MvPolynomial.X (i, 0) ∈ I) (h1 : MvPolynomial.X (i, 1) ∈ I)
    {u : Fin (N + 1) →₀ ℤ} (hu : 1 ≤ u i) : pieceZ N u ≤ I.restrictScalars ℂ := by
  have hspan : pieceZ N u = Submodule.span ℂ
      ((fun x => MvPolynomial.monomial x (1 : ℂ)) ''
        {d : Fin (N + 1) × Fin 2 →₀ ℕ | Finsupp.weight (wZ N) d = u}) := by
    rw [pieceZ, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
    exact MvPolynomial.restrictSupport_eq_span ℂ _
  rw [hspan, Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  rw [Set.mem_setOf_eq] at hm
  have hpos : 0 < Finsupp.weight (wZ N) m i := by rw [hm]; omega
  obtain ⟨j, hj⟩ := exists_pos_of_weight_pos hpos
  have hX : MvPolynomial.X (i, j) ∈ I := by
    fin_cases j
    · exact h0
    · exact h1
  have hdvd : MvPolynomial.X (i, j) ∣ MvPolynomial.monomial m (1 : ℂ) :=
    MvPolynomial.X_dvd_monomial.mpr (Or.inr (ne_of_gt hj))
  obtain ⟨c, hc⟩ := hdvd
  change MvPolynomial.monomial m (1 : ℂ) ∈ I
  rw [hc]
  exact Ideal.mul_mem_right c I hX

theorem hilbIdeal_eq_sub (p : Ideal (MR N)) (u : Fin (N + 1) →₀ ℤ) :
    hilbIdeal N p u = Module.finrank ℂ ↥(pieceZ N u) -
      Module.finrank ℂ ↥(Submodule.comap (pieceZ N u).subtype (p.restrictScalars ℂ)) := by
  haveI := moduleFinite_pieceZ N u
  unfold hilbIdeal
  have h := Submodule.finrank_quotient_add_finrank
    (Submodule.comap (pieceZ N u).subtype (p.restrictScalars ℂ))
  omega

theorem hilbIdeal_le_add {p : Ideal (MR N)} (hp : p.IsPrime)
    (hW : ∀ i : Fin (N + 1), ¬ (MvPolynomial.X (i, 0) ∈ p ∧ MvPolynomial.X (i, 1) ∈ p))
    (u : Fin (N + 1) →₀ ℤ) (F : Fin (N + 1) →₀ ℕ) :
    hilbIdeal N p u ≤ hilbIdeal N p (u + castF F) := by
  classical
  have hchoice : ∀ i : Fin (N + 1), ∃ j : Fin 2, MvPolynomial.X (i, j) ∉ p := by
    intro i
    by_contra hc
    push_neg at hc
    exact hW i ⟨hc 0, hc 1⟩
  choose c hc using hchoice
  set m : MR N := ∏ i : Fin (N + 1), (MvPolynomial.X (i, c i)) ^ (F i) with hmdef
  have hm_notp : m ∉ p := by
    rw [hmdef]
    refine Finset.prod_induction _ (fun x : MR N => x ∉ p) ?_ ?_ ?_
    · intro a b ha hb hab
      exact (hp.mem_or_mem hab).elim ha hb
    · intro h1
      exact (Ideal.ne_top_iff_one p).mp hp.ne_top h1
    · intro i _
      exact fun hpow => hc i (hp.mem_of_pow_mem _ hpow)
  have hm_ne : m ≠ 0 := fun h => hm_notp (h ▸ p.zero_mem)
  have hm_hom : MvPolynomial.IsWeightedHomogeneous (wZ N) m (castF F) := by
    rw [hmdef]
    have h := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
      (fun i : Fin (N + 1) => (MvPolynomial.X (i, c i)) ^ (F i))
      (fun i => (F i) • wZ N (i, c i))
      (fun i _ => (MvPolynomial.isWeightedHomogeneous_X ℂ (wZ N) (i, c i)).pow (F i))
    have hsum : (∑ i : Fin (N + 1), (F i) • wZ N (i, c i)) = castF F := by
      ext j
      rw [Finset.sum_apply']
      simp only [Finsupp.smul_apply, wZ_apply, nsmul_eq_mul, mul_ite, mul_one, mul_zero,
        castF_apply]
      simp
    rwa [hsum] at h
  have hm_piece : m ∈ pieceZ N (castF F) := by
    rw [mem_pieceZ]
    exact hm_hom
  have hmem1 : ∀ x ∈ pieceZ N u, m * x ∈ pieceZ N (u + castF F) := by
    intro x hx
    rw [mem_pieceZ] at hx ⊢
    have h4 := MvPolynomial.IsWeightedHomogeneous.mul hm_hom hx
    convert h4 using 1
    exact add_comm _ _
  let φ : ↥(pieceZ N u) →ₗ[ℂ] ↥(pieceZ N (u + castF F)) :=
    { toFun := fun x => ⟨m * (x : MR N), hmem1 x x.2⟩
      map_add' := fun x y => by ext; simp [mul_add]
      map_smul' := fun r x => by ext; simp [mul_left_comm] }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : m * (x : MR N) = m * (y : MR N) := by
      have := congrArg (fun z : ↥(pieceZ N (u + castF F)) => (z : MR N)) hxy
      simpa [φ] using this
    exact Subtype.ext (mul_left_cancel₀ hm_ne h1)
  have hle1 : Module.finrank ℂ ↥(pieceZ N u) ≤
      Module.finrank ℂ ↥(pieceZ N (u + castF F)) := by
    haveI : Module.Finite ℂ ↥(pieceZ N (u + castF F)) := moduleFinite_pieceZ N _
    exact LinearMap.finrank_le_finrank_of_injective hφinj
  have hkernel : Submodule.comap φ (Submodule.comap (pieceZ N (u + castF F)).subtype
      (p.restrictScalars ℂ)) =
      Submodule.comap (pieceZ N u).subtype (p.restrictScalars ℂ) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hxm : m * (x : MR N) ∈ p := hx
      rcases hp.mem_or_mem hxm with h | h
      · exact absurd h hm_notp
      · exact h
    · intro x hx
      change ((φ x : ↥(pieceZ N (u + castF F))) : MR N) ∈ p
      rw [show ((φ x : ↥(pieceZ N (u + castF F))) : MR N) = m * (x : MR N) from rfl]
      exact Ideal.mul_mem_left p m hx
  have hle : Submodule.comap (pieceZ N u).subtype (p.restrictScalars ℂ) ≤
      Submodule.comap φ (Submodule.comap (pieceZ N (u + castF F)).subtype
        (p.restrictScalars ℂ)) := le_of_eq hkernel.symm
  have hker : LinearMap.ker (Submodule.mapQ
      (Submodule.comap (pieceZ N u).subtype (p.restrictScalars ℂ))
      (Submodule.comap (pieceZ N (u + castF F)).subtype (p.restrictScalars ℂ)) φ hle) = ⊥ := by
    rw [Submodule.ker_mapQ, hkernel]
    refine le_antisymm ?_ bot_le
    rintro x ⟨y, hy, rfl⟩
    show (Submodule.mkQ (Submodule.comap (pieceZ N u).subtype (p.restrictScalars ℂ))) y = 0
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact hy
  have hinj : Function.Injective (Submodule.mapQ
      (Submodule.comap (pieceZ N u).subtype (p.restrictScalars ℂ))
      (Submodule.comap (pieceZ N (u + castF F)).subtype (p.restrictScalars ℂ)) φ hle) :=
    LinearMap.ker_eq_bot.mp hker
  haveI : Module.Finite ℂ ↥(pieceZ N (u + castF F)) := moduleFinite_pieceZ N _
  haveI : Module.Finite ℂ (↥(pieceZ N (u + castF F)) ⧸
      Submodule.comap (pieceZ N (u + castF F)).subtype (p.restrictScalars ℂ)) :=
    Module.Finite.quotient ℂ _
  exact LinearMap.finrank_le_finrank_of_injective hinj


theorem hilbIdeal_eq_zero_of_pos {p : Ideal (MR N)} {i : Fin (N + 1)}
    (h0 : MvPolynomial.X (i, 0) ∈ p) (h1 : MvPolynomial.X (i, 1) ∈ p)
    {u : Fin (N + 1) →₀ ℤ} (hu : 1 ≤ u i) : hilbIdeal N p u = 0 := by
  haveI := moduleFinite_pieceZ N u
  unfold hilbIdeal
  have hle := pieceZ_le_of_both_X_mem (I := p) h0 h1 hu
  have htop : Submodule.comap (pieceZ N u).subtype (p.restrictScalars ℂ) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact hle x.2
  rw [htop]
  haveI : Module.Finite ℂ (↥(pieceZ N u) ⧸ (⊤ : Submodule ℂ ↥(pieceZ N u))) :=
    Module.Finite.quotient ℂ _
  haveI : Subsingleton (↥(pieceZ N u) ⧸ (⊤ : Submodule ℂ ↥(pieceZ N u))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

theorem hilbIdeal_prime_ray_mono_self (p : Ideal (MR N)) (hp : p.IsPrime) (hpH : MultiHom N p)
    (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i) (E F : Fin (N + 1) →₀ ℕ) :
    ∀ᶠ t : ℕ in Filter.atTop,
      hilbIdeal N p (castF (t • D) - castF E) ≤
        hilbIdeal N p (castF (t • D) - castF E + castF F) := by
  classical
  by_cases hW : ∃ i : Fin (N + 1), MvPolynomial.X (i, 0) ∈ p ∧ MvPolynomial.X (i, 1) ∈ p
  · obtain ⟨i₀, hX0, hX1⟩ := hW
    refine Filter.eventually_atTop.mpr ⟨E i₀ + 1, fun t ht => ?_⟩
    have hDi : 1 ≤ D i₀ := hD i₀
    have hlt : E i₀ < t * D i₀ := by
      have h1 : t ≤ t * D i₀ := Nat.le_mul_of_pos_right t (by omega)
      omega
    have hu1 : 1 ≤ (castF (t • D) - castF E) i₀ := by
      rw [Finsupp.sub_apply, castF_apply, castF_apply, Finsupp.smul_apply, smul_eq_mul]
      have h2 : ((E i₀ : ℕ) : ℤ) < ((t * D i₀ : ℕ) : ℤ) := by exact_mod_cast hlt
      omega
    have hu2 : 1 ≤ (castF (t • D) - castF E + castF F) i₀ := by
      rw [Finsupp.add_apply]
      have h3 : 0 ≤ (castF F) i₀ := Int.natCast_nonneg _
      omega
    rw [hilbIdeal_eq_zero_of_pos hX0 hX1 hu1, hilbIdeal_eq_zero_of_pos hX0 hX1 hu2]
  · push_neg at hW
    exact Filter.Eventually.of_forall fun t => hilbIdeal_le_add hp (fun i h => hW i h.1 h.2) _ _


end RayMonoAux

/-! ### Block A3b (Philippon 1986, 3.2) -/

theorem rayDeg_additive {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I : Ideal (MR N)) (hI : MultiHom N I) (hne : rayPoly N D I ≠ 0) :
    rayDeg N D I =
      ∑ᶠ (p : Ideal (MR N)) (_ : p ∈ I.minimalPrimes ∧ rayPoly N D p ≠ 0 ∧
          rayDim N D p = rayDim N D I),
        ((primLen I p).toNat : ℚ) * rayDeg N D p := by
  classical
  have hs : HilbSerreInput N := hilb_serre_input N
  obtain ⟨k, P, E, hPprime, hPmh, hIP, hvect, hcount⟩ := exists_graded_prime_series N I hI
  have hmono : ∀ j, RayMonoAt N (P j) D hD :=
    fun j E' F => RayMonoAux.hilbIdeal_prime_ray_mono_self (P j) (hPprime j) (hPmh j) D hD E' F
  obtain ⟨S, hS⟩ : ∃ S : Finset (Ideal (MR N)), (∀ p, p ∈ S ↔ p ∈ I.minimalPrimes) :=
    ⟨(Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) I).toFinset,
      fun _ => Set.Finite.mem_toFinset
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) I)⟩
  have hlc := leadingCoeff_rayPoly_eq hs D hD I hI k P E hPprime hPmh hIP hvect hmono S hS hcount
  have hfinsum : (∑ᶠ (p : Ideal (MR N))
        (_ : p ∈ I.minimalPrimes ∧ rayPoly N D p ≠ 0 ∧ rayDim N D p = rayDim N D I),
        ((primLen I p).toNat : ℚ) * rayDeg N D p)
      = ∑ p ∈ S, (if (p ∈ I.minimalPrimes ∧ rayPoly N D p ≠ 0 ∧ rayDim N D p = rayDim N D I)
          then ((primLen I p).toNat : ℚ) * rayDeg N D p else 0) :=
    finsum_cond_eq_sum (fun p : Ideal (MR N) =>
        p ∈ I.minimalPrimes ∧ rayPoly N D p ≠ 0 ∧ rayDim N D p = rayDim N D I)
      S (fun p hp => (hS p).mpr hp.1) (fun p => ((primLen I p).toNat : ℚ) * rayDeg N D p)
  have key : ∑ p ∈ S, (if (p ∈ I.minimalPrimes ∧ rayPoly N D p ≠ 0 ∧ rayDim N D p = rayDim N D I)
        then ((primLen I p).toNat : ℚ) * rayDeg N D p else 0)
      = ((rayDim N D I).factorial : ℚ) * ∑ p ∈ S,
          (if rayDim N D p = rayDim N D I then ((primLen I p).toNat : ℚ) *
            (rayPoly N D p).leadingCoeff else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpMin : p ∈ I.minimalPrimes := (hS p).mp hp
    by_cases hd : rayDim N D p = rayDim N D I
    · by_cases hp0 : rayPoly N D p = 0
      · rw [if_neg (by simp [hp0]), if_pos hd, Polynomial.leadingCoeff_eq_zero.mpr hp0]
        ring
      · rw [if_pos ⟨hpMin, hp0, hd⟩, if_pos hd]
        simp only [rayDeg, rayDim]
        rw [show (rayPoly N D p).natDegree = (rayPoly N D I).natDegree from hd]
        ring
    · rw [if_neg (by simp [hd]), if_neg hd, mul_zero]
  calc rayDeg N D I
      = ((rayDim N D I).factorial : ℚ) * (rayPoly N D I).leadingCoeff := rfl
    _ = ((rayDim N D I).factorial : ℚ) * ∑ p ∈ S,
          (if rayDim N D p = rayDim N D I then ((primLen I p).toNat : ℚ) *
            (rayPoly N D p).leadingCoeff else 0) := by rw [hlc]
    _ = ∑ p ∈ S, (if (p ∈ I.minimalPrimes ∧ rayPoly N D p ≠ 0 ∧ rayDim N D p = rayDim N D I)
          then ((primLen I p).toNat : ℚ) * rayDeg N D p else 0) := key.symm
    _ = ∑ᶠ (p : Ideal (MR N)) (_ : p ∈ I.minimalPrimes ∧ rayPoly N D p ≠ 0 ∧
          rayDim N D p = rayDim N D I),
        ((primLen I p).toNat : ℚ) * rayDeg N D p := hfinsum.symm

end Work.BW
