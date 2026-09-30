import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.RB.graded_hilbert
import Submission.Work.BW.GradedHilbDefs
import Submission.Work.BW.HilbSerreDefs
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive, multiplicity block). Your node is `rayDeg_mono`. The design is below: find your node in the §2.3 or §3 tables for its content, its dependencies and its size.
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

/-! ## Auxiliary lemmas for `rayDeg_mono` (block A3d)

The proof of `rayDeg_mono` has three ingredients:

* `rayHilb` is antitone in the ideal (`rayHilb_mono`): the quotient of the degree-`tD` piece by
  `I` surjects onto the quotient by `J` when `I ≤ J`;
* if two polynomials of the **same** `natDegree` satisfy `p(n) ≤ q(n)` for all large naturals `n`,
  then `p.leadingCoeff ≤ q.leadingCoeff` (`leadingCoeff_le_of_eventually_le`);
* the eventual polynomial representing `rayHilb N D I` exists (block A2).  For `J` the existence is
  *derived* from the hypothesis `rayPoly N D J ≠ 0`, which forces the `if` in the definition of
  `rayPoly` to take the positive branch. -/

/-- The multihomogeneous piece `homPiece N d` is finite-dimensional: it is contained in the
(total-)homogeneous piece of degree `∑ i, d i`, which is spanned by finitely many monomials. -/
private theorem homPiece_finite (N : ℕ) (d : Fin (N + 1) →₀ ℕ) :
    Module.Finite ℂ ↥(homPiece N d) := by
  rw [Module.Finite.iff_fg]
  refine Submodule.FG.of_le
    (MvPolynomial.homogeneousSubmodule_fg (Fin (N + 1) × Fin 2) ℂ (∑ i, d i)) ?_
  intro p hp
  rw [MvPolynomial.mem_homogeneousSubmodule, MvPolynomial.IsHomogeneous]
  intro a ha
  -- `Finsupp.weight (mdeg N) a = d → Finsupp.degree a = ∑ i, d i`
  have hkey : (Finsupp.degree a : ℕ) = ∑ i, Finsupp.weight (mdeg N) a i := by
    have h : (Finsupp.degree (Finsupp.weight (mdeg N) a) : ℕ) = ∑ v, a v := by
      rw [Finsupp.weight_eq_sum, map_sum]
      simp [mdeg, Finsupp.degree_single]
    rw [Finsupp.degree_eq_sum (f := a),
      (Finsupp.degree_eq_sum (f := Finsupp.weight (mdeg N) a)).symm, h]
  have hwa : Finsupp.weight (mdeg N) a = d := hp ha
  have h1 : Finsupp.weight (1 : Fin (N + 1) × Fin 2 → ℕ) a = Finsupp.degree a := by
    simp only [Finsupp.weight, Finsupp.degree_eq_weight_one]; rfl
  rw [h1, hkey, hwa]

/-- `rayHilb` is antitone in the ideal: for `I ≤ J` the degree-`tD` pieces satisfy
`(R/I)_{tD} ↠ (R/J)_{tD}`, so `dim (R/J)_{tD} ≤ dim (R/I)_{tD}`. -/
private theorem rayHilb_mono {N : ℕ} (D : Fin (N + 1) →₀ ℕ) {I J : Ideal (MR N)}
    (hIJ : I ≤ J) (t : ℕ) : rayHilb N D J t ≤ rayHilb N D I t := by
  haveI := homPiece_finite N (t • D)
  unfold rayHilb
  have hp : Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ) ≤
      Submodule.comap (homPiece N (t • D)).subtype (J.restrictScalars ℂ) :=
    Submodule.comap_mono fun _ hx => hIJ hx
  have h1 := Submodule.finrank_quotient_add_finrank
    (Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ))
  have h2 := Submodule.finrank_quotient_add_finrank
    (Submodule.comap (homPiece N (t • D)).subtype (J.restrictScalars ℂ))
  have h3 : Module.finrank ℂ
        ↥(Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ)) ≤
      Module.finrank ℂ
        ↥(Submodule.comap (homPiece N (t • D)).subtype (J.restrictScalars ℂ)) :=
    Submodule.finrank_mono hp
  omega

/-- A polynomial which is nonnegative at all large natural arguments has nonnegative leading
coefficient. -/
private theorem leadingCoeff_nonneg_of_eventually (P : Polynomial ℚ)
    (h : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.leadingCoeff := by
  by_contra hc
  push Not at hc
  rcases eq_or_ne P 0 with h0 | h0
  · rw [h0] at hc; simp at hc
  rcases Nat.eq_zero_or_pos P.natDegree with hd | hd
  · -- `P` is a constant
    have hC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
    have hval : ∀ n : ℕ, P.eval (n : ℚ) = P.coeff 0 := by
      intro n
      conv_lhs => rw [hC]
      rw [Polynomial.eval_C]
    have hlc : P.leadingCoeff = P.coeff 0 := by
      conv_lhs => rw [hC]
      rw [Polynomial.leadingCoeff_C]
    rw [hlc] at hc
    obtain ⟨n, hn⟩ := h.exists
    rw [hval n] at hn
    linarith
  · -- `P` has positive degree and negative leading coefficient: it tends to `-∞`.
    have hdeg : 0 < P.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hd
    have hT : Filter.Tendsto (fun n : ℕ => P.eval (n : ℚ)) Filter.atTop Filter.atBot :=
      (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg (le_of_lt hc)).comp
        tendsto_natCast_atTop_atTop
    have h1 : ∀ᶠ n : ℕ in Filter.atTop, P.eval (n : ℚ) ≤ (-1 : ℚ) :=
      (Filter.tendsto_atBot.mp hT) (-1)
    obtain ⟨n, hn1, hn2⟩ := (h1.and h).exists
    linarith

/-- If `p` and `q` have the same `natDegree` and `p(n) ≤ q(n)` for all large naturals `n`, then
`leadingCoeff p ≤ leadingCoeff q`. -/
private theorem leadingCoeff_le_of_eventually_le {p q : Polynomial ℚ}
    (hd : p.natDegree = q.natDegree)
    (h : ∀ᶠ n : ℕ in Filter.atTop, p.eval (n : ℚ) ≤ q.eval (n : ℚ)) :
    p.leadingCoeff ≤ q.leadingCoeff := by
  have hle : (q - p).natDegree ≤ p.natDegree := by
    simpa [← hd] using Polynomial.natDegree_sub_le q p
  have hnonneg : 0 ≤ (q - p).coeff p.natDegree := by
    rcases hle.lt_or_eq with hlt | heq
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    · rw [← heq]
      exact leadingCoeff_nonneg_of_eventually (q - p) (by
        filter_upwards [h] with n hn
        rw [Polynomial.eval_sub]
        linarith)
  have hkey : q.coeff p.natDegree = p.coeff p.natDegree + (q - p).coeff p.natDegree := by
    conv_lhs => rw [show q = p + (q - p) by ring]
    rw [Polynomial.coeff_add]
  have hq : q.coeff p.natDegree = q.leadingCoeff := by
    rw [hd, Polynomial.coeff_natDegree]
  rw [hq, Polynomial.coeff_natDegree] at hkey
  linarith

/-! ## From a multigraded Hilbert polynomial to the ray Hilbert polynomial

`graded_hilbert` (route `Work.RB`) produces a polynomial `P` in the multidegrees `d` giving
`dim (R/I)_d` for all `d` with all coordinates large.  Along the ray `d = t • D` this is a polynomial
function of `t`, which is exactly what `IsRayPoly N D I` asks for. -/

/-- Evaluation of a substituted polynomial: substituting `X i ↦ C (D i) * X` and evaluating at `t`
is evaluating the original polynomial at the point `i ↦ t * D i`. -/
private lemma aeval_eval (N : ℕ) (P : MvPolynomial (Fin (N + 1)) ℚ)
    (D : Fin (N + 1) →₀ ℕ) (t : ℚ) :
    (MvPolynomial.aeval (fun i : Fin (N + 1) => Polynomial.C ((D i : ℚ)) * Polynomial.X) P).eval t
      = P.eval (fun i => t * (D i : ℚ)) := by
  rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom t]
  rw [MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom t)]
  have h1 : (Polynomial.evalRingHom t).comp (algebraMap ℚ (Polynomial ℚ)) = RingHom.id ℚ := by
    ext a; simp
  have h2 : (⇑(Polynomial.evalRingHom t) ∘ fun i => Polynomial.C (D i : ℚ) * Polynomial.X)
      = (fun i => t * (D i : ℚ)) := by
    funext i; simp [mul_comm]
  rw [h1, h2, MvPolynomial.eval₂_id]

/-- A multigraded Hilbert polynomial for `R/I` (in the form produced by `graded_hilbert`)
specialises to a ray Hilbert polynomial: restrict it to the ray `d = t • D`. -/
private theorem exists_isRayPoly_of_hilbert {N : ℕ} (D : Fin (N + 1) →₀ ℕ)
    (hD : ∀ i, 1 ≤ D i) (I : Ideal (MR N)) (hI : MultiHom N I)
    (h : ∃ (P : MvPolynomial (Fin (N + 1)) ℚ) (N₀ : ℕ), ∀ d : Fin (N + 1) →₀ ℕ,
      (∀ i, N₀ ≤ d i) →
      ((Module.finrank ℂ (homPiece N d ⧸
        Submodule.comap (homPiece N d).subtype (I.restrictScalars ℂ)) : ℕ) : ℚ)
        = P.eval (fun i => (d i : ℚ))) :
    ∃ q : Polynomial ℚ, IsRayPoly N D I q := by
  obtain ⟨P, N₀, hP⟩ := h
  refine ⟨MvPolynomial.aeval (fun i : Fin (N + 1) => Polynomial.C ((D i : ℚ)) * Polynomial.X) P, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N₀] with t ht
  have hd : ∀ i, N₀ ≤ (t • D) i := by
    intro i
    have h1 : t * 1 ≤ t * D i := Nat.mul_le_mul_left t (hD i)
    have h2 : (t • D) i = t * D i := by
      rw [Finsupp.smul_apply, smul_eq_mul]
    rw [h2]; exact le_trans ht (by simpa using h1)
  have hmain := hP (t • D) hd
  have hfun : (fun i : Fin (N + 1) => (((t • D) i : ℕ) : ℚ))
      = (fun i : Fin (N + 1) => (t : ℚ) * (D i : ℚ)) := by
    funext i
    rw [Finsupp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [rayHilb, hmain, aeval_eval, hfun]

/-- Block A2: the ray Hilbert polynomial of a multihomogeneous ideal exists.

(Obtained here from the multigraded Hilbert polynomial theorem `Work.RB.graded_hilbert` of the
`Work.RB` route: `mdeg N` is a basis-vector weight, and `MultiHom N I` is exactly the
`w`-homogeneity hypothesis.) -/
private theorem rayPoly_exists_local {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I : Ideal (MR N)) (hI : MultiHom N I) : ∃ q : Polynomial ℚ, IsRayPoly N D I q :=
  exists_isRayPoly_of_hilbert D hD I hI <|
    Work.RB.graded_hilbert (mdeg N) (fun v => ⟨v.1, rfl⟩) I hI

/-- Block A3d. `I ≤ J` of the same ray dimension gives `H(J; D) ≤ H(I; D)`. -/
theorem rayDeg_mono {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I J : Ideal (MR N)) (hI : MultiHom N I) (hJ : MultiHom N J) (hIJ : I ≤ J)
    (hJ0 : rayPoly N D J ≠ 0) (hdim : rayDim N D J = rayDim N D I) :
    rayDeg N D J ≤ rayDeg N D I := by
  -- existence of the ray Hilbert polynomial on the `J` side, from `rayPoly N D J ≠ 0`
  have hJex : ∃ q : Polynomial ℚ, IsRayPoly N D J q := by
    by_contra h
    exact hJ0 (by rw [rayPoly, dif_neg h])
  have hJis : IsRayPoly N D J (rayPoly N D J) := by
    rw [rayPoly, dif_pos hJex]; exact Classical.choose_spec hJex
  -- existence on the `I` side: block A2
  have hIis : IsRayPoly N D I (rayPoly N D I) := by
    rw [rayPoly, dif_pos (rayPoly_exists_local D hD I hI)]
    exact Classical.choose_spec (rayPoly_exists_local D hD I hI)
  -- pointwise comparison of the two ray Hilbert polynomials
  have hmono : ∀ᶠ t : ℕ in Filter.atTop,
      (rayPoly N D J).eval (t : ℚ) ≤ (rayPoly N D I).eval (t : ℚ) := by
    filter_upwards [hIis, hJis] with t hIt hJt
    rw [← hJt, ← hIt]
    exact_mod_cast rayHilb_mono D hIJ t
  have hnat : (rayPoly N D J).natDegree = (rayPoly N D I).natDegree := hdim
  have hlc := leadingCoeff_le_of_eventually_le hnat hmono
  have hfac : ((rayPoly N D J).natDegree.factorial : ℚ) =
      ((rayPoly N D I).natDegree.factorial : ℚ) :=
    congrArg (fun n : ℕ => (n.factorial : ℚ)) hnat
  show ((rayPoly N D J).natDegree.factorial : ℚ) * (rayPoly N D J).leadingCoeff ≤
    ((rayPoly N D I).natDegree.factorial : ℚ) * (rayPoly N D I).leadingCoeff
  rw [hfac]
  exact mul_le_mul_of_nonneg_left hlc (by positivity)

end Work.BW
