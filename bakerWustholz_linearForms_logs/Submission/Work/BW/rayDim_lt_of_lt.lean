import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.rayPoly_eq
import Submission.Work.BW.rayHilb_finite
import Submission.Work.BW.rayHilb_cut
import Submission.Work.BW.poly_shift_natDegree
import Submission.Work.BW.poly_natDegree_eventually_le
import Submission.Work.RB.graded_hilbert

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive, multiplicity block). Your node is `rayDim_lt_of_lt`. The design is below: find your node in the §2.3 or §3 tables for its content, its dependencies and its size.
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

variable {N : ℕ}

/-! ### Multidegree bookkeeping for monomials -/

private lemma mdeg_apply (v : Fin (N + 1) × Fin 2) (i : Fin (N + 1)) :
    mdeg N v i = if v.1 = i then 1 else 0 := by
  by_cases h : v.1 = i <;> simp [mdeg, h]

private lemma weight_apply (m : Fin (N + 1) × Fin 2 →₀ ℕ) (i : Fin (N + 1)) :
    Finsupp.weight (mdeg N) m i = ∑ v, m v * (if v.1 = i then 1 else 0) := by
  rw [Finsupp.weight_eq_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, mdeg_apply, smul_eq_mul]

private lemma exists_support_of_weight_apply_pos {m : Fin (N + 1) × Fin 2 →₀ ℕ}
    {e : Fin (N + 1) →₀ ℕ} (h : Finsupp.weight (mdeg N) m = e) {i : Fin (N + 1)}
    (hi : 1 ≤ e i) : ∃ j : Fin 2, m (i, j) ≠ 0 := by
  have hsum : e i = ∑ v, m v * (if v.1 = i then 1 else 0) := by
    rw [← h]; exact weight_apply m i
  have hne : (∑ v, m v * (if v.1 = i then 1 else 0)) ≠ 0 := by omega
  obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hmv : m v ≠ 0 := fun h0 => hv (by rw [h0, zero_mul])
  have hvi : v.1 = i := by
    by_contra hc
    exact hv (by rw [ite_eq_right hc, mul_zero])
  refine ⟨v.2, ?_⟩
  rwa [show (i, v.2) = v from by rw [← hvi]]

private lemma sum_smul_mdeg_apply (a : Fin (N + 1) → ℕ) (j : Fin (N + 1) → Fin 2) (i : Fin (N + 1)) :
    (∑ i' : Fin (N + 1), a i' • mdeg N (i', j i')) i = a i := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · rw [Finsupp.smul_apply, mdeg_apply, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro i' _ hne
    rw [Finsupp.smul_apply, mdeg_apply, ite_eq_right hne, smul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ### The multihomogeneous pieces as spans of monomials -/

private lemma monomial_mem_homPiece {e : Fin (N + 1) →₀ ℕ}
    {m : Fin (N + 1) × Fin 2 →₀ ℕ} (h : Finsupp.weight (mdeg N) m = e) :
    (monomial m (1 : ℂ)) ∈ homPiece N e := by
  rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
  exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ h

private lemma homPiece_eq_span (e : Fin (N + 1) →₀ ℕ) :
    homPiece N e = Submodule.span ℂ ((fun m => MvPolynomial.monomial m (1 : ℂ)) ''
      {m | Finsupp.weight (mdeg N) m = e}) := by
  rw [homPiece, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact MvPolynomial.restrictSupport_eq_span ℂ _

/-- If both variables of the `i`-th factor lie in an ideal `I`, and the `i`-th multidegree is
nonzero, then `I` contains the whole multihomogeneous piece. -/
private lemma homPiece_le_of_both_X_mem {I : Ideal (MR N)} {i : Fin (N + 1)}
    (h0 : MvPolynomial.X (i, 0) ∈ I) (h1 : MvPolynomial.X (i, 1) ∈ I)
    {e : Fin (N + 1) →₀ ℕ} (he : 1 ≤ e i) : homPiece N e ≤ I.restrictScalars ℂ := by
  rw [homPiece_eq_span, Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨j, hj⟩ := exists_support_of_weight_apply_pos hm he
  have hX : MvPolynomial.X (i, j) ∈ I := by
    fin_cases j
    · exact h0
    · exact h1
  have hdvd : MvPolynomial.X (i, j) ∣ MvPolynomial.monomial m (1 : ℂ) :=
    MvPolynomial.X_dvd_monomial.mpr (Or.inr hj)
  obtain ⟨c, hc⟩ := hdvd
  simpa [hc] using Ideal.mul_mem_right c I hX

private lemma prod_notMem_of_notMem {I : Ideal (MR N)} (hp : I.IsPrime) {ι : Type*} {s : Finset ι}
    {f : ι → MR N} (h : ∀ i ∈ s, f i ∉ I) : ∏ i ∈ s, f i ∉ I := by
  classical
  refine Finset.prod_induction _ (fun x => x ∉ I) ?_ ?_ h
  · intro a b ha hb hab
    exact (hp.mem_or_mem hab).elim ha hb
  · intro h1
    exact (Ideal.ne_top_iff_one I).mp hp.ne_top h1

private theorem exists_cut_element (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (p q : Ideal (MR N)) (hp : p.IsPrime) (hq : q.IsPrime) (hpH : MultiHom N p)
    (hqH : MultiHom N q) (hpq : p < q) (hq0 : rayPoly N D q ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ Q ∈ homPiece N (k • D), Q ∈ q ∧ Q ∉ p := by
  classical
  have hne : p ≠ q := hpq.ne
  have hle : p ≤ q := hpq.le
  have hnotsub : ¬ (q : Set (MR N)) ⊆ p := by
    intro hsub
    exact hne (le_antisymm hle fun x hx => hsub hx)
  obtain ⟨f, hfq, hfp⟩ := Set.not_subset.mp hnotsub
  obtain ⟨d, hd⟩ : ∃ d : Fin (N + 1) →₀ ℕ,
      MvPolynomial.weightedHomogeneousComponent (mdeg N) d f ∉ p := by
    by_contra hc
    push Not at hc
    have hfin := MvPolynomial.weightedHomogeneousComponent_finsupp (w := mdeg N) f
    have hsum := MvPolynomial.sum_weightedHomogeneousComponent (mdeg N) f
    rw [finsum_eq_sum _ hfin] at hsum
    refine hfp (hsum ▸ Submodule.sum_mem _ fun d _ => hc d)
  set g : MR N := MvPolynomial.weightedHomogeneousComponent (mdeg N) d f with hgdef
  have hgq : g ∈ q := hqH f hfq d
  have hgne : g ≠ 0 := fun h => hd (h ▸ p.zero_mem)
  have hghom : MvPolynomial.IsWeightedHomogeneous (mdeg N) g d :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous d f
  have hvar : ∀ i : Fin (N + 1), ∃ j : Fin 2, MvPolynomial.X (i, j) ∉ p := by
    intro i
    by_contra hc
    push Not at hc
    have hzero : ∀ t : ℕ, 1 ≤ t → rayHilb N D q t = 0 := by
      intro t ht
      have hpiece : homPiece N (t • D) ≤ q.restrictScalars ℂ := fun x hx =>
        hle (homPiece_le_of_both_X_mem (hc 0) (hc 1) (by
          rw [Finsupp.smul_apply, smul_eq_mul]
          simpa using Nat.mul_le_mul ht (hD i)) hx)
      unfold rayHilb
      have htop : Submodule.comap (homPiece N (t • D)).subtype (q.restrictScalars ℂ) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact hpiece x.2
      rw [htop]
      haveI : Subsingleton (↥(homPiece N (t • D)) ⧸
          (⊤ : Submodule ℂ ↥(homPiece N (t • D)))) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      exact Module.finrank_zero_of_subsingleton
    have hpoly : IsRayPoly N D q 0 := by
      filter_upwards [Filter.eventually_ge_atTop 1] with t ht
      rw [hzero t ht]; simp
    exact hq0 (rayPoly_eq hpoly)
  choose j hj using hvar
  let k : ℕ := 1 + ∑ i : Fin (N + 1), d i
  have hk : 1 ≤ k := by simp [k]
  have hkD : ∀ i, d i ≤ k * D i := by
    intro i
    have h1 : k ≤ k * D i := Nat.le_mul_of_pos_right k (by have := hD i; omega)
    have h2 : d i ≤ k := by
      have h3 : d i ≤ ∑ i : Fin (N + 1), d i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      simp only [k]
      omega
    exact le_trans h2 h1
  let M : MR N := ∏ i : Fin (N + 1), MvPolynomial.X (i, j i) ^ (k * D i - d i)
  have hMhom : MvPolynomial.IsWeightedHomogeneous (mdeg N) M
      (∑ i : Fin (N + 1), (k * D i - d i) • mdeg N (i, j i)) := by
    refine MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ ?_
    intro i _
    exact (MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) (i, j i)).pow _
  have hdeg : d + (∑ i : Fin (N + 1), (k * D i - d i) • mdeg N (i, j i)) = k • D := by
    ext i
    rw [Finsupp.add_apply, sum_smul_mdeg_apply, Finsupp.smul_apply, smul_eq_mul]
    have := hkD i
    omega
  have hQhom : MvPolynomial.IsWeightedHomogeneous (mdeg N) (g * M) (k • D) := by
    have h := hghom.mul hMhom
    rwa [hdeg] at h
  have hMp : M ∉ p := by
    refine prod_notMem_of_notMem hp ?_
    intro i _
    rcases Nat.eq_zero_or_pos (k * D i - d i) with h | h
    · rw [h, pow_zero]
      exact fun h1 => (Ideal.ne_top_iff_one p).mp hp.ne_top h1
    · exact fun hpow => hj i (hp.mem_of_pow_mem _ hpow)
  have hQmem : g * M ∈ homPiece N (k • D) := by
    rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact hQhom
  have hQq : g * M ∈ q := Ideal.mul_mem_right M q hgq
  have hQp : g * M ∉ p := fun hab => (hp.mem_or_mem hab).elim hd hMp
  exact ⟨k, hk, g * M, hQmem, hQq, hQp⟩

/-! ### Basic facts about the ray Hilbert polynomial -/

private lemma isRayPoly_rayPoly_of_ne_zero {N : ℕ} {D : Fin (N + 1) →₀ ℕ} {I : Ideal (MR N)}
    (h : rayPoly N D I ≠ 0) : IsRayPoly N D I (rayPoly N D I) := by
  by_cases hh : ∃ q, IsRayPoly N D I q
  · unfold rayPoly
    rw [dite_eq_left hh]
    exact Classical.choose_spec hh
  · exact absurd (show rayPoly N D I = 0 from by
      unfold rayPoly; rw [dite_eq_right hh]) h

/-! ### The ray Hilbert function is antitone in the ideal -/

private lemma rayHilb_anti {N : ℕ} (D : Fin (N + 1) →₀ ℕ) {I J : Ideal (MR N)} (hIJ : I ≤ J)
    (t : ℕ) : rayHilb N D J t ≤ rayHilb N D I t := by
  haveI := rayHilb_finite N (t • D)
  unfold rayHilb
  have hmono : Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ) ≤
      Submodule.comap (homPiece N (t • D)).subtype (J.restrictScalars ℂ) :=
    Submodule.comap_mono fun x hx => hIJ hx
  have h1 := Submodule.finrank_quotient_add_finrank
    (Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ))
  have h2 := Submodule.finrank_quotient_add_finrank
    (Submodule.comap (homPiece N (t • D)).subtype (J.restrictScalars ℂ))
  have h3 : Module.finrank ℂ
        ↥(Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ)) ≤
      Module.finrank ℂ
        ↥(Submodule.comap (homPiece N (t • D)).subtype (J.restrictScalars ℂ)) :=
    Submodule.finrank_mono hmono
  omega

/-! ### From the exact sequence to the ray Hilbert polynomial of the cut ideal -/

private lemma isRayPoly_cut {N : ℕ} {D : Fin (N + 1) →₀ ℕ} {k : ℕ} (hk : 1 ≤ k) {I : Ideal (MR N)}
    (hI : MultiHom N I) {Q : MR N} (hQ : Q ∈ homPiece N (k • D))
    (hreg : ∀ f, Q * f ∈ I → f ∈ I) {P : Polynomial ℚ} (hP : IsRayPoly N D I P) :
    IsRayPoly N D (I ⊔ Ideal.span {Q})
      (P - P.comp (Polynomial.X - Polynomial.C (k : ℚ))) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hP
  refine Filter.eventually_atTop.mpr ⟨T + k, fun t ht => ?_⟩
  have hkt : k ≤ t := by omega
  have hTt : T ≤ t := by omega
  have hTtk : T ≤ t - k := by omega
  have hcut := rayHilb_cut D k hk I hI Q hQ hreg (t - k)
  rw [Nat.sub_add_cancel hkt] at hcut
  have hsub : rayHilb N D (I ⊔ Ideal.span {Q}) t =
      rayHilb N D I t - rayHilb N D I (t - k) := by omega
  have hble : rayHilb N D I (t - k) ≤ rayHilb N D I t := by omega
  rw [hsub, Nat.cast_sub hble, hT t hTt, hT (t - k) hTtk]
  rw [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Nat.cast_sub hkt]

/-! ### The main theorem -/


/-! ### The ray Hilbert polynomial of a multihomogeneous ideal

The design of the multiplicity block feeds the ray Hilbert polynomial of `p` in through block A2
(`Submission.Work.BW.rayHilb_poly`).  Instead of that node, this file derives the needed input from
the *general* multigraded Hilbert–Samuel theorem `Work.RB.graded_hilbert` (a variable has weight a
basis vector, so the multigraded Hilbert function of a multigraded ideal is, for all sufficiently
large multidegrees, given by a polynomial in the multidegree); restricting that polynomial to the
ray `t ↦ t • D` (`D ≥ 1`) gives the univariate polynomial required by `IsRayPoly`.

If `Work.BW.rayHilb_poly` is available, `rayHilb_poly D hD p hpH` can be used in place of
`isRayPoly_of_multigraded D hD p hpH` in `rayDim_lt_of_lt` below (it yields the same
`IsRayPoly N D p P0`). -/


/-- Substituting `X i ↦ a i * x` commutes with evaluating a multivariate polynomial at `x`. -/
private lemma eval_eval₂Hom_ray (n : ℕ) (P : MvPolynomial (Fin n) ℚ) (a : Fin n → ℚ) (x : ℚ) :
    (MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.C (a i) * Polynomial.X) P).eval x
      = P.eval (fun i => a i * x) := by
  let φ : MvPolynomial (Fin n) ℚ →+* ℚ := (Polynomial.evalRingHom x).comp
    (MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.C (a i) * Polynomial.X))
  let ψ : MvPolynomial (Fin n) ℚ →+* ℚ := MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun i => a i * x)
  have hφψ : φ = ψ := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r; simp [φ, ψ]
    · intro i; simp [φ, ψ]
  exact congrFun (congrArg DFunLike.coe hφψ) P

/-- **Ray Hilbert polynomial from the general multigraded Hilbert–Samuel theorem.** If every
variable has weight a basis vector then the multigraded Hilbert function of a graded ideal is
eventually a polynomial in the multidegree, so its restriction to the ray `t ↦ t • D` with `D ≥ 1`
is eventually a polynomial in `t`. -/
private theorem isRayPoly_of_multigraded {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I : Ideal (MR N)) (hI : MultiHom N I) : ∃ P : Polynomial ℚ, IsRayPoly N D I P := by
  obtain ⟨P, M, hP⟩ := Work.RB.graded_hilbert (n := N + 1) (σ := Fin (N + 1) × Fin 2)
    (w := mdeg N) (fun v => ⟨v.1, rfl⟩) I (fun p hp d => hI p hp d)
  refine ⟨MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.C ((D i : ℚ)) * Polynomial.X) P, ?_⟩
  rw [IsRayPoly]
  filter_upwards [Filter.eventually_ge_atTop M] with t ht
  have hdt : ∀ i : Fin (N + 1), M ≤ (t • D) i := by
    intro i
    rw [Finsupp.smul_apply, smul_eq_mul]
    calc M ≤ t := ht
      _ = t * 1 := (mul_one t).symm
      _ ≤ t * D i := Nat.mul_le_mul_left t (hD i)
  have h1 := hP (t • D) hdt
  have h2 : (fun i : Fin (N + 1) => (((t • D) i : ℕ) : ℚ)) = fun i => (D i : ℚ) * (t : ℚ) := by
    funext i
    rw [Finsupp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [h2] at h1
  have h3 : ((rayHilb N D I t : ℕ) : ℚ) =
      ((Module.finrank ℂ (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) (t • D) ⧸
        Submodule.comap (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) (t • D)).subtype
          (I.restrictScalars ℂ)) : ℕ) : ℚ) := rfl
  rw [h3, h1, eval_eval₂Hom_ray]

/-- Block A3e, with the ray Hilbert polynomial of `p` supplied by block A2: if `P0` is a
polynomial eventually equal to `t ↦ dim (R/p)_{tD}`, then the ray dimension strictly drops when
passing from `p` to the strictly larger relevant prime `q`. -/
private theorem rayDim_lt_of_isRayPoly {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (p q : Ideal (MR N)) (hp : p.IsPrime) (hq : q.IsPrime) (hpH : MultiHom N p)
    (hqH : MultiHom N q) (hpq : p < q) (hq0 : rayPoly N D q ≠ 0) (P0 : Polynomial ℚ)
    (hP0 : IsRayPoly N D p P0) :
    rayDim N D q < rayDim N D p := by
  classical
  -- a multihomogeneous element of multidegree `k • D` in `q \ p`
  obtain ⟨k, hk, Q, hQmem, hQq, hQp⟩ := exists_cut_element D hD p q hp hq hpH hqH hpq hq0
  -- `Q` is a non-zerodivisor modulo `p`
  have hreg : ∀ f, Q * f ∈ p → f ∈ p := fun f hf =>
    (hp.mem_or_mem hf).elim (fun h => absurd h hQp) id
  -- the cut ideal sits between `p` and `q`
  have hIQ : p ⊔ Ideal.span {Q} ≤ q :=
    sup_le hpq.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hQq))
  -- the exact sequence gives the ray Hilbert polynomial of the cut ideal
  have hcut : IsRayPoly N D (p ⊔ Ideal.span {Q})
      (P0 - P0.comp (Polynomial.X - Polynomial.C (k : ℚ))) :=
    isRayPoly_cut hk hpH hQmem hreg hP0
  have hqpoly : IsRayPoly N D q (rayPoly N D q) := isRayPoly_rayPoly_of_ne_zero hq0
  have hdimp : rayDim N D p = P0.natDegree := by rw [rayDim, rayPoly_eq hP0]
  by_cases hr : P0.natDegree = 0
  · -- degenerate case: `P0` is a constant, so the cut ideal has vanishing ray Hilbert function
    exfalso
    have hz : P0 - P0.comp (Polynomial.X - Polynomial.C (k : ℚ)) = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hr, Polynomial.C_comp, sub_self]
    rw [hz] at hcut
    have hqzero : IsRayPoly N D q 0 := by
      filter_upwards [hcut] with t ht
      have hI0 : rayHilb N D (p ⊔ Ideal.span {Q}) t = 0 := by
        have h := ht
        simp only [Polynomial.eval_zero] at h
        exact_mod_cast h
      have hle := rayHilb_anti D hIQ t
      rw [hI0] at hle
      rw [Nat.eq_zero_of_le_zero hle]
      simp
    exact hq0 (rayPoly_eq hqzero)
  · -- main case: the degree of the ray Hilbert polynomial drops by one
    have hr1 : 0 < P0.natDegree := Nat.pos_of_ne_zero hr
    have hanti : ∀ᶠ t : ℕ in Filter.atTop,
        (rayPoly N D q).eval (t : ℚ) ≤
          (P0 - P0.comp (Polynomial.X - Polynomial.C (k : ℚ))).eval (t : ℚ) := by
      filter_upwards [hqpoly, hcut] with t ht1 ht2
      rw [← ht1, ← ht2]
      exact_mod_cast rayHilb_anti D hIQ t
    have hnonneg : ∀ᶠ t : ℕ in Filter.atTop, 0 ≤ (rayPoly N D q).eval (t : ℚ) := by
      filter_upwards [hqpoly] with t ht
      rw [← ht]
      exact Nat.cast_nonneg _
    have hle := poly_natDegree_eventually_le hanti hnonneg
    rw [poly_shift_natDegree P0 k hk] at hle
    rw [rayDim, hdimp]
    omega


/-- Block A3e. A strictly larger relevant multihomogeneous prime has strictly smaller ray
dimension (cut `p` by an element of `q \ p`, made of multidegree `kD`, and use A3a). -/
theorem rayDim_lt_of_lt {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (p q : Ideal (MR N)) (hp : p.IsPrime) (hq : q.IsPrime) (hpH : MultiHom N p)
    (hqH : MultiHom N q) (hpq : p < q) (hq0 : rayPoly N D q ≠ 0) :
    rayDim N D q < rayDim N D p := by
  obtain ⟨P0, hP0⟩ := isRayPoly_of_multigraded D hD p hpH
  exact rayDim_lt_of_isRayPoly D hD p q hp hq hpH hqH hpq hq0 P0 hP0

end Work.BW
