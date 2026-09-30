import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.ellW_B_mem_span
import Submission.Work.BW.not_fully_degenerate
import Submission.Work.BW.multiplicity_engine
import Submission.Work.BW.zero_estimate_stepwise
import Submission.Work.BW.ellW_dichotomy
import Submission.Work.BW.applyW_cons_eq_applyDer
import Submission.Work.BW.one_le_ellW_false
import Submission.Work.BW.prim_basis_from_minors
import Submission.Work.BW.B_eq_zero_of_deg_lt_one
import Submission.Work.BW.zeroDeg_reduce
import Submission.Work.BW.hE1_extend
import Submission.Work.BW.quotient_reduction_core
import Submission.Work.BW.reduced_span_eq
import Submission.Work.BW.reduced_ellW_facts
import Submission.Work.BW.mp_pullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive, multiplicity block). Your node is `multiplicity_prop`. The design is below: find your node in the §2.3 or §3 tables for its content, its dependencies and its size.
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

/-! ### Status 2026-09-29 (session notes for the next stretch)

**PROVED IN THIS FILE (sorry-free, verified by `lake build Submission.Work.BW.multiplicity_prop`).**
* `Spos_of_hLambda` — `hΛ` forces `0 < 𝒮`.
* `ze_hvan_full` — the vanishing hypothesis of `zero_estimate_stepwise` in the operator family
  `w = (e₀, (0, c_m))` containing `∂₀` (uses the delegated `applyW_cons_eq_applyDer`).
* `one_le_floor_of` — `1 ≤ ⌊𝒟 i⌋₊` from `h𝒟0` and the non-degeneracy `𝒟 j.succ ≥ 1`.
* `minorJ_zero` — the minor of a `0 × N` matrix on an empty column set is `1`.
* `zedata_nondegenerate` — in the non-degenerate case the `ZEData r r` of the engine is the
  theorem's own data with `δ = 𝒟`.
* `ldich_of_dichotomy` — `ellW_dichotomy` in the shape `ze_engine` consumes.
* **`mp_main`** — the *whole non-degenerate case of `multiplicity_prop`*: builds the hypothesis
  package, runs `zero_estimate_stepwise` (level `N = r`, `q = r-1+1`, `P`, `D = ⌊𝒟⌋`, `w` as above,
  `θ = exp ∘ ℓ`), and feeds its output to `ze_engine` (with `L = ellW w ε M`, `hLdich` from
  `ldich_of_dichotomy`, `hLpos` from `one_le_ellW_false`, `hGoodB` from `ellW_B_mem_span`,
  `hmin` from `prim_basis_from_minors` passed in as the hypothesis `hmin`).  `mp_main` therefore
  *is* `multiplicity_prop` modulo (a) `prim_basis_from_minors` and (b) the degenerate case.

**DELEGATED.**
* proved: `applyW_cons_eq_applyDer`, `one_le_ellW_false`, `hE1_extend` (the `(E1)` transfer along
  `liftIdx σ`), `extM_sum_abs` (reindexing `∏ ∑ a|M|` along `σ`);
* in flight: `B_eq_zero_of_deg_lt_one` (if `𝒟 i.succ < 1` then `B i = 0`) and `mem_span_extM`
  (pulling `B ∘ σ ∈ ℚ-span M'` back to `B ∈ ℚ-span (extM σ M')`).

**THE REMAINING GAP: the degenerate case (`∃ i, 𝒟 i.succ < 1`).**  The design's route (drop the
coordinates with `𝒟 < 1`, apply the zero estimate on the quotient `G_a × G_m^{Z^c}`, pull the answer
back with `extM`) has **two structural problems** that the design does not address:

1. **The lattice transfer needs `B` supported off `Z`.**  With `M = extM σ M'` every column outside
   `range σ` is zero, so `B ∈ ℚ-span M` forces `B i = 0` for `i ∉ range σ`.  Nothing in the
   hypotheses obviously forces this (delegated as `B_eq_zero_of_deg_lt_one`); the evidence (exact
   searches for `r = 2`, and the «no two exponents of `P` differ by a rational multiple of `B`»
   argument which holds as soon as `B` has a non-zero coordinate in `Z`) is that instead the
   *degenerate case is contradictory* whenever some such `B i ≠ 0`.
2. **The engine does not apply at level `N' < r`.**  `ze_engine`, `ellW_dichotomy` and
   `ellW_B_mem_span` are all stated for an operator family `w : Fin (r'-1+1) → Fin (r'+1) → ℂ`
   whose `r'-1` torus directions are ℚ-independent, so that `dim span w = r'` and
   `ellW w ε M ∈ {k-1, k}` — the latter needs `dim W + dim Lie G' ≥` (ambient) `- 1`.  In the
   quotient the (`r-1`) restricted directions `c_m ∘ σ` live in `ℚ^{N'}`; their rank is `≤ min(r-1,N')`:
   * if `|Z| = 1` (`N' = r-1`) the restricted family can still be ℚ-independent, and then
     `dim span w = 1 + (r-1) = r` and a **generalized** `ellW_dichotomy` (arbitrary operator-index
     type, or rank-formulated) would give the dichotomy;
   * if `|Z| ≥ 2` (`N' < r-1`) the `c_m ∘ σ` are **dependent**, `dim span w ≤ 1 + N' < r`, and
     neither the dichotomy nor the `ℓ = k-1 ⟹ B' ∈ ℚ-span M'` analysis is available, because the
     exclusions (E0)–(E3) and the collision analysis are calibrated to `k = (if ε then 0 else 1)+ρ`
     with `dim W = r` the ambient dimension.  (BW themselves avoid this: their operators
     `a_j = B_jY_j∂_j - B_0Y_0∂_0` always have `dim W = r`, the ambient dimension — they work with a
     *fixed* ambient and never quotient.)
   So the fix (if the quotient route is kept) is to generalise `ellW_dichotomy` / `ellW_B_mem_span`
   to an arbitrary `w : Fin q → Fin (N+1) → ℂ` with `dim span w` replaced by an explicit rank, and to
   redo the (E)-table with `k` measured against `dim span w` rather than the ambient dimension.
So the degenerate case needs either a *generalized* engine (family of arbitrary rank) or a
contradiction argument; the numerical evidence of `hE0`+`hE1`+`hvan` (see also the delegated
`not_fully_degenerate`, which handles `Z = Fin r`) points to the contradiction.

**Also needed to finish.**  `Submission.Work.BW.prim_basis_from_minors` does not build (it imports
`minkowski_basis`, which needs the empty stub `Submission.Work.BW.minkowski_second_l1`, being
proved by agent `…-H9-L68`).  Once it lands: instantiate `mp_main`'s `hmin` with it, and handle the
degenerate case; then `multiplicity_prop` is done.
-/

namespace Work.BW

/-! ### Glue lemmas for the assembly (BW §10 restated, P86* route)

`hvan` is stated with `ptS ℓ` (points `(s, e^{sℓ})`) and `applyDer c` (the operators
`∂₀^{t0} ∏_m (eulerDer (c m))^{t m}`), while the zero estimate `zero_estimate_stepwise` is stated
with `ptTheta θ` (points `(s, θ^s)`) and `applyW w` (the operators `∏_k (derC (w k))^{t k}`).
The two formalisms agree:

* `ptS_eq_ptTheta : ptS ℓ = ptTheta (fun i => exp (ℓ i))`;
* `derC_cons_zero_eq_eulerDer : derC (Fin.cons 0 c) = eulerDer c`, hence
  `applyDer_eq_pderiv_applyW : applyDer c t0 t P = ∂₀^{[t0]} (applyW w t P)` for
  `w m = Fin.cons 0 (c m)` — in particular `applyDer c 0 t P = applyW w t P`, which is the form
  needed to feed `hvan` into `zero_estimate_stepwise` (taking `t0 = 0` and using `hTsum`,
  `∑ Tq ≤ 𝒯`). -/

/-- `List.foldr` respects pointwise equal step functions. -/
lemma foldr_congr_poly {n q : ℕ} (l : List (Fin q))
    (F G : Fin q → MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ)
    (h : ∀ m, F m = G m) (b : MvPolynomial (Fin n) ℂ) :
    l.foldr F b = l.foldr G b := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons]; rw [h a, ih]

/-- The two conventions for the point `s·γ` of `G_a × G_m^r` agree. -/
lemma ptS_eq_ptTheta {r : ℕ} (ℓ : Fin r → ℂ) :
    ptS ℓ = ptTheta (fun i => Complex.exp (ℓ i)) := by
  funext s
  simp only [ptS, ptTheta]
  congr 1
  funext i
  exact Complex.exp_nat_mul (ℓ i) s

/-- A sequence that does not increase at every step is nonincreasing on `{0,…,r}`. -/
lemma sq_le {r : ℕ} {Sq : ℕ → ℕ} (hSa : ∀ m, m < r → Sq (m + 1) ≤ Sq m)
    {m k : ℕ} (hm : m + 1 ≤ k) (hk : k ≤ r) :
    Sq (k - 1) + 1 ≤ Sq m + 1 := by
  have h1 : m ≤ k - 1 := by omega
  have h2 : k - 1 ≤ r := by omega
  exact Nat.succ_le_succ (anti_of_step hSa h1 h2)

/-- The degree bound needed to feed `zero_estimate_stepwise` (whose `hdeg` asks for `degreeOf i ≤ D i`
with `D i : ℕ`): from `(P.degreeOf i : ℝ) ≤ 𝒟 i` get `P.degreeOf i ≤ ⌊𝒟 i⌋₊`. -/
lemma degreeOf_le_floor {r : ℕ} (P : MvPolynomial (Fin (r+1)) ℂ) (𝒟 : Fin (r+1) → ℝ)
    (hdeg : ∀ j, (P.degreeOf j : ℝ) ≤ 𝒟 j) (j : Fin (r+1)) :
    P.degreeOf j ≤ ⌊𝒟 j⌋₊ :=
  Nat.le_floor (hdeg j)

/-- `cardMod` is at least `1`, so the factor `#((Σ_m+G')/G') ≥ 1` can be dropped when transferring
the zero estimate's inequality to the theorem's conclusion. -/
lemma applyDer_eq_pderiv_applyW {r : ℕ} (c : Fin (r-1) → Fin r → ℚ) (t0 : ℕ)
    (t : Fin (r-1) → ℕ) (P : MvPolynomial (Fin (r+1)) ℂ) :
    (MvPolynomial.pderiv (0 : Fin (r+1)))^[t0]
        (applyW (N := r) (q := r-1)
          (fun m => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))) t P)
      = applyDer c t0 t P := by
  simp only [applyDer, applyW]
  congr 1
  refine foldr_congr_poly _ _ _ (fun m => ?_) _
  rw [derC_cons_zero_eq_eulerDer (c m)]


/-! ### Status of the assembly (notes for the next stretch of work)

**Verified here (sorry-free).** The glue lemmas above identify the two formalisms
(`ptS`/`applyDer` vs `ptTheta`/`applyW`), so `hvan` for `t0 = 0` *is* the hypothesis of
`zero_estimate_stepwise` with `w = (e₀, (0, c_m))`, `θ i = exp (ℓ i)`, `N = r`, `q = r-1`, using
`hTsum : ∑ Tq ≤ 𝒯`. Concretely: `derC_cons_zero_eq_eulerDer`, `foldr_congr_poly`,
`ptS_eq_ptTheta`, `applyDer_eq_pderiv_applyW`, `ze_hvan_of_hvan` (this last one *derives* the zero
estimate's vanishing hypothesis from `hvan`), plus the pieces the transfer needs:
`degreeOf_le_floor` (feeds the zero estimate's `Dᵢ = ⌊𝒟ᵢ⌋`), `anti_of_step`, `sq_le`,
`choose_mono_top` (the monotonicity of `Sq`/`Tq` along the steps, giving
`Sq(k-1)+1 ≤ Sq m + 1` and `C(Tq(k-1)+k-1,k-1) ≤ C(Tq m+k-1,k-1)` for `m+1 ≤ k`).

**Delegated pieces (both proved, imported above).**
* `Submission.Work.BW.ellW_B_mem_span` — the case-analysis core: `ellW w ε M = k-1` (with
  `w = (e₀,(0,c_m))`, `k = ρ` resp. `1+ρ`) forces `B ∈ ℚ-span M`.
* `Submission.Work.BW.not_fully_degenerate` — the fully degenerate case (`∀ i : Fin r, 𝒟 i.succ < 1`,
  i.e. all torus coordinates drop in step 1) is contradictory, as the lead requested: `P ∈ ℂ[Y₀]`
  plus `hvan` gives `(⌊𝒯⌋+1)(⌊𝒮⌋+1) ≤ deg_{Y₀}P`, contradicting (E1) at `m = 0`.

**Still to be written (the assembly proper).**
* The partial-degeneracy reduction (design step 1): for `{i ≥ 1 : 𝒟ᵢ < 1} ≠ ∅` work on
  `G/T_Z`, where `P` has degree `0` in the dropped coordinates, and pull the quotient's
  case-A/case-B output back.
* The (E)-exclusion analyses of the zero estimate's remaining outputs: `ℓ = k` (by (E1)), the
  collisions (`cardMod = Sq m + 1`, by (E0) with `hΛ`), and `0 × 1` (by (E2)).
* The final transfer: combine `zero_estimate_stepwise`'s inequality (with `m`, `ℓ = k-1`,
  `cardMod ≥ Sq m+1`), the imported `prim_basis_from_minors` bound and `Dᵢ = ⌊𝒟ᵢ⌋` via
  `choose_mono_top`, `sq_le`, `anti_of_step` to produce the two alternatives; the constant
  bookkeeping is verified above.

**Verified on paper (constants match the zero estimate exactly).** Write `Dᵢ = ⌊𝒟ᵢ⌋`, `k = ρ` in
the `G_a × H'` case (`ε = true`) and `k = ρ+1` in the `0 × H'` case (`ε = false`). The zero
estimate gives, for some step `m` and every `J` with `|J| = ρ` and `minorJ M J hJ ≠ 0`,

    C(Tq m + ℓ, ℓ) · (#((Σ_m+G')/G')) · (N+1-k)! · |Δ_J| · D₀^ε · ∏_{i∉J} D_{i+1} ≤ (N+1)! · ∏ D.

The case analysis supplies `ℓ = k-1` and (via the collision analysis of step 4, using (E0)) that the
classes of `{0,…,Sq m}` mod `G'` are all distinct, i.e. `cardMod ε M θ (Sq m) ≥ Sq m + 1`; the
monotonicity `hSa` gives `Sq m + 1 ≥ Sq (k-1) + 1`, and `m ≤ k-1` with `hTa` gives
`C(Tq m + ℓ, ℓ) = C(Tq m + k-1, k-1) ≥ C(Tq (k-1) + k-1, k-1)`. Hence
`(Sq(ρ-1)+1)·C(Tq(ρ-1)+ρ-1,ρ-1) ≤ cardMod ε M θ (Sq m) · C(Tq m + ℓ, ℓ)` in case A (`k = ρ`) and
likewise `(Sq ρ+1)·C(Tq ρ+ρ,ρ) ≤ cardMod · C(Tq m+ℓ,ℓ)` in case B (`k = 1+ρ`). Dividing the zero
estimate's inequality by `∏_{i∉J}D_{i+1}·D_0^ε = (∏D) / (D₀^{1-ε}∏_{i∈J}D_{i+1})`, using
`(N+1)!/(N+1-k)! = (r+1).descFactorial k`, `Dᵢ ≤ 𝒟ᵢ`, and `prim_basis_from_minors`'
`∏ℛ ≤ 2^{1-ρ}(ρ!)²r^ρ|Δ_J|∏_J a_i` gives exactly the theorem's two alternatives with
`constA r ρ = 2^{1-ρ}(ρ!)²r^ρ (r+1).descFactorial ρ` (case `ε=true`, `k = ρ`) and
`constB r ρ = 2^{1-ρ}(ρ!)²r^ρ (r+1).descFactorial (ρ+1)` (case `ε=false`, `k = ρ+1`).
So the constant bookkeeping is right; **no weakening of `constA`/`constB` is needed**, and
`one_le_cardMod` is not the right tool (the bound `cardMod ≥ Sq m + 1` from the collision analysis is).

**Case analysis (`ℓ = k-1`; design step 4) checked.** With `W = span (e₀, (0,c_m))`
(`dim W = r`, the `c_m` being ℚ-independent) and `G' = G_a^ε × ker 𝒵`:
`W ⊓ Lie G' = ℂe₀ ⊕ (span c ⊓ (span M)^⊥)` for `ε = true` (and `= span c ⊓ (span M)^⊥` for
`ε = false`); hence `ℓ = ellW w ε M` equals `(r-1) - dim(span c ⊓ (span M)^⊥)` resp.
`r - dim(span c ⊓ (span M)^⊥)`. So `ℓ = k-1` (`k = ρ` resp. `k = 1+ρ`) is equivalent to
`(span M)^⊥ ⊆ span c`, i.e. to `(span c)^⊥ ⊆ span M`, and since `B ≠ 0` is orthogonal to every
`c_m` (hypothesis `hcB`) we get `(span c)^⊥ = ℂ·B` and therefore **`B ∈ ℚ-span M`** — exactly the
second requirement of the conclusion. (So the case analysis is sound; only the two `sorry`'d
siblings and the quantitative collision analysis via (E0)–(E3) remain.)

**Blocking.** `zero_estimate_stepwise` (P86*) and `prim_basis_from_minors` are dispatched siblings
and are still `sorry`; this file's theorem cannot be *verified* before they land, since its proof
is an assembly over their statements (nothing about the statement itself is in doubt).
-/

/-- `hvan` (stated with `ptS`/`applyDer`) implies the vanishing hypothesis of
`zero_estimate_stepwise` (stated with `ptTheta θ`, `θ = exp ∘ ℓ`, and `applyW` with
`w = (e₀, (0, c m))`): take `t0 = 0` and use `hSsum`, `hTsum`. This is the instantiation the
assembly performs. -/
lemma ze_hvan_of_hvan {r : ℕ} (P : MvPolynomial (Fin (r+1)) ℂ) (ℓ : Fin r → ℂ)
    (c : Fin (r-1) → Fin r → ℚ) (𝒮 𝒯 : ℝ) (Sq Tq : ℕ → ℕ)
    (hSsum : ((∑ m ∈ Finset.range (r+1), Sq m : ℕ) : ℝ) ≤ 𝒮)
    (hTsum : ((∑ m ∈ Finset.range (r+1), Tq m : ℕ) : ℝ) ≤ 𝒯)
    (hvan : ∀ s : ℕ, (s:ℝ) ≤ 𝒮 → ∀ (t0 : ℕ) (t : Fin (r-1) → ℕ),
      ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ 𝒯 →
      MvPolynomial.eval (ptS ℓ s) (applyDer c t0 t P) = 0) :
    ∀ s : ℕ, s ≤ ∑ m ∈ Finset.range (r+1), Sq m → ∀ t : Fin (r-1) → ℕ,
      ∑ k, t k ≤ ∑ m ∈ Finset.range (r+1), Tq m →
      MvPolynomial.eval (ptTheta (fun i => Complex.exp (ℓ i)) s)
        (applyW (N := r) (q := r-1)
          (fun m => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))) t P) = 0 := by
  intro s hs t ht
  have hs' : (s : ℝ) ≤ 𝒮 := le_trans (by exact_mod_cast hs) hSsum
  have ht' : ((0 + ∑ m, t m : ℕ) : ℝ) ≤ 𝒯 := by
    have h1 : ((∑ k, t k : ℕ) : ℝ) ≤ ((∑ m ∈ Finset.range (r+1), Tq m : ℕ) : ℝ) := by
      exact_mod_cast ht
    simpa using le_trans h1 hTsum
  have hw : applyW (N := r) (q := r-1)
      (fun m => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))) t P = applyDer c 0 t P := by
    have h := applyDer_eq_pderiv_applyW c 0 t P
    simpa only [Function.iterate_zero, id_eq] using h
  rw [← ptS_eq_ptTheta, hw]
  exact hvan s hs' 0 t ht'

/-- `hΛ` forces the budget to be positive: if `𝒮 ≤ 0` then `π/𝒮 ≤ 0`, contradicting
`‖·‖ < π/𝒮`. -/
lemma Spos_of_hLambda {r : ℕ} (B : Fin r → ℤ) (ℓ : Fin r → ℂ) (𝒮 : ℝ)
    (hΛ : ‖∑ i, (B i : ℂ) * ℓ i‖ < Real.pi / 𝒮) : 0 < 𝒮 := by
  by_contra h
  have h𝒮 : 𝒮 ≤ 0 := not_lt.mp h
  have hle : Real.pi / 𝒮 ≤ 0 := by
    rcases lt_or_eq_of_le h𝒮 with h' | h'
    · exact le_of_lt (div_neg_of_pos_of_neg Real.pi_pos h')
    · rw [h', div_zero]
  have hnn : (0 : ℝ) ≤ ‖∑ i, (B i : ℂ) * ℓ i‖ := norm_nonneg _
  linarith

/-- The vanishing hypothesis of `zero_estimate_stepwise` at level `N = r`, in the operator family
`w = (e₀, (0, c_m))` (which contains `∂₀`, unlike the family used in `ze_hvan_of_hvan`). -/
lemma ze_hvan_full {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) (ℓ : Fin r → ℂ)
    (c : Fin (r - 1) → Fin r → ℚ) (𝒮 𝒯 : ℝ) (Sq Tq : ℕ → ℕ)
    (hSsum : ((∑ m ∈ Finset.range (r + 1), Sq m : ℕ) : ℝ) ≤ 𝒮)
    (hTsum : ((∑ m ∈ Finset.range (r + 1), Tq m : ℕ) : ℝ) ≤ 𝒯)
    (hvan : ∀ s : ℕ, (s : ℝ) ≤ 𝒮 → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
      ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ 𝒯 →
      MvPolynomial.eval (ptS ℓ s) (applyDer c t0 t P) = 0) :
    ∀ s : ℕ, s ≤ ∑ m ∈ Finset.range (r + 1), Sq m → ∀ t : Fin (r - 1 + 1) → ℕ,
      ∑ k, t k ≤ ∑ m ∈ Finset.range (r + 1), Tq m →
      MvPolynomial.eval (ptTheta (fun i => Complex.exp (ℓ i)) s)
        (applyW (N := r) (q := r - 1 + 1)
          (Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
            (fun m : Fin (r - 1) => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ)))) t P) = 0 := by
  intro s hs t ht
  have hs' : (s : ℝ) ≤ 𝒮 := le_trans (by exact_mod_cast hs) hSsum
  have htsum : (∑ k : Fin (r - 1 + 1), t k) = t 0 + ∑ m : Fin (r - 1), t m.succ :=
    Fin.sum_univ_succ t
  have ht' : ((t 0 + ∑ m : Fin (r - 1), t m.succ : ℕ) : ℝ) ≤ 𝒯 := by
    rw [← htsum]
    exact le_trans (by exact_mod_cast ht) hTsum
  rw [← ptS_eq_ptTheta, applyW_cons_eq_applyDer c t P]
  exact hvan s hs' (t 0) (fun m => t m.succ) ht'

/-- `1 ≤ ⌊𝒟 i⌋₊` from the two degree hypotheses of `multiplicity_prop`. -/
lemma one_le_floor_of {r : ℕ} {𝒟 : Fin (r + 1) → ℝ} (h𝒟0 : 1 ≤ 𝒟 0)
    (hnd : ∀ j : Fin r, 1 ≤ 𝒟 j.succ) : ∀ i : Fin (r + 1), 1 ≤ ⌊𝒟 i⌋₊ := by
  intro i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact Nat.le_floor (by exact_mod_cast h𝒟0)
  · exact Nat.le_floor (by exact_mod_cast hnd j)

/-- **Non-degenerate hypothesis package.** If every torus degree is at least `1`, the data of
`multiplicity_prop` at level `N = r` with `δ = 𝒟` is a valid `ZEData r r`. -/
noncomputable def zedata_nondegenerate {r : ℕ} (hr : 2 ≤ r) (𝒟 : Fin (r + 1) → ℝ)
    (hδnn : ∀ i, 0 ≤ 𝒟 i) (h𝒟0 : 1 ≤ 𝒟 0) (hnd : ∀ j : Fin r, 1 ≤ 𝒟 j.succ)
    (𝒮 : ℝ) (hSpos : 0 < 𝒮) (Sq Tq : ℕ → ℕ)
    (hSa : ∀ m, m < r → Sq (m + 1) ≤ Sq m) (hTa : ∀ m, m < r → Tq (m + 1) ≤ Tq m)
    (hSsum : ((∑ m ∈ Finset.range (r + 1), Sq m : ℕ) : ℝ) ≤ 𝒮)
    (hE0 : ∀ j : Fin r, ((r : ℝ) + 1) * 𝒟 j.succ < (Tq 0 : ℝ) + 1)
    (hE1 : ∀ m, m < r → ∀ e : Fin (r + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, 𝒟 i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ))
    (hE2 : ((r + 1).factorial : ℝ) * ∏ i, 𝒟 i < ((Sq r : ℝ) + 1) * ((Tq r + r).choose r : ℝ))
    (hE3 : ((r + 1).factorial : ℝ) * ∏ i : Fin r, 𝒟 i.succ <
      ((Sq (r - 1) : ℝ) + 1) * ((Tq (r - 1) + (r - 1)).choose (r - 1) : ℝ))
    (B : Fin r → ℤ) (hB : B ≠ 0) (ℓ : Fin r → ℂ) (hℓ : LinearIndependent ℚ ℓ)
    (hΛ : ‖∑ i, (B i : ℂ) * ℓ i‖ < Real.pi / 𝒮) : ZEData r r := by
  have hE2' : ((r + 1).factorial : ℝ) * ∏ i : Fin (r + 1), ((⌊𝒟 i⌋₊ : ℕ) : ℝ) <
      ((Sq r : ℝ) + 1) * ((Tq r + r).choose r : ℝ) := by
    have hle : (∏ i : Fin (r + 1), ((⌊𝒟 i⌋₊ : ℕ) : ℝ)) ≤ ∏ i : Fin (r + 1), 𝒟 i :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => Nat.floor_le (hδnn i))
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle (by positivity)) hE2
  have hE3' : ((r + 1).factorial : ℝ) * ∏ i : Fin r, ((⌊𝒟 i.succ⌋₊ : ℕ) : ℝ) <
      ((Sq (r - 1) : ℝ) + 1) * ((Tq (r - 1) + (r - 1)).choose (r - 1) : ℝ) := by
    have hle : (∏ i : Fin r, ((⌊𝒟 i.succ⌋₊ : ℕ) : ℝ)) ≤ ∏ i : Fin r, 𝒟 i.succ :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => Nat.floor_le (hδnn i.succ))
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle (by positivity)) hE3
  exact
  { hNr := le_rfl
    hr := hr
    δ := 𝒟
    hδnn := hδnn
    hδ0 := h𝒟0
    hδ1 := one_le_floor_of h𝒟0 hnd
    𝒮 := 𝒮
    hSpos := hSpos
    Sq := Sq
    Tq := Tq
    hSa := hSa
    hTa := hTa
    hSsum := hSsum
    hE0 := hE0
    hE1 := hE1
    hE2 := fun _ => hE2'
    hE3 := fun _ => hE3'
    B := B
    hB := hB
    ℓ := ℓ
    hℓ := hℓ
    hΛ := hΛ }

/-- `ellW_dichotomy` in the form consumed by `ze_engine` (with `(if ε then 0 else 1) + ρ - 1`
instead of `(if ε then ρ else ρ + 1) - 1`). -/
lemma ldich_of_dichotomy {r : ℕ} (hr : 2 ≤ r) (ρ : ℕ) (hρr : ρ ≤ r)
    (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ c)
    (M : Fin ρ → Fin r → ℤ) (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ))) (ε : Bool) :
    ellW (N := r) (q := r - 1 + 1)
        (Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
          (fun m : Fin (r - 1) => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ)))) ε M =
      (if ε then 0 else 1) + ρ - 1 ∨
    ellW (N := r) (q := r - 1 + 1)
        (Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
          (fun m : Fin (r - 1) => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ)))) ε M =
      (if ε then 0 else 1) + ρ := by
  have h := ellW_dichotomy hr hρr c hc M hM ε
    (Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
      (fun m : Fin (r - 1) => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))))
    (Fin.cons_zero _ _) (fun m => Fin.cons_succ _ _ m)
  rcases h with h | h
  · left
    rw [h]
    rcases ε with _ | _ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · right
    rw [h]
    rcases ε with _ | _ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The minor of a `0 × N` matrix on an empty column set is `1`. -/
lemma minorJ_zero {N ρ : ℕ} {M : Fin ρ → Fin N → ℤ} {J : Finset (Fin N)} (hJ : J.card = ρ)
    (h0 : J.card = 0) : minorJ M J hJ = 1 := by
  obtain rfl : J = ∅ := Finset.card_eq_zero.mp h0
  have hρ : ρ = 0 := by
    rw [← hJ]
    simp
  subst hρ
  rw [minorJ]
  exact Matrix.det_fin_zero

/-- **The non-degenerate case of `multiplicity_prop`.** The mathematics is entirely in
`ze_engine`; here we build the hypothesis package, run `zero_estimate_stepwise` in the operator
family `w = (e₀, (0, c_m))` (which contains `∂₀`) and feed its output to the engine. `hmin` is the
interface to `prim_basis_from_minors`. -/
theorem mp_main {r : ℕ} (hr : 2 ≤ r) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : P ≠ 0) (𝒟 : Fin (r + 1) → ℝ) (hdeg : ∀ j, (P.degreeOf j : ℝ) ≤ 𝒟 j)
    (h𝒟0 : 1 ≤ 𝒟 0) (𝒮 𝒯 : ℝ) (Sq Tq : ℕ → ℕ) (hSa : ∀ m, m < r → Sq (m + 1) ≤ Sq m)
    (hTa : ∀ m, m < r → Tq (m + 1) ≤ Tq m)
    (hSsum : ((∑ m ∈ Finset.range (r + 1), Sq m : ℕ) : ℝ) ≤ 𝒮)
    (hTsum : ((∑ m ∈ Finset.range (r + 1), Tq m : ℕ) : ℝ) ≤ 𝒯)
    (hnd : ∀ j : Fin r, 1 ≤ 𝒟 j.succ)
    (hE0 : ∀ j : Fin r, ((r : ℝ) + 1) * 𝒟 j.succ < (Tq 0 : ℝ) + 1)
    (hE1 : ∀ m, m < r → ∀ e : Fin (r + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, 𝒟 i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ))
    (hE2 : ((r + 1).factorial : ℝ) * ∏ i, 𝒟 i < ((Sq r : ℝ) + 1) * ((Tq r + r).choose r : ℝ))
    (hE3 : ((r + 1).factorial : ℝ) * ∏ i : Fin r, 𝒟 i.succ <
      ((Sq (r - 1) : ℝ) + 1) * ((Tq (r - 1) + (r - 1)).choose (r - 1) : ℝ))
    (B : Fin r → ℤ) (hB : B ≠ 0) (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ c)
    (hcB : ∀ m, ∑ i, c m i * (B i : ℚ) = 0) (ℓ : Fin r → ℂ) (hℓ : LinearIndependent ℚ ℓ)
    (hΛ : ‖∑ i, (B i : ℂ) * ℓ i‖ < Real.pi / 𝒮)
    (hvan : ∀ s : ℕ, (s : ℝ) ≤ 𝒮 → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
      ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ 𝒯 →
      MvPolynomial.eval (ptS ℓ s) (applyDer c t0 t P) = 0)
    (hmin : ∀ (ρ : ℕ), 1 ≤ ρ → ρ ≤ r → ∀ (M : Fin ρ → Fin r → ℤ), PrimSys M →
      ∀ (a : Fin r → ℝ), (∀ i, 0 < a i) →
      ∀ (J₀ : Finset (Fin r)) (hJ₀ : J₀.card = ρ),
        (∀ (I : Finset (Fin r)) (hI : I.card = ρ),
          |(minorJ M I hI : ℝ)| * ∏ i ∈ I, a i ≤ |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i) →
        ∃ M' : Fin ρ → Fin r → ℤ, PrimSys M' ∧
          Submodule.span ℤ (Set.range M') = Submodule.span ℤ (Set.range M) ∧
          (∏ j, ∑ i, a i * |(M' j i : ℝ)|) ≤
            (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (r : ℝ) ^ ρ *
              |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i) :
    ∃ ρ : ℕ, 1 ≤ ρ ∧ ρ < r ∧ ∀ a : Fin r → ℝ, (∀ i, 0 < a i) →
      ∃ M : Fin ρ → Fin r → ℤ, PrimSys M ∧
        (fun i => (B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M j i : ℚ)) ∧
        ∃ J : Finset (Fin r), J.card = ρ ∧
          ((∏ j, ∑ i, a i * |(M j i : ℝ)|) * ((Sq (ρ - 1) : ℝ) + 1) *
                ((Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ) ≤
              constA r ρ * ∏ i ∈ J, (a i * 𝒟 i.succ) ∨
            (∏ j, ∑ i, a i * |(M j i : ℝ)|) * ((Sq ρ : ℝ) + 1) * ((Tq ρ + ρ).choose ρ : ℝ) ≤
              constB r ρ * 𝒟 0 * ∏ i ∈ J, (a i * 𝒟 i.succ)) := by
  classical
  have hδnn : ∀ i : Fin (r + 1), 0 ≤ 𝒟 i := fun i => le_trans (Nat.cast_nonneg _) (hdeg i)
  have hSpos : 0 < 𝒮 := Spos_of_hLambda B ℓ 𝒮 hΛ
  let hD : ZEData r r :=
    zedata_nondegenerate hr 𝒟 hδnn h𝒟0 hnd 𝒮 hSpos Sq Tq hSa hTa hSsum hE0 hE1 hE2 hE3 B hB ℓ hℓ
      hΛ
  set w : Fin (r - 1 + 1) → Fin (r + 1) → ℂ :=
    Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
      (fun m : Fin (r - 1) => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))) with hw
  have hw0 : w 0 = Pi.single (0 : Fin (r + 1)) (1 : ℂ) := by rw [hw]; exact Fin.cons_zero _ _
  have hw1 : ∀ m : Fin (r - 1), w m.succ = Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ)) := by
    intro m; rw [hw]; exact Fin.cons_succ _ _ m
  have hθ : ∀ i : Fin r, Complex.exp (ℓ i) ≠ 0 := fun i => Complex.exp_ne_zero (ℓ i)
  obtain ⟨ε, ρ, M, hρr, hM, hε0, m, hm, hineq⟩ :=
    zero_estimate_stepwise (N := r) (q := r - 1 + 1) P hP (fun i => ⌊𝒟 i⌋₊)
      (one_le_floor_of h𝒟0 hnd) (fun i => Nat.le_floor (hdeg i)) w (fun i => Complex.exp (ℓ i)) hθ
      Sq Tq (ze_hvan_full P ℓ c 𝒮 𝒯 Sq Tq hSsum hTsum hvan)
  have hLpos : ε = false → 1 ≤ ellW w ε M := by
    intro hε
    rw [hε, hw]
    exact one_le_ellW_false c ρ M
  have hLdich := ldich_of_dichotomy hr ρ hρr c hc M hM.1 ε
  have hGoodB : ellW w ε M = (if ε then 0 else 1) + ρ - 1 →
      (fun i => (B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M j i : ℚ)) := by
    intro hL
    have hρ1 : 1 ≤ ρ := by
      by_contra hlt
      have h0 : ρ = 0 := by omega
      rcases ε with _ | _
      · have h1 := hLpos rfl
        have h2 : ellW w false M = 0 := by
          have h3 : (if (false : Bool) = true then (0 : ℕ) else 1) + ρ - 1 = 0 := by
            rw [h0]
            simp
          exact hL.trans h3
        omega
      · exact hε0 ⟨rfl, h0⟩
    have hL' : ellW w ε M = (if ε then ρ else ρ + 1) - 1 := by
      rw [hL]
      rcases ε with _ | _ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    exact ellW_B_mem_span hr hρ1 hρr c hc M hM.1 B hB hcB ε w hw0 hw1 hL'
  have hminr : ∀ (a : Fin r → ℝ), (∀ i, 0 < a i) →
      ∀ (J₀ : Finset (Fin r)) (hJ₀ : J₀.card = ρ),
        (∀ (I : Finset (Fin r)) (hI : I.card = ρ),
          |(minorJ M I hI : ℝ)| * ∏ i ∈ I, a i ≤ |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i) →
        ∃ M' : Fin ρ → Fin r → ℤ, PrimSys M' ∧
          Submodule.span ℤ (Set.range M') = Submodule.span ℤ (Set.range M) ∧
          (∏ j, ∑ i, a i * |(M' j i : ℝ)|) ≤
            (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (r : ℝ) ^ ρ *
              |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i := by
    intro a ha J₀ hJ₀ hmax
    rcases Nat.eq_zero_or_pos ρ with h0 | hρ1
    · subst h0
      refine ⟨M, hM, rfl, ?_⟩
      have hΔ : minorJ M J₀ hJ₀ = 1 := minorJ_zero hJ₀ hJ₀
      have hJ0' : J₀ = ∅ := Finset.card_eq_zero.mp hJ₀
      have hleft : (∏ j : Fin 0, ∑ i : Fin r, a i * |(M j i : ℝ)|) = 1 := by simp
      have hright : (2 : ℝ) ^ (1 - ((0 : ℕ) : ℤ)) * (((0 : ℕ).factorial : ℝ) ^ 2) *
          (r : ℝ) ^ (0 : ℕ) * |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i = 2 := by
        rw [hΔ, hJ0']
        norm_num
      rw [hleft, hright]
      norm_num
    · exact hmin ρ hρ1 hρr M hM a ha J₀ hJ₀ hmax
  obtain ⟨ρ', hρ'1, hρ'r, hconcl⟩ :=
    ze_engine hD ε ρ M m (ellW w ε M) hρr hM hε0 hm hLdich hLpos hGoodB hminr hineq
  exact ⟨ρ', hρ'1, hρ'r, hconcl⟩

/-- **The degenerate case of `multiplicity_prop`.** When some coordinate has `𝒟 i.succ < 1`,
`P` has degree `0` in `Y_{i+1}`. `B_eq_zero_of_deg_lt_one` first shows that `B` vanishes on every
degenerate coordinate; `quotient_reduction_core` then drops those coordinates (renaming `P` to
`P'` with `P = rename (liftIdx σ) P'`) and transports the vanishing of `applyDer` to the vanishing
of `applyW` for the restricted family `w = (e₀, (0, c m ∘ σ))` at level `N' < r`; the engine
`ze_engine` runs at that level with `B ∘ σ`, and `mp_pullback` returns the conclusion to level
`r` via `M = extM σ M'`, `J = J'.map σ`. -/
theorem mp_degenerate {r : ℕ} (hr : 2 ≤ r) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : P ≠ 0) (𝒟 : Fin (r + 1) → ℝ) (hdeg : ∀ j, (P.degreeOf j : ℝ) ≤ 𝒟 j)
    (h𝒟0 : 1 ≤ 𝒟 0) (𝒮 𝒯 : ℝ) (Sq Tq : ℕ → ℕ) (hSa : ∀ m, m < r → Sq (m + 1) ≤ Sq m)
    (hTa : ∀ m, m < r → Tq (m + 1) ≤ Tq m)
    (hSsum : ((∑ m ∈ Finset.range (r + 1), Sq m : ℕ) : ℝ) ≤ 𝒮)
    (hTsum : ((∑ m ∈ Finset.range (r + 1), Tq m : ℕ) : ℝ) ≤ 𝒯)
    (hE0 : ∀ j : Fin r, ((r : ℝ) + 1) * 𝒟 j.succ < (Tq 0 : ℝ) + 1)
    (hE1 : ∀ m, m < r → ∀ e : Fin (r + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, 𝒟 i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ))
    (hE2 : ((r + 1).factorial : ℝ) * ∏ i, 𝒟 i < ((Sq r : ℝ) + 1) * ((Tq r + r).choose r : ℝ))
    (hE3 : ((r + 1).factorial : ℝ) * ∏ i : Fin r, 𝒟 i.succ <
      ((Sq (r - 1) : ℝ) + 1) * ((Tq (r - 1) + (r - 1)).choose (r - 1) : ℝ))
    (B : Fin r → ℤ) (hB : B ≠ 0) (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ c)
    (hcB : ∀ m, ∑ i, c m i * (B i : ℚ) = 0) (ℓ : Fin r → ℂ) (hℓ : LinearIndependent ℚ ℓ)
    (hΛ : ‖∑ i, (B i : ℂ) * ℓ i‖ < Real.pi / 𝒮)
    (hvan : ∀ s : ℕ, (s : ℝ) ≤ 𝒮 → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
      ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ 𝒯 →
      MvPolynomial.eval (ptS ℓ s) (applyDer c t0 t P) = 0)
    (hdg : ∃ i : Fin r, 𝒟 i.succ < 1) :
    ∃ ρ : ℕ, 1 ≤ ρ ∧ ρ < r ∧ ∀ a : Fin r → ℝ, (∀ i, 0 < a i) →
      ∃ M : Fin ρ → Fin r → ℤ, PrimSys M ∧
        (fun i => (B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M j i : ℚ)) ∧
        ∃ J : Finset (Fin r), J.card = ρ ∧
          ((∏ j, ∑ i, a i * |(M j i : ℝ)|) * ((Sq (ρ - 1) : ℝ) + 1) *
                ((Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ) ≤
              constA r ρ * ∏ i ∈ J, (a i * 𝒟 i.succ) ∨
            (∏ j, ∑ i, a i * |(M j i : ℝ)|) * ((Sq ρ : ℝ) + 1) * ((Tq ρ + ρ).choose ρ : ℝ) ≤
              constB r ρ * 𝒟 0 * ∏ i ∈ J, (a i * 𝒟 i.succ)) := by
  classical
  obtain ⟨i, hi⟩ := hdg
  have hBZdeg : ∀ k : Fin r, 𝒟 k.succ < 1 → B k = 0 := fun k hk =>
    B_eq_zero_of_deg_lt_one hr P hP 𝒟 hdeg h𝒟0 𝒮 𝒯 Sq Tq hSa hTa hSsum hTsum hE0 hE1 hE2 hE3
      B hB c hc hcB ℓ hℓ hΛ hvan k hk
  obtain ⟨N', σ, P', δ, w, hN'lt, hσmono, hσdeg, hP'ne, hδnn, hδ0, hδ1, hdeg', hδeq, hw1, hw0,
      hvan'⟩ := quotient_reduction_core P hP 𝒟 hdeg h𝒟0 Sq Tq 𝒮 𝒯 hSsum hTsum c ℓ hvan i hi
  have hσinj : Function.Injective σ := hσmono.injective
  have hBZ : ∀ k, k ∉ Set.range σ → B k = 0 := fun k hk => hBZdeg k (hσdeg k hk)
  have hBσ : (fun j => B (σ j)) ≠ 0 := by
    intro h0; apply hB; funext k
    by_cases hk : k ∈ Set.range σ
    · obtain ⟨j, rfl⟩ := hk; exact congr_fun h0 j
    · exact hBZ k hk
  have hΛσ : ‖∑ j, ((B (σ j) : ℤ) : ℂ) * ℓ (σ j)‖ < Real.pi / 𝒮 := by
    have h : ∑ k, (B k : ℂ) * ℓ k = ∑ j, ((B (σ j) : ℤ) : ℂ) * ℓ (σ j) :=
      zeroDeg_sum_range_eq σ hσinj (fun k => (B k : ℂ) * ℓ k) (fun k hk => by simp [hBZ k hk])
    rw [← h]; exact hΛ
  have hSpos : 0 < 𝒮 := Spos_of_hLambda B ℓ 𝒮 hΛ
  have hsub : Finset.range (N' + 1) ⊆ Finset.range (r + 1) := Finset.range_mono (by omega)
  have hSsum' : ((∑ m ∈ Finset.range (N' + 1), Sq m : ℕ) : ℝ) ≤ 𝒮 :=
    le_trans (by exact_mod_cast Finset.sum_le_sum_of_subset hsub) hSsum
  have hE1δ : ∀ m, m < r → ∀ e : Fin (N' + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, δ i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ) := by
    intro m hm e he hs
    have h := hE1_extend σ hσmono 𝒟 Sq Tq m hm hE1 e he hs
    simpa only [← hδeq] using h
  let D : ZEData N' r :=
    { hNr := hN'lt.le, hr := hr, δ := δ, hδnn := hδnn, hδ0 := hδ0, hδ1 := hδ1, 𝒮 := 𝒮,
      hSpos := hSpos, Sq := Sq, Tq := Tq, hSa := fun m hm => hSa m (by omega),
      hTa := fun m hm => hTa m (by omega), hSsum := hSsum',
      hE0 := fun j => by rw [hδeq, zeroDeg_liftIdx_succ]; exact hE0 (σ j),
      hE1 := hE1δ, hE2 := fun h => absurd h (by omega), hE3 := fun h => absurd h (by omega),
      B := fun j => B (σ j), hB := hBσ, ℓ := fun j => ℓ (σ j), hℓ := hℓ.comp σ hσinj,
      hΛ := hΛσ }
  obtain ⟨ε, ρ, M, hρN, hM, hε0, m, hm, hineq⟩ :=
    zero_estimate_stepwise (N := N') (q := r - 1 + 1) P' hP'ne (fun j => ⌊δ j⌋₊) hδ1 hdeg' w
      (fun j => Complex.exp (ℓ (σ j))) (fun j => Complex.exp_ne_zero _) Sq Tq hvan'
  obtain ⟨hLdich, hLpos, hGoodB⟩ :=
    reduced_ellW_facts σ hσinj c hc B hB hcB hBZ w hw0 hw1 hρN M hM ε hε0
  have hminr : ∀ (a : Fin N' → ℝ), (∀ i, 0 < a i) →
      ∀ (J₀ : Finset (Fin N')) (hJ₀ : J₀.card = ρ),
        (∀ (I : Finset (Fin N')) (hI : I.card = ρ),
          |(minorJ M I hI : ℝ)| * ∏ i ∈ I, a i ≤ |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i) →
        ∃ M' : Fin ρ → Fin N' → ℤ, PrimSys M' ∧
          Submodule.span ℤ (Set.range M') = Submodule.span ℤ (Set.range M) ∧
          (∏ j, ∑ i, a i * |(M' j i : ℝ)|) ≤
            (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (N' : ℝ) ^ ρ *
              |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i := by
    intro a ha J₀ hJ₀ hmax
    rcases Nat.eq_zero_or_pos ρ with h0 | hρ1
    · subst h0
      refine ⟨M, hM, rfl, ?_⟩
      have hΔ : minorJ M J₀ hJ₀ = 1 := minorJ_zero hJ₀ hJ₀
      have hJ0' : J₀ = ∅ := Finset.card_eq_zero.mp hJ₀
      have hleft : (∏ j : Fin 0, ∑ i : Fin N', a i * |(M j i : ℝ)|) = 1 := by simp
      have hright : (2 : ℝ) ^ (1 - ((0 : ℕ) : ℤ)) * (((0 : ℕ).factorial : ℝ) ^ 2) *
          (N' : ℝ) ^ (0 : ℕ) * |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i = 2 := by
        rw [hΔ, hJ0']
        norm_num
      rw [hleft, hright]
      norm_num
    · exact prim_basis_from_minors hρ1 hρN M hM a ha J₀ hJ₀ hmax
  have hout := ze_engine D ε ρ M m (ellW w ε M) hρN hM hε0 hm hLdich hLpos hGoodB hminr hineq
  exact mp_pullback σ hσinj 𝒟 δ hδeq Sq Tq B hBZ hout

/-- BW §10 Proposition, restated for the P86* route. Changes from BW: the budgets are sums
(`∑ 𝒮ₘ ≤ 𝒮`, `∑ 𝒯ₘ ≤ 𝒯`, as on BW p. 32); (5) is replaced by the exclusion conditions (E0)–(E3)
with Philippon's normalisation `(r+1)!/(r-m)!`; `B` is integral; the conclusion has two cases
(`G_a × H'` and `0 × H'`) with constants `constA`, `constB`. Route: reduce to the torus
coordinates with `𝒟ᵢ ≥ 1` (a coordinate with `𝒟ᵢ < 1` has degree `0`, so `P` lives on the
quotient by that `G_m`; `ℓ` is unchanged), apply `zero_estimate_stepwise` with `Dᵢ = ⌊𝒟ᵢ⌋`,
`W = span(∂₀, D_m)`, `Σ_m = {0..Sq m}`, split into cases by `ℓ ∈ {k−1, k}` (`ℓ = k−1 ⇔ B ∈ ℚ𝒵`),
exclude `ℓ = k`, `G_a × 1`, `0 × 1` and point collisions by (E0)–(E3) and `hΛ`, then
`prim_basis_from_minors`. -/
theorem multiplicity_prop {r : ℕ} (hr : 2 ≤ r) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : P ≠ 0) (𝒟 : Fin (r + 1) → ℝ) (hdeg : ∀ j, (P.degreeOf j : ℝ) ≤ 𝒟 j)
    (h𝒟0 : 1 ≤ 𝒟 0) (𝒮 𝒯 : ℝ) (Sq Tq : ℕ → ℕ) (hSa : ∀ m, m < r → Sq (m + 1) ≤ Sq m)
    (hTa : ∀ m, m < r → Tq (m + 1) ≤ Tq m)
    (hSsum : ((∑ m ∈ Finset.range (r + 1), Sq m : ℕ) : ℝ) ≤ 𝒮)
    (hTsum : ((∑ m ∈ Finset.range (r + 1), Tq m : ℕ) : ℝ) ≤ 𝒯)
    (hE0 : ∀ j : Fin r, ((r : ℝ) + 1) * 𝒟 j.succ < (Tq 0 : ℝ) + 1)
    (hE1 : ∀ m, m < r → ∀ e : Fin (r + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, 𝒟 i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ))
    (hE2 : ((r + 1).factorial : ℝ) * ∏ i, 𝒟 i < ((Sq r : ℝ) + 1) * ((Tq r + r).choose r : ℝ))
    (hE3 : ((r + 1).factorial : ℝ) * ∏ i : Fin r, 𝒟 i.succ <
      ((Sq (r - 1) : ℝ) + 1) * ((Tq (r - 1) + (r - 1)).choose (r - 1) : ℝ))
    (B : Fin r → ℤ) (hB : B ≠ 0) (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ c)
    (hcB : ∀ m, ∑ i, c m i * (B i : ℚ) = 0) (ℓ : Fin r → ℂ) (hℓ : LinearIndependent ℚ ℓ)
    (hΛ : ‖∑ i, (B i : ℂ) * ℓ i‖ < Real.pi / 𝒮)
    (hvan : ∀ s : ℕ, (s : ℝ) ≤ 𝒮 → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
      ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ 𝒯 →
      MvPolynomial.eval (ptS ℓ s) (applyDer c t0 t P) = 0) :
    ∃ ρ : ℕ, 1 ≤ ρ ∧ ρ < r ∧ ∀ a : Fin r → ℝ, (∀ i, 0 < a i) →
      ∃ M : Fin ρ → Fin r → ℤ, PrimSys M ∧
        (fun i => (B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M j i : ℚ)) ∧
        ∃ J : Finset (Fin r), J.card = ρ ∧
          ((∏ j, ∑ i, a i * |(M j i : ℝ)|) * ((Sq (ρ - 1) : ℝ) + 1) *
                ((Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ) ≤
              constA r ρ * ∏ i ∈ J, (a i * 𝒟 i.succ) ∨
            (∏ j, ∑ i, a i * |(M j i : ℝ)|) * ((Sq ρ : ℝ) + 1) * ((Tq ρ + ρ).choose ρ : ℝ) ≤
              constB r ρ * 𝒟 0 * ∏ i ∈ J, (a i * 𝒟 i.succ)) := by
  by_cases hnd : ∀ j : Fin r, 1 ≤ 𝒟 j.succ
  · exact mp_main hr P hP 𝒟 hdeg h𝒟0 𝒮 𝒯 Sq Tq hSa hTa hSsum hTsum hnd hE0 hE1 hE2 hE3 B hB c hc
      hcB ℓ hℓ hΛ hvan (fun ρ h1 h2 M hM a ha J hJ hmax =>
        prim_basis_from_minors h1 h2 M hM a ha J hJ hmax)
  · push Not at hnd
    exact mp_degenerate hr P hP 𝒟 hdeg h𝒟0 𝒮 𝒯 Sq Tq hSa hTa hSsum hTsum hE0 hE1 hE2 hE3 B hB c
      hc hcB ℓ hℓ hΛ hvan hnd

end Work.BW
