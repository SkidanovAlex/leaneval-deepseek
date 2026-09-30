import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.solve_adi
import Submission.Work.BMF.n8_defs
-- proved by the fleet for this node (axiom-clean):
import Submission.Work.N8.IntegralOn_gcd
import Submission.Work.N8.lattice_deriv
import Submission.Work.N8.eC_periodic
import Submission.Work.N8.edge_unique
import Submission.Work.N8.quads_from_edges
import Submission.Work.N8.local_finite
import Submission.Work.N8.primes_big
import Submission.Work.N8.greedy_family_sub
import Submission.Work.N8.compatible_pairs_v4
import Submission.Work.N8.approx_ergodicity_strong
import Submission.Work.N8.extract_local
import Submission.Work.N8.aggregate_twist
import Submission.Work.N8.bad_edges_le
import Submission.Work.N8.n4_uniform
import Submission.Work.N8.omega_totient_bound
import Submission.Work.N8.step6_q0_bound_v2
import Submission.Work.N8.edge_sep_800
import Submission.Work.N8.ball_card_le
import Submission.Work.N8.scale_qe
import Submission.Work.N8.scale_bad_edges
import Submission.Work.N8.scale_step6_hyp
import Submission.Work.N8.scales_large
import Submission.Work.N8.exists_psi_set
import Submission.Work.N8.q0_from_bound
import Submission.Work.N8.integral_coeff_denom
import Submission.Work.N8.aggregate_twist_v2
import Submission.Work.N8.omega_le_log_div_log
import Submission.Work.BMF.fam_card_le
import Submission.Work.N8.step6v2_defs
import Submission.Work.BMF.mixing_count
import Submission.Work.BMF.fam_card_le
import Submission.Work.N8.arc_graph_data2
import Submission.Work.N8.scale_c0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 8000000

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/BMF/DESIGN.md (your node's section has exact formulas; N5/N8 were held until solve_adi (N6) was proved: it IS now, Work.BMF.solve_adi, axiom-clean). The statement imports only Defs + solve_adi, because some siblings are still in progress; for the proof add these imports once they build: Submission.Work.BMF.Defs,Submission.Work.BMF.solve_adi,Submission.Work.BMF.mixing_count,Submission.Work.BMF.prime_tuple_count. Shared definitions: Submission/Work/BMF/Defs.lean (do NOT edit). Owned assets: ASSETS.md.

# N8 `global_structure`: from local to global structure, and extraction of the twist

**Sources.**
- MRTTZ §3, from Prop. 3.9 ("prop53-analog") to the end of the section.
- MRT §5 (Lemma 5.1, Cor. 5.2, Props. 5.3–5.6, final paragraph).

**Imports.**
- `Submission.Work.BMF.Defs`
- `Submission.Work.BMF.solve_adi` (N6)
- `Submission.Work.BMF.mixing_count` (N7)
- `Submission.Work.BMF.prime_tuple_count` (N4)

Multiplicativity of `f` is not used. Only the correlation data in `ADIData` is.

## Notation

Scales and counts:
- `X'' = X/(P₁P₂)`, `L = H/(P₁P₂)`, `N = X/H`, `V = A.fam` with `#V ≍ N`.
- `d = π₀(P₁)²`, and `P_x := A.pol x`.
- "Poly size" means `≤ X^{O(1)}`, with the `O(1)` depending on `k, θ, ε, ℓ`.

Moduli:
- `Q_e = ∏ S_e`. Since `#S_e ≥ c π₀(P₂)`, we have `Q_e ≥ (P₂/2)^{cπ₀(P₂)} ≥ exp(X^{ε²/3})`.
- `Q_e` therefore dominates every poly-size quantity. This one fact replaces "`Q` is effectively
  infinite" throughout.

## Step 1: solve every edge (N6)

For `e ∈ A.edges`, `ADIEdge` gives `(a_i, b_i, S_e)`. Apply N6 with:
- `C₀ := C_A`, where `C_A` is the constant carried by `A`;
- `x_i := e.x_i`, `L := L`, `N := X/H`, `Qm := Q_e`.

N6's hypotheses:
- `x_i ≍ NL`: from `IsFam`, `x ∈ [X''/10, 10X'']`.
- `100C₀⁴ ≤ N`.
- `Z^K ≤ Q_e`: holds because `Z ≤ X^{O(ℓ)}` is poly size.

Output: `T_e`, `q_e ≤ X^{O(1)}`, and `γ_{e,1}, γ_{e,2}` with:
- `P_{x_i} = ε_{e,i} + (T_e/2π) log + γ_{e,i}`, where `|ε_{e,i}'| ≤ C/L` on `I_i`;
- `γ_{e,i}` is `(q_e/Q_e)`-integral;
- `γ_{e,1}(p₂·) − γ_{e,2}(p₁·)` is `ℤ`-valued on `ℤ`.

## Step 2: good triples, and their minimal denominators

Fix a small `δ > 0`, depending on `k, θ, ε, c, C, ℓ`. A **good triple at `x ∈ V`** is
`(T, q, γ, 𝒫)` such that:
- `|T| ≤ δ^{-1} N^{k+1}` and `1 ≤ q ≤ X^{1/δ}`;
- `𝒫` is a set of primes in `[P₂/2, P₂]` with `#𝒫 ≥ δπ₀(P₂)`, none dividing `q`;
- `γ` has degree `≤ k` and is `(q/∏𝒫)`-integral;
- `q` is the least `r ≥ 1` with `γ` being `r`-integral;
- `P_x = ε + (T/2π) log + γ` with `|ε'| ≤ δ^{-1}/L` on `[x, x+L]`.

**Bezout lemma** (MRTTZ Lemma 2.2, Appendix B; prove as helper
`IntegralOn_inter`): for coprime `a, b`,
`IntegralOn (λ/a) γ ∧ IntegralOn (λ/b) γ ↔ IntegralOn (λ/(ab)) γ`. Proof: induction on `deg γ`,
peeling the top coefficient with (T2) of N6. Two corollaries:
- The set `{r : IntegralOn r γ}` is closed under `gcd`, so the minimal `r` divides every other.
- From N6's `(q_e/Q_e)`-integrality and minimality of `q = q(γ)`, we get `q ∣ q_e`. Remove from
  `S_e` the `O(1)` primes dividing `q_e`, leaving `S'_e` (at most `log q_e / log(P₂/2) = O(1)`
  primes). Bezout with `λ = q_e`, `a = ∏S'_e`, `b = q_e/q` then gives `(q/∏S'_e)`-integrality.

So each edge produces good triples at both endpoints, with the **same** `T = T_e`.

## Step 3: boundedly many essentially distinct triples per interval (MRTTZ Prop. 3.9)

Let `(T_j, q_j, γ_j, 𝒫_j)`, `j = 1..K`, be good triples at `x`, with `K ≥ K(δ)`.

- Pigeonhole: some `j ≠ j'` have `#(𝒫_j ∩ 𝒫_{j'}) ≥ c_δ π₀(P₂)`. Put `Π := ∏(𝒫_j ∩ 𝒫_{j'})`.
- Differentiate `P_x` both ways at a point `t₀ ∈ [x, x+L]` of the lattice `(q_jq_{j'}/Π)ℤ`. Then
  `(T_j − T_{j'})/(2πt₀) = O(1/L) + (γ_{j'} − γ_j)'(t₀)`.
- By (T3) of N6, `(γ_{j'} − γ_j)'(t₀) ∈ (Π/(q_j q_{j'} k!))ℤ`, and `Π` is huge. So
  `T_j − T_{j'} = O(N)`, and `(γ_j − γ_{j'})' = O(1/L)` on `[x, x+L]`.
- Bernstein: `(γ_j − γ_{j'})^{(l)} = O(L^{-l})`. These derivatives at lattice points also lie in a
  huge lattice, so they vanish. Hence `γ_j − γ_{j'}` is a constant, necessarily an integer.
- Minimality then gives `q_j = q_{j'}`.

**Greedy (MRT Cor. 5.4).** There is `ℱ(x)` with `#ℱ(x) ≤ K(δ)` such that every good triple at `x`
equals some `(T', q, γ') ∈ ℱ(x)` up to `T = T' + O(N)` and `γ ≡ γ' mod ℤ`.

## Step 4: compatible pairs along edges (MRTTZ Prop. 3.11)

For `≫ dN` edges `e = (x₁, x₂, p₁, p₂)` there are `(T_i, q, γ_i) ∈ ℱ(x_i)` with:
- `T₂ = T₁ + O(N)`, the same `q`, and `p₁, p₂ ∤ q`;
- `γ₁(p₂·) ≡ γ₂(p₁·) mod Poly(ℤ → ℤ)`.

Details:
- Edges with `p_i ∣ q_j` number `O(N π₀(P₁))`, which is negligible.
- `q₁ = q₂`: `γ₂` is `p₂q₁`-integral, so `q₂ ∣ p₂q₁` by the Bezout corollary. Symmetrically
  `q₁ ∣ p₁q₂`. Coprimality then gives `q₁ = q₂`.

## Step 5: approximate ergodicity (MRT Cor. 5.2), using N7

Metric on triples: `dist((T,q,γ), (T',q',γ')) := c(δ)|T − T'|/N + 1_{q≠q'}`. Drop the `γ` term
from MRT: it is not needed for polynomial phases. Radius `r = 1/10`. Balls have bounded doubling
`M = O(1/c(δ))`.

Apply the corollary's proof verbatim to the sextuples from Step 4. The only analytic input is N7:
- `A₁, A₂ ⊆ V`, which are `500L`-separated, hence `L`-separated;
- mixing scale `X''` and prime scale `P₁`;
- `c₀ := min(θ/2, ε²/2)/2`, checked against `X''^{c₀} ≤ P₁ ≤ X''^{1/4}` and
  `X''^{c₀} ≤ L ≤ X''` for large `X`.

The alternative "`MK³/δ ≫ log^{100} P₁`" is impossible for large `X`. Hence there are `T₀`, `q₀`,
and `𝒯 ⊆ {(x, z) : z ∈ ℱ(x)}` with:
- `#𝒯 ≫ N`, and every `(x, T, q, γ) ∈ 𝒯` has `q = q₀`, `T = T₀ + O(N)`;
- `≫ dN` edges inside `𝒯` satisfying Step 4.

Since `|T| ≤ δ^{-1}N^{k+1}`, also `|T₀| ≪ N^{k+1}`.

## Step 6: `q₀ ≪ 1` (MRTTZ Prop. 3.13, MRT Prop. 5.6), using N4

Let `ℓ'` be the least even integer with `d^{ℓ'} ≥ N^{2+ε}`.

Lower bound. Blakley–Roy (the helper from N5, step 3) plus Cauchy–Schwarz on the `𝒯`-graph give
`≫ d^{ℓ'}` closed walks `(Q₀, …, Q_{ℓ'−1})`.

Relations around a walk:
- Telescoping the Step 4 relations gives `γ₀(A·) ≡ γ₀(B·) mod Poly(ℤ→ℤ)`, where
  `A = ∏p'_{·,2}` and `B = ∏p'_{·,1}`.
- Iterating the geometry gives `|A − B| ≪ P₁^{ℓ'}/N`.

Choosing a congruence:
- Write `γ₀ = Σ_m (a_m/b_m) t^m` in lowest terms (coefficients are rational since `γ₀` is
  `q₀`-integral).
- Then `γ₀` is `∏b_m`-integral, so `q₀ ≤ ∏b_m`, and some `b_m ≥ q₀^{1/k}` with `m ≥ 1`.
- Coefficients of `Poly_{≤k}(ℤ→ℤ)` lie in `(1/k!)ℤ`. Hence `A^m ≡ B^m (mod q)` with
  `q := b_m / gcd(b_m, k!)`.
- The primes are coprime to `q`: they are `> k` and do not divide `q₀`, and `b_m ∣ k! q₀^m`.

Upper bound. N4 with `(ℓ', m, C₀ = C, q)` bounds the walks by
`N · K(δ)^{ℓ'} · C (d^{ℓ'}/N) ((2m)^{ω(q)}/φ(q) + 1/log N)`, and
`(2m)^{ω(q)}/φ(q) ≪ q^{-1/2}`.

Comparing the two bounds: `q^{-1/2} + 1/log N ≫ 1`, so `q ≪ 1` and `q₀ ≪ 1`.

## Step 7: extraction (MRTTZ, last page of §3)

Fix `(x, T, q₀, γ) ∈ 𝒯`. From `A.corr_ge`, `|corr f P_x x L| ≥ cL`.

Let `H* := c* L` with `c*` small. Averaging over shifts gives
`∫_x^{x+L} |Σ_{n ∈ [y, y+H*]} f(n) e(−P_x(n))| dy ≫ L H*`.

On `[y, y+H*]`, with `P_x = ε + (T/2π) log + γ`:
- `ε(n) = ε(y) + O(c*)`;
- `n^{−iT} = n^{−iT₀} n^{−i(T−T₀)}`, and `(T − T₀) log n = (T − T₀) log y + O(c*)` because
  `|T − T₀| ≤ CN` and `H*/y ≤ c*/N`.

The constant phases disappear inside `| |`. Put `ψ(n) := e(−γ(n))`:
- `γ` is `q₀`-integral, so `γ(n) ∈ (1/(k! q₀^k))ℤ` for `n ∈ ℤ`.
- `ψ` is `r`-periodic with `r := k! q₀^k ≤ R₀`, takes values in `μ_r`, and is `1`-bounded.
- There are at most `r^r` such functions. Pigeonhole a common `ψ` for `≫ N` intervals.

Sum over those intervals. They are disjoint and lie in `[X''/10, 10X'']`, which is covered by 8
dyadic ranges `[Y, 2Y]`. Pigeonhole one `Y` to get `TwistCorr f ψ T₀ Y H' c'` with `H' := H*`.

The remaining output inequalities hold for `X ≥ X₀(Y₀)`:
- `Y ≍ X/(P₁P₂) ∈ [X^{1/2}, X]`, because `P₁P₂ ≤ X^{2ε}`;
- `Y^{θ/2} ≤ H' ≤ Y`, because `H' ≥ c* X^{θ−2ε}`;
- `Y/H' ≤ C' X/H ≤ C' X^{k+1}/H^{k+1}`, because `X ≥ H`;
- `|T₀| ≤ C' N^{k+1} = C' X^{k+1}/H^{k+1}`.

## Size and risk

Size 8–15k. **Risk high.** This is the longest paper-to-Lean distance in the project.

Split it into sub-nodes:
- `good_triple_bounded` (Step 3)
- `compatible_edges` (Step 4)
- `approx_ergodicity` (Step 5, abstract metric version)
- `q0_bounded` (Step 6)
- `extract_twist` (Step 7)

These sub-nodes are internal to the proof of N8 and are not needed in the assembly.
-/

namespace Work.BMF

open Polynomial BoundedMultiplicativeFunctions

open scoped BigOperators

/-- The local structure `(T, q, qf, γ, Ps)` of a good quadruple. -/
abbrev N8Quad := ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ

/-! ## Helper lemmas for the assembly (stage A)

`PolyRel` and `ADIEdge` are monotone in the constant `C`; this lets one upgrade an `ADIData`
whose constant `C` does not satisfy the `10 ≤ C` hypothesis of `quads_from_edges`. -/

/-- `PolyRel` is monotone in `C` (for nonnegative lengths). -/
private lemma PolyRel_mono {k : ℕ} {C C' δ x₁ L₁ x₂ L₂ : ℝ} {P₁ P₂ : ℝ[X]}
    (hC : C ≤ C') (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (h : Work.BMF.PolyRel k C δ x₁ L₁ P₁ x₂ L₂ P₂) :
    Work.BMF.PolyRel k C' δ x₁ L₁ P₁ x₂ L₂ P₂ := by
  obtain ⟨h1, h2, h3, ε, γ, hε, hγ, hP, hεb, hγi⟩ := h
  exact ⟨le_trans h1 (mul_le_mul_of_nonneg_right hC hL₂),
    le_trans h2 (mul_le_mul_of_nonneg_right hC hL₁),
    le_trans h3 (mul_le_mul_of_nonneg_right hC hL₁),
    ε, γ, hε, hγ, hP, fun t ht => le_trans (hεb t ht) hC, hγi⟩

/-- `ADIEdge` is monotone in `C`. -/
lemma ADIEdge_mono {k : ℕ} {c C C' N L P₁ P₂ : ℝ} {ℓ : ℕ} {pol : ℝ → ℝ[X]} {e : Work.BMF.Edge}
    (hC : C ≤ C') (hN : 0 ≤ N) (hL : 0 ≤ L) (hx₁ : 0 ≤ e.x₁) (hx₂ : 0 ≤ e.x₂)
    (h : Work.BMF.ADIEdge k c C N L P₁ P₂ ℓ pol e) :
    Work.BMF.ADIEdge k c C' N L P₁ P₂ ℓ pol e := by
  obtain ⟨a₁, b₁, a₂, b₂, S, hS1, hS2, hb1, hab1, ha1, hb2, hab2, ha2,
    h11, h12, h21, h22, hrel, hpl1, hpl2⟩ := h
  have hb1a1 : (b₁ : ℝ) ≤ (a₁ : ℝ) := by exact_mod_cast le_of_lt hab1
  have hb2a2 : (b₂ : ℝ) ≤ (a₂ : ℝ) := by exact_mod_cast le_of_lt hab2
  have ha₁0 : (0 : ℝ) ≤ (a₁ : ℝ) := Nat.cast_nonneg _
  have ha₂0 : (0 : ℝ) ≤ (a₂ : ℝ) := Nat.cast_nonneg _
  have hp₂ : (0 : ℝ) ≤ (e.p₂ : ℝ) := Nat.cast_nonneg _
  have hp₁ : (0 : ℝ) ≤ (e.p₁ : ℝ) := Nat.cast_nonneg _
  refine ⟨a₁, b₁, a₂, b₂, S, hS1, hS2, hb1, hab1, ha1, hb2, hab2, ha2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (a₁ : ℝ) ≤ C * N * ((a₁ : ℝ) - b₁) := h11
      _ ≤ C' * N * ((a₁ : ℝ) - b₁) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hN) (by linarith)
  · exact le_trans h12 (mul_le_mul_of_nonneg_right hC ha₁0)
  · calc (a₂ : ℝ) ≤ C * N * ((a₂ : ℝ) - b₂) := h21
      _ ≤ C' * N * ((a₂ : ℝ) - b₂) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hN) (by linarith)
  · exact le_trans h22 (mul_le_mul_of_nonneg_right hC ha₂0)
  · refine PolyRel_mono (L₁ := L / (e.p₂ : ℝ)) (L₂ := L / (e.p₁ : ℝ)) hC ?_ ?_ hrel
    · exact div_nonneg hL hp₂
    · exact div_nonneg hL hp₁
  · refine PolyRel_mono (L₁ := L / (a₁ : ℝ)) (L₂ := L / (b₁ : ℝ)) hC ?_ ?_ hpl1
    · exact div_nonneg hL ha₁0
    · exact div_nonneg hL (Nat.cast_nonneg b₁)
  · refine PolyRel_mono (L₁ := L / (a₂ : ℝ)) (L₂ := L / (b₂ : ℝ)) hC ?_ ?_ hpl2
    · exact div_nonneg hL ha₂0
    · exact div_nonneg hL (Nat.cast_nonneg b₂)

/-- Rebuild an `ADIData` with a larger constant `C`. -/
noncomputable def upgradeC {k : ℕ} {f : ℕ → ℂ} {c C C' X L P₁ P₂ : ℝ} {ℓ : ℕ}
    (hC : C ≤ C') (hX : 0 < X) (hL : 0 < L) (hA : Work.BMF.ADIData k f c C X L P₁ P₂ ℓ) :
    Work.BMF.ADIData k f c C' X L P₁ P₂ ℓ :=
  { fam := hA.fam, pol := hA.pol, isFam := hA.isFam, card_ge := hA.card_ge,
    deg := hA.deg, corr_ge := hA.corr_ge,
    edges := hA.edges, edges_card := hA.edges_card, geom := hA.geom,
    adi := fun e he =>
      ADIEdge_mono (C := C) (C' := C') (N := X / L) (L := L) hC
        (le_of_lt (div_pos hX hL)) (le_of_lt hL)
        (by have h := (hA.isFam.1 e.x₁ (hA.geom e he).1).1; linarith)
        (by have h := (hA.isFam.1 e.x₂ (hA.geom e he).2.1).1; linarith)
        (hA.adi e he) }

/-- `GoodQuad` only depends on an `ADIData` through its `fam` and `pol`. -/
lemma GoodQuad_upgradeC {k : ℕ} {f : ℕ → ℂ} {c C C' X L P₁ P₂ δ : ℝ} {ℓ : ℕ}
    (hC : C ≤ C') (hX : 0 < X) (hL : 0 < L) (hA : Work.BMF.ADIData k f c C X L P₁ P₂ ℓ)
    {x T : ℝ} {q qf : ℕ} {γ : ℝ[X]} {Ps : Finset ℕ}
    (h : Work.BMF.GoodQuad hA δ x T q qf γ Ps) :
    Work.BMF.GoodQuad (upgradeC hC hX hL hA) δ x T q qf γ Ps :=
  ⟨h.x_mem, h.deg, h.T_bound, h.q_bound, h.q_le, h.qf_bound, h.qf_le, h.primes, h.card,
    h.not_dvd, h.int_coarse, h.minimal, h.int_fine, h.decomp⟩

/-- **N8. From local to global structure, and extraction of the twist**
(MRTTZ Props. 3.9–3.13, MRT §5). Solve each edge with N6, bound the essentially distinct local
structures per interval (MRTTZ Prop. 3.9), make them compatible along edges (Prop. 3.11), make
`T` and `q` global by the approximate-ergodicity argument (N7), bound `q₀` (N4), and extract a
twisted short-interval correlation: `∫_Y^{2Y} |Σ_{y ≤ n ≤ y+H'} f(n) ψ(n) n^{-iT₀}| ≥ c' H' Y` with
`ψ` periodic of period `≤ R₀` and `|T₀| ≪ (X/H)^{k+1}`. -/
theorem global_structure (k : ℕ) (θ ε c C : ℝ) (ℓ : ℕ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2)
    (hε : 0 < ε) (hεθ : ε ≤ θ / 100) (hc : 0 < c) (hℓ : 1 ≤ ℓ) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∃ R₀ : ℕ, ∀ Y₀ : ℝ, ∃ X₀ : ℝ,
      ∀ (f : ℕ → ℂ), IsOneBounded f → ∀ (X H P₁ P₂ : ℝ), X₀ ≤ X → X ^ θ ≤ H →
        H ≤ X ^ (1 - θ) → X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ →
        P₂ ≤ X ^ ε →
        ADIData k f c C (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ P₂ ℓ →
        ∃ (T₀ : ℝ) (r : ℕ) (ψ : ℕ → ℂ) (Y H' : ℝ),
          |T₀| ≤ C' * X ^ (k + 1) / H ^ (k + 1) ∧ r ≤ R₀ ∧ IsPeriodicBdd r ψ ∧
          Y₀ ≤ Y ∧ X ^ (1 / 2 : ℝ) ≤ Y ∧ Y ≤ X ∧ Y ^ (θ / 2) ≤ H' ∧ H' ≤ Y ∧
          Y / H' ≤ C' * X ^ (k + 1) / H ^ (k + 1) ∧ TwistCorr f ψ T₀ Y H' c' := by
  classical
  --------------------------------------------------------------------------
  -- §0. Numerical constants
  --------------------------------------------------------------------------
  set C₀C : ℝ := max C 10 with hC₀Cdef
  have hC₀C_ge10 : 10 ≤ C₀C := le_max_right C 10
  have hC₀C_ge1 : 1 ≤ C₀C := le_trans (by norm_num) hC₀C_ge10
  have hC₀C_pos : 0 < C₀C := lt_of_lt_of_le (by norm_num) hC₀C_ge10
  have hC_le : C ≤ C₀C := le_max_left C 10
  have hC1c_ge2 : (2 : ℝ) ≤ Work.BMF.C1c k C₀C := Work.BMF.C1c_ge_two k C₀C hC₀C_ge1
  have hθ100 : ε < 1 / 200 := by linarith [hεθ, hθ₀, hθ₁]
  have h1m2e : 0 < 1 - 2 * ε := by linarith
  have htexp : 0 < θ / 2 - 2 * ε := by linarith [hεθ, hθ₀]
  have hthexp : 0 < θ - 3 * ε + ε ^ 2 / 2 := by
    nlinarith [hεθ, hθ₀, hε, sq_nonneg (ε - 3)]
  set Kbig : ℝ := 1 + 3 * (Work.BMF.K0c k : ℝ) *
      ((2 * (ℓ : ℝ) + 2) * (Real.log 2 + ε) + 2) with hKbigdef
  have hKbig_pos : 0 < Kbig := by rw [hKbigdef]; positivity
  set Lm : ℝ := max 4 (max (4 / c) (max (Work.BMF.C1c k C₀C) Kbig)) with hLmdef
  have hLm_ge4 : 4 ≤ Lm := le_max_left _ _
  have hLm_pos : 0 < Lm := lt_of_lt_of_le (by norm_num) hLm_ge4
  have hLm_ge_4c : 4 / c ≤ Lm := le_trans (le_max_left _ _) (le_max_right _ _)
  have hLm_ge_C1c : Work.BMF.C1c k C₀C ≤ Lm :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hLm_ge_Kbig : Kbig ≤ Lm :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  set δ : ℝ := 1 / Lm with hδdef
  have hδinv : δ⁻¹ = Lm := by rw [hδdef, one_div, inv_inv]
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos hLm_pos
  have hδle1 : δ ≤ 1 := by rw [hδdef, div_le_one hLm_pos]; linarith
  have hδc : 2 * δ ≤ c := by
    rw [hδdef, show 2 * (1 / Lm) = 2 / Lm by ring, div_le_iff₀ hLm_pos]
    have h1 : (2 : ℝ) ≤ c * (4 / c) := by
      rw [mul_div_cancel₀ 4 (ne_of_gt hc)]; norm_num
    exact le_trans h1 (mul_le_mul_of_nonneg_left hLm_ge_4c (le_of_lt hc))
  have hδinv_C1c : Work.BMF.C1c k C₀C ≤ δ⁻¹ := by rw [hδinv]; exact hLm_ge_C1c
  have hδinv_Kbig : Kbig ≤ δ⁻¹ := by rw [hδinv]; exact hLm_ge_Kbig
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt3 : Real.log 2 < 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  set δb : ℝ := δ * Real.log 2 / 3 with hδbdef
  have hδbpos : 0 < δb := by rw [hδbdef]; positivity
  have hδble1 : δb ≤ 1 := by rw [hδbdef]; nlinarith [hδpos, hδle1, hlog2lt3, hlog2pos]
  --------------------------------------------------------------------------
  -- §1. Constants extracted from the fleet lemmas
  --------------------------------------------------------------------------
  obtain ⟨Kloc, hKlocpos, C1loc, hC1locpos, hlocfin⟩ :=
    Work.N8.local_finite k δ hδpos hδle1
  obtain ⟨Kg, hKgpos, hKg_le_Kloc, hgreedy⟩ := Work.N8.greedy_family_sub Kloc hKlocpos
  have hKgRpos : (0 : ℝ) < (Kg : ℝ) := by exact_mod_cast hKgpos
  obtain ⟨X₀pb, hpb⟩ := Work.N8.primes_big k ε δ hε hδpos hδle1
  obtain ⟨X₀qe, hqe⟩ := Work.N8.quads_from_edges k δ hδpos
  obtain ⟨X₀sqe, hsqe⟩ :=
    Work.N8.scale_qe k θ ε c ℓ C₀C δ hθ₀ hθ₁ hε hεθ hc hC₀C_ge10 hδpos hδle1 hδc
      hδinv_C1c hδinv_Kbig
  obtain ⟨X₀bad, hbada⟩ :=
    Work.N8.scale_bad_edges θ ε c δb Kg hKgpos hθ₀ hθ₁ hε hεθ hc hδbpos hδble1
  obtain ⟨X₀sep, hsep800a⟩ := Work.N8.edge_sep_800 θ ε hθ₀ hθ₁ hε hεθ
  obtain ⟨Csc, hCscpos, hsc⟩ := Work.N8.scales_large θ ε hθ₀ hθ₁ hε hεθ
  obtain ⟨Lbig, hLbig2, X₀s6, hs6⟩ := Work.N8.scale_step6_hyp k θ ε 0 hθ₀ hθ₁ hε hεθ
  have hLbig1 : 1 ≤ Lbig := by omega
  --------------------------------------------------------------------------
  -- §2. The N7 mixing count (stubbed while `LFunction_zeroFree_VK` is broken)
  --------------------------------------------------------------------------
  obtain ⟨Cmix, X₀mix, hCmixpos, hmix⟩ : ∃ Cmix X₀mix : ℝ, 0 < Cmix ∧
      ∀ (Xu Lr P : ℝ) (A₁ A₂ : Finset ℝ), X₀mix ≤ Xu →
        Xu ^ (min (θ / 2) (ε ^ 2 / 2) / 2) ≤ P → P ≤ Xu ^ (1 / 4 : ℝ) →
        Xu ^ (min (θ / 2) (ε ^ 2 / 2) / 2) ≤ Lr → Lr ≤ Xu →
        (∀ x ∈ A₁ ∪ A₂, Xu / 10 ≤ x ∧ x ≤ 10 * Xu) →
        (∀ x ∈ A₁, ∀ y ∈ A₁, x ≠ y → Lr ≤ |x - y|) →
        (∀ x ∈ A₂, ∀ y ∈ A₂, x ≠ y → Lr ≤ |x - y|) →
        ((((A₁ ×ˢ A₂) ×ˢ (Work.BMF.primesIn P (2 * P) ×ˢ
            Work.BMF.primesIn P (2 * P))).filter
            (fun v => |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * Lr)).card : ℝ)
          ≤ Cmix * ((A₁.card : ℝ) * (A₂.card : ℝ) * (Lr / Xu) * Work.BMF.pi0 P ^ 2 +
              Real.sqrt ((A₁.card : ℝ) * (A₂.card : ℝ)) * Work.BMF.pi0 P ^ 2
                / Real.log P) :=
    Work.BMF.mixing_count (min (θ / 2) (ε ^ 2 / 2) / 2) (by positivity)
  --------------------------------------------------------------------------
  -- §3. Uniform constants of the fleet lemmas, packed conditionally on `1 ≤ k`
  --------------------------------------------------------------------------
  set Ab : ℕ → ℝ → ℝ → ℝ → ℝ :=
    (if hk : 1 ≤ k then Classical.choose (Work.N8.step6_q0_bound_v2 k hk ε hε)
      else fun _ _ _ _ => 1) with hAbdef
  set Gf : ℕ → ℝ :=
    (if hk : 1 ≤ k then
        (fun l : ℕ => if hl : 1 ≤ l then Classical.choose (Work.N8.n4_uniform l k hl hk)
          else 1)
      else fun _ => 1) with hGfdef
  set Bf : ℕ → ℝ :=
    (if hk : 1 ≤ k then
        (fun l : ℕ => if hl : 1 ≤ l then
          Classical.choose (Classical.choose_spec (Work.N8.n4_uniform l k hl hk)) else 1)
      else fun _ => 1) with hBfdef
  set Ckb : ℝ :=
    (if hk : 1 ≤ k then Classical.choose (Work.N8.omega_totient_bound k) else 1)
    with hCkbdef
  set Bmax : ℝ := max 1 ((Finset.range (Lbig + 1)).sup'
      ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun l => Bf l)) with hBmaxdef
  have hBmax_pos : 0 < Bmax := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hBf_le_Bmax : ∀ l ∈ Finset.range (Lbig + 1), Bf l ≤ Bmax := by
    intro l hl
    exact le_trans (Finset.le_sup' (f := fun l => Bf l) hl) (le_max_right _ _)
  set c₂ : ℝ := 100 * (Kg : ℝ) with hc₂def
  have hc₂pos : 0 < c₂ := by rw [hc₂def]; positivity
  set δae : ℝ := c / 8 with hδaedef
  have hδaepos : 0 < δae := by rw [hδaedef]; positivity
  set cE : ℝ := min ((1 / (10 : ℝ) ^ 7) * (δae / (Cmix * 100 * (Kg : ℝ) ^ 3)))
      ((1 / (10 : ℝ) ^ 7) * (δae ^ 2 / (Cmix * 100 * (Kg : ℝ) ^ 4))) with hcEdef
  have hcEpos : 0 < cE := by rw [hcEdef]; exact lt_min (by positivity) (by positivity)
  have hcE_le1 : cE ≤ (1 / (10 : ℝ) ^ 7) * (δae / (Cmix * 100 * (Kg : ℝ) ^ 3)) :=
    min_le_left _ _
  have hcE_le2 : cE ≤ (1 / (10 : ℝ) ^ 7) * (δae ^ 2 / (Cmix * 100 * (Kg : ℝ) ^ 4)) :=
    min_le_right _ _
  set Mbig : ℝ := (Finset.range (Lbig + 1)).sup'
      ⟨0, Finset.mem_range.mpr (by omega)⟩
      (fun l => 2 * Ab l c₂ (Gf l) Ckb * (Kg : ℝ) ^ l * (c₂ / cE) ^ l) with hMbigdef
  have hMbig_ge : ∀ l ∈ Finset.range (Lbig + 1),
      2 * Ab l c₂ (Gf l) Ckb * (Kg : ℝ) ^ l * (c₂ / cE) ^ l ≤ Mbig := by
    intro l hl
    rw [hMbigdef]
    exact Finset.le_sup' (f := fun l => 2 * Ab l c₂ (Gf l) Ckb * (Kg : ℝ) ^ l * (c₂ / cE) ^ l) hl
  set Q₀ : ℕ := max 1 ⌈(Finset.range (Lbig + 1)).sup'
      ⟨0, Finset.mem_range.mpr (by omega)⟩
      (fun l => (2 * Ab l c₂ (Gf l) Ckb * (Kg : ℝ) ^ l * (c₂ / cE) ^ l) ^ (2 * k))⌉₊
    with hQ₀def
  have hQ₀pos : 1 ≤ Q₀ := le_max_left 1 _
  have hQ₀_ge : ∀ l ∈ Finset.range (Lbig + 1),
      (2 * Ab l c₂ (Gf l) Ckb * (Kg : ℝ) ^ l * (c₂ / cE) ^ l) ^ (2 * k) ≤ (Q₀ : ℝ) := by
    intro l hl
    have h1 : (2 * Ab l c₂ (Gf l) Ckb * (Kg : ℝ) ^ l * (c₂ / cE) ^ l) ^ (2 * k)
        ≤ (Finset.range (Lbig + 1)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
            (fun l => (2 * Ab l c₂ (Gf l) Ckb * (Kg : ℝ) ^ l * (c₂ / cE) ^ l) ^ (2 * k)) :=
      Finset.le_sup' (f := fun l => (2 * Ab l c₂ (Gf l) Ckb * (Kg : ℝ) ^ l * (c₂ / cE) ^ l) ^ (2 * k)) hl
    refine le_trans h1 ?_
    rw [hQ₀def]
    push_cast
    exact le_trans (Nat.le_ceil _) (le_max_right 1 _)
  obtain ⟨R₀, hR₀pos, hR₀le, hR₀psi⟩ := Work.N8.exists_psi_set k Q₀ hQ₀pos
  set cT2 : ℝ := max 1 (2000 * C1loc) with hcT2def
  have hcT2pos : 0 < cT2 := lt_of_lt_of_le one_pos (le_max_left _ _)
  obtain ⟨cstar, cdbl, hcstarpos, hcstarle1, hcdblpos, hExtract⟩ :=
    Work.N8.extract_local k c δ⁻¹ cT2 hc (by positivity) hcT2pos
  set cA : ℝ := min (min (cdbl * c) c) (cE / (2 * (Kg : ℝ))) with hcAdef
  have hcApos : 0 < cA := by
    rw [hcAdef]; exact lt_min (lt_min (mul_pos hcdblpos hc) hc) (by positivity)
  have hcA_le : cA ≤ cdbl * c := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcA_le_c : cA ≤ c := le_trans (min_le_left _ _) (min_le_right _ _)
  have hcA_le' : cA ≤ cE / (2 * (Kg : ℝ)) := min_le_right _ _
  obtain ⟨c', hc'pos, hagg⟩ := Work.N8.aggregate_twist_v2 R₀ hR₀pos cA hcApos
  have hε2pos : (0:ℝ) < ε ^ 2 / 2 := by positivity
  have hε2nonneg : (0:ℝ) ≤ ε ^ 2 / 2 := le_of_lt hε2pos
  have hθ2pos : (0:ℝ) < θ / 2 := by linarith
  have hθ2nonneg : (0:ℝ) ≤ θ / 2 := le_of_lt hθ2pos
  have h1000C1pos : (0:ℝ) < 1000 * C1loc := by positivity
  have h1000C1nonneg : (0:ℝ) ≤ 1000 * C1loc := le_of_lt h1000C1pos
  have h2Kgpos : (0:ℝ) < 2 * (Kg : ℝ) := by positivity
  have hinv1000C1pos : (0:ℝ) < 1 / (1000 * C1loc) := one_div_pos.mpr h1000C1pos
  set C' : ℝ := max 1 (max (δ⁻¹ + 200 * C1loc) (40 / cstar)) with hC'def
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hC'_ge1 : 1 ≤ C' := le_max_left _ _
  have hC'_geT : δ⁻¹ + 200 * C1loc ≤ C' := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC'_geC : 40 / cstar ≤ C' := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨c', C', hc'pos, hC'pos, R₀, fun Y₀ => ?_⟩
  --------------------------------------------------------------------------
  -- §4. The per-instance threshold `X₀(Y₀)`
  --------------------------------------------------------------------------
  set Y₀p : ℝ := max Y₀ 0 with hY₀pdef
  set Lg : ℝ := (10 : ℝ) ^ 7 * Cmix * 100 * (Kg : ℝ) ^ 3 / δae with hLgdef
  set M0 : ℝ := ({X₀pb, X₀qe, X₀sqe, X₀bad, X₀mix, X₀s6, X₀sep, 1} : Finset ℝ).max'
    ⟨1, by simp⟩ with hM0def
  have hM0_ge : ∀ a ∈ ({X₀pb, X₀qe, X₀sqe, X₀bad, X₀mix, X₀s6, X₀sep, 1} : Finset ℝ), a ≤ M0 := by
    intro a ha
    rw [hM0def]
    exact Finset.le_max' _ _ ha
  set Tset₀ : Finset ℝ := {Csc, Real.exp (Mbig / θ + 1) + 2,
      Real.exp (Lg * (2 / ε ^ 2) + 1) + 2,
      Real.exp ((40 / cstar) * (2 / ε ^ 2) + 1) + 2,
      M0 ^ (1 / (1 - 2 * ε)), (10 * (Y₀p + 2)) ^ (1 / (1 - 2 * ε)),
      (13 : ℝ) ^ (1 / θ), (8000 : ℝ) ^ (2 / θ), (4 : ℝ) ^ (2 / ε ^ 2),
      Bmax ^ (2 / ε ^ 2), (8 / c + 1) ^ (2 / θ), (16 / cA + 1) ^ (1 / θ),
      (max 1 (6.4 ^ (θ / 2) / cstar)) ^ (100 / θ)} with hTset₀def
  set X₀all : ℝ := Tset₀.max' (by rw [hTset₀def]; simp) with hX₀alldef
  have hX₀all_ge : ∀ a ∈ Tset₀, a ≤ X₀all := by
    intro a ha
    rw [hX₀alldef]
    exact Finset.le_max' _ _ ha
  have hmem : ∀ a : ℝ, a ∈ ({Csc, Real.exp (Mbig / θ + 1) + 2,
      Real.exp (Lg * (2 / ε ^ 2) + 1) + 2,
      Real.exp ((40 / cstar) * (2 / ε ^ 2) + 1) + 2,
      M0 ^ (1 / (1 - 2 * ε)), (10 * (Y₀p + 2)) ^ (1 / (1 - 2 * ε)),
      (13 : ℝ) ^ (1 / θ), (8000 : ℝ) ^ (2 / θ), (4 : ℝ) ^ (2 / ε ^ 2),
      Bmax ^ (2 / ε ^ 2), (8 / c + 1) ^ (2 / θ), (16 / cA + 1) ^ (1 / θ),
      (max 1 (6.4 ^ (θ / 2) / cstar)) ^ (100 / θ)} : Finset ℝ) →
      a ≤ X₀all := by
    intro a ha
    exact hX₀all_ge a (by rw [hTset₀def]; exact ha)
  refine ⟨X₀all, ?_⟩
  intro f hf X H P₁ P₂ hX hXθ hH hP₁lo hP₁hi hP₂lo hP₂hi A
  have hXsc : Csc ≤ X := le_trans (hmem Csc (by simp)) hX
  have hXlogM : Real.exp (Mbig / θ + 1) + 2 ≤ X := le_trans (hmem _ (by simp)) hX
  have hXlogG : Real.exp (Lg * (2 / ε ^ 2) + 1) + 2 ≤ X := le_trans (hmem _ (by simp)) hX
  have hXlogC : Real.exp ((40 / cstar) * (2 / ε ^ 2) + 1) + 2 ≤ X :=
    le_trans (hmem _ (by simp)) hX
  have hXM0 : M0 ^ (1 / (1 - 2 * ε)) ≤ X := le_trans (hmem _ (by simp)) hX
  have hXY₀ : (10 * (Y₀p + 2)) ^ (1 / (1 - 2 * ε)) ≤ X := le_trans (hmem _ (by simp)) hX
  have hX13 : (13 : ℝ) ^ (1 / θ) ≤ X := le_trans (hmem _ (by simp)) hX
  have hX8000 : (8000 : ℝ) ^ (2 / θ) ≤ X := le_trans (hmem _ (by simp)) hX
  have hX4 : (4 : ℝ) ^ (2 / ε ^ 2) ≤ X := le_trans (hmem _ (by simp)) hX
  obtain ⟨hXpos, hX1, hHpos, hP₁pos, hP₁1, hP₂pos, hP₂4, hP₁P₂pos, hP₁P₂10, hlogX1,
    hXppos, hXp10, hXp1, hXpge, hXpleX, h10sqrt, h10Xp, hNpos, hN3, hNle,
    hLpos, hL1, hLge, hLge2, hLleXp, hLleH, hsqrtX, hlogP₁pos, hlogP₁1, hlogP₂pos,
    hlogP₂half, hpi0P₁⟩ := hsc X H P₁ P₂ hXsc hXθ hH hP₁lo hP₁hi hP₂lo hP₂hi
  have hc₀pos : 0 < min (θ / 2) (ε ^ 2 / 2) / 2 := by
    exact div_pos (lt_min hθ2pos hε2pos) two_pos
  have hc₀θ : min (θ / 2) (ε ^ 2 / 2) / 2 ≤ θ / 2 := by
    have h := min_le_left (θ / 2) (ε ^ 2 / 2); linarith
  have hc₀ε : min (θ / 2) (ε ^ 2 / 2) / 2 ≤ ε ^ 2 / 2 := by
    have h := min_le_right (θ / 2) (ε ^ 2 / 2); linarith
  have hPowP : (X / (P₁ * P₂)) ^ (min (θ / 2) (ε ^ 2 / 2) / 2) ≤ P₁ := by
    have h1 : (X / (P₁ * P₂)) ^ (min (θ / 2) (ε ^ 2 / 2) / 2) ≤ X ^ (min (θ / 2) (ε ^ 2 / 2) / 2) :=
      Real.rpow_le_rpow (le_of_lt hXppos) hXpleX hc₀pos.le
    have h2 : X ^ (min (θ / 2) (ε ^ 2 / 2) / 2) ≤ X ^ (ε ^ 2 / 2) :=
      Real.rpow_le_rpow_of_exponent_le hX1 hc₀ε
    linarith [h1, h2, hP₁lo]
  have hP₁quart : P₁ ≤ (X / (P₁ * P₂)) ^ (1 / 4 : ℝ) := by
    have hε1 : ε ≤ 1 / 6 := by linarith [hεθ, hθ₁]
    have h1 : X ^ ε ≤ X ^ ((1 - 2 * ε) / 4) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have h2 : X ^ ((1 - 2 * ε) / 4) = (X ^ (1 - 2 * ε)) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_mul hXpos.le]
      ring_nf
    have h3 : (X ^ (1 - 2 * ε)) ^ (1 / 4 : ℝ) ≤ (X / (P₁ * P₂)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hXpos.le _) hXpge (by norm_num)
    linarith [hP₁hi, h1, h2, h3]
  have hPowL : (X / (P₁ * P₂)) ^ (min (θ / 2) (ε ^ 2 / 2) / 2) ≤ H / (P₁ * P₂) := by
    have h1 : (X / (P₁ * P₂)) ^ (min (θ / 2) (ε ^ 2 / 2) / 2) ≤ X ^ (min (θ / 2) (ε ^ 2 / 2) / 2) :=
      Real.rpow_le_rpow (le_of_lt hXppos) hXpleX hc₀pos.le
    have h2 : X ^ (min (θ / 2) (ε ^ 2 / 2) / 2) ≤ X ^ (θ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hX1 hc₀θ
    have h3 : X ^ (θ / 2) ≤ X ^ (θ - 2 * ε) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith [hεθ, hθ₀])
    linarith [h1, h2, h3, hLge2]
  have hBmax_le : Bmax ≤ P₁ := by
    have h1 : Bmax ^ (2 / ε ^ 2) ≤ X := le_trans (hmem _ (by simp)) hX
    have h2 : (Bmax ^ (2 / ε ^ 2)) ^ (ε ^ 2 / 2) = Bmax := by
      rw [← Real.rpow_mul (le_of_lt hBmax_pos)]
      rw [show 2 / ε ^ 2 * (ε ^ 2 / 2) = 1 by field_simp]
      exact Real.rpow_one _
    have h3 : (Bmax ^ (2 / ε ^ 2)) ^ (ε ^ 2 / 2) ≤ X ^ (ε ^ 2 / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hBmax_pos.le _) h1 hε2nonneg
    linarith [h2, h3, hP₁lo]
  have hXpow13 : (13 : ℝ) ≤ X ^ θ := by
    have h1 : ((13 : ℝ) ^ (1 / θ)) ^ θ = 13 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 13)]
      rw [show 1 / θ * θ = 1 by field_simp]
      exact Real.rpow_one 13
    calc (13 : ℝ) = ((13 : ℝ) ^ (1 / θ)) ^ θ := h1.symm
      _ ≤ X ^ θ := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hX13 (le_of_lt hθ₀)
  have hN13 : 13 ≤ X / H := by
    have h4 : X ^ θ * H ≤ X := by
      have h5 : X ^ θ * H ≤ X ^ θ * X ^ (1 - θ) :=
        mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hXpos.le _)
      have h6 : X ^ θ * X ^ (1 - θ) = X := by
        rw [← Real.rpow_add hXpos, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
      linarith [h5, h6.le, h6.ge]
    rw [le_div_iff₀ hHpos]
    exact le_trans (mul_le_mul_of_nonneg_right hXpow13 hHpos.le) h4
  have h4le : (4 : ℝ) ≤ X ^ (ε ^ 2 / 2) := by
    have h2 : ((4 : ℝ) ^ (2 / ε ^ 2)) ^ (ε ^ 2 / 2) = 4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show 2 / ε ^ 2 * (ε ^ 2 / 2) = 1 by field_simp]
      exact Real.rpow_one 4
    calc (4 : ℝ) = ((4 : ℝ) ^ (2 / ε ^ 2)) ^ (ε ^ 2 / 2) := h2.symm
      _ ≤ X ^ (ε ^ 2 / 2) := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hX4
          hε2nonneg
  have hP₁4 : (4 : ℝ) ≤ P₁ := le_trans h4le hP₁lo
  have hP₁Xp : P₁ ≤ X / (P₁ * P₂) := by
    have h1 : P₁ ≤ X ^ ε := hP₁hi
    have h2 : X ^ ε ≤ X ^ (1 - 2 * ε) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    exact le_trans h1 (le_trans h2 hXpge)
  have hX''4 : (4 : ℝ) ≤ X / (P₁ * P₂) := le_trans hP₁4 hP₁Xp
  --------------------------------------------------------------------------
  -- §5. The upgraded `ADIData`, edge solutions and the greedy family
  --------------------------------------------------------------------------
  set A' : Work.BMF.ADIData k f c C₀C (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ P₂ ℓ :=
    upgradeC hC_le hXppos hLpos A with hA'def
  have hM0_le_xp : M0 ≤ X / (P₁ * P₂) := by
    refine le_trans ?_ hXpge
    have hM0_ge1 : (1 : ℝ) ≤ M0 := hM0_ge 1 (by simp)
    have h1 : (M0 ^ (1 / (1 - 2 * ε))) ^ (1 - 2 * ε) = M0 := by
      rw [← Real.rpow_mul (le_of_lt (lt_of_lt_of_le zero_lt_one hM0_ge1))]
      rw [show 1 / (1 - 2 * ε) * (1 - 2 * ε) = 1 by field_simp]
      exact Real.rpow_one M0
    calc M0 = (M0 ^ (1 / (1 - 2 * ε))) ^ (1 - 2 * ε) := h1.symm
      _ ≤ X ^ (1 - 2 * ε) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hXM0 (le_of_lt h1m2e)
  have hY₀_le : Y₀ ≤ X / (P₁ * P₂) / 10 := by
    have hb0 : (0 : ℝ) ≤ 10 * (Y₀p + 2) := by
      have hz : (0 : ℝ) ≤ Y₀p := le_max_right _ _
      linarith
    have h2 : 10 * (Y₀p + 2) ≤ X ^ (1 - 2 * ε) := by
      have h1 : ((10 * (Y₀p + 2)) ^ (1 / (1 - 2 * ε))) ^ (1 - 2 * ε) = 10 * (Y₀p + 2) := by
        rw [← Real.rpow_mul hb0, show 1 / (1 - 2 * ε) * (1 - 2 * ε) = 1 by field_simp,
          Real.rpow_one]
      calc 10 * (Y₀p + 2) = ((10 * (Y₀p + 2)) ^ (1 / (1 - 2 * ε))) ^ (1 - 2 * ε) := h1.symm
        _ ≤ X ^ (1 - 2 * ε) := Real.rpow_le_rpow (Real.rpow_nonneg hb0 _) hXY₀ (le_of_lt h1m2e)
    have h3 : Y₀p ≤ X / (P₁ * P₂) / 10 := by linarith [h2, hXpge]
    have h4 : Y₀ ≤ Y₀p := le_max_left _ _
    linarith
  obtain ⟨hsq2L, hsqLX, hsqP24, h100N, hK0log, hK0card, hZKhi⟩ :=
    hsqe X H P₁ P₂ (le_trans (hM0_ge X₀sqe (by simp)) hM0_le_xp) hXθ hH hP₁lo hP₁hi
      hP₂lo hP₂hi
  have hxdiv : X / (P₁ * P₂) / (H / (P₁ * P₂)) = X / H := by
    have h1 : (P₁ * P₂) ≠ 0 := ne_of_gt hP₁P₂pos
    have h2 : H ≠ 0 := ne_of_gt hHpos
    field_simp

  have hCmax : max C₀C 10 = C₀C := max_eq_left hC₀C_ge10
  --------------------------------------------------------------------------
  -- §5. The upgraded `ADIData`, the edge solutions and the greedy family
  --------------------------------------------------------------------------
  have hEdge2 : ∀ e ∈ A'.edges, ∃ z₁ z₂ : N8Quad,
      Work.BMF.GoodQuad A' δ e.x₁ z₁.1 z₁.2.1 z₁.2.2.1 z₁.2.2.2.1 z₁.2.2.2.2 ∧
      Work.BMF.GoodQuad A' δ e.x₂ z₂.1 z₂.2.1 z₂.2.2.1 z₂.2.2.2.1 z₂.2.2.2.2 ∧
      z₁.1 = z₂.1 ∧
      Work.BMF.IntegralOn 1 (Work.BMF.dil (e.p₂ : ℝ) z₁.2.2.2.1 -
        Work.BMF.dil (e.p₁ : ℝ) z₂.2.2.2.1) := by
    intro e he
    obtain ⟨Tq, q₁, qf₁, γ₁, Ps₁, q₂, qf₂, γ₂, Ps₂, h1, h2, h3⟩ :=
      hqe f c C₀C (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ P₂ ℓ A' hc
        (le_trans (hM0_ge X₀qe (by simp)) hM0_le_xp) hC₀C_ge10 hsq2L hsqLX hsqP24
        (by linarith [hδc, hδpos]) (by rw [hCmax, hxdiv]; exact h100N)
        (by rw [hCmax]; exact hδinv_C1c) hK0log hK0card hZKhi e he
    exact ⟨(Tq, q₁, qf₁, γ₁, Ps₁), (Tq, q₂, qf₂, γ₂, Ps₂), h1, h2, rfl, h3⟩
  let z₁c : Work.BMF.Edge → N8Quad := fun e =>
    dite (e ∈ A'.edges) (fun he => Classical.choose (hEdge2 e he)) (fun _ => (0, 1, 1, 0, ∅))
  let z₂c : Work.BMF.Edge → N8Quad := fun e =>
    dite (e ∈ A'.edges) (fun he => Classical.choose (Classical.choose_spec (hEdge2 e he)))
      (fun _ => (0, 1, 1, 0, ∅))
  have hz₁c : ∀ (e : Work.BMF.Edge) (he : e ∈ A'.edges),
      z₁c e = Classical.choose (hEdge2 e he) := fun e he => dite_eq_left he
  have hz₂c : ∀ (e : Work.BMF.Edge) (he : e ∈ A'.edges),
      z₂c e = Classical.choose (Classical.choose_spec (hEdge2 e he)) :=
    fun e he => dite_eq_left he
  have hz₁good : ∀ (e : Work.BMF.Edge) (he : e ∈ A'.edges),
      Work.BMF.GoodQuad A' δ e.x₁ (z₁c e).1 (z₁c e).2.1 (z₁c e).2.2.1 (z₁c e).2.2.2.1
        (z₁c e).2.2.2.2 := by
    intro e he
    rw [hz₁c e he]
    exact (Classical.choose_spec (Classical.choose_spec (hEdge2 e he))).1
  have hz₂good : ∀ (e : Work.BMF.Edge) (he : e ∈ A'.edges),
      Work.BMF.GoodQuad A' δ e.x₂ (z₂c e).1 (z₂c e).2.1 (z₂c e).2.2.1 (z₂c e).2.2.2.1
        (z₂c e).2.2.2.2 := by
    intro e he
    rw [hz₂c e he]
    exact (Classical.choose_spec (Classical.choose_spec (hEdge2 e he))).2.1
  have hTcc : ∀ (e : Work.BMF.Edge) (he : e ∈ A'.edges), (z₁c e).1 = (z₂c e).1 := by
    intro e he
    rw [hz₁c e he, hz₂c e he]
    exact (Classical.choose_spec (Classical.choose_spec (hEdge2 e he))).2.2.1
  have hzrel : ∀ (e : Work.BMF.Edge) (he : e ∈ A'.edges),
      Work.BMF.IntegralOn 1 (Work.BMF.dil (e.p₂ : ℝ) (z₁c e).2.2.2.1 -
        Work.BMF.dil (e.p₁ : ℝ) (z₂c e).2.2.2.1) := by
    intro e he
    rw [hz₁c e he, hz₂c e he]
    exact (Classical.choose_spec (Classical.choose_spec (hEdge2 e he))).2.2.2
  let Gd : ℝ → Finset N8Quad := fun x =>
    A'.edges.biUnion (fun e =>
      ((if h : e.x₁ = x then ({z₁c e} : Finset N8Quad) else ∅) ∪
       (if h : e.x₂ = x then ({z₂c e} : Finset N8Quad) else ∅)))
  have hGdmem₁ : ∀ (e : Work.BMF.Edge) (he : e ∈ A'.edges), z₁c e ∈ Gd e.x₁ := by
    intro e he
    refine Finset.mem_biUnion.mpr ⟨e, he, ?_⟩
    rw [dif_pos rfl]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  have hGdmem₂ : ∀ (e : Work.BMF.Edge) (he : e ∈ A'.edges), z₂c e ∈ Gd e.x₂ := by
    intro e he
    refine Finset.mem_biUnion.mpr ⟨e, he, ?_⟩
    rw [Finset.mem_union]
    right
    rw [dif_pos rfl]
    exact Finset.mem_singleton_self _
  have hGdgood : ∀ x, ∀ z ∈ Gd x,
      Work.BMF.GoodQuad A' δ x z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 := by
    intro x z hz
    rw [show Gd x = A'.edges.biUnion (fun e' =>
        ((if h : e'.x₁ = x then ({z₁c e'} : Finset N8Quad) else ∅) ∪
         (if h : e'.x₂ = x then ({z₂c e'} : Finset N8Quad) else ∅))) from rfl] at hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨e, he, hz⟩ := hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · by_cases hx : e.x₁ = x
      · rw [dif_pos hx, Finset.mem_singleton] at hz
        rw [hz, ← hx]
        exact hz₁good e he
      · rw [dif_neg hx] at hz
        exact absurd hz (Finset.notMem_empty z)
    · by_cases hx : e.x₂ = x
      · rw [dif_pos hx, Finset.mem_singleton] at hz
        rw [hz, ← hx]
        exact hz₂good e he
      · rw [dif_neg hx] at hz
        exact absurd hz (Finset.notMem_empty z)
  have hpbX : Work.BMF.PrimesBig k δ X P₂ :=
    hpb X P₂ (le_trans (le_trans (hM0_ge X₀pb (by simp)) hM0_le_xp) hXpleX) hP₂lo hP₂hi
  have hpb2 : Work.BMF.PrimesBig k δ (X / (P₁ * P₂)) P₂ := by
    intro Ps hpr hcard
    have hXpnn : (0:ℝ) ≤ X / (P₁ * P₂) := le_of_lt hXppos
    have hδinv : (0:ℝ) ≤ 1 / δ := div_nonneg zero_le_one hδpos.le
    have hle : (X / (P₁ * P₂)) ^ (1 / δ) ≤ X ^ (1 / δ) :=
      Real.rpow_le_rpow hXpnn hXpleX hδinv
    have hle' : (0:ℝ) ≤ (X / (P₁ * P₂)) ^ (1 / δ) := Real.rpow_nonneg hXpnn _
    have h2 : ((X / (P₁ * P₂)) ^ (1 / δ)) ^ (2 * k) ≤ (X ^ (1 / δ)) ^ (2 * k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow hle' hle (Nat.cast_nonneg (2 * k))
    have h3 : ((X / (P₁ * P₂)) ^ (1 / δ)) ^ (k + 1) ≤ (X ^ (1 / δ)) ^ (k + 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow hle' hle (Nat.cast_nonneg (k + 1))
    have h4 : (0:ℝ) ≤ ((X / (P₁ * P₂)) ^ (1 / δ)) ^ (k + 1) + 1 := by
      have hh : (0:ℝ) ≤ ((X / (P₁ * P₂)) ^ (1 / δ)) ^ (k + 1) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_nonneg hle' _
      linarith
    have h5 : (0:ℝ) ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
    have hk1 : (0:ℝ) ≤ (k : ℝ) + 1 := by
      have h : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h6 : (0:ℝ) ≤ 2 * ((k : ℝ) + 1) * δ⁻¹ :=
      mul_nonneg (mul_nonneg (by norm_num) hk1) (inv_nonneg.mpr hδpos.le)
    have hxk : (0:ℝ) ≤ (X ^ (1 / δ)) ^ (2 * k) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_nonneg (Real.rpow_nonneg hXpos.le _) _
    refine le_trans ?_ (hpbX Ps hpr hcard)
    have ha : (k.factorial : ℝ) * ((X / (P₁ * P₂)) ^ (1 / δ)) ^ (2 * k)
        ≤ (k.factorial : ℝ) * (X ^ (1 / δ)) ^ (2 * k) :=
      mul_le_mul_of_nonneg_left h2 h5
    have hb : 2 * ((k : ℝ) + 1) * δ⁻¹ * (((X / (P₁ * P₂)) ^ (1 / δ)) ^ (k + 1) + 1)
        ≤ 2 * ((k : ℝ) + 1) * δ⁻¹ * ((X ^ (1 / δ)) ^ (k + 1) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) h6
    have hb' : (0:ℝ) ≤ 2 * ((k : ℝ) + 1) * δ⁻¹ *
        (((X / (P₁ * P₂)) ^ (1 / δ)) ^ (k + 1) + 1) := mul_nonneg h6 h4
    have ha' : (0:ℝ) ≤ (k.factorial : ℝ) * (X ^ (1 / δ)) ^ (2 * k) := mul_nonneg h5 hxk
    exact mul_le_mul ha hb hb' ha'
  obtain ⟨Fg, hFgcard, hFgsub, hFgdom⟩ :=
    hgreedy Gd C1loc (X / (P₁ * P₂) / (H / (P₁ * P₂))) hC1locpos (by exact div_pos hXppos hLpos)
      (by
        intro x v hv
        obtain ⟨j, j', hne, hq, hmod, hT⟩ :=
          hlocfin f c C₀C (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ P₂ ℓ A' x
            (fun j => v (Fin.castSucc j)) hXppos hL1 hLleXp
            (fun j => hGdgood x (v (Fin.castSucc j)) (hv (Fin.castSucc j)))
            hpb2
        exact ⟨Fin.castSucc j, Fin.castSucc j',
          fun hh => hne (Fin.castSucc_injective Kloc hh), hq, hmod, hT⟩)
  have hFggood : ∀ x, ∀ z ∈ Fg x,
      Work.BMF.GoodQuad A' δ x z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 :=
    fun x z hz => hGdgood x z (hFgsub x hz)
  have hEdgemerge : ∀ e ∈ A'.edges, ∃ (T : ℝ) (q₁ qf₁ : ℕ) (γ₁ : Polynomial ℝ)
        (Ps₁ : Finset ℕ) (q₂ qf₂ : ℕ) (γ₂ : Polynomial ℝ) (Ps₂ : Finset ℕ),
      Work.BMF.GoodQuad A' δ e.x₁ T q₁ qf₁ γ₁ Ps₁ ∧
      Work.BMF.GoodQuad A' δ e.x₂ T q₂ qf₂ γ₂ Ps₂ ∧
      Work.BMF.IntegralOn 1 (Work.BMF.dil (e.p₂ : ℝ) γ₁ - Work.BMF.dil (e.p₁ : ℝ) γ₂) ∧
      (∃ z ∈ Fg e.x₁, z.2.1 = q₁ ∧ Work.BMF.ModZConst z.2.2.2.1 γ₁ ∧
        |z.1 - T| ≤ C1loc * (X / (P₁ * P₂) / (H / (P₁ * P₂)))) ∧
      (∃ z ∈ Fg e.x₂, z.2.1 = q₂ ∧ Work.BMF.ModZConst z.2.2.2.1 γ₂ ∧
        |z.1 - T| ≤ C1loc * (X / (P₁ * P₂) / (H / (P₁ * P₂)))) := by
    intro e he
    refine ⟨(z₁c e).1, (z₁c e).2.1, (z₁c e).2.2.1, (z₁c e).2.2.2.1, (z₁c e).2.2.2.2,
      (z₂c e).2.1, (z₂c e).2.2.1, (z₂c e).2.2.2.1, (z₂c e).2.2.2.2,
      hz₁good e he, ?_, ?_, ?_, ?_⟩
    · rw [hTcc e he]
      exact hz₂good e he
    · exact hzrel e he
    · obtain ⟨z', hz'F, hz'q, hz'mod, hz'T⟩ := hFgdom e.x₁ (z₁c e) (hGdmem₁ e he)
      exact ⟨z', hz'F, hz'q, hz'mod, hz'T⟩
    · obtain ⟨z', hz'F, hz'q, hz'mod, hz'T⟩ := hFgdom e.x₂ (z₂c e) (hGdmem₂ e he)
      exact ⟨z', hz'F, hz'q, hz'mod, by rw [hTcc e he]; exact hz'T⟩
  --------------------------------------------------------------------------
  -- §6. The bad edges are few, and the compatible pairs `S` (Step 4)
  --------------------------------------------------------------------------
  have hNf : ((A'.fam.card : ℕ) : ℝ) ≤ X / H / 10 := by
    have h1 := Work.BMF.fam_card_le (X / (P₁ * P₂)) (H / (P₁ * P₂)) hXppos hLpos A'.fam A'.isFam
    have h2 : 10 * (X / (P₁ * P₂)) / (500 * (H / (P₁ * P₂))) = X / H / 50 := by
      rw [show 10 * (X / (P₁ * P₂)) / (500 * (H / (P₁ * P₂)))
          = (10 / 500) * ((X / (P₁ * P₂)) / (H / (P₁ * P₂))) by ring, hxdiv]
      ring
    rw [h2] at h1
    linarith [h1, hN13]
  have hbadle : ((A'.edges.filter (fun e ↦
      (∃ z ∈ Fg e.x₁, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1) ∨
      (∃ z ∈ Fg e.x₂, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1))).card : ℝ)
      ≤ (A'.edges.card : ℝ) / 2 := by
    have hBom : ∀ x : ℝ, ∀ z ∈ Fg x,
        (((z.2.1).primeFactors.card : ℕ) : ℝ) ≤ Real.log (X / (P₁ * P₂)) / δb + 1 := by
      intro x z hz
      have hq1 : 1 ≤ z.2.1 := (hFggood x z hz).q_bound
      have hqle : ((z.2.1 : ℕ) : ℝ) ≤ (X / (P₁ * P₂)) ^ (1 / δ) := (hFggood x z hz).q_le
      have h1 : (((z.2.1).primeFactors.card : ℕ) : ℝ)
          ≤ Real.log (X / (P₁ * P₂)) / (δ * Real.log 2) :=
        Work.N8.omega_le_log_div_log (X / (P₁ * P₂)) δ hXp1 hδpos (z.2.1) hq1 hqle
      have h2 : Real.log (X / (P₁ * P₂)) / (δ * Real.log 2)
          ≤ Real.log (X / (P₁ * P₂)) / δb := by
        have hδ20 : 0 < δ * Real.log 2 := mul_pos hδpos hlog2pos
        rw [div_le_div_iff₀ hδ20 hδbpos]
        exact mul_le_mul_of_nonneg_left (by rw [hδbdef]; linarith [hδpos, hlog2pos])
          (Real.log_nonneg hXp1)
      linarith
    have hstruct := Work.N8.bad_edges_le k f c C₀C (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ P₂ ℓ A' Fg Kg
        (Real.log (X / (P₁ * P₂)) / δb + 1) hL1 hP₁1
        (by have h0 : (0:ℝ) ≤ Real.log (X / (P₁ * P₂)) := Real.log_nonneg hXp1
            have h1 : (0:ℝ) ≤ Real.log (X / (P₁ * P₂)) / δb := div_nonneg h0 hδbpos.le
            linarith) hFgcard
        (fun x z hz => (hFggood x z hz).q_bound) hBom
    have hBeq : Real.log (X / (P₁ * P₂)) / δb + 1 + 1 = Real.log (X / (P₁ * P₂)) / δb + 2 := by
      ring
    rw [hBeq] at hstruct
    have hnum := hbada X H P₁ P₂ ((A'.fam.card : ℕ) : ℝ)
        (le_trans (le_trans (hM0_ge X₀bad (by simp)) hM0_le_xp) hXpleX) hXθ hH hP₁lo hP₁hi
        hP₂lo hP₂hi hNf
    have h5 : c * Work.BMF.pi0 P₁ ^ 2 * (X / H) ≤ (A'.edges.card : ℝ) := by
      have h6 := A'.edges_card
      rw [hxdiv] at h6
      exact h6
    have h1 : 2 * ((A'.edges.filter (fun e ↦
        (∃ z ∈ Fg e.x₁, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1) ∨
        (∃ z ∈ Fg e.x₂, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1))).card : ℝ) ≤ (A'.edges.card : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hstruct (by norm_num : (0:ℝ) ≤ 2)
      linarith [hh, hnum, h5]
    linarith
  have hsep800 : ∀ x ∈ A'.fam, 800 * (H / (P₁ * P₂)) * P₁ ^ 2 < x := by
    intro x hx
    exact hsep800a X H P₁ P₂ x
      (le_trans (le_trans (hM0_ge X₀sep (by simp)) hM0_le_xp) hXpleX)
      hXθ hH hP₁lo hP₁hi hP₂lo hP₂hi (A'.isFam.1 x hx).1
  obtain ⟨S, hSmem, hScard⟩ :=
    Work.N8.compatible_pairs_v4 k δ hδpos hδle1 C1loc hC1locpos f c C₀C
      (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ P₂ ℓ A' Fg Kg hc hXppos hL1 hLleXp hP₁4
      hP₁Xp hFgcard hFggood hEdgemerge
      (fun e he e' he' h1 h2 => Work.N8.edge_unique P₁ (H / (P₁ * P₂)) A'.fam e e'
        hP₁pos hLpos hsep800 (A'.geom e he) (A'.geom e' he') h1 h2)
      hbadle
  have hSbig : δae * (X / (P₁ * P₂) / (H / (P₁ * P₂))) * Work.BMF.pi0 P₁ ^ 2
      ≤ (S.card : ℝ) := by
    have h2 : δae ≤ c / 4 := by rw [hδaedef]; linarith
    have h4 : δae * (X / (P₁ * P₂) / (H / (P₁ * P₂))) * Work.BMF.pi0 P₁ ^ 2
        ≤ c / 4 * (X / (P₁ * P₂) / (H / (P₁ * P₂))) * Work.BMF.pi0 P₁ ^ 2 := by
      have hA : (0:ℝ) ≤ Work.BMF.pi0 P₁ ^ 2 := sq_nonneg _
      have hA2 : (0:ℝ) ≤ X / (P₁ * P₂) / (H / (P₁ * P₂)) :=
        le_of_lt (div_pos hXppos hLpos)
      have hAB : (0:ℝ) ≤ (X / (P₁ * P₂) / (H / (P₁ * P₂))) * Work.BMF.pi0 P₁ ^ 2 :=
        mul_nonneg hA2 hA
      calc δae * (X / (P₁ * P₂) / (H / (P₁ * P₂))) * Work.BMF.pi0 P₁ ^ 2
          = δae * ((X / (P₁ * P₂) / (H / (P₁ * P₂))) * Work.BMF.pi0 P₁ ^ 2) := by ring
        _ ≤ c / 4 * ((X / (P₁ * P₂) / (H / (P₁ * P₂))) * Work.BMF.pi0 P₁ ^ 2) :=
            mul_le_mul_of_nonneg_right h2 hAB
        _ = c / 4 * (X / (P₁ * P₂) / (H / (P₁ * P₂))) * Work.BMF.pi0 P₁ ^ 2 := by ring
    linarith [hScard, h4]

  set dd : N8Quad → N8Quad → ℝ := fun u v =>
    (1 / (1000 * C1loc)) * |u.1 - v.1| / (X / H) +
      (if u.2.1 = v.2.1 then 0 else 1) with hdddef
  have hDv : ∀ u v : N8Quad, dd u v =
      (1 / (1000 * C1loc)) * |u.1 - v.1| / (X / H) + (if u.2.1 = v.2.1 then 0 else 1) :=
    fun u v => rfl
  have hdd_nn : ∀ u v, 0 ≤ dd u v := by
    intro u v
    rw [hDv u v]
    have h1 : 0 ≤ (1 / (1000 * C1loc)) * |u.1 - v.1| / (X / H) :=
      div_nonneg (mul_nonneg hinv1000C1pos.le (abs_nonneg _)) (div_pos hXpos hHpos).le
    by_cases h : u.2.1 = v.2.1
    · rw [if_pos h]; linarith
    · rw [if_neg h]; linarith
  have hdd_symm : ∀ u v, dd u v = dd v u := by
    intro u v
    rw [hDv u v, hDv v u]
    have h1 : (1 / (1000 * C1loc)) * |u.1 - v.1| / (X / H)
        = (1 / (1000 * C1loc)) * |v.1 - u.1| / (X / H) := by rw [abs_sub_comm]
    rw [h1]
    by_cases h : u.2.1 = v.2.1
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  have hdd_refl : ∀ u, dd u u = 0 := by
    intro u
    rw [hDv u u]
    simp
  have hdd_tri : ∀ a b c, dd a c ≤ dd a b + dd b c := by
    intro a b c
    have h1 : (1 / (1000 * C1loc)) * |a.1 - c.1| / (X / H) ≤
        (1 / (1000 * C1loc)) * |a.1 - b.1| / (X / H) +
        (1 / (1000 * C1loc)) * |b.1 - c.1| / (X / H) := by
      have hXH : (0:ℝ) < X / H := div_pos hXpos hHpos
      have habs : |a.1 - c.1| ≤ |a.1 - b.1| + |b.1 - c.1| := abs_sub_le _ _ _
      have hmul : (1 / (1000 * C1loc)) * |a.1 - c.1| ≤
          (1 / (1000 * C1loc)) * (|a.1 - b.1| + |b.1 - c.1|) :=
        mul_le_mul_of_nonneg_left habs hinv1000C1pos.le
      have hsplit : (1 / (1000 * C1loc)) * (|a.1 - b.1| + |b.1 - c.1|) / (X / H) =
          (1 / (1000 * C1loc)) * |a.1 - b.1| / (X / H) +
          (1 / (1000 * C1loc)) * |b.1 - c.1| / (X / H) := by ring
      calc (1 / (1000 * C1loc)) * |a.1 - c.1| / (X / H)
          ≤ (1 / (1000 * C1loc)) * (|a.1 - b.1| + |b.1 - c.1|) / (X / H) :=
            div_le_div_of_nonneg_right hmul (le_of_lt hXH)
        _ = _ := hsplit
    have h2 : (if a.2.1 = c.2.1 then (0:ℝ) else 1) ≤
        (if a.2.1 = b.2.1 then 0 else 1) + (if b.2.1 = c.2.1 then 0 else 1) := by
      split_ifs <;> first | (exfalso; omega) | norm_num
    rw [hDv a c, hDv a b, hDv b c]
    linarith [h1, h2]
  have hdd_doub : ∀ z : N8Quad, ∀ s : Finset N8Quad, (∀ w ∈ s, dd w z ≤ 5 * (1/10) / 2) →
      (∀ w ∈ s, ∀ w' ∈ s, w ≠ w' → (1/10) / 2 ≤ dd w w') → (s.card : ℝ) ≤ 100 := by
    intro z s hzs hsep
    have hNz : (0:ℝ) < X / H := div_pos hXpos hHpos
    have hC1 : (0:ℝ) < C1loc := hC1locpos
    have hqz : ∀ w ∈ s, w.2.1 = z.2.1 := by
      intro w hw
      have h := hzs w hw
      rw [hDv w z] at h
      by_contra hne
      rw [if_neg hne] at h
      have h1 : 0 ≤ (1 / (1000 * C1loc)) * |w.1 - z.1| / (X / H) :=
        div_nonneg (mul_nonneg hinv1000C1pos.le (abs_nonneg _)) (le_of_lt hNz)
      linarith
    set r : ℝ := 250 * C1loc * (X / H) with hrdef
    set B : ℝ := 50 * C1loc * (X / H) with hBdef
    have hinj : Set.InjOn (fun w : N8Quad => w.1) ↑s := by
      intro w hw w' hw' heq
      by_contra hne
      have h := hsep w hw w' hw' hne
      have hq : w.2.1 = w'.2.1 := by rw [hqz w hw, hqz w' hw']
      have heq' : w.1 = w'.1 := heq
      rw [hDv w w'] at h
      rw [if_pos hq, add_zero, heq', sub_self, abs_zero, mul_zero, zero_div] at h
      norm_num at h
    have hcard : (s.card : ℝ) = ((s.image (fun w => w.1)).card : ℝ) := by
      rw [Finset.card_image_of_injOn hinj]
    rw [hcard]
    have hb := Work.N8.ball_card_le r B z.1
      (by rw [hrdef]; exact mul_pos (mul_pos (by norm_num) hC1locpos) hNz)
      (by rw [hBdef]; exact mul_pos (mul_pos (by norm_num) hC1locpos) hNz)
      (s.image (fun w => w.1)) ?_ ?_
    · have h2rB : 2 * r / B = 10 := by
        rw [hrdef, hBdef]
        field_simp
        norm_num
      rw [h2rB] at hb
      linarith
    · intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      have h := hzs w hw
      rw [hDv w z, if_pos (hqz w hw), add_zero] at h
      rw [hrdef]
      have h2 : (1 / (1000 * C1loc)) * |w.1 - z.1| ≤ (1/4) * (X / H) := by
        have h' := h
        rw [div_le_iff₀ hNz] at h'
        linarith [h']
      have h3 : (1 / (1000 * C1loc)) * |w.1 - z.1| = |w.1 - z.1| / (1000 * C1loc) := by ring
      rw [h3, div_le_iff₀ h1000C1pos] at h2
      have h4 : (1/4) * (X / H) * (1000 * C1loc) = 250 * C1loc * (X / H) := by ring
      linarith [h2, h4.le, h4.ge]
    · intro y hy y' hy' hne
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨w', hw', hw'eq⟩ := Finset.mem_image.mp hy'
      rw [← hw'eq]
      have hne' : w ≠ w' := fun hh => hne (by rw [congrArg (fun z : N8Quad => z.1) hh, hw'eq])
      have h := hsep w hw w' hw' hne'
      have hq : w.2.1 = w'.2.1 := by rw [hqz w hw, hqz w' hw']
      rw [hDv w w', if_pos hq, add_zero] at h
      rw [hBdef]
      have h2 : (1/20) * (X / H) ≤ (1 / (1000 * C1loc)) * |w.1 - w'.1| := by
        have h' := h
        rw [le_div_iff₀ hNz] at h'
        linarith [h']
      have h3 : (1 / (1000 * C1loc)) * |w.1 - w'.1| = |w.1 - w'.1| / (1000 * C1loc) := by ring
      rw [h3, le_div_iff₀ h1000C1pos] at h2
      have h4 : (1/20) * (X / H) * (1000 * C1loc) = 50 * C1loc * (X / H) := by ring
      linarith [h2, h4.le, h4.ge]
  have hfam100 : ((A'.fam.card : ℕ) : ℝ) ≤ 100 * (X / (P₁ * P₂) / (H / (P₁ * P₂))) := by
    rw [hxdiv]
    linarith [hNf, hN13]
  have hmixApp : ∀ A₁ A₂ : Finset ℝ, A₁ ⊆ A'.fam → A₂ ⊆ A'.fam →
      (Work.BMF.quadCount (fun i i' p p' =>
        Work.BMF.EdgeGeom A'.fam P₁ (H / (P₁ * P₂)) ⟨i, i', p, p'⟩) P₁ A₁ A₂ : ℝ) ≤
      Cmix * ((A₁.card : ℝ) * (A₂.card : ℝ) * (H / X) * Work.BMF.pi0 P₁ ^ 2 +
        Real.sqrt ((A₁.card : ℝ) * (A₂.card : ℝ)) * Work.BMF.pi0 P₁ ^ 2 / Real.log P₁) := by
    intro A₁ A₂ hA₁ hA₂
    have hc₀pos : 0 < min (θ / 2) (ε ^ 2 / 2) / 2 := by
      exact div_pos (lt_min hθ2pos hε2pos) two_pos
    have hFrac : (H / (P₁ * P₂)) / (X / (P₁ * P₂)) = H / X := by field_simp
    have hm := hmix (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ A₁ A₂
      (le_trans (hM0_ge X₀mix (by simp)) hM0_le_xp)
      hPowP hP₁quart hPowL hLleXp
      (by intro x hx
          rcases Finset.mem_union.mp hx with h | h
          · exact ⟨(A'.isFam.1 x (hA₁ h)).1, by linarith [(A'.isFam.1 x (hA₁ h)).2, hLpos]⟩
          · exact ⟨(A'.isFam.1 x (hA₂ h)).1, by linarith [(A'.isFam.1 x (hA₂ h)).2, hLpos]⟩)
      (by intro x hx y hy hne
          exact le_trans (by linarith [hLpos]) (A'.isFam.2 x (hA₁ hx) y (hA₁ hy) hne))
      (by intro x hx y hy hne
          exact le_trans (by linarith [hLpos]) (A'.isFam.2 x (hA₂ hx) y (hA₂ hy) hne))
    have hsub : (((A₁.product A₂).product
          ((Work.BMF.primesIn P₁ (2 * P₁)).product (Work.BMF.primesIn P₁ (2 * P₁)))).filter
        (fun v => Work.BMF.EdgeGeom A'.fam P₁ (H / (P₁ * P₂)) ⟨v.1.1, v.1.2, v.2.1, v.2.2⟩))
        ⊆ (((A₁.product A₂).product
          ((Work.BMF.primesIn P₁ (2 * P₁)).product (Work.BMF.primesIn P₁ (2 * P₁)))).filter
        (fun v => |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * (H / (P₁ * P₂)))) :=
      Finset.monotone_filter_right _ (fun v _ hv => hv.2.2.2.2.2.2)
    have hcardle := Finset.card_le_card hsub
    have hquad : Work.BMF.quadCount (fun i i' p p' =>
        Work.BMF.EdgeGeom A'.fam P₁ (H / (P₁ * P₂)) ⟨i, i', p, p'⟩) P₁ A₁ A₂
        ≤ (((A₁.product A₂).product
          ((Work.BMF.primesIn P₁ (2 * P₁)).product (Work.BMF.primesIn P₁ (2 * P₁)))).filter
        (fun v => |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * (H / (P₁ * P₂)))).card :=
      hcardle
    have hcast : ((Work.BMF.quadCount (fun i i' p p' =>
        Work.BMF.EdgeGeom A'.fam P₁ (H / (P₁ * P₂)) ⟨i, i', p, p'⟩) P₁ A₁ A₂ : ℕ) : ℝ) ≤
        ((((A₁.product A₂).product
          ((Work.BMF.primesIn P₁ (2 * P₁)).product (Work.BMF.primesIn P₁ (2 * P₁)))).filter
        (fun v => |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * (H / (P₁ * P₂)))).card : ℝ) := by
      exact_mod_cast hquad
    calc (Work.BMF.quadCount (fun i i' p p' =>
          Work.BMF.EdgeGeom A'.fam P₁ (H / (P₁ * P₂)) ⟨i, i', p, p'⟩) P₁ A₁ A₂ : ℝ)
        ≤ _ := hcast
      _ ≤ Cmix * ((A₁.card : ℝ) * (A₂.card : ℝ) * ((H / (P₁ * P₂)) / (X / (P₁ * P₂)))
            * Work.BMF.pi0 P₁ ^ 2 +
          Real.sqrt ((A₁.card : ℝ) * (A₂.card : ℝ)) * Work.BMF.pi0 P₁ ^ 2 / Real.log P₁) := hm
      _ = Cmix * ((A₁.card : ℝ) * (A₂.card : ℝ) * (H / X) * Work.BMF.pi0 P₁ ^ 2 +
          Real.sqrt ((A₁.card : ℝ) * (A₂.card : ℝ)) * Work.BMF.pi0 P₁ ^ 2 / Real.log P₁) := by
        rw [hFrac]
  have hS_app : ∀ p ∈ S, p.1.1 ∈ A'.fam ∧ p.2.1 ∈ A'.fam ∧ p.1.2 ∈ Fg p.1.1 ∧
      p.2.2 ∈ Fg p.2.1 ∧
      (∃ p1 p2 : ℕ, p1 ∈ Work.BMF.primesIn P₁ (2 * P₁) ∧
        p2 ∈ Work.BMF.primesIn P₁ (2 * P₁) ∧
        Work.BMF.EdgeGeom A'.fam P₁ (H / (P₁ * P₂)) ⟨p.1.1, p.2.1, p1, p2⟩) ∧
      dd p.1.2 p.2.2 ≤ 1 / 10 := by
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hSmem p hp
    obtain ⟨p1, p2, hp1, hp2, hpne, hnd1, hnd2, hgeo, _hint⟩ := h7
    refine ⟨h1, h2, h3, h4, ⟨p1, p2, ?_, ?_, hgeo⟩, ?_⟩
    · exact (Work.BMF.mem_primesIn_iff (by linarith [hP₁pos])).mpr hp1
    · exact (Work.BMF.mem_primesIn_iff (by linarith [hP₁pos])).mpr hp2
    · have h7' : |p.1.2.1 - p.2.2.1| ≤ 2 * C1loc * (X / H) := by
        rw [hxdiv] at h6
        exact h6
      rw [hDv p.1.2 p.2.2, if_pos h5, add_zero]
      have hXH : (0:ℝ) < X / H := div_pos hXpos hHpos
      rw [div_le_iff₀ hXH]
      have h8 : (1 / (1000 * C1loc)) * |p.1.2.1 - p.2.2.1| ≤ (1/10) * (X / H) := by
        have h9 : (1 / (1000 * C1loc)) * |p.1.2.1 - p.2.2.1| ≤
            (1 / (1000 * C1loc)) * (2 * C1loc * (X / H)) :=
          mul_le_mul_of_nonneg_left h7' hinv1000C1pos.le
        have h10 : (1 / (1000 * C1loc)) * (2 * C1loc * (X / H)) = (1/500) * (X / H) := by
          field_simp
          ring
        rw [h10] at h9
        linarith [h9, hXH]
      exact h8
  have hae := Work.N8.approx_ergodicity_strong (ι := ℝ) (Z := N8Quad) (A'.fam) Fg Kg hKgpos
    hFgcard dd (1/10) (by norm_num) hdd_nn hdd_symm hdd_tri hdd_refl 100 (by norm_num) hdd_doub
    (fun i i' p p' => Work.BMF.EdgeGeom A'.fam P₁ (H / (P₁ * P₂)) ⟨i, i', p, p'⟩)
    P₁ (X / (P₁ * P₂)) (H / (P₁ * P₂)) (H / X) (Work.BMF.pi0 P₁) (Real.log P₁) δae Cmix
    hXppos hLpos (by exact div_pos hHpos hXpos)
    (by rw [Work.BMF.pi0]; exact div_pos hP₁pos hlogP₁pos) hlogP₁pos hδaepos hCmixpos
    (by have hh : (H / X) * (X / H) = 1 := by field_simp
        rw [hxdiv, hh])
    hfam100 (fun A₁ A₂ hA₁ hA₂ => hmixApp A₁ A₂ hA₁ hA₂) S hS_app hSbig

  rcases hae with hcontr | ⟨z₀, Tset, hTmem, hTcard, S', hS'sub, hS'T, hS'card⟩
  · exfalso
    have h1 : Real.log P₁ ≥ (ε ^ 2 / 2) * Real.log X := by
      have h2 : Real.log (X ^ (ε ^ 2 / 2)) ≤ Real.log P₁ :=
        Real.log_le_log (Real.rpow_pos_of_pos hXpos _) hP₁lo
      rwa [Real.log_rpow hXpos] at h2
    have h3 : Real.log X ≥ Lg * (2 / ε ^ 2) + 1 := by
      have h4 : Real.exp (Lg * (2 / ε ^ 2) + 1) ≤ X := by linarith [hXlogG]
      calc Lg * (2 / ε ^ 2) + 1 = Real.log (Real.exp (Lg * (2 / ε ^ 2) + 1)) :=
            (Real.log_exp _).symm
        _ ≤ Real.log X := Real.log_le_log (Real.exp_pos _) h4
    have h5 : (ε ^ 2 / 2) * (Lg * (2 / ε ^ 2) + 1) = Lg + ε ^ 2 / 2 := by
      field_simp
    have h6 : (ε ^ 2 / 2) * Real.log X ≥ Lg + ε ^ 2 / 2 := by
      rw [← h5]
      exact mul_le_mul_of_nonneg_left h3 hε2nonneg
    have h7 : Real.log P₁ ≤ Lg := by
      rw [hLgdef]
      exact hcontr
    linarith
  · ---------------------------------------------------------------------
    -- §8. Step 6: `q₀` is bounded
    ---------------------------------------------------------------------
    have hNL : (X / H) * (H / (P₁ * P₂)) = X / (P₁ * P₂) := by
      have h1 : (P₁ * P₂) ≠ 0 := ne_of_gt hP₁P₂pos
      have h2 : H ≠ 0 := ne_of_gt hHpos
      field_simp
    have hTgood' : ∀ p ∈ Tset,
        Work.BMF.GoodQuad A' δ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 :=
      fun p hp => hFggood p.1 p.2 (hTmem p hp).2.1
    have hTq : ∀ p ∈ Tset, p.2.2.1 = z₀.2.1 := by
      intro p hp
      by_contra hne
      have h1 := (hTmem p hp).2.2
      rw [hDv p.2 z₀, if_neg hne] at h1
      have h2 : 0 ≤ (1 / (1000 * C1loc)) * |p.2.1 - z₀.1| / (X / H) :=
        div_nonneg (mul_nonneg hinv1000C1pos.le (abs_nonneg _)) (le_of_lt (div_pos hXpos hHpos))
      linarith
    have hTdd : ∀ p ∈ Tset, dd p.2 z₀ ≤ 1 / 5 := fun p hp => by linarith [(hTmem p hp).2.2]
    have hTne : Tset.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have h1 := hTcard
      rw [hempty] at h1
      simp at h1
      have h3 : 0 < (1 / (10 : ℝ) ^ 7) * (δae / (Cmix * 100 * (Kg : ℝ) ^ 3)) *
          (X / (P₁ * P₂) / (H / (P₁ * P₂))) :=
        mul_pos (mul_pos (by norm_num)
          (div_pos hδaepos (by positivity : (0:ℝ) < Cmix * 100 * (Kg:ℝ) ^ 3)))
          (div_pos hXppos hLpos)
      linarith [h1, h3]
    obtain ⟨p₀, hp₀⟩ := hTne
    have hq₀pos : 1 ≤ z₀.2.1 := by
      rw [← hTq p₀ hp₀]
      exact (hTgood' p₀ hp₀).q_bound
    have hq₀le : z₀.2.1 ≤ Q₀ := by
      by_cases hk : 1 ≤ k
      · ------------------------------------------------------------------
        -- the case `1 ≤ k`: instantiate `step6_q0_bound_v2`
        ------------------------------------------------------------------
        obtain ⟨ℓ1, hℓ12, hℓ1even, hℓ1le, hℓ1d, hℓ1N, hℓ1P, hℓ1fac, _hℓ1log, hℓ1N3⟩ :=
          hs6 X H P₁ P₂ (le_trans (le_trans (hM0_ge X₀s6 (by simp)) hM0_le_xp) hXpleX)
            hXθ hH hP₁lo hP₁hi hP₂lo hP₂hi
        have hℓ1one : 1 ≤ ℓ1 := by omega
        have hGfℓ1 : Gf ℓ1 = Classical.choose (Work.N8.n4_uniform ℓ1 k hℓ1one hk) := by
          rw [hGfdef]
          simp only [dif_pos hk, dif_pos hℓ1one]
        have hBfℓ1 : Bf ℓ1 =
            Classical.choose (Classical.choose_spec (Work.N8.n4_uniform ℓ1 k hℓ1one hk)) := by
          rw [hBfdef]
          simp only [dif_pos hk, dif_pos hℓ1one]
        have hBfℓ1le : Bf ℓ1 ≤ Bmax := hBf_le_Bmax ℓ1 (Finset.mem_range.mpr (by omega))
        rw [hBfℓ1] at hBfℓ1le
        have hGpos1 : 0 < Gf ℓ1 := by
          rw [hGfℓ1]
          exact (Classical.choose_spec (Classical.choose_spec (Work.N8.n4_uniform ℓ1 k hℓ1one hk))).1
        have hCkbpos : 0 < Ckb := by
          rw [hCkbdef]
          simp only [dif_pos hk]
          exact (Classical.choose_spec (Work.N8.omega_totient_bound k)).1
        have hAbdef1 : ∀ (c₂' G Ck : ℝ),
            Ab ℓ1 c₂' G Ck = Classical.choose (Work.N8.step6_q0_bound_v2 k hk ε hε) ℓ1 c₂' G Ck := by
          intro c₂' G Ck
          rw [hAbdef]
          simp only [dif_pos hk]
        have hAbpos : 0 < Ab ℓ1 c₂ (Gf ℓ1) Ckb := by
          rw [hAbdef1]
          exact (Classical.choose_spec (Work.N8.step6_q0_bound_v2 k hk ε hε)).1 ℓ1 c₂ (Gf ℓ1) Ckb
        obtain ⟨AArc, EArc, prArc, posArc, γArc, hArcsym, hEAarc, hEcard, hposA, hγA, hposDA,
          hAdjdata, hfibA, hsepA⟩ :=
          Work.N8.arc_graph_data2 P₁ (H / (P₁ * P₂)) z₀.2.1 A'.fam Tset S' Fg Kg
            (X / (P₁ * P₂) / 10) hP₁pos hLpos (div_pos hXppos (by norm_num))
            (fun v hv => ⟨(hTmem v hv).1, (hTmem v hv).2.1⟩) hFgcard
            (fun v hv => hTq v hv)
            (fun x hx y hy hne => A'.isFam.2 x hx y hy hne)
            (fun v hv => (A'.isFam.1 v.1 (hTmem v hv).1).1)
            (fun p hp => by
              obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hSmem p (hS'sub hp)
              obtain ⟨p1, p2, hp1, hp2, hpne, hnd1, hnd2, hgeo, hint⟩ := h7
              exact ⟨(hS'T p hp).1, (hS'T p hp).2, p1, p2, hp1, hp2, hpne,
                by rw [← hTq p.1 (hS'T p hp).1]; exact hnd1,
                by rw [← hTq p.2 (hS'T p hp).2]; exact hnd2, hgeo, hint⟩)
        have hlogNbig : Mbig < Real.log (X / H) := by
          have h1 : Real.log X ≥ Mbig / θ + 1 := by
            have h2 : Real.exp (Mbig / θ + 1) ≤ X := by linarith [hXlogM]
            calc Mbig / θ + 1 = Real.log (Real.exp (Mbig / θ + 1)) := (Real.log_exp _).symm
              _ ≤ Real.log X := Real.log_le_log (Real.exp_pos _) h2
          have h3 : Real.log H ≤ (1 - θ) * Real.log X := by
            have h4 : Real.log H ≤ Real.log (X ^ (1 - θ)) := Real.log_le_log hHpos hH
            rwa [Real.log_rpow hXpos] at h4
          have h5 : Real.log (X / H) = Real.log X - Real.log H := Real.log_div hXpos.ne' hHpos.ne'
          have h6 : θ * (Mbig / θ + 1) ≤ θ * Real.log X :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hθ₀)
          rw [h5]
          have h8 : θ * (Mbig / θ + 1) = Mbig + θ := by
            field_simp
          have h9 : Mbig + θ ≤ θ * Real.log X := by linarith [h6, h8]
          have h10 : θ * Real.log X ≤ Real.log X - Real.log H := by linarith [h3]
          linarith [h9, h10, hθ₀]
        have hNpos : 0 < X / H := by linarith [hℓ1N3]
        have hVcard : (Finset.univ : Finset {v : ℝ × N8Quad // v ∈ Tset}).card = Tset.card := by
          rw [Finset.card_univ]
          exact Fintype.card_coe Tset
        have hstep6 := (Classical.choose_spec (Work.N8.step6_q0_bound_v2 k hk ε hε)).2
          ℓ1 hℓ12 hℓ1even AArc hArcsym
          (Finset.univ : Finset {v : ℝ × N8Quad // v ∈ Tset}) posArc prArc γArc z₀.2.1 hq₀pos
          P₁ (X / H) (H / (P₁ * P₂)) (X / (P₁ * P₂) / 10) cE c₂ (Gf ℓ1) Bmax Ckb Kg
          hGpos1 hBmax_pos hCkbpos hBmax_le
          (fun m hm1 hmk P' N' C₀ q hBP' hN3' hNle' hC₀ hq1 => by
            have h := (Classical.choose_spec
                (Classical.choose_spec (Work.N8.n4_uniform ℓ1 k hℓ1one hk))).2.2
              m hm1 hmk P' N' C₀ q (le_trans hBfℓ1le hBP') hN3' hNle' hC₀ hq1
            rw [← hGfℓ1] at h
            exact h)
          (fun m q hm1 hmk hq1 => by
            have h := (Classical.choose_spec (Work.N8.omega_totient_bound k)).2 m q hm1 hmk hq1
            rw [hCkbdef]
            simp only [dif_pos hk]
            exact h)
          (fun v _ => by
            rw [hγA v]
            exact Polynomial.natDegree_le_iff_degree_le.mpr
              (Polynomial.mem_degreeLE.mp (hTgood' v.1 v.2).deg))
          (fun v _ => by
            rw [hγA v, ← hTq v.1 v.2]
            exact (hTgood' v.1 v.2).int_coarse)
          (fun v _ r hr hInt => by
            rw [hγA v] at hInt
            rw [← hTq v.1 v.2]
            exact (hTgood' v.1 v.2).minimal r hr hInt)
          (fun v _ v' _ hadj => ⟨(hAdjdata v v' hadj).2.2.1, (hAdjdata v v' hadj).2.2.2.1⟩)
          (fun v _ v' _ hadj => ⟨(hAdjdata v v' hadj).1, (hAdjdata v v' hadj).2.1,
            (hAdjdata v v' hadj).2.2.2.2.1⟩)
          (fun v _ v' _ hadj => (hAdjdata v v' hadj).2.2.2.2.2)
          (fun y => hfibA y)
          (fun v _ v' _ hne => hsepA v v' hne)
          (fun v _ => hposDA v)
          (div_pos hXppos (by norm_num)) hLpos hP₁1 hlogP₁1 hℓ1fac
          (by rw [hNL]; linarith) hℓ1N3 hℓ1N hℓ1d hcEpos hc₂pos
          (by
            rw [hVcard]
            have h2 : cE * (X / H) ≤ (Tset.card : ℝ) := by
              have h1 : cE ≤ (1 / (10 : ℝ) ^ 7) * (δae / (Cmix * 100 * (Kg : ℝ) ^ 3)) := hcE_le1
              have h2' : cE * (X / H) ≤
                  (1 / (10 : ℝ) ^ 7) * (δae / (Cmix * 100 * (Kg : ℝ) ^ 3)) * (X / H) :=
                mul_le_mul_of_nonneg_right h1 (le_of_lt (div_pos hXpos hHpos))
              have h3 : (1 / (10 : ℝ) ^ 7) * (δae / (Cmix * 100 * (Kg : ℝ) ^ 3)) * (X / H)
                  ≤ (Tset.card : ℝ) := by
                rw [hxdiv] at hTcard
                exact hTcard
              linarith [h2', h3]
            exact h2)
          (by
            rw [hVcard]
            have h4 : ((Tset.image (fun p => p.1)).card : ℝ) * (Kg : ℝ) ≤
                100 * (X / (P₁ * P₂) / (H / (P₁ * P₂))) * (Kg : ℝ) := by
              have h5 : ((Tset.image (fun p => p.1)).card : ℝ) ≤ ((A'.fam.card : ℕ) : ℝ) := by
                exact_mod_cast Finset.card_le_card
                  (Finset.image_subset_iff.mpr (fun p hp => (hTmem p hp).1))
              exact mul_le_mul_of_nonneg_right (le_trans h5 hfam100) hKgRpos.le
            have h6 : ((Tset.card : ℕ) : ℝ) ≤ ((Tset.image (fun p => p.1)).card : ℝ) * (Kg : ℝ) := by
              have h7 : Tset.card ≤ Kg * (Tset.image (fun p => p.1)).card := by
                refine Finset.card_le_mul_card_image (f := fun p : ℝ × N8Quad => p.1) Tset Kg ?_
                intro b hb
                refine le_trans ?_ (hFgcard b)
                have hinj : Set.InjOn (fun a : ℝ × N8Quad => a.2)
                    ↑({a ∈ Tset | a.1 = b} : Finset (ℝ × N8Quad)) := by
                  intro a ha a' ha' heq
                  simp only [Finset.mem_filter, Finset.mem_coe] at ha ha'
                  exact Prod.ext (by rw [ha.2, ha'.2]) heq
                calc ({a ∈ Tset | a.1 = b}).card
                    = (({a ∈ Tset | a.1 = b}).image (fun a => a.2)).card :=
                      (Finset.card_image_of_injOn hinj).symm
                  _ ≤ (Fg b).card := by
                      refine Finset.card_le_card ?_
                      intro w hw
                      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
                      simp only [Finset.mem_filter] at ha
                      have h8 := (hTmem a ha.1).2.1
                      rwa [ha.2] at h8
              have h7' : ((Tset.card : ℕ) : ℝ) ≤
                  (Kg : ℝ) * ((Tset.image (fun p => p.1)).card : ℝ) := by exact_mod_cast h7
              linarith [h7', mul_comm (Kg : ℝ) (((Tset.image (fun p => p.1)).card : ℕ) : ℝ)]
            have h9 : (Tset.card : ℝ) ≤ 100 * (X / (P₁ * P₂) / (H / (P₁ * P₂))) * (Kg : ℝ) :=
              le_trans h6 h4
            have h10 : (100 : ℝ) * (X / (P₁ * P₂) / (H / (P₁ * P₂))) * (Kg : ℝ)
                = c₂ * (X / (P₁ * P₂) / (H / (P₁ * P₂))) := by
              rw [hc₂def]; ring
            rw [h10, hxdiv] at h9
            exact h9)
          (by
            have h5 : cE * (P₁ / Real.log P₁) ^ 2 * (X / H) ≤ (S'.card : ℝ) := by
              rw [hxdiv] at hS'card
              have hA : (0:ℝ) ≤ (X / H) * Work.BMF.pi0 P₁ ^ 2 :=
                mul_nonneg (le_of_lt (div_pos hXpos hHpos)) (sq_nonneg _)
              have h6 : cE * (P₁ / Real.log P₁) ^ 2 * (X / H) ≤
                  (1 / (10 : ℝ) ^ 7) * (δae ^ 2 / (Cmix * 100 * (Kg : ℝ) ^ 4)) *
                    (X / H) * Work.BMF.pi0 P₁ ^ 2 := by
                have h1 : cE ≤ (1 / (10:ℝ)^7) * (δae ^ 2 / (Cmix * 100 * (Kg:ℝ) ^ 4)) := hcE_le2
                have hA2 : (0:ℝ) ≤ Work.BMF.pi0 P₁ ^ 2 * (X / H) :=
                  mul_nonneg (sq_nonneg _) (le_of_lt (div_pos hXpos hHpos))
                have h2 := mul_le_mul_of_nonneg_right h1 hA2
                calc cE * (P₁ / Real.log P₁) ^ 2 * (X / H)
                    = cE * (Work.BMF.pi0 P₁ ^ 2 * (X / H)) := by
                      simp only [Work.BMF.pi0]; ring
                  _ ≤ (1 / (10:ℝ)^7) * (δae ^ 2 / (Cmix * 100 * (Kg:ℝ) ^ 4)) *
                        (Work.BMF.pi0 P₁ ^ 2 * (X / H)) := h2
                  _ = (1 / (10 : ℝ) ^ 7) * (δae ^ 2 / (Cmix * 100 * (Kg : ℝ) ^ 4)) *
                        (X / H) * Work.BMF.pi0 P₁ ^ 2 := by
                      simp only [Work.BMF.pi0]; ring
              linarith [h6, hS'card]
            have h1 : ((EArc.card : ℕ) : ℝ) ≤
                ((Finset.univ.filter (fun p : {v : ℝ × N8Quad // v ∈ Tset} ×
                  {v : ℝ × N8Quad // v ∈ Tset} =>
                  p.1 ∈ (Finset.univ : Finset {v : ℝ × N8Quad // v ∈ Tset}) ∧
                  p.2 ∈ (Finset.univ : Finset {v : ℝ × N8Quad // v ∈ Tset}) ∧
                  AArc p.1 p.2)).card : ℝ) := by
              apply Nat.cast_le.mpr
              refine Finset.card_le_card ?_
              intro p hp
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hEAarc p hp
            linarith [h1, h5, hEcard])
        have hstep6' : (cE / c₂) ^ ℓ1 ≤
            Ab ℓ1 c₂ (Gf ℓ1) Ckb * (Kg : ℝ) ^ ℓ1 * ((z₀.2.1 : ℝ) ^ (-(1 / (2 * (k : ℝ)))) +
              1 / Real.log (X / H)) := by
          rw [hAbdef1]
          exact hstep6
        have hfin := Work.N8.q0_from_bound k hk cE c₂ (Kg : ℝ) (X / H) (z₀.2.1)
          (Ab ℓ1 c₂ (Gf ℓ1) Ckb) ℓ1 hAbpos hcEpos hc₂pos hKgRpos
          hℓ1one hNpos (by exact_mod_cast hq₀pos)
          (lt_of_le_of_lt (hMbig_ge ℓ1 (Finset.mem_range.mpr (by omega))) hlogNbig)
          hstep6'
        have hQ₀ge := hQ₀_ge ℓ1 (Finset.mem_range.mpr (by omega))
        have hfin' : ((z₀.2.1 : ℕ) : ℝ) ≤ (Q₀ : ℝ) := le_trans hfin hQ₀ge
        exact_mod_cast hfin'
      · ------------------------------------------------------------------
        -- the case `k = 0`: `γ` is a constant and minimality forces `q₀ = 1`
        ------------------------------------------------------------------
        have hk0 : k = 0 := by omega
        have hQ₀1 : 1 ≤ Q₀ := hQ₀pos
        have hγconst : ∀ p ∈ Tset, ∃ a : ℝ, p.2.2.2.2.1 = Polynomial.C a := by
          intro p hp
          have h := (hTgood' p hp).deg
          rw [Polynomial.mem_degreeLE] at h
          have h2 : (p.2.2.2.2.1).natDegree ≤ k := Polynomial.natDegree_le_iff_degree_le.mpr h
          rw [hk0] at h2
          obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp (Nat.le_zero.mp h2)
          exact ⟨a, ha.symm⟩
        obtain ⟨a, ha⟩ := hγconst p₀ hp₀
        have hint0 : Work.BMF.IntegralOn (z₀.2.1 : ℝ) (Polynomial.C a) := by
          rw [← ha, ← hTq p₀ hp₀]
          exact (hTgood' p₀ hp₀).int_coarse
        obtain ⟨m, hm⟩ := hint0 0
        have hma : a = (m : ℝ) := by
          have h1 : (Polynomial.C a).eval ((z₀.2.1 : ℝ) * ((0 : ℤ) : ℝ)) = a := by
            rw [Polynomial.eval_C]
          rw [h1] at hm
          exact hm
        have hInt1 : Work.BMF.IntegralOn (((1:ℕ):ℝ)) (Polynomial.C a) := by
          intro n
          refine ⟨m, ?_⟩
          rw [show (((1:ℕ):ℝ)) * (n : ℝ) = (n : ℝ) by norm_num, Polynomial.eval_C]
          exact hma
        have hle1 : z₀.2.1 ≤ 1 := by
          rw [← hTq p₀ hp₀]
          exact (hTgood' p₀ hp₀).minimal 1 (le_refl 1) (by rw [ha]; exact hInt1)
        have heq1 : z₀.2.1 = 1 := le_antisymm hle1 hq₀pos
        rw [heq1]
        exact hQ₀1
    ---------------------------------------------------------------------
    -- §9. The extraction: `Ψ`, `x ↦ ψ_x`, and the global `Y`
    ---------------------------------------------------------------------
    obtain ⟨Ψ, hΨmem, hΨper, hΨcard⟩ := hR₀psi z₀.2.1 hq₀pos hq₀le
      (Tset.image (fun p => p.2)) (fun v => v.2.2.2.1)
      (fun v hv => by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
        exact Polynomial.natDegree_le_iff_degree_le.mpr
          (Polynomial.mem_degreeLE.mp (hTgood' p hp).deg))
      (fun v hv => by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
        rw [← hTq p hp]
        exact (hTgood' p hp).int_coarse)
    have hrQ : k.factorial * z₀.2.1 ^ k ≤ R₀ := by
      have h1 : k.factorial * z₀.2.1 ^ k ≤ k.factorial * Q₀ ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq₀le k)
      exact le_trans h1 hR₀le
    have hXt_mem : ∀ x ∈ Tset.image (fun p => p.1), x ∈ A'.fam := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact (hTmem p hp).1
    have hXt_place : ∀ x ∈ Tset.image (fun p => p.1),
        X / (P₁ * P₂) / 10 ≤ x ∧ x + H / (P₁ * P₂) ≤ 10 * (X / (P₁ * P₂)) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact A'.isFam.1 p.1 (hTmem p hp).1
    have hXt_sep : ∀ x ∈ Tset.image (fun p => p.1), ∀ x' ∈ Tset.image (fun p => p.1),
        x ≠ x' → 2 * (H / (P₁ * P₂)) ≤ |x - x'| := by
      intro x hx x' hx' hne
      exact le_trans (by linarith [hLpos]) (A'.isFam.2 x (hXt_mem x hx) x' (hXt_mem x' hx') hne)
    have hXt_card : cA * (X / H) ≤ ((Tset.image (fun p => p.1)).card : ℝ) := by
      have h6 : ((Tset.card : ℕ) : ℝ) ≤ ((Tset.image (fun p => p.1)).card : ℝ) * (Kg : ℝ) := by
        have h7 : Tset.card ≤ Kg * (Tset.image (fun p => p.1)).card := by
          refine Finset.card_le_mul_card_image (f := fun p : ℝ × N8Quad => p.1) Tset Kg ?_
          intro b hb
          refine le_trans ?_ (hFgcard b)
          have hinj : Set.InjOn (fun a : ℝ × N8Quad => a.2)
              ↑({a ∈ Tset | a.1 = b} : Finset (ℝ × N8Quad)) := by
            intro a ha a' ha' heq
            simp only [Finset.mem_filter, Finset.mem_coe] at ha ha'
            obtain ⟨haT, ha1⟩ := ha
            obtain ⟨ha'T, ha'1⟩ := ha'
            exact Prod.ext (by rw [ha1, ha'1]) heq
          calc ({a ∈ Tset | a.1 = b}).card
              = (({a ∈ Tset | a.1 = b}).image (fun a => a.2)).card :=
                (Finset.card_image_of_injOn hinj).symm
            _ ≤ (Fg b).card := by
                refine Finset.card_le_card ?_
                intro w hw
                obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
                simp only [Finset.mem_filter] at ha
                have h8 := (hTmem a ha.1).2.1
                rwa [ha.2] at h8
        have h7' : ((Tset.card : ℕ) : ℝ) ≤ (Kg : ℝ) * ((Tset.image (fun p => p.1)).card : ℝ) := by
          exact_mod_cast h7
        linarith [h7', mul_comm (Kg : ℝ) (((Tset.image (fun p => p.1)).card : ℕ) : ℝ)]
      have hlow : cE * (X / H) ≤ (Tset.card : ℝ) := by
        rw [hxdiv] at hTcard
        exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
          (le_of_lt (div_pos hXpos hHpos))) hTcard
      have h8 : cA * (X / H) ≤ cE * (X / H) / (2 * (Kg : ℝ)) := by
        have h9 : cA * (X / H) ≤ cE / (2 * (Kg : ℝ)) * (X / H) :=
          mul_le_mul_of_nonneg_right hcA_le' (le_of_lt (div_pos hXpos hHpos))
        calc cA * (X / H) ≤ cE / (2 * (Kg : ℝ)) * (X / H) := h9
          _ = cE * (X / H) / (2 * (Kg : ℝ)) := by ring
      have h10 : cE * (X / H) / (2 * (Kg : ℝ)) * (Kg : ℝ) ≤ ((Tset.card : ℕ) : ℝ) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ h2Kgpos]
        nlinarith [hlow, hKgRpos]
      have h11 : cA * (X / H) * (Kg : ℝ) ≤ ((Tset.image (fun p => p.1)).card : ℝ) * (Kg : ℝ) :=
        le_trans (le_trans (mul_le_mul_of_nonneg_right h8 hKgRpos.le) h10) h6
      exact le_of_mul_le_mul_right h11 hKgRpos
    have hXt_local : ∀ x ∈ Tset.image (fun p => p.1), ∃ ψ ∈ Ψ,
        Work.BMF.LocalTwist f ψ z₀.1 x (H / (P₁ * P₂)) (cstar * (H / (P₁ * P₂))) cA := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have hgood := hTgood' p hp
      have hcorr : c * (H / (P₁ * P₂)) ≤ ‖Work.BMF.corr f (A'.pol p.1) p.1 (H / (P₁ * P₂))‖ :=
        A'.corr_ge p.1 hgood.x_mem
      have hx1 : 1 ≤ p.1 := by
        have h := (A'.isFam.1 p.1 (hTmem p hp).1).1
        have h2 : (10:ℝ) ≤ X / (P₁ * P₂) := by linarith [hXp10]
        linarith
      have h8L : 8 ≤ c * (H / (P₁ * P₂)) := by
        have h8c : (0:ℝ) < 8 / c := div_pos (by norm_num) hc
        have h3 : X ^ (θ / 2) ≥ 8 / c := by
          have h4 : (8 / c + 1) ^ (2 / θ) ≤ X := le_trans (hmem _ (by simp)) hX
          have h5 : ((8 / c + 1) ^ (2 / θ)) ^ (θ / 2) = 8 / c + 1 := by
            rw [← Real.rpow_mul (le_of_lt (by linarith : (0:ℝ) < 8 / c + 1))]
            rw [show 2 / θ * (θ / 2) = 1 by field_simp]
            exact Real.rpow_one _
          calc 8 / c = (8 / c + 1) - 1 := by ring
            _ ≤ (8 / c + 1) := by linarith
            _ = ((8 / c + 1) ^ (2 / θ)) ^ (θ / 2) := h5.symm
            _ ≤ X ^ (θ / 2) := Real.rpow_le_rpow
              (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le h8c
                (le_add_of_nonneg_right zero_le_one))) _) h4 hθ2nonneg
        have h6 : c * (8 / c) = 8 := by field_simp
        have h2 : (8:ℝ) ≤ c * X ^ (θ / 2) :=
          calc (8:ℝ) = c * (8 / c) := h6.symm
            _ ≤ c * X ^ (θ / 2) := mul_le_mul_of_nonneg_left h3 hc.le
        exact le_trans h2 (mul_le_mul_of_nonneg_left hLge2 hc.le)
      have hTdiff : |p.2.1 - z₀.1| ≤ cT2 * (p.1 / (H / (P₁ * P₂))) := by
        have h1 := hTdd p hp
        rw [hDv p.2 z₀, if_pos (hTq p hp), add_zero] at h1
        have hXH : (0:ℝ) < X / H := div_pos hXpos hHpos
        rw [div_le_iff₀ hXH] at h1
        have h2 : (1 / (1000 * C1loc)) * |p.2.1 - z₀.1| ≤ (1/5) * (X / H) := by linarith [h1]
        rw [div_mul_eq_mul_div, div_le_iff₀ h1000C1pos] at h2
        have h3 : |p.2.1 - z₀.1| ≤ 200 * C1loc * (X / H) := by linarith [h2]
        have h4 : (X / H) ≤ 10 * (p.1 / (H / (P₁ * P₂))) := by
          have h5 : (X / H) * (H / (P₁ * P₂)) / 10 ≤ p.1 := by
            have h := (A'.isFam.1 p.1 (hTmem p hp).1).1
            rwa [← hNL] at h
          have h6 : (X / H) * (H / (P₁ * P₂)) ≤ 10 * p.1 := by linarith
          have h7 : (X / H) ≤ 10 * p.1 / (H / (P₁ * P₂)) := by
            rw [le_div_iff₀ hLpos]
            linarith
          calc (X / H) ≤ 10 * p.1 / (H / (P₁ * P₂)) := h7
            _ = 10 * (p.1 / (H / (P₁ * P₂))) := by ring
        have h5 : 2000 * C1loc ≤ cT2 := by
          rw [hcT2def]
          exact le_max_right _ _
        have h6 : (0:ℝ) < p.1 / (H / (P₁ * P₂)) := by
          have h7 : (0:ℝ) < p.1 := by linarith [hx1]
          exact div_pos h7 hLpos
        have h4' : 200 * C1loc * (X / H)
            ≤ 200 * C1loc * (10 * (p.1 / (H / (P₁ * P₂)))) :=
          mul_le_mul_of_nonneg_left h4 (by linarith [hC1locpos])
        have h5' : 200 * C1loc * (10 * (p.1 / (H / (P₁ * P₂))))
            ≤ cT2 * (p.1 / (H / (P₁ * P₂))) := by
          rw [show 200 * C1loc * (10 * (p.1 / (H / (P₁ * P₂))))
              = 2000 * C1loc * (p.1 / (H / (P₁ * P₂))) by ring]
          exact mul_le_mul_of_nonneg_right h5 h6.le
        linarith [h3, h4', h5']
      have hlt := hExtract f p.2.1 z₀.1 p.1 (H / (P₁ * P₂)) (A'.pol p.1) p.2.2.2.2.1 hf
        hL1 hx1 h8L hTdiff hgood.decomp hcorr
      have hmem : p.2 ∈ Tset.image (fun p => p.2) := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      have hmemψ : (fun n : ℕ => Work.BMF.eC (-(p.2.2.2.2.1).eval (n : ℝ))) ∈ Ψ :=
        hΨmem p.2 hmem
      refine ⟨fun n => Work.BMF.eC (-(p.2.2.2.2.1).eval (n : ℝ)), hmemψ, ?_⟩
      have hmono : (cdbl * c) * (H / (P₁ * P₂)) * (cstar * (H / (P₁ * P₂)))
          ≤ ∫ y in p.1..(p.1 + H / (P₁ * P₂)),
            ‖∑ n ∈ Work.BMF.natIcc y (y + (cstar * (H / (P₁ * P₂)))), f n *
              (fun n : ℕ => Work.BMF.eC (-(p.2.2.2.2.1).eval (n : ℝ))) n *
              (n : ℂ) ^ (-(Complex.I * z₀.1))‖ := hlt
      have hLnn : 0 ≤ H / (P₁ * P₂) := le_of_lt hLpos
      have hH'nn : 0 ≤ cstar * (H / (P₁ * P₂)) := mul_nonneg hcstarpos.le hLpos.le
      have : cA * (H / (P₁ * P₂)) * (cstar * (H / (P₁ * P₂)))
          ≤ (cdbl * c) * (H / (P₁ * P₂)) * (cstar * (H / (P₁ * P₂))) := by
        apply mul_le_mul_of_nonneg_right _ hH'nn
        exact mul_le_mul_of_nonneg_right hcA_le hLnn
      exact le_trans this hmono

    obtain ⟨ψ, hψΨ, Y, hY₀N, hYsqrt, hYX, hY64, hYtw⟩ :=
      hagg ((X / H) * (H / (P₁ * P₂)) / 10) (X / H) (H / (P₁ * P₂))
        (cstar * (H / (P₁ * P₂))) z₀.1 X f
        (Tset.image (fun p => p.1)) Ψ (k.factorial * z₀.2.1 ^ k)
        hLpos (mul_pos hcstarpos hLpos)
        (mul_le_of_le_one_left hLpos.le hcstarle1) (by linarith [hN3])
        (by
          have h16cA : (0:ℝ) < 16 / cA := div_pos (by norm_num) hcApos
          have h16p : (0:ℝ) < 16 / cA + 1 := lt_of_lt_of_le h16cA (le_add_of_nonneg_right zero_le_one)
          have h3 : ((16 / cA + 1) ^ (1 / θ)) ^ θ = 16 / cA + 1 := by
            rw [← Real.rpow_mul h16p.le]
            rw [show 1 / θ * θ = 1 by field_simp]
            exact Real.rpow_one _
          have h4 : 16 / cA + 1 ≤ X ^ θ := by
            rw [← h3]
            exact Real.rpow_le_rpow (Real.rpow_nonneg h16p.le _)
              (le_trans (hmem _ (by simp)) hX) (le_of_lt hθ₀)
          have h5 : X ^ θ ≤ X / H := by
            rw [le_div_iff₀ hHpos]
            calc X ^ θ * H ≤ X ^ θ * X ^ (1 - θ) :=
                  mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hXpos.le _)
              _ = X := by rw [← Real.rpow_add hXpos, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
          have h6 : 16 ≤ cA * (16 / cA) := by
            rw [mul_div_cancel₀ _ (ne_of_gt hcApos)]
          have h4' : 16 / cA ≤ X ^ θ := le_trans (le_add_of_nonneg_right zero_le_one) h4
          have h7 : (16:ℝ) ≤ cA * X ^ θ := le_trans h6 (mul_le_mul_of_nonneg_left h4' hcApos.le)
          have h8 : cA * X ^ θ ≤ cA * (X / H) := mul_le_mul_of_nonneg_left h5 hcApos.le
          linarith [h7, h8])
        hrQ hΨcard hΨper hXt_local
        (by intro x hx
            obtain ⟨h1, h2⟩ := hXt_place x hx
            rw [hNL]
            exact ⟨h1, h2⟩)
        hXt_sep hXt_card
        (by rw [hNL]; exact h10sqrt)
        (by rw [hNL]; exact h10Xp)
        (le_refl _)
    have hYN : X / (P₁ * P₂) / 10 ≤ Y := by
      rw [hNL] at hY₀N
      exact hY₀N
    refine ⟨z₀.1, k.factorial * z₀.2.1 ^ k, ψ, Y, cstar * (H / (P₁ * P₂)),
      ?_, hrQ, hΨper ψ hψΨ, ?_, hYsqrt, hYX, ?_, ?_, ?_, hYtw⟩
    · -- |T₀| ≤ C' X^{k+1}/H^{k+1}
      have hNpow : C' * X ^ (k + 1) / H ^ (k + 1) = C' * (X / H) ^ (k + 1) := by
        rw [div_pow]
        ring
      rw [hNpow]
      have h1 : |z₀.1| ≤ |p₀.2.1| + |p₀.2.1 - z₀.1| := by
        calc |z₀.1| = |p₀.2.1 - (p₀.2.1 - z₀.1)| := by
              rw [show p₀.2.1 - (p₀.2.1 - z₀.1) = z₀.1 by ring]
          _ ≤ |p₀.2.1| + |p₀.2.1 - z₀.1| := abs_sub p₀.2.1 (p₀.2.1 - z₀.1)
      have h2 : |p₀.2.1| ≤ δ⁻¹ * (X / H) ^ (k + 1) := by
        have h := (hTgood' p₀ hp₀).T_bound
        rwa [hxdiv] at h
      have h3 : |p₀.2.1 - z₀.1| ≤ 200 * C1loc * (X / H) := by
        have h := hTdd p₀ hp₀
        rw [hDv p₀.2 z₀, if_pos (hTq p₀ hp₀), add_zero] at h
        have hXH : (0:ℝ) < X / H := div_pos hXpos hHpos
        rw [div_le_iff₀ hXH] at h
        have h4 : (1 / (1000 * C1loc)) * |p₀.2.1 - z₀.1| ≤ (1 / 5) * (X / H) := by linarith [h]
        have h5 : (1000 * C1loc) * ((1 / (1000 * C1loc)) * |p₀.2.1 - z₀.1|)
            = |p₀.2.1 - z₀.1| := by field_simp
        have h6 : (1000 * C1loc) * ((1 / 5) * (X / H)) = 200 * C1loc * (X / H) := by ring
        have h7 := mul_le_mul_of_nonneg_left h4 h1000C1nonneg
        rw [h5, h6] at h7
        exact h7
      have h8 : (1:ℝ) ≤ X / H := by linarith [hN3]
      have h9 : X / H ≤ (X / H) ^ (k + 1) := by
        calc X / H = (X / H) ^ 1 := (pow_one _).symm
          _ ≤ (X / H) ^ (k + 1) := pow_le_pow_right₀ h8 (by omega)
      have h10 : 200 * C1loc * (X / H) ≤ 200 * C1loc * (X / H) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left h9 (by linarith [hC1locpos])
      have h11 : δ⁻¹ * (X / H) ^ (k + 1) + 200 * C1loc * (X / H) ^ (k + 1)
          ≤ C' * (X / H) ^ (k + 1) := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right hC'_geT
          (pow_nonneg (le_of_lt (div_pos hXpos hHpos)) _)
      linarith [h1, h2, h3, h10, h11]
    · -- Y₀ ≤ Y
      exact le_trans hY₀_le hYN
    · -- Y^{θ/2} ≤ H'
      have hA1 : (max 1 (6.4 ^ (θ / 2) / cstar)) ^ (100 / θ) ≤ X :=
        le_trans (hmem _ (by simp)) hX
      have hY64c := hY64
      have hY64' : Y ≤ 6.4 * (X / (P₁ * P₂)) := by
        rw [hNL] at hY64c
        linarith [hY64c]
      have h1 : Y ^ (θ / 2) ≤ (6.4 * (X / (P₁ * P₂))) ^ (θ / 2) :=
        Real.rpow_le_rpow (le_of_lt (lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hYsqrt)) hY64' hθ2nonneg
      have h2 : (6.4 * (X / (P₁ * P₂))) ^ (θ / 2) ≤ cstar * X ^ (θ - 2 * ε) := by
        have h3 : (6.4 * (X / (P₁ * P₂))) ^ (θ / 2)
            = 6.4 ^ (θ / 2) * (X / (P₁ * P₂)) ^ (θ / 2) :=
          Real.mul_rpow (by norm_num) hXppos.le
        rw [h3]
        have h4 : (X / (P₁ * P₂)) ^ (θ / 2) ≤ X ^ (θ / 2) :=
          Real.rpow_le_rpow (le_of_lt hXppos) hXpleX hθ2nonneg
        have h5 : X ^ (θ / 2 - 2 * ε) * X ^ (θ / 2) = X ^ (θ - 2 * ε) := by
          rw [← Real.rpow_add hXpos]
          ring_nf
        have h6 : 6.4 ^ (θ / 2) / cstar ≤ X ^ (θ / 2 - 2 * ε) := by
          have hB1 : (1:ℝ) ≤ max 1 (6.4 ^ (θ / 2) / cstar) := le_max_left _ _
          have hB2 : 6.4 ^ (θ / 2) / cstar ≤ max 1 (6.4 ^ (θ / 2) / cstar) := le_max_right _ _
          have hmax_eq : (max 1 (6.4 ^ (θ / 2) / cstar))
              = ((max 1 (6.4 ^ (θ / 2) / cstar)) ^ (100 / θ)) ^ (θ / 100) := by
            rw [← Real.rpow_mul (le_trans zero_le_one hB1)]
            rw [show 100 / θ * (θ / 100) = 1 by field_simp]
            exact (Real.rpow_one _).symm
          have hBX : (max 1 (6.4 ^ (θ / 2) / cstar)) ≤ X ^ (θ / 100) := by
            rw [hmax_eq]
            exact Real.rpow_le_rpow (Real.rpow_nonneg (le_trans zero_le_one hB1) _) hA1
              (by linarith [hθ₀])
          have hexp2 : θ / 100 * (50 - 200 * (ε / θ)) = θ / 2 - 2 * ε := by
            field_simp
            ring
          have hXexp : X ^ (θ / 2 - 2 * ε) = (X ^ (θ / 100)) ^ (50 - 200 * (ε / θ)) := by
            rw [← hexp2]
            exact Real.rpow_mul hXpos.le _ _
          calc 6.4 ^ (θ / 2) / cstar ≤ max 1 (6.4 ^ (θ / 2) / cstar) := hB2
            _ ≤ X ^ (θ / 100) := hBX
            _ ≤ (X ^ (θ / 100)) ^ (50 - 200 * (ε / θ)) := by
                have hW1 : (1:ℝ) ≤ X ^ (θ / 100) := Real.one_le_rpow hX1 (by linarith [hθ₀])
                rw [show (50 - 200 * (ε / θ)) = 1 + (49 - 200 * (ε / θ)) by ring]
                rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one hW1), Real.rpow_one]
                have h9 : ε / θ ≤ 1 / 100 := by
                  rw [div_le_div_iff₀ hθ₀ (by norm_num)]
                  linarith
                have h13 : (1:ℝ) ≤ (X ^ (θ / 100)) ^ (49 - 200 * (ε / θ)) :=
                  Real.one_le_rpow hW1 (by linarith [h9])
                exact le_mul_of_one_le_right (le_of_lt (Real.rpow_pos_of_pos hXpos _)) h13
            _ = X ^ (θ / 2 - 2 * ε) := hXexp.symm
        have hfin2 : 6.4 ^ (θ / 2) * (X / (P₁ * P₂)) ^ (θ / 2) ≤ cstar * X ^ (θ - 2 * ε) := by
          have hA : 6.4 ^ (θ / 2) * (X / (P₁ * P₂)) ^ (θ / 2)
              ≤ 6.4 ^ (θ / 2) * X ^ (θ / 2) :=
            mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (by norm_num) _)
          have hB : 6.4 ^ (θ / 2) * X ^ (θ / 2) ≤ cstar * X ^ (θ - 2 * ε) := by
            rw [show 6.4 ^ (θ / 2) = cstar * (6.4 ^ (θ / 2) / cstar) by field_simp]
            calc cstar * (6.4 ^ (θ / 2) / cstar) * X ^ (θ / 2)
                = cstar * ((6.4 ^ (θ / 2) / cstar) * X ^ (θ / 2)) := by ring
              _ ≤ cstar * (X ^ (θ / 2 - 2 * ε) * X ^ (θ / 2)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hXpos.le _)) hcstarpos.le
              _ = cstar * X ^ (θ - 2 * ε) := by rw [h5]
          linarith [hA, hB]
        linarith [hfin2]
      have h4 : cstar * X ^ (θ - 2 * ε) ≤ cstar * (H / (P₁ * P₂)) :=
        mul_le_mul_of_nonneg_left hLge (le_of_lt hcstarpos)
      linarith [h1, h2, h4]
    · -- H' ≤ Y
      have h1 : cstar * (H / (P₁ * P₂)) ≤ H / (P₁ * P₂) :=
        mul_le_of_le_one_left hLpos.le hcstarle1
      have h2 : H / (P₁ * P₂) ≤ X / (P₁ * P₂) / 10 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 10)]
        have h3 : (10:ℝ) ≤ X / H := by linarith [hN13]
        have h4 : (H / (P₁ * P₂)) * 10 ≤ (H / (P₁ * P₂)) * (X / H) :=
          mul_le_mul_of_nonneg_left h3 hLpos.le
        have h5 : (H / (P₁ * P₂)) * (X / H) = X / (P₁ * P₂) := by
          rw [mul_comm, hNL]
        linarith [h4, h5.le, h5.ge]
      linarith [h1, h2, hYN]
    · -- Y/H' ≤ C' X^{k+1}/H^{k+1}
      have hNpow : C' * X ^ (k + 1) / H ^ (k + 1) = C' * (X / H) ^ (k + 1) := by
        rw [div_pow]
        ring
      rw [hNpow]
      have hY64d := hY64
      rw [hNL] at hY64d
      have h1 : Y ≤ 6.4 * ((X / H) * (H / (P₁ * P₂))) := by
        rw [hNL]
        linarith [hY64d]
      have h2 : Y / (cstar * (H / (P₁ * P₂))) ≤ 6.4 * (X / H) / cstar := by
        have hHz : (0:ℝ) < cstar * (H / (P₁ * P₂)) := mul_pos hcstarpos hLpos
        have h2a : Y / (cstar * (H / (P₁ * P₂)))
            ≤ (6.4 * ((X / H) * (H / (P₁ * P₂)))) / (cstar * (H / (P₁ * P₂))) :=
          div_le_div_of_nonneg_right h1 hHz.le
        have h2b : (6.4 * ((X / H) * (H / (P₁ * P₂)))) / (cstar * (H / (P₁ * P₂)))
            = 6.4 * (X / H) / cstar := by
          field_simp
        linarith [h2a, h2b.le, h2b.ge]
      have h3 : 6.4 * (X / H) / cstar ≤ C' * (X / H) ^ (k + 1) := by
        have h4 : 6.4 / cstar ≤ C' := by
          have h5 : (6.4:ℝ) ≤ 40 := by norm_num
          calc 6.4 / cstar ≤ 40 / cstar :=
                div_le_div_of_nonneg_right h5 (le_of_lt hcstarpos)
            _ ≤ C' := hC'_geC
        have h6 : (1:ℝ) ≤ X / H := by linarith [hN3]
        have h5 : X / H ≤ (X / H) ^ (k + 1) := by
          calc X / H = (X / H) ^ 1 := (pow_one _).symm
            _ ≤ (X / H) ^ (k + 1) := pow_le_pow_right₀ h6 (by omega)
        have h7 : 6.4 * (X / H) / cstar = (6.4 / cstar) * (X / H) := by ring
        rw [h7]
        calc (6.4 / cstar) * (X / H) ≤ C' * (X / H) :=
              mul_le_mul_of_nonneg_right h4 (by linarith [hN3])
          _ ≤ C' * (X / H) ^ (k + 1) := mul_le_mul_of_nonneg_left h5 hC'pos.le
      linarith [h2, h3]


end Work.BMF
