import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.solve_adi
import Submission.Work.BMF.adi_edge_dec
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.adi_graph_defs
import Submission.Work.BMF.adi_num_setup
import Submission.Work.BMF.good_bike_exists
import Submission.Work.BMF.good_edges
import Submission.Work.BMF.good_bike_adi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/BMF/DESIGN.md (your node's section has exact formulas; N5/N8 were held until solve_adi (N6) was proved: it IS now, Work.BMF.solve_adi, axiom-clean). The statement imports only Defs + solve_adi, because some siblings are still in progress; for the proof add these imports once they build: Submission.Work.BMF.Defs,Submission.Work.BMF.prime_tuple_count. Shared definitions: Submission/Work/BMF/Defs.lean (do NOT edit). Owned assets: ASSETS.md.

# N5 `adi_cycles`: cycles in the quadruple graph give approximate dilation invariance

**Sources.**
- MRT Invent. 2020 (arXiv 1812.01224) §4, Prop. 4.1, down to (53).
- MRTTZ Prop. 3.7 and its proof, including the two extra non-degeneracy reductions.

**Imports.** `Submission.Work.BMF.Defs`, `Submission.Work.BMF.prime_tuple_count` (N4, with `q = 1`
and `m = 1`).

## Parameters

Scale and graph quantities:
- `X'' = X/(P₁P₂)`, `L = H/(P₁P₂)`, `N := X/H`, so `X'' = N L`.
- `V := D.fam`, with `cN ≤ #V ≤ N/50`.
- `d := π₀(P₁)²`, with `X^{ε²/2}/(log X)² ≤ d ≤ X^{2ε}`.

Cycle length:
- `ℓ` is the least even integer with `d^ℓ ≥ N² d^{10}`.
- It depends only on `ε`: `ℓ := 2⌈(11 + 4/ε²)/2⌉` works for large `X`, because
  `log N ≤ log X` and `log d ≥ (ε²/2 − o(1)) log X`.
- This value of `ℓ` is the one returned by the statement.

## Basic `PolyRel` algebra (put in a helper file `PolyRelBasic.lean`; N3 also needs it)

- (R1) Symmetry.
- (R2) Transitivity, with `C ↦ C'(k, C)`. Moving a degree-`≤ k` bound from `I₂` to a comparable
  `I₁` costs `(1 + 2·dist/|I₂|)^k · 2^{O(k)}` (Chebyshev growth).
- (R3) Dilation. `PolyRel k C δ (x₁,L₁,P₁) (x₂,L₂,P₂)` gives
  `PolyRel k C (δ/a) (x₁/a, L₁/a, dil a P₁) (x₂/a, L₂/a, dil a P₂)` for `a > 0`. Use
  `dil a ε`, `dil a γ`, and `(dil a γ)((δ/a) n) = γ(δ n)`.
- (R4) Sparsification. `IntegralOn δ γ` gives `IntegralOn (m δ) γ` for `m ∈ ℕ`.
- (R5) `dil a (dil b P) = dil (ab) P`.

## Route (MRT §4 with MRTTZ's changes)

**1. The graph `𝒢` on `V`.** Put an edge `{x₁, x₂}` for each `e ∈ D.edges`.
- The pair `(p₁, p₂)` is unique given `(x₁, x₂)`. If `(p₃, p₄)` also works, then
  `|p₂/p₁ − p₄/p₃| ≤ 2000 L/X'' = 2000/N ≤ 2000 X^{−θ}`. But a nonzero difference is
  `≥ 1/(4P₁²) ≥ X^{−2ε}/4`, and `2ε ≤ θ/50`.
- `x₁` is unique given `(x₂, p₁, p₂)`, by the `500L` separation.
- Hence the maximum degree is `≤ 4d`: use Chebyshev for the number of primes in `[P₁, 2P₁]`.

**2. Random refinement (Gowers).** For a prime `p ∈ [P₂/2, P₂]`, let `𝒢_p` be the edges `e` with
`p ∈ S_e`. Double counting gives `Σ_p #E(𝒢_p) ≥ c π₀(P₂) #E ≥ c² π₀(P₂) d N`.

Do not choose `p` yet. Everything below is an expectation over uniform `p`, and at the end one `p`
is chosen deterministically, as in MRT.

**3. Blakley–Roy for even length.** Let `A` be symmetric with nonnegative entries and `m` even.
Then `1ᵀA^m 1 ≥ (1ᵀA1)^m / n^{m−1}`, where `n` is the size of `A`.

Proof: spectral theorem (`Matrix.IsHermitian.spectral_theorem`). With `w_i = (1·v_i)²/n`,
`Σ w_i = 1` and Jensen for `x ↦ x^m` gives `Σ λ_i^m w_i ≥ (Σ λ_i w_i)^m`.

**4. Two cycles joined by an edge.**
- Walks of length `ℓ + 1` in `𝒢_p` number `≥ c d^{ℓ+1} N`, whenever `#E(𝒢_p) ≥ c' d N`.
- The number of endpoint quadruples `(x_{ℓ/2,1}, x_{0,1}, x_{0,2}, x_{ℓ/2,2})` joined by the middle
  edge is `≤ 4dN³`.
- Cauchy–Schwarz then gives `≥ c d^{2ℓ+1}/N` good tuples `(x_{j,i})_{i=1,2; 0≤j<ℓ}`. Each is two
  closed `ℓ`-walks through `x_{0,1}` and `x_{0,2}`, plus the edge `{x_{0,1}, x_{0,2}}`, all in
  `𝒢_p`.

Each cycle edge carries its primes `(p'_{1,j,i}, p'_{2,j,i})`. Iterating the geometry gives
`|∏_j p'_{2,j,i} − ∏_j p'_{1,j,i}| ≤ C (P₁)^ℓ/N`.

**5. Removing degenerate tuples** (MRTTZ, text after (3.18)).

(a) A collision `p'_{1,j,i} = p'_{2,j',i}`. Cancelling a factor gives a shorter congruence-free
count. By N4 (`q = 1`), there are `O(d^{2ℓ+1/2}/N)` such tuples. This is negligible.

(b) `|∏p'_2 − ∏p'_1| ≤ c₅ P₁^ℓ/N` for some `i`. By N4 with `C₀ = c₅`, there are
`O(c₅ d^{2ℓ+1}/N)` such tuples. Choose `c₅` small; this is where the linear dependence on `C₀`
in N4 is used.

What remains satisfies `c₅ P₁^ℓ/N ≤ |∏p'_2 − ∏p'_1| ≤ C P₁^ℓ/N` and has all primes distinct. The
count of a tuple is determined by `(x_{0,1}, x_{0,2}, p₁, p₂)` together with its primes.

**6. Very good tuples.** Let `𝒫(x⃗) := ∩ S_e` over the `2ℓ + 1` edges. A candidate tuple (edges
in `𝒢`, non-degenerate) with `#𝒫(x⃗) ≤ δ π₀(P₂)` lies in `𝒢_p` with probability `≤ δ`.

By N4, the number of candidates is `≤ C d^{2ℓ+1}/N`. So the expected number of good-but-not-very-good
tuples is `≤ C δ d^{2ℓ+1}/N`. Fix a deterministic `p` with at least `c d^{2ℓ+1}/N` very good
tuples.

**7. Telescoping around each cycle.** For a very good tuple put `Q = ∏ 𝒫(x⃗)`. Each edge relation
holds modulo `1/p''` for every `p'' ∈ 𝒫(x⃗)`.

- CRT (MRTTZ Prop. 3.5 (ii), Appendix B, `papers/mrttz/AppendixB4.tex`): for `|I|` large, the edge relation holds modulo
  `1/∏𝒫(x⃗)`. This is a separate helper. It is the "if a polynomial is `1/p`-integral up to smooth
  for all `p ∈ 𝒫` then it is `1/∏𝒫`-integral up to smooth" statement. Prove it by comparing the
  `γ_p`'s pairwise: `γ_p − γ_{p'}` is smooth plus integral on `ℤ`, so by (T2) of N6 their top
  coefficients agree modulo a lattice. The paper's proof is in Appendix B; follow it.
- Set `a_{j,i} := ∏_{j'<j} p'_{1,j',i} · ∏_{j'≥j} p'_{2,j',i}`.
- Apply (R3) with `a = ∏_{j'<j} p'_{1,j',i} ∏_{j'>j} p'_{2,j',i}`, then (R4) with the same
  number. The `j`-th edge relation becomes
  `(1/a_{j,i})_* φ_{I_{j,i}} ~_{1/Q} (1/a_{j+1,i})_* φ_{I_{j+1,i}}`.
- Chain `ℓ` times with (R2) to get `(1/a_{0,i})_* φ_{I_{0,i}} ~_{1/Q} (1/a_{ℓ,i})_* φ_{I_{0,i}}`.
- Take `a_i := max`, `b_i := min`. Then `P₁^ℓ ≤ b_i < a_i ≤ (2P₁)^ℓ` and, from step 5,
  `c₅ a_i/(4^ℓ N) ≤ a_i − b_i ≤ C a_i / N`.
- The middle edge gives the `EdgeRel` with modulus `1/Q`.

**8. Counting edges.** By N4 twice, each `e = (x_{0,1}, x_{0,2}, p₁, p₂)` is completed by
`≤ C (d^ℓ/N)²` very good tuples. With `≥ c d^{2ℓ+1}/N` tuples, at least `c' d N` edges are hit.
Take `ADIData.edges` to be these edges. The family fields are copied from `D`, with
`c' := min(c, …)`.

## Size and risk

Size 5–10k. Risk medium-high: steps 2 and 6 (probabilistic selection) and step 7's CRT helper.

The expectation argument can be replaced by an averaging (pigeonhole) over the finite set of
primes. State it as `Finset.exists_le_card_fiber`-style averaging to avoid probability theory.
-/

namespace Work.BMF

open Polynomial BoundedMultiplicativeFunctions

/-! ## Assembly of `adi_cycles`

The four ingredients established elsewhere in `Submission/Work/BMF/` are

* `Work.BMF.adi_num_setup` — the cycle length `ℓ`, the threshold `X₀`, and all the numerical
  constraints (`3 ≤ X/H`, `X/H ≤ P₁^{ℓ-1}`, `8000 P₁² < X/H`, `1 ≤ L/(2P₁)`, the dominance of
  the iterated transitivity constant by `L/(2P₁)`);
* `Work.BMF.good_bike_exists` — averaging over the primes `q ∈ [P₂/2, P₂]` produces a `q` whose
  `q`-subgraph carries `≫ c^{4ℓ+2} (π₀(P₁)²)^{2ℓ+1}/(X/L)` good bicycles;
* `Work.BMF.good_edges` — each arc is hit by at most `≪ π₀(P₁)^{4ℓ}/(X/L)²` good bicycles, so
  the arcs hit are `≫ π₀(P₁)² (X/L)` in number;
* `Work.BMF.good_bike_adi` — a good bicycle over an arc yields `ADIEdge` for that arc.

This file glues them together, with the elementary arithmetic (`edge_count_arith`) turning the
two counting estimates into the edge lower bound required by `ADIData.edges_card`.
-/

/-- **Arithmetic core of the edge count.**  If a set of bicycles `S` satisfies
`K P Q²/N ≤ #S` and `#S ≤ C·M·Q²/N²`, then the number `M` of arcs is at least `c' P N`
whenever `c' ≤ K/C`.  (`P = π₀(P₁)²`, `Q = π₀(P₁)^{2ℓ}`, `N = X/L`.) -/
private lemma edge_count_arith {P Q N S M Cg c' K : ℝ} (hQ : 0 < Q) (hP : 0 < P) (hN : 0 < N)
    (hCg : 0 < Cg) (hc' : c' ≤ K / Cg)
    (hlow : K * P * Q ^ 2 / N ≤ S) (hhigh : S ≤ Cg * M * Q ^ 2 / N ^ 2) :
    c' * P * N ≤ M := by
  have hQ2 : 0 < Q ^ 2 := pow_pos hQ 2
  have h1 : K * P * Q ^ 2 / N ≤ Cg * M * Q ^ 2 / N ^ 2 := le_trans hlow hhigh
  have h2 : K * P * Q ^ 2 * N ≤ Cg * M * Q ^ 2 := by
    have h1' : K * P * Q ^ 2 * N ^ 2 ≤ Cg * M * Q ^ 2 * N :=
      (div_le_div_iff₀ hN (pow_pos hN 2)).mp h1
    have h2'' : K * P * Q ^ 2 * N * N ≤ Cg * M * Q ^ 2 * N := by nlinarith [h1']
    exact le_of_mul_le_mul_right h2'' hN
  have h3 : K * P * N ≤ Cg * M := by
    have h2' : K * P * N * Q ^ 2 ≤ Cg * M * Q ^ 2 := by nlinarith [h2]
    exact le_of_mul_le_mul_right h2' hQ2
  have h4 : K / Cg * (P * N) ≤ M := by
    have h5 : K * P * N / Cg ≤ M := (div_le_iff₀ hCg).mpr (by linarith [h3])
    have he : K / Cg * (P * N) = K * P * N / Cg := by rw [div_mul_eq_mul_div, ← mul_assoc]
    rw [he]; exact h5
  calc c' * P * N = c' * (P * N) := by ring
    _ ≤ K / Cg * (P * N) := mul_le_mul_of_nonneg_right hc' (mul_nonneg hP.le hN.le)
    _ ≤ M := h4

/-- **A quadruple graph with `C ≤ 0` is impossible** (when the scale is nondegenerate): the edge
relation of any arc forces `L/p₂ ≤ C·(L/p₁)` with a positive left-hand side. -/
private theorem false_of_C_nonpos {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (hc : 0 < c) (hX : 0 < X) (hL : 0 < L) (hpi₁ : 0 < pi0 P₁) (hpi₂ : 0 < pi0 P₂)
    (hC : C ≤ 0) (D : QuadData k f c C X L P₁ P₂) : False := by
  have hNpos : 0 < X / L := div_pos hX hL
  have hpos : 0 < c * pi0 P₁ ^ 2 * (X / L) := by positivity
  have hcard : (0 : ℝ) < (D.edges.card : ℝ) := lt_of_lt_of_le hpos D.edges_card
  have hne : D.edges.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcard)
  obtain ⟨e, he⟩ := hne
  obtain ⟨S, _hSp, hScard, hSrel⟩ := D.rel e he
  have hSpos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le (by positivity : 0 < c * pi0 P₂) hScard
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by exact_mod_cast hSpos)
  have hge := D.geom e he
  have hp₁pos : (0 : ℝ) < (e.p₁ : ℝ) := by
    have h := (EdgeGeom.prime_p₁ hge).1.pos
    exact_mod_cast h
  have hp₂pos : (0 : ℝ) < (e.p₂ : ℝ) := by
    have h := (EdgeGeom.prime_p₂ hge).1.pos
    exact_mod_cast h
  have h1 : L / (e.p₂ : ℝ) ≤ C * (L / (e.p₁ : ℝ)) := by
    have h : EdgeRel k C (1 / (p : ℝ)) L D.pol e := hSrel p hp
    simp only [EdgeRel, PolyRel] at h
    exact h.1
  have h2 : 0 < L / (e.p₂ : ℝ) := div_pos hL hp₂pos
  have h3 : 0 ≤ L / (e.p₁ : ℝ) := le_of_lt (div_pos hL hp₁pos)
  have h4 : C * (L / (e.p₁ : ℝ)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC h3
  linarith

/-- The underlying arc of a good bicycle is an arc of `D`. -/
private lemma mem_goodBikeSet_fst {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    {D : QuadData k f c C X L P₁ P₂} {q ℓ : ℕ} {N c₅ δ : ℝ}
    {t : Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)}
    (ht : t ∈ goodBikeSet D q ℓ N c₅ δ) : t.1 ∈ D.edges := by
  classical
  have h1 : t ∈ (bikeSet D q ℓ).filter (fun t => goodBikeQ N c₅ δ D ℓ t) := ht
  have h2 : t ∈ bikeSet D q ℓ := (Finset.mem_filter.mp h1).1
  have h3 : t ∈ (D.edges.filter (fun e => q ∈ edgeS D e)).sigma
      (fun e => (closedWalkVal D q ℓ e.x₁).product (closedWalkVal D q ℓ e.x₂)) := h2
  rw [Finset.mem_sigma] at h3
  exact (Finset.mem_filter.mp h3.1).1

/-- **N5. Cycles in the quadruple graph give approximate dilation invariance**
(MRT Prop. 4.1 down to (53); MRTTZ Prop. 3.7). Random choice of one prime `𝐩 ∈ [P₂/2, P₂]`,
Blakley–Roy, Cauchy–Schwarz to two `ℓ`-cycles joined by an edge, removal of degenerate and
nearly-degenerate cycles (N4), and telescoping of the edge relations around each cycle yield,
for `≫ π₀(P₁)² X/H` edges, integers `b_i < a_i` (products of `ℓ` primes of `[P₁, 2P₁]`) with
`a_i - b_i ≍ a_i H/X` and `(1/a_i)_* φ_{I_i} ~_{1/Q} (1/b_i)_* φ_{I_i}`, `Q = ∏ S`. -/
theorem adi_cycles (k : ℕ) (θ ε c C : ℝ) (hθ₀ : 0 < θ) (hε : 0 < ε) (hεθ : ε ≤ θ / 100)
    (hc : 0 < c) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ∃ c' C' X₀ : ℝ, 0 < c' ∧
      ∀ (f : ℕ → ℂ) (X H P₁ P₂ : ℝ), X₀ ≤ X → X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
        X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ → P₂ ≤ X ^ ε →
        QuadData k f c C (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ P₂ →
        Nonempty (ADIData k f c' C' (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ P₂ ℓ) := by
  -- 1. the numerical setup: the cycle length `ℓ`, the threshold, and the admissible scales
  obtain ⟨ℓ, hℓ1, heven, X₀, hX₀pos, hnum⟩ := adi_num_setup k C θ ε hθ₀ hε hεθ
  have hε2pos : 0 < ε ^ 2 / 2 := by positivity
  have hℓ2 : 2 ≤ ℓ := by
    obtain ⟨m, hm⟩ := heven
    omega
  -- 2. the counting of good bicycles and the multiplicity of arcs
  obtain ⟨c₂, hc₂, hgb⟩ := good_bike_exists k ℓ hℓ2 heven
  obtain ⟨c₅, δ, P₀, hc₅, hδ, hP₀, hgb⟩ := hgb c hc
  obtain ⟨Cg, P₀g, hCgpos, hgedges⟩ := good_edges k ℓ hℓ2
  -- 3. the constants `c'` and the threshold
  set K : ℝ := c₂ * c ^ (4 * ℓ + 2) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set c' : ℝ := min (min (K / Cg) (c / 2)) δ with hc'def
  have hc'pos : 0 < c' := by
    rw [hc'def]
    exact lt_min (lt_min (div_pos hKpos hCgpos) (by linarith)) hδ
  have hc'K : c' ≤ K / Cg := le_trans (min_le_left _ _) (min_le_left _ _)
  have hc'δ : c' ≤ δ := min_le_right _ _
  have hc'c : c' ≤ c := by
    rw [hc'def]
    exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  set M₀ : ℝ := max P₀ P₀g with hM₀def
  have hM₀pos : 0 < M₀ := by rw [hM₀def]; exact lt_max_of_lt_left hP₀
  set X₁ : ℝ := max (max X₀ (3 ^ (1 / (ε ^ 2 / 2)))) (M₀ ^ (1 / (ε ^ 2 / 2))) with hX₁def
  have hX₁pos : 0 < X₁ := by
    rw [hX₁def]; exact lt_max_of_lt_left (lt_max_of_lt_left hX₀pos)
  by_cases hCpos : 0 < C
  · -- 4(a). the nondegenerate case `0 < C`: build the `ADIData` from a good bicycle
    obtain ⟨C', hC'pos, hC'⟩ :=
      good_bike_adi k ℓ c C c₅ δ c' hc hCpos hc₅ hδ hc'pos hc'δ
    refine ⟨ℓ, hℓ1, c', C', X₁, hc'pos, ?_⟩
    intro f X H P₁ P₂ hX hHlo hHhi hP1lo hP1hi hP2lo hP2hi D
    -- the threshold hypotheses
    have hX₀le : X₀ ≤ X :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
    have h3thr : (3 : ℝ) ^ (1 / (ε ^ 2 / 2)) ≤ X :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
    have hM₀thr : M₀ ^ (1 / (ε ^ 2 / 2)) ≤ X := le_trans (le_max_right _ _) hX
    have h3ε : (3 : ℝ) ≤ X ^ (ε ^ 2 / 2) :=
      rpow_threshold (by norm_num) hε2pos h3thr
    have hM₀le : M₀ ≤ X ^ (ε ^ 2 / 2) :=
      rpow_threshold hM₀pos hε2pos hM₀thr
    have hM₀leP₁ : M₀ ≤ P₁ := le_trans hM₀le hP1lo
    obtain ⟨hP₀le, hP₀gle⟩ := max_le_iff.mp hM₀leP₁
    have hnum' := hnum X H P₁ P₂ hX₀le hHlo hHhi hP1lo hP1hi hP2lo hP2hi
    obtain ⟨hXpos, hP1pos, hP2pos, hHpos, h3N, hNle, hpi1, hpi2, hfield, hbig, hL1, hLbig⟩ :=
      hnum'
    have hP₂2 : 2 ≤ P₂ := by linarith
    -- the rescaled quantities
    set X'' : ℝ := X / (P₁ * P₂) with hX''def
    set L : ℝ := H / (P₁ * P₂) with hLdef
    have hP1P2pos : 0 < P₁ * P₂ := mul_pos hP1pos hP2pos
    have hX''pos : 0 < X'' := by rw [hX''def]; exact div_pos hXpos hP1P2pos
    have hLpos : 0 < L := by rw [hLdef]; exact div_pos hHpos hP1P2pos
    have hN_eqq : X'' / L = X / H := by rw [hX''def, hLdef]; exact hfield
    have hbig' : 8000 * P₁ ^ 2 < X'' / L := by rw [hN_eqq]; exact hbig
    have h3N' : 3 ≤ X'' / L := by rw [hN_eqq]; exact h3N
    have hNle' : X'' / L ≤ P₁ ^ (ℓ - 1) := by rw [hN_eqq]; exact hNle
    have hL1' : 1 ≤ L / (2 * P₁) := by rw [hLdef]; exact hL1
    have hLbig' : 2 * symmConst k (max C (symmConst k C)) * ((k : ℝ) + 1) *
        (k : ℝ) ^ k * (k.factorial : ℝ) < L / (2 * P₁) := by rw [hLdef]; exact hLbig
    -- 5. the prime `q` and its good bicycles
    obtain ⟨q, hqmem, hqbike⟩ :=
      hgb f C X'' L P₁ P₂ D hP₀le hP1pos hP₂2 hLpos hX''pos hbig' h3N' hNle' D.edges_card
    set S : Finset (Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) :=
      goodBikeSet D q ℓ (X'' / L) c₅ δ with hSdef
    set M : Finset Edge := S.image (fun t => t.1) with hMdef
    -- 6. the multiplicity of good bicycles over a single arc
    have hgedge := hgedges f c C X'' L P₁ P₂ c₅ δ D q hP₀gle hP1pos hLpos hbig' h3N' hNle'
    have hQ2 : pi0 P₁ ^ (4 * ℓ) = (pi0 P₁ ^ (2 * ℓ)) ^ 2 := by
      rw [← pow_mul]
      rw [show 4 * ℓ = (2 * ℓ) * 2 from by ring]
    have hA : (pi0 P₁ ^ 2) ^ (2 * ℓ) = (pi0 P₁ ^ (2 * ℓ)) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      rw [show 2 * (2 * ℓ) = (2 * ℓ) * 2 from by ring]
    have hpow : (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) = pi0 P₁ ^ 2 * (pi0 P₁ ^ (2 * ℓ)) ^ 2 := by
      rw [pow_succ', hA]
    have hlow : K * (pi0 P₁ ^ 2) * (pi0 P₁ ^ (2 * ℓ)) ^ 2 / (X'' / L) ≤ (S.card : ℝ) := by
      have h : K * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X'' / L) ≤
          ((goodBikeSet D q ℓ (X'' / L) c₅ δ).card : ℝ) := hqbike
      rw [hpow, ← mul_assoc] at h
      rwa [hSdef]
    have hhigh : (S.card : ℝ) ≤
        Cg * (M.card : ℝ) * (pi0 P₁ ^ (2 * ℓ)) ^ 2 / (X'' / L) ^ 2 := by
      have h : ((goodBikeSet D q ℓ (X'' / L) c₅ δ).card : ℝ) ≤
          Cg * (((goodBikeSet D q ℓ (X'' / L) c₅ δ).image (fun t => t.1)).card : ℝ) *
            pi0 P₁ ^ (4 * ℓ) / (X'' / L) ^ 2 := hgedge
      rw [hQ2] at h
      rwa [hMdef, hSdef]
    -- 7. the arithmetic
    have hpi1pos : 0 < pi0 P₁ := lt_of_lt_of_le zero_lt_one hpi1
    have harith : c' * pi0 P₁ ^ 2 * (X'' / L) ≤ (M.card : ℝ) :=
      edge_count_arith (P := pi0 P₁ ^ 2) (Q := pi0 P₁ ^ (2 * ℓ)) (N := X'' / L)
        (S := (S.card : ℝ)) (M := (M.card : ℝ)) (Cg := Cg) (c' := c') (K := K)
        (pow_pos hpi1pos _) (pow_pos hpi1pos 2) (div_pos hX''pos hLpos) hCgpos hc'K hlow hhigh
    -- 8. the assembly of the `ADIData`
    refine ⟨{ fam := D.fam
              pol := D.pol
              isFam := D.isFam
              card_ge := ?_
              deg := D.deg
              corr_ge := fun x hx =>
                le_trans (mul_le_mul_of_nonneg_right hc'c hLpos.le) (D.corr_ge x hx)
              edges := M
              edges_card := harith
              geom := ?_
              adi := ?_ }⟩
    · refine le_trans (mul_le_mul_of_nonneg_right hc'c ?_) D.card_ge
      exact le_of_lt (div_pos hX''pos hLpos)
    · intro e he
      obtain ⟨t, htS, hte⟩ := Finset.mem_image.mp he
      have ht1 : t.1 ∈ D.edges := mem_goodBikeSet_fst htS
      rw [← hte]
      exact D.geom t.1 ht1
    · intro e he
      obtain ⟨t, htS, hte⟩ := Finset.mem_image.mp he
      have hthis := hC' f X'' L P₁ P₂ D q t hP1pos hP₂2 hLpos hbig' hL1' hLbig' htS
      rwa [hte] at hthis
  · -- 4(b). the degenerate case `C ≤ 0`: the quadruple data is inconsistent
    refine ⟨ℓ, hℓ1, c', 1, X₁, hc'pos, ?_⟩
    intro f X H P₁ P₂ hX hHlo hHhi hP1lo hP1hi hP2lo hP2hi D
    have hX₀le : X₀ ≤ X :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
    have hnum' := hnum X H P₁ P₂ hX₀le hHlo hHhi hP1lo hP1hi hP2lo hP2hi
    obtain ⟨hXpos, hP1pos, hP2pos, hHpos, -, -, hpi1, hpi2, -, -, -, -⟩ := hnum'
    have hP1P2pos : 0 < P₁ * P₂ := mul_pos hP1pos hP2pos
    exact (false_of_C_nonpos (f := f) hc (div_pos hXpos hP1P2pos) (div_pos hHpos hP1P2pos)
      (lt_of_lt_of_le zero_lt_one hpi1) (lt_of_lt_of_le zero_lt_one hpi2)
      (not_lt.mp hCpos) D).elim

end Work.BMF
