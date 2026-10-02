/-
# The naive colouring procedure: the probabilistic core via pairs and triples

This module proves the probabilistic core `Work.Deep.Sparse.NCPCore`
(`Submission/Work/Deep/Sparse/Assembly.lean`) by the route of
Bonamy--Perrett--Postle (`Papers/bpp/ColouringSparseGraphsRevision-clean.tex`, Section 3) and
Molloy--Reed (Chapter 10): draw a uniformly random colouring `f : V → Fin k`, uncolour both
ends of every monochromatic edge, and let `A_v` be the event that the resulting partial
colouring has fewer than `d(v) + 1 - k` *repeated* colours at `v` (i.e.
`Col(v) - Dist(v) < d(v) + 1 - k`).

* `bad_event_bound` (proved in the sibling module of the same name, from the concentration of
  `pairTerm - tripleTerm` over the Bruhn--Joos/BPP analysis) bounds `Pr[A_v] ≤ 1/(4 D^6)`;
* `A_v` only sees the colours of `ball G v`, the set of vertices at distance at most two from
  `v` (`PTAgree`), and at most `(D+1)^4 + 1` balls meet `ball G v` (`ball_dep_card`);
* the Lovász Local Lemma in the form `lll_apply` therefore produces a colouring avoiding all
  the events `A_v`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.Basic
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.FiringDefs
import Submission.Work.Deep.Sparse.nonadj_card
import Submission.Work.Deep.Sparse.ball_dep_card
import Submission.Work.Deep.Sparse.lll_apply
import Submission.Work.Deep.Sparse.bad_event_bound
import Submission.Work.Deep.Sparse.PTAgree
import Submission.Work.Deep.Sparse.pt_hbig
import Submission.Work.Deep.Sparse.pt_key_arith
import Submission.Work.Deep.Sparse.pt_hsp_arith
import Submission.Work.Deep.Sparse.pt_nonadj_ge
import Submission.Work.Deep.Sparse.Assembly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The expectation lower bound `μ = (|nonAdjPairs G v|/2)·(1/k)·((k-1)/k)^(2D)·(1 - D/(3k))`
of the statistic `pairTerm v - tripleTerm v` of the naive colouring procedure. -/
noncomputable def ncpMean (G : SimpleGraph V) [DecidableRel G.Adj] (k D : ℕ) (v : V) : ℝ :=
  ((nonAdjPairs G v).card : ℝ) / 2
    * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
    * (1 - (D : ℝ) / (3 * (k : ℝ)))

theorem ncpMean_def (G : SimpleGraph V) [DecidableRel G.Adj] (k D : ℕ) (v : V) :
    ncpMean G k D v
      = ((nonAdjPairs G v).card : ℝ) / 2
        * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
        * (1 - (D : ℝ) / (3 * (k : ℝ))) := rfl

/-- The local sparsity hypothesis of the concentration input at a vertex. -/
def ncpSparse (G : SimpleGraph V) [DecidableRel G.Adj] (δ : ℝ) (D : ℕ) (v : V) : Prop :=
  (δ / 2) * (D : ℝ) ^ 2 / 2 ≤ ((nonAdjPairs G v).card : ℝ) / 2

/-- The requirement of the extension step at a vertex, in the form needed by the concentration
input: `d(v) + 1 - k ≤ μ/2`. -/
def ncpReq (G : SimpleGraph V) [DecidableRel G.Adj] (k D : ℕ) (v : V) : Prop :=
  (G.degree v : ℝ) + 1 - k ≤ (1 / 2) * ncpMean G k D v

/-- The two hypotheses of the concentration input hold at `v`. -/
def ncpCond (G : SimpleGraph V) [DecidableRel G.Adj] (δ : ℝ) (k D : ℕ) (v : V) : Prop :=
  ncpSparse G δ D v ∧ ncpReq G k D v

/-- The bad event at `v`: the partial colouring has fewer than `d(v) + 1 - k` repeated colours
at `v`. -/
def ncpBad (G : SimpleGraph V) [DecidableRel G.Adj] (k D : ℕ) (v : V) : Set (V → Fin k) :=
  {f : V → Fin k | ((ofColoring G f).numColored v : ℝ)
    - ((ofColoring G f).numDistinct v : ℝ) < (G.degree v : ℝ) + 1 - k}

/-- **The dichotomy at a vertex.**  Either the requirement `d(v) + 1 - k` of the extension step
is already non-positive (so nothing has to be proved at `v`), or the two hypotheses of the
concentration input hold at `v`. -/
theorem ncp_good_or_trivial (G : SimpleGraph V) [DecidableRel G.Adj]
    {δ Δ : ℝ} {k D : ℕ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : (10 : ℝ) ^ 24 / δ ^ 8 ≤ Δ)
    (hDle : Δ ≤ (D : ℝ)) (hDlt : (D : ℝ) < Δ + 1) (hDk : D ≤ 2 * k) (hk2 : 2 ≤ k)
    (hdeg : (G.maxDegree : ℝ) ≤ Δ)
    (hsp : ∀ w : V, (ErdosFaberLovaszConjecture.nbrEdges G w : ℝ) ≤ (1 - δ) * Δ ^ 2 / 2)
    (hk : (1 - δ / 100) * (Δ + 1) - 1 ≤ (k : ℝ)) (hk' : (k : ℝ) ≤ (1 - δ / 100) * (Δ + 1))
    (v : V) :
    (G.degree v : ℝ) + 1 - k ≤ 0 ∨ ncpCond G δ k D v := by
  by_cases hcase : (G.degree v : ℝ) + 1 - k ≤ 0
  · exact Or.inl hcase
  · right
    have hpos : 0 < (G.degree v : ℝ) + 1 - (k : ℝ) := lt_of_not_ge hcase
    have hdΔ : (G.degree v : ℝ) ≤ Δ :=
      le_trans (by exact_mod_cast SimpleGraph.degree_le_maxDegree (G := G) v) hdeg
    have hd0 : (0 : ℝ) ≤ (G.degree v : ℝ) := by positivity
    have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    -- the arithmetic inputs
    have hkey := pt_key_arith hδ0 hδ1 hΔ hDle hDlt hk hk' (G.degree v : ℝ) hd0 hdΔ hpos
    have hna := pt_nonadj_ge G hsp v
    have hhsp := pt_hsp_arith hδ0 hδ1 hΔ hDlt hk
    -- elementary consequences of `hpos`
    have hdle : (k : ℝ) - 1 ≤ (G.degree v : ℝ) := by linarith
    have hdle2 : (k : ℝ) - 2 ≤ (G.degree v : ℝ) - 1 := by linarith
    have hnn1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    have hnn2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by linarith
    have hmono : ((k : ℝ) - 1) * ((k : ℝ) - 2)
        ≤ (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) :=
      mul_le_mul hdle hdle2 hnn2 hd0
    -- sign facts for the composite factor
    have hq0 : (0 : ℝ) ≤ (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D) := by positivity
    have hDkR : (D : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hDk
    have hfac : (0 : ℝ) ≤ (1 - (D : ℝ) / (3 * (k : ℝ))) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      linarith
    have hQ0 : (0 : ℝ) ≤ (1 / 4) * ((1 : ℝ) / (k : ℝ)
        * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D)) * (1 - (D : ℝ) / (3 * (k : ℝ))) := by
      have h1 : (0 : ℝ) ≤ (1 : ℝ) / (k : ℝ) := by positivity
      have h2 := mul_nonneg h1 hq0
      have h3 := mul_nonneg h2 hfac
      linarith
    constructor
    · -- the sparsity lower bound
      rw [ncpSparse]
      have h1 : (δ / 2) * (D : ℝ) ^ 2
          ≤ ((k : ℝ) - 1) * ((k : ℝ) - 2) - (1 - δ) * Δ ^ 2 := hhsp
      have h2 : ((k : ℝ) - 1) * ((k : ℝ) - 2) - (1 - δ) * Δ ^ 2
          ≤ (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) - (1 - δ) * Δ ^ 2 := by linarith
      linarith
    · -- the requirement
      rw [ncpReq, ncpMean_def]
      have h4 : (G.degree v : ℝ) + 1 - (k : ℝ)
          ≤ (1 / 4) * ((G.degree v : ℝ) * ((G.degree v : ℝ) - 1) - (1 - δ) * Δ ^ 2)
              * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
              * (1 - (D : ℝ) / (3 * (k : ℝ))) := by
        have := hkey
        nlinarith [this]
      have h5 : (1 / 4) * ((G.degree v : ℝ) * ((G.degree v : ℝ) - 1) - (1 - δ) * Δ ^ 2)
              * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
              * (1 - (D : ℝ) / (3 * (k : ℝ)))
          ≤ (1 / 4) * ((nonAdjPairs G v).card : ℝ)
              * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
              * (1 - (D : ℝ) / (3 * (k : ℝ))) := by
        nlinarith [hna, hQ0]
      have h6 : (1 / 4) * ((nonAdjPairs G v).card : ℝ)
              * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
              * (1 - (D : ℝ) / (3 * (k : ℝ)))
          = (1 / 2) * (((nonAdjPairs G v).card : ℝ) / 2
              * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
              * (1 - (D : ℝ) / (3 * (k : ℝ)))) := by ring
      linarith

/-- **The probabilistic core of the naive colouring procedure** (Molloy--Reed, Chapter 10;
Bonamy--Perrett--Postle, Section 3), proved by the Lovász Local Lemma.

For a graph of maximum degree at most `Δ` in which every neighbourhood spans at most
`(1-δ)Δ²/2` edges and with `Δ ≥ 10²⁴/δ⁸`, every colour count `k` in the window
`(1-δ/100)(Δ+1) - 1 ≤ k ≤ (1-δ/100)(Δ+1)` admits a *partial* proper `k`-colouring with
`Col(v) - Dist(v) ≥ d(v) + 1 - k` at every vertex. -/
theorem ncp_core_pt (G : SimpleGraph V) [DecidableRel G.Adj]
    {δ Δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : (10 : ℝ) ^ 24 / δ ^ 8 ≤ Δ)
    (hdeg : (G.maxDegree : ℝ) ≤ Δ)
    (hsp : ∀ v : V, (ErdosFaberLovaszConjecture.nbrEdges G v : ℝ) ≤ (1 - δ) * Δ ^ 2 / 2)
    {k : ℕ} (hk : (1 - δ / 100) * (Δ + 1) - 1 ≤ (k : ℝ))
    (hk' : (k : ℝ) ≤ (1 - δ / 100) * (Δ + 1)) :
    ∃ φ : PartialColoring G k,
      ∀ v : V, (G.degree v : ℝ) + 1 - k ≤ (φ.numColored v : ℝ) - (φ.numDistinct v : ℝ) := by
  classical
  -- ## the parameters
  have hδ8pos : (0 : ℝ) < δ ^ 8 := by positivity
  have hδ8le1 : δ ^ 8 ≤ 1 := by
    calc δ ^ 8 ≤ 1 ^ 8 := pow_le_pow_left₀ (le_of_lt hδ0) hδ1 8
      _ = 1 := one_pow 8
  have hΔ24 : (10 : ℝ) ^ 24 ≤ Δ := by
    have h1 : (10 : ℝ) ^ 24 ≤ (10 : ℝ) ^ 24 / δ ^ 8 := by
      rw [le_div_iff₀ hδ8pos]; nlinarith
    linarith
  have hΔpos : (0 : ℝ) < Δ := by linarith
  set D : ℕ := Nat.ceil Δ with hDdef
  have hDle : Δ ≤ (D : ℝ) := Nat.le_ceil Δ
  have hDlt : (D : ℝ) < Δ + 1 := Nat.ceil_lt_add_one (le_of_lt hΔpos)
  have hD1 : 1 ≤ D := by
    have : (1 : ℝ) ≤ (D : ℝ) := by linarith
    exact_mod_cast this
  have hD0 : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD1
  have hD5 : 5 ≤ D := by
    have : (5 : ℝ) ≤ (D : ℝ) := by linarith
    exact_mod_cast this
  -- ## the colour count is huge
  have hkge : (0.99 : ℝ) * (Δ + 1) - 1 ≤ (k : ℝ) := by
    have hc : (0.99 : ℝ) ≤ 1 - δ / 100 := by nlinarith [hδ1]
    have h2 : (0.99 : ℝ) * (Δ + 1) ≤ (1 - δ / 100) * (Δ + 1) :=
      mul_le_mul_of_nonneg_right hc (by linarith)
    linarith
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ (k : ℝ) := by nlinarith [hkge, hΔ24]
    exact_mod_cast this
  have hk0 : 0 < k := by omega
  have hkD : (k : ℝ) ≤ 2 * (D : ℝ) := by
    have h1 : (1 - δ / 100 : ℝ) ≤ 1 := by linarith
    have h3 : (k : ℝ) ≤ Δ + 1 := by
      have h2 : (1 - δ / 100 : ℝ) * (Δ + 1) ≤ Δ + 1 := by
        nlinarith [h1, hΔpos]
      linarith
    have h4 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    linarith
  have hDk : D ≤ 2 * k := by
    have h2 : (D : ℝ) < ((2 * k : ℕ) : ℝ) := by
      push_cast
      nlinarith [hDlt, hkge, hΔ24]
    exact le_of_lt (by exact_mod_cast h2)
  have hdegD : ∀ x : V, G.degree x ≤ D := by
    intro x
    have h1 : (G.degree x : ℝ) ≤ (G.maxDegree : ℝ) := by
      exact_mod_cast SimpleGraph.degree_le_maxDegree (G := G) x
    have : (G.degree x : ℝ) ≤ (D : ℝ) := by linarith [h1, hdeg, hDle]
    exact_mod_cast this
  have hbig : (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ δ ^ 2 * (D : ℝ) :=
    pt_hbig hδ0 hδ1 (le_trans hΔ hDle)
  haveI : Nonempty (V → Fin k) := ⟨fun _ => ⟨0, hk0⟩⟩
  -- ## the bad events
  set X : ℕ := (D + 1) ^ 4 + 1 with hXdef
  set A : V → Set (V → Fin k) :=
    fun v => if ncpCond G δ k D v then ncpBad G k D v else ∅ with hA
  have hAeq : ∀ v : V, A v = if ncpCond G δ k D v then ncpBad G k D v else ∅ := by
    intro v; simp only [hA]
  have hdet : ∀ i (f g : V → Fin k), (∀ u ∈ ball G i, f u = g u) → (f ∈ A i ↔ g ∈ A i) := by
    intro i f g hag
    by_cases hc : ncpCond G δ k D i
    · have h1 : A i = ncpBad G k D i := by rw [hAeq, if_pos hc]
      rw [h1, ncpBad]
      simp only [Set.mem_ofPred_eq]
      rw [numColored_sub_numDistinct_agree G hag]
    · have h1 : A i = ∅ := by rw [hAeq, if_neg hc]
      rw [h1]; simp
  have hcard : ∀ i, (Finset.univ.filter (fun j : V => (ball G i ∩ ball G j).Nonempty)).card ≤ X := by
    intro i
    rw [hXdef]
    exact ball_dep_card G D hdegD i
  have hprob : ∀ i, (colSpace (V := V) k).prob (A i) ≤ 1 / (4 * (D : ℝ) ^ 6) := by
    intro i
    by_cases hc : ncpCond G δ k D i
    · have h1 : A i = ncpBad G k D i := by rw [hAeq, if_pos hc]
      rw [h1, ncpBad]
      exact bad_event_bound G hk0 hD0 hDk hkD hdegD i hδ0 hδ1 hc.1 hbig hc.2
    · have h1 : A i = ∅ := by rw [hAeq, if_neg hc]
      rw [h1]
      simp [FinSpace.prob]
  have hsmall : 4 * (1 / (4 * (D : ℝ) ^ 6)) * ((X : ℝ) + 1) ≤ 1 := by
    have hXval : (X : ℝ) = ((D : ℝ) + 1) ^ 4 + 1 := by rw [hXdef]; push_cast; ring
    have h5 : 4 * (1 / (4 * (D : ℝ) ^ 6)) = 1 / (D : ℝ) ^ 6 := by field_simp
    rw [hXval, h5]
    have hDpos : (0 : ℝ) < (D : ℝ) := by positivity
    have hD5R : (5 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD5
    have h17 : (17 : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
    have h1 : ((D : ℝ) + 1) ^ 4 ≤ (2 * (D : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    have h2 : (2 * (D : ℝ)) ^ 4 = 16 * (D : ℝ) ^ 4 := by ring
    have h3 : 16 * (D : ℝ) ^ 4 ≤ (D : ℝ) ^ 6 := by
      calc 16 * (D : ℝ) ^ 4 ≤ (D : ℝ) ^ 2 * (D : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (D : ℝ) ^ 6 := by ring
    have h4 : ((D : ℝ) + 1) ^ 4 + 1 + 1 ≤ (D : ℝ) ^ 6 := by
      have h2' : (2 : ℝ) ≤ (D : ℝ) ^ 4 := by
        have : (2 : ℝ) ≤ (D : ℝ) := by linarith
        nlinarith [this, hDpos]
      nlinarith [h1, h2, h3, h2']
    calc (1 / (D : ℝ) ^ 6) * (((D : ℝ) + 1) ^ 4 + 1 + 1)
        ≤ (1 / (D : ℝ) ^ 6) * (D : ℝ) ^ 6 :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 1 := by field_simp
  obtain ⟨f, hf⟩ := lll_apply (V := V) (k := k) A (fun i => ball G i) X (1 / (4 * (D : ℝ) ^ 6))
    hdet hcard hprob hsmall
  -- ## conclusion
  refine ⟨ofColoring G f, fun v => ?_⟩
  by_cases hc : ncpCond G δ k D v
  · have hmem : f ∉ A v := hf v
    have h1 : A v = ncpBad G k D v := by rw [hAeq, if_pos hc]
    rw [h1, ncpBad] at hmem
    simp only [Set.mem_ofPred_eq, not_lt] at hmem
    exact hmem
  · rcases ncp_good_or_trivial G hδ0 hδ1 hΔ hDle hDlt hDk hk2 hdeg hsp hk hk' v with h | h
    · have h0 : (0 : ℝ) ≤ ((ofColoring G f).numColored v : ℝ)
          - ((ofColoring G f).numDistinct v : ℝ) := by
        have h1 := (ofColoring G f).numDistinct_le_numColored v
        have h2 : (((ofColoring G f).numDistinct v : ℕ) : ℝ)
            ≤ ((ofColoring G f).numColored v : ℝ) := by exact_mod_cast h1
        linarith
      linarith
    · exact absurd h hc

/-- The probabilistic core of the naive colouring procedure, in the packaging `NCPCore`. -/
theorem ncpCore_of_pt : NCPCore := fun V _ _ G _ => ncp_core_pt (V := V) (G := G)

end Work.Deep.Sparse
