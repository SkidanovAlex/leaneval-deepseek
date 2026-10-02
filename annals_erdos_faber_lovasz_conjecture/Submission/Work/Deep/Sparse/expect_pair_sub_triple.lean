/-
# The expectation of `pairTerm - tripleTerm` in the naive colouring procedure

This module proves `Work.Deep.Sparse.expect_pair_sub_triple`, the triple-corrected
companion of `Work.Deep.Sparse.expect_pair` (`Submission/Work/Deep/Sparse/expect_pair.lean`).

Setting: `G` is a finite simple graph of maximum degree at most `D`, `f : V → Fin k` is the
uniform random colouring of the vertices (the sample space `colSpace k` of
`Submission/Work/Deep/Sparse/ProbBasic.lean`), and `ofColoring G f` is the partial colouring
in which a vertex keeps its colour exactly when no neighbour shares it (the *naive colouring
procedure*, `Submission/Work/Deep/Sparse/ProbModel.lean`).  For a vertex `v` the paper's
quantities are

* `pairTerm v = ∑_c C(Col_c(v), 2)`, the number of unordered pairs of coloured neighbours of
  `v` of equal colour, and
* `tripleTerm v = ∑_c C(Col_c(v), 3)`, the number of unordered triples of coloured neighbours
  of `v` of equal colour.

The main theorem bounds below the *expectation* of the difference `pairTerm v - tripleTerm v`:

`|nonAdjPairs G v| / 2 · (1 - D/(3k)) · (1/k) · ((k-1)/k)^(2D) ≤ E[pairTerm v - tripleTerm v]`.

The proof is the standard one (Molloy–Reed, *Graph Colouring and the Probabilistic Method*,
Chapter 10; Bonamy–Perrett–Postle, arXiv:1810.06704, §3), organised as follows.

* `collisionPairs G f v` (the ordered pairs of distinct retained neighbours of `v` of equal
  colour) is twice `pairTerm`, and likewise `collisionTriples G f v` is six times `tripleTerm`
  (`collision_card`, `collision_triples_card`); hence the expectation of `pairTerm` is half the
  sum, over the ordered pairs of distinct non-adjacent neighbours of `v`, of the probability
  that the pair collides (`two_mul_expect_pairTerm_eq_sum`), and the expectation of
  `tripleTerm` is a sixth of the analogous sum over ordered triples of neighbours of `v`
  (`six_mul_expect_tripleTerm_eq_sum`).

* For every ordered pair `p` of distinct non-adjacent neighbours of `v` the collision
  probability is at least `(1/k)·((k-1)/k)^(2D)` (`prob_collision`/`expect_pair`), while for
  the *triples* the collision probability is at most `1/k` times the collision probability of
  the pair formed by their first two entries (`collision_triples_prob_le`): a third vertex is
  retained with the same colour only `1/k` of the time.

* The sum over the ordered triples of neighbours of `v` of the pair collision probability is
  at most `deg v ≤ D` times the sum over the pairs (`sum_nbrCube`), because for a fixed pair
  there are at most `deg v` choices of the third vertex.  Altogether
  `6·E[tripleTerm] ≤ (D/k)·2·E[pairTerm]`, i.e. `E[tripleTerm] ≤ (D/(3k))·E[pairTerm]`.

* Finally `E[pairTerm] ≥ (|nonAdjPairs G v|/2)·(1/k)·((k-1)/k)^(2D)` is exactly
  `Work.Deep.Sparse.expect_pair`, and `E[pairTerm - tripleTerm] = E[pairTerm] - E[tripleTerm]`,
  which gives the theorem.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.collision_card
import Submission.Work.Deep.Sparse.expect_pair
import Submission.Work.Deep.Sparse.collision_triples_card
import Submission.Work.Deep.Sparse.collision_triples_prob_le

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Expectation of an indicator, and of a cardinality -/

/-- The expectation of the indicator of an event is the probability of the event. -/
theorem FinSpace.expect_indicator {Ω : Type*} [Fintype Ω] (P : FinSpace Ω) (A : Set Ω) :
    P.expect (A.indicator fun _ => (1 : ℝ)) = P.prob A := by
  classical
  rw [FinSpace.expect, FinSpace.prob]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- The cardinality of a sub-`Finset` of `U`, written as a sum of indicators over `U`. -/
theorem card_eq_sum_ite {ι : Type*} [DecidableEq ι] (U S : Finset ι) (h : S ⊆ U) :
    ((S.card : ℝ)) = ∑ p ∈ U, (if p ∈ S then (1 : ℝ) else 0) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, ← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr h]

/-- **The expectation of a cardinality is the sum of the probabilities of the individual
memberships.**  If `S ω ⊆ U` for every sample point `ω`, then
`E[#(S ω)] = ∑_{p ∈ U} P(p ∈ S ω)`. -/
theorem expect_card_eq_sum_prob {Ω ι : Type*} [Fintype Ω] [DecidableEq ι] (P : FinSpace Ω)
    (U : Finset ι) (S : Ω → Finset ι) (hSU : ∀ ω, S ω ⊆ U) :
    P.expect (fun ω => ((S ω).card : ℝ)) = ∑ p ∈ U, P.prob {ω | p ∈ S ω} := by
  classical
  have hpt : ∀ ω, ((S ω).card : ℝ) = ∑ p ∈ U, (if p ∈ S ω then (1 : ℝ) else 0) :=
    fun ω => card_eq_sum_ite U (S ω) (hSU ω)
  rw [FinSpace.expect]
  calc ∑ ω, P.mass ω * ((S ω).card : ℝ)
      = ∑ ω, P.mass ω * ∑ p ∈ U, (if p ∈ S ω then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun ω _ => by rw [hpt ω]
    _ = ∑ ω, ∑ p ∈ U, P.mass ω * (if p ∈ S ω then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun ω _ => Finset.mul_sum U _ (P.mass ω)
    _ = ∑ p ∈ U, ∑ ω, P.mass ω * (if p ∈ S ω then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ p ∈ U, P.prob {ω | p ∈ S ω} := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← FinSpace.expect_indicator P {ω | p ∈ S ω}, FinSpace.expect]
        refine Finset.sum_congr rfl fun ω _ => ?_
        simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-! ## 2. The collision probabilities vanish outside the non-adjacent pairs -/

/-- The collision probability of an ordered pair which is not an ordered pair of distinct
non-adjacent neighbours of `v` is zero: such a pair never collides. -/
theorem prob_collisionPairs_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    [Nonempty (V → Fin k)] {v : V} {p : V × V} (hp : p ∉ nonAdjPairs G v) :
    (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v} = 0 := by
  classical
  have hemp : {f : V → Fin k | p ∈ collisionPairs G f v} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun g hg => hp ?_
    have hg' : p ∈ collisionPairs G g v := hg
    rw [mem_collisionPairs] at hg'
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg'
    rw [mem_nonAdjPairs]
    exact ⟨h1, h2, h3, fun hadj => h4 p.2 hadj h6.symm⟩
  rw [hemp, FinSpace.prob]
  simp

/-! ## 3. A sum over the ordered triples of neighbours of `v` -/

/-- For a fixed ordered pair of neighbours of `v` there are at most `deg v` ordered triples of
neighbours of `v` extending it, so a sum over the ordered triples of neighbours of `v` of a
function of the first two entries is at most `deg v` times the corresponding sum over the
ordered pairs. -/
theorem sum_nbrCube (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (g : V → V → ℝ) :
    ∑ t ∈ (G.neighborFinset v) ×ˢ ((G.neighborFinset v) ×ˢ (G.neighborFinset v)),
        g t.1 t.2.1
      = (G.degree v : ℝ) * ∑ p ∈ (G.neighborFinset v) ×ˢ (G.neighborFinset v), g p.1 p.2 := by
  calc ∑ t ∈ (G.neighborFinset v) ×ˢ ((G.neighborFinset v) ×ˢ (G.neighborFinset v)),
        g t.1 t.2.1
      = ∑ x ∈ G.neighborFinset v, ∑ y ∈ G.neighborFinset v, ∑ z ∈ G.neighborFinset v, g x y := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_product]
    _ = ∑ x ∈ G.neighborFinset v, ∑ y ∈ G.neighborFinset v,
          ((G.neighborFinset v).card : ℝ) * g x y := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ x ∈ G.neighborFinset v, ((G.neighborFinset v).card : ℝ) *
          ∑ y ∈ G.neighborFinset v, g x y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ = ((G.neighborFinset v).card : ℝ) *
          ∑ x ∈ G.neighborFinset v, ∑ y ∈ G.neighborFinset v, g x y := by
        rw [Finset.mul_sum]
    _ = ((G.neighborFinset v).card : ℝ) *
          ∑ p ∈ (G.neighborFinset v) ×ˢ (G.neighborFinset v), g p.1 p.2 := by
        rw [Finset.sum_product]
    _ = (G.degree v : ℝ) *
          ∑ p ∈ (G.neighborFinset v) ×ˢ (G.neighborFinset v), g p.1 p.2 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]

/-! ## 4. The expectations as sums of collision probabilities -/

/-- Twice the expectation of `pairTerm v` is the sum, over the ordered pairs of distinct
non-adjacent neighbours of `v`, of the probability that the pair collides. -/
theorem two_mul_expect_pairTerm_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    [Nonempty (V → Fin k)] (v : V) :
    2 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ))
      = ∑ p ∈ nonAdjPairs G v,
          (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v} := by
  have hcard : ∀ f : V → Fin k,
      ((collisionPairs G f v).card : ℝ) = 2 * ((ofColoring G f).pairTerm v : ℝ) := by
    intro f
    calc ((collisionPairs G f v).card : ℝ) = ((2 * (ofColoring G f).pairTerm v : ℕ) : ℝ) := by
          rw [collision_card G f v]
      _ = 2 * ((ofColoring G f).pairTerm v : ℝ) := by push_cast; ring
  have hmid : ∑ p ∈ (G.neighborFinset v) ×ˢ (G.neighborFinset v),
        (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v}
      = ∑ p ∈ nonAdjPairs G v,
          (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v} :=
    (Finset.sum_subset (Finset.filter_subset _ _)
      (fun p _ hp => prob_collisionPairs_eq_zero G hp)).symm
  calc 2 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ))
      = (colSpace (V := V) k).expect (fun f => ((collisionPairs G f v).card : ℝ)) := by
        rw [FinSpace.expect, FinSpace.expect, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [hcard f]
        ring
    _ = ∑ p ∈ (G.neighborFinset v) ×ˢ (G.neighborFinset v),
          (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v} :=
        expect_card_eq_sum_prob _ _ _ (fun f => Finset.filter_subset _ _)
    _ = ∑ p ∈ nonAdjPairs G v,
          (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v} := hmid

/-- Six times the expectation of `tripleTerm v` is the sum, over the ordered triples of
neighbours of `v`, of the probability that the triple collides. -/
theorem six_mul_expect_tripleTerm_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    [Nonempty (V → Fin k)] (v : V) :
    6 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).tripleTerm v : ℝ))
      = ∑ t ∈ (G.neighborFinset v) ×ˢ ((G.neighborFinset v) ×ˢ (G.neighborFinset v)),
          (colSpace (V := V) k).prob {f : V → Fin k | t ∈ collisionTriples G f v} := by
  have hcard : ∀ f : V → Fin k,
      ((collisionTriples G f v).card : ℝ) = 6 * ((ofColoring G f).tripleTerm v : ℝ) := by
    intro f
    calc ((collisionTriples G f v).card : ℝ) = ((6 * (ofColoring G f).tripleTerm v : ℕ) : ℝ) := by
          rw [collision_triples_card G f v]
      _ = 6 * ((ofColoring G f).tripleTerm v : ℝ) := by push_cast; ring
  calc 6 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).tripleTerm v : ℝ))
      = (colSpace (V := V) k).expect (fun f => ((collisionTriples G f v).card : ℝ)) := by
        rw [FinSpace.expect, FinSpace.expect, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [hcard f]
        ring
    _ = ∑ t ∈ (G.neighborFinset v) ×ˢ ((G.neighborFinset v) ×ˢ (G.neighborFinset v)),
          (colSpace (V := V) k).prob {f : V → Fin k | t ∈ collisionTriples G f v} :=
        expect_card_eq_sum_prob _ _ _ (fun f => Finset.filter_subset _ _)

/-! ## 5. The main theorem -/

theorem expect_pair_sub_triple {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (hDk : D ≤ 2 * k) [Nonempty (V → Fin k)]
    (hdeg : ∀ x : V, G.degree x ≤ D) (v : V) :
    ((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2 * (1 - (D : ℝ) / (3 * (k : ℝ)))
        * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
      ≤ (Work.Deep.Sparse.colSpace (V := V) k).expect
          (fun f => (((Work.Deep.Sparse.ofColoring G f).pairTerm v : ℝ)
            - ((Work.Deep.Sparse.ofColoring G f).tripleTerm v : ℝ))) := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  -- the pair expectation bound of `expect_pair`
  have hEP : ((nonAdjPairs G v).card : ℝ) / 2
        * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
      ≤ (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)) :=
    expect_pair G hk hD hdeg v
  -- the two collision sums
  have hpair := two_mul_expect_pairTerm_eq_sum (V := V) (k := k) G v
  have htriple := six_mul_expect_tripleTerm_eq_sum (V := V) (k := k) G v
  -- the pointwise comparison of the triple and pair collision probabilities
  have hpt : ∀ t ∈ (G.neighborFinset v) ×ˢ ((G.neighborFinset v) ×ˢ (G.neighborFinset v)),
      (colSpace (V := V) k).prob {f : V → Fin k | t ∈ collisionTriples G f v}
        ≤ (1 / (k : ℝ)) * (colSpace (V := V) k).prob
            {f : V → Fin k | (t.1, t.2.1) ∈ collisionPairs G f v} := by
    intro t ht
    exact collision_triples_prob_le G hk v t ht
  -- sum the pointwise comparison, then evaluate the pair sum
  have hsum3 : (∑ t ∈ (G.neighborFinset v) ×ˢ ((G.neighborFinset v) ×ˢ (G.neighborFinset v)),
        (colSpace (V := V) k).prob {f : V → Fin k | t ∈ collisionTriples G f v})
      ≤ (1 / (k : ℝ)) * ∑ t ∈ (G.neighborFinset v) ×ˢ ((G.neighborFinset v) ×ˢ (G.neighborFinset v)),
        (colSpace (V := V) k).prob {f : V → Fin k | (t.1, t.2.1) ∈ collisionPairs G f v} := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  have hprod : (∑ t ∈ (G.neighborFinset v) ×ˢ ((G.neighborFinset v) ×ˢ (G.neighborFinset v)),
        (colSpace (V := V) k).prob {f : V → Fin k | (t.1, t.2.1) ∈ collisionPairs G f v})
      = (G.degree v : ℝ) * ∑ p ∈ (G.neighborFinset v) ×ˢ (G.neighborFinset v),
        (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v} :=
    sum_nbrCube G v (fun a b =>
      (colSpace (V := V) k).prob {f : V → Fin k | (a, b) ∈ collisionPairs G f v})
  have hsum2 : (∑ p ∈ (G.neighborFinset v) ×ˢ (G.neighborFinset v),
        (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v})
      = ∑ p ∈ nonAdjPairs G v,
        (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v} :=
    (Finset.sum_subset (Finset.filter_subset _ _)
      (fun p _ hp => prob_collisionPairs_eq_zero G hp)).symm
  -- `6 * E[tripleTerm] ≤ (1/k) * deg v * (2 * E[pairTerm])`
  have h6 : 6 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).tripleTerm v : ℝ))
      ≤ (1 / (k : ℝ)) * ((G.degree v : ℝ)
          * (2 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)))) := by
    rw [htriple]
    calc (∑ t ∈ (G.neighborFinset v) ×ˢ ((G.neighborFinset v) ×ˢ (G.neighborFinset v)),
          (colSpace (V := V) k).prob {f : V → Fin k | t ∈ collisionTriples G f v})
        ≤ (1 / (k : ℝ)) * ∑ t ∈ (G.neighborFinset v) ×ˢ ((G.neighborFinset v) ×ˢ (G.neighborFinset v)),
          (colSpace (V := V) k).prob {f : V → Fin k | (t.1, t.2.1) ∈ collisionPairs G f v} := hsum3
      _ = (1 / (k : ℝ)) * ((G.degree v : ℝ) * ∑ p ∈ (G.neighborFinset v) ×ˢ (G.neighborFinset v),
          (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v}) := by rw [hprod]
      _ = (1 / (k : ℝ)) * ((G.degree v : ℝ)
          * (2 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)))) := by
          rw [hsum2, ← hpair]
  -- hence `E[tripleTerm] ≤ (D/(3k)) * E[pairTerm]`
  have hET : (colSpace (V := V) k).expect (fun f => ((ofColoring G f).tripleTerm v : ℝ))
      ≤ ((D : ℝ) / (3 * (k : ℝ)))
        * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)) := by
    have hdegR : (G.degree v : ℝ) ≤ (D : ℝ) := by exact_mod_cast hdeg v
    have hEPnn : 0 ≤ (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)) :=
      FinSpace.expect_nonneg _ (fun f => Nat.cast_nonneg _)
    have h2 : 6 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).tripleTerm v : ℝ))
        ≤ ((2 * (G.degree v : ℝ)) / (k : ℝ))
          * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)) := by
      calc 6 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).tripleTerm v : ℝ))
          ≤ (1 / (k : ℝ)) * ((G.degree v : ℝ)
              * (2 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)))) := h6
        _ = ((2 * (G.degree v : ℝ)) / (k : ℝ))
              * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)) := by ring
    have h3 : (colSpace (V := V) k).expect (fun f => ((ofColoring G f).tripleTerm v : ℝ))
        ≤ ((2 * (G.degree v : ℝ)) / (k : ℝ))
            * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)) / 6 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
      linarith
    calc (colSpace (V := V) k).expect (fun f => ((ofColoring G f).tripleTerm v : ℝ))
        ≤ ((2 * (G.degree v : ℝ)) / (k : ℝ))
            * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)) / 6 := h3
      _ = ((G.degree v : ℝ) / (3 * (k : ℝ)))
            * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)) := by ring
      _ ≤ ((D : ℝ) / (3 * (k : ℝ)))
            * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hEPnn
          apply div_le_div_of_nonneg_right hdegR
          positivity
  -- assemble
  have h1m : (0 : ℝ) ≤ 1 - (D : ℝ) / (3 * (k : ℝ)) := by
    have hDkR : (D : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hDk
    have h3k : (0 : ℝ) < 3 * (k : ℝ) := by positivity
    have hle : (D : ℝ) / (3 * (k : ℝ)) ≤ 1 := by
      rw [div_le_one h3k]
      linarith
    linarith
  have hfin : ((nonAdjPairs G v).card : ℝ) / 2 * (1 - (D : ℝ) / (3 * (k : ℝ)))
        * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
      ≤ (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ))
        - (colSpace (V := V) k).expect (fun f => ((ofColoring G f).tripleTerm v : ℝ)) := by
    calc ((nonAdjPairs G v).card : ℝ) / 2 * (1 - (D : ℝ) / (3 * (k : ℝ)))
          * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
        = (1 - (D : ℝ) / (3 * (k : ℝ))) * (((nonAdjPairs G v).card : ℝ) / 2
            * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))) := by ring
      _ ≤ (1 - (D : ℝ) / (3 * (k : ℝ)))
            * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)) :=
          mul_le_mul_of_nonneg_left hEP h1m
      _ ≤ (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ))
            - (colSpace (V := V) k).expect (fun f => ((ofColoring G f).tripleTerm v : ℝ)) := by
          have hx := hET
          have : (1 - (D : ℝ) / (3 * (k : ℝ)))
                * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ))
              = (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ))
                - (D : ℝ) / (3 * (k : ℝ))
                  * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ)) := by
            ring
          rw [this]
          linarith
  rw [FinSpace.expect_sub]
  exact hfin

end Work.Deep.Sparse
