import Submission.Grassmann.Cardinality

/-!
# Elementary facts about the expansion functional `Φ`

`Φ G S hS = #(G.interedges S Sᶜ) / (G.degree hS.choose * #S)` is the
(ordered, `S`-to-complement) edge-expansion ratio used in the formalisation of
Khot--Minzer--Safra's Theorem 1.12.

Here we record the basic sanity facts that any use of the hypothesis
`Φ (Gr k ℓ) S hS ≤ α` (with `0 < α`) relies on:

* `Φ` is non-negative;
* the number of boundary pairs is at most the sum of the degrees of the
  vertices of `S`;
* if every element of `S` has degree at most the degree of `hS.choose`
  (in particular if the graph is regular), then `Φ ≤ 1`.
-/

open PseudorandomGrassmann
open SimpleGraph
open Module Finset Filter

set_option autoImplicit false

namespace Submission.Grassmann

open Classical in
/-- The expansion ratio is non-negative (division in `ℚ` is total). -/
lemma Phi_nonneg {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : S.Nonempty) : (0 : ℚ) ≤ Φ G S hS := by
  unfold Φ
  have hnum0 : (0 : ℚ) ≤ (#(G.interedges S Sᶜ) : ℚ) := by
    exact_mod_cast Nat.zero_le _
  have hden0 : (0 : ℚ) ≤ (G.degree hS.choose : ℚ) * (#S : ℚ) := by positivity
  exact div_nonneg hnum0 hden0

open Classical in
/-- The number of boundary pairs (ordered, first coordinate in `S`) is at most
the sum of the degrees of the vertices of `S`. -/
lemma card_interedges_le_sum_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    #(G.interedges S Sᶜ) ≤ S.sum (fun v => G.degree v) := by
  classical
  let e : V → V ↪ V × V := fun v => ⟨(v, ·), Prod.mk_right_injective v⟩
  have hfib : G.interedges S Sᶜ = S.biUnion (fun v => ((Sᶜ.filter (fun w => G.Adj v w)).map (e v))) := by
    -- `SimpleGraph.interedges` is definitionally `Rel.interedges G.Adj`
    simpa [SimpleGraph.interedges] using
      (Rel.interedges_eq_biUnion (r := G.Adj) (s := S) (t := Sᶜ))
  calc
    #(G.interedges S Sᶜ)
        = #(S.biUnion (fun v => ((Sᶜ.filter (fun w => G.Adj v w)).map (e v)))) := by
          rw [hfib]
    _ ≤ S.sum (fun v => #((Sᶜ.filter (fun w => G.Adj v w)).map (e v))) := Finset.card_biUnion_le
    _ ≤ S.sum (fun v => G.degree v) := by
      apply Finset.sum_le_sum
      intro v _hv
      calc
        #((Sᶜ.filter (fun w => G.Adj v w)).map (e v)) = #(Sᶜ.filter (fun w => G.Adj v w)) := by
          rw [Finset.card_map]
        _ ≤ #(G.neighborFinset v) := by
          apply Finset.card_le_card
          intro w hw
          rw [mem_filter] at hw
          rw [mem_neighborFinset]
          exact hw.2
        _ = G.degree v := by rw [card_neighborFinset_eq_degree]

open Classical in
/-- If every vertex of `S` has degree at most the degree of `hS.choose` -- in
particular for regular graphs -- then the expansion ratio is at most `1`. -/
lemma Phi_le_one {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : S.Nonempty)
    (hdeg : ∀ v ∈ S, G.degree v ≤ G.degree hS.choose) :
    Φ G S hS ≤ 1 := by
  unfold Φ
  classical
  have hnum : #(G.interedges S Sᶜ) ≤ G.degree hS.choose * #S := by
    calc
      #(G.interedges S Sᶜ) ≤ S.sum (fun v => G.degree v) := card_interedges_le_sum_degree G S
      _ ≤ S.sum (fun _v => G.degree hS.choose) := by
        exact Finset.sum_le_sum (fun v hv => hdeg v hv)
      _ = G.degree hS.choose * #S := by
        simp [Finset.sum_const, Nat.mul_comm]
  have hnumQ : (↑(#(G.interedges S Sᶜ)) : ℚ) ≤ (G.degree hS.choose : ℚ) * (#S : ℚ) := by
    exact_mod_cast hnum
  have hden0 : (0 : ℚ) ≤ (G.degree hS.choose : ℚ) * (#S : ℚ) := by positivity
  by_cases hz : (G.degree hS.choose : ℚ) * (#S : ℚ) = 0
  · simp [hz]
  · have hpos : 0 < (G.degree hS.choose : ℚ) * (#S : ℚ) := lt_of_le_of_ne hden0 (Ne.symm hz)
    rw [div_le_iff₀ hpos]
    simpa using hnumQ

end Submission.Grassmann
