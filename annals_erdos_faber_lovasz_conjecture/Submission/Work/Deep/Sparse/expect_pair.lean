import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.ProbModel

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Elementary arithmetic of `n.choose 2` -/

/-- `n * (n - 1) = 2 * n.choose 2`. -/
private lemma mul_self_sub_self_eq_two_mul_choose_two (n : ℕ) : n * n - n = 2 * n.choose 2 := by
  rw [Nat.choose_two_right, ← Nat.mul_div_assoc 2 (Nat.two_dvd_mul_sub_one n),
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), ← Nat.mul_sub_one n n]

/-! ## The counting identity: the colliding ordered pairs enumerate `pairTerm` -/

/-- The number of ordered pairs of distinct retained neighbours of `v` which carry the same
colour under `f` is exactly `2 * pairTerm` of the induced partial colouring. -/
private lemma collisionPairs_card_eq (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (f : V → Fin k) (v : V) :
    (collisionPairs G f v).card = 2 * (ofColoring G f).pairTerm v := by
  classical
  let S : Fin k → Finset V :=
    fun c => (G.neighborFinset v).filter (fun w => Retained G f w ∧ f w = c)
  have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun c => (S c).offDiag) := by
    intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    have h1 : f p.1 = c := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hp).1).2.2
    have h2 : f p.1 = c' := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hp').1).2.2
    exact hcc' (h1 ▸ h2)
  have hunion : collisionPairs G f v =
      (Finset.univ : Finset (Fin k)).disjiUnion (fun c => (S c).offDiag) hdisj := by
    ext p
    rw [Finset.mem_disjiUnion, mem_collisionPairs]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨f p.1, Finset.mem_univ _, Finset.mem_offDiag.mpr
        ⟨Finset.mem_filter.mpr ⟨h1, h4, rfl⟩, Finset.mem_filter.mpr ⟨h2, h5, h6.symm⟩, h3⟩⟩
    · rintro ⟨c, -, hc⟩
      obtain ⟨hc1, hc2, hne⟩ := Finset.mem_offDiag.mp hc
      obtain ⟨hc1a, hc1b, hc1c⟩ := Finset.mem_filter.mp hc1
      obtain ⟨hc2a, hc2b, hc2c⟩ := Finset.mem_filter.mp hc2
      exact ⟨hc1a, hc2a, hne, hc1b, hc2b, hc1c.trans hc2c.symm⟩
  rw [hunion, Finset.card_disjiUnion, pairTerm_ofColoring G f v, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.offDiag_card]
  exact mul_self_sub_self_eq_two_mul_choose_two (S c).card

/-! ## The expectation is a sum over the non-adjacent pairs -/

/-- Twice the expectation of `pairTerm` is the sum, over the ordered pairs of distinct
non-adjacent neighbours of `v`, of the probability that the pair collides. -/
private lemma two_mul_expect_pairTerm (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    [Nonempty (V → Fin k)] (v : V) :
    2 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ))
      = ∑ p ∈ nonAdjPairs G v,
          (colSpace (V := V) k).prob {g : V → Fin k | p ∈ collisionPairs G g v} := by
  classical
  have hsub : ∀ f : V → Fin k, collisionPairs G f v ⊆ nonAdjPairs G v := by
    intro f p hp
    rw [mem_collisionPairs] at hp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
    rw [mem_nonAdjPairs]
    exact ⟨h1, h2, h3, fun hadj => h4 p.2 hadj h6.symm⟩
  have hcardf : ∀ f : V → Fin k, ((collisionPairs G f v).card : ℝ)
      = ∑ p ∈ nonAdjPairs G v, (if p ∈ collisionPairs G f v then (1 : ℝ) else 0) := by
    intro f
    have hunit : ∑ p ∈ collisionPairs G f v, (if p ∈ collisionPairs G f v then (1 : ℝ) else 0)
        = ∑ _p ∈ collisionPairs G f v, (1 : ℝ) :=
      Finset.sum_congr rfl (fun p hp => if_pos hp)
    have hcast : ∑ _p ∈ collisionPairs G f v, (1 : ℝ) = ((collisionPairs G f v).card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    calc ((collisionPairs G f v).card : ℝ)
        = ∑ p ∈ collisionPairs G f v, (if p ∈ collisionPairs G f v then (1 : ℝ) else 0) := by
          rw [hunit, hcast]
      _ = ∑ p ∈ nonAdjPairs G v, (if p ∈ collisionPairs G f v then (1 : ℝ) else 0) :=
          Finset.sum_subset (hsub f) (fun x _ hx => by simp [hx])
  calc 2 * (colSpace (V := V) k).expect (fun f => ((ofColoring G f).pairTerm v : ℝ))
      = ∑ f, (colSpace (V := V) k).mass f * ((collisionPairs G f v).card : ℝ) := by
        rw [FinSpace.expect, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [collisionPairs_card_eq G f v]
        push_cast
        ring
    _ = ∑ f, (colSpace (V := V) k).mass f *
          ∑ p ∈ nonAdjPairs G v, (if p ∈ collisionPairs G f v then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [hcardf f]
    _ = ∑ f, ∑ p ∈ nonAdjPairs G v, (colSpace (V := V) k).mass f *
          (if p ∈ collisionPairs G f v then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ p ∈ nonAdjPairs G v, ∑ f, (colSpace (V := V) k).mass f *
          (if p ∈ collisionPairs G f v then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ p ∈ nonAdjPairs G v,
          (colSpace (V := V) k).prob {g : V → Fin k | p ∈ collisionPairs G g v} := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [FinSpace.prob]
        refine Finset.sum_congr rfl (fun f _ => ?_)
        by_cases h : p ∈ collisionPairs G f v
        · rw [if_pos h,
            Set.indicator_of_mem (show f ∈ ({g : V → Fin k | p ∈ collisionPairs G g v} :
              Set (V → Fin k)) from h), mul_one]
        · rw [if_neg h,
            Set.indicator_of_notMem (show f ∉ ({g : V → Fin k | p ∈ collisionPairs G g v} :
              Set (V → Fin k)) from fun hf => h hf), mul_zero]

/-! ## The probability that a fixed pair collides -/

/-- The probability that a fixed ordered pair of distinct non-adjacent neighbours of `v`
collides is at least `(1/k) ((k-1)/k)^(2D)`. -/
private lemma prob_collision_aux (G : SimpleGraph V) [DecidableRel G.Adj] {k D : ℕ} (hk : 0 < k)
    [Nonempty (V → Fin k)] (hdeg : ∀ x : V, G.degree x ≤ D) (v : V) {p : V × V}
    (hp : p ∈ nonAdjPairs G v) :
    (1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D)
      ≤ (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v} := by
  classical
  rw [mem_nonAdjPairs] at hp
  obtain ⟨hxN, hyN, hxy, hnadj⟩ := hp
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set T : Finset V := G.neighborFinset p.1 ∪ G.neighborFinset p.2 with hT
  have hxT : p.1 ∉ T := by
    rw [hT, Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
    rintro (h | h)
    · exact G.irrefl h
    · exact hnadj ((SimpleGraph.adj_comm G p.1 p.2).mpr h)
  have hyT : p.2 ∉ T := by
    rw [hT, Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
    rintro (h | h)
    · exact hnadj h
    · exact G.irrefl h
  have hset : {f : V → Fin k | p ∈ collisionPairs G f v}
      = ⋃ c ∈ (Finset.univ : Finset (Fin k)),
          {f : V → Fin k | f p.1 = c ∧ f p.2 = c ∧ ∀ w ∈ T, f w ≠ c} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion₂, Finset.mem_univ, exists_prop, true_and]
    constructor
    · intro hg
      rw [mem_collisionPairs] at hg
      obtain ⟨-, -, -, hg4, hg5, hg6⟩ := hg
      refine ⟨g p.1, rfl, hg6.symm, fun w hw => ?_⟩
      rw [hT, Finset.mem_union] at hw
      rcases hw with hw | hw
      · exact hg4 w ((SimpleGraph.mem_neighborFinset G p.1 w).mp hw)
      · rw [hg6]
        exact hg5 w ((SimpleGraph.mem_neighborFinset G p.2 w).mp hw)
    · rintro ⟨c, h1, h2, h3⟩
      rw [mem_collisionPairs]
      refine ⟨hxN, hyN, hxy, ?_, ?_, by rw [h1, h2]⟩
      · intro w hw
        rw [h1]
        exact h3 w (Finset.mem_union.mpr (Or.inl ((SimpleGraph.mem_neighborFinset G p.1 w).mpr hw)))
      · intro w hw
        rw [h2]
        exact h3 w (Finset.mem_union.mpr (Or.inr ((SimpleGraph.mem_neighborFinset G p.2 w).mpr hw)))
  have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun c => {f : V → Fin k | f p.1 = c ∧ f p.2 = c ∧ ∀ w ∈ T, f w ≠ c}) := by
    intro c _ c' _ hcc'
    rw [Function.onFun, Set.disjoint_left]
    intro g hg hg'
    simp only [Set.mem_ofPred_eq] at hg hg'
    exact hcc' (hg.1.symm.trans hg'.1)
  have hcard : T.card ≤ 2 * D := by
    rw [hT]
    calc (G.neighborFinset p.1 ∪ G.neighborFinset p.2).card
        ≤ (G.neighborFinset p.1).card + (G.neighborFinset p.2).card := Finset.card_union_le _ _
      _ = G.degree p.1 + G.degree p.2 := by
            rw [SimpleGraph.card_neighborFinset_eq_degree,
              SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ D + D := add_le_add (hdeg p.1) (hdeg p.2)
      _ = 2 * D := by ring
  have hb0 : 0 ≤ ((k : ℝ) - 1) / (k : ℝ) := by
    apply div_nonneg _ hkR.le
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hb1 : ((k : ℝ) - 1) / (k : ℝ) ≤ 1 := by
    rw [div_le_one hkR]
    linarith
  have hpw : (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D) ≤ (((k : ℝ) - 1) / (k : ℝ)) ^ T.card :=
    pow_le_pow_of_le_one hb0 hb1 hcard
  have hbu : (colSpace (V := V) k).prob
        (⋃ c ∈ (Finset.univ : Finset (Fin k)),
          {f : V → Fin k | f p.1 = c ∧ f p.2 = c ∧ ∀ w ∈ T, f w ≠ c})
      = ∑ c ∈ (Finset.univ : Finset (Fin k)), (colSpace (V := V) k).prob
          {f : V → Fin k | f p.1 = c ∧ f p.2 = c ∧ ∀ w ∈ T, f w ≠ c} :=
    FinSpace.prob_biUnion_disjoint (colSpace (V := V) k) (Finset.univ : Finset (Fin k)) _ hdisj
  have hfield : (1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ T.card
      = ∑ c ∈ (Finset.univ : Finset (Fin k)),
          (1 : ℝ) / (k : ℝ) * (1 / (k : ℝ)) * (((k : ℝ) - 1) / (k : ℝ)) ^ T.card := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hset, hbu]
  calc (1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D)
      ≤ (1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ T.card :=
        mul_le_mul_of_nonneg_left hpw (by positivity)
    _ = ∑ c ∈ (Finset.univ : Finset (Fin k)),
          (1 : ℝ) / (k : ℝ) * (1 / (k : ℝ)) * (((k : ℝ) - 1) / (k : ℝ)) ^ T.card := hfield
    _ = ∑ c ∈ (Finset.univ : Finset (Fin k)), (colSpace (V := V) k).prob
          {f : V → Fin k | f p.1 = c ∧ f p.2 = c ∧ ∀ w ∈ T, f w ≠ c} := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [prob_two_and_avoid (V := V) (x := p.1) (y := p.2) (T := T) hk hxy hxT hyT c]

/-! ## The target -/

theorem expect_pair {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k D : ℕ} (hk : 0 < k) (hD : 0 < D) [Nonempty (V → Fin k)]
    (hdeg : ∀ x : V, G.degree x ≤ D) (v : V) :
    ((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2
        * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
      ≤ (Work.Deep.Sparse.colSpace (V := V) k).expect
          (fun f => ((Work.Deep.Sparse.ofColoring G f).pairTerm v : ℝ)) := by
  classical
  have hmain := two_mul_expect_pairTerm (V := V) (k := k) G v
  have hbound : ∑ p ∈ nonAdjPairs G v,
        ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
      ≤ ∑ p ∈ nonAdjPairs G v,
          (colSpace (V := V) k).prob {f : V → Fin k | p ∈ collisionPairs G f v} :=
    Finset.sum_le_sum (fun p hp => prob_collision_aux (V := V) (k := k) (D := D) G hk hdeg v hp)
  have hconst : ∑ p ∈ nonAdjPairs G v,
        ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
      = ((nonAdjPairs G v).card : ℝ)
          * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ((nonAdjPairs G v).card : ℝ)
        * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
      ≤ 2 * ((colSpace (V := V) k).expect
          (fun f => ((ofColoring G f).pairTerm v : ℝ))) := by
    rw [hmain, ← hconst]
    exact hbound
  have h3 : ((nonAdjPairs G v).card : ℝ) / 2
        * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
      = (((nonAdjPairs G v).card : ℝ)
          * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))) / 2 := by
    ring
  rw [h3]
  linarith

end Work.Deep.Sparse
