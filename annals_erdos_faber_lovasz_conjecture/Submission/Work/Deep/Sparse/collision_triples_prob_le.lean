import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.ProbBasic

/-!
# The triple collision probability is at most `1/k` times the pair collision probability

Fix a graph `G` on a finite vertex set `V`, a vertex `v` and an ordered triple
`t = (a, b, c)` of neighbours of `v`.  Under the uniform random colouring `g : V → Fin k`
(the sample space `Work.Deep.Sparse.colSpace`), the probability that `t` is a *collision
triple* at `v` (all three of `a, b, c` retain their colour and share it) is at most `1/k`
times the probability that the ordered pair `(a, b)` is a *collision pair* at `v`.

The point is that a collision triple consists of a collision pair together with the extra
requirement that the *third* vertex `c` is retained with the same colour; the vertex `c` is
not involved in the pair event, so pinning down its colour costs a factor `1/k`, and the
retention of `c` can only make the event smaller.

The formal argument:

* the pair event is the disjoint union, over the common colour `c₀`, of the cylinder events
  "`a` and `b` get colour `c₀` and every vertex of `T = N(a) ∪ N(b)` avoids `c₀`"
  (`hpair_set`, `hpair_disj`);
* each such cylinder event is a `Fintype.piFinset` event (`setOf_pair_eq_piFinset`), and
  intersecting it with the coordinate condition `g c = c₀` at a coordinate `c` where the
  cylinder is `Finset.univ` multiplies its probability by `1/k`
  (`piFinset_inter_singleton`, `prob_pi_update`, `prob_piFinset_inter`);
* the triple event is contained in the union over `c₀` of those intersections (`htriple_sub`).

Everything is elementary: only the product law of the random colouring
(`Work.Deep.Sparse.colSpace_prob_pi`) is used.
-/

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Two elementary cylinder computations -/

/-- The event "`x` gets the colour `c₀` and every vertex of `T` avoids `c₀`" (with
`x ∉ T`) is the `Fintype.piFinset` event of the allowed-colour function that pins `x` to
`{c₀}`, forbids `c₀` on `T` and allows everything else. -/
theorem setOf_pair_eq_piFinset {k : ℕ} (c₀ : Fin k) {x y : V} (hxy : x ≠ y) {T : Finset V}
    (hxT : x ∉ T) (hyT : y ∉ T) :
    {g : V → Fin k | g x = c₀ ∧ g y = c₀ ∧ ∀ w ∈ T, g w ≠ c₀}
      = (↑(Fintype.piFinset (fun v => if v = x then {c₀} else if v = y then {c₀}
          else if v ∈ T then colourCompl c₀ else Finset.univ)) : Set (V → Fin k)) := by
  ext g
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Fintype.mem_piFinset]
  constructor
  · intro hg v
    by_cases hvx : v = x
    · rw [if_pos hvx, Finset.mem_singleton]; rw [hvx]; exact hg.1
    · rw [if_neg hvx]
      by_cases hvy : v = y
      · rw [if_pos hvy, Finset.mem_singleton]; rw [hvy]; exact hg.2.1
      · rw [if_neg hvy]
        by_cases hvT : v ∈ T
        · rw [if_pos hvT, mem_colourCompl]; exact hg.2.2 v hvT
        · rw [if_neg hvT]; exact Finset.mem_univ (g v)
  · intro hg
    refine ⟨?_, ?_, ?_⟩
    · have h := hg x; rw [if_pos rfl, Finset.mem_singleton] at h; exact h
    · have h := hg y; rw [if_neg (Ne.symm hxy), if_pos rfl, Finset.mem_singleton] at h; exact h
    · intro w hw
      have h := hg w
      have hwa : w ≠ x := by rintro rfl; exact hxT hw
      have hwb : w ≠ y := by rintro rfl; exact hyT hw
      rw [if_neg hwa, if_neg hwb, if_pos hw, mem_colourCompl] at h
      exact h

/-- **Freezing a free coordinate costs a factor `1/k`.**  If the allowed-colour function `A`
imposes no restriction at the coordinate `x`, then the probability of the cylinder event
`π A` intersected with the condition "`x` gets the colour `c`" is `1/k` times the probability
of `π A`. -/
theorem prob_pi_update {k : ℕ} [Nonempty (V → Fin k)] (hk : 0 < k)
    (A : V → Finset (Fin k)) (x : V) (c' : Fin k) (hx : A x = Finset.univ) :
    (colSpace (V := V) k).prob
        (↑(Fintype.piFinset (fun v => if v = x then {c'} else A v)) : Set (V → Fin k))
      = (1 / (k : ℝ)) * (colSpace (V := V) k).prob
          (↑(Fintype.piFinset A) : Set (V → Fin k)) := by
  classical
  rw [colSpace_prob_pi, colSpace_prob_pi]
  have hkne : ((k : ℕ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hAx : (((A x).card : ℝ)) / (k : ℝ) = 1 := by
    rw [hx, Finset.card_univ, Fintype.card_fin]
    exact div_self hkne
  have hgx : (((if x = x then ({c'} : Finset (Fin k)) else A x).card : ℝ)) / (k : ℝ)
      = 1 / (k : ℝ) := by
    rw [if_pos rfl, Finset.card_singleton, Nat.cast_one]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset V)
      (fun v => (((if v = x then ({c'} : Finset (Fin k)) else A v).card : ℝ)) / (k : ℝ))
      (Finset.mem_univ x)]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset V)
      (fun v => ((A v).card : ℝ) / (k : ℝ)) (Finset.mem_univ x)]
  rw [hgx, hAx, one_mul]
  congr 1
  exact Finset.prod_congr rfl fun v hv => by
    rw [Finset.mem_erase] at hv
    rw [if_neg hv.1]

/-- The `Fintype.piFinset` event of `A`, intersected with the coordinate condition "`x` gets
the colour `c`", is the `Fintype.piFinset` event of the updated allowed-colour function. -/
theorem piFinset_inter_singleton {k : ℕ} (A : V → Finset (Fin k)) (x : V) (c' : Fin k)
    (hx : A x = Finset.univ) :
    (↑(Fintype.piFinset A) : Set (V → Fin k)) ∩ {g : V → Fin k | g x = c'}
      = (↑(Fintype.piFinset (fun v => if v = x then {c'} else A v)) : Set (V → Fin k)) := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_coe, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hA, hgx⟩ v
    by_cases hvx : v = x
    · rw [if_pos hvx, Finset.mem_singleton]; rw [hvx]; exact hgx
    · rw [if_neg hvx]; exact hA v
  · intro h
    refine ⟨fun v => ?_, ?_⟩
    · have hv := h v
      by_cases hvx : v = x
      · rw [if_pos hvx, Finset.mem_singleton] at hv
        rw [hvx, hx]; exact Finset.mem_univ _
      · rw [if_neg hvx] at hv; exact hv
    · have hx' := h x
      rw [if_pos rfl, Finset.mem_singleton] at hx'
      exact hx'

/-- Freezing a free coordinate of a `Fintype.piFinset` event costs a factor `1/k`. -/
theorem prob_piFinset_inter {k : ℕ} [Nonempty (V → Fin k)] (hk : 0 < k)
    (A : V → Finset (Fin k)) (x : V) (c' : Fin k) (hx : A x = Finset.univ) :
    (colSpace (V := V) k).prob
        ((↑(Fintype.piFinset A) : Set (V → Fin k)) ∩ {g : V → Fin k | g x = c'})
      = (1 / (k : ℝ)) * (colSpace (V := V) k).prob
          (↑(Fintype.piFinset A) : Set (V → Fin k)) := by
  rw [piFinset_inter_singleton A x c' hx, prob_pi_update hk A x c' hx]

/-! ## The main lemma -/

theorem collision_triples_prob_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k) [Nonempty (V → Fin k)] (v : V) (t : V × V × V) (ht : t ∈ (G.neighborFinset v) ×ˢ ((G.neighborFinset v) ×ˢ (G.neighborFinset v))) : (Work.Deep.Sparse.colSpace (V := V) k).prob {g : V → Fin k | t ∈ Work.Deep.Sparse.collisionTriples G g v} ≤ (1 / (k : ℝ)) * (Work.Deep.Sparse.colSpace (V := V) k).prob {g : V → Fin k | (t.1, t.2.1) ∈ Work.Deep.Sparse.collisionPairs G g v} := by
  classical
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, t = (a, b, c) := ⟨t.1, t.2.1, t.2.2, rfl⟩
  change (colSpace (V := V) k).prob {g : V → Fin k | (a, b, c) ∈ collisionTriples G g v}
      ≤ (1 / (k : ℝ)) * (colSpace (V := V) k).prob {g : V → Fin k | (a, b) ∈ collisionPairs G g v}
  have ha : a ∈ G.neighborFinset v := by
    have h := ht; simp only [Finset.mem_product] at h; exact h.1
  have hb : b ∈ G.neighborFinset v := by
    have h := ht; simp only [Finset.mem_product] at h; exact h.2.1
  have hc : c ∈ G.neighborFinset v := by
    have h := ht; simp only [Finset.mem_product] at h; exact h.2.2
  by_cases hgood : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c
  · -- the generic case: `a, b, c` are distinct and pairwise non-adjacent
    obtain ⟨hab, hac, hbc, hnab, hnac, hnbc⟩ := hgood
    set T : Finset V := G.neighborFinset a ∪ G.neighborFinset b with hT
    have hTa : a ∉ T := by
      rw [hT, Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      rintro (h | h)
      · exact G.irrefl h
      · exact hnab ((SimpleGraph.adj_comm G a b).mpr h)
    have hTb : b ∉ T := by
      rw [hT, Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      rintro (h | h)
      · exact hnab h
      · exact G.irrefl h
    have hTc : c ∉ T := by
      rw [hT, Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      rintro (h | h)
      · exact hnac h
      · exact hnbc h
    -- the pair event splits over the common colour of `a` and `b`
    have hpair_set : {g : V → Fin k | (a, b) ∈ collisionPairs G g v}
        = ⋃ c₀ ∈ (Finset.univ : Finset (Fin k)),
            {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ ∀ w ∈ T, g w ≠ c₀} := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion₂, Finset.mem_univ, exists_prop, true_and]
      constructor
      · intro hg
        rw [mem_collisionPairs] at hg
        obtain ⟨-, -, -, hRa, hRb, hgab⟩ := hg
        refine ⟨g a, rfl, ?_, ?_⟩
        · rw [hgab]
        · intro w hw
          rw [hT, Finset.mem_union] at hw
          rcases hw with hw | hw
          · exact hRa w ((SimpleGraph.mem_neighborFinset G a w).mp hw)
          · rw [hgab]; exact hRb w ((SimpleGraph.mem_neighborFinset G b w).mp hw)
      · rintro ⟨c₀, h1, h2, h3⟩
        rw [mem_collisionPairs]
        refine ⟨ha, hb, hab, ?_, ?_, by rw [h1, h2]⟩
        · intro w hw
          rw [h1]
          refine h3 w ?_
          rw [hT]
          exact Finset.mem_union.mpr (Or.inl ((SimpleGraph.mem_neighborFinset G a w).mpr hw))
        · intro w hw
          rw [h2]
          refine h3 w ?_
          rw [hT]
          exact Finset.mem_union.mpr (Or.inr ((SimpleGraph.mem_neighborFinset G b w).mpr hw))
    have hpair_disj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (fun c₀ => {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ ∀ w ∈ T, g w ≠ c₀}) := by
      intro c _ c' _ hcc'
      rw [Function.onFun, Set.disjoint_left]
      intro g hg hg'
      simp only [Set.mem_ofPred_eq] at hg hg'
      exact hcc' (hg.1.symm.trans hg'.1)
    have hpair_prob : (colSpace (V := V) k).prob {g : V → Fin k | (a, b) ∈ collisionPairs G g v}
        = ∑ c₀ ∈ (Finset.univ : Finset (Fin k)),
            (colSpace (V := V) k).prob
              {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ ∀ w ∈ T, g w ≠ c₀} := by
      rw [hpair_set]
      exact FinSpace.prob_biUnion_disjoint _ _ _ hpair_disj
    -- for each colour, adding the requirement that `c` gets the same colour costs `1/k`
    have hpoint : ∀ c₀ : Fin k,
        (colSpace (V := V) k).prob
            {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ g c = c₀ ∧ ∀ w ∈ T, g w ≠ c₀}
        ≤ (1 / (k : ℝ)) * (colSpace (V := V) k).prob
            {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ ∀ w ∈ T, g w ≠ c₀} := by
      intro c₀
      have hπ : {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ ∀ w ∈ T, g w ≠ c₀}
          = (↑(Fintype.piFinset (fun v => if v = a then {c₀} else if v = b then {c₀}
              else if v ∈ T then colourCompl c₀ else Finset.univ)) : Set (V → Fin k)) :=
        setOf_pair_eq_piFinset c₀ hab hTa hTb
      have hAuniv : ((fun v => if v = a then {c₀} else if v = b then {c₀}
              else if v ∈ T then colourCompl c₀ else Finset.univ) c) = Finset.univ := by
        show (if c = a then {c₀} else if c = b then {c₀}
          else if c ∈ T then colourCompl c₀ else Finset.univ) = Finset.univ
        rw [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), if_neg hTc]
      have hregroup : {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ g c = c₀ ∧ ∀ w ∈ T, g w ≠ c₀}
          = {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ ∀ w ∈ T, g w ≠ c₀}
            ∩ {g : V → Fin k | g c = c₀} := by
        ext g; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
      rw [hregroup, hπ, prob_piFinset_inter (V := V) hk _ c c₀ hAuniv]
    have hsum_bound : (∑ c₀ ∈ (Finset.univ : Finset (Fin k)),
          (colSpace (V := V) k).prob
            {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ g c = c₀ ∧ ∀ w ∈ T, g w ≠ c₀})
        ≤ (1 / (k : ℝ)) * ∑ c₀ ∈ (Finset.univ : Finset (Fin k)),
          (colSpace (V := V) k).prob {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ ∀ w ∈ T, g w ≠ c₀} := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun c₀ _ => hpoint c₀
    -- the triple event is contained in the union of the "frozen" cylinders
    have htriple_le : (colSpace (V := V) k).prob {g : V → Fin k | (a, b, c) ∈ collisionTriples G g v}
        ≤ ∑ c₀ ∈ (Finset.univ : Finset (Fin k)),
            (colSpace (V := V) k).prob
              {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ g c = c₀ ∧ ∀ w ∈ T, g w ≠ c₀} := by
      have hsub : {g : V → Fin k | (a, b, c) ∈ collisionTriples G g v}
          ⊆ ⋃ c₀ ∈ (Finset.univ : Finset (Fin k)),
              {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ g c = c₀ ∧ ∀ w ∈ T, g w ≠ c₀} := by
        intro g hg
        rw [Set.mem_ofPred_eq] at hg
        rw [mem_collisionTriples] at hg
        obtain ⟨-, -, -, -, -, -, hRa, hRb, -, hgab, hgbc⟩ := hg
        simp only [Set.mem_iUnion₂, Finset.mem_univ, exists_prop, true_and, Set.mem_ofPred_eq]
        refine ⟨g a, rfl, ?_, ?_, ?_⟩
        · rw [hgab]
        · rw [← hgbc, hgab]
        · intro w hw
          rw [hT, Finset.mem_union] at hw
          rcases hw with hw | hw
          · exact hRa w ((SimpleGraph.mem_neighborFinset G a w).mp hw)
          · rw [hgab]; exact hRb w ((SimpleGraph.mem_neighborFinset G b w).mp hw)
      have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
          (fun c₀ => {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ g c = c₀ ∧ ∀ w ∈ T, g w ≠ c₀}) := by
        intro c _ c' _ hcc'
        rw [Function.onFun, Set.disjoint_left]
        intro g hg hg'
        simp only [Set.mem_ofPred_eq] at hg hg'
        exact hcc' (hg.1.symm.trans hg'.1)
      calc (colSpace (V := V) k).prob {g : V → Fin k | (a, b, c) ∈ collisionTriples G g v}
          ≤ (colSpace (V := V) k).prob (⋃ c₀ ∈ (Finset.univ : Finset (Fin k)),
              {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ g c = c₀ ∧ ∀ w ∈ T, g w ≠ c₀}) :=
            FinSpace.prob_mono _ hsub
        _ = ∑ c₀ ∈ (Finset.univ : Finset (Fin k)),
              (colSpace (V := V) k).prob
                {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ g c = c₀ ∧ ∀ w ∈ T, g w ≠ c₀} :=
            FinSpace.prob_biUnion_disjoint _ _ _ hdisj
    calc (colSpace (V := V) k).prob {g : V → Fin k | (a, b, c) ∈ collisionTriples G g v}
        ≤ ∑ c₀ ∈ (Finset.univ : Finset (Fin k)),
            (colSpace (V := V) k).prob
              {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ g c = c₀ ∧ ∀ w ∈ T, g w ≠ c₀} := htriple_le
      _ ≤ (1 / (k : ℝ)) * ∑ c₀ ∈ (Finset.univ : Finset (Fin k)),
            (colSpace (V := V) k).prob
              {g : V → Fin k | g a = c₀ ∧ g b = c₀ ∧ ∀ w ∈ T, g w ≠ c₀} := hsum_bound
      _ = (1 / (k : ℝ)) * (colSpace (V := V) k).prob
            {g : V → Fin k | (a, b) ∈ collisionPairs G g v} := by
          rw [hpair_prob]
  · -- degenerate case: the triple event is empty
    have hcases : a = b ∨ a = c ∨ b = c ∨ G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
      tauto
    have hempty : ∀ g : V → Fin k, (a, b, c) ∈ collisionTriples G g v → False := by
      intro g hmem
      rw [mem_collisionTriples] at hmem
      obtain ⟨-, -, -, h1, h2, h3, hR1, hR2, hR3, he1, he2⟩ := hmem
      rcases hcases with h | h | h | h | h | h
      · exact h1 h
      · exact h2 h
      · exact h3 h
      · exact hR1 b h he1.symm
      · exact hR1 c h (he2.symm.trans he1.symm)
      · exact hR2 c h he2.symm
    have hLHS0 : (colSpace (V := V) k).prob
        {g : V → Fin k | (a, b, c) ∈ collisionTriples G g v} = 0 := by
      have hsub : {g : V → Fin k | (a, b, c) ∈ collisionTriples G g v} ⊆ (∅ : Set (V → Fin k)) :=
        fun g hg => hempty g hg
      have hle := FinSpace.prob_mono (colSpace (V := V) k) hsub
      have h0 : (colSpace (V := V) k).prob (∅ : Set (V → Fin k)) = 0 := by
        rw [FinSpace.prob]
        exact Finset.sum_eq_zero fun ω _ => Set.indicator_of_notMem (Set.notMem_empty ω) _
      rw [h0] at hle
      exact le_antisymm hle (FinSpace.prob_nonneg _ _)
    rw [hLHS0]
    refine mul_nonneg ?_ (FinSpace.prob_nonneg _ _)
    exact one_div_nonneg.mpr (by exact_mod_cast hk.le)

end Work.Deep.Sparse
