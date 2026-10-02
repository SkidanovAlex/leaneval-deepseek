/-
# The probability that prescribed colours all occur `j` times on *retained* neighbours

For the uniform random colouring `f : V → Fin k` (`colSpace`, see
`Submission/Work/Deep/Sparse/ProbBasic.lean`) and a vertex `v` of a graph `G`, a colour `c`
occurs `colourClassCount G f v c` times on the *retained* neighbours of `v` — the neighbours
of `v` that keep their colour under `f` (`Retained`, see `ProbModel`).  This module proves
that, for a set `S` of colours and a level `j ≥ 1`, the probability that *every* colour of
`S` occurs at least `j` times on the retained neighbours of `v` is at most

  `((indepSets G (G.neighborFinset v) j).card) ^ S.card / k ^ (j * S.card)`.

This is the refinement of `colSpace_prob_all_occ_le` needed for the *retained* occupancy
counts: the counting is over `indepSets` (the independent `j`-subsets of `N(v)`) rather than
all `j`-subsets of `N(v)`, because a colour class of retained neighbours is automatically
independent (two adjacent vertices cannot both retain a common colour).

The proof is the standard union bound.

* If every colour of `S` occurs `j` times on the retained neighbours of `v`, then for each
  colour `c ∈ S` the set of retained neighbours coloured `c` contains a `j`-element subset
  `T_c`; that subset is independent, since a retained vertex has no neighbour of its own
  colour.  Thus the event is contained in the union, over all families `(T_c)_{c ∈ S}` of
  members of `indepSets G (G.neighborFinset v) j`, of the cylinder events "all of `T_c` has
  colour `c` for every `c ∈ S`" (the family is indexed by the `Finset`
  `Fintype.piFinset (fun _ : ↥S => indepSets G (G.neighborFinset v) j)`).
* The union bound gives the sum of the probabilities of the cylinder events.
* Each cylinder event has probability at most `k ^ (-(j * S.card))`: it is contained in the
  `Fintype.piFinset` event of the allowed-colour function `B v = {c | every T_{c'} containing
  v is {c}}`, whose probability is `∏ v, |B v| / k` by the product law (`colSpace_prob_pi`).
  If the family `(T_c)` is pairwise disjoint then `|B v| ≤ 1` on the union `U` of the `T_c`
  and `|B v| ≤ k` off `U`, so the product is at most `(1/k) ^ (j * S.card)` because
  `|U| = ∑_c |T_c| = j * S.card`; if two of the `T_c` meet then the cylinder event is empty
  and there is nothing to prove.
* Finally there are `(indepSets G (G.neighborFinset v) j).card ^ S.card` families.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ncpTailDefs
import Submission.Work.Deep.Sparse.colSpace_prob_all_occ_le

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

/-- **Union bound** for a finite probability space: the probability of a finite union of
events is at most the sum of the individual probabilities. -/
private theorem prob_iUnion_le_sum_aux {Ω : Type*} [Fintype Ω] (P : FinSpace Ω) {ι : Type*}
    (s : Finset ι) (A : ι → Set Ω) :
    P.prob (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, P.prob (A i) := by
  classical
  calc P.prob (⋃ i ∈ s, A i) = ∑ ω, (⋃ i ∈ s, A i).indicator P.mass ω := rfl
    _ ≤ ∑ ω, ∑ i ∈ s, (A i).indicator P.mass ω := by
        refine Finset.sum_le_sum (fun ω _ => ?_)
        by_cases h : ω ∈ ⋃ i ∈ s, A i
        · rw [Set.indicator_of_mem h]
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
          obtain ⟨his, hAi⟩ := Set.mem_iUnion.mp hi
          have hsum : (A i).indicator P.mass ω ≤ ∑ x ∈ s, (A x).indicator P.mass ω :=
            Finset.single_le_sum (f := fun j => (A j).indicator P.mass ω) (fun j _ => by
              by_cases hj : ω ∈ A j
              · rw [Set.indicator_of_mem hj]; exact P.mass_nonneg ω
              · rw [Set.indicator_of_notMem hj]) his
          rwa [Set.indicator_of_mem hAi] at hsum
        · rw [Set.indicator_of_notMem h]
          exact Finset.sum_nonneg (fun i _ => FinSpace.ind_nonneg P (A i) ω)
    _ = ∑ i ∈ s, ∑ ω, (A i).indicator P.mass ω := Finset.sum_comm
    _ = ∑ i ∈ s, P.prob (A i) := rfl

theorem colCount_prob_all_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k) [Nonempty (V → Fin k)] (v : V) {j : ℕ} (hj : 0 < j) (S : Finset (Fin k)) : (colSpace (V := V) k).prob {f : V → Fin k | ∀ c ∈ S, j ≤ colourClassCount G f v c} ≤ ((indepSets G (G.neighborFinset v) j).card : ℝ) ^ S.card / (k : ℝ) ^ (j * S.card) := by
  classical
  set E : Set (V → Fin k) :=
    {f : V → Fin k | ∀ c ∈ S, j ≤ colourClassCount G f v c} with hE
  set F : Finset (↥S → Finset V) :=
    Fintype.piFinset (fun _ : ↥S => indepSets G (G.neighborFinset v) j) with hF
  set Ev : (↥S → Finset V) → Set (V → Fin k) :=
    fun π => {f : V → Fin k | ∀ c : ↥S, ∀ x ∈ π c, f x = (c : Fin k)} with hEv
  -- Step 1: the event is contained in the union of the cylinder events of all families of
  -- independent `j`-sets of neighbours, one per colour of `S`.
  have hsub : E ⊆ ⋃ π ∈ F, Ev π := by
    intro f hf
    rw [hE] at hf
    have hchoice : ∀ c : ↥S, ∃ T : Finset V,
        T ⊆ (G.neighborFinset v).filter (fun x => Retained G f x ∧ f x = (c : Fin k)) ∧
          T.card = j := by
      intro c
      have h := hf (c : Fin k) c.2
      rw [colourClassCount_eq] at h
      exact Finset.exists_subset_card_eq h
    choose π hπ using hchoice
    refine Set.mem_iUnion.mpr ⟨π, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · rw [hF, Fintype.mem_piFinset]
      intro c
      -- the colour class of a retained colour is independent
      refine mem_indepSets.mpr ⟨Finset.Subset.trans (hπ c).1 (Finset.filter_subset _ _),
        (hπ c).2, ?_⟩
      intro x hx y hy hxy
      have hmemx := (hπ c).1 hx
      have hmemy := (hπ c).1 hy
      simp only [Finset.mem_filter] at hmemx hmemy
      exact absurd ((hmemy.2.2).trans (hmemx.2.2).symm) (hmemx.2.1 y hxy)
    · show f ∈ Ev π
      rw [hEv]
      intro c x hx
      have hmemx := (hπ c).1 hx
      simp only [Finset.mem_filter] at hmemx
      exact hmemx.2.2
  -- Step 2: union bound
  have hbound1 : (colSpace (V := V) k).prob E
      ≤ ∑ π ∈ F, (colSpace (V := V) k).prob (Ev π) :=
    calc (colSpace (V := V) k).prob E
        ≤ (colSpace (V := V) k).prob (⋃ π ∈ F, Ev π) := FinSpace.prob_mono _ hsub
      _ ≤ ∑ π ∈ F, (colSpace (V := V) k).prob (Ev π) := prob_iUnion_le_sum_aux _ F Ev
  -- Step 3: each cylinder event has probability at most `(1/k) ^ (j * S.card)`
  have hbound2 : ∀ π ∈ F, (colSpace (V := V) k).prob (Ev π)
      ≤ (1 / (k : ℝ)) ^ (j * S.card) := by
    intro π hπF
    have hπmem : ∀ c : ↥S, π c ∈ indepSets G (G.neighborFinset v) j := by
      rw [hF] at hπF
      exact Fintype.mem_piFinset.mp hπF
    have hπc : ∀ c : ↥S, (π c).card = j :=
      fun c => (mem_indepSets.mp (hπmem c)).2.1
    by_cases hd : ∀ c c' : ↥S, c ≠ c' → Disjoint (π c) (π c')
    · -- the family `π` is pairwise disjoint
      set U : Finset V := (Finset.univ : Finset ↥S).biUnion π with hU
      set B : V → Finset (Fin k) :=
        fun v => (Finset.univ : Finset (Fin k)).filter
          (fun c => ∀ c' : ↥S, v ∈ π c' → (c' : Fin k) = c) with hB
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      -- the cylinder event is contained in the `piFinset` event of `B`
      have hsubB : Ev π ⊆ (↑(Fintype.piFinset B) : Set (V → Fin k)) := by
        intro f hf
        rw [hEv] at hf
        have hf' : ∀ c : ↥S, ∀ x ∈ π c, f x = (c : Fin k) := hf
        rw [Finset.mem_coe, Fintype.mem_piFinset]
        intro v
        simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun c' hv => (hf' c' v hv).symm
      -- the allowed-colour function `B` is small on `U` and everything off `U`
      have hBcard : ∀ v : V, (B v).card ≤ (if v ∈ U then 1 else k) := by
        intro v
        by_cases hv : v ∈ U
        · rw [if_pos hv]
          rw [hU, Finset.mem_biUnion] at hv
          obtain ⟨c₀, -, hvc₀⟩ := hv
          have hsub' : B v ⊆ ({(c₀ : Fin k)} : Finset (Fin k)) := by
            intro c hc
            simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hc
            exact Finset.mem_singleton.mpr (hc c₀ hvc₀).symm
          calc (B v).card ≤ ({(c₀ : Fin k)} : Finset (Fin k)).card := Finset.card_le_card hsub'
            _ = 1 := Finset.card_singleton _
        · rw [if_neg hv]
          have hBv : B v = Finset.univ := by
            rw [hB]
            ext c
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun _ => trivial, fun _ c' hvc' =>
              absurd (show v ∈ U from by
                rw [hU]
                exact Finset.mem_biUnion.mpr ⟨c', Finset.mem_univ c', hvc'⟩) hv⟩
          rw [hBv, Finset.card_univ, Fintype.card_fin]
      have hstep : (∏ v : V, ((B v).card : ℝ) / (k : ℝ))
          ≤ ∏ v : V, (if v ∈ U then (1 / (k : ℝ)) else 1) := by
        refine Finset.prod_le_prod₀ (fun v _ => div_nonneg (Nat.cast_nonneg _) hkpos.le)
          (fun v _ => ?_)
        by_cases hv : v ∈ U
        · have h1 : ((B v).card : ℝ) ≤ 1 := by
            have h2 := hBcard v
            rw [if_pos hv] at h2
            exact_mod_cast h2
          rw [if_pos hv, div_le_div_iff_of_pos_right hkpos]
          exact h1
        · have h1 : ((B v).card : ℝ) ≤ (k : ℝ) := by
            have h2 := hBcard v
            rw [if_neg hv] at h2
            exact_mod_cast h2
          rw [if_neg hv, div_le_one hkpos]
          exact h1
      have hprodU : (∏ v : V, (if v ∈ U then (1 / (k : ℝ)) else 1))
          = (1 / (k : ℝ)) ^ U.card := by
        rw [Finset.prod_ite (f := fun _ : V => (1 / (k : ℝ))) (g := fun _ : V => (1 : ℝ))]
        have hf1 : (Finset.univ.filter (fun v : V => v ∈ U)) = U := by
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        have hf2 : (∏ x ∈ (Finset.univ.filter fun v : V => ¬ v ∈ U), (1 : ℝ)) = 1 :=
          Finset.prod_eq_one (fun x _ => rfl)
        rw [hf1, hf2, Finset.prod_const, mul_one]
      have hUcard : U.card = j * S.card := by
        rw [hU, Finset.card_biUnion (t := π) (by intro a _ b _ hab; exact hd a b hab)]
        rw [Finset.sum_congr rfl (fun c _ => hπc c), Finset.sum_const, Finset.card_univ,
          Fintype.card_coe, nsmul_eq_mul]
        exact Nat.mul_comm _ _
      calc (colSpace (V := V) k).prob (Ev π)
          ≤ (colSpace (V := V) k).prob (↑(Fintype.piFinset B) : Set (V → Fin k)) :=
            FinSpace.prob_mono _ hsubB
        _ = ∏ v : V, ((B v).card : ℝ) / (k : ℝ) := colSpace_prob_pi B
        _ ≤ ∏ v : V, (if v ∈ U then (1 / (k : ℝ)) else 1) := hstep
        _ = (1 / (k : ℝ)) ^ U.card := hprodU
        _ = (1 / (k : ℝ)) ^ (j * S.card) := by rw [hUcard]
    · -- two of the sets of the family meet: the cylinder event is empty
      push Not at hd
      obtain ⟨c, c', hne, hnd⟩ := hd
      obtain ⟨x, hxc, hxc'⟩ := Finset.not_disjoint_iff.mp hnd
      have hempty : Ev π = ∅ := by
        rw [hEv]
        refine Set.eq_empty_iff_forall_notMem.mpr fun f hf => ?_
        have h1 : f x = (c : Fin k) := hf c x hxc
        have h2 : f x = (c' : Fin k) := hf c' x hxc'
        exact hne (Subtype.ext (h1.symm.trans h2))
      have hzero : (colSpace (V := V) k).prob (Ev π) = 0 := by
        rw [hempty, FinSpace.prob, Set.indicator_empty, Finset.sum_const_zero]
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      rw [hzero]
      exact pow_nonneg (div_nonneg zero_le_one hkpos.le) _
  -- Step 4: sum up
  calc (colSpace (V := V) k).prob E
      ≤ ∑ π ∈ F, (colSpace (V := V) k).prob (Ev π) := hbound1
    _ ≤ ∑ π ∈ F, (1 / (k : ℝ)) ^ (j * S.card) :=
        Finset.sum_le_sum (fun π hπ => hbound2 π hπ)
    _ = (F.card : ℝ) * (1 / (k : ℝ)) ^ (j * S.card) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((indepSets G (G.neighborFinset v) j).card : ℝ) ^ S.card
          * (1 / (k : ℝ)) ^ (j * S.card) := by
        have hFcard : (F.card : ℝ) = ((indepSets G (G.neighborFinset v) j).card : ℝ) ^ S.card := by
          rw [hF, Fintype.card_piFinset]
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
          rw [Nat.cast_pow]
        rw [hFcard]
    _ = ((indepSets G (G.neighborFinset v) j).card : ℝ) ^ S.card / (k : ℝ) ^ (j * S.card) := by
        rw [one_div_pow, mul_one_div]

end Work.Deep.Sparse
