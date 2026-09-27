import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.SpineDefs
import Submission.Work.Noncompact.CompressionTube.CorridorDefs
import Submission.Work.Noncompact.CompressionTube.LineBuild.nested_canals
import Submission.Work.Noncompact.Routing.junction_facts
import Submission.Work.Noncompact.Routing.seed_shell
import Submission.Work.Noncompact.CompressionTube.thinPairwiseDisjointNhd

namespace Work.Noncompact.CompressionTube

/-- **The corridor chain of a nested canal datum.**  The concrete corridor construction of the
routing: from the spine `SpineData K B lev q γ` of `exists_nested_canals` (with the tail containment
of the spine arcs in the nested regions `D b · ⊆ W b` and `q b (lev b) = b`), every canal `W b`
carries a `CorridorChain (b : M) (W b)`.

Concretely (this is the construction the reviewers confirmed): for each `b` one takes the junctions
`Q i := q b (lev b + i)` (so `Q 0 = b`), the shells `U i := interior (K (lev b + i + 2)) \ K (lev b + i)`
and the corridors `C i` = the connected component of `U i ∩ W b` containing the spine arc
`A i := γ b (lev b + i) '' Set.Icc 0 1`.  Then

* `A i` is compact and connected (continuous image of `Icc`), `A i ⊆ W b` by `htail` + `hDsub`, and
  `A i ⊆ U i` by `SpineData.image_sub` + `disjoint_K`, so `C i` is an open preconnected neighbourhood
  of `A i` inside `U i ∩ W b`;
* `C i` contains `Q i` and `Q (i+1)` (`SpineData.ends`, `hqlev`);
* `C i ∩ C j = ∅` for `Nat.dist i j ≥ 2`: `C i ⊆ U i` and, for `j ≥ i + 2`, `U j ⊆ (K (lev b + j))ᶜ`
  with `K (lev b + i + 2) ⊆ K (lev b + j)` (monotonicity of the exhaustion, from `hKsub`);
* the **neck** at `Q (i+1)` is the shell `V := interior (K (lev b + i + 2)) \ K (lev b + i + 1)`:
  open, contains `Q (i+1)` by `SpineData.q_shell`, contains `C i ∩ C (i+1)` (since
  `C i ⊆ interior (K (lev b+i+2))` and `C (i+1) ⊆ (K (lev b+i+1))ᶜ`), and is disjoint from every
  other corridor: `C k ⊆ (K (lev b+k))ᶜ` for `k ≥ i + 2` while `V ⊆ K (lev b + i + 2) ⊆ K (lev b + k)`,
  and `C k ⊆ interior (K (lev b+k+2)) ⊆ K (lev b + i + 1)` for `k ≤ i - 1`;
* `escape`: `C i ⊆ (K (lev b + i))ᶜ` and `(K i)` covers `M`, so a compact set lies in some `K m` and
  hence meets only the corridors of levels with `lev b + i ≤ m`.

This is the missing brick `exists_corridorChain_canals_of_spineData` of the routing design; it is the
input of `twoLanes_of_corridorChain` (`CompressionTube/twoLanes_of_corridorChain.lean`), and it is
independent of the two-lane recursion. -/
theorem corridorChain_of_spine {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    {B : Set M} {W : B → Set M} {D : B → ℕ → Set M} {K : ℕ → Set M} {lev : B → ℕ}
    {q : B → ℕ → M} {γ : B → ℕ → ℝ → M}
    (hKc : ∀ i, IsCompact (K i)) (hKsub : ∀ i, K i ⊆ interior (K (i + 1)))
    (hKcov : (⋃ i, K i) = (Set.univ : Set M))
    (hWo : ∀ b, IsOpen (W b)) (hWpc : ∀ b, IsPreconnected (W b))
    (hDsub : ∀ b i, D b i ⊆ W b)
    (hspine : SpineData K B lev q γ)
    (htail : ∀ (b : B) (i : ℕ), lev b ≤ i →
      (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ D b i)
    (hqlev : ∀ b : B, q b (lev b) = (b : M)) :
    ∀ b : B, Nonempty (CorridorChain (b : M) (W b)) := by
  intro b
  classical
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  have hKmono : Monotone K := monotone_K K hKsub
  have hKmono1 : ∀ i, K i ⊆ K (i + 1) := fun i => (hKsub i).trans interior_subset
  have hA_sub : ∀ i, γ b (lev b + i) '' Set.Icc (0:ℝ) 1 ⊆
      (interior (K (lev b + i + 2)) \ K (lev b + i)) ∩ W b := by
    intro i x hx
    obtain ⟨t, ht, rfl⟩ := hx
    have hl : lev b ≤ lev b + i := le_add_right le_rfl
    refine ⟨⟨hspine.image_sub b (lev b + i) hl t ht, ?_⟩, ?_⟩
    · intro hc
      exact Set.disjoint_left.mp (hspine.disjoint_K b (lev b + i) hl) ⟨t, ht, rfl⟩ hc
    · exact hDsub b (lev b + i) (htail b (lev b + i) hl
        (Set.mem_iUnion.mpr ⟨⟨lev b + i, le_rfl⟩, ⟨t, ht, rfl⟩⟩))
  have hA_pre : ∀ i, IsPreconnected (γ b (lev b + i) '' Set.Icc (0:ℝ) 1) :=
    fun i => isPreconnected_Icc.image _
      (hspine.cont b (lev b + i) (le_add_right le_rfl)).continuousOn
  have hA_start : ∀ i, q b (lev b + i) ∈ γ b (lev b + i) '' Set.Icc (0:ℝ) 1 :=
    fun i => ⟨0, Set.left_mem_Icc.mpr zero_le_one,
      (hspine.ends b (lev b + i) (le_add_right le_rfl)).1⟩
  have hA_end : ∀ i, q b (lev b + i + 1) ∈ γ b (lev b + i) '' Set.Icc (0:ℝ) 1 :=
    fun i => ⟨1, Set.right_mem_Icc.mpr zero_le_one,
      (hspine.ends b (lev b + i) (le_add_right le_rfl)).2⟩
  have hA_C : ∀ i, γ b (lev b + i) '' Set.Icc (0:ℝ) 1 ⊆
      connectedComponentIn
        ((interior (K (lev b + i + 2)) \ K (lev b + i)) ∩ W b) (q b (lev b + i)) :=
    fun i => IsPreconnected.subset_connectedComponentIn (hA_pre i) (hA_start i) (hA_sub i)
  have hesc : ∀ K' : Set M, IsCompact K' → ∃ I, ∀ i, I ≤ i →
      Disjoint (connectedComponentIn
        ((interior (K (lev b + i + 2)) \ K (lev b + i)) ∩ W b) (q b (lev b + i))) K' := by
    intro K' hK'
    obtain ⟨N, hN⟩ := Work.Noncompact.Routing.exists_avoid_level hKmono1 hKsub hKcov hK'
    refine ⟨N, fun i hi => Set.disjoint_left.mpr fun x hxC hxK => ?_⟩
    have hxK' : x ∈ (K (lev b + i))ᶜ := (connectedComponentIn_subset _ _ hxC).1.2
    exact hxK' (hKmono (by omega) (hN hxK))
  refine ⟨
    { Q := fun i => q b (lev b + i)
      C := fun i => connectedComponentIn
        ((interior (K (lev b + i + 2)) \ K (lev b + i)) ∩ W b) (q b (lev b + i))
      base := by simpa using hqlev b
      isOpen_C := fun i =>
        ((isOpen_interior.sdiff (hKc _).isClosed).inter (hWo b)).connectedComponentIn
      isPreconnected_C := fun _ => isPreconnected_connectedComponentIn
      subset_W := fun i => (connectedComponentIn_subset _ _).trans Set.inter_subset_right
      mem_Q := fun i => hA_C i (hA_start i)
      mem_Q_succ := fun i => by
        have h := hA_C i (hA_end i)
        rwa [Nat.add_assoc] at h
      disjoint := fun i j hij => by
        have hcases : i + 2 ≤ j ∨ j + 2 ≤ i := by
          rcases lt_or_ge i j with hlt | hge
          · left
            have hd : Nat.dist i j = j - i := Nat.dist_eq_sub_of_le (le_of_lt hlt)
            omega
          · right
            have hd : Nat.dist i j = i - j := Nat.dist_eq_sub_of_le_right hge
            omega
        rcases hcases with h2 | h2
        · refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
          have h1 : x ∈ interior (K (lev b + i + 2)) :=
            ((connectedComponentIn_subset _ _) hx1).1.1
          have h2' : x ∈ (K (lev b + j))ᶜ :=
            (connectedComponentIn_subset _ _ hx2).1.2
          exact h2' (hKmono (by omega) (interior_subset h1))
        · refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
          have h1 : x ∈ interior (K (lev b + j + 2)) :=
            ((connectedComponentIn_subset _ _) hx2).1.1
          have h2' : x ∈ (K (lev b + i))ᶜ :=
            (connectedComponentIn_subset _ _ hx1).1.2
          exact h2' (hKmono (by omega) (interior_subset h1))
      neck := fun i => by
        refine ⟨interior (K (lev b + i + 2)) \ K (lev b + i + 1),
          isOpen_interior.sdiff (hKc _).isClosed, ?_, ?_, ?_⟩
        · exact hspine.q_shell b (lev b + i + 1) (by omega)
        · intro x hx
          exact ⟨(connectedComponentIn_subset _ _ hx.1).1.1,
            (connectedComponentIn_subset _ _ hx.2).1.2⟩
        · intro k hk1 hk2
          rcases lt_or_gt_of_ne hk1 with hlt | hgt
          · refine Set.disjoint_left.mpr fun x hxV hxC => ?_
            have hle : lev b + k + 2 ≤ lev b + i + 1 := by omega
            have hxK : x ∈ K (lev b + i + 1) :=
              hKmono hle (interior_subset ((connectedComponentIn_subset _ _ hxC).1.1))
            exact hxV.2 hxK
          · refine Set.disjoint_left.mpr fun x hxV hxC => ?_
            have hk : lev b + i + 2 ≤ lev b + k := by omega
            have hxK : x ∈ (K (lev b + k))ᶜ :=
              (connectedComponentIn_subset _ _ hxC).1.2
            exact hxK (hKmono hk (interior_subset hxV.1))
      escape := hesc }⟩

end Work.Noncompact.CompressionTube
