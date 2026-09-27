import Mathlib
import Submission.Work.Noncompact.CompressionTube.LineBuild.spines_with_arcs
import Submission.Work.Noncompact.CompressionTube.PocketDefs
import Submission.Work.Noncompact.CompressionTube.spine_recursion_from_routing

/-!
# Nested canals to infinity through a locally finite set

`Work.Noncompact.CompressionTube.exists_nested_canals`: in a connected non-compact `n`-manifold
(`n ≥ 2`), through a locally finite set `B ⊆ M` there is

* a compact exhaustion `K` of `M` (`K 0 = ∅`, `K i ⊆ interior (K (i+1))`, `⋃ K = M`),
* for each `b ∈ B` an open preconnected "canal" `W b ∋ b`, the canals being pairwise disjoint and
  locally finite,
* for each `b` a decreasing sequence `D b i` of open preconnected nonempty sets with
  `D b 0 = W b`, `D b (i+1) ⊆ D b i` and `D b i ⊆ (K i)ᶜ`,

i.e. an *escaping chain of regions* inside each canal.  The regions are the components of
`W b \ K i` that contain the spine's tail at level `i`; the containment `D b i ⊆ (K i)ᶜ` is what
makes the pieces of a line routed in these regions avoid every compact set.

The proof assembles: the pocket-free exhaustion,
the shell-by-shell routing `spine_recursion_from_routing` (producing `SpineData`),
`exists_disjoint_spines_with_arcs` (the spines, *with* the containment of the routing arcs, needed
to know that a point of the spine's tail lies in the canal), and the canal construction of
`Routing/canals_of_spines_clean`, re-done here so that the canals are known to contain the spines.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology

variable {M : Type*} [TopologicalSpace M]

section Aux

/-- A set meeting every compact set in a finite set is countable, in a `σ`-compact space. -/
private lemma nc_countable_of_finite_inter_compact [LocallyCompactSpace M]
    [SigmaCompactSpace M] {B : Set M}
    (hB : ∀ K : Set M, IsCompact K → (B ∩ K).Finite) : B.Countable := by
  let E : CompactExhaustion M := CompactExhaustion.choice M
  have hBuniv : B = ⋃ i, B ∩ E i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (E.iUnion_eq ▸ mem_univ x)
      exact mem_iUnion.mpr ⟨i, hx, hi⟩
    · intro hx
      obtain ⟨i, hx, -⟩ := mem_iUnion.mp hx
      exact hx
  rw [hBuniv]
  exact countable_iUnion fun i => (hB (E i) (E.isCompact i)).countable

/-- A compact exhaustion which is strictly nested through the interiors is monotone. -/
private lemma nc_exhaustion_mono {K : ℕ → Set M}
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1))) : Monotone K := by
  intro i j hij
  induction hij with
  | refl => exact subset_rfl
  | step _ ih => exact subset_trans ih (subset_trans (hKsub _) interior_subset)

/-- Every compact set is contained in some level of a monotone exhaustion. -/
private lemma nc_exists_subset_of_mono_exhaust {K : ℕ → Set M}
    (hKmono : Monotone K) (hKint : ∀ i, K i ⊆ interior (K (i + 1)))
    (hKcov : (⋃ i, K i) = Set.univ) {C : Set M} (hC : IsCompact C) : ∃ N, C ⊆ K N := by
  classical
  have hopen : C ⊆ ⋃ i, interior (K (i + 1)) := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (show x ∈ ⋃ i, K i by rw [hKcov]; trivial)
    exact Set.mem_iUnion.mpr ⟨i, hKint i hi⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun i : ℕ => interior (K (i + 1)))
    (fun i => isOpen_interior) hopen
  refine ⟨t.sup (fun i => i + 1), fun x hx => ?_⟩
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact hKmono (Finset.le_sup (f := fun i => i + 1) hit) (interior_subset hxi)

/-- **A locally finite family of pairwise disjoint closed sets has pairwise disjoint open
neighbourhoods.** -/
private lemma nc_exists_pairwiseDisjoint_isOpen_nhds {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    {ι : Type*} [Countable ι] {L : ι → Set M}
    (hclosed : ∀ j, IsClosed (L j)) (hlocfin : LocallyFinite L)
    (hdisj : Pairwise (fun j j' => Disjoint (L j) (L j'))) :
    ∃ U : ι → Set M, (∀ j, IsOpen (U j)) ∧ (∀ j, L j ⊆ U j) ∧
      Pairwise (fun j j' => Disjoint (U j) (U j')) := by
  classical
  haveI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : NormalSpace M := inferInstance
  have hSclosed : ∀ j, IsClosed (⋃ (j' : {x : ι // x ≠ j}), L j'.1) := by
    intro j
    have hlf : LocallyFinite (fun a : {x : ι // x ≠ j} => L a.1) :=
      hlocfin.comp_injOn (g := (Subtype.val : {x : ι // x ≠ j} → ι))
        (fun a _ b _ hab => Subtype.ext hab)
    exact hlf.isClosed_iUnion (fun a => hclosed a.1)
  have hSdisj : ∀ j, Disjoint (⋃ (j' : {x : ι // x ≠ j}), L j'.1) (L j) := by
    intro j
    rw [Set.disjoint_left]
    intro x hx hxL
    obtain ⟨j', hxj'⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hdisj j'.2) hxj' hxL
  have hUry : ∀ j, ∃ f : C(M, ℝ),
      (∀ x, x ∈ (⋃ (j' : {x : ι // x ≠ j}), L j'.1) → f x = 0) ∧
      (∀ x ∈ L j, f x = 1) ∧ (∀ x, f x ∈ Set.Icc (0:ℝ) 1) := by
    intro j
    obtain ⟨f, hf0, hf1, hf01⟩ :=
      exists_continuous_zero_one_of_isClosed (hSclosed j) (hclosed j) (hSdisj j)
    exact ⟨f, fun x hx => hf0 hx, hf1, hf01⟩
  choose f hf0 hf1 hf01 using hUry
  have hO : ∀ j, ∃ (O : Set M), IsOpen O ∧ L j ⊆ O ∧
      (∀ j' ≠ j, Disjoint (closure O) (L j')) := by
    intro j
    refine ⟨{x | (1/2 : ℝ) < f j x}, isOpen_lt continuous_const (f j).continuous, ?_, ?_⟩
    · intro x hx
      show (1:ℝ)/2 < f j x
      rw [hf1 j x hx]; norm_num
    · intro j' hj'
      rw [Set.disjoint_left]
      intro x hxcl hxL
      have hx' : (1/2 : ℝ) ≤ f j x :=
        closure_minimal (fun y hy => le_of_lt hy)
          (isClosed_Ici.preimage (f j).continuous) hxcl
      have h0 : f j x = 0 := hf0 j x (Set.mem_iUnion.mpr ⟨⟨j', hj'⟩, hxL⟩)
      rw [h0] at hx'
      norm_num at hx'
  choose O hOopen hOL hOcl using hO
  obtain ⟨e, he⟩ := exists_injective_nat ι
  refine ⟨fun j => O j \ (⋃ j' ∈ {j' | e j' < e j}, closure (O j')), ?_, ?_, ?_⟩
  · intro j
    refine (hOopen j).sdiff ?_
    refine (Set.finite_lt_nat (e j)).preimage (fun a _ b _ h => he h) |>.isClosed_biUnion ?_
    intro j' _
    exact isClosed_closure
  · intro j x hx
    refine ⟨hOL j hx, ?_⟩
    intro hcon
    obtain ⟨j', hj', hxcl⟩ := Set.mem_iUnion₂.mp hcon
    have hne : j ≠ j' := by rintro rfl; simp at hj'
    exact Set.disjoint_left.mp (hOcl j' j hne) hxcl hx
  · intro j j' hjj'
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases lt_trichotomy (e j) (e j') with h | h | h
    · exact hx'.2 (Set.mem_iUnion₂.mpr ⟨j, h, subset_closure hx.1⟩)
    · exact absurd (he h) hjj'
    · exact hx.2 (Set.mem_iUnion₂.mpr ⟨j', h, subset_closure hx'.1⟩)

end Aux

end Work.Noncompact.CompressionTube

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- **The tail of a spine chain above a level is connected, escapes the level, and is nonempty.**

For `SpineData` arcs `γ b j` the union of the arcs from level `i` on is connected (consecutive arcs
share the junction points `q b (j+1)`), is contained in `(K i)ᶜ` (each arc at level `j ≥ i` avoids
`K j ⊇ K i`) and contains the point `q b i`. -/
theorem spine_tail {n : ℕ} {M : Type*} [TopologicalSpace M]
    (K : ℕ → Set M) (hKmono : Monotone K) (B : Set M) (lev : B → ℕ) (q : B → ℕ → M)
    (γ : B → ℕ → ℝ → M) (h : SpineData K B lev q γ) (b : B) (i : ℕ) (hi : lev b ≤ i) :
    IsPreconnected (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ∧
      (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ (K i)ᶜ ∧
      q b i ∈ (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) := by
  classical
  set T : Set M := ⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1 with hT
  have hpre : IsPreconnected T := by
    -- index the tail by `m ↦ i + m`
    set H : ℕ → Set M := fun m => γ b (i + m) '' Set.Icc (0:ℝ) 1 with hH
    have hHpre : ∀ m : ℕ, IsPreconnected (H m) := fun m =>
      isPreconnected_Icc.image _ (h.cont b (i + m) (by omega)).continuousOn
    have hHne : ∀ m : ℕ, (H m ∩ H (m + 1)).Nonempty := by
      intro m
      refine ⟨q b (i + m + 1), ?_, ?_⟩
      · exact ⟨1, Set.right_mem_Icc.mpr zero_le_one, (h.ends b (i + m) (by omega)).2⟩
      · exact ⟨0, Set.left_mem_Icc.mpr zero_le_one,
          (h.ends b (i + m + 1) (by omega)).1⟩
    have hchain : ∀ m m' : ℕ,
        Relation.ReflTransGen (fun a c => (H a ∩ H c).Nonempty) m m' := by
      have hup : ∀ d m : ℕ, Relation.ReflTransGen (fun a c => (H a ∩ H c).Nonempty) m (m + d) := by
        intro d
        induction d with
        | zero => intro m; simpa using Relation.ReflTransGen.refl
        | succ d ih =>
            intro m
            have h1 : m + (d + 1) = (m + d) + 1 := by omega
            rw [h1]
            exact (ih m).tail (hHne (m + d))
      have hdown : ∀ d m : ℕ, Relation.ReflTransGen (fun a c => (H a ∩ H c).Nonempty) (m + d) m := by
        intro d
        induction d with
        | zero => intro m; simpa using Relation.ReflTransGen.refl
        | succ d ih =>
            intro m
            have h1 : m + (d + 1) = (m + 1) + d := by omega
            rw [h1]
            refine (ih (m + 1)).tail ?_
            exact ⟨(hHne m).choose, (hHne m).choose_spec.2, (hHne m).choose_spec.1⟩
      intro m m'
      rcases le_total m m' with hle | hle
      · have h1 : m' = m + (m' - m) := (Nat.add_sub_cancel' hle).symm
        rw [h1]; exact hup (m' - m) m
      · have h1 : m = m' + (m - m') := (Nat.add_sub_cancel' hle).symm
        rw [h1]; exact hdown (m - m') m'
    have hbig : IsPreconnected (⋃ m : ℕ, H m) :=
      IsPreconnected.iUnion_of_reflTransGen hHpre (fun m m' => hchain m m')
    have heq : T = ⋃ m : ℕ, H m := by
      rw [hT, hH]
      ext x
      constructor
      · intro hx
        obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨(j : ℕ) - i, by
          rw [Nat.add_sub_cancel' j.2]; exact hx⟩
      · intro hx
        obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨⟨i + m, by omega⟩, by simpa using hx⟩
    rw [heq]; exact hbig
  have hsub : T ⊆ (K i)ᶜ := by
    rw [hT]
    rintro x hx hxK
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (h.disjoint_K b (j : ℕ) (le_trans hi j.2)) hxj
      (hKmono j.2 hxK)
  have hmem : q b i ∈ T := by
    rw [hT]
    exact Set.mem_iUnion.mpr ⟨⟨i, le_rfl⟩, 0, Set.left_mem_Icc.mpr zero_le_one,
      (h.ends b i hi).1⟩
  exact ⟨hpre, hsub, hmem⟩

end Work.Noncompact.CompressionTube

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- Monotonicity of `connectedComponentIn` in the ambient set. -/
private lemma nc_ccIn_mono {M : Type*} [TopologicalSpace M] {F F' : Set M} (h : F ⊆ F') (x : M) :
    connectedComponentIn F x ⊆ connectedComponentIn F' x := by
  by_cases hx : x ∈ F
  · exact IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_connectedComponentIn hx) (subset_trans (connectedComponentIn_subset F x) h)
  · rw [connectedComponentIn_eq_empty (by simpa using hx)]
    exact empty_subset _

/-- **Nested canals to infinity.** -/
theorem exists_nested_canals {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] (hM : ¬ CompactSpace M)
    (B : Set M) (hB : ∀ K : Set M, IsCompact K → (B ∩ K).Finite) :
    ∃ (K : ℕ → Set M) (W : B → Set M) (D : B → ℕ → Set M)
      (lev : B → ℕ) (q : B → ℕ → M) (γ : B → ℕ → ℝ → M),
      (∀ i, IsCompact (K i)) ∧ K 0 = ∅ ∧ (∀ i, K i ⊆ interior (K (i + 1))) ∧
      (⋃ i, K i) = Set.univ ∧
      (∀ b, IsOpen (W b)) ∧ (∀ b, (b : M) ∈ W b) ∧ (∀ b, IsPreconnected (W b)) ∧
      (∀ b, D b 0 = W b) ∧
      (∀ b i, IsOpen (D b i)) ∧ (∀ b i, IsPreconnected (D b i)) ∧
      (∀ b i, (D b i).Nonempty) ∧ (∀ b i, D b (i + 1) ⊆ D b i) ∧
      (∀ b i, D b i ⊆ W b) ∧ (∀ b i, D b i ⊆ (K i)ᶜ) ∧
      (∀ b b', b ≠ b' → Disjoint (W b) (W b')) ∧
      (∀ K' : Set M, IsCompact K' → {b : B | (W b ∩ K').Nonempty}.Finite) ∧
      (∀ b i, ¬ IsCompact (closure (D b i))) ∧
      SpineData K B lev q γ ∧
      (∀ b i, lev b ≤ i →
        (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ D b i) ∧
      (∀ b, q b (lev b) = (b : M)) := by
  classical
  haveI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  -- a pocket-free compact exhaustion
  obtain ⟨K, hKc, hK0, hKsub, hKuniv, hKpf⟩ :=
    pocketFreeExhaustion_self (n := n) hn hM
  have hKmono : Monotone K := nc_exhaustion_mono hKsub
  -- the shell-by-shell routing
  obtain ⟨lev, q, γ, hdata⟩ :=
    spine_recursion_from_routing (n := n) hn hM B hB K hKc hK0 hKsub hKuniv hKpf
  -- the spines, together with the containment of the routing arcs
  obtain ⟨A, hAclosed, hApre, hAmem, hAnc, hAdisj, hAfin, hAarc⟩ :=
    exists_disjoint_spines_with_arcs (n := n) hn B hB K hKc hK0 hKsub hKuniv lev q γ hdata
  -- the family of spines is locally finite
  have hlf : LocallyFinite (fun b : B => A b) := by
    intro x
    obtain ⟨s, hsc, hsx⟩ := exists_compact_mem_nhds x
    exact ⟨s, hsx, hAfin s hsc⟩
  haveI : Countable B := (nc_countable_of_finite_inter_compact hB).to_subtype
  -- pairwise disjoint open neighbourhoods of the spines
  obtain ⟨U, hUopen, hUsub, hUdisj⟩ :=
    nc_exists_pairwiseDisjoint_isOpen_nhds (n := n) hAclosed hlf hAdisj
  -- the first level of the exhaustion met by each spine
  have hex : ∀ b : B, ∃ N : ℕ, (A b ∩ K N).Nonempty := by
    intro b
    obtain ⟨N, hN⟩ := mem_iUnion.mp (hKuniv ▸ mem_univ (b : M))
    exact ⟨N, (b : M), hAmem b, hN⟩
  have hAvoid : ∀ b : B, A b ∩ K (Nat.find (hex b) - 1) = ∅ := by
    intro b
    rw [← Set.not_nonempty_iff_eq_empty]
    have hc0 : Nat.find (hex b) ≠ 0 := by
      intro h0
      have hspec := Nat.find_spec (hex b)
      rw [h0, hK0, Set.inter_empty] at hspec
      exact hspec.ne_empty rfl
    exact Nat.find_min (hex b) (Nat.sub_one_lt hc0)
  set W : B → Set M := fun b => connectedComponentIn (U b ∩ (K (Nat.find (hex b) - 1))ᶜ) b
    with hW
  have hWsub : ∀ b, W b ⊆ U b ∩ (K (Nat.find (hex b) - 1))ᶜ := fun b => by
    rw [hW]
    exact connectedComponentIn_subset _ _
  have hWU : ∀ b, W b ⊆ U b := fun b => (hWsub b).trans (Set.inter_subset_left)
  -- the spine is contained in its canal
  have hAW : ∀ b : B, A b ⊆ W b := by
    intro b
    rw [hW]
    refine IsPreconnected.subset_connectedComponentIn (hApre b) (hAmem b) ?_
    intro x hx
    refine ⟨hUsub b hx, ?_⟩
    intro hcon
    have : x ∈ A b ∩ K (Nat.find (hex b) - 1) := ⟨hx, hcon⟩
    rw [hAvoid b] at this
    exact this
  -- openness of the canal
  have hWopen : ∀ b, IsOpen (W b) := by
    intro b
    rw [hW]
    exact ((hUopen b).inter (hKc _).isClosed.isOpen_compl).connectedComponentIn
  -- the spine is contained in its canal
  have hAW : ∀ b : B, A b ⊆ W b := by
    intro b
    rw [hW]
    refine IsPreconnected.subset_connectedComponentIn (hApre b) (hAmem b) ?_
    intro x hx
    refine ⟨hUsub b hx, ?_⟩
    intro hcon
    have hmem : x ∈ A b ∩ K (Nat.find (hex b) - 1) := ⟨hx, hcon⟩
    rw [hAvoid b] at hmem
    exact hmem
  -- the seeds of the regions: `q b i` above the level of `b`, and `b` below it
  set t : B → ℕ → M := fun b i => if lev b ≤ i then q b i else (b : M) with ht
  have ht_of_ge : ∀ b i, lev b ≤ i → t b i = q b i := fun b i hi => by
    rw [ht]; exact if_pos hi
  have ht_of_lt : ∀ b i, i < lev b → t b i = (b : M) := fun b i hi => by
    rw [ht]; exact if_neg (not_le.mpr hi)
  set D : B → ℕ → Set M := fun b i => connectedComponentIn (W b \ K i) (t b i) with hD
  -- the seed lies in the canal and avoids the level
  have htW : ∀ b i, t b i ∈ W b := by
    intro b i
    by_cases hi : lev b ≤ i
    · rw [ht_of_ge b i hi]
      exact hAW b (hAarc b i hi ⟨0, Set.left_mem_Icc.mpr zero_le_one,
        (hdata.ends b i hi).1⟩)
    · rw [ht_of_lt b i (not_le.mp hi)]
      exact hAW b (hAmem b)
  have htK : ∀ b i, t b i ∉ K i := by
    intro b i
    by_cases hi : lev b ≤ i
    · rcases lt_or_eq_of_le hi with hlt | heq
      · rw [ht_of_ge b i hi]
        exact (hdata.q_shell b i hlt).2
      · rw [ht_of_ge b i hi, ← heq, hdata.q_lev b]
        exact hdata.lev_notMem b
    · rw [ht_of_lt b i (not_le.mp hi)]
      intro hcon
      exact hdata.lev_notMem b (hKmono (le_of_lt (not_le.mp hi)) hcon)
  -- the seed of the next level stays in the region
  have ht_succ_mem : ∀ b i, t b (i + 1) ∈ D b i := by
    intro b i
    by_cases hi : lev b ≤ i
    · -- the arc at level `i` connects the two seeds and avoids `K i`
      have hilev1 : lev b ≤ i + 1 := le_trans hi (Nat.le_succ i)
      have hpre : IsPreconnected (γ b i '' Set.Icc (0:ℝ) 1) :=
        isPreconnected_Icc.image _ (hdata.cont b i hi).continuousOn
      have hstart : q b i ∈ γ b i '' Set.Icc (0:ℝ) 1 :=
        ⟨0, Set.left_mem_Icc.mpr zero_le_one, (hdata.ends b i hi).1⟩
      have hend : q b (i + 1) ∈ γ b i '' Set.Icc (0:ℝ) 1 :=
        ⟨1, Set.right_mem_Icc.mpr zero_le_one, (hdata.ends b i hi).2⟩
      have hsub : γ b i '' Set.Icc (0:ℝ) 1 ⊆ W b \ K i := by
        rintro x ⟨s, hs, rfl⟩
        exact ⟨hAW b (hAarc b i hi ⟨s, hs, rfl⟩),
          fun hcon => Set.disjoint_left.mp (hdata.disjoint_K b i hi) ⟨s, hs, rfl⟩ hcon⟩
      have hcomp := IsPreconnected.subset_connectedComponentIn hpre hstart hsub
      simp only [hD, ht_of_ge b i hi, ht_of_ge b (i + 1) hilev1]
      exact hcomp hend
    · -- below the level both seeds are `b`
      have hilt : i < lev b := not_le.mp hi
      have hilev : i + 1 ≤ lev b := hilt
      have hts : t b (i + 1) = (b : M) := by
        rcases lt_or_eq_of_le hilev with h | h
        · exact ht_of_lt b (i + 1) h
        · rw [h, ht_of_ge b (lev b) le_rfl, hdata.q_lev b]
      simp only [hD]
      simpa only [ht_of_lt b i hilt, hts] using
        mem_connectedComponentIn (F := W b \ K i) ⟨htW b i, htK b i⟩
  -- nesting of the regions
  have hDmono : ∀ b i, D b (i + 1) ⊆ D b i := by
    intro b i
    have hgoal : connectedComponentIn (W b \ K (i + 1)) (t b (i + 1)) ⊆
        connectedComponentIn (W b \ K i) (t b i) := by
      have hpre : IsPreconnected (connectedComponentIn (W b \ K (i + 1)) (t b (i + 1))) :=
        isPreconnected_connectedComponentIn
      have hsub : connectedComponentIn (W b \ K (i + 1)) (t b (i + 1)) ⊆ W b \ K i :=
        (connectedComponentIn_subset _ _).trans
          (Set.sdiff_subset_sdiff_right (hKmono (Nat.le_succ i)))
      have hmem : t b (i + 1) ∈ connectedComponentIn (W b \ K (i + 1)) (t b (i + 1)) :=
        mem_connectedComponentIn ⟨htW b (i + 1), htK b (i + 1)⟩
      have h1 : connectedComponentIn (W b \ K (i + 1)) (t b (i + 1)) ⊆
          connectedComponentIn (W b \ K i) (t b (i + 1)) :=
        IsPreconnected.subset_connectedComponentIn hpre hmem hsub
      have h2 : connectedComponentIn (W b \ K i) (t b (i + 1)) =
          connectedComponentIn (W b \ K i) (t b i) :=
        (connectedComponentIn_eq (ht_succ_mem b i)).symm
      rw [h2] at h1
      exact h1
    intro x hx
    simp only [hD] at hx ⊢
    exact hgoal hx
  refine ⟨K, W, D, lev, q, γ, hKc, hK0, hKsub, hKuniv, hWopen, fun b => ?_, fun b => ?_, ?_,
    (fun b i => ?_), (fun b i => ?_), (fun b i => ?_), hDmono, (fun b i => ?_),
    (fun b i => ?_), (fun b b' hbb' => ?_), (fun K' hK' => ?_), (fun b i => ?_),
    hdata, (fun b i hi => ?_), hdata.q_lev⟩
  · -- the base point lies in its canal
    rw [hW]
    refine mem_connectedComponentIn ⟨hUsub b (hAmem b), ?_⟩
    intro hcon
    have hmem : (b : M) ∈ A b ∩ K (Nat.find (hex b) - 1) := ⟨hAmem b, hcon⟩
    rw [hAvoid b] at hmem
    exact hmem
  · -- the canal is preconnected
    rw [hW]
    exact isPreconnected_connectedComponentIn
  · -- `D b 0 = W b`
    intro b
    have h0 : t b 0 = (b : M) := by
      by_cases h : lev b ≤ 0
      · have hlev : lev b = 0 := Nat.le_zero.mp h
        rw [ht_of_ge b 0 h, ← hlev, hdata.q_lev b]
      · exact ht_of_lt b 0 (not_le.mp h)
    have hbW : (b : M) ∈ W b := by
      rw [hW]
      refine mem_connectedComponentIn ⟨hUsub b (hAmem b), ?_⟩
      intro hcon
      have hmem : (b : M) ∈ A b ∩ K (Nat.find (hex b) - 1) := ⟨hAmem b, hcon⟩
      rw [hAvoid b] at hmem
      exact hmem
    have hWpc : IsPreconnected (W b) := by
      rw [hW]; exact isPreconnected_connectedComponentIn
    simp only [hD, hK0, Set.sdiff_empty, h0] at *
    exact Subset.antisymm (connectedComponentIn_subset _ _)
      (IsPreconnected.subset_connectedComponentIn hWpc hbW subset_rfl)
  · -- openness of the regions
    simp only [hD]
    exact ((hWopen b).sdiff (hKc i).isClosed).connectedComponentIn
  · -- preconnectedness of the regions
    simp only [hD]
    exact isPreconnected_connectedComponentIn
  · -- nonemptiness
    simp only [hD]
    exact ⟨t b i, mem_connectedComponentIn ⟨htW b i, htK b i⟩⟩
  · -- contained in the canal
    intro x hx
    simp only [hD] at hx
    exact (connectedComponentIn_subset _ _ hx).1
  · -- avoids the level
    intro x hx
    simp only [hD] at hx
    exact (connectedComponentIn_subset _ _ hx).2
  · -- disjointness of the canals
    exact Disjoint.mono (hWU b) (hWU b') (hUdisj hbb')
  · -- local finiteness of the family
    obtain ⟨N, hN⟩ := nc_exists_subset_of_mono_exhaust hKmono hKsub hKuniv hK'
    refine (hAfin (K (N + 1)) (hKc (N + 1))).subset ?_
    intro b hb
    obtain ⟨x, hxW, hxC⟩ := hb
    have hxnot : x ∉ K (Nat.find (hex b) - 1) := (hWsub b hxW).2
    have hcN : Nat.find (hex b) ≤ N := by
      by_contra hcon
      exact hxnot (hKmono (by omega) (hN hxC))
    obtain ⟨y, hyA, hyK⟩ := Nat.find_spec (hex b)
    exact ⟨y, hyA, hKmono (by omega) hyK⟩
  · -- the regions have non-compact closure (the spine's tail escapes)
    set L : ℕ := max i (lev b) with hL
    have hilev : lev b ≤ L := le_max_right i (lev b)
    -- the seed `t b i` is the left end `q b L` of the tail above level `L`
    have htq : t b i = q b L := by
      rcases le_or_gt (lev b) i with h | h
      · have hLi : L = i := by simp only [hL]; omega
        rw [ht_of_ge b i h, hLi]
      · have hLv : L = lev b := by simp only [hL]; omega
        rw [ht_of_lt b i h, hLv, hdata.q_lev b]
    have hsub : (⋃ j : {j : ℕ // L ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ D b i := by
      obtain ⟨hpre, hsubK, hmem⟩ := spine_tail (n := n) K hKmono B lev q γ hdata b L hilev
      rw [hD]
      refine IsPreconnected.subset_connectedComponentIn hpre ?_ ?_
      · rw [htq]; exact hmem
      · intro z hz
        refine ⟨?_, ?_⟩
        · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion.mp hz
          exact hAW b (hAarc b (j : ℕ) (le_trans hilev j.2) ⟨hj, hzj⟩)
        · intro hzK
          exact hsubK hz (hKmono (le_max_left i (lev b)) hzK)
    intro hcomp
    obtain ⟨N, hN⟩ := nc_exists_subset_of_mono_exhaust hKmono hKsub hKuniv hcomp
    set m : ℕ := max (max L (lev b + 1)) (N + 1) with hm
    have hLm : L ≤ m := le_trans (le_max_left L (lev b + 1)) (le_max_left (max L (lev b + 1)) (N + 1))
    have hlevlt : lev b < m := by
      have h1 : lev b + 1 ≤ m :=
        le_trans (le_max_right L (lev b + 1)) (le_max_left (max L (lev b + 1)) (N + 1))
      omega
    have hlevm : lev b ≤ m := le_trans hilev hLm
    have hmN : N ≤ m := by
      have h1 : N + 1 ≤ m := le_max_right (max L (lev b + 1)) (N + 1)
      omega
    have hmem2 : q b m ∈ (⋃ j : {j : ℕ // L ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) :=
      Set.mem_iUnion.mpr ⟨⟨m, hLm⟩, ⟨0, Set.left_mem_Icc.mpr zero_le_one,
        (hdata.ends b m hlevm).1⟩⟩
    have hqK : q b m ∉ K m := (hdata.q_shell b m hlevlt).2
    exact hqK (hKmono hmN (hN (subset_closure (hsub hmem2))))
  · -- the spine's tail above any level is contained in the region of that level
    obtain ⟨hpre, hsubK, hmem⟩ := spine_tail (n := n) K hKmono B lev q γ hdata b i hi
    rw [hD]
    refine IsPreconnected.subset_connectedComponentIn hpre ?_ ?_
    · rw [ht_of_ge b i hi]
      exact hmem
    · intro z hz
      refine ⟨?_, hsubK hz⟩
      obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion.mp hz
      exact hAW b (hAarc b (j : ℕ) (le_trans hi j.2) ⟨hj, hzj⟩)

end Work.Noncompact.CompressionTube
