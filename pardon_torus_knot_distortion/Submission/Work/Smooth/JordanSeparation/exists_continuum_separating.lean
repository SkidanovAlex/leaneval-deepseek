import Mathlib
import Submission.Work.Smooth.JordanSeparation.ComplHelpers
import Submission.Work.Smooth.JordanSeparation.componentIn_inter_componentIn
import Submission.Work.Smooth.JordanSeparation.isPreconnected_frontier_connectedComponentIn
open Set
namespace Work.Smooth.JordanSeparation
noncomputable section
open Classical

theorem isPreconnected_compl_point (x : ℂ) : IsPreconnected ({x}ᶜ : Set ℂ) := by
  have h : ({x}ᶜ : Set ℂ) = {z : ℂ | 0 < ‖z - x‖} := by
    ext z; simp [sub_ne_zero, norm_pos_iff]
  rw [h]
  have h0 : IsPreconnected {z : ℂ | (0:ℝ) < ‖z‖} := isPreconnected_lt_norm_compl 0 le_rfl
  have hcont : Continuous fun z : ℂ => z + x := continuous_id.add continuous_const
  have himg : IsPreconnected ((fun z : ℂ => z + x) '' {z : ℂ | (0:ℝ) < ‖z‖}) :=
    h0.image _ hcont.continuousOn
  have heq : (fun z : ℂ => z + x) '' {z : ℂ | (0:ℝ) < ‖z‖} = {z : ℂ | 0 < ‖z - x‖} := by
    ext z; constructor
    · rintro ⟨w, hw, rfl⟩; simpa using hw
    · intro hz; exact ⟨z - x, by simpa using hz, by ring⟩
  rwa [heq] at himg

theorem exists_compact_preconnected_between {U : Set ℂ} (hU : IsOpen U) {p q : ℂ}
    (hp : p ∈ U) (hq : q ∈ connectedComponentIn U p) :
    ∃ K : Set ℂ, K ⊆ U ∧ IsCompact K ∧ IsPreconnected K ∧ p ∈ K ∧ q ∈ K := by
  have hcomp : IsOpen (connectedComponentIn U p) := hU.connectedComponentIn
  haveI : LocallyPathConnectedSpace ↥(connectedComponentIn U p) := hcomp.locallyPathConnectedSpace
  have hpc : PreconnectedSpace ↥(connectedComponentIn U p) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponentIn
  haveI : ConnectedSpace ↥(connectedComponentIn U p) :=
    ConnectedSpace.mk (toPreconnectedSpace := hpc) ⟨⟨p, mem_connectedComponentIn hp⟩⟩
  haveI : PathConnectedSpace ↥(connectedComponentIn U p) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  let pp : ↥(connectedComponentIn U p) := ⟨p, mem_connectedComponentIn hp⟩
  let qq : ↥(connectedComponentIn U p) := ⟨q, hq⟩
  let γ : Path pp qq := PathConnectedSpace.somePath pp qq
  refine ⟨Set.range (fun t : unitInterval => ((γ t : ↥(connectedComponentIn U p)) : ℂ)),
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨t, rfl⟩; exact connectedComponentIn_subset U p (γ t).2
  · exact isCompact_range γ.continuous.subtype_val
  · exact isPreconnected_range γ.continuous.subtype_val
  · exact ⟨0, by simp [pp]⟩
  · exact ⟨1, by simp [qq]⟩

theorem Finset.exists_max_of_chain {ι : Type*} {U : ι → Set ℂ} {c : Set ι}
    (hc : IsChain (fun i j => U i ⊆ U j) c) (b : Finset ι) (hb : ∀ x ∈ b, x ∈ c)
    (hne : b.Nonempty) : ∃ i ∈ b, ∀ j ∈ b, U j ⊆ U i := by
  classical
  induction b using Finset.induction_on with
  | empty => obtain ⟨x, hx⟩ := hne; exact absurd hx (Finset.notMem_empty x)
  | insert a s ha ih =>
      rcases s.eq_empty_or_nonempty with rfl | hse
      · refine ⟨a, Finset.mem_insert_self a ∅, fun j hj => ?_⟩
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hj
        rw [hj]
      · obtain ⟨i, hi, hmax⟩ := ih (fun x hx => hb x (Finset.mem_insert_of_mem hx)) hse
        have haC : a ∈ c := hb a (Finset.mem_insert_self a s)
        have hiC : i ∈ c := hb i (Finset.mem_insert_of_mem hi)
        by_cases hai : a = i
        · subst hai
          refine ⟨a, Finset.mem_insert_of_mem hi, fun j hj => ?_⟩
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact subset_rfl
          · exact hmax j hj
        · rcases hc haC hiC hai with h | h
          · refine ⟨i, Finset.mem_insert_of_mem hi, fun j hj => ?_⟩
            rw [Finset.mem_insert] at hj
            rcases hj with rfl | hj
            · exact h
            · exact hmax j hj
          · refine ⟨a, Finset.mem_insert_self a s, fun j hj => ?_⟩
            rw [Finset.mem_insert] at hj
            rcases hj with rfl | hj
            · exact subset_rfl
            · exact (hmax j hj).trans h

theorem IsCompact.exists_subset_of_isChain {ι : Type*} {U : ι → Set ℂ} {c : Set ι}
    (hc : IsChain (fun i j => U i ⊆ U j) c) {K : Set ℂ} (hKo : ∀ i ∈ c, IsOpen (U i))
    (hKc : IsCompact K) (hKne : K.Nonempty) (hsub : K ⊆ ⋃ i ∈ c, U i) :
    ∃ i ∈ c, K ⊆ U i := by
  classical
  have hsub' : K ⊆ ⋃ i : {i // i ∈ c}, U i.1 := by simpa using hsub
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun i : {i // i ∈ c} => U i.1)
    (fun i => hKo i.1 i.2) hsub'
  have htne : t.Nonempty := by
    rcases t.eq_empty_or_nonempty with he | h
    · rw [he] at ht
      simp only [Finset.notMem_empty, iUnion_false, iUnion_empty] at ht
      obtain ⟨x, hx⟩ := hKne
      exact (ht hx).elim
    · exact h
  have hchain : IsChain (fun i j : {i // i ∈ c} => U i.1 ⊆ U j.1) Set.univ := by
    intro i _ j _ hij
    exact hc i.2 j.2 (fun h => hij (Subtype.ext h))
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_of_chain hchain t (by simp) htne
  refine ⟨i.1, i.2, fun z hz => ?_⟩
  rcases mem_iUnion₂.mp (ht hz) with ⟨j, hj, hzj⟩
  exact hmax j hj hzj

theorem sInter_sep {c : Set (Set ℂ)} (hchain_c : IsChain (fun x y : Set ℂ => x ⊆ y) c)
    (hclosed : ∀ s ∈ c, IsClosed s) {p q : ℂ}
    (hpc : ∀ s ∈ c, p ∉ s) (hsep : ∀ s ∈ c, q ∉ connectedComponentIn sᶜ p)
    (hne : c.Nonempty) : q ∉ connectedComponentIn (⋂₀ c)ᶜ p := by
  intro hcon
  obtain ⟨s0, hs0⟩ := hne
  have hopen : IsOpen (⋂₀ c)ᶜ := (isClosed_sInter hclosed).isOpen_compl
  have hpU : p ∈ (⋂₀ c)ᶜ := fun h => hpc s0 hs0 (sInter_subset_of_mem hs0 h)
  obtain ⟨K, hKU, hKc, hKpre, hpK, hqK⟩ := exists_compact_preconnected_between hopen hpU hcon
  have hchain : IsChain (fun s t : Set ℂ => sᶜ ⊆ tᶜ) c := by
    intro s hs t ht hst
    rcases hchain_c hs ht hst with h | h
    · exact Or.inr (compl_subset_compl.mpr h)
    · exact Or.inl (compl_subset_compl.mpr h)
  have hsubU : K ⊆ ⋃ s ∈ c, sᶜ := fun z hz => by
    have h1 : z ∈ (⋂₀ c)ᶜ := hKU hz
    simpa using h1
  obtain ⟨s1, hs1, hKs1⟩ := IsCompact.exists_subset_of_isChain hchain
    (fun s _ => (hclosed s (by assumption)).isOpen_compl) hKc ⟨p, hpK⟩ hsubU
  exact hsep s1 hs1 (hKpre.subset_connectedComponentIn hpK hKs1 hqK)

/-! ## The frontier of a complementary domain

Let `K ⊆ ℂ` be closed, `U` a connected component of `Kᶜ`.  Then the frontier of `U` lies in `K`,
and `U` is a connected component of the open set `(frontier U)ᶜ`.  Consequently `frontier U`
separates every point of `U` from every point of the complement of `closure U`. -/

-- `isPreconnected_insert_of_mem_closure` used to be defined here, in the `Set ℂ` form.  It is now
-- imported, in the stronger form for an arbitrary topological space (which specialises to `Set ℂ`),
-- from `Submission.Work.Smooth.JordanSeparation.isPreconnected_frontier_connectedComponentIn`.  The
-- two copies had *different types*, so Lean could not merge them and refused to import both
-- chapters together; see `Submission/Work/Smooth/RepairImport/README.md`.

/-- The frontier of a connected component of the complement of a closed set `K` lies in `K`. -/
theorem frontier_connectedComponentIn_subset {K : Set ℂ} (hK : IsClosed K) (x : ℂ) :
    frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  set U : Set ℂ := connectedComponentIn Kᶜ x with hUdef
  have hUo : IsOpen U := IsOpen.connectedComponentIn hK.isOpen_compl
  intro z hz
  by_contra hzK
  have hzc : z ∈ Kᶜ := hzK
  have hzcl : z ∈ closure U := frontier_subset_closure hz
  have hznU : z ∉ U := by
    rw [hUo.frontier_eq] at hz
    exact hz.2
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hK.isOpen_compl z hzc
  obtain ⟨y, hyU, hyz⟩ := Metric.mem_closure_iff.mp hzcl (ε/2) (by linarith)
  have hyball : y ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_comm]; linarith
  have hcomp : connectedComponentIn Kᶜ y = U :=
    (connectedComponentIn_eq (by rwa [hUdef] at hyU)).symm
  have hkey : Metric.ball z ε ⊆ connectedComponentIn Kᶜ y := by
    refine IsPreconnected.subset_connectedComponentIn (convex_ball z ε).isPreconnected hyball ?_
    intro w hw
    exact hεsub hw
  have hzU : z ∈ connectedComponentIn Kᶜ y := hkey (Metric.mem_ball_self hε)
  rw [hcomp] at hzU
  exact hznU hzU

-- `compl_frontier_eq_of_isOpen` was defined here as well; its statement was the same as that of the
-- copy in `Submission.Work.Smooth.JordanSeparation.isPreconnected_frontier_connectedComponentIn`, so
-- it is now imported from that file, together with the compiler-generated `_simp_1_*` companion
-- declarations that Lean attaches to it.  The two files must have a single source for each
-- declaration they have in common in order to be importable together; see
-- `Submission/Work/Smooth/RepairImport/README.md`.

/-- **The frontier of a domain separates it from the complement of its closure.** -/
theorem notMem_connectedComponentIn_compl_frontier {U : Set ℂ} (hU : IsOpen U) {p q : ℂ}
    (hp : p ∈ U) (hq : q ∉ closure U) :
    q ∉ connectedComponentIn (frontier U)ᶜ p := by
  have hcompl : (frontier U)ᶜ = U ∪ (closure U)ᶜ := compl_frontier_eq_of_isOpen hU
  have hpV : p ∈ (frontier U)ᶜ := by rw [hcompl]; exact Or.inl hp
  have hqU : q ∉ U := fun h => hq (subset_closure h)
  have hclopen : IsClopen (Subtype.val ⁻¹' U : Set ↥((frontier U)ᶜ)) := by
    refine ⟨?_, hU.preimage continuous_subtype_val⟩
    rw [← isOpen_compl_iff]
    have hset : (Subtype.val ⁻¹' U : Set ↥((frontier U)ᶜ))ᶜ
        = Subtype.val ⁻¹' (closure U)ᶜ := by
      rw [← Set.preimage_compl]
      ext w
      simp only [mem_preimage, mem_compl_iff]
      constructor
      · intro h
        have hz : (w : ℂ) ∈ U ∪ (closure U)ᶜ := by rw [← hcompl]; exact w.2
        rcases hz with h' | h'
        · exact absurd h' h
        · exact h'
      · exact fun h h' => h (subset_closure h')
    rw [hset]
    exact isClosed_closure.isOpen_compl.preimage continuous_subtype_val
  have hsub : connectedComponentIn (frontier U)ᶜ p ⊆ U := by
    rw [connectedComponentIn_eq_image hpV]
    rintro z ⟨w, hw, rfl⟩
    exact hclopen.connectedComponent_subset (x := ⟨p, hpV⟩)
      (show (⟨p, hpV⟩ : ↥((frontier U)ᶜ)) ∈ Subtype.val ⁻¹' U from hp) hw
  exact fun h => hqU (hsub h)

/-- **A minimal closed separator is the frontier of the component of one of the two points.**

If `L` is a closed set separating `p` from `q` and minimal with this property, then `L` is exactly
the frontier of the connected component of `p` in `Lᶜ`. -/
theorem eq_frontier_of_minimal {L : Set ℂ} (hLc : IsClosed L) {p q : ℂ} (hp : p ∈ Lᶜ)
    (hqLc : q ∈ Lᶜ)
    (hsep : q ∉ connectedComponentIn Lᶜ p)
    (hmin : ∀ D ⊆ L, IsClosed D → q ∉ connectedComponentIn Dᶜ p → L ⊆ D) :
    L = frontier (connectedComponentIn Lᶜ p) := by
  set U : Set ℂ := connectedComponentIn Lᶜ p with hUdef
  have hUo : IsOpen U := IsOpen.connectedComponentIn hLc.isOpen_compl
  have hUL : U ⊆ Lᶜ := connectedComponentIn_subset Lᶜ p
  have hqclU : q ∉ closure U := by
    intro hqcl
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hLc.isOpen_compl q hqLc
    obtain ⟨y, hyU, hyq⟩ := Metric.mem_closure_iff.mp hqcl (ε/2) (by linarith)
    have hyball : y ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, dist_comm]; linarith
    have hcomp : connectedComponentIn Lᶜ y = U :=
      (connectedComponentIn_eq (by rwa [hUdef] at hyU)).symm
    have hkey : Metric.ball q ε ⊆ connectedComponentIn Lᶜ y := by
      refine IsPreconnected.subset_connectedComponentIn (convex_ball q ε).isPreconnected hyball ?_
      intro w hw
      exact hεsub hw
    have hqU : q ∈ connectedComponentIn Lᶜ y := hkey (Metric.mem_ball_self hε)
    rw [hcomp] at hqU
    exact hsep (by rwa [hUdef] at hqU)
  have hfro : frontier U ⊆ L := frontier_connectedComponentIn_subset hLc p
  have hsep' : q ∉ connectedComponentIn (frontier U)ᶜ p :=
    notMem_connectedComponentIn_compl_frontier hUo (mem_connectedComponentIn hp) hqclU
  exact Subset.antisymm (hmin (frontier U) hfro isClosed_frontier hsep') hfro

/-! ## The two-set (Janiszewski) input

`janiszewskiDisjointAux` below is the classical Janiszewski theorem for two **disjoint** compact
sets: it is the single remaining input of the argument.  Everything above and below is proved. -/

/-- **Janiszewski's theorem for two disjoint compact plane sets.**  If `A` and `B` are disjoint
compact subsets of `ℂ` and `p, q ∉ A ∪ B` lie in the same component both of `Aᶜ` and of `Bᶜ`,
then they lie in the same component of `(A ∪ B)ᶜ`. -/
theorem janiszewskiDisjointAux {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) {p q : ℂ} (hp : p ∉ A ∪ B) (hq : q ∉ A ∪ B)
    (hA' : q ∈ connectedComponentIn Aᶜ p) (hB' : q ∈ connectedComponentIn Bᶜ p) :
    q ∈ connectedComponentIn (A ∪ B)ᶜ p := by
  have hpA : p ∈ Aᶜ := fun h => hp (Or.inl h)
  have hpB : p ∈ Bᶜ := fun h => hp (Or.inr h)
  have hpre : IsPreconnected
      (connectedComponentIn Aᶜ p ∩ connectedComponentIn Bᶜ p) :=
    componentIn_inter_componentIn hA hB hAB hpA hpB
  have hpq : q ∈ connectedComponentIn Aᶜ p ∩ connectedComponentIn Bᶜ p := ⟨hA', hB'⟩
  have hsub : connectedComponentIn Aᶜ p ∩ connectedComponentIn Bᶜ p ⊆ (A ∪ B)ᶜ := by
    rintro z ⟨hz1, hz2⟩
    rw [Set.mem_compl_iff]
    rintro (h | h)
    · exact (connectedComponentIn_subset Aᶜ p hz1) h
    · exact (connectedComponentIn_subset Bᶜ p hz2) h
  exact hpre.subset_connectedComponentIn (x := p)
    ⟨mem_connectedComponentIn hpA, mem_connectedComponentIn hpB⟩ hsub hpq

/-- **Target.**  A compact subset of `ℂ` separating `p` from `q` contains a non-degenerate
preconnected subset that still separates them.

The proof is the classical one: minimise the family of closed subsets of `K` separating `p` from
`q` (Zorn, the chain condition being `sInter_sep`), obtaining `L`, and conclude from
`janiszewskiDisjointAux` that `L` cannot be written as the union of two disjoint non-empty closed
pieces — so `L` is preconnected; it is non-degenerate because a point does not separate
`isPreconnected_compl_point`. -/
theorem exists_continuum_separating {K : Set ℂ} (hK : IsCompact K) {p q : ℂ}
    (hp : p ∉ K) (hq : q ∉ K) (hsep : q ∉ connectedComponentIn Kᶜ p) :
    ∃ C : Set ℂ, C ⊆ K ∧ IsPreconnected C ∧ C.Nontrivial ∧
      q ∉ connectedComponentIn Cᶜ p := by
  set SS : Set (Set ℂ) := {L | L ⊆ K ∧ IsClosed L ∧ q ∉ connectedComponentIn Lᶜ p} with hSS
  have hKmem : K ∈ SS := ⟨subset_rfl, hK.isClosed, hsep⟩
  have hchain : ∀ c ⊆ SS, IsChain (fun x1 x2 : Set ℂ => x1 ⊆ x2) c →
      ∃ lb ∈ SS, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hch
    rcases c.eq_empty_or_nonempty with rfl | hneC
    · exact ⟨K, hKmem, by simp⟩
    · obtain ⟨s0, hs0⟩ := hneC
      have hs0SS : s0 ∈ SS := hc hs0
      exact ⟨⋂₀ c, ⟨(sInter_subset_of_mem hs0).trans hs0SS.1,
        isClosed_sInter (fun s hs => (hc hs).2.1),
        sInter_sep hch (fun s hs => (hc hs).2.1)
          (fun s hs h => hp ((hc hs).1 h)) (fun s hs => (hc hs).2.2) ⟨s0, hs0⟩⟩,
        fun s hs => sInter_subset_of_mem hs⟩
  obtain ⟨L, hLmin⟩ := zorn_superset SS hchain
  have hLK : L ⊆ K := hLmin.1.1
  have hLclosed : IsClosed L := hLmin.1.2.1
  have hLsep : q ∉ connectedComponentIn Lᶜ p := hLmin.1.2.2
  have hLpre : IsPreconnected L := by
    rw [isPreconnected_iff_subset_of_disjoint_closed]
    intro u v hu hv huv hdisj
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hnu, hnv⟩ := hc
    have hAc : IsClosed (L ∩ u) := hLclosed.inter hu
    have hBc : IsClosed (L ∩ v) := hLclosed.inter hv
    have hUnion : (L ∩ u) ∪ (L ∩ v) = L := by
      apply Subset.antisymm
      · rintro z (hz | hz) <;> exact hz.1
      · intro z hz
        rcases huv hz with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
    have hAB : Disjoint (L ∩ u) (L ∩ v) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      have hmem : z ∈ L ∩ (u ∩ v) := ⟨hz1.1, hz1.2, hz2.2⟩
      rw [hdisj] at hmem
      exact hmem
    have hAne : (L ∩ u).Nonempty := by
      obtain ⟨z, hzL, hzv⟩ := not_subset.mp hnv
      have hzu : z ∈ u := by rcases huv hzL with h | h; exacts [h, absurd h hzv]
      exact ⟨z, hzL, hzu⟩
    have hBne : (L ∩ v).Nonempty := by
      obtain ⟨z, hzL, hzu⟩ := not_subset.mp hnu
      have hzv : z ∈ v := by rcases huv hzL with h | h; exacts [absurd h hzu, h]
      exact ⟨z, hzL, hzv⟩
    have hAproper : L ∩ u ≠ L := by
      intro h
      obtain ⟨z, hzB⟩ := hBne
      have hzu : z ∈ u := (h.symm ▸ hzB.1 : z ∈ L ∩ u).2
      have hmem : z ∈ L ∩ (u ∩ v) := ⟨hzB.1, hzu, hzB.2⟩
      rw [hdisj] at hmem
      exact hmem
    have hBproper : L ∩ v ≠ L := by
      intro h
      obtain ⟨z, hzA⟩ := hAne
      have hzv : z ∈ v := (h.symm ▸ hzA.1 : z ∈ L ∩ v).2
      have hmem : z ∈ L ∩ (u ∩ v) := ⟨hzA.1, hzA.2, hzv⟩
      rw [hdisj] at hmem
      exact hmem
    have hAsep : q ∈ connectedComponentIn (L ∩ u)ᶜ p := by
      by_contra h
      exact hAproper (Subset.antisymm (fun z hz => hz.1) (hLmin.2
        ⟨fun z hz => hLK hz.1, hAc, h⟩ (fun z hz => hz.1)))
    have hBsep : q ∈ connectedComponentIn (L ∩ v)ᶜ p := by
      by_contra h
      exact hBproper (Subset.antisymm (fun z hz => hz.1) (hLmin.2
        ⟨fun z hz => hLK hz.1, hBc, h⟩ (fun z hz => hz.1)))
    have hLcompact : IsCompact L := hK.of_isClosed_subset hLclosed hLK
    have hcontra := janiszewskiDisjointAux (hLcompact.inter_right hu)
      (hLcompact.inter_right hv) hAB
      (by rw [hUnion]; exact fun h => hp (hLK h))
      (by rw [hUnion]; exact fun h => hq (hLK h)) hAsep hBsep
    have hcompl : (((L ∩ u) ∪ (L ∩ v))ᶜ : Set ℂ) = Lᶜ := by rw [hUnion]
    exact hLsep (hcompl ▸ hcontra)
  have hLne : L.Nonempty := by
    rcases L.eq_empty_or_nonempty with he | h
    · refine absurd ?_ hLsep
      rw [he]
      simpa using (isPreconnected_univ.subset_connectedComponentIn (mem_univ p)
        (subset_refl _) (mem_univ q))
    · exact h
  obtain ⟨x, hxL⟩ := hLne
  refine ⟨L, hLK, hLpre, ?_, hLsep⟩
  by_contra hnt
  rw [Set.not_nontrivial_iff] at hnt
  have hsing : L = {x} := Subset.antisymm (fun z hz => by
      simp [hnt hz hxL]) (by rintro z rfl; exact hxL)
  rw [hsing] at hLsep
  have hp' : p ∈ ({x}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => hp (hLK (h ▸ hxL))
  have hq' : q ∈ ({x}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => hq (hLK (h ▸ hxL))
  exact hLsep ((isPreconnected_compl_point x).subset_connectedComponentIn
    (x := p) hp' subset_rfl hq')

end
end Work.Smooth.JordanSeparation
