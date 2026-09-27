import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_pocketFree
import Submission.Work.Noncompact.CompressionTube.preconnected_open_cover
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite

/-!
# The pocket-free collar, in the form the spine recursion consumes

This is `Work.Noncompact.CompressionTube.exists_collar_pocketFree_of_tubes` with its conclusion
re-cut: the exposed open set is `U` itself (not `U ∩ (interior B \ A)`), and the *whole* `U` is
required to avoid `A` (`U ⊆ Aᶜ`) and `L` (`Disjoint U L`).  Those two facts hold verbatim for the
`L`, `U` built in the proof of the original lemma (`L = B ∩ Uᶜ`, `U = ⋃ p ∈ sf, N p` with
`A ∩ closure (N p) = ∅`); this file records them under a name that the level step of the spine
recursion can use.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Work.Noncompact.CompressionTube

open Set Topology
theorem exists_collar_pocketFree_open {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {A B : Set M} (hAc : IsCompact A) (hBc : IsClosed B) (hBcpt : IsCompact B)
    (hAB : A ⊆ interior B)
    (hApf : ∀ x : M, x ∉ A → ¬ IsCompact (closure (connectedComponentIn (Aᶜ) x)))
    (hBpf : ∀ x : M, x ∉ B → ¬ IsCompact (closure (connectedComponentIn (Bᶜ) x)))
    {S : Set M} (hSfin : S.Finite) (hSA : Disjoint S A)
    {w : M} (hw : w ∈ interior B \ A) :
    ∃ (L U : Set M), IsClosed L ∧ A ⊆ interior L ∧ L ⊆ interior B ∧ Disjoint L S ∧
      (∀ x : M, x ∈ Lᶜ → ¬ IsCompact (closure (connectedComponentIn (Lᶜ) x))) ∧
      IsOpen U ∧ w ∈ U ∧ S ⊆ U ∧ U ⊆ Aᶜ ∧ Disjoint U L ∧
      (∀ z ∈ frontier L, ∃ (x : M) (b : Work.Whitney.PathTools.ChartBall n M Set.univ x),
        z ∈ b.K ∧ b.c.symm '' Metric.ball (b.c x) b.ρ ⊆ U) := by
  classical
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
  -- the "escape paths"
  have hTfin : (S ∪ {w}).Finite := hSfin.union (Set.finite_singleton w)
  have hTA : Disjoint (S ∪ {w}) A := by
    rw [Set.disjoint_left]
    intro x hx hxA
    rcases hx with hx | hx
    · exact (Set.disjoint_left.mp hSA hx) hxA
    · rw [Set.mem_singleton_iff] at hx; rw [hx] at hxA; exact hw.2 hxA
  have hex : ∀ s : M, s ∈ S ∪ {w} → ∃ γ : ℝ → M, Continuous γ ∧ γ 0 = s ∧
      γ '' Set.Icc (0:ℝ) 1 ⊆ Aᶜ ∧ (γ '' Set.Icc (0:ℝ) 1 ∩ Bᶜ).Nonempty := by
    intro s hs
    have hsA : s ∉ A := fun h => (Set.disjoint_left.mp hTA hs) h
    have hsD : s ∈ connectedComponentIn (Aᶜ) s := mem_connectedComponentIn hsA
    have hnotsub : ¬ connectedComponentIn (Aᶜ) s ⊆ B := by
      intro hsub
      exact hApf s hsA (hBcpt.of_isClosed_subset isClosed_closure (closure_minimal hsub hBc))
    obtain ⟨y, hyD, hyB⟩ := Set.not_subset.mp hnotsub
    have hDopen : IsOpen (connectedComponentIn (Aᶜ) s) :=
      hAc.isClosed.isOpen_compl.connectedComponentIn
    by_cases hys : y = s
    · refine ⟨fun _ => s, continuous_const, rfl, ?_, ?_⟩
      · intro z hz
        obtain ⟨t, _, rfl⟩ := hz
        exact hsA
      · exact ⟨s, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, hys ▸ hyB⟩
    · have hpath : IsPathConnected (connectedComponentIn (Aᶜ) s) :=
        hDopen.isConnected_iff_isPathConnected.mp
          ⟨⟨s, hsD⟩, isPreconnected_connectedComponentIn⟩
      obtain ⟨γ, hc, -, h0, h1, himg⟩ := Work.Whitney.PathTools.exists_arc_of_isPathConnected
        (n := n) hDopen hpath hsD hyD (fun h => hys h.symm)
      exact ⟨γ, hc, h0, fun z hz => by
          obtain ⟨t, ht, rfl⟩ := hz
          exact connectedComponentIn_subset _ _ (himg t ht),
        ⟨y, h1 ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, hyB⟩⟩
  -- totalise the choice of the escape paths
  have hexT : ∀ s : M, ∃ γ : ℝ → M, Continuous γ ∧ γ 0 = s ∧
      (s ∈ S ∪ {w} → γ '' Set.Icc (0:ℝ) 1 ⊆ Aᶜ ∧ (γ '' Set.Icc (0:ℝ) 1 ∩ Bᶜ).Nonempty) := by
    intro s
    by_cases hs : s ∈ S ∪ {w}
    · obtain ⟨γ, h1, h2, h3, h4⟩ := hex s hs
      exact ⟨γ, h1, h2, fun _ => ⟨h3, h4⟩⟩
    · exact ⟨fun _ => s, continuous_const, rfl, fun h => absurd h hs⟩
  choose Γ hΓc hΓ0 hΓ using hexT
  -- the compact set covered by the collar's complement
  have hKc : IsCompact (frontier B ∪
      ⋃ s ∈ (S ∪ {w}), Γ s '' Set.Icc (0:ℝ) 1) := by
    refine IsCompact.union
      (hBcpt.of_isClosed_subset isClosed_frontier
        (frontier_subset_closure.trans (le_of_eq hBc.closure_eq))) ?_
    exact hTfin.isCompact_biUnion fun s hs => isCompact_Icc.image (hΓc s)
  have hKA : Disjoint (frontier B ∪ ⋃ s ∈ (S ∪ {w}), Γ s '' Set.Icc (0:ℝ) 1) A := by
    rw [Set.disjoint_left]
    intro x hx hxA
    rcases hx with hx | hx
    · have hfr : x ∈ frontier B := hx
      rw [hBc.frontier_eq] at hfr
      exact hfr.2 (hAB hxA)
    · obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
      exact ((hΓ s hs).1 hxs) hxA
  -- the preconnected open cover
  obtain ⟨N, sf, Bb, hNeq, hNo, hNp, hNcov, hNZ, hNK⟩ :=
    exists_preconnected_open_cover (n := n)
      (K := frontier B ∪ ⋃ s ∈ (S ∪ {w}), Γ s '' Set.Icc (0:ℝ) 1) (Z := A)
      hKc hAc.isClosed hKA
  -- the collar and its complementary open set
  have hUo : IsOpen (⋃ p ∈ sf, N p) :=
    isOpen_iUnion fun p => isOpen_iUnion fun _ => hNo p
  have hfrU : frontier B ⊆ ⋃ p ∈ sf, N p := fun x hx => hNcov (Or.inl hx)
  have hAU : Disjoint A (closure (⋃ p ∈ sf, N p)) := by
    rw [Set.disjoint_left]
    intro z hzA hzcl
    have hclosed : IsClosed (⋃ p ∈ sf, closure (N p)) :=
      sf.finite_toSet.isClosed_biUnion fun p _ => isClosed_closure
    have hsub : (⋃ p ∈ sf, N p) ⊆ ⋃ p ∈ sf, closure (N p) := by
      intro z hz
      obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
      exact Set.mem_iUnion₂.mpr ⟨p, hp, subset_closure hzp⟩
    have hz' : z ∈ ⋃ p ∈ sf, closure (N p) := closure_minimal hsub hclosed hzcl
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz'
    exact (Set.disjoint_left.mp (hNZ p)) hzA hzp
  have hUcomp : ∀ x : M, x ∈ ⋃ p ∈ sf, N p →
      ∃ y ∈ connectedComponentIn (⋃ p ∈ sf, N p) x, y ∉ B := by
    intro x hx
    obtain ⟨p, hps, hxp⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨k, hkN, hkK⟩ := hNK p hps
    have hNsub : N p ⊆ ⋃ p' ∈ sf, N p' :=
      fun z hz => Set.mem_iUnion₂.mpr ⟨p, hps, hz⟩
    have hcomp : N p ⊆ connectedComponentIn (⋃ p' ∈ sf, N p') x :=
      (hNp p).subset_connectedComponentIn hxp hNsub
    rcases hkK with hkfr | hkarc
    · have hkfr' : k ∈ B ∧ k ∉ interior B := by
        rw [hBc.frontier_eq] at hkfr; exact hkfr
      have hkcl : k ∈ closure Bᶜ := by rw [closure_compl]; exact hkfr'.2
      obtain ⟨y, hyN, hyB⟩ := mem_closure_iff_nhds.mp hkcl (N p) ((hNo p).mem_nhds hkN)
      exact ⟨y, hcomp hyN, hyB⟩
    · obtain ⟨s, hsT, hks⟩ := Set.mem_iUnion₂.mp hkarc
      have harcU : Γ s '' Set.Icc (0:ℝ) 1 ⊆ ⋃ p' ∈ sf, N p' := fun z hz =>
        hNcov (Or.inr (Set.mem_iUnion₂.mpr ⟨s, hsT, hz⟩))
      have harcpc : IsPreconnected (Γ s '' Set.Icc (0:ℝ) 1) :=
        isPreconnected_Icc.image _ (hΓc s).continuousOn
      have hunion : IsPreconnected (N p ∪ Γ s '' Set.Icc (0:ℝ) 1) :=
        IsPreconnected.union' ⟨k, hkN, hks⟩ (hNp p) harcpc
      have hsub : N p ∪ Γ s '' Set.Icc (0:ℝ) 1 ⊆
          connectedComponentIn (⋃ p' ∈ sf, N p') x :=
        hunion.subset_connectedComponentIn (Or.inl hxp) (Set.union_subset hNsub harcU)
      obtain ⟨y, hyarc, hyB⟩ := (hΓ s hsT).2
      exact ⟨y, hsub (Or.inr hyarc), hyB⟩
  -- the collar
  obtain ⟨hLc, hAL, hLB, hLU, hLpf⟩ :=
    isClosed_and_pocketFree_inter_compl (A := A) (B := B) (U := ⋃ p ∈ sf, N p)
      hBc hUo hfrU hAB hAU hBpf hUcomp
  -- the prescribed points lie in the complement
  have hSU : S ⊆ ⋃ p ∈ sf, N p := by
    intro s hs
    refine hNcov (Or.inr (Set.mem_iUnion₂.mpr ⟨s, Or.inl hs, ?_⟩))
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, hΓ0 s⟩
  have hwU : w ∈ ⋃ p ∈ sf, N p := by
    refine hNcov (Or.inr (Set.mem_iUnion₂.mpr ⟨w, Or.inr rfl, ?_⟩))
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, hΓ0 w⟩
  have hLsubint : B ∩ (⋃ p ∈ sf, N p)ᶜ ⊆ interior B := hLB
  have hpiece : ∀ z ∈ frontier (B ∩ (⋃ p ∈ sf, N p)ᶜ),
      ∃ (x : M) (b : Work.Whitney.PathTools.ChartBall n M Aᶜ x),
        z ∈ b.K ∧ b.c.symm '' Metric.ball (b.c x) b.ρ ⊆ ⋃ p ∈ sf, N p := by
    intro z hz
    -- `z ∉ interior L`, so `z ∈ closure (Lᶜ)`, and `z ∈ interior B`; hence `z ∈ closure U`
    have hz2 : z ∈ (B ∩ (⋃ p ∈ sf, N p)ᶜ) \ interior (B ∩ (⋃ p ∈ sf, N p)ᶜ) := by
      rw [← (hBc.inter hUo.isClosed_compl).frontier_eq]
      exact hz
    have hzcl : z ∈ closure (B ∩ (⋃ p ∈ sf, N p)ᶜ)ᶜ := by
      rw [closure_compl]
      exact hz2.2
    rw [Set.compl_inter, compl_compl] at hzcl
    have hzB : z ∈ interior B := hLsubint hz2.1
    have hznotBc : z ∉ closure Bᶜ := by
      intro hcon
      have : interior B ∈ 𝓝 z := isOpen_interior.mem_nhds hzB
      obtain ⟨w', hw'mem, hw'B⟩ := (mem_closure_iff_nhds.mp hcon) (interior B) this
      exact hw'B (interior_subset hw'mem)
    have hzU : z ∈ closure (⋃ p ∈ sf, N p) := by
      rw [closure_union] at hzcl
      rcases hzcl with h | h
      · exact absurd h hznotBc
      · exact h
    rw [show (⋃ p ∈ sf, N p) = (⋃ p ∈ (sf : Set _), N p) from rfl] at hzU
    rw [(sf.finite_toSet).closure_biUnion N] at hzU
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hzU
    refine ⟨p, Bb p, ?_, ?_⟩
    · refine closure_minimal ?_ (Bb p).isClosed_K hzp
      exact (hNeq p) ▸ Work.Whitney.PathTools.ChartBall.ballImage_subset_K (Bb p)
    · intro x hx
      refine Set.mem_iUnion₂.mpr ⟨p, hp, ?_⟩
      rw [hNeq p]
      exact hx
  have hpieceU : ∀ z ∈ frontier (B ∩ (⋃ p ∈ sf, N p)ᶜ),
      ∃ (x : M) (b : Work.Whitney.PathTools.ChartBall n M Set.univ x),
        z ∈ b.K ∧ b.c.symm '' Metric.ball (b.c x) b.ρ ⊆ ⋃ p ∈ sf, N p := by
    intro z hz
    obtain ⟨x, b, hbK, hbU⟩ := hpiece z hz
    exact ⟨x, ⟨b.c, b.ρ, b.hρ, b.hz, b.hclosed, fun v _ => Set.mem_univ v⟩, hbK, hbU⟩
  refine ⟨B ∩ (⋃ p ∈ sf, N p)ᶜ, ⋃ p ∈ sf, N p, hLc, hAL, hLB, ?_, hLpf, hUo, hwU, hSU, ?_, ?_, hpieceU⟩
  · rw [Set.disjoint_left]
    intro z hzL hzS
    exact hzL.2 (hSU hzS)
  · intro z hz
    exact fun hzA => Set.disjoint_left.mp hAU hzA (subset_closure hz)
  · rw [Set.disjoint_left]
    intro z hzU hzL
    exact hzL.2 hzU

end Work.Noncompact.CompressionTube
