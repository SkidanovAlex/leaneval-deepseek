import Submission.Work.Whitney.PathTools.JaniszewskiTwo

/-!
# A compact totally disconnected subset of the plane does not separate it

If `K ⊆ ℝ²` is compact and totally disconnected, then `Kᶜ` is path connected.

The proof uses a minimal-separator argument (Zorn).  Suppose `K` separates two points `X, Y`.
Among all compact subsets of `K` that still separate `X` from `Y` choose a minimal one `L` under
inclusion; such an element exists because the intersection of a chain of separators is again a
separator (compactness: a path avoiding all of them would avoid finitely many complement-open sets,
and a finite subfamily of a chain has a least member).  Then `L` cannot be disconnected: writing
`L = A ∪ B` with `A, B` nonempty compact would contradict minimality of `L` through Janiszewski's
theorem for two separated compacta (`joinedIn_compl_union`).  Hence `L` is connected, and since
`L ⊆ K` is totally disconnected, `L` is a single point — but a point does not separate the plane.
-/

namespace Work.Whitney.PathTools
namespace Grid

open Set Metric Topology

noncomputable section

/-- The complement of a closed ball in a real inner product space of dimension `> 1` is path
connected. -/
theorem isPathConnected_compl_closedBall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (hE : 1 < Module.rank ℝ E) (a : E) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsPathConnected ((closedBall a ρ)ᶜ : Set E) := by
  have hI : IsPathConnected (Ioi ρ) := (convex_Ioi ρ).isPathConnected ⟨ρ + 1, by simp⟩
  have hS : IsPathConnected (sphere (0:E) 1) := isPathConnected_sphere hE 0 (by norm_num)
  have hprod : IsPathConnected ((Ioi ρ) ×ˢ (sphere (0:E) 1)) := hI.prod hS
  have hcont : Continuous (fun p : ℝ × E => a + p.1 • p.2) :=
    continuous_const.add (continuous_fst.smul continuous_snd)
  have himg : IsPathConnected ((fun p : ℝ × E => a + p.1 • p.2)
      '' ((Ioi ρ) ×ˢ (sphere (0:E) 1))) := hprod.image hcont
  have hset : (fun p : ℝ × E => a + p.1 • p.2) '' ((Ioi ρ) ×ˢ (sphere (0:E) 1))
      = (closedBall a ρ)ᶜ := by
    ext z
    constructor
    · rintro ⟨⟨s, u⟩, ⟨hs, hu⟩, rfl⟩
      simp only [mem_Ioi] at hs
      simp only [mem_sphere, dist_eq_norm, sub_zero] at hu
      simp only [mem_compl_iff, mem_closedBall, dist_eq_norm]
      have : a + s • u - a = s • u := by abel
      rw [this, norm_smul, hu, mul_one, Real.norm_of_nonneg (le_of_lt (lt_of_le_of_lt hρ hs))]
      linarith
    · intro hz
      rw [mem_compl_iff, mem_closedBall, dist_eq_norm] at hz
      have hlt : ρ < ‖z - a‖ := lt_of_not_ge hz
      have hne : ‖z - a‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt hρ hlt)
      refine ⟨(‖z - a‖, (‖z - a‖)⁻¹ • (z - a)), ⟨hlt, ?_⟩, ?_⟩
      · simp only [mem_sphere, dist_eq_norm, sub_zero]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hne]
      · simp only
        rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
        abel
  rw [hset] at himg
  exact himg

/-- A finite subset of a chain of sets has a least element. -/
theorem Finset.exists_subset_of_isChain {α : Type*} {c : Set (Set α)}
    (hc : IsChain (· ⊆ ·) c) {t : Finset (Set α)} (ht : ∀ L ∈ t, L ∈ c) (hne : t.Nonempty) :
    ∃ L ∈ t, ∀ L' ∈ t, L ⊆ L' := by
  classical
  induction t using Finset.induction_on with
  | empty => exact absurd hne (by simp)
  | insert a t ha ih =>
      rcases t.eq_empty_or_nonempty with hte | htne
      · subst hte
        exact ⟨a, Finset.mem_insert_self a ∅, fun L' hL' => by
          rcases Finset.mem_insert.mp hL' with h' | h'
          · subst h'; exact subset_rfl
          · exact absurd h' (by simp)⟩
      · obtain ⟨L₀, hL₀t, hL₀min⟩ := ih (fun L hL => ht L (Finset.mem_insert_of_mem hL)) htne
        have haC : a ∈ c := ht a (Finset.mem_insert_self a t)
        have hL₀C : L₀ ∈ c := ht L₀ (Finset.mem_insert_of_mem hL₀t)
        rcases eq_or_ne a L₀ with heq | hne'
        · subst heq
          exact ⟨a, Finset.mem_insert_of_mem hL₀t, fun L' hL' => by
            rcases Finset.mem_insert.mp hL' with h' | hL't
            · subst h'; exact subset_rfl
            · exact hL₀min L' hL't⟩
        · rcases hc haC hL₀C hne' with hsub | hsub
          · refine ⟨a, Finset.mem_insert_self a t, fun L' hL' => ?_⟩
            rcases Finset.mem_insert.mp hL' with h' | hL't
            · subst h'; exact subset_rfl
            · exact hsub.trans (hL₀min L' hL't)
          · refine ⟨L₀, Finset.mem_insert_of_mem hL₀t, fun L' hL' => ?_⟩
            rcases Finset.mem_insert.mp hL' with h' | hL't
            · subst h'; exact hsub
            · exact hL₀min L' hL't

/-- In the plane, for `m = 2`, the rank is `> 1`. -/
theorem one_lt_rank_pt : 1 < Module.rank ℝ Pt := by
  have hfin : Module.finrank ℝ Pt = 2 := by
    rw [finrank_euclideanSpace]
    simp
  rw [← Module.finrank_eq_rank']
  rw [hfin]
  norm_num

/-- The complement of a point in the plane is path connected. -/
theorem isPathConnected_compl_singleton (p : Pt) : IsPathConnected (({p} : Set Pt)ᶜ) := by
  have h := isPathConnected_compl_closedBall (E := Pt) one_lt_rank_pt p (ρ := 0) le_rfl
  rwa [Metric.closedBall_zero] at h

/-- A single point does not separate two distinct points of the plane. -/
theorem joinedIn_compl_singleton {p X Y : Pt} (hX : X ≠ p) (hY : Y ≠ p) :
    JoinedIn (({p} : Set Pt)ᶜ) X Y :=
  (isPathConnected_compl_singleton p).joinedIn X (by simpa [mem_compl_iff]) Y
    (by simpa [mem_compl_iff])

/-- **Main lemma.**  A compact totally disconnected subset of the plane does not separate. -/
theorem joinedIn_compl_of_isCompact_isTotallyDisconnected {K : Set Pt} (hK : IsCompact K)
    (htd : IsTotallyDisconnected K) {X Y : Pt} (hX : X ∉ K) (hY : Y ∉ K) :
    JoinedIn (Kᶜ) X Y := by
  classical
  by_contra hsep
  set S : Set (Set Pt) := {L | L ⊆ K ∧ IsCompact L ∧ ¬ JoinedIn (Lᶜ) X Y} with hSdef
  have hKmem : K ∈ S := ⟨subset_rfl, hK, hsep⟩
  -- Zorn: a minimal separator
  have hchaincond : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨K, hKmem, fun s hs => absurd hs (by simp)⟩
    · refine ⟨⋂₀ c, ⟨?_, ?_, ?_⟩, fun s hs => sInter_subset_of_mem hs⟩
      · obtain ⟨L₀, hL₀⟩ := hne
        exact (sInter_subset_of_mem hL₀).trans (hcS hL₀).1
      · refine hK.of_isClosed_subset ?_ ?_
        · exact isClosed_sInter (fun s hs => ((hcS hs).2.1).isClosed)
        · obtain ⟨L₀, hL₀⟩ := hne
          exact (sInter_subset_of_mem hL₀).trans (hcS hL₀).1
      · rintro ⟨γ, hγ⟩
        -- a finite subfamily already covers the path
        have hcover : range γ ⊆ ⋃ i : {L // L ∈ c}, ((i : Set Pt))ᶜ := by
          intro z hz
          obtain ⟨t, rfl⟩ := hz
          have h1 : γ t ∉ ⋂₀ c := hγ t
          rw [Set.mem_sInter] at h1
          push_neg at h1
          obtain ⟨L, hLc, hLt⟩ := h1
          exact Set.mem_iUnion.mpr ⟨⟨L, hLc⟩, hLt⟩
        obtain ⟨u, hu⟩ := (isCompact_range γ.continuous).elim_finite_subcover
          (fun i : {L // L ∈ c} => ((i : Set Pt))ᶜ)
          (fun i => ((hcS i.2).2.1).isClosed.isOpen_compl) hcover
        have hufin : ∀ L' ∈ u.image Subtype.val, L' ∈ c := by
          intro L' hL'
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hL'
          exact i.2
        rcases u.eq_empty_or_nonempty with rfl | uone
        · exfalso
          have h0 := hu ⟨(0 : unitInterval), rfl⟩
          simpa using h0
        obtain ⟨L', hL'u, hL'min⟩ := Finset.exists_subset_of_isChain hchain hufin
          (uone.image Subtype.val)
        have hsub : range γ ⊆ ((L' : Set Pt))ᶜ := by
          intro z hz
          have h1 := hu hz
          rw [Set.mem_iUnion] at h1
          obtain ⟨i, h1⟩ := h1
          rw [Set.mem_iUnion] at h1
          obtain ⟨hiu, hzi⟩ := h1
          have h2 : (i : Set Pt) ∈ u.image Subtype.val :=
            Finset.mem_image.mpr ⟨i, hiu, rfl⟩
          exact fun hzL => hzi ((hL'min (i : Set Pt) h2) hzL)
        have hL'c : L' ∈ c := hufin L' hL'u
        exact (hcS hL'c).2.2 ⟨γ, fun t => hsub ⟨t, rfl⟩⟩
  obtain ⟨L, hLmin⟩ := zorn_superset S hchaincond
  have hLmem : L ∈ S := hLmin.1
  obtain ⟨hLK, hLcomp, hLsep⟩ := hLmem
  have hLmin' : ∀ a ∈ S, a ⊆ L → L ⊆ a := hLmin.2
  -- `L` is nonempty
  have hLne : L.Nonempty := by
    rcases L.eq_empty_or_nonempty with rfl | h
    · exfalso
      refine hLsep ?_
      simpa using (convex_univ.isPathConnected ⟨X, mem_univ X⟩).joinedIn X (mem_univ X) Y (mem_univ Y)
    · exact h
  -- `L` is connected
  have hLpre : IsPreconnected L := by
    by_contra hcon
    unfold IsPreconnected at hcon
    push_neg at hcon
    obtain ⟨u, v, hu, hv, hLuv, hLu, hLv, hLuv'⟩ := hcon
    -- the two pieces
    have hAeq : L ∩ u = L ∩ vᶜ := by
      ext z; constructor
      · rintro ⟨hzL, hzu⟩
        refine ⟨hzL, ?_⟩
        intro hzv
        have : z ∈ L ∩ (u ∩ v) := ⟨hzL, hzu, hzv⟩
        rw [hLuv'] at this
        exact this
      · rintro ⟨hzL, hzv⟩
        rcases hLuv hzL with h | h
        · exact ⟨hzL, h⟩
        · exact absurd h hzv
    have hBeq : L ∩ v = L ∩ uᶜ := by
      ext z; constructor
      · rintro ⟨hzL, hzv⟩
        refine ⟨hzL, ?_⟩
        intro hzu
        have : z ∈ L ∩ (u ∩ v) := ⟨hzL, hzu, hzv⟩
        rw [hLuv'] at this
        exact this
      · rintro ⟨hzL, hzu⟩
        rcases hLuv hzL with h | h
        · exact absurd h hzu
        · exact ⟨hzL, h⟩
    have hAcpt : IsCompact (L ∩ u) := by
      rw [hAeq]
      exact hLcomp.of_isClosed_subset (hLcomp.isClosed.inter hv.isClosed_compl) inter_subset_left
    have hBcpt : IsCompact (L ∩ v) := by
      rw [hBeq]
      exact hLcomp.of_isClosed_subset (hLcomp.isClosed.inter hu.isClosed_compl) inter_subset_left
    have hAne' : (L ∩ u).Nonempty := hLu
    have hBne' : (L ∩ v).Nonempty := hLv
    have hAneK : (L ∩ u) ⊆ K := inter_subset_left.trans hLK
    have hBneK : (L ∩ v) ⊆ K := inter_subset_left.trans hLK
    -- minimality: neither piece separates
    have hAjoin : JoinedIn ((L ∩ u)ᶜ) X Y := by
      by_contra hcon2
      have : L ∩ u ∈ S := ⟨hAneK, hAcpt, hcon2⟩
      have hsub := hLmin' (L ∩ u) this inter_subset_left
      obtain ⟨z, hz⟩ := hBne'
      have hz1 : z ∈ L := hz.1
      have hz2 : z ∈ L ∩ u := hsub hz1
      have hz3 : z ∈ L ∩ (u ∩ v) := ⟨hz1, hz2.2, hz.2⟩
      rw [hLuv'] at hz3
      exact hz3
    have hBjoin : JoinedIn ((L ∩ v)ᶜ) X Y := by
      by_contra hcon2
      have : L ∩ v ∈ S := ⟨hBneK, hBcpt, hcon2⟩
      have hsub := hLmin' (L ∩ v) this inter_subset_left
      obtain ⟨z, hz⟩ := hAne'
      have hz1 : z ∈ L := hz.1
      have hz2 : z ∈ L ∩ v := hsub hz1
      have hz3 : z ∈ L ∩ (u ∩ v) := ⟨hz1, hz.2, hz2.2⟩
      rw [hLuv'] at hz3
      exact hz3
    -- the separation hypothesis
    have hsepuv : ∀ a ∈ L ∩ u, ∀ b ∈ L ∩ v, 0 < dist a b := by
      intro a ha b hb
      refine dist_pos.mpr fun h => ?_
      have : a ∈ L ∩ (u ∩ v) := ⟨ha.1, ha.2, h ▸ hb.2⟩
      rw [hLuv'] at this
      exact this
    have hXAB : X ∉ (L ∩ u) ∪ (L ∩ v) := by
      intro hmem
      rcases hmem with h | h
      · exact hX (hLK h.1)
      · exact hX (hLK h.1)
    have hYAB : Y ∉ (L ∩ u) ∪ (L ∩ v) := by
      intro hmem
      rcases hmem with h | h
      · exact hY (hLK h.1)
      · exact hY (hLK h.1)
    have := joinedIn_compl_union hAcpt hBcpt hsepuv hXAB hYAB hAjoin hBjoin
    refine hLsep ?_
    have hunion : (L ∩ u) ∪ (L ∩ v) = L := by
      ext z; constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        rcases hLuv hz with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
    rwa [hunion] at this
  -- `L` is a point
  have hLsub : L.Subsingleton := htd L hLK hLpre
  obtain ⟨p, hp⟩ := hLne
  have hLsing : L = {p} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun q hq => ?_⟩
    exact hLsub hq hp
  refine hLsep ?_
  have hXp : X ≠ p := fun h => hX (hLK (by rw [hLsing, h]; exact mem_singleton p))
  have hYp : Y ≠ p := fun h => hY (hLK (by rw [hLsing, h]; exact mem_singleton p))
  rw [hLsing]
  exact joinedIn_compl_singleton hXp hYp

/-- **A compact totally disconnected subset of the plane does not separate it.** -/
theorem compl_totallyDisconnected_plane {K : Set Pt} (hK : IsCompact K)
    (htd : IsTotallyDisconnected K) : IsPathConnected (Kᶜ) := by
  classical
  -- a point outside `K`
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Pt)).mp hK.isBounded
  obtain ⟨w, hw⟩ := exists_ne (0 : Pt)
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set z₀ : Pt := ((|R| + 1) / ‖w‖) • w with hz₀
  have hz₀n : ‖z₀‖ = |R| + 1 := by
    rw [hz₀, norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ (ne_of_gt hwn)]
  have hz₀K : z₀ ∉ K := by
    intro hmem
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, hz₀n] at h1
    have h2 := le_abs_self R
    linarith
  exact ⟨z₀, hz₀K, fun Y hY => joinedIn_compl_of_isCompact_isTotallyDisconnected hK htd hz₀K hY⟩

end

end Grid
end Work.Whitney.PathTools
