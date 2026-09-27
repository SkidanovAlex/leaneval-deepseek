import Mathlib
import Submission.Work.Whitney.PathTools.ball_sdiff_totallyDisconnected

/-!
# A compact totally disconnected subset of the plane is removable from an open ball

If `K ⊆ ℝ²` is compact and totally disconnected and `X, Y ∈ ball c r \ K`, then `X` and `Y` are
joined by a path inside `ball c r \ K`.  There is **no** hypothesis `K ⊆ ball c r`: the compact set
`K` may meet the sphere `sphere c r` and may extend outside the ball.

The proof is a minimal-separator (Zorn) argument.  By `joinedIn_ball_sdiff_iff_compl_union_sphere_pt`
it is the same to ask for a path avoiding `K ∪ sphere c r`, so we consider the family

  `S = { M : M ⊆ K, IsCompact M, ¬ JoinedIn ((M ∪ sphere c r)ᶜ) X Y }`,

which contains `K`.  A minimal element `M` is shown to be empty, which is absurd because then
`M ∪ sphere c r = sphere c r` and the segment inside the convex ball `ball c r` avoids the sphere.

Suppose `M ≠ ∅`.

* If `M` misses the sphere, then `M ∩ closedBall c r` is a compact totally disconnected set
  contained in a strictly smaller closed ball, so removing it from `ball c r` leaves a path
  connected space (`ball_sdiff_totallyDisconnected`); moreover `ball c r \ (M ∩ closedBall c r)`
  avoids `M` and the sphere.  This contradicts `M ∈ S`.
* If `M` meets the sphere, then `M ⊄ sphere c r` (otherwise `M ∪ sphere c r = sphere c r` and
  `M ∈ S` would contradict the segment in the ball).  Pick `p ∈ M \ sphere c r`; in the compact
  totally disconnected space `↥M` the point `p` has a clopen neighbourhood avoiding `M ∩ sphere`,
  giving `C ⊆ M` with `C` and `M \ C` closed, `p ∈ C`, `C ∩ sphere = ∅`.  Both `C` and `M \ C` are
  proper compact subsets of `M`, so by minimality there are paths avoiding `C ∪ sphere` and avoiding
  `(M \ C) ∪ sphere`; Janiszewski's theorem for the two disjoint compacta `(M \ C) ∪ sphere` and `C`
  then produces a path avoiding `M ∪ sphere`, contradicting `M ∈ S`.
-/

open Set Metric Topology
open scoped Topology

namespace Work.Whitney.PathTools

open Grid

noncomputable section

/-- A path in the open ball avoiding `K` is the same as a path avoiding `K ∪ sphere c r`. -/
private lemma joinedIn_ball_sdiff_iff_compl_union_sphere_pt {K : Set Pt} {c : Pt} {r : ℝ}
    {X Y : Pt} (hX : X ∈ Metric.ball c r) (_hY : Y ∈ Metric.ball c r) :
    JoinedIn (Metric.ball c r \ K) X Y ↔
      JoinedIn ((K ∪ Metric.sphere c r)ᶜ : Set Pt) X Y := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, fun t => ?_⟩
    obtain ⟨hb, hK⟩ := hγ t
    simp only [mem_compl_iff, mem_union, not_or]
    exact ⟨hK, fun hsphere =>
      ne_of_lt (Metric.mem_ball.mp hb) (Metric.mem_sphere.mp hsphere)⟩
  · rintro ⟨γ, hγ⟩
    have hγ' : ∀ t, γ t ∉ K ∧ γ t ∉ Metric.sphere c r := by
      intro t; simpa only [mem_compl_iff, mem_union, not_or] using hγ t
    refine ⟨γ, fun t => ⟨?_, (hγ' t).1⟩⟩
    have hpre : IsPreconnected (Set.range γ) := isPreconnected_range γ.continuous
    have hsub : Set.range γ ⊆ Metric.ball c r ∪ (Metric.closedBall c r)ᶜ := by
      rintro _ ⟨s, rfl⟩
      by_cases hlt : dist (γ s) c < r
      · exact Or.inl (Metric.mem_ball.mpr hlt)
      · refine Or.inr ?_
        simp only [mem_compl_iff, Metric.mem_closedBall, not_le]
        exact lt_of_le_of_ne (le_of_not_gt hlt)
          (fun h => (hγ' s).2 (Metric.mem_sphere.mpr h.symm))
    have hdisj : Set.range γ ∩ (Metric.ball c r ∩ (Metric.closedBall c r)ᶜ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro _ ⟨-, hb, hc⟩
      exact hc (Metric.ball_subset_closedBall hb)
    rcases (isPreconnected_iff_subset_of_disjoint.mp hpre) (Metric.ball c r)
        ((Metric.closedBall c r)ᶜ) Metric.isOpen_ball Metric.isClosed_closedBall.isOpen_compl
        hsub hdisj with h | h
    · exact h ⟨t, rfl⟩
    · exact absurd (h ⟨0, γ.source⟩) (by
        simp only [mem_compl_iff, Metric.mem_closedBall, not_le]
        exact not_lt.mpr (le_of_lt (Metric.mem_ball.mp hX)))

/-- A point of a compact totally disconnected set can be separated from a closed subset of it by a
clopen piece. -/
private lemma exists_clopen_sep_pt {M Q : Set Pt} (hMc : IsCompact M)
    (hMtd : IsTotallyDisconnected M) (hQ : IsClosed Q) (hQM : Q ⊆ M) {p : Pt} (hpM : p ∈ M)
    (hpQ : p ∉ Q) :
    ∃ B : Set Pt, B ⊆ M ∧ IsClosed B ∧ IsClosed (M \ B) ∧ p ∈ B ∧ B ∩ Q = ∅ := by
  haveI : CompactSpace ↥M := isCompact_iff_compactSpace.mp hMc
  haveI : TotallyDisconnectedSpace ↥M := totallyDisconnectedSpace_subtype_iff.mpr hMtd
  have hQcl : IsClosed ((↑) ⁻¹' Q : Set ↥M) := hQ.preimage continuous_subtype_val
  obtain ⟨V, hVcl, hVp, hVsub⟩ :=
    compact_exists_isClopen_in_isOpen (x := (⟨p, hpM⟩ : ↥M)) (U := ((↑) ⁻¹' Q)ᶜ)
      hQcl.isOpen_compl (by simpa using hpQ)
  refine ⟨Subtype.val '' V, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, -, rfl⟩; exact v.2
  · exact hVcl.isClosed.isCompact.image_of_continuousOn continuous_subtype_val.continuousOn
      |>.isClosed
  · have hcomp : M \ (Subtype.val '' V) = Subtype.val '' (Vᶜ) := by
      ext z
      constructor
      · rintro ⟨hzM, hzV⟩
        exact ⟨⟨z, hzM⟩, fun hv => hzV ⟨⟨z, hzM⟩, hv, rfl⟩, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v.2, fun hmem => hv (by
          obtain ⟨w, hw, hwv⟩ := hmem
          exact (Subtype.val_injective hwv.symm) ▸ hw)⟩
    rw [hcomp]
    exact (hVcl.compl.isClosed).isCompact.image_of_continuousOn
      continuous_subtype_val.continuousOn |>.isClosed
  · exact ⟨⟨p, hpM⟩, hVp, rfl⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨⟨v, hv, rfl⟩, hvQ⟩
    exact hVsub hv hvQ

/-- **A compact totally disconnected subset of the plane is removable from an open ball.** -/
theorem planar_ball_sdiff_totallyDisconnected {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (htd : IsTotallyDisconnected K) {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hr : 0 < r) {X Y : EuclideanSpace ℝ (Fin 2)}
    (hX : X ∈ Metric.ball c r \ K) (hY : Y ∈ Metric.ball c r \ K) :
    JoinedIn (Metric.ball c r \ K) X Y := by
  classical
  haveI : ProperSpace Pt := FiniteDimensional.proper ℝ Pt
  by_contra hcon
  have hXb : X ∈ Metric.ball c r := hX.1
  have hYb : Y ∈ Metric.ball c r := hY.1
  have hcon' : ¬ JoinedIn ((K ∪ Metric.sphere c r)ᶜ : Set Pt) X Y := fun h =>
    hcon ((joinedIn_ball_sdiff_iff_compl_union_sphere_pt hXb hYb).mpr h)
  have hsphere : JoinedIn ((Metric.sphere c r)ᶜ : Set Pt) X Y :=
    ((convex_ball c r).isPathConnected ⟨X, hXb⟩).joinedIn X hXb Y hYb |>.mono
      (fun z hz => by
        rw [mem_compl_iff, Metric.mem_sphere]
        exact ne_of_lt (Metric.mem_ball.mp hz))
  set S : Set (Set Pt) :=
    {M | M ⊆ K ∧ IsCompact M ∧ ¬ JoinedIn ((M ∪ Metric.sphere c r)ᶜ) X Y} with hSdef
  have hKmemS : K ∈ S := ⟨subset_rfl, hK, hcon'⟩
  have hchain : ∀ ch ⊆ S, IsChain (· ⊆ ·) ch → ∃ lb ∈ S, ∀ s ∈ ch, lb ⊆ s := by
    intro ch hchS hchain
    rcases ch.eq_empty_or_nonempty with rfl | hne
    · exact ⟨K, hKmemS, fun s hs => absurd hs (by simp)⟩
    · refine ⟨⋂₀ ch, ⟨?_, ?_, ?_⟩, fun s hs => sInter_subset_of_mem hs⟩
      · obtain ⟨L₀, hL₀⟩ := hne
        exact (sInter_subset_of_mem hL₀).trans (hchS hL₀).1
      · exact hK.of_isClosed_subset (isClosed_sInter fun s hs => ((hchS hs).2.1).isClosed)
          ((sInter_subset_of_mem hne.some_mem).trans (hchS hne.some_mem).1)
      · rintro ⟨γ, hγ⟩
        have hcover : range γ ⊆ ⋃ i : {L // L ∈ ch}, ((i : Set Pt) ∪ Metric.sphere c r)ᶜ := by
          intro z hz
          obtain ⟨t, rfl⟩ := hz
          have h1 : γ t ∉ ⋂₀ ch ∪ Metric.sphere c r := by
            have := hγ t
            simpa only [mem_compl_iff] using this
          rw [Set.mem_union, not_or, Set.mem_sInter] at h1
          push_neg at h1
          obtain ⟨L, hLc, hLt⟩ := h1.1
          exact Set.mem_iUnion.mpr ⟨⟨L, hLc⟩, by
            simp only [mem_compl_iff, mem_union, not_or]; exact ⟨hLt, h1.2⟩⟩
        obtain ⟨u, hu⟩ := (isCompact_range γ.continuous).elim_finite_subcover
          (fun i : {L // L ∈ ch} => ((i : Set Pt) ∪ Metric.sphere c r)ᶜ)
          (fun i => ((hchS i.2).2.1.isClosed.union Metric.isClosed_sphere).isOpen_compl) hcover
        have hufin : ∀ L' ∈ u.image Subtype.val, L' ∈ ch := by
          intro L' hL'
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hL'
          exact i.2
        rcases u.eq_empty_or_nonempty with rfl | uone
        · exfalso
          have h0 := hu ⟨(0 : unitInterval), rfl⟩
          simpa using h0
        obtain ⟨L', hL'u, hL'min⟩ := Finset.exists_subset_of_isChain hchain hufin
          (uone.image Subtype.val)
        have hsub : range γ ⊆ ((L' : Set Pt) ∪ Metric.sphere c r)ᶜ := by
          intro z hz
          have h1 := hu hz
          rw [Set.mem_iUnion] at h1
          obtain ⟨i, h1⟩ := h1
          rw [Set.mem_iUnion] at h1
          obtain ⟨hiu, hzi⟩ := h1
          have h2 : (i : Set Pt) ∈ u.image Subtype.val := Finset.mem_image.mpr ⟨i, hiu, rfl⟩
          intro hzL
          rcases hzL with h | h
          · exact hzi (Or.inl ((hL'min (i : Set Pt) h2) h))
          · exact hzi (Or.inr h)
        have hL'c : L' ∈ ch := hufin L' hL'u
        exact (hchS hL'c).2.2 ⟨γ, fun t => by
          have := hsub ⟨t, rfl⟩
          simpa only [mem_compl_iff] using this⟩
  obtain ⟨M, hMmin⟩ := zorn_superset S hchain
  have hMmem : M ∈ S := hMmin.1
  obtain ⟨hMK, hMcpt, hMsep⟩ := hMmem
  have hMmin' : ∀ a ∈ S, a ⊆ M → M ⊆ a := hMmin.2
  have hMtd : IsTotallyDisconnected M := fun t ht hpre => htd t (ht.trans hMK) hpre
  have hMempty : M = ∅ := by
    rcases M.eq_empty_or_nonempty with h | hMne
    · exact h
    · exfalso
      rcases (M ∩ Metric.sphere c r).eq_empty_or_nonempty with hmiss | hmeet
      · -- `M` misses the sphere: remove the part of `M` inside a suitable closed ball
        set K' : Set Pt := M ∩ Metric.closedBall c r with hK'def
        have hK'cpt : IsCompact K' := hMcpt.inter_right Metric.isClosed_closedBall
        have hK'td : IsTotallyDisconnected K' :=
          fun t ht hpre => hMtd t (ht.trans inter_subset_left) hpre
        have hmaxlt : ∀ x ∈ K', dist x c < r := by
          intro x hx
          have h1 : dist x c ≤ r := Metric.mem_closedBall.mp hx.2
          have h2 : x ∉ Metric.sphere c r := fun hs => by
            have hmem : x ∈ M ∩ Metric.sphere c r := ⟨hx.1, hs⟩
            rw [hmiss] at hmem
            exact hmem
          have h3 : dist x c ≠ r := fun hh => h2 (Metric.mem_sphere.mpr hh)
          exact lt_of_le_of_ne h1 h3
        obtain ⟨ρ, _hρpos, hρr, hK'sub⟩ :
            ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ K' ⊆ Metric.closedBall c ρ := by
          rcases K'.eq_empty_or_nonempty with he | hne'
          · exact ⟨r / 2, by linarith, by linarith, by rw [he]; exact Set.empty_subset _⟩
          · obtain ⟨x₀, hx₀, hmax⟩ := hK'cpt.exists_isMaxOn hne'
              (f := fun z : Pt => dist z c) (continuous_id.dist continuous_const).continuousOn
            refine ⟨(dist x₀ c + r) / 2, by linarith [dist_nonneg (x := x₀) (y := c)],
              by linarith [hmaxlt x₀ hx₀], ?_⟩
            intro x hx
            rw [Metric.mem_closedBall]
            have hxx : dist x c ≤ dist x₀ c := by simpa using hmax hx
            linarith [hmaxlt x₀ hx₀]
        have hpc : IsPathConnected (Metric.ball c r \ K') :=
          ball_sdiff_totallyDisconnected (E := Pt) (by rw [finrank_euclideanSpace]; simp) hr
            hK'cpt
            (fun x hx => Metric.mem_ball.mpr
              (lt_of_le_of_lt (Metric.mem_closedBall.mp (hK'sub hx)) hρr))
            hK'td
        refine hMsep ?_
        refine (hpc.joinedIn X ⟨hXb, fun h => hX.2 (hMK h.1)⟩ Y
          ⟨hYb, fun h => hY.2 (hMK h.1)⟩).mono ?_
        rintro z ⟨hzb, hzK'⟩
        simp only [mem_compl_iff, mem_union, not_or]
        exact ⟨fun hzM => hzK' ⟨hzM, Metric.ball_subset_closedBall hzb⟩,
          fun hs => ne_of_lt (Metric.mem_ball.mp hzb) (Metric.mem_sphere.mp hs)⟩
      · -- `M` meets the sphere: split `M` by a clopen piece and use Janiszewski
        have hnotsub : ¬ M ⊆ Metric.sphere c r := by
          intro hsub
          refine hMsep ?_
          rw [Set.union_eq_right.mpr hsub]
          exact hsphere
        obtain ⟨p, hpM, hpns⟩ := Set.not_subset.mp hnotsub
        obtain ⟨C, hCM, hCcl, hMcls, hpC, hCdisj⟩ :=
          exists_clopen_sep_pt hMcpt hMtd (hMcpt.isClosed.inter Metric.isClosed_sphere)
            inter_subset_left hpM (fun h => hpns h.2)
        have hCne : C ≠ M := by
          intro hEq
          obtain ⟨z, hz⟩ := hmeet
          exact (Set.eq_empty_iff_forall_notMem.mp hCdisj) z ⟨hEq.symm ▸ hz.1, hz⟩
        have hAcne : M \ C ≠ M := by
          intro hEq
          exact (hEq.symm ▸ hpM).2 hpC
        have hAcpt : IsCompact (M \ C) := hMcpt.of_isClosed_subset hMcls sdiff_subset
        have hCnS : C ∉ S := fun hmem =>
          hCne (Set.Subset.antisymm hCM (hMmin' C hmem hCM))
        have hAnS : M \ C ∉ S := fun hmem =>
          hAcne (Set.Subset.antisymm sdiff_subset (hMmin' (M \ C) hmem sdiff_subset))
        have hjoinA : JoinedIn (((M \ C) ∪ Metric.sphere c r)ᶜ) X Y :=
          not_not.mp fun hc => hAnS ⟨sdiff_subset.trans hMK, hAcpt, hc⟩
        have hjoinC : JoinedIn ((C ∪ Metric.sphere c r)ᶜ) X Y :=
          not_not.mp fun hc => hCnS ⟨hCM.trans hMK, hMcpt.of_isClosed_subset hCcl hCM, hc⟩
        have hjoinC' : JoinedIn (Cᶜ) X Y := hjoinC.mono (fun z hz => by
          rw [mem_compl_iff] at hz ⊢
          exact fun hzC => hz (Or.inl hzC))
        have hdisj : Disjoint ((M \ C) ∪ Metric.sphere c r) C := by
          rw [Set.disjoint_left]
          rintro z (⟨-, hznC⟩ | hzs) hzC
          · exact hznC hzC
          · exact (Set.eq_empty_iff_forall_notMem.mp hCdisj) z ⟨hzC, ⟨hCM hzC, hzs⟩⟩
        have hXnot : X ∉ ((M \ C) ∪ Metric.sphere c r) ∪ C := by
          rintro ((h | h) | h)
          · exact hX.2 (hMK h.1)
          · exact absurd (Metric.mem_sphere.mp h) (ne_of_lt (Metric.mem_ball.mp hXb))
          · exact hX.2 (hMK (hCM h))
        have hYnot : Y ∉ ((M \ C) ∪ Metric.sphere c r) ∪ C := by
          rintro ((h | h) | h)
          · exact hY.2 (hMK h.1)
          · exact absurd (Metric.mem_sphere.mp h) (ne_of_lt (Metric.mem_ball.mp hYb))
          · exact hY.2 (hMK (hCM h))
        have hsepuv : ∀ a ∈ (M \ C) ∪ Metric.sphere c r, ∀ b ∈ C, 0 < dist a b :=
          fun a ha b hb => dist_pos.mpr fun hEq =>
            Set.disjoint_left.mp hdisj ha (hEq ▸ hb)
        have hfin := Grid.joinedIn_compl_union (hAcpt.union (isCompact_sphere c r))
          (hMcpt.of_isClosed_subset hCcl hCM) hsepuv hXnot hYnot hjoinA hjoinC'
        refine hMsep ?_
        have hunion : (M \ C) ∪ Metric.sphere c r ∪ C = M ∪ Metric.sphere c r := by
          ext z
          constructor
          · rintro ((⟨hzM, -⟩ | hzs) | hzC)
            · exact Or.inl hzM
            · exact Or.inr hzs
            · exact Or.inl (hCM hzC)
          · rintro (hzM | hzs)
            · by_cases hzC : z ∈ C
              · exact Or.inr hzC
              · exact Or.inl (Or.inl ⟨hzM, hzC⟩)
            · exact Or.inl (Or.inr hzs)
        rwa [hunion] at hfin
  rw [hMempty] at hMsep
  exact hMsep (by simpa using hsphere)

end

end Work.Whitney.PathTools
