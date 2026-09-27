import Mathlib
import Submission.Work.Whitney.PathTools.JaniszewskiTwo
import Submission.Work.Whitney.PathTools.janiszewski_subsingleton
import Submission.Work.Whitney.PathTools.arc_complement_interval_of_inter_singleton

/-!
# Non-separation of the injectively parametrised image of a compact subset of `ℝ` in the plane

Target: `Work.Whitney.PathTools.plane_arc_nonseparation`.

The mathematical content is the classical "Jordan arc theorem" in the plane: a compact arc does
not separate `ℝ²`.  We reduce the general statement (compact `K ⊆ ℝ`, `γ` continuous and injective
on `K`) to the case `K = Icc a b` with `a < b` (a genuine arc) by a minimal-separator argument
(Zorn): a minimal compact separator `L ⊆ γ '' K` is connected, and a connected compact subset of
`ℝ` is a closed interval; then `L = γ '' Icc a b` is a sub-arc.
-/

open Set Metric Topology

namespace Work.Whitney.PathTools

/-- The plane, as in the `Grid` files. -/
abbrev Pt2 := EuclideanSpace ℝ (Fin 2)

/-- The rank of the plane is `> 1`. -/
theorem one_lt_rank_pt2 : 1 < Module.rank ℝ Pt2 := by
  have hfin : Module.finrank ℝ Pt2 = 2 := by
    rw [finrank_euclideanSpace]
    simp
  rw [← Module.finrank_eq_rank', hfin]
  norm_num

/-- The complement of a closed ball in the plane is path connected. -/
theorem isPathConnected_compl_closedBall_pt2 (a : Pt2) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsPathConnected ((Metric.closedBall a ρ)ᶜ : Set Pt2) := by
  have hI : IsPathConnected (Ioi ρ) := (convex_Ioi ρ).isPathConnected ⟨ρ + 1, by simp⟩
  have hS : IsPathConnected (sphere (0 : Pt2) 1) :=
    isPathConnected_sphere one_lt_rank_pt2 0 (by norm_num)
  have hprod : IsPathConnected ((Ioi ρ) ×ˢ (sphere (0 : Pt2) 1)) := hI.prod hS
  have hcont : Continuous (fun p : ℝ × Pt2 => a + p.1 • p.2) :=
    continuous_const.add (continuous_fst.smul continuous_snd)
  have himg := hprod.image hcont
  have hset : (fun p : ℝ × Pt2 => a + p.1 • p.2) '' ((Ioi ρ) ×ˢ (sphere (0 : Pt2) 1))
      = (Metric.closedBall a ρ)ᶜ := by
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
  rwa [hset] at himg

/-- The complement of a point in the plane is path connected. -/
theorem isPathConnected_compl_singleton_pt2 (p : Pt2) :
    IsPathConnected (({p} : Set Pt2)ᶜ) := by
  have h := isPathConnected_compl_closedBall_pt2 p (ρ := 0) le_rfl
  rwa [Metric.closedBall_zero] at h

/-- A single point does not separate two points of the plane. -/
theorem joinedIn_compl_singleton_pt2 {p X Y : Pt2} (hX : X ≠ p) (hY : Y ≠ p) :
    JoinedIn (({p} : Set Pt2)ᶜ) X Y :=
  (isPathConnected_compl_singleton_pt2 p).joinedIn X (by simpa [mem_compl_iff]) Y
    (by simpa [mem_compl_iff])

/-- A finite subfamily of a chain has a least element. -/
theorem Finset.exists_subset_of_isChain' {α : Type*} {c : Set (Set α)}
    (hc : IsChain (· ⊆ ·) c) {t : Finset (Set α)} (ht : ∀ L ∈ t, L ∈ c)
    (hne : t.Nonempty) : ∃ L ∈ t, ∀ L' ∈ t, L ⊆ L' := by
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

/-- A compact, nonempty, order-connected subset of `ℝ` is a closed interval. -/
theorem eq_Icc_of_isCompact_ordConnected {s : Set ℝ} (hcomp : IsCompact s) (hne : s.Nonempty)
    (hord : s.OrdConnected) : s = Set.Icc (sInf s) (sSup s) := by
  have hbddB : BddBelow s := hcomp.isBounded.bddBelow
  have hbddA : BddAbove s := hcomp.isBounded.bddAbove
  have ha : sInf s ∈ s := hcomp.isClosed.csInf_mem hne hbddB
  have hb : sSup s ∈ s := hcomp.isClosed.csSup_mem hne hbddA
  refine subset_antisymm (fun x hx => ⟨csInf_le hbddB hx, le_csSup hbddA hx⟩) (fun x hx => ?_)
  exact hord.out ha hb hx

/-- **Reduction to a sub-interval.**  If the image of the compact set `K` separates `X` from `Y`,
then so does the image of some compact sub-interval of `K`.

Proof: let `L` be a minimal compact subset of `γ '' K` that still separates `X` from `Y` (Zorn).
Minimality forces `L` to be connected, and then `K' := γ ⁻¹' L ∩ K` is order-connected: if
`s < r < t` with `s, t ∈ K'` and `r ∉ K'`, the two closed pieces `γ '' (K' ∩ Iic r)` and
`γ '' (K' ∩ Ici r)` are nonempty, disjoint, closed and cover `L = γ '' K'`, contradicting the
connectedness of `L`.  Hence `K' = Icc (sInf K') (sSup K')` and `L = γ '' Icc a b`. -/
theorem exists_subinterval_not_joinedIn {K : Set ℝ} (hK : IsCompact K) {γ : ℝ → Pt2}
    (hcont : ContinuousOn γ K) (hinj : Set.InjOn γ K) {X Y : Pt2} (hX : X ∉ γ '' K)
    (hY : Y ∉ γ '' K) (hsep : ¬ JoinedIn ((γ '' K)ᶜ) X Y) :
    ∃ a b : ℝ, a ∈ K ∧ b ∈ K ∧ a ≤ b ∧ Set.Icc a b ⊆ K ∧
      ¬ JoinedIn ((γ '' Set.Icc a b)ᶜ) X Y := by
  classical
  set A : Set Pt2 := γ '' K with hAdef
  have hAcomp : IsCompact A := hK.image_of_continuousOn hcont
  set S : Set (Set Pt2) := {L | L ⊆ A ∧ IsCompact L ∧ ¬ JoinedIn (Lᶜ) X Y} with hSdef
  have hAmem : A ∈ S := ⟨subset_rfl, hAcomp, hsep⟩
  have hchaincond : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨A, hAmem, fun s hs => absurd hs (by simp)⟩
    · refine ⟨⋂₀ c, ⟨?_, ?_, ?_⟩, fun s hs => sInter_subset_of_mem hs⟩
      · obtain ⟨L₀, hL₀⟩ := hne
        exact (sInter_subset_of_mem hL₀).trans (hcS hL₀).1
      · refine hAcomp.of_isClosed_subset ?_ ?_
        · exact isClosed_sInter (fun s hs => ((hcS hs).2.1).isClosed)
        · obtain ⟨L₀, hL₀⟩ := hne
          exact (sInter_subset_of_mem hL₀).trans (hcS hL₀).1
      · rintro ⟨σ, hσ⟩
        have hcover : range σ ⊆ ⋃ i : {L // L ∈ c}, ((i : Set Pt2))ᶜ := by
          intro z hz
          obtain ⟨t, rfl⟩ := hz
          have h1 : σ t ∉ ⋂₀ c := hσ t
          rw [Set.mem_sInter] at h1
          push_neg at h1
          obtain ⟨L, hLc, hLt⟩ := h1
          exact Set.mem_iUnion.mpr ⟨⟨L, hLc⟩, hLt⟩
        obtain ⟨u, hu⟩ := (isCompact_range σ.continuous).elim_finite_subcover
          (fun i : {L // L ∈ c} => ((i : Set Pt2))ᶜ)
          (fun i => ((hcS i.2).2.1).isClosed.isOpen_compl) hcover
        have hufin : ∀ L' ∈ u.image Subtype.val, L' ∈ c := by
          intro L' hL'
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hL'
          exact i.2
        rcases u.eq_empty_or_nonempty with rfl | uone
        · exfalso
          have h0 := hu ⟨(0 : unitInterval), rfl⟩
          simpa using h0
        obtain ⟨L', hL'u, hL'min⟩ := Finset.exists_subset_of_isChain' hchain hufin
          (uone.image Subtype.val)
        have hsub : range σ ⊆ ((L' : Set Pt2))ᶜ := by
          intro z hz
          have h1 := hu hz
          rw [Set.mem_iUnion] at h1
          obtain ⟨i, h1⟩ := h1
          rw [Set.mem_iUnion] at h1
          obtain ⟨hiu, hzi⟩ := h1
          have h2 : (i : Set Pt2) ∈ u.image Subtype.val :=
            Finset.mem_image.mpr ⟨i, hiu, rfl⟩
          exact fun hzL => hzi ((hL'min (i : Set Pt2) h2) hzL)
        have hL'c : L' ∈ c := hufin L' hL'u
        exact (hcS hL'c).2.2 ⟨σ, fun t => hsub ⟨t, rfl⟩⟩
  obtain ⟨L, hLmin⟩ := zorn_superset S hchaincond
  have hLmem : L ∈ S := hLmin.1
  obtain ⟨hLA, hLcomp, hLsep⟩ := hLmem
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
    have hAeq : L ∩ u = L ∩ vᶜ := by
      ext z; constructor
      · rintro ⟨hzL, hzu⟩
        exact ⟨hzL, fun hzv => Set.eq_empty_iff_forall_notMem.mp hLuv' z ⟨hzL, hzu, hzv⟩⟩
      · rintro ⟨hzL, hzv⟩
        rcases hLuv hzL with h | h
        · exact ⟨hzL, h⟩
        · exact absurd h hzv
    have hBeq : L ∩ v = L ∩ uᶜ := by
      ext z; constructor
      · rintro ⟨hzL, hzv⟩
        exact ⟨hzL, fun hzu => Set.eq_empty_iff_forall_notMem.mp hLuv' z ⟨hzL, hzu, hzv⟩⟩
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
    have hAneK : (L ∩ u) ⊆ A := inter_subset_left.trans hLA
    have hBneK : (L ∩ v) ⊆ A := inter_subset_left.trans hLA
    have hAjoin : JoinedIn ((L ∩ u)ᶜ) X Y := by
      by_contra hcon2
      have : L ∩ u ∈ S := ⟨hAneK, hAcpt, hcon2⟩
      have hsub := hLmin' (L ∩ u) this inter_subset_left
      obtain ⟨z, hz⟩ := hLv
      have hz1 : z ∈ L := hz.1
      have hz2 : z ∈ L ∩ u := hsub hz1
      have hz3 : z ∈ L ∩ (u ∩ v) := ⟨hz1, hz2.2, hz.2⟩
      rw [hLuv'] at hz3
      exact hz3
    have hBjoin : JoinedIn ((L ∩ v)ᶜ) X Y := by
      by_contra hcon2
      have : L ∩ v ∈ S := ⟨hBneK, hBcpt, hcon2⟩
      have hsub := hLmin' (L ∩ v) this inter_subset_left
      obtain ⟨z, hz⟩ := hLu
      have hz1 : z ∈ L := hz.1
      have hz2 : z ∈ L ∩ v := hsub hz1
      have hz3 : z ∈ L ∩ (u ∩ v) := ⟨hz1, hz.2, hz2.2⟩
      rw [hLuv'] at hz3
      exact hz3
    have hsepuv : ∀ a ∈ L ∩ u, ∀ b ∈ L ∩ v, 0 < dist a b := by
      intro a ha b hb
      refine dist_pos.mpr fun h => ?_
      have : a ∈ L ∩ (u ∩ v) := ⟨ha.1, ha.2, h ▸ hb.2⟩
      rw [hLuv'] at this
      exact this
    have hXAB : X ∉ (L ∩ u) ∪ (L ∩ v) := by
      intro hmem
      rcases hmem with h | h
      · exact hX (hLA h.1)
      · exact hX (hLA h.1)
    have hYAB : Y ∉ (L ∩ u) ∪ (L ∩ v) := by
      intro hmem
      rcases hmem with h | h
      · exact hY (hLA h.1)
      · exact hY (hLA h.1)
    have := Grid.joinedIn_compl_union hAcpt hBcpt hsepuv hXAB hYAB hAjoin hBjoin
    refine hLsep ?_
    have hunion : (L ∩ u) ∪ (L ∩ v) = L := by
      ext z; constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        rcases hLuv hz with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
    rwa [hunion] at this
  -- the parameter set whose image is `L`
  set K' : Set ℝ := {t | t ∈ K ∧ γ t ∈ L} with hK'def
  have hK'image : γ '' K' = L := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht.2
    · intro hz
      obtain ⟨t, htK, htz⟩ := hLA hz
      exact ⟨t, ⟨htK, htz ▸ hz⟩, htz⟩
  have hK'ne : K'.Nonempty := by
    obtain ⟨z, hz⟩ := hLne
    obtain ⟨t, ht, rfl⟩ := hLA hz
    exact ⟨t, ⟨ht, hz⟩⟩
  have hK'comp : IsCompact K' := by
    have hsub : K' = (Subtype.val : ↥K → ℝ) '' ((fun t : ↥K => γ t.1) ⁻¹' L) := by
      ext t
      constructor
      · rintro ⟨htK, htL⟩
        exact ⟨⟨t, htK⟩, htL, rfl⟩
      · rintro ⟨t, htL, rfl⟩
        exact ⟨t.2, htL⟩
    rw [hsub]
    haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
    have hcont' : Continuous (fun t : ↥K => γ t.1) := hcont.domRestrict
    have hcl : IsClosed ((fun t : ↥K => γ t.1) ⁻¹' L) := hLcomp.isClosed.preimage hcont'
    exact (hcl.isCompact).image continuous_subtype_val
  -- `K'` is order-connected
  have hK'ord : K'.OrdConnected := by
    refine ⟨fun s hs t ht => ?_⟩
    intro r hr
    by_cases hrs : r = s
    · rwa [hrs]
    by_cases hrt : r = t
    · rwa [hrt]
    have hsr : s < r := lt_of_le_of_ne hr.1 (Ne.symm hrs)
    have hrt' : r < t := lt_of_le_of_ne hr.2 hrt
    by_contra hrK'
    have hcompP : IsCompact (K' ∩ Iic r) := hK'comp.inter_right isClosed_Iic
    have hcompQ : IsCompact (K' ∩ Ici r) := hK'comp.inter_right isClosed_Ici
    have hcontP : ContinuousOn γ (K' ∩ Iic r) :=
      hcont.mono (inter_subset_left.trans inter_subset_left)
    have hcontQ : ContinuousOn γ (K' ∩ Ici r) :=
      hcont.mono (inter_subset_left.trans inter_subset_left)
    have hPcomp : IsCompact (γ '' (K' ∩ Iic r)) := hcompP.image_of_continuousOn hcontP
    have hQcomp : IsCompact (γ '' (K' ∩ Ici r)) := hcompQ.image_of_continuousOn hcontQ
    have hPne : (γ '' (K' ∩ Iic r)).Nonempty :=
      ⟨γ s, s, ⟨hs, le_of_lt hsr⟩, rfl⟩
    have hQne : (γ '' (K' ∩ Ici r)).Nonempty :=
      ⟨γ t, t, ⟨ht, le_of_lt hrt'⟩, rfl⟩
    have hunion' : γ '' (K' ∩ Iic r) ∪ γ '' (K' ∩ Ici r) = L := by
      rw [← Set.image_union, ← hK'image]
      congr 1
      ext x
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        rcases lt_trichotomy x r with h | h | h
        · exact Or.inl ⟨hx, le_of_lt h⟩
        · exact absurd (h ▸ hx) hrK'
        · exact Or.inr ⟨hx, le_of_lt h⟩
    have hdisj' : γ '' (K' ∩ Iic r) ∩ γ '' (K' ∩ Ici r) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨⟨a, ⟨ha, har⟩, haz⟩, ⟨b, ⟨hb, hbr⟩, hbz⟩⟩
      have hab : a = b := hinj ha.1 hb.1 (by rw [haz, hbz])
      have hra : r = a := le_antisymm (hab.symm ▸ hbr) har
      exact hrK' (by rw [hra]; exact ha)
    -- contradict connectivity of `L`
    have hLuv : L ⊆ (γ '' (K' ∩ Ici r))ᶜ ∪ (γ '' (K' ∩ Iic r))ᶜ := by
      intro z hz
      have hz' : z ∈ γ '' (K' ∩ Iic r) ∪ γ '' (K' ∩ Ici r) := by
        rw [hunion']; exact hz
      rcases hz' with hP | hQ
      · exact Or.inl (fun hQ' => Set.eq_empty_iff_forall_notMem.mp hdisj' z ⟨hP, hQ'⟩)
      · exact Or.inr (fun hP' => Set.eq_empty_iff_forall_notMem.mp hdisj' z ⟨hP', hQ⟩)
    have hLu : (L ∩ (γ '' (K' ∩ Ici r))ᶜ).Nonempty := by
      refine ⟨γ s, ?_, ?_⟩
      · rw [← hunion']; exact Or.inl (Set.mem_image_of_mem γ ⟨hs, le_of_lt hsr⟩)
      · intro hc
        obtain ⟨w, ⟨hw, hwr⟩, hweq⟩ := hc
        rw [mem_Ici] at hwr
        have hsw : s = w := hinj hs.1 hw.1 hweq.symm
        linarith
    have hLv : (L ∩ (γ '' (K' ∩ Iic r))ᶜ).Nonempty := by
      refine ⟨γ t, ?_, ?_⟩
      · rw [← hunion']; exact Or.inr (Set.mem_image_of_mem γ ⟨ht, le_of_lt hrt'⟩)
      · intro hc
        obtain ⟨w, ⟨hw, hwr⟩, hweq⟩ := hc
        rw [mem_Iic] at hwr
        have htw : t = w := hinj ht.1 hw.1 hweq.symm
        linarith
    obtain ⟨z, hz1, hzQ, hzP⟩ :=
      hLpre ((γ '' (K' ∩ Ici r))ᶜ) ((γ '' (K' ∩ Iic r))ᶜ)
        hQcomp.isClosed.isOpen_compl hPcomp.isClosed.isOpen_compl hLuv hLu hLv
    rw [← hunion'] at hz1
    rcases hz1 with h | h
    · exact hzP h
    · exact hzQ h
  -- conclude
  set a : ℝ := sInf K' with hadef
  set b : ℝ := sSup K' with hbdef
  have hbddB : BddBelow K' := hK'comp.isBounded.bddBelow
  have hbddA : BddAbove K' := hK'comp.isBounded.bddAbove
  have hab : a ≤ b := le_trans (csInf_le hbddB hK'ne.choose_spec)
    (le_csSup hbddA hK'ne.choose_spec)
  have hK'eq : K' = Icc a b := eq_Icc_of_isCompact_ordConnected hK'comp hK'ne hK'ord
  have haK : a ∈ K' := by rw [hK'eq]; exact ⟨le_rfl, hab⟩
  have hbK : b ∈ K' := by rw [hK'eq]; exact ⟨hab, le_rfl⟩
  have hLab : γ '' Icc a b = L := by rw [← hK'eq]; exact hK'image
  exact ⟨a, b, haK.1, hbK.1, hab, by rw [← hK'eq]; exact fun t ht => ht.1,
    by rw [hLab]; exact hLsep⟩

/-- **The planar Jordan arc theorem** (from Janiszewski's splitting principle for two compacta
meeting in a single point). -/
theorem arc_complement_interval' {γ : ℝ → Pt2} (hcont : Continuous γ)
    (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1)) :
    IsPathConnected ((γ '' Set.Icc (0:ℝ) 1)ᶜ : Set Pt2) :=
  arc_complement_interval_of_inter_singleton
    (fun {K L} hK hL {p} hKL {x y} hx hy h₁ h₂ =>
      janiszewski_subsingleton hK hL (by rw [hKL]; exact Set.subsingleton_singleton)
        hx hy h₁ h₂)
    hcont hinj

/-- **The target.**  The complement of the image of a compact subset of `ℝ` under a continuous
injection into the plane is path connected. -/
theorem plane_arc_nonseparation {K : Set ℝ} (hK : IsCompact K)
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} (hcont : ContinuousOn γ K)
    (hinj : Set.InjOn γ K) :
    IsPathConnected ((γ '' K)ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
  classical
  -- a point outside `γ '' K`
  have hex : ∃ z : Pt2, z ∉ γ '' K := by
    rcases K.eq_empty_or_nonempty with hKemp | ⟨t, ht⟩
    · exact ⟨0, by rw [hKemp]; simp⟩
    · obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Pt2)).mp
        (hK.image_of_continuousOn hcont).isBounded
      obtain ⟨w, hw⟩ := exists_ne (0 : Pt2)
      have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
      refine ⟨((|R| + 1) / ‖w‖) • w, ?_⟩
      intro hmem
      have h1 := hR hmem
      have h2 : ‖((|R| + 1) / ‖w‖) • w‖ = |R| + 1 := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ (ne_of_gt hwn)]
      rw [Metric.mem_closedBall, dist_zero_right, h2] at h1
      have h3 := le_abs_self R
      linarith
  obtain ⟨z₀, hz₀⟩ := hex
  refine ⟨z₀, hz₀, ?_⟩
  intro y hy
  by_contra hsep
  obtain ⟨a, b, haK, hbK, hab, hIccK, hsep'⟩ :=
    exists_subinterval_not_joinedIn hK hcont hinj hz₀ hy hsep
  rcases lt_or_eq_of_le hab with hlt | heq
  · -- the genuine arc case: parametrise the arc over `Icc 0 1`, extend to the line (Tietze), and
    -- apply the planar Jordan arc theorem
    have hbda : 0 < b - a := by linarith
    have hmap : ∀ u ∈ Set.Icc (0:ℝ) 1, a + u * (b - a) ∈ Set.Icc a b := by
      intro u hu
      have h1 : 0 ≤ u * (b - a) := mul_nonneg hu.1 (by linarith)
      have h2 : u * (b - a) ≤ b - a := by nlinarith [hu.2]
      constructor <;> linarith
    have hlin : ContinuousOn (fun u : ℝ => a + u * (b - a)) (Set.Icc (0:ℝ) 1) := by fun_prop
    have hγ₁ : ContinuousOn (fun u : ℝ => γ (a + u * (b - a))) (Set.Icc (0:ℝ) 1) :=
      (hcont.mono hIccK).comp hlin hmap
    obtain ⟨G, hG⟩ := ContinuousMap.exists_extension (Y := Pt2)
      (IsClosed.isClosedEmbedding_subtypeVal isClosed_Icc)
      (⟨(Set.Icc (0:ℝ) 1).domRestrict (fun u : ℝ => γ (a + u * (b - a))), hγ₁.domRestrict⟩ :
        C(↥(Set.Icc (0:ℝ) 1), Pt2))
    have hGeq : ∀ u ∈ Set.Icc (0:ℝ) 1, G u = γ (a + u * (b - a)) := by
      intro u hu
      have h := congrFun (congrArg (fun f : C(↥(Set.Icc (0:ℝ) 1), Pt2) =>
        (f : ↥(Set.Icc (0:ℝ) 1) → Pt2)) hG) ⟨u, hu⟩
      simpa using h
    have hGinj : Set.InjOn (fun u => G u) (Set.Icc (0:ℝ) 1) := by
      intro u hu v hv huv
      have h1 : γ (a + u * (b - a)) = γ (a + v * (b - a)) := by
        rw [← hGeq u hu, ← hGeq v hv]; exact huv
      have h2 : a + u * (b - a) = a + v * (b - a) :=
        hinj (hIccK (hmap u hu)) (hIccK (hmap v hv)) h1
      have h3 : u * (b - a) = v * (b - a) := by linarith
      exact mul_right_cancel₀ (ne_of_gt hbda) h3
    have harc := arc_complement_interval' G.continuous hGinj
    have hset : (fun u => G u) '' Set.Icc (0:ℝ) 1 = γ '' Set.Icc a b := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨a + u * (b - a), hmap u hu, (hGeq u hu).symm⟩
      · rintro ⟨t, ht, rfl⟩
        have hu : (t - a) / (b - a) ∈ Set.Icc (0:ℝ) 1 := by
          refine ⟨div_nonneg (by linarith [ht.1]) hbda.le, ?_⟩
          rw [div_le_one hbda]
          linarith [ht.2]
        refine ⟨(t - a) / (b - a), hu, ?_⟩
        show G ((t - a) / (b - a)) = γ t
        rw [hGeq ((t - a) / (b - a)) hu]
        have : a + (t - a) / (b - a) * (b - a) = t := by
          field_simp
          ring
        rw [this]
    rw [hset] at harc
    exact hsep' (harc.joinedIn z₀ (fun h => hz₀ (Set.image_mono hIccK h)) y
      (fun h => hy (Set.image_mono hIccK h)))
  · -- the degenerate case: `γ '' Icc a a = {γ a}` is a point
    subst heq
    rw [Set.Icc_self, Set.image_singleton] at hsep'
    exact hsep' (joinedIn_compl_singleton_pt2
      (fun h => hz₀ ⟨a, haK, h.symm⟩) (fun h => hy ⟨a, haK, h.symm⟩))

end Work.Whitney.PathTools
