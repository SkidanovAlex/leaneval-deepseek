import Mathlib.Analysis.Normed.Module.Convex
import Submission.Commons.Topology.Jordan.square_sets_top_bottom_continuum

set_option autoImplicit false
set_option maxHeartbeats 3200000

open Set Metric
open scoped Topology

namespace Commons.Topology.Jordan

noncomputable section

private def SepC (a b : ℂ) (S : Set ℂ) : Prop := ¬ JoinedIn Sᶜ a b

private theorem exists_minimal_closed_separating {K : Set ℂ} (hK : IsClosed K) {a b : ℂ}
    (hsep : ¬ JoinedIn Kᶜ a b) :
    ∃ S : Set ℂ, S ⊆ K ∧ IsClosed S ∧ ¬ JoinedIn Sᶜ a b ∧
      ∀ T : Set ℂ, T ⊆ S → IsClosed T → ¬ JoinedIn Tᶜ a b → T = S := by
  classical
  set 𝓢 : Set (Set ℂ) := {S | S ⊆ K ∧ IsClosed S ∧ ¬ JoinedIn Sᶜ a b} with h𝓢
  have hKmem : K ∈ 𝓢 := ⟨subset_rfl, hK, hsep⟩
  have hchain_cond : ∀ c ⊆ 𝓢, IsChain (fun x1 x2 : Set ℂ => x1 ⊆ x2) c →
      ∃ lb ∈ 𝓢, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hchain
    rcases c.eq_empty_or_nonempty with rfl | hcne
    · exact ⟨K, hKmem, by simp⟩
    · refine ⟨⋂₀ c, ?_, fun s hs => Set.sInter_subset_of_mem hs⟩
      have hsub : ⋂₀ c ⊆ K := by
        obtain ⟨s₀, hs₀⟩ := hcne
        exact (Set.sInter_subset_of_mem hs₀).trans (hc hs₀).1
      have hclosed : IsClosed (⋂₀ c) := isClosed_sInter (fun t ht => (hc ht).2.1)
      refine ⟨hsub, hclosed, ?_⟩
      rintro ⟨p, hp⟩
      have hPc : IsCompact (Set.range p) := isCompact_range p.continuous
      have hiff : (⋂ i : {s // s ∈ c}, (i : Set ℂ)) = ⋂₀ c := by
        rw [Set.sInter_eq_iInter]
      have hdisj : Set.range p ∩ (⋂ i : {s // s ∈ c}, (i : Set ℂ)) = ∅ := by
        rw [hiff, Set.eq_empty_iff_forall_notMem]
        rintro x ⟨⟨t, ht⟩, hxc⟩
        rw [← ht] at hxc
        exact hp t hxc
      obtain ⟨u, hu⟩ := hPc.elim_finite_subfamily_closed
        (fun i : {s // s ∈ c} => (i : Set ℂ)) (fun i => (hc i.2).2.1)
        (Set.disjoint_iff_inter_eq_empty.mpr hdisj)
      replace hu := Set.disjoint_iff_inter_eq_empty.mp hu
      have hune : u.Nonempty := by
        rcases u.eq_empty_or_nonempty with h | h
        · exfalso
          rw [h] at hu
          simp at hu
        · exact h
      obtain ⟨i₀, hi₀u, hi₀min⟩ := Finset.exists_minimal (s := u) hune
      have hle : ∀ j ∈ u, (i₀ : Set ℂ) ⊆ (j : Set ℂ) := by
        intro j hj
        rcases hchain.total i₀.2 j.2 with h | h
        · exact h
        · exact hi₀min hj h
      have hinter : (⋂ i ∈ u, (i : Set ℂ)) = (i₀ : Set ℂ) :=
        Set.Subset.antisymm (Set.biInter_subset_of_mem hi₀u) (Set.subset_iInter₂ hle)
      have hPi₀ : Set.range p ∩ (i₀ : Set ℂ) = ∅ := by rw [← hinter]; exact hu
      exact (hc i₀.2).2.2 ⟨p, fun t => by
        intro hmem
        exact Set.eq_empty_iff_forall_notMem.mp hPi₀ (p t) ⟨⟨t, rfl⟩, hmem⟩⟩
  obtain ⟨m, hmmin⟩ := zorn_superset 𝓢 hchain_cond
  refine ⟨m, hmmin.1.1, hmmin.1.2.1, hmmin.1.2.2, ?_⟩
  intro T hTm hTc hTs
  have hTmem : T ∈ 𝓢 := ⟨hTm.trans hmmin.1.1, hTc, hTs⟩
  exact Set.Subset.antisymm hTm (hmmin.2 hTmem hTm)

private lemma frontier_connectedComponentIn_subset {S : Set ℂ} (hS : IsClosed S) (c : ℂ) :
    ∀ z ∈ closure (connectedComponentIn Sᶜ c), z ∉ interior (connectedComponentIn Sᶜ c) → z ∈ S := by
  intro z hzcl hznotint
  by_contra hzS
  have hzSc : z ∈ Sᶜ := by simpa using hzS
  set M := connectedComponentIn Sᶜ c with hM
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hS.isOpen_compl z hzSc
  have hball : Metric.ball z r ⊆ connectedComponentIn Sᶜ z :=
    (convex_ball z r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr) hrsub
  have hne : M ≠ connectedComponentIn Sᶜ z := by
    intro heq
    refine hznotint (interior_maximal ?_ isOpen_ball (mem_ball_self hr))
    rw [heq]; exact hball
  have hdisj : M ∩ connectedComponentIn Sᶜ z = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hw1, hw2⟩
    exact hne ((connectedComponentIn_eq hw1).trans (connectedComponentIn_eq hw2).symm)
  have hsub : M ⊆ (Metric.ball z r)ᶜ := by
    intro w hw
    simp only [mem_compl_iff]
    intro hwb
    exact Set.eq_empty_iff_forall_notMem.mp hdisj w ⟨hw, hball hwb⟩
  have hcl : closure M ⊆ (Metric.ball z r)ᶜ :=
    closure_minimal hsub (isClosed_compl_iff.mpr isOpen_ball)
  exact hcl hzcl (mem_ball_self hr)

private lemma exists_mem_frontier_of_path {M : Set ℂ} {a b : ℂ} (p : Path a b) {t₀ : unitInterval}
    (h0 : p 0 ∈ closure M) (h1 : p t₀ ∉ closure M) :
    ∃ t, p t ∈ closure M ∧ p t ∉ interior M := by
  set A : Set unitInterval := {s | s ≤ t₀ ∧ p s ∈ closure M} with hA
  have h0t : (0 : unitInterval) ≤ t₀ := (Set.mem_Icc.mp t₀.2).1
  have hAne : A.Nonempty := ⟨0, h0t, h0⟩
  have hAcl : IsClosed A :=
    (isClosed_Iic.preimage continuous_subtype_val).inter (isClosed_closure.preimage p.continuous)
  have hAc : IsCompact A := hAcl.isCompact
  obtain ⟨t, htA, htmax⟩ := hAc.exists_isMaxOn hAne continuous_id.continuousOn
  have htle : t ≤ t₀ := htA.1
  have htcl : p t ∈ closure M := htA.2
  have htne : t ≠ t₀ := by intro h; rw [h] at htcl; exact h1 htcl
  have htlt : t < t₀ := lt_of_le_of_ne htle htne
  refine ⟨t, htcl, ?_⟩
  intro hint
  obtain ⟨e, he, hesub⟩ := Metric.mem_nhds_iff.mp
    (p.continuous.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint))
  have ht0 : (0:ℝ) ≤ (t:ℝ) := (Set.mem_Icc.mp t.2).1
  have htlt' : (t:ℝ) < (t₀:ℝ) := htlt
  set sr : ℝ := min (t₀ : ℝ) ((t : ℝ) + e/2) with hsr
  have hsrt : (t:ℝ) < sr := lt_min htlt' (by linarith)
  have hsr0 : 0 ≤ sr := le_min (le_trans ht0 (le_of_lt htlt')) (by linarith)
  have hsrt₀ : sr ≤ (t₀:ℝ) := min_le_left _ _
  have hsrt1 : sr ≤ 1 := le_trans hsrt₀ (Set.mem_Icc.mp t₀.2).2
  have hdist : |sr - (t:ℝ)| < e := by
    rw [abs_of_pos (sub_pos.mpr hsrt)]
    have : sr ≤ (t:ℝ) + e/2 := min_le_right _ _
    linarith
  set s : unitInterval := ⟨sr, Set.mem_Icc.mpr ⟨hsr0, hsrt1⟩⟩ with hss
  have hsv : (s : ℝ) = sr := by rw [hss]
  have hstt : t < s := by rw [← Subtype.coe_lt_coe, hsv]; exact hsrt
  have hslet : s ≤ t₀ := by rw [← Subtype.coe_le_coe, hsv]; exact hsrt₀
  have hsd : dist s t < e := by
    rw [Subtype.dist_eq, hsv, Real.dist_eq]; exact hdist
  have hsmem : p s ∈ interior M := hesub hsd
  have hsA : s ∈ A := ⟨hslet, subset_closure (interior_subset hsmem)⟩
  exact absurd (htmax hsA) (not_le.mpr hstt)

private lemma sep_symm {a b : ℂ} {S : Set ℂ} (h : SepC a b S) : SepC b a S :=
  fun h' => h h'.symm

private lemma subset_frontier_of_minimal {S : Set ℂ} (hScl : IsClosed S) {a b : ℂ} (ha : a ∈ Sᶜ)
    (hSsep : SepC a b S)
    (hSmin : ∀ T : Set ℂ, T ⊆ S → IsClosed T → SepC a b T → T = S) {z : ℂ} (hz : z ∈ S) :
    z ∈ closure (connectedComponentIn Sᶜ a) ∧ z ∉ interior (connectedComponentIn Sᶜ a) := by
  set M := connectedComponentIn Sᶜ a with hM
  have hMopen : IsOpen M := hScl.isOpen_compl.connectedComponentIn
  have haM : a ∈ M := mem_connectedComponentIn ha
  have hzM : z ∉ M := fun h => (connectedComponentIn_subset Sᶜ a h) hz
  have hzint : z ∉ interior M := by rw [hMopen.interior_eq]; exact hzM
  by_contra hcon
  have hzcl : z ∉ closure M := fun h => hcon ⟨h, hzint⟩
  set S' : Set ℂ := S ∩ closure M with hS'
  have hS'cl : IsClosed S' := hScl.inter isClosed_closure
  have hS'sub : S' ⊆ S := inter_subset_left
  have hS'proper : S' ≠ S := by
    intro h; have : z ∈ S' := by rw [h]; exact hz
    exact hzcl this.2
  have hS'notsep : ¬ SepC a b S' := fun hsep' => hS'proper (hSmin S' hS'sub hS'cl hsep')
  obtain ⟨π, hπ⟩ := not_not.mp hS'notsep
  have hhits : ∃ t, π t ∈ S := by
    by_contra h
    push Not at h
    exact hSsep ⟨π, fun t => h t⟩
  obtain ⟨t₀, ht₀⟩ := hhits
  have ht₀cl : π t₀ ∉ closure M := by
    intro hcl
    exact (hπ t₀) ⟨ht₀, hcl⟩
  have hπ0 : π 0 ∈ closure M := subset_closure (by rw [π.source]; exact haM)
  obtain ⟨t, htcl, htnotint⟩ := exists_mem_frontier_of_path π hπ0 ht₀cl
  have htS : π t ∈ S := frontier_connectedComponentIn_subset hScl a (π t) htcl htnotint
  exact (hπ t) ⟨htS, htcl⟩

private theorem janiszewski_closed_disjoint_aux {A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) {a b : ℂ} (ha : a ∉ A ∪ B) (hb : b ∉ A ∪ B)
    (hAx : JoinedIn Aᶜ a b) (hBx : JoinedIn Bᶜ a b) : JoinedIn (A ∪ B)ᶜ a b := by
  classical
  by_contra hsep
  have hABc : IsClosed (A ∪ B) := hA.union hB
  obtain ⟨S, hSK, hScl, hSsep, hSmin⟩ := exists_minimal_closed_separating hABc hsep
  have hSc : IsOpen Sᶜ := hScl.isOpen_compl
  have haS : a ∈ Sᶜ := fun h => ha (hSK h)
  have hbS : b ∈ Sᶜ := fun h => hb (hSK h)
  set M : Set ℂ := connectedComponentIn Sᶜ a with hM
  set N : Set ℂ := connectedComponentIn Sᶜ b with hN
  have hMopen : IsOpen M := hSc.connectedComponentIn
  have hNopen : IsOpen N := hSc.connectedComponentIn
  have haM : a ∈ M := mem_connectedComponentIn haS
  have hbN : b ∈ N := mem_connectedComponentIn hbS
  have hMsub : M ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hNsub : N ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hMpath : IsPathConnected M :=
    (hMopen.isConnected_iff_isPathConnected).mp ⟨⟨a, haM⟩, isPreconnected_connectedComponentIn⟩
  have hNpath : IsPathConnected N :=
    (hNopen.isConnected_iff_isPathConnected).mp ⟨⟨b, hbN⟩, isPreconnected_connectedComponentIn⟩
  have hMN : M ≠ N := by
    intro heq
    have hbM : b ∈ M := heq ▸ hbN
    exact hSsep ((hMpath.joinedIn a haM b hbM).mono hMsub)
  have hSBne : (S ∩ B).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hSA : S ⊆ A := by
      intro z hz
      rcases hSK hz with hA' | hB'
      · exact hA'
      · exact (Set.eq_empty_iff_forall_notMem.mp h z ⟨hz, hB'⟩).elim
    exact hSsep (hAx.mono (fun z hz hzS => hz (hSA hzS)))
  have hSAne : (S ∩ A).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hSB : S ⊆ B := by
      intro z hz
      rcases hSK hz with hA' | hB'
      · exact (Set.eq_empty_iff_forall_notMem.mp h z ⟨hz, hA'⟩).elim
      · exact hB'
    exact hSsep (hBx.mono (fun z hz hzS => hz (hSB hzS)))
  have hSAcl : IsClosed (S ∩ A) := hScl.inter hA
  have hSBcl : IsClosed (S ∩ B) := hScl.inter hB
  have hdisj' : Disjoint (S ∩ A) (S ∩ B) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact Set.disjoint_left.mp hdisj hz1.2 hz2.2
  obtain ⟨h0, hh0⟩ := hSAne
  obtain ⟨k0, hk0⟩ := hSBne
  have h0B : h0 ∉ S ∩ B := fun h => Set.disjoint_left.mp hdisj' hh0 h
  have k0A : k0 ∉ S ∩ A := fun h => Set.disjoint_left.mp hdisj' h hk0
  have h0k0 : h0 ≠ k0 := fun h => h0B (h ▸ hk0)
  have hpos1 : 0 < infDist h0 (S ∩ B) := (hSBcl.notMem_iff_infDist_pos ⟨k0, hk0⟩).1 h0B
  have hpos2 : 0 < infDist k0 (S ∩ A) := (hSAcl.notMem_iff_infDist_pos ⟨h0, hh0⟩).1 k0A
  have hpos3 : 0 < dist h0 k0 := dist_pos.mpr h0k0
  set D : ℝ := min (min (infDist h0 (S ∩ B)) (infDist k0 (S ∩ A))) (dist h0 k0) with hD
  set ε : ℝ := D / 10 with hε
  have hεpos : 0 < ε := by rw [hε, hD]; positivity
  have hε1 : 10 * ε ≤ infDist h0 (S ∩ B) := by
    have h : D ≤ infDist h0 (S ∩ B) :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    rw [hε]; linarith
  have hε2 : 10 * ε ≤ infDist k0 (S ∩ A) := by
    have h : D ≤ infDist k0 (S ∩ A) :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    rw [hε]; linarith
  have hε3 : 10 * ε ≤ dist h0 k0 := by
    have h : D ≤ dist h0 k0 := min_le_right _ _
    rw [hε]; linarith
  -- frontier facts
  have hh0fr := subset_frontier_of_minimal hScl haS hSsep hSmin hh0.1
  have hk0fr := subset_frontier_of_minimal hScl haS hSsep hSmin hk0.1
  have hminsymm : ∀ T : Set ℂ, T ⊆ S → IsClosed T → SepC b a T → T = S :=
    fun T h1 h2 h3 => hSmin T h1 h2 (sep_symm h3)
  have hh0frN := subset_frontier_of_minimal hScl hbS (sep_symm hSsep) hminsymm hh0.1
  have hk0frN := subset_frontier_of_minimal hScl hbS (sep_symm hSsep) hminsymm hk0.1
  obtain ⟨a₁, ha₁M, ha₁h0⟩ := Metric.mem_closure_iff.mp hh0fr.1 ε hεpos
  obtain ⟨c₁, hc₁N, hc₁h0⟩ := Metric.mem_closure_iff.mp hh0frN.1 ε hεpos
  obtain ⟨b₁, hb₁M, hb₁k0⟩ := Metric.mem_closure_iff.mp hk0fr.1 ε hεpos
  obtain ⟨d₁, hd₁N, hd₁k0⟩ := Metric.mem_closure_iff.mp hk0frN.1 ε hεpos
  have ha₁_ball : a₁ ∈ Metric.ball h0 ε := by rw [Metric.mem_ball]; rwa [dist_comm]
  have hc₁_ball : c₁ ∈ Metric.ball h0 ε := by rw [Metric.mem_ball]; rwa [dist_comm]
  have hb₁_ball : b₁ ∈ Metric.ball k0 ε := by rw [Metric.mem_ball]; rwa [dist_comm]
  have hd₁_ball : d₁ ∈ Metric.ball k0 ε := by rw [Metric.mem_ball]; rwa [dist_comm]
  have hseg_ac_ball : segment ℝ a₁ c₁ ⊆ Metric.ball h0 ε :=
    (convex_ball h0 ε).segment_subset ha₁_ball hc₁_ball
  have hseg_bd_ball : segment ℝ b₁ d₁ ⊆ Metric.ball k0 ε :=
    (convex_ball k0 ε).segment_subset hb₁_ball hd₁_ball
  have hball_h0_B : Disjoint (Metric.ball h0 ε) (S ∩ B) := by
    rw [Set.disjoint_left]
    intro z hz hzB
    have h1 : dist h0 z < ε := by rw [Metric.mem_ball] at hz; rwa [dist_comm] at hz
    have h2 : infDist h0 (S ∩ B) ≤ dist h0 z := infDist_le_dist_of_mem hzB
    linarith
  have hball_k0_A : Disjoint (Metric.ball k0 ε) (S ∩ A) := by
    rw [Set.disjoint_left]
    intro z hz hzA
    have h1 : dist k0 z < ε := by rw [Metric.mem_ball] at hz; rwa [dist_comm] at hz
    have h2 : infDist k0 (S ∩ A) ≤ dist k0 z := infDist_le_dist_of_mem hzA
    linarith
  have hball_disj : Disjoint (Metric.ball h0 ε) (Metric.ball k0 ε) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h1 : dist h0 z < ε := by rw [Metric.mem_ball] at hz1; rwa [dist_comm] at hz1
    have h2 : dist z k0 < ε := by rw [Metric.mem_ball] at hz2; exact hz2
    have h4 : dist h0 k0 ≤ dist h0 z + dist z k0 := dist_triangle _ _ _
    linarith
  -- the two segments meet S
  have hseg_ac_S : (segment ℝ a₁ c₁ ∩ S).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : segment ℝ a₁ c₁ ⊆ Sᶜ := by
      intro z hz
      rw [Set.mem_compl_iff]
      intro hzS
      exact Set.eq_empty_iff_forall_notMem.mp hcon z ⟨hz, hzS⟩
    have hpre : IsPreconnected (segment ℝ a₁ c₁) := (convex_segment a₁ c₁).isPreconnected
    have h1 : segment ℝ a₁ c₁ ⊆ connectedComponentIn Sᶜ a₁ :=
      hpre.subset_connectedComponentIn (left_mem_segment ℝ a₁ c₁) hsub
    have h2 : connectedComponentIn Sᶜ a₁ = M := by rw [hM, connectedComponentIn_eq ha₁M]
    rw [h2] at h1
    have hc₁M : c₁ ∈ M := h1 (right_mem_segment ℝ a₁ c₁)
    exact hMN ((hM.trans (connectedComponentIn_eq hc₁M)).trans
      ((hN.trans (connectedComponentIn_eq hc₁N)).symm))
  have hseg_bd_S : (segment ℝ b₁ d₁ ∩ S).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : segment ℝ b₁ d₁ ⊆ Sᶜ := by
      intro z hz
      rw [Set.mem_compl_iff]
      intro hzS
      exact Set.eq_empty_iff_forall_notMem.mp hcon z ⟨hz, hzS⟩
    have hpre : IsPreconnected (segment ℝ b₁ d₁) := (convex_segment b₁ d₁).isPreconnected
    have h1 : segment ℝ b₁ d₁ ⊆ connectedComponentIn Sᶜ b₁ :=
      hpre.subset_connectedComponentIn (left_mem_segment ℝ b₁ d₁) hsub
    have h2 : connectedComponentIn Sᶜ b₁ = M := by rw [hM, connectedComponentIn_eq hb₁M]
    rw [h2] at h1
    have hd₁M : d₁ ∈ M := h1 (right_mem_segment ℝ b₁ d₁)
    exact hMN ((hM.trans (connectedComponentIn_eq hd₁M)).trans
      ((hN.trans (connectedComponentIn_eq hd₁N)).symm))
  obtain ⟨w, hwseg, hwS⟩ := hseg_ac_S
  obtain ⟨v, hvseg, hvS⟩ := hseg_bd_S
  have hwA : w ∈ S ∩ A := by
    refine ⟨hwS, ?_⟩
    rcases hSK hwS with h | h
    · exact h
    · exfalso
      exact Set.disjoint_left.mp hball_h0_B (hseg_ac_ball hwseg) ⟨hwS, h⟩
  have hvB : v ∈ S ∩ B := by
    refine ⟨hvS, ?_⟩
    rcases hSK hvS with h | h
    · exfalso
      exact Set.disjoint_left.mp hball_k0_A (hseg_bd_ball hvseg) ⟨hvS, h⟩
    · exact h
  -- the ladder
  obtain ⟨α, hα⟩ := hMpath.joinedIn a₁ ha₁M b₁ hb₁M
  obtain ⟨β, hβ⟩ := hNpath.joinedIn c₁ hc₁N d₁ hd₁N
  let ss : ℂ → unitInterval := fun z => Set.projIcc (0:ℝ) 1 (by norm_num) ((z.re + 1) / 2)
  let tt : ℂ → unitInterval := fun z => Set.projIcc (0:ℝ) 1 (by norm_num) ((z.im + 1) / 2)
  let Φ : ℂ → ℂ := fun z => (1 - ((tt z : unitInterval) : ℝ)) • α (ss z)
    + ((tt z : unitInterval) : ℝ) • β (ss z)
  have hΦcont : Continuous Φ := by
    simp only [Φ, ss, tt]
    fun_prop
  let E' : Set ℂ := Qsq ∩ Φ ⁻¹' (S ∩ A)
  let F' : Set ℂ := Qsq ∩ Φ ⁻¹' (S ∩ B)
  have hE'cl : IsClosed E' := by
    show IsClosed (Qsq ∩ Φ ⁻¹' (S ∩ A))
    exact isClosed_Qsq.inter (hSAcl.preimage hΦcont)
  have hF'cl : IsClosed F' := by
    show IsClosed (Qsq ∩ Φ ⁻¹' (S ∩ B))
    exact isClosed_Qsq.inter (hSBcl.preimage hΦcont)
  have hE'F'disj : Disjoint E' F' := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact Set.disjoint_left.mp hdisj' hz1.2 hz2.2
  have hE'right : ∀ z ∈ E', z.re < 1 := by
    intro z hz
    have hzQ : z ∈ Qsq := hz.1
    have hzA : Φ z ∈ S ∩ A := hz.2
    have hle : z.re ≤ 1 := (Set.mem_Icc.mp hzQ.1).2
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hz1 : (z.re + 1) / 2 = 1 := by rw [h]; ring
      have hss1 : ss z = 1 := by
        simp only [ss]
        rw [hz1]
        exact Set.projIcc_of_mem _ (by norm_num)
      have hΦval : Φ z = (1 - ((tt z : unitInterval) : ℝ)) • b₁
          + ((tt z : unitInterval) : ℝ) • d₁ := by
        simp only [Φ, hss1, α.target, β.target]
      have htmem : ((tt z : unitInterval) : ℝ) ∈ Set.Icc (0:ℝ) 1 := (tt z).2
      have hseg : Φ z ∈ segment ℝ b₁ d₁ := by
        rw [segment_eq_image]
        exact ⟨((tt z : unitInterval) : ℝ), htmem, by rw [hΦval]⟩
      exact Set.disjoint_left.mp hball_k0_A (hseg_bd_ball hseg) hzA
  have hF'left : ∀ z ∈ F', -1 < z.re := by
    intro z hz
    have hzQ : z ∈ Qsq := hz.1
    have hzB : Φ z ∈ S ∩ B := hz.2
    have hle : -1 ≤ z.re := (Set.mem_Icc.mp hzQ.1).1
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hz1 : (z.re + 1) / 2 = 0 := by rw [← h]; ring
      have hss0 : ss z = 0 := by
        simp only [ss]
        rw [hz1]
        exact Set.projIcc_of_mem _ (by norm_num)
      have hΦval : Φ z = (1 - ((tt z : unitInterval) : ℝ)) • a₁
          + ((tt z : unitInterval) : ℝ) • c₁ := by
        simp only [Φ, hss0, α.source, β.source]
      have htmem : ((tt z : unitInterval) : ℝ) ∈ Set.Icc (0:ℝ) 1 := (tt z).2
      have hseg : Φ z ∈ segment ℝ a₁ c₁ := by
        rw [segment_eq_image]
        exact ⟨((tt z : unitInterval) : ℝ), htmem, by rw [hΦval]⟩
      exact Set.disjoint_left.mp hball_h0_B (hseg_ac_ball hseg) hzB
  have hE'left : ∃ z ∈ E', z.re = -1 := by
    rw [segment_eq_image] at hwseg
    obtain ⟨θ, hθ, hθw⟩ := hwseg
    refine ⟨Complex.mk (-1) (2 * θ - 1), ?_, ?_⟩
    · have hQ : Complex.mk (-1) (2 * θ - 1) ∈ Qsq :=
        ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
      have hA' : Φ (Complex.mk (-1) (2 * θ - 1)) ∈ S ∩ A := by
        have hre : (Complex.mk (-1) (2 * θ - 1)).re = -1 := rfl
        have him : (Complex.mk (-1) (2 * θ - 1)).im = 2 * θ - 1 := rfl
        have hss0 : ss (Complex.mk (-1) (2 * θ - 1)) = 0 := by
          simp only [ss]
          rw [show ((-1 : ℝ) + 1) / 2 = (0:ℝ) by norm_num]
          exact Set.projIcc_of_mem _ (by norm_num)
        have htt : ((tt (Complex.mk (-1) (2 * θ - 1)) : unitInterval) : ℝ) = θ := by
          simp only [tt]
          rw [show ((2 * θ - 1 : ℝ) + 1) / 2 = θ by ring]
          exact congrArg Subtype.val (Set.projIcc_of_mem _ hθ)
        have hΦval : Φ (Complex.mk (-1) (2 * θ - 1)) = (1 - θ) • a₁ + θ • c₁ := by
          simp only [Φ, hss0, htt, α.source, β.source]
        have hθw' : (1 - θ) • a₁ + θ • c₁ = w := hθw
        rw [hΦval, hθw']
        exact hwA
      exact ⟨hQ, hA'⟩
    · rfl
  have hF'right : ∃ z ∈ F', z.re = 1 := by
    rw [segment_eq_image] at hvseg
    obtain ⟨θ, hθ, hθv⟩ := hvseg
    refine ⟨Complex.mk 1 (2 * θ - 1), ?_, ?_⟩
    · have hQ : Complex.mk 1 (2 * θ - 1) ∈ Qsq :=
        ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
      have hA' : Φ (Complex.mk 1 (2 * θ - 1)) ∈ S ∩ B := by
        have hre : (Complex.mk 1 (2 * θ - 1)).re = 1 := rfl
        have him : (Complex.mk 1 (2 * θ - 1)).im = 2 * θ - 1 := rfl
        have hss1 : ss (Complex.mk 1 (2 * θ - 1)) = 1 := by
          simp only [ss]
          rw [show ((1 : ℝ) + 1) / 2 = (1:ℝ) by norm_num]
          exact Set.projIcc_of_mem _ (by norm_num)
        have htt : ((tt (Complex.mk 1 (2 * θ - 1)) : unitInterval) : ℝ) = θ := by
          simp only [tt]
          rw [show ((2 * θ - 1 : ℝ) + 1) / 2 = θ by ring]
          exact congrArg Subtype.val (Set.projIcc_of_mem _ hθ)
        have hΦval : Φ (Complex.mk 1 (2 * θ - 1)) = (1 - θ) • b₁ + θ • d₁ := by
          simp only [Φ, hss1, htt, α.target, β.target]
        have hθv' : (1 - θ) • b₁ + θ • d₁ = v := hθv
        rw [hΦval, hθv']
        exact hvB
      exact ⟨hQ, hA'⟩
    · rfl
  obtain ⟨K, hKsub, hKdisjE, hKdisjF, hKpre, hKcpt, hKtop, hKbot⟩ :=
    square_sets_top_bottom_continuum hE'cl hF'cl (fun z hz => hz.1) (fun z hz => hz.1)
      hE'F'disj hE'right hF'left hE'left hF'right
  let Kc : Set ℂ := Φ '' K
  have hKcpre : IsPreconnected Kc := by
    show IsPreconnected (Φ '' K)
    exact hKpre.image Φ hΦcont.continuousOn
  have hKcS : Kc ⊆ Sᶜ := by
    intro u hu
    obtain ⟨z, hzK, rfl⟩ := hu
    rw [Set.mem_compl_iff]
    intro huS
    have hzQ : z ∈ Qsq := hKsub hzK
    rcases hSK huS with h | h
    · exact Set.disjoint_left.mp hKdisjE hzK ⟨hzQ, huS, h⟩
    · exact Set.disjoint_left.mp hKdisjF hzK ⟨hzQ, huS, h⟩
  have hKcM : (Kc ∩ M).Nonempty := by
    obtain ⟨z, hzK, hzim⟩ := hKbot
    refine ⟨Φ z, ⟨⟨z, hzK, rfl⟩, ?_⟩⟩
    have htt : (tt z : unitInterval) = 0 := by
      simp only [tt]
      have h2 : (z.im + 1) / 2 = 0 := by rw [hzim]; ring
      rw [h2]
      exact Set.projIcc_of_mem _ (by norm_num)
    have hΦval : Φ z = α (ss z) := by
      simp only [Φ, htt]
      simp
    rw [hΦval]
    exact hα (ss z)
  have hKcN : (Kc ∩ N).Nonempty := by
    obtain ⟨z, hzK, hzim⟩ := hKtop
    refine ⟨Φ z, ⟨⟨z, hzK, rfl⟩, ?_⟩⟩
    have htt : (tt z : unitInterval) = 1 := by
      simp only [tt]
      have h2 : (z.im + 1) / 2 = 1 := by rw [hzim]; ring
      rw [h2]
      exact Set.projIcc_of_mem _ (by norm_num)
    have hΦval : Φ z = β (ss z) := by
      simp only [Φ, htt]
      simp
    rw [hΦval]
    exact hβ (ss z)
  obtain ⟨u, huKc, huM⟩ := hKcM
  obtain ⟨v', hv'Kc, hv'N⟩ := hKcN
  have hKcsubM : Kc ⊆ M := by
    have h1 : Kc ⊆ connectedComponentIn Sᶜ u := hKcpre.subset_connectedComponentIn huKc hKcS
    have h2 : connectedComponentIn Sᶜ u = M := by rw [hM, connectedComponentIn_eq huM]
    rw [h2] at h1
    exact h1
  have hv'M : v' ∈ M := hKcsubM hv'Kc
  have hMNeq : M = N :=
    (hM.trans (connectedComponentIn_eq hv'M)).trans
      ((hN.trans (connectedComponentIn_eq hv'N)).symm)
  exact hMN hMNeq


/-- **Irreducible-cut theorem, closed (non-compact) form.** If a closed subset `K` of the
plane separates two points `a`, `b` (i.e. `a` and `b` cannot be joined by a path in `Kᶜ`),
then some closed connected subset `S ⊆ K` separates them as well.  (The connexion is via
Janiszewski's theorem / the Phragmén–Brouwer separation property of the plane.) -/
theorem closed_separates_continuum {K : Set ℂ} (hK : IsClosed K) {a b : ℂ}
    (ha : a ∉ K) (hb : b ∉ K)
    (hsep : ¬ ∃ p : Path a b, ∀ t, p t ∉ K) :
    ∃ S : Set ℂ, S ⊆ K ∧ IsClosed S ∧ IsPreconnected S ∧
      ¬ ∃ p : Path a b, ∀ t, p t ∉ S := by
  have hsep' : ¬ JoinedIn Kᶜ a b := hsep
  obtain ⟨S, hSK, hScl, hSsep, hmin⟩ := exists_minimal_closed_separating hK hsep'
  refine ⟨S, hSK, hScl, ?_, hSsep⟩
  by_contra hnp
  rw [isPreconnected_iff_subset_of_disjoint] at hnp
  push Not at hnp
  obtain ⟨u, v, huopen, hvopen, hSuv, hinter, hnu, hnv⟩ := hnp
  set A : Set ℂ := S ∩ vᶜ with hA
  set B : Set ℂ := S ∩ uᶜ with hB
  have hAcl : IsClosed A := by
    rw [hA]
    exact hScl.inter hvopen.isClosed_compl
  have hBcl : IsClosed B := by
    rw [hB]
    exact hScl.inter huopen.isClosed_compl
  have hAB : A ∪ B = S := by
    rw [hA, hB]
    ext x; constructor
    · rintro (⟨hxS, -⟩ | ⟨hxS, -⟩) <;> exact hxS
    · intro hxS
      by_cases hxu : x ∈ u
      · refine Or.inl ⟨hxS, ?_⟩
        simp only [Set.mem_compl_iff]
        intro hxv
        exact Set.eq_empty_iff_forall_notMem.mp hinter x ⟨hxS, hxu, hxv⟩
      · exact Or.inr ⟨hxS, by simpa using hxu⟩
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro x ⟨hxS, hxv⟩ ⟨-, hxu⟩
    rcases hSuv hxS with h | h
    · exact hxu h
    · exact hxv h
  have hAne : A.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hAe
    apply hnv
    intro x hxS
    by_contra hxv
    have hxA : x ∈ A := ⟨hxS, by simpa using hxv⟩
    rw [hAe] at hxA
    exact hxA
  have hBne : B.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hBe
    apply hnu
    intro x hxS
    by_contra hxu
    have hxB : x ∈ B := ⟨hxS, by simpa using hxu⟩
    rw [hBe] at hxB
    exact hxB
  have hAneS : A ≠ S := by
    intro hAS
    obtain ⟨y, hyB⟩ := hBne
    have hyS : y ∈ S := by rw [← hAB]; exact Or.inr hyB
    exact Set.disjoint_left.mp hdisj (by rw [hAS]; exact hyS) hyB
  have hBneS : B ≠ S := by
    intro hBS
    obtain ⟨y, hyA⟩ := hAne
    have hyS : y ∈ S := by rw [← hAB]; exact Or.inl hyA
    exact Set.disjoint_left.mp hdisj hyA (by rw [hBS]; exact hyS)
  have hAsep : JoinedIn Aᶜ a b := by
    by_contra hcon
    exact hAneS (hmin A Set.inter_subset_left hAcl hcon)
  have hBsep : JoinedIn Bᶜ a b := by
    by_contra hcon
    exact hBneS (hmin B Set.inter_subset_left hBcl hcon)
  have haAB : a ∉ A ∪ B := by rw [hAB]; exact fun h => ha (hSK h)
  have hbAB : b ∉ A ∪ B := by rw [hAB]; exact fun h => hb (hSK h)
  have hres := janiszewski_closed_disjoint_aux hAcl hBcl hdisj haAB hbAB hAsep hBsep
  rw [hAB] at hres
  exact hSsep hres

end

end Commons.Topology.Jordan