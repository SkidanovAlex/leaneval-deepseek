import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_state
import Submission.Work.Noncompact.CompressionTube.collar_peel

/-!
# The step of the collar construction

From the level-`m` datum `st` (`LInv K L U (levK …) m st`) this file produces the level-`(m+1)`
datum `st'` with its invariant and the cross-level conditions `LStep`, by a single application of
the peel lemma `peel_arcs`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Noncompact.CompressionTube

open Set Topology

theorem collar_step {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    {K : ℕ → Set M} {B : Set M}
    (hB : ∀ K' : Set M, IsCompact K' → (B ∩ K').Finite)
    (hKc : ∀ i, IsCompact (K i)) (hK0 : K 0 = ∅) (hKsub : ∀ i, K i ⊆ interior (K (i+1)))
    (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    {L U : ℕ → Set M} (hLc : ∀ j, IsClosed (L j)) (hAL : ∀ j, K (j+1) ⊆ interior (L j))
    (hLB : ∀ j, L j ⊆ interior (K (j+2)))
    (hLpf : ∀ j (x : M), x ∉ L j → ¬ IsCompact (closure (connectedComponentIn ((L j)ᶜ) x)))
    (hUo : ∀ j, IsOpen (U j)) (hUL : ∀ j, Disjoint (U j) (L j))
    (hLavoidB : ∀ j, Disjoint (L j) (B ∩ (K (j+2) \ K (j+1))))
    (hpieces : ∀ j z, z ∈ frontier (L j) →
      ∃ (x : M) (b : Work.Whitney.PathTools.ChartBall n M Set.univ x),
        z ∈ b.K ∧ b.c.symm '' Metric.ball (b.c x) b.ρ ⊆ U j)
    {m : ℕ} {st : LSt B} (hst : LInv K L U (levK K hKuniv) m st) :
    ∃ st' : LSt B, LInv K L U (levK K hKuniv) (m+1) st' ∧
      LStep K L (levK K hKuniv) m st st' := by
  classical
  haveI hi1 : Fintype {b : B // levK K hKuniv b ≤ m+1} := by
    haveI : Fintype ↥(B ∩ K (m+2)) := (hB (K (m+2)) (hKc (m+2))).fintype
    refine Fintype.ofInjective
      (fun b : {b : B // levK K hKuniv b ≤ m+1} =>
        (⟨(b.1 : M), ⟨b.1.2, ?_⟩⟩ : ↥(B ∩ K (m+2)))) ?_
    · exact monotone_K K hKsub (by omega) (levK_mem_succ hK0 hKuniv b.1)
    · intro b b' h
      have h1 : (b.1 : M) = (b'.1 : M) := congrArg (fun x : ↥(B ∩ K (m+2)) => (x : M)) h
      exact Subtype.ext (Subtype.ext h1)
  set A := {b : B // levK K hKuniv b ≤ m+1} with hAdef
  set k : ℕ := Fintype.card A with hkdef
  set e : A ≃ Fin k := Fintype.equivFin A with hedef
  -- the underlying `B`-point of each index
  set bb : Fin k → B := fun i => (e.symm i).1 with hbbdef
  -- the strands active already at level `m`
  set K0 := {b : B // levK K hKuniv b ≤ m} with hK0def
  haveI hi0 : Fintype K0 := by
    haveI : Fintype ↥(B ∩ K (m+1)) := (hB (K (m+1)) (hKc (m+1))).fintype
    refine Fintype.ofInjective
      (fun b : K0 => (⟨(b.1 : M), ⟨b.1.2, ?_⟩⟩ : ↥(B ∩ K (m+1)))) ?_
    · exact monotone_K K hKsub (by omega) (levK_mem_succ hK0 hKuniv b.1)
    · intro b b' h
      have h1 : (b.1 : M) = (b'.1 : M) := congrArg (fun x : ↥(B ∩ K (m+1)) => (x : M)) h
      exact Subtype.ext (Subtype.ext h1)
  set r : ℕ := Fintype.card K0 with hrdef
  set e0 : K0 ≃ Fin r := Fintype.equivFin K0 with he0def
  have hK0A : ∀ b : K0, levK K hKuniv b.1 ≤ m+1 := fun b => le_trans b.2 (by omega)
  have hK0A' : ∀ b : B, levK K hKuniv b ≤ m → levK K hKuniv b ≤ m+1 := fun b h => le_trans h (by omega)
  -- the start points
  set s : Fin k → M := fun i =>
    if hb : levK K hKuniv (bb i) ≤ m then st.γ (bb i) 1 else (bb i : M) with hsdef
  -- the slits: the level-`m` spikes, reparametrised
  set sfun : Fin r → B := fun j => (e0.symm j).1 with hsfundef
  set clip : Fin r → Fin k := fun j => e ⟨sfun j, hK0A (e0.symm j)⟩ with hclipdef
  set slt : Fin r → ℝ → M := fun j u => st.γ (sfun j) ((1-u) * st.τ (sfun j) + u) with hsltdef
  -- the avoidance sets
  set F : Fin k → Set M := fun i =>
    ((B ∩ K (m+3) : Set M) \ {s i}) ∪ {x : M | ∃ i' : Fin k, i' ≠ i ∧ x = s i'} with hFdef
  -- elementary facts about the start points
  have hbb_of : ∀ i : Fin k, bb i = (e.symm i).1 := fun i => rfl
  have hlev_b : ∀ i : Fin k, levK K hKuniv (bb i) ≤ m+1 := fun i => (e.symm i).2
  have hs_at : ∀ (i : Fin k) (hb : levK K hKuniv (bb i) ≤ m), s i = st.γ (bb i) 1 := by
    intro i hb
    simp only [hsdef]
    simp only [dif_pos hb]
  have hs_notat : ∀ (i : Fin k) (hb : ¬ levK K hKuniv (bb i) ≤ m), s i = (bb i : M) := by
    intro i hb
    simp only [hsdef]
    simp only [dif_neg hb]
  have hs_le : ∀ (b : B) (hb : levK K hKuniv b ≤ m), s (e ⟨b, hK0A' b hb⟩) = st.γ b 1 := by
    intro b hb
    have h2 : bb (e ⟨b, hK0A' b hb⟩) = b := by
      rw [hbb_of]
      exact congrArg Subtype.val (Equiv.symm_apply_apply e ⟨b, hK0A' b hb⟩)
    rw [hs_at _ (by rw [h2]; exact hb), h2]
  have hsmem : ∀ i : Fin k, s i ∈ K (m+2) ∧ s i ∉ K (m+1) := by
    intro i
    by_cases h : levK K hKuniv (bb i) ≤ m
    · have htip := hst.tip_shell (bb i) h
      rw [hs_at i h]
      exact ⟨interior_subset htip.1, htip.2⟩
    · rw [hs_notat i h]
      have h5 : (bb i : M) ∈ K (levK K hKuniv (bb i) + 1) := levK_mem_succ hK0 hKuniv (bb i)
      have h6 : (bb i : M) ∉ K (levK K hKuniv (bb i)) := levK_notMem hK0 hKuniv (bb i)
      have h1 : levK K hKuniv (bb i) + 1 = m+2 := by have := hlev_b i; omega
      have h2 : levK K hKuniv (bb i) = m+1 := by have := hlev_b i; omega
      exact ⟨h1 ▸ h5, h2 ▸ h6⟩
  have hsintL : ∀ i : Fin k, s i ∈ interior (L (m+1)) :=
    fun i => hAL (m+1) (monotone_K K hKsub (by omega) (hsmem i).1)
  have hsP : ∀ i : Fin k, s i ∉ L m := by
    intro i
    by_cases h : levK K hKuniv (bb i) ≤ m
    · rw [hs_at i h]
      exact fun hL => Set.disjoint_left.mp (hUL m)
        (hst.outside_U (bb i) h 1 ⟨(hst.tau_mem (bb i) h).2, le_rfl⟩) hL
    · have hb : (bb i : M) ∈ B ∩ (K (m+2) \ K (m+1)) := by
        refine ⟨(bb i).2, ?_, ?_⟩
        · have h5 : (bb i : M) ∈ K (levK K hKuniv (bb i) + 1) := levK_mem_succ hK0 hKuniv (bb i)
          have h1 : levK K hKuniv (bb i) + 1 = m + 2 := by have := hlev_b i; omega
          exact h1 ▸ h5
        · have h6 : (bb i : M) ∉ K (levK K hKuniv (bb i)) := levK_notMem hK0 hKuniv (bb i)
          have h2 : levK K hKuniv (bb i) = m + 1 := by have := hlev_b i; omega
          exact h2 ▸ h6
      rw [hs_notat i h]
      exact fun hL => Set.disjoint_left.mp (hLavoidB m) hL hb
  have hsinj : Function.Injective s := by
    intro i i' hii
    have hneq : ∀ j : Fin k, bb j = (e.symm j).1 := hbb_of
    by_cases h : levK K hKuniv (bb i) ≤ m
    · by_cases h' : levK K hKuniv (bb i') ≤ m
      · rw [hs_at i h, hs_at i' h'] at hii
        by_cases hsame : bb i = bb i'
        · exact e.symm.injective (Subtype.ext hsame)
        · have hd := hst.arc_disj (bb i) (bb i') h h' hsame
          rw [Set.disjoint_left] at hd
          exact absurd ⟨1, ⟨zero_le_one, le_rfl⟩, hii.symm⟩ (hd ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩)
      · rw [hs_at i h, hs_notat i' h'] at hii
        by_cases hsame : bb i = bb i'
        · exact e.symm.injective (Subtype.ext hsame)
        · exact absurd hii (hst.arc_notB (bb i) (bb i') h (fun hc => hsame hc.symm) 1
            ⟨zero_le_one, le_rfl⟩)
    · by_cases h' : levK K hKuniv (bb i') ≤ m
      · rw [hs_notat i h, hs_at i' h'] at hii
        by_cases hsame : bb i = bb i'
        · exact e.symm.injective (Subtype.ext hsame)
        · exact absurd hii.symm (hst.arc_notB (bb i') (bb i) h' hsame 1 ⟨zero_le_one, le_rfl⟩)
      · rw [hs_notat i h, hs_notat i' h'] at hii
        exact e.symm.injective (Subtype.ext (Subtype.ext hii))
  -- the slits are free-ended slits in `(L m)ᶜ`, disjoint from `U (m+1)`
  have hsfunK0 : ∀ j, levK K hKuniv (sfun j) ≤ m := fun j => (e0.symm j).2
  have hsltc : ∀ j, Continuous (slt j) := by
    intro j
    rw [hsltdef]
    exact (hst.arc_cont (sfun j) (hsfunK0 j)).comp (by fun_prop)
  have hsltinj : ∀ j, Set.InjOn (slt j) (Set.Icc (0:ℝ) 1) := by
    intro j a ha b hb hab
    rw [hsltdef] at hab
    have hτ0 := (hst.tau_mem (sfun j) (hsfunK0 j)).1
    have hτ1 := (hst.tau_mem (sfun j) (hsfunK0 j)).2
    have h1 : (1-a) * st.τ (sfun j) + a ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by nlinarith [ha.1, ha.2], by nlinarith [ha.1, ha.2, hτ1]⟩
    have h2 : (1-b) * st.τ (sfun j) + b ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by nlinarith [hb.1, hb.2], by nlinarith [hb.1, hb.2, hτ1]⟩
    have h3 : (1-a) * st.τ (sfun j) + a = (1-b) * st.τ (sfun j) + b :=
      hst.arc_inj (sfun j) (hsfunK0 j) h1 h2 hab
    have h4 : (1 - st.τ (sfun j)) * (a - b) = 0 := by linear_combination h3
    have h5 : (0:ℝ) < 1 - st.τ (sfun j) := by linarith
    have h6 : a - b = 0 := by
      rcases mul_eq_zero.mp h4 with h7 | h7
      · exact absurd h7 (by linarith)
      · exact h7
    linarith
  have hsltbody : ∀ j, slt j '' Set.Ioc (0:ℝ) 1 ⊆ (L m)ᶜ := by
    intro j x hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [hsltdef]
    intro hL
    have hτ0 := (hst.tau_mem (sfun j) (hsfunK0 j)).1
    have hτ1 := (hst.tau_mem (sfun j) (hsfunK0 j)).2
    refine hst.outside_notL (sfun j) (hsfunK0 j) _ ⟨?_, ?_⟩ hL
    · nlinarith [hu.1, hu.2, hτ1]
    · nlinarith [hu.1, hu.2]
  have hsltroot : ∀ j, slt j 0 ∉ (L m)ᶜ := by
    intro j hc
    have h1 : slt j 0 = st.γ (sfun j) (st.τ (sfun j)) := by
      simp only [hsltdef]; ring_nf
    exact hc (h1.symm ▸ hst.inside_L (sfun j) (hsfunK0 j) _
      ⟨(hst.tau_mem (sfun j) (hsfunK0 j)).1.le, le_rfl⟩)
  have hsltU : ∀ j, Disjoint (slt j '' Set.Icc (0:ℝ) 1) (U (m+1)) := by
    intro j
    rw [Set.disjoint_left]
    rintro x ⟨u, hu, rfl⟩ hx
    rw [hsltdef] at hx
    have hτ0 := (hst.tau_mem (sfun j) (hsfunK0 j)).1
    have hτ1 := (hst.tau_mem (sfun j) (hsfunK0 j)).2
    have hK : st.γ (sfun j) ((1-u) * st.τ (sfun j) + u) ∈ L (m+1) :=
      interior_subset (hAL (m+1) (interior_subset ((hst.arc_sub (sfun j) (hsfunK0 j) _
        ⟨by nlinarith [hu.1, hu.2, hτ0, hτ1], by nlinarith [hu.1, hu.2, hτ1]⟩).1)))
    exact Set.disjoint_left.mp (hUL (m+1)) hx hK
  have hsltdisj : ∀ j j', j ≠ j' →
      Disjoint (slt j '' Set.Icc (0:ℝ) 1) (slt j' '' Set.Icc (0:ℝ) 1) := by
    intro j j' hne
    rw [Set.disjoint_left]
    rintro x ⟨u, hu, rfl⟩ ⟨u', hu', hxx⟩
    have hsame : sfun j ≠ sfun j' := fun hc => hne (e0.symm.injective (Subtype.ext hc))
    have hvv : (1-u) * st.τ (sfun j) + u ∈ Set.Icc (0:ℝ) 1 := by
      have hτ0 := (hst.tau_mem (sfun j) (hsfunK0 j)).1
      have hτ1 := (hst.tau_mem (sfun j) (hsfunK0 j)).2
      exact ⟨by nlinarith [hu.1, hu.2, hτ0, hτ1], by nlinarith [hu.1, hu.2, hτ1]⟩
    have hvv' : (1-u') * st.τ (sfun j') + u' ∈ Set.Icc (0:ℝ) 1 := by
      have hτ0 := (hst.tau_mem (sfun j') (hsfunK0 j')).1
      have hτ1 := (hst.tau_mem (sfun j') (hsfunK0 j')).2
      exact ⟨by nlinarith [hu'.1, hu'.2, hτ0, hτ1], by nlinarith [hu'.1, hu'.2, hτ1]⟩
    refine (Set.disjoint_left.mp (hst.arc_disj (sfun j) (sfun j') (hsfunK0 j) (hsfunK0 j') hsame)
      ⟨(1-u) * st.τ (sfun j) + u, hvv, rfl⟩) ⟨(1-u') * st.τ (sfun j') + u', hvv', hxx⟩
  have hbb_self : ∀ (b : B) (hb : levK K hKuniv b ≤ m+1), bb (e ⟨b, hb⟩) = b := by
    intro b hb
    rw [hbb_of]
    exact congrArg Subtype.val (Equiv.symm_apply_apply e ⟨b, hb⟩)
  have hbbclip : ∀ j, bb (clip j) = sfun j := by
    intro j
    rw [hbb_of, hclipdef]
    exact congrArg Subtype.val (Equiv.symm_apply_apply e _)
  have hslttip : ∀ j, slt j 1 = s (clip j) := by
    intro j
    have h1 : slt j 1 = st.γ (sfun j) 1 := by
      simp only [hsltdef]
      congr 1
      ring
    rw [h1]
    have h2 : s (clip j) = st.γ (bb (clip j)) 1 :=
      hs_at (clip j) (by rw [hbbclip j]; exact hsfunK0 j)
    rw [h2, hbbclip j]
  have hsnotslt : ∀ i j, clip j ≠ i → s i ∉ slt j '' Set.Icc (0:ℝ) 1 := by
    intro i j hne hmem
    obtain ⟨u, hu, heq⟩ := hmem
    rw [hsltdef] at heq
    have hsame : sfun j ≠ bb i := by
      intro hc
      refine hne ?_
      simp only [hclipdef]
      have h2 : (⟨sfun j, hK0A (e0.symm j)⟩ : A) = e.symm i := by
        apply Subtype.ext
        rw [← hbb_of i]
        exact hc
      rw [h2]
      exact Equiv.apply_symm_apply e i
    have hvv : (1-u) * st.τ (sfun j) + u ∈ Set.Icc (0:ℝ) 1 := by
      have hτ0 := (hst.tau_mem (sfun j) (hsfunK0 j)).1
      have hτ1 := (hst.tau_mem (sfun j) (hsfunK0 j)).2
      exact ⟨by nlinarith [hu.1, hu.2, hτ0, hτ1], by nlinarith [hu.1, hu.2, hτ1]⟩
    by_cases h : levK K hKuniv (bb i) ≤ m
    · rw [hs_at i h] at heq
      exact (Set.disjoint_left.mp (hst.arc_disj (sfun j) (bb i) (hsfunK0 j) h hsame)
        ⟨(1-u) * st.τ (sfun j) + u, hvv, heq⟩) ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
    · rw [hs_notat i h] at heq
      exact absurd heq (hst.arc_notB (sfun j) (bb i) (hsfunK0 j) (Ne.symm hsame) _ hvv)
  have hFfin : ∀ i : Fin k, (F i).Finite := by
    intro i
    refine Set.Finite.union ?_ ?_
    · exact (hB (K (m+3)) (hKc (m+3))).sdiff
    · exact (Set.finite_range (fun i' : Fin k => s i')).subset (fun x hx => by
        obtain ⟨i', _, rfl⟩ := hx; exact ⟨i', rfl⟩)
  have hsF : ∀ i : Fin k, s i ∉ F i := by
    intro i h
    rcases h with h | ⟨i', hne, heq⟩
    · exact h.2 rfl
    · exact hne (hsinj heq.symm ▸ rfl)
  have hFs : ∀ i i' : Fin k, i ≠ i' → s i' ∈ F i := fun i i' hne => Or.inr ⟨i', hne.symm, rfl⟩
  -- the peel
  obtain ⟨α, σ, hcont, hinj, hzero, hσ, hin, hout, houtU, houtSh, htipSh, htipU, htipF, hcomp,
    hincomp, hnotF, havβ, havslt, havown, hdisj, hstart⟩ :=
    peel_arcs (n := n) hn (P := L m) (L := L (m+1)) (K := K (m+3))
      (U := U (m+1)) (Shell := Shell K (m+2))
      (hLc m) (hLpf m) (hLc (m+1)) (hKc (m+3)) ((hLB (m+1)).trans interior_subset)
      (hUo (m+1)) (hUL (m+1)) (isOpen_shell K (hKc (m+2)).isClosed)
      (frontier_collar_subset_shell (hLc (m+1)) (hAL (m+1)) (hLB (m+1)))
      (hpieces (m+1)) s hsintL hsinj hsP
      (F := F) (hF := hFfin) (hsF := hsF) (hFs := hFs)
      (slt := slt) (hsltc := hsltc) (hsltinj := hsltinj) (hsltbody := hsltbody)
      (hsltroot := hsltroot) (hsltU := hsltU) (hsltdisj := hsltdisj)
      (hclip := hslttip) (hsnotslt := hsnotslt)
      (β := fun j : Fin 0 => (Fin.elim0 j : ℝ → M))
      (hβc := fun j : Fin 0 => Fin.elim0 j) (hβsub := fun j : Fin 0 => Fin.elim0 j)
      (hβ0F := fun (i : Fin k) (j : Fin 0) => Fin.elim0 j)
      (hβfront := fun (i : Fin k) (j : Fin 0) => Fin.elim0 j)
  -- the arc stays inside `interior (K (m+3))` and avoids `K (m+1)`
  have harcK : ∀ i u, u ∈ Set.Icc (0:ℝ) 1 → α i u ∈ interior (K (m+3)) := by
    intro i u hu
    by_cases hlt : u ≤ σ i
    · exact hLB (m+1) (hin i u ⟨hu.1, hlt⟩)
    · have hu' : u ∈ Set.Ioc (σ i) 1 := ⟨lt_of_not_ge hlt, hu.2⟩
      rw [Shell] at houtSh
      exact (houtSh i u hu').1
  have harcKm : ∀ i u, u ∈ Set.Icc (0:ℝ) 1 → α i u ∉ K (m+1) := by
    intro i u hu hKm
    by_cases hlt : u ≤ σ i
    · exact (connectedComponentIn_subset ((L m)ᶜ) (s i) (hincomp i u ⟨hu.1, hlt⟩))
        (interior_subset (hAL m hKm))
    · have hu' : u ∈ Set.Ioc (σ i) 1 := ⟨lt_of_not_ge hlt, hu.2⟩
      rw [Shell] at houtSh
      exact (houtSh i u hu').2 (monotone_K K hKsub (by omega) hKm)
  refine ⟨⟨fun b => if hb : levK K hKuniv b ≤ m+1 then s (e ⟨b, hb⟩) else (b : M),
    fun b => if hb : levK K hKuniv b ≤ m+1 then α (e ⟨b, hb⟩) else fun _ => (b : M),
    fun b => if hb : levK K hKuniv b ≤ m+1 then σ (e ⟨b, hb⟩) else 1/2⟩, ?_, ?_⟩
  · -- the level-`(m+1)` invariant
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b hb; simp only [dif_pos hb]; exact hcont _
    · intro b hb; simp only [dif_pos hb]; exact hinj _
    · intro b hb; simp only [dif_pos hb]; exact hzero _
    · intro b hb; simp only [dif_pos hb]; exact hσ _
    · intro b hb u hu; simp only [dif_pos hb] at hu ⊢; exact hin _ u hu
    · intro b hb u hu; simp only [dif_pos hb] at hu ⊢; exact hout _ u hu
    · intro b hb u hu; simp only [dif_pos hb] at hu ⊢; exact houtU _ u hu
    · intro b hb
      simp only [dif_pos hb]
      simpa only [Shell] using htipSh _
    · intro b hb u hu
      simp only [dif_pos hb]
      by_cases hlt : u ≤ σ (e ⟨b, hb⟩)
      · exact ⟨hLB (m+1) (hin _ u ⟨hu.1, hlt⟩),
          fun h2 => harcKm _ u hu (monotone_K K hKsub (by omega) h2)⟩
      · have hu' : u ∈ Set.Ioc (σ (e ⟨b, hb⟩)) 1 := ⟨lt_of_not_ge hlt, hu.2⟩
        rw [Shell] at houtSh
        exact ⟨(houtSh _ u hu').1, fun h2 =>
          (houtSh _ u hu').2 (monotone_K K hKsub (by omega) h2)⟩
    · intro b b' hb hne u hu
      simp only [dif_pos hb]
      intro heq
      have hmF : α (e ⟨b, hb⟩) u ∉ F (e ⟨b, hb⟩) := hnotF _ u hu
      have hbK : ((b' : B) : M) ∈ B ∩ K (m+3) :=
        ⟨(b' : B).2, by rw [← heq]; exact interior_subset (harcK _ u hu)⟩
      by_cases hcase : ((b' : B) : M) = s (e ⟨b, hb⟩)
      · exfalso
        by_cases hlev : levK K hKuniv b ≤ m
        · have h2 : st.γ b 1 ≠ ((b' : B) : M) :=
            hst.arc_notB b b' hlev hne 1 ⟨zero_le_one, le_rfl⟩
          refine h2 ?_
          rw [hcase]
          rw [hs_at (e ⟨b, hb⟩) (by rw [hbb_self b hb]; exact hlev), hbb_self b hb]
        · have h4 : s (e ⟨b, hb⟩) = ((b : B) : M) := by
            rw [hs_notat (e ⟨b, hb⟩) (by rw [hbb_self b hb]; exact hlev), hbb_self b hb]
          exact hne (Subtype.ext (by rw [← h4, hcase]))
      · exact hmF (Or.inl ⟨heq ▸ hbK, fun hc => hcase (heq.symm.trans hc)⟩)
    · intro b hb
      simp only [dif_pos hb]
      exact hsmem _
    · intro b hb hlt
      simp only [dif_pos hb]
      have h2 : levK K hKuniv (bb (e ⟨b, hb⟩)) ≤ m := by rw [hbb_self b hb]; omega
      rw [hs_at _ h2]
      exact hst.tip_shell _ h2
    · intro b hb heq
      simp only [dif_pos hb]
      have h2 : ¬ levK K hKuniv (bb (e ⟨b, hb⟩)) ≤ m := by rw [hbb_self b hb]; omega
      rw [hs_notat _ h2]
      exact congrArg (fun z : B => (z : M)) (hbb_self b hb)
    · intro b b' hb hb' hne
      simp only [dif_pos hb, dif_pos hb']
      refine hdisj _ _ (fun hc => hne ?_)
      exact Subtype.ext (congrArg (fun x : A => ((x.1 : B) : M)) (e.injective hc))
  · -- the cross-level conditions
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      simp only [dif_pos (hK0A' b hb)]
      exact hs_le b hb
    · intro b hb u hu
      simp only [dif_pos hb]
      rcases hcomp (e ⟨b, hb⟩) u hu with h1 | h1
      · exact fun hL => (connectedComponentIn_subset ((L m)ᶜ) _ h1) hL
      · exact fun hL => Set.disjoint_left.mp (hUL (m+1)) h1
          (interior_subset (hAL (m+1) (interior_subset (hLB m hL))))
    · intro b b' hb hb' hne u hu
      simp only [dif_pos hb']
      have hbK0 : levK K hKuniv b ≤ m := hb
      have hsf : sfun (e0 ⟨b, hbK0⟩) = b := by
        rw [hsfundef]
        exact congrArg Subtype.val (Equiv.symm_apply_apply e0 ⟨b, hbK0⟩)
      have hclipb : clip (e0 ⟨b, hbK0⟩) = e ⟨b, hK0A' b hbK0⟩ := by
        simp only [hclipdef]
        refine congrArg e ?_
        apply Subtype.ext
        exact hsf
      have hneidx : clip (e0 ⟨b, hbK0⟩) ≠ e ⟨b', hb'⟩ := by
        rw [hclipb]
        intro hc
        exact hne (Subtype.ext
          (congrArg (fun x : A => ((x.1 : B) : M)) (e.injective hc)))
      have havoid : α (e ⟨b', hb'⟩) u ∉ slt (e0 ⟨b, hbK0⟩) '' Set.Icc (0:ℝ) 1 :=
        havslt (e ⟨b', hb'⟩) u hu (e0 ⟨b, hbK0⟩) hneidx
      intro heq
      refine havoid ?_
      have hsub : st.γ b '' Set.Ioc (st.τ b) 1 ⊆ slt (e0 ⟨b, hbK0⟩) '' Set.Icc (0:ℝ) 1 := by
        rintro x ⟨v, hv, rfl⟩
        simp only [hsltdef]
        rw [hsf]
        have hτ1 := (hst.tau_mem b hbK0).2
        have hden : (0:ℝ) < 1 - st.τ b := by linarith
        refine ⟨(v - st.τ b) / (1 - st.τ b), ⟨?_, ?_⟩, ?_⟩
        · exact div_nonneg (by linarith [hv.1]) hden.le
        · rw [div_le_one hden]; linarith [hv.2]
        · have harg : (1 - (v - st.τ b) / (1 - st.τ b)) * st.τ b +
              (v - st.τ b) / (1 - st.τ b) = v := by field_simp; ring
          show st.γ b ((1 - (v - st.τ b) / (1 - st.τ b)) * st.τ b +
            (v - st.τ b) / (1 - st.τ b)) = st.γ b v
          rw [harg]
      exact hsub heq

end Work.Noncompact.CompressionTube
