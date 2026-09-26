import Mathlib
import Submission.Work.BoxShrink.PinchOff.isPreconnected_sInter_of_chain

/-!
# A nontrivial continuum contains a preconnected non-compact subset

We prove `Work.BoxShrink.PinchOff.exists_preconnected_not_isCompact_of_nontrivial_continuum`:
every compact, preconnected, nontrivial subset `C ⊆ ℂ` contains a preconnected subset which is not
compact.

By Zorn's lemma (with `isPreconnected_sInter_of_chain` supplying the chain condition) we find a
subcontinuum `M ⊆ C` irreducible between two distinct points `a, b ∈ M`, i.e. minimal among the
compact preconnected subsets containing `a` and `b`.  If `M \ {a}` admitted a separation `A ⊔ B`,
then `a` would lie in the closure of each side and `closure A` -- a proper subcontinuum, since the
other side is non-empty and disjoint from it -- would contain both `a` and `b`, contradicting
minimality.  Hence `M \ {a}` is preconnected, and it is not compact because `a` is a limit point
of it.
-/

namespace Work.BoxShrink.PinchOff

open Set

/-- If closed sets `C`, `D` cover a preconnected set `M` and meet in exactly one point `a`, then
`C` is preconnected. -/
private theorem isPreconnected_of_isClosed_union_eq {M C D : Set ℂ} {a : ℂ}
    (hM : IsPreconnected M) (hCc : IsClosed C) (hDc : IsClosed D)
    (hCD : C ∪ D = M) (hCDa : C ∩ D = {a}) : IsPreconnected C := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv huv huv0
  by_contra hcon
  have hcu : ¬ C ⊆ u := fun h => hcon (Or.inl h)
  have hcv : ¬ C ⊆ v := fun h => hcon (Or.inr h)
  obtain ⟨x, hxC, hxv⟩ := not_subset.mp hcv
  obtain ⟨y, hyC, hyu⟩ := not_subset.mp hcu
  have hxu : x ∈ u := (huv hxC).resolve_right hxv
  have hyv : y ∈ v := (huv hyC).resolve_left hyu
  have hCM : C ⊆ M := hCD ▸ subset_union_left
  have hCun : (C ∩ u).Nonempty := ⟨x, hxC, hxu⟩
  have hCvn : (C ∩ v).Nonempty := ⟨y, hyC, hyv⟩
  have haC : a ∈ C := (show a ∈ C ∩ D from by rw [hCDa]; exact mem_singleton a).1
  have hT1 : (C ∩ v) ∩ (C ∩ u) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro z ⟨⟨hzC, hzv⟩, -, hzu⟩
    have hz : z ∈ C ∩ (u ∩ v) := ⟨hzC, hzu, hzv⟩
    rw [huv0] at hz; exact hz
  have hT1' : (C ∩ u) ∩ (C ∩ v) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro z ⟨⟨hzC, hzu⟩, -, hzv⟩
    have hz : z ∈ C ∩ (u ∩ v) := ⟨hzC, hzu, hzv⟩
    rw [huv0] at hz; exact hz
  have hCMv : C ∩ v ⊆ M := inter_subset_left.trans hCM
  have hCMu : C ∩ u ⊆ M := inter_subset_left.trans hCM
  by_cases haP : a ∈ C ∩ u
  · have haT : a ∉ C ∩ v := fun h => by
      have hz : a ∈ C ∩ (u ∩ v) := ⟨haP.1, haP.2, h.2⟩
      rw [huv0] at hz; exact hz
    have hT2 : (C ∩ v) ∩ D = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro z ⟨⟨hzC, hzv⟩, hzD⟩
      have hz : z ∈ C ∩ D := ⟨hzC, hzD⟩
      rw [hCDa, mem_singleton_iff] at hz
      subst hz
      exact haT ⟨hzC, hzv⟩
    have hd : (C ∩ v) ∩ (C ∩ u ∪ D) = ∅ := by
      rw [inter_union_distrib_left, hT1, hT2, empty_union]
    have hc : (C ∩ v) ∪ (C ∩ u ∪ D) = M := by
      rw [← union_assoc, union_comm (C ∩ v) (C ∩ u), ← inter_union_distrib_left,
        inter_eq_left.mpr huv, hCD]
    have hneS : (C ∩ u ∪ D).Nonempty := ⟨a, Or.inl haP⟩
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hM) (C ∩ v) (C ∩ u ∪ D)
        (hCc.inter hv) ((hCc.inter hu).union hDc) hc.ge
        (by rw [← inter_assoc, inter_eq_self_of_subset_right hCMv, hd]) with h | h
    · obtain ⟨z, hzj⟩ := hneS
      have hzM : z ∈ M := by
        rcases hzj with hz | hz
        · exact hCD ▸ (Or.inl hz.1)
        · exact hCD ▸ (Or.inr hz)
      have hzT : z ∈ C ∩ v := h hzM
      have : z ∈ (C ∩ v) ∩ (C ∩ u ∪ D) := ⟨hzT, hzj⟩
      rw [hd] at this; exact this
    · obtain ⟨z, hzj⟩ := hCvn
      have hzM : z ∈ M := hCD ▸ (Or.inl hzj.1)
      have hzS : z ∈ C ∩ u ∪ D := h hzM
      have : z ∈ (C ∩ v) ∩ (C ∩ u ∪ D) := ⟨hzj, hzS⟩
      rw [hd] at this; exact this
  · have hCvn' : a ∈ C ∩ v := by
      rcases (huv haC) with h | h
      · exact absurd ⟨haC, h⟩ haP
      · exact ⟨haC, h⟩
    have hT2 : (C ∩ u) ∩ D = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro z ⟨⟨hzC, hzu⟩, hzD⟩
      have hz : z ∈ C ∩ D := ⟨hzC, hzD⟩
      rw [hCDa, mem_singleton_iff] at hz
      subst hz
      exact haP ⟨hzC, hzu⟩
    have hd : (C ∩ u) ∩ (C ∩ v ∪ D) = ∅ := by
      rw [inter_union_distrib_left, hT1', hT2, empty_union]
    have hc : (C ∩ u) ∪ (C ∩ v ∪ D) = M := by
      rw [← union_assoc, ← inter_union_distrib_left, inter_eq_left.mpr huv, hCD]
    have hneS : (C ∩ v ∪ D).Nonempty := ⟨a, Or.inl hCvn'⟩
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hM) (C ∩ u) (C ∩ v ∪ D)
        (hCc.inter hu) ((hCc.inter hv).union hDc) hc.ge
        (by rw [← inter_assoc, inter_eq_self_of_subset_right hCMu, hd]) with h | h
    · obtain ⟨z, hzj⟩ := hneS
      have hzM : z ∈ M := by
        rcases hzj with hz | hz
        · exact hCD ▸ (Or.inl hz.1)
        · exact hCD ▸ (Or.inr hz)
      have hzT : z ∈ C ∩ u := h hzM
      have : z ∈ (C ∩ u) ∩ (C ∩ v ∪ D) := ⟨hzT, hzj⟩
      rw [hd] at this; exact this
    · obtain ⟨z, hzj⟩ := hCun
      have hzM : z ∈ M := hCD ▸ (Or.inl hzj.1)
      have hzS : z ∈ C ∩ v ∪ D := h hzM
      have : z ∈ (C ∩ u) ∩ (C ∩ v ∪ D) := ⟨hzj, hzS⟩
      rw [hd] at this; exact this

/-- If `A ⊔ B` separates `M \ {a}` (with `M` preconnected, closed) then `a` lies in the closure of
each side. -/
private theorem mem_closure_of_separation {M A B : Set ℂ} {a : ℂ} (hM : IsPreconnected M)
    (hMclosed : IsClosed M) (haM : a ∈ M) (hAM : A ⊆ M) (hAB : A ∪ B = M \ {a})
    (hAcB : closure A ∩ B = ∅) (hBcA : A ∩ closure B = ∅) (hAne : A.Nonempty) :
    a ∈ closure A := by
  by_contra ha
  have hAclM : closure A ⊆ M := closure_minimal hAM hMclosed
  have hkeyA : closure A ∩ (M \ {a}) = A := by
    rw [← hAB, inter_union_distrib_left, inter_eq_self_of_subset_right subset_closure, hAcB,
      union_empty]
  have hsub : closure A ⊆ M \ {a} :=
    fun x hx => ⟨hAclM hx, fun hxa => ha (hxa ▸ hx)⟩
  have hkeyA' : closure A ∩ (M \ {a}) = closure A := inter_eq_self_of_subset_left hsub
  have hcA : closure A = A := hkeyA'.symm.trans hkeyA
  have hAclosed : IsClosed A := by rw [← hcA]; exact isClosed_closure
  have haA : a ∉ A := fun h => (hAB ▸ subset_union_left h).2 (mem_singleton_iff.mpr rfl)
  have hBcl : IsClosed (closure B ∪ {a}) := isClosed_closure.union isClosed_singleton
  have hcover : M ⊆ A ∪ (closure B ∪ {a}) := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inr (Or.inr (mem_singleton_iff.mpr hxa))
    · have hx' : x ∈ M \ {a} := ⟨hx, hxa⟩
      rw [← hAB] at hx'
      rcases hx' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (subset_closure h))
  have hdisj : M ∩ (A ∩ (closure B ∪ {a})) = ∅ := by
    have e1 : M ∩ A = A := inter_eq_self_of_subset_right hAM
    have e2 : A ∩ ({a} : Set ℂ) = ∅ := by rw [inter_singleton_eq_empty]; exact haA
    rw [← inter_assoc, e1, inter_union_distrib_left, hBcA, e2, union_empty]
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hM) A (closure B ∪ {a}) hAclosed hBcl
      hcover hdisj with h | h
  · exact haA (h haM)
  · have hAB' : A ⊆ closure B := by
      intro z hz
      rcases h (hAM hz) with hzB | hza
      · exact hzB
      · exact absurd (mem_singleton_iff.mp hza ▸ hz) haA
    obtain ⟨z, hz⟩ := hAne
    have : z ∈ A ∩ closure B := ⟨hz, hAB' hz⟩
    rw [hBcA] at this
    exact this

/-- The separating halves `A`, `B` of `M \ {a}` (a preconnected closed `M`) have closures meeting
exactly in `a` and covering `M`. -/
private theorem closure_facts_of_separation {M A B : Set ℂ} {a : ℂ} (hM : IsPreconnected M)
    (hMclosed : IsClosed M) (haM : a ∈ M) (hAM : A ⊆ M) (hAB : A ∪ B = M \ {a})
    (hAcB : closure A ∩ B = ∅) (hBcA : A ∩ closure B = ∅)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    a ∈ closure A ∧ a ∈ closure B ∧ closure A ∩ closure B = {a} ∧ M ⊆ closure A ∪ closure B := by
  have hBM : B ⊆ M := fun x hx => (hAB ▸ subset_union_right hx).1
  have hAclM : closure A ⊆ M := closure_minimal hAM hMclosed
  have hBclM : closure B ⊆ M := closure_minimal hBM hMclosed
  have haA : a ∈ closure A := mem_closure_of_separation hM hMclosed haM hAM hAB hAcB hBcA hAne
  have haB : a ∈ closure B :=
    mem_closure_of_separation hM hMclosed haM hBM (by rw [union_comm]; exact hAB)
      (by rw [inter_comm]; exact hBcA) (by rw [inter_comm]; exact hAcB) hBne
  have hkeyA : closure A ∩ (M \ {a}) = A := by
    rw [← hAB, inter_union_distrib_left, inter_eq_self_of_subset_right subset_closure, hAcB,
      union_empty]
  have hkeyB : closure B ∩ (M \ {a}) = B := by
    have h1 : closure B ∩ A = ∅ := by rw [inter_comm]; exact hBcA
    rw [← hAB, inter_union_distrib_left, h1, inter_eq_right.mpr subset_closure, empty_union]
  have hABint : A ∩ B = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro z ⟨hzA, hzB⟩
    have hz : z ∈ closure A ∩ B := ⟨subset_closure hzA, hzB⟩
    rw [hAcB] at hz
    exact hz
  have hCDa : closure A ∩ closure B = {a} := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxa : x = a
      · exact mem_singleton_iff.mpr hxa
      · exfalso
        have hxm : x ∈ M \ {a} := ⟨hAclM hx.1, hxa⟩
        have h1 : x ∈ A := by rw [← hkeyA]; exact ⟨hx.1, hxm⟩
        have h2 : x ∈ B := by rw [← hkeyB]; exact ⟨hx.2, hxm⟩
        have : x ∈ A ∩ B := ⟨h1, h2⟩
        rw [hABint] at this
        exact this
    · intro x hx
      rw [mem_singleton_iff] at hx
      rw [hx]
      exact ⟨haA, haB⟩
  refine ⟨haA, haB, hCDa, ?_⟩
  intro x hx
  have hx' : x ∈ A ∪ B ∪ {a} := by
    by_cases hxa : x = a
    · exact Or.inr (mem_singleton_iff.mpr hxa)
    · exact Or.inl (by rw [hAB]; exact ⟨hx, hxa⟩)
  rcases hx' with h | h
  · rcases h with h | h
    · exact Or.inl (subset_closure h)
    · exact Or.inr (subset_closure h)
  · exact Or.inl (mem_singleton_iff.mp h ▸ haA)

theorem exists_preconnected_not_isCompact_of_nontrivial_continuum {C : Set ℂ}
    (hCk : IsCompact C) (hCp : IsPreconnected C) (hCnt : C.Nontrivial) :
    ∃ D : Set ℂ, D ⊆ C ∧ IsPreconnected D ∧ ¬ IsCompact D := by
  obtain ⟨a, ha, b, hb, hab⟩ := hCnt
  let S : Set (Set ℂ) := {E | E ⊆ C ∧ IsCompact E ∧ IsPreconnected E ∧ a ∈ E ∧ b ∈ E}
  have hCS : C ∈ S := ⟨subset_rfl, hCk, hCp, ha, hb⟩
  have H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hchain hcne
    have hsubC : ⋂₀ c ⊆ C :=
      fun x hx => (hcS hcne.some_mem).1 (sInter_subset_of_mem hcne.some_mem hx)
    refine ⟨⋂₀ c, ⟨hsubC, ?_, ?_, ?_, ?_⟩, fun s hs => sInter_subset_of_mem hs⟩
    · exact hCk.of_isClosed_subset (isClosed_sInter fun s hs => (hcS hs).2.1.isClosed) hsubC
    · exact isPreconnected_sInter_of_chain hchain hcne (fun s hs => (hcS hs).2.1)
        (fun s hs => (hcS hs).2.2.1)
    · exact fun s hs => (hcS hs).2.2.2.1
    · exact fun s hs => (hcS hs).2.2.2.2
  obtain ⟨M, hMsubC, hmin⟩ := zorn_superset_nonempty S H C hCS
  obtain ⟨hMS, hmin2⟩ := hmin
  obtain ⟨hMC, hMk, hMp, hMa, hMb⟩ := hMS
  have hMclosed : IsClosed M := hMk.isClosed
  have hkey : IsPreconnected (M \ {a}) := by
    by_contra hnot
    rw [isPreconnected_iff_subset_of_disjoint_closed] at hnot
    push Not at hnot
    obtain ⟨u, v, hu, hv, huv, huv0, hcon⟩ := hnot
    have hnu : ¬ (M \ {a}) ⊆ u := hcon.1
    have hnv : ¬ (M \ {a}) ⊆ v := hcon.2
    set A : Set ℂ := (M \ {a}) ∩ u with hA
    set B : Set ℂ := (M \ {a}) ∩ v with hB
    have hAB : A ∪ B = M \ {a} := by
      rw [hA, hB, ← inter_union_distrib_left, inter_eq_left.mpr huv]
    have hAM' : A ⊆ M \ {a} := hAB ▸ subset_union_left
    have hBM' : B ⊆ M \ {a} := hAB ▸ subset_union_right
    have hAM : A ⊆ M := fun x hx => (hAM' hx).1
    have hBM : B ⊆ M := fun x hx => (hBM' hx).1
    have hAu : A ⊆ u := fun x hx => (hA ▸ hx).2
    have hBv : B ⊆ v := fun x hx => (hB ▸ hx).2
    have hAcB : closure A ∩ B = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨hxcl, hxB⟩
      have hxu : x ∈ u := closure_minimal hAu hu hxcl
      have hxm : x ∈ M \ {a} := (hB ▸ hxB).1
      have hxv : x ∈ v := (hB ▸ hxB).2
      have : x ∈ (M \ {a}) ∩ (u ∩ v) := ⟨hxm, hxu, hxv⟩
      rw [huv0] at this; exact this
    have hBcA : A ∩ closure B = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨hxA, hxcl⟩
      have hxv : x ∈ v := closure_minimal hBv hv hxcl
      have hxm : x ∈ M \ {a} := (hA ▸ hxA).1
      have hxu : x ∈ u := (hA ▸ hxA).2
      have : x ∈ (M \ {a}) ∩ (u ∩ v) := ⟨hxm, hxu, hxv⟩
      rw [huv0] at this; exact this
    have hAne : A.Nonempty := by
      obtain ⟨x, hx, hxv⟩ := not_subset.mp hnv
      exact ⟨x, by rw [hA]; exact ⟨hx, (huv hx).resolve_right hxv⟩⟩
    have hBne : B.Nonempty := by
      obtain ⟨x, hx, hxu⟩ := not_subset.mp hnu
      exact ⟨x, by rw [hB]; exact ⟨hx, (huv hx).resolve_left hxu⟩⟩
    obtain ⟨haA, haB, hCDa, hcover⟩ :=
      closure_facts_of_separation hMp hMclosed hMa hAM hAB hAcB hBcA hAne hBne
    have hEA_M : closure A ⊆ M := closure_minimal hAM hMclosed
    have hEB_M : closure B ⊆ M := closure_minimal hBM hMclosed
    have hunion : closure A ∪ closure B = M := Subset.antisymm (union_subset hEA_M hEB_M) hcover
    have hb' : b ∈ M \ {a} := ⟨hMb, fun h => hab h.symm⟩
    have hbAB : b ∈ A ∪ B := by rw [hAB]; exact hb'
    rcases hbAB with hbA | hbB
    · have hpreA : IsPreconnected (closure A) :=
        isPreconnected_of_isClosed_union_eq hMp isClosed_closure isClosed_closure hunion hCDa
      have hEin : closure A ∈ S :=
        ⟨hEA_M.trans hMC, hMk.of_isClosed_subset isClosed_closure hEA_M, hpreA, haA,
          subset_closure hbA⟩
      have hME : M ⊆ closure A := hmin2 hEin hEA_M
      obtain ⟨z, hz⟩ := hBne
      have hzM : z ∈ M := hBM hz
      have : z ∈ closure A ∩ B := ⟨hME hzM, hz⟩
      rw [hAcB] at this; exact this
    · have hpreB : IsPreconnected (closure B) :=
        isPreconnected_of_isClosed_union_eq hMp isClosed_closure isClosed_closure
          (by rw [union_comm]; exact hunion) (by rw [inter_comm]; exact hCDa)
      have hEin : closure B ∈ S :=
        ⟨hEB_M.trans hMC, hMk.of_isClosed_subset isClosed_closure hEB_M, hpreB, haB,
          subset_closure hbB⟩
      have hME : M ⊆ closure B := hmin2 hEin hEB_M
      obtain ⟨z, hz⟩ := hAne
      have hzM : z ∈ M := hAM hz
      have : z ∈ A ∩ closure B := ⟨hz, hME hzM⟩
      rw [hBcA] at this; exact this
  refine ⟨M \ {a}, fun x hx => hMC hx.1, hkey, ?_⟩
  intro hcomp
  have hcl : IsClosed (M \ {a}) := hcomp.isClosed
  have hacl : a ∈ closure (M \ {a}) := by
    by_contra hcon
    have hmem : ∃ o : Set ℂ, IsOpen o ∧ a ∈ o ∧ o ∩ (M \ {a}) = ∅ := by
      by_contra h
      apply hcon
      rw [mem_closure_iff]
      intro o ho hao
      by_contra hdisj'
      exact h ⟨o, ho, hao, Set.not_nonempty_iff_eq_empty.mp hdisj'⟩
    obtain ⟨o, ho, hao, hodisj⟩ := hmem
    have hMo : M ∩ o ⊆ {a} := by
      intro x hx
      by_cases hxa : x = a
      · exact mem_singleton_iff.mpr hxa
      · exfalso
        have : x ∈ o ∩ (M \ {a}) := ⟨hx.2, hx.1, hxa⟩
        rw [hodisj] at this; exact this
    have hMo' : M ∩ ({a} ∩ closure (M \ {a})) = ∅ := by
      rw [← inter_assoc, eq_empty_iff_forall_notMem]
      rintro x ⟨⟨-, hxa⟩, hxcl⟩
      rw [mem_singleton_iff] at hxa
      rw [hxa] at hxcl
      exact hcon hxcl
    have hsub : M ⊆ {a} ∪ closure (M \ {a}) := by
      intro x hx
      by_cases hxa : x = a
      · exact Or.inl (mem_singleton_iff.mpr hxa)
      · exact Or.inr (subset_closure ⟨hx, hxa⟩)
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hMp) {a} (closure (M \ {a}))
        isClosed_singleton isClosed_closure hsub hMo' with h | h
    · have hb1 : b ∈ ({a} : Set ℂ) := h hMb
      rw [mem_singleton_iff] at hb1
      exact hab hb1.symm
    · exact hcon (h hMa)
  have : a ∈ M \ {a} := hcl.closure_eq ▸ hacl
  exact this.2 (mem_singleton_iff.mpr rfl)

end Work.BoxShrink.PinchOff
