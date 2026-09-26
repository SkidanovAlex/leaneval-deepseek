import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Separator
import Submission.Work.Smooth.JordanSeparation.isPreconnected_compl_of_totallyDisconnected
import Submission.Work.BoxShrink.PinchOff.isPreconnected_sInter_of_chain

/-!
# An unbounded complementary component

If `Z ⊆ ℂ` is closed and *every* preconnected subset of `Z` is compact, and `Zᶜ` is nonempty, then
some connected component of `Zᶜ` is unbounded.

The hypothesis on `Z` is very strong: it forces every preconnected subset of `Z` to be a
subsingleton.  Indeed, a nondegenerate continuum `C ⊆ Z` would contain a preconnected non-compact
subset, namely `C \ {p}` for a suitable point `p ∈ C`: taking `K ⊆ C` minimal among subcontinua
containing two distinct points `a b`, the set `K \ {a}` is preconnected by Whyburn's theorem 9.8
(Analytic Topology), since `K \ {a}` cannot split into two separated pieces (such a split would
produce a proper subcontinuum `{a} ∪ A` containing both `a` and `b`).

With that, writing `U` for the component of a point `z₀ ∈ Zᶜ`: if `U` were bounded then, for `R`
bounding `U`, the compact totally disconnected set `F = Z ∩ closedBall 0 R` has *preconnected*
complement (`isPreconnected_compl_of_totallyDisconnected`), and `U` is a nonempty clopen subset of
`Fᶜ`, forcing `U = Fᶜ` — contradicting the boundedness of `U` since `Fᶜ` contains all points of
large norm.
-/

open Set Metric
open scoped Topology

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## Auxiliary facts about preconnected sets -/

/-- Two nonempty sets covering `S`, each disjoint from the other's closure, make `S`
non-preconnected. -/
theorem not_isPreconnected_of_separated_union {S A B : Set ℂ} (hcover : A ∪ B = S)
    (h1 : Disjoint (closure A) B) (h2 : Disjoint A (closure B))
    (hA : A.Nonempty) (hB : B.Nonempty) : ¬ IsPreconnected S := by
  intro hS
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hS
  have hsub : S ⊆ closure A ∪ closure B := by
    rw [← hcover]
    exact union_subset_union subset_closure subset_closure
  have hdisj : S ∩ (closure A ∩ closure B) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxS, hxA, hxB⟩
    rw [← hcover] at hxS
    rcases hxS with hx | hx
    · exact (Set.disjoint_left.mp h2) hx hxB
    · exact (Set.disjoint_left.mp h1) hxA hx
  rcases hS (closure A) (closure B) isClosed_closure isClosed_closure hsub hdisj with h | h
  · have hBsub : B ⊆ closure A := fun x hx => h (by rw [← hcover]; exact Or.inr hx)
    exact hB.ne_empty (eq_empty_iff_forall_notMem.mpr fun x hx =>
      (Set.disjoint_left.mp h1) (hBsub hx) hx)
  · have hAsub : A ⊆ closure B := fun x hx => h (by rw [← hcover]; exact Or.inl hx)
    exact hA.ne_empty (eq_empty_iff_forall_notMem.mpr fun x hx =>
      (Set.disjoint_left.mp h2) hx (hAsub hx))

/-- A point of a preconnected set the removal of which leaves the set nonempty is a limit point of
that complement. -/
theorem mem_closure_diff_singleton_of_isPreconnected {S : Set ℂ} {a : ℂ}
    (hS : IsPreconnected S) (haS : a ∈ S) (hne : (S \ {a}).Nonempty) :
    a ∈ closure (S \ {a}) := by
  by_contra hnot
  rw [_root_.mem_closure_iff] at hnot
  push_neg at hnot
  obtain ⟨O, hOopen, haO, hOdisj⟩ := hnot
  have hcover : S ⊆ O ∪ {a}ᶜ := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl (hxa ▸ haO)
    · exact Or.inr (by simpa [hxa])
  have hne' : (S ∩ {a}ᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx.1, hx.2⟩
  have hcontra := hS O {a}ᶜ hOopen isClosed_singleton.isOpen_compl hcover
    ⟨a, haS, haO⟩ hne'
  obtain ⟨z, hz⟩ := hcontra
  exact (eq_empty_iff_forall_notMem.mp hOdisj) z ⟨hz.2.1, hz.1, hz.2.2⟩

/-- **Whyburn, Analytic Topology, Theorem 9.8** (the case `C = {a}`): if `K` is preconnected,
`a ∈ K` and `K \ {a} = A ∪ B` with `A`, `B` separated, then `{a} ∪ A` is preconnected. -/
theorem isPreconnected_insert_of_compl_eq {K A B : Set ℂ} {a : ℂ}
    (hK : IsPreconnected K) (haK : a ∈ K)
    (hunion : A ∪ B = K \ {a})
    (hsepA : Disjoint (closure A) B) (hsepB : Disjoint A (closure B)) :
    IsPreconnected (insert a A) := by
  by_contra hcon
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hcon
  push_neg at hcon
  obtain ⟨u, v, hu, hv, huv, huvd, hnu, hnv⟩ := hcon
  have hKeq : insert a A ∪ B = K := by
    rw [insert_eq, union_assoc, hunion, union_sdiff_cancel (show ({a} : Set ℂ) ⊆ K from by simpa using haK)]
  have key : ∀ (u v : Set ℂ), IsClosed u → IsClosed v → insert a A ⊆ u ∪ v →
      insert a A ∩ (u ∩ v) = ∅ → ¬ insert a A ⊆ u → ¬ insert a A ⊆ v →
      a ∈ v → False := by
    intro u v hu hv huv huvd hnu hnv hav
    set E : Set ℂ := insert a A ∩ u with hEdef
    set F : Set ℂ := insert a A ∩ v with hFdef
    have hau : a ∉ u := fun h => (eq_empty_iff_forall_notMem.mp huvd) a ⟨mem_insert a A, h, hav⟩
    have hEne : E.Nonempty := by
      obtain ⟨x, hx⟩ := not_subset.mp hnv
      exact ⟨x, hx.1, (huv hx.1).resolve_right hx.2⟩
    have hFne : F.Nonempty := ⟨a, mem_insert a A, hav⟩
    have hEsubA : E ⊆ A := by
      rintro x ⟨hx, hxu⟩
      rcases mem_insert_iff.mp hx with rfl | hxA
      · exact absurd hxu hau
      · exact hxA
    have hEF : E ∪ F = insert a A := by
      rw [hEdef, hFdef, ← inter_union_distrib_left]
      exact inter_eq_left.mpr huv
    have hKsplit : E ∪ (F ∪ B) = K := by
      rw [← union_assoc, hEF]; exact hKeq
    have hclEu : closure E ⊆ u := closure_minimal inter_subset_right hu
    have hFsub : F ⊆ ({a} : Set ℂ) ∪ (closure A ∩ v) := by
      rintro y ⟨hy, hyv⟩
      rcases mem_insert_iff.mp hy with rfl | hyA
      · exact Or.inl rfl
      · exact Or.inr ⟨subset_closure hyA, hyv⟩
    have hclFsub : closure F ⊆ ({a} : Set ℂ) ∪ (closure A ∩ v) :=
      closure_minimal hFsub (isClosed_singleton.union (isClosed_closure.inter hv))
    have hsep1 : Disjoint (closure E) (F ∪ B) := by
      rw [Set.disjoint_left]
      rintro x hxE (hxF | hxB)
      · have hxu : x ∈ u := hclEu hxE
        exact (eq_empty_iff_forall_notMem.mp huvd) x ⟨hxF.1, hxu, hxF.2⟩
      · exact (Set.disjoint_left.mp hsepA) (closure_mono hEsubA hxE) hxB
    have hsep2 : Disjoint E (closure (F ∪ B)) := by
      rw [Set.disjoint_left]
      rintro x hxE hxcl
      rw [closure_union] at hxcl
      rcases hxcl with hxclF | hxclB
      · have hxA : x ∈ A := hEsubA hxE
        have hxu : x ∈ u := hxE.2
        rcases hclFsub hxclF with hxa | ⟨-, hxv⟩
        · have hxa' : x = a := mem_singleton_iff.mp hxa
          rw [hxa'] at hxu
          exact hau hxu
        · exact (eq_empty_iff_forall_notMem.mp huvd) x ⟨mem_insert_of_mem a hxA, hxu, hxv⟩
      · exact (Set.disjoint_left.mp hsepB) (hEsubA hxE) hxclB
    exact (not_isPreconnected_of_separated_union hKsplit hsep1 hsep2 hEne
      ⟨a, Or.inl ⟨mem_insert a A, hav⟩⟩) hK
  rcases (huv (mem_insert a A)) with hau | hav
  · exact key v u hv hu (by rwa [union_comm]) (by rw [inter_comm v u]; exact huvd) hnv hnu hau
  · exact key u v hu hv huv huvd hnu hnv hav

/-- **A nondegenerate continuum contains a preconnected non-compact subset.**  Equivalently, a
compact preconnected subset of `ℂ` all of whose preconnected subsets are compact is a single
point. -/
theorem exists_preconnected_noncompact_of_nontrivial_continuum {C : Set ℂ}
    (hCk : IsCompact C) (hCp : IsPreconnected C) (hCnt : C.Nontrivial) :
    ∃ D : Set ℂ, D ⊆ C ∧ IsPreconnected D ∧ ¬ IsCompact D := by
  obtain ⟨a, haC, b, hbC, hab⟩ := hCnt
  set SS : Set (Set ℂ) := {K | K ⊆ C ∧ IsCompact K ∧ IsPreconnected K ∧ a ∈ K ∧ b ∈ K} with hSS
  have hCmem : C ∈ SS := ⟨subset_rfl, hCk, hCp, haC, hbC⟩
  have hchain : ∀ c ⊆ SS, IsChain (· ⊆ ·) c → ∃ lb ∈ SS, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hch
    rcases c.eq_empty_or_nonempty with hcem | hcne
    · rw [hcem]
      exact ⟨C, hCmem, by simp⟩
    · obtain ⟨s0, hs0⟩ := hcne
      refine ⟨⋂₀ c, ⟨?_, ?_, ?_, ?_, ?_⟩, fun s hs => sInter_subset_of_mem hs⟩
      · exact (sInter_subset_of_mem hs0).trans (hc hs0).1
      · exact ((hc hs0).2.1).of_isClosed_subset
          (isClosed_sInter fun s hs => ((hc hs).2.1).isClosed) (sInter_subset_of_mem hs0)
      · exact isPreconnected_sInter_of_chain hch ⟨s0, hs0⟩ (fun s hs => (hc hs).2.1)
          fun s hs => (hc hs).2.2.1
      · exact mem_sInter.mpr fun s hs => (hc hs).2.2.2.1
      · exact mem_sInter.mpr fun s hs => (hc hs).2.2.2.2
  obtain ⟨K, hKmin⟩ := zorn_superset SS hchain
  obtain ⟨hKC, hKk, hKp, haK, hbK⟩ := hKmin.1
  have hmin : ∀ K' ∈ SS, K' ⊆ K → K ⊆ K' := fun K' hK' hsub => hKmin.2 hK' hsub
  have hKpre : IsPreconnected (K \ {a}) := by
    by_contra hnot
    rw [isPreconnected_iff_subset_of_disjoint_closed] at hnot
    push_neg at hnot
    obtain ⟨u, v, hu, hv, huv, huvd, hnu, hnv⟩ := hnot
    set A : Set ℂ := (K \ {a}) ∩ u with hAdef
    set B : Set ℂ := (K \ {a}) ∩ v with hBdef
    have hAunionB : A ∪ B = K \ {a} := by
      rw [hAdef, hBdef, ← inter_union_distrib_left]
      exact inter_eq_left.mpr huv
    have hAne : A.Nonempty := by
      obtain ⟨x, hx⟩ := not_subset.mp hnv
      exact ⟨x, hx.1, (huv hx.1).resolve_right hx.2⟩
    have hBne : B.Nonempty := by
      obtain ⟨x, hx⟩ := not_subset.mp hnu
      exact ⟨x, hx.1, (huv hx.1).resolve_left hx.2⟩
    have hABd : Disjoint A B := by
      rw [Set.disjoint_left]
      rintro x ⟨hxK, hxu⟩ ⟨-, hxv⟩
      exact (eq_empty_iff_forall_notMem.mp huvd) x ⟨hxK, hxu, hxv⟩
    have hclAsub : closure A ⊆ K ∩ u :=
      closure_minimal (fun x hx => ⟨diff_subset hx.1, hx.2⟩) (hKk.isClosed.inter hu)
    have hclBsub : closure B ⊆ K ∩ v :=
      closure_minimal (fun x hx => ⟨diff_subset hx.1, hx.2⟩) (hKk.isClosed.inter hv)
    have hsepA : Disjoint (closure A) B := by
      rw [Set.disjoint_left]
      rintro x hxA hxB
      exact (eq_empty_iff_forall_notMem.mp huvd) x ⟨hxB.1, (hclAsub hxA).2, hxB.2⟩
    have hsepB : Disjoint A (closure B) := by
      rw [Set.disjoint_left]
      rintro x hxA hxB
      exact (eq_empty_iff_forall_notMem.mp huvd) x ⟨hxA.1, hxA.2, (hclBsub hxB).2⟩
    have hclA : closure A ⊆ {a} ∪ A := by
      intro x hx
      have hx' : x ∈ K ∩ u := hclAsub hx
      rcases (show x ∈ {a} ∪ (K \ {a}) from by
        rw [union_sdiff_cancel (show ({a} : Set ℂ) ⊆ K from by simpa using haK)]; exact hx'.1) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hx'.2⟩
    have hclB : closure B ⊆ {a} ∪ B := by
      intro x hx
      have hx' : x ∈ K ∩ v := hclBsub hx
      rcases (show x ∈ {a} ∪ (K \ {a}) from by
        rw [union_sdiff_cancel (show ({a} : Set ℂ) ⊆ K from by simpa using haK)]; exact hx'.1) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hx'.2⟩
    have hAclosed : IsClosed ({a} ∪ A) := by
      rw [← closure_subset_iff_isClosed, closure_union, closure_singleton]
      rintro x (rfl | hx)
      · exact Or.inl rfl
      · exact hclA hx
    have hBclosed : IsClosed ({a} ∪ B) := by
      rw [← closure_subset_iff_isClosed, closure_union, closure_singleton]
      rintro x (rfl | hx)
      · exact Or.inl rfl
      · exact hclB hx
    have hAclK : {a} ∪ A ⊆ K := by
      rintro x (rfl | hx)
      · exact haK
      · exact hx.1.1
    have hBclK : {a} ∪ B ⊆ K := by
      rintro x (rfl | hx)
      · exact haK
      · exact hx.1.1
    have hApre : IsPreconnected ({a} ∪ A) := by
      rw [← insert_eq]
      exact isPreconnected_insert_of_compl_eq hKp haK hAunionB hsepA hsepB
    have hBpre : IsPreconnected ({a} ∪ B) := by
      rw [← insert_eq]
      exact isPreconnected_insert_of_compl_eq hKp haK (by rw [union_comm]; exact hAunionB)
        hsepB.symm hsepA.symm
    have hbK' : b ∈ K \ {a} := ⟨hbK, by simpa using (Ne.symm hab)⟩
    rw [← hAunionB] at hbK'
    rcases hbK' with hbA | hbB
    · have hmem : {a} ∪ A ∈ SS :=
        ⟨hAclK.trans hKC, hKk.of_isClosed_subset hAclosed hAclK, hApre, Or.inl rfl, Or.inr hbA⟩
      have hKsub := hmin ({a} ∪ A) hmem hAclK
      obtain ⟨y, hy⟩ := hBne
      rcases hKsub hy.1.1 with hya | hyA
      · exact hy.1.2 hya
      · exact (Set.disjoint_left.mp hABd) hyA hy
    · have hmem : {a} ∪ B ∈ SS :=
        ⟨hBclK.trans hKC, hKk.of_isClosed_subset hBclosed hBclK, hBpre, Or.inl rfl, Or.inr hbB⟩
      have hKsub := hmin ({a} ∪ B) hmem hBclK
      obtain ⟨y, hy⟩ := hAne
      rcases hKsub hy.1.1 with hya | hyB
      · exact hy.1.2 hya
      · exact (Set.disjoint_left.mp hABd) hy hyB
  refine ⟨K \ {a}, diff_subset.trans hKC, hKpre, ?_⟩
  intro hc
  have hcl : a ∈ closure (K \ {a}) :=
    mem_closure_diff_singleton_of_isPreconnected hKp haK ⟨b, hbK, by simpa using (Ne.symm hab)⟩
  have : a ∈ K \ {a} := by rw [← hc.isClosed.closure_eq]; exact hcl
  exact this.2 (mem_singleton a)

/-- **An unbounded complementary component.**  If `Z ⊆ ℂ` is closed, every preconnected subset of
`Z` is compact, and `Zᶜ` is nonempty, then some connected component of `Zᶜ` is unbounded. -/
theorem exists_unbounded_component_compl_of_preconnected_compact {Z : Set ℂ} (hZ : IsClosed Z)
    (hcomp : ∀ C : Set ℂ, C ⊆ Z → IsPreconnected C → IsCompact C) (hne : Zᶜ.Nonempty) :
    ∃ z ∈ Zᶜ, ∀ R : ℝ, ∃ w ∈ connectedComponentIn Zᶜ z, R ≤ ‖w‖ := by
  -- every preconnected subset of `Z` is a subsingleton
  have htd : ∀ C : Set ℂ, C ⊆ Z → IsPreconnected C → C.Subsingleton := by
    intro C hCZ hCpre
    by_contra hnt
    rw [not_subsingleton_iff] at hnt
    obtain ⟨D, hDC, hDpre, hDnc⟩ :=
      exists_preconnected_noncompact_of_nontrivial_continuum (hcomp C hCZ hCpre) hCpre hnt
    exact hDnc (hcomp D (hDC.trans hCZ) hDpre)
  by_contra hcon
  push_neg at hcon
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨R, hR⟩ := hcon z₀ hz₀
  have hUsubR : connectedComponentIn Zᶜ z₀ ⊆ closedBall (0 : ℂ) R := by
    intro w hw
    rw [mem_closedBall, dist_zero_right]
    exact le_of_lt (hR w hw)
  set F : Set ℂ := Z ∩ closedBall (0 : ℂ) R with hFdef
  have hFc : IsCompact F := by
    rw [hFdef]
    exact (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
      (hZ.inter Metric.isClosed_closedBall) inter_subset_right
  have hFtd : ∀ E : Set ℂ, E ⊆ F → IsPreconnected E → E.Subsingleton := by
    intro E hE hEpre
    refine htd E ?_ hEpre
    rw [hFdef] at hE
    exact hE.trans inter_subset_left
  have hFpre : IsPreconnected Fᶜ :=
    Work.Smooth.JordanSeparation.isPreconnected_compl_of_totallyDisconnected hFc hFtd
  have hZc_open : IsOpen (Zᶜ) := hZ.isOpen_compl
  have hUopen : IsOpen (connectedComponentIn Zᶜ z₀) := hZc_open.connectedComponentIn
  have hUsubFc : connectedComponentIn Zᶜ z₀ ⊆ Fᶜ := by
    intro x hx hxF
    rw [hFdef] at hxF
    exact (connectedComponentIn_subset Zᶜ z₀ hx) hxF.1
  have hZcU_open : IsOpen (Zᶜ \ connectedComponentIn Zᶜ z₀) := by
    have hcov : Zᶜ \ connectedComponentIn Zᶜ z₀
        = ⋃ y ∈ (Zᶜ \ connectedComponentIn Zᶜ z₀), connectedComponentIn Zᶜ y := by
      apply Subset.antisymm
      · intro y hy
        exact mem_iUnion₂.mpr ⟨y, hy, mem_connectedComponentIn hy.1⟩
      · intro y hy
        obtain ⟨y', hy', hyy'⟩ := mem_iUnion₂.mp hy
        refine ⟨connectedComponentIn_subset Zᶜ y' hyy', ?_⟩
        intro hyU
        have h1 : y' ∈ connectedComponentIn Zᶜ y' := mem_connectedComponentIn hy'.1
        have h2 : connectedComponentIn Zᶜ y' = connectedComponentIn Zᶜ y :=
          connectedComponentIn_eq hyy'
        have h3 : connectedComponentIn Zᶜ y = connectedComponentIn Zᶜ z₀ :=
          (connectedComponentIn_eq hyU).symm
        rw [h2, h3] at h1
        exact hy'.2 h1
    rw [hcov]
    exact isOpen_iUnion fun y => isOpen_iUnion fun _ => hZc_open.connectedComponentIn
  have hFcU_open : IsOpen (Fᶜ \ connectedComponentIn Zᶜ z₀) := by
    have hset : Fᶜ \ connectedComponentIn Zᶜ z₀
        = (Zᶜ \ connectedComponentIn Zᶜ z₀) ∪ (closedBall (0 : ℂ) R)ᶜ := by
      rw [hFdef, compl_inter]
      ext x
      simp only [mem_sdiff, mem_union, mem_compl_iff]
      constructor
      · rintro ⟨hx | hx, hxU⟩
        · exact Or.inl ⟨hx, hxU⟩
        · exact Or.inr hx
      · rintro (⟨hx, hxU⟩ | hx)
        · exact ⟨Or.inl hx, hxU⟩
        · exact ⟨Or.inr hx, fun hmem => hx (hUsubR hmem)⟩
    rw [hset]
    exact hZcU_open.union Metric.isClosed_closedBall.isOpen_compl
  have hdisj : Disjoint (connectedComponentIn Zᶜ z₀) (Fᶜ \ connectedComponentIn Zᶜ z₀) := by
    rw [disjoint_left]
    intro x hxU hx
    exact hx.2 hxU
  have hcover : Fᶜ ⊆ connectedComponentIn Zᶜ z₀ ∪ (Fᶜ \ connectedComponentIn Zᶜ z₀) := by
    intro x hx
    by_cases h : x ∈ connectedComponentIn Zᶜ z₀
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  have hFcU : Fᶜ ⊆ connectedComponentIn Zᶜ z₀ := by
    rcases hFpre.subset_or_subset hUopen hFcU_open hdisj hcover with h | h
    · exact h
    · exfalso
      have hz0U : z₀ ∈ connectedComponentIn Zᶜ z₀ := mem_connectedComponentIn hz₀
      exact (h (hUsubFc hz0U)).2 hz0U
  set w : ℂ := ((max R 0 + 1 : ℝ) : ℂ) with hwdef
  have hwnorm : ‖w‖ = max R 0 + 1 := by
    rw [hwdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  have hwR : R < ‖w‖ := by
    rw [hwnorm]
    have := le_max_left R (0 : ℝ)
    linarith
  have hw_ball : w ∈ (closedBall (0 : ℂ) R)ᶜ := by
    rw [mem_compl_iff, mem_closedBall, dist_zero_right]
    exact not_le.mpr hwR
  have hwFc : w ∈ Fᶜ := by
    rw [hFdef, compl_inter]
    exact Or.inr hw_ball
  have hmem : w ∈ closedBall (0 : ℂ) R := hUsubR (hFcU hwFc)
  rw [mem_closedBall, dist_zero_right] at hmem
  exact absurd hmem (not_le.mpr hwR)

end

end Work.BoxShrink.PinchOff
