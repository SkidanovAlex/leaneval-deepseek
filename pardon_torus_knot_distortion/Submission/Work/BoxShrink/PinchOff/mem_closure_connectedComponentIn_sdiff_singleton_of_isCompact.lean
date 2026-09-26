import Mathlib
import Submission.Work.BoxShrink.PinchOff.isPreconnected_sInter_of_chain

/-!
# A component of `S \ {a}` accumulates at `a`

`Work.BoxShrink.PinchOff.mem_closure_connectedComponentIn_sdiff_singleton_of_isCompact`: if `S` is a
(preconnected) continuum in `ℂ` and `a, b ∈ S` with `b ≠ a`, then `a` lies in the closure of the
connected component of `b` in `S \ {a}`.

This is the *boundary bumping theorem* for the special case `U = X \ {a}` (X compact connected):
the components of a proper open subset of a continuum bump into its complement.

The proof uses an *irreducible* subcontinuum: by Zorn's lemma (chain-intersections of compact
preconnected sets are preconnected, `isPreconnected_sInter_of_chain`) choose `K ⊆ S` minimal among
the compact preconnected subsets containing `a` and `b`.  For such a `K` the complement of a point
is preconnected (Whyburn's theorem 9.8: a separation of `K \ {a}` would produce a smaller
subcontinuum containing both `a` and `b`), so `K \ {a} ⊆ connectedComponentIn (S \ {a}) b`, while
`a ∈ closure (K \ {a})` since `K` is preconnected and `b ∈ K \ {a}`.  Hence
`a ∈ closure (connectedComponentIn (S \ {a}) b)`.
-/

namespace Work.BoxShrink.PinchOff

open Set

noncomputable section

/-! ## Auxiliary facts about preconnected sets (Whyburn 9.8 and its companions) -/

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

/-! ## An irreducible subcontinuum -/

/-- **An irreducible subcontinuum.**  A compact preconnected subset of `ℂ` containing two points
contains a minimal such subset. -/
theorem exists_minimal_subcontinuum {S : Set ℂ} (hcpt : IsCompact S) (hS : IsPreconnected S)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) :
    ∃ K : Set ℂ, K ⊆ S ∧ IsCompact K ∧ IsPreconnected K ∧ a ∈ K ∧ b ∈ K ∧
      ∀ K' : Set ℂ, K' ⊆ K → IsCompact K' → IsPreconnected K' → a ∈ K' → b ∈ K' → K' = K := by
  set SS : Set (Set ℂ) := {K | K ⊆ S ∧ IsCompact K ∧ IsPreconnected K ∧ a ∈ K ∧ b ∈ K} with hSS
  have hSmem : S ∈ SS := ⟨subset_rfl, hcpt, hS, ha, hb⟩
  have hchain : ∀ c ⊆ SS, IsChain (· ⊆ ·) c → ∃ lb ∈ SS, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hch
    rcases c.eq_empty_or_nonempty with hcem | hcne
    · rw [hcem]
      exact ⟨S, hSmem, by simp⟩
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
  obtain ⟨hKmem, hKmini⟩ := hKmin
  refine ⟨K, hKmem.1, hKmem.2.1, hKmem.2.2.1, hKmem.2.2.2.1, hKmem.2.2.2.2, ?_⟩
  intro K' hK'K hK'c hK'p hK'a hK'b
  refine Subset.antisymm hK'K ?_
  exact hKmini ⟨hK'K.trans hKmem.1, hK'c, hK'p, hK'a, hK'b⟩ hK'K

/-- **Whyburn's theorem 9.8 for an irreducible continuum.**  If `K` is compact and preconnected,
`a ≠ b`, and `K` is minimal among the compact preconnected subsets containing `a` and `b`, then
`K \ {a}` is preconnected. -/
theorem isPreconnected_sdiff_singleton_of_isMinimal {K : Set ℂ} {a b : ℂ}
    (hKk : IsCompact K) (hKp : IsPreconnected K) (haK : a ∈ K) (hbK : b ∈ K) (hab : a ≠ b)
    (hmin : ∀ K' : Set ℂ, K' ⊆ K → IsCompact K' → IsPreconnected K' → a ∈ K' → b ∈ K' →
      K' = K) :
    IsPreconnected (K \ {a}) := by
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
    closure_minimal (fun x hx => ⟨sdiff_subset hx.1, hx.2⟩) (hKk.isClosed.inter hu)
  have hclBsub : closure B ⊆ K ∩ v :=
    closure_minimal (fun x hx => ⟨sdiff_subset hx.1, hx.2⟩) (hKk.isClosed.inter hv)
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
      rw [union_sdiff_cancel (show ({a} : Set ℂ) ⊆ K from by simpa using haK)]
      exact hx'.1) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hx'.2⟩
  have hclB : closure B ⊆ {a} ∪ B := by
    intro x hx
    have hx' : x ∈ K ∩ v := hclBsub hx
    rcases (show x ∈ {a} ∪ (K \ {a}) from by
      rw [union_sdiff_cancel (show ({a} : Set ℂ) ⊆ K from by simpa using haK)]
      exact hx'.1) with h | h
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
  have hbK' : b ∈ K \ {a} := ⟨hbK, by simpa using hab.symm⟩
  rw [← hAunionB] at hbK'
  rcases hbK' with hbA | hbB
  · have hEq : {a} ∪ A = K :=
      hmin ({a} ∪ A) hAclK (hKk.of_isClosed_subset hAclosed hAclK) hApre (Or.inl rfl)
        (Or.inr hbA)
    have hKsub : K ⊆ {a} ∪ A := hEq ▸ subset_rfl
    obtain ⟨y, hy⟩ := hBne
    rcases hKsub hy.1.1 with hya | hyA
    · exact hy.1.2 hya
    · exact (Set.disjoint_left.mp hABd) hyA hy
  · have hEq : {a} ∪ B = K :=
      hmin ({a} ∪ B) hBclK (hKk.of_isClosed_subset hBclosed hBclK) hBpre (Or.inl rfl)
        (Or.inr hbB)
    have hKsub : K ⊆ {a} ∪ B := hEq ▸ subset_rfl
    obtain ⟨y, hy⟩ := hAne
    rcases hKsub hy.1.1 with hya | hyB
    · exact hy.1.2 hya
    · exact (Set.disjoint_left.mp hABd) hy hyB

/-! ## The boundary bumping theorem -/

theorem mem_closure_connectedComponentIn_sdiff_singleton_of_isCompact {S : Set ℂ}
    (hS : IsPreconnected S) (hcpt : IsCompact S) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S)
    (hba : b ≠ a) :
    a ∈ closure (connectedComponentIn (S \ {a}) b) := by
  obtain ⟨K, hKS, hKk, hKp, haK, hbK, hKmin⟩ := exists_minimal_subcontinuum hcpt hS ha hb
  have hab : a ≠ b := hba.symm
  have hKpre : IsPreconnected (K \ {a}) :=
    isPreconnected_sdiff_singleton_of_isMinimal hKk hKp haK hbK hab hKmin
  have hbK' : b ∈ K \ {a} := ⟨hbK, by simpa using hba⟩
  have hsub : K \ {a} ⊆ S \ {a} := fun x hx => ⟨hKS hx.1, hx.2⟩
  have hsubC : K \ {a} ⊆ connectedComponentIn (S \ {a}) b :=
    hKpre.subset_connectedComponentIn hbK' hsub
  have hacl : a ∈ closure (K \ {a}) :=
    mem_closure_diff_singleton_of_isPreconnected hKp haK ⟨b, hbK'⟩
  exact closure_mono hsubC hacl

end

end Work.BoxShrink.PinchOff
