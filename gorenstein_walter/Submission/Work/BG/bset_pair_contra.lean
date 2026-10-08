import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.lemma24
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.lemma36Defs

namespace Work.BG

open OddOrder.RepresentationTheory

/-! ## Auxiliary combinatorial lemma

A finite set carrying a fixed-point-free involution has even cardinality.  This is what makes
`|𝒮(χ)|` even in the crux case of BG Lemma 3.6: `ν ↦ ν^s` is a fixed-point-free involution
on `𝒮(χ)` (`bset_orbit_struct` part 1, together with `hfix` and `s² = 1`). -/

/-- A `Finset` carrying a fixed-point-free involution has even cardinality.  Proof by strong
induction: remove an element `x` together with its partner `f x`, which reduces the cardinality
by `2` and preserves all the hypotheses. -/
private theorem even_card_of_fpf_involution {α : Type*} (f : α → α) :
    ∀ (F : Finset α), (∀ x ∈ F, f x ∈ F) → (∀ x, f (f x) = x) →
      (∀ x ∈ F, f x ≠ x) → Even F.card := by
  classical
  intro F
  induction F using Finset.strongInduction with
  | H F ih =>
    intro hmaps hinv hfp
    rcases F.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hfxF : f x ∈ F := hmaps x hx
      have hfxne : f x ≠ x := hfp x hx
      set F' : Finset α := (F.erase x).erase (f x) with hF'def
      have hF'mem : ∀ y ∈ F', y ∈ F ∧ y ≠ x ∧ y ≠ f x := by
        intro y hy
        rw [hF'def] at hy
        obtain ⟨hyfx, hyex⟩ := Finset.mem_erase.mp hy
        obtain ⟨hyx, hyF⟩ := Finset.mem_erase.mp hyex
        exact ⟨hyF, hyx, hyfx⟩
      have hF'sub : F' ⊂ F := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun y hy => (hF'mem y hy).1, ?_⟩
        intro h
        have : f x ∈ F' := by rw [h]; exact hfxF
        rw [hF'def] at this
        exact Finset.notMem_erase (f x) (F.erase x) this
      have hmaps' : ∀ y ∈ F', f y ∈ F' := by
        intro y hy
        obtain ⟨hyF, hyx, hyfx⟩ := hF'mem y hy
        rw [hF'def]
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmaps y hyF⟩⟩
        · intro h
          have : y = x := by rw [← hinv y, h, hinv x]
          exact hyx this
        · intro h
          have : y = f x := by rw [← hinv y, h]
          exact hyfx this
      have hfp' : ∀ y ∈ F', f y ≠ y := fun y hy => hfp y (hF'mem y hy).1
      have ih' : Even F'.card := ih F' hF'sub hmaps' hinv hfp'
      have hxnotin : x ∉ insert (f x) F' := by
        rw [Finset.mem_insert, not_or]
        refine ⟨hfxne.symm, ?_⟩
        intro h
        rw [hF'def] at h
        exact Finset.notMem_erase x F (Finset.mem_erase.mp h).2
      have hfxnotin : f x ∉ F' := by
        rw [hF'def]; exact Finset.notMem_erase (f x) (F.erase x)
      have hFeq : F = insert x (insert (f x) F') := by
        ext y
        rw [Finset.mem_insert, Finset.mem_insert]
        constructor
        · intro hy
          by_cases hyx : y = x
          · exact Or.inl hyx
          · right
            by_cases hyfx : y = f x
            · exact Or.inl hyfx
            · refine Or.inr ?_
              rw [hF'def]
              exact Finset.mem_erase.mpr ⟨hyfx, Finset.mem_erase.mpr ⟨hyx, hy⟩⟩
        · intro hy
          rcases hy with rfl | rfl | hy
          · exact hx
          · exact hfxF
          · exact (hF'mem y hy).1
      rw [hFeq, Finset.card_insert_of_notMem hxnotin,
        Finset.card_insert_of_notMem hfxnotin]
      exact ih'.add even_two

/-- Set version of `even_card_of_fpf_involution`. -/
private theorem even_ncard_of_fpf_involution {α : Type*} (S : Set α) (f : α → α)
    (hfin : S.Finite) (hmaps : ∀ x ∈ S, f x ∈ S) (hinv : ∀ x, f (f x) = x)
    (hfp : ∀ x ∈ S, f x ≠ x) : Even S.ncard := by
  have h := even_card_of_fpf_involution f hfin.toFinset
    (fun x hx => (Set.Finite.mem_toFinset hfin).mpr
      (hmaps x ((Set.Finite.mem_toFinset hfin).mp hx)))
    hinv (fun x hx => hfp x ((Set.Finite.mem_toFinset hfin).mp hx))
  rwa [← Set.ncard_eq_toFinset_card S hfin] at h

/-- Conjugation by `s ∈ H` fixes `t` (since `t` is central in `H`). -/
private theorem conjMulEquiv_s_t' {G : Type} [Group G] [Finite G] (C : Sec2Ctx G) :
    conjMulEquiv C.P C.s C.t = C.t := by
  apply Subtype.ext
  rw [conjMulEquiv_apply, C.t_comm_H (C.s : G) C.s.2]
  group

/-- `ν^s(t) = ν(t)`: conjugation by `s ∈ H` fixes the central involution `t` of `H₀`. -/
private theorem sconj_apply_t' {G : Type} [Group G] [Finite G]
    (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C ν C.t = ν C.t := by
  rw [sconj, conjByH_apply, conjMulEquiv_s_t' C]

/-- **Step 3 of BG Lemma 3.6 (the equality case, crux).**  Let `χ ∈ Irr(G)` and suppose
(i) every `ν ∈ 𝒮(χ)` satisfies `ν^s ∈ Λν` (`hsl`), (ii) the `Λ`-orbit of every member of `𝒮(χ)`
is contained in `𝒮(χ)` (`hsub`), (iii) every member of `𝒮(χ)` is moved by `s` (`hfix`),
(iv) no member of `𝒮(χ)` vanishes at `t` (`htval`), (v) `χ(t) = 0` (`ht`), and
(vi) `|𝒮(χ)| ≤ 3` (`hcard`, supplied in the application by `Work.BG.thm32`).
Then `False`.

Route: `𝒮(χ)` is `s`-stable (`bset_orbit_struct` part 1); by (ii) and `bset_orbit_struct` part 2
together with (i) and (iii) every `ν ∈ 𝒮(χ)` has `Λν = {ν, ν^s}`, so `𝒮(χ)` is a disjoint union of
two-element `Λ`-orbits and `|𝒮(χ)|` is even; with (vi), `𝒮(χ) = {ν₀, ν₀^s}`.  Lemma 2.4
(`Work.BG.lemma24`, using `hf`) at `t ∉ C.P.U` gives `χ(t) = ∑_{ν∈𝒮(χ)} ⟨χ, fν⟩·ν(t)` with
`⟨χ, fν⟩ = ±1` (`bset_orbit_struct` part 1) and `ν₀^s(t) = ν₀(t)` (`t` is fixed by `s`), so
`χ(t) = 2·⟨χ,fν₀⟩·ν₀(t) ≠ 0` by (iv), contradicting (v). -/
theorem bset_pair_contra {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ →
      OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hf : Work.GW2.C16.IsCoherent C f)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hχ : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ)
    (hne : (Work.GW2.C16.bset C f χ).Nonempty)
    (hcard : (Work.GW2.C16.bset C f χ).ncard ≤ 3)
    (hsl : ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ∈ Work.BG.lamOrbit C ν)
    (hsub : ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.lamOrbit C ν ⊆ Work.GW2.C16.bset C f χ)
    (hfix : ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν)
    (htval : ∀ ν ∈ Work.GW2.C16.bset C f χ, ν C.t ≠ 0)
    (ht : χ (C.t : G) = 0) : False := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  obtain ⟨ν₀, hν₀⟩ := hne
  -- `𝒮(χ)` is `s`-stable, `f` is `s`-invariant on it, and the coefficients are `±1`
  obtain ⟨hstable, _hpair⟩ := bset_orbit_struct C f hf χ (Or.inl hχ)
  have hfin : (Work.GW2.C16.bset C f χ).Finite := (lemma24 C f hf χ (Or.inl hχ)).1
  -- `ν ↦ ν^s` is a fixed-point-free involution on `𝒮(χ)`, so `|𝒮(χ)|` is even
  have heven : Even (Work.GW2.C16.bset C f χ).ncard :=
    even_ncard_of_fpf_involution (Work.GW2.C16.bset C f χ) (sconj C) hfin
      (fun ν hν => (hstable ν hν).1) (sconj_sconj C) hfix
  have hpos : 0 < (Work.GW2.C16.bset C f χ).ncard :=
    (Set.ncard_pos hfin).mpr ⟨ν₀, hν₀⟩
  have hcard2 : (Work.GW2.C16.bset C f χ).ncard = 2 := by
    obtain ⟨m, hm⟩ := heven
    omega
  have hsν₀ : sconj C ν₀ ∈ Work.GW2.C16.bset C f χ := (hstable ν₀ hν₀).1
  have hfsν₀ : f (sconj C ν₀) = f ν₀ := (hstable ν₀ hν₀).2.1
  have hcoef : ClassFunction.inner χ (f ν₀) = 1 ∨ ClassFunction.inner χ (f ν₀) = -1 :=
    (hstable ν₀ hν₀).2.2
  have hne_s : sconj C ν₀ ≠ ν₀ := hfix ν₀ hν₀
  -- `𝒮(χ)` is exactly the pair `{ν₀, ν₀^s}`
  have hpair2 : ({ν₀, sconj C ν₀} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆
      Work.GW2.C16.bset C f χ := by
    intro η hη
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rcases hη with rfl | rfl
    · exact hν₀
    · exact hsν₀
  have hpaircard : ({ν₀, sconj C ν₀} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 2 :=
    Set.ncard_pair hne_s.symm
  have hS_eq : ({ν₀, sconj C ν₀} : Set (ClassFunction ↥C.P.H0 ℂ)) =
      Work.GW2.C16.bset C f χ :=
    Set.eq_of_subset_of_ncard_le hpair2 (by rw [hcard2, hpaircard]) hfin
  -- Lemma 2.4 at `t`, evaluated on the two-element support
  have hT := (lemma24 C f hf χ (Or.inl hχ)).2.1 C.t C.t_not_mem_U
  have hsum : (∑ᶠ ν ∈ Work.GW2.C16.bset C f χ, ClassFunction.inner χ (f ν) * ν C.t)
      = 2 * (ClassFunction.inner χ (f ν₀) * ν₀ C.t) := by
    rw [← hS_eq,
      finsum_mem_insert (f := fun ν => ClassFunction.inner χ (f ν) * ν C.t)
        (by simpa using hne_s.symm) (Set.toFinite _),
      finsum_mem_singleton, hfsν₀, sconj_apply_t']
    ring
  have hval : χ (C.t : G) = 2 * (ClassFunction.inner χ (f ν₀) * ν₀ C.t) := by
    rw [hT, hsum]
  have hcoefne : ClassFunction.inner χ (f ν₀) ≠ 0 := by
    rcases hcoef with h | h <;> rw [h] <;> norm_num
  have hνt : ν₀ C.t ≠ 0 := htval ν₀ hν₀
  rw [ht] at hval
  exact (mul_ne_zero (by norm_num) (mul_ne_zero hcoefne hνt)) hval.symm

end Work.BG
