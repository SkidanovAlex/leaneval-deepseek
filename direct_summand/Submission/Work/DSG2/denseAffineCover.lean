import Mathlib
import Submission.Work.DSG2.privateAffineOpens
import Submission.Work.DSG2.dense_of_meets_irreducibleComponents

/-!
# A finite affine open cover with dense intersection

`Work.DSG2.denseAffineCover`: every Noetherian scheme `X` admits a finite family of affine opens
`U i` covering `X` whose intersection is dense in `X`.

The construction is as follows.  Start with any finite affine open cover `W a` of `X` (which
exists because `X` is Noetherian, hence quasi-compact) and let `C k` run over the finitely many
irreducible components of `X`.  For every component `C` pick a nonempty affine open `A C` inside
the *private region* of `C`, i.e. inside the complement of the union of all the other components
(`Work.DSG2.privateAffineOpens`).  These private regions are pairwise disjoint and each `A C` is
contained in `C`.  Now replace each `W a` by

  `U a = W a ⊔ ⨆ (k : components missing from W a), A k`.

This is a finite disjoint union of affine opens, hence affine.  Every `A k` meets `C k` and is
disjoint from `W a` whenever `W a` misses `C k`, so each `U a` meets *every* irreducible
component of `X`; and the `U a` still cover `X` because they contain the `W a`.  Finally a finite
intersection of nonempty opens of a component is nonempty (a component is irreducible), so the
intersection of the `U a` meets every component, and an open set meeting every irreducible
component is dense (`Work.DSG2.dense_of_meets_irreducibleComponents`).
-/

open CategoryTheory AlgebraicGeometry
open scoped Function

set_option linter.style.haveILetI false

namespace Work.DSG2

theorem denseAffineCover {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsNoetherian X] :
    ∃ (m : ℕ) (U : Fin m → X.affineOpens),
      (⨆ i, (U i : X.Opens)) = ⊤ ∧ Dense (((⨅ i, (U i : X.Opens)) : X.Opens) : Set X) := by
  classical
  -- Step 1: a finite affine open cover of `X`.
  let 𝒰 := X.affineCover.finiteSubcover
  let W : 𝒰.I₀ → X.affineOpens := fun a => ⟨(𝒰.f a).opensRange, isAffineOpen_opensRange _⟩
  have hWcov : ⨆ a, (W a : X.Opens) = ⊤ := by
    rw [← Scheme.OpenCover.iSup_opensRange 𝒰]
  -- Step 2: the irreducible components of `X`, indexed by a finite type.
  let κ := {C : Set X // C ∈ irreducibleComponents X}
  haveI : Fintype κ := (finite_irreducibleComponents_of_isNoetherian (X := X)).fintype
  let C : κ → Set X := fun k => k.1
  have hCmem : ∀ k : κ, C k ∈ irreducibleComponents X := fun k => k.2
  -- Step 3: nonempty affine opens inside the private regions of the components.
  obtain ⟨A, hAne, hApriv⟩ := privateAffineOpens X
  let Aκ : κ → X.affineOpens := fun k => A (C k) (hCmem k)
  have hAκne : ∀ k, ((Aκ k : X.Opens) : Set X).Nonempty := fun k => hAne (C k) (hCmem k)
  -- Each `A k` is contained in `C k`.
  have hAκsub : ∀ k, ((Aκ k : X.Opens) : Set X) ⊆ C k := by
    intro k x hx
    have hx' : x ∈ (⋃₀ (irreducibleComponents X \ {C k}))ᶜ := hApriv (C k) (hCmem k) hx
    have hxU : x ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]; exact Set.mem_univ x
    obtain ⟨D, hD, hxD⟩ := Set.mem_sUnion.mp hxU
    by_cases h : D = C k
    · rwa [h] at hxD
    · have hD' : D ∈ irreducibleComponents X \ {C k} := ⟨hD, by simpa using h⟩
      exact absurd (Set.mem_sUnion_of_mem (t := D) hxD hD') hx'
  -- ... and the `A k` are pairwise disjoint (both are contained in the respective private region).
  have hAκdisj_set : ∀ k k' : κ, k ≠ k' →
      Disjoint ((Aκ k : X.Opens) : Set X) ((Aκ k' : X.Opens) : Set X) := by
    intro k k' hne
    rw [Set.disjoint_left]
    intro x hxk hxk'
    have hne' : C k' ≠ C k := fun h => hne (Subtype.ext h.symm)
    have h1 : x ∈ (⋃₀ (irreducibleComponents X \ {C k}))ᶜ := hApriv (C k) (hCmem k) hxk
    have h1' : x ∈ ⋃₀ (irreducibleComponents X \ {C k}) :=
      Set.mem_sUnion_of_mem (t := C k') (hAκsub k' hxk')
        ⟨hCmem k', by simpa using hne'⟩
    exact h1 h1'
  have hAκdisj : Pairwise (fun k k' : κ => Disjoint (Aκ k : X.Opens) (Aκ k' : X.Opens)) :=
    fun k k' hne => (TopologicalSpace.Opens.coe_disjoint).mp (hAκdisj_set k k' hne)
  -- Step 4: the spread cover `U a = W a ⊔ ⨆ (k missing from W a), A k`.
  let spread : 𝒰.I₀ → X.Opens := fun a =>
    (W a : X.Opens) ⊔ ⨆ (k : {k : κ // Disjoint (W a : Set X) (C k)}), (Aκ k.1 : X.Opens)
  have hspread_aff : ∀ a, IsAffineOpen (spread a) := by
    intro a
    show IsAffineOpen ((W a : X.Opens) ⊔
      ⨆ (k : {k : κ // Disjoint (W a : Set X) (C k)}), (Aκ k.1 : X.Opens))
    have h1 : IsAffineOpen
        (⨆ (k : {k : κ // Disjoint (W a : Set X) (C k)}), (Aκ k.1 : X.Opens)) := by
      refine IsAffineOpen.iSup_of_disjoint (fun k => (Aκ k.1).2) ?_
      intro k k' hne
      exact hAκdisj (i := k.1) (j := k'.1) (fun h => hne (Subtype.ext h))
    have h2 : Disjoint (W a : X.Opens)
        (⨆ (k : {k : κ // Disjoint (W a : Set X) (C k)}), (Aκ k.1 : X.Opens)) := by
      rw [disjoint_iSup_iff]
      intro k
      rw [← TopologicalSpace.Opens.coe_disjoint]
      exact (k.2).mono_right (hAκsub k.1)
    exact (W a).2.sup_of_disjoint h1 h2
  -- Each `spread a` meets every irreducible component.
  have hspread_meets : ∀ (a : 𝒰.I₀) (k : κ),
      (((spread a : X.Opens) : Set X) ∩ C k).Nonempty := by
    intro a k
    by_cases h : Disjoint (W a : Set X) (C k)
    · obtain ⟨x, hxA⟩ := hAκne k
      have hxC : x ∈ C k := hAκsub k hxA
      have hle : (Aκ k : X.Opens) ≤ spread a := by
        show (Aκ k : X.Opens) ≤ (W a : X.Opens) ⊔
          ⨆ (k' : {k : κ // Disjoint (W a : Set X) (C k)}), (Aκ k'.1 : X.Opens)
        exact (le_iSup (fun k' : {k : κ // Disjoint (W a : Set X) (C k)} =>
          (Aκ k'.1 : X.Opens)) ⟨k, h⟩).trans le_sup_right
      exact ⟨x, hle hxA, hxC⟩
    · obtain ⟨x, hxW, hxC⟩ := Set.not_disjoint_iff.mp h
      have hle : (W a : X.Opens) ≤ spread a := le_sup_left
      exact ⟨x, hle hxW, hxC⟩
  -- The spread cover still covers `X`.
  have hspread_cov : ⨆ a, spread a = ⊤ := by
    rw [eq_top_iff, ← hWcov]
    exact iSup_mono (fun a => le_sup_left)
  -- Step 5: reindex by `Fin m` and conclude.
  let e := Fintype.equivFin 𝒰.I₀
  let U : Fin (Fintype.card 𝒰.I₀) → X.affineOpens :=
    fun i => ⟨spread (e.symm i), hspread_aff _⟩
  refine ⟨Fintype.card 𝒰.I₀, U, ?_, ?_⟩
  · rw [show (⨆ i : Fin (Fintype.card 𝒰.I₀), (U i : X.Opens)) = ⨆ i, spread (e.symm i)
        from rfl, Equiv.iSup_comp, hspread_cov]
  · refine dense_of_meets_irreducibleComponents _ ?_
    intro Cc hCc
    have hirr : IsIrreducible Cc := hCc.1
    -- the intersection of the `U i` is `⋂ i, ↑(U i)`.
    have himg : (⋂₀ ↑(Finset.univ.image
        (fun i : Fin (Fintype.card 𝒰.I₀) => ((U i : X.Opens) : Set X))) : Set X)
        = ⋂ i, ((U i : X.Opens) : Set X) := by
      ext x
      simp
    -- a finite intersection of nonempty opens of the irreducible component `Cc` is nonempty.
    have hfin' : (Cc ∩ ⋂ i : Fin (Fintype.card 𝒰.I₀),
        ((U i : X.Opens) : Set X)).Nonempty := by
      have h := (isIrreducible_iff_sInter.mp hirr)
        (Finset.univ.image (fun i : Fin (Fintype.card 𝒰.I₀) => ((U i : X.Opens) : Set X)))
        (by intro u hu; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu; exact (U i).1.isOpen)
        (by
          intro u hu
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
          simpa [Set.inter_comm] using hspread_meets (e.symm i) ⟨Cc, hCc⟩)
      rwa [himg] at h
    rw [TopologicalSpace.Opens.coe_iInf, Set.inter_comm]
    exact hfin'

end Work.DSG2
