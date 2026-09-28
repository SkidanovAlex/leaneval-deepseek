import Mathlib
import Submission.Work.Cohomology.subsingleton_pdCohSub_union_clean
import Submission.Work.Thom.subsingleton_PieceCoh_genFibre
import Submission.Work.Thom.thomClass_of_finite_cover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Thom

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type} {N : ℕ}

/-! ## Set algebra for finite intersections of pieces -/

/-- The intersection over a union of two finite subfamilies. -/
theorem finInter_union (U : Fin N → Set B) (S T : Finset (Fin N)) :
    finInter U (S ∪ T) = finInter U S ∩ finInter U T := by
  simp only [finInter, Finset.coe_union, Set.biInter_union]

/-- The intersection of a finite subfamily of open pieces is open. -/
theorem isOpen_finInter {U : Fin N → Set B} (hU : ∀ k, IsOpen (U k)) (S : Finset (Fin N)) :
    IsOpen (finInter U S) :=
  S.finite_toSet.isOpen_biInter (fun k _ => hU k)

/-- The union of the finite intersections over an empty family of subfamilies is empty. -/
theorem iUnion_finInter_empty (U : Fin N → Set B) :
    (⋃ S ∈ (∅ : Finset (Finset (Fin N))), finInter U S) = (∅ : Set B) := by
  ext x; simp

/-- The union of the finite intersections over a family of open pieces is open. -/
theorem isOpen_iUnion_finInter {U : Fin N → Set B} (hU : ∀ k, IsOpen (U k))
    (A : Finset (Finset (Fin N))) : IsOpen (⋃ S ∈ A, finInter U S) := by
  refine isOpen_biUnion (s := (A : Set (Finset (Fin N)))) (f := fun S => finInter U S) ?_
  intro S _
  exact isOpen_finInter hU S

/-- The union of the finite intersections over `insert S₀ A'`. -/
theorem iUnion_finInter_insert (U : Fin N → Set B) (S₀ : Finset (Fin N))
    (A' : Finset (Finset (Fin N))) :
    (⋃ S ∈ (insert S₀ A' : Finset (Finset (Fin N))), finInter U S)
      = finInter U S₀ ∪ (⋃ S ∈ A', finInter U S) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨S, hS, hx⟩
    rw [Finset.mem_insert] at hS
    rcases hS with rfl | hS
    · exact Or.inl hx
    · exact Or.inr ⟨S, hS, hx⟩
  · rintro (hx | ⟨S, hS, hx⟩)
    · exact ⟨S₀, Finset.mem_insert_self S₀ A', hx⟩
    · exact ⟨S, Finset.mem_insert_of_mem hS, hx⟩

/-! ## The main theorem -/

/-- **Vanishing below the rank on finite unions of finite intersections of chart pieces** — an
island-clean copy of the existing result `Work.Thom.subsingleton_PieceCoh_iUnion_finInter`, whose
own module cannot be imported together with this file's import island.

Let `U : Fin N → Set B` be open pieces each contained in a chart `Z.baseSet (cc k)` of a real
bundle `Z` of finite-dimensional real fibre `F`.  Then for every finite family `A` of nonempty
subfamilies of `Fin N` and every `m < Module.finrank ℝ F`, the relative cohomology of the Thom pair
over the piece `⋃ S ∈ A, Work.Thom.finInter U S` vanishes in degree `m`.

This is the low-degree input of the finite-cover Thom isomorphism theorem
(`Work.Thom.thomClass_of_finite_cover`), needed for the family of unions of intersections that the
induction over the cover produces.

NOTE (import islands — read before starting).  This workspace contains several mutually
incompatible copies of the same constants: `Work.Cohomology.Yt` is declared in four different
modules and `Work.Cohomology.dualZ` in two.  Your file must stay inside one island.  The permitted
imports are the transitive closure of

  `Submission.Work.Thom.subsingleton_PieceCoh_genFibre`,
  `Submission.Work.Thom.thomClass_of_finite_cover`,
  `Submission.Work.Cohomology.subsingleton_pdCohSub_union_clean`

(the first gives the chart-local base case `Work.Thom.subsingleton_PieceCoh_genFibre`; the second
gives `Work.Thom.PieceCoh`, `Work.Thom.finInter`, `Work.Thom.mem_finInter`,
`Work.Thom.subsingleton_PieceCoh_of_isEmpty` and the `Eq`-transport helper
`Work.Thom.subsingleton_PieceCoh_of_eq`; the third is the in-island two-piece union step
`Work.Cohomology.subsingleton_pdCohSub_union_clean`).  Check with `lake build` of your own module;
do NOT import `Submission.Work.Cohomology.subsingleton_pdCohSub_union`,
`Submission.Work.Cohomology.prod_sphere_aux` or
`Submission.Work.Thom.subsingleton_PieceCoh_iUnion_finInter` — they are in a different island and, if
imported, break the environment with a duplicated constant.

PROOF ROUTE.  The existing proof sits in
`Submission/Work/Thom/subsingleton_PieceCoh_iUnion_finInter.lean` (lines 100–228) and can be copied
almost verbatim.  It is a strong induction on `A.card` with the degree `m` universally quantified:
* `A = ∅`: the piece is `∅`, and `Work.Thom.subsingleton_PieceCoh_of_isEmpty` gives the vanishing;
* `A = insert S₀ A'`: write the piece as `finInter U S₀ ∪ ⋃ S ∈ A', finInter U S`; the first piece is
  chart-local (`hS₀ne.choose ∈ S₀`, so `finInter U S₀ ⊆ U (hS₀ne.choose) ⊆ Z.baseSet (cc _)`, hence
  `Work.Thom.subsingleton_PieceCoh_genFibre`), the second is the induction hypothesis for `A'`, and
  the overlap is `⋃ S ∈ A'.image (S₀ ∪ ·), finInter U S` — again the induction hypothesis, one
  degree down — so the two-piece union step
  `Work.Cohomology.subsingleton_pdCohSub_union_clean` finishes.  The set algebra needed
  (`finInter_union`, `isOpen_finInter`, `iUnion_finInter_empty`, `isOpen_iUnion_finInter`,
  `iUnion_finInter_insert`) is also in that file and only needs `Work.Thom.finInter`/`mem_finInter`
  plus `S.finite_toSet.isOpen_biInter`.  Note that `PieceCoh Z W n` is definitionally
  `Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' W) n`.

The degree bookkeeping is `e < finrank ℝ F` for `e + 1 = m` from `m < finrank ℝ F`, and
`Module.finrank ℝ F` is the rank of the fibre of `Z`. -/
theorem subsingleton_PieceCoh_iUnion_finInter_clean
    {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (N : ℕ) (U : Fin N → Set B) (hU : ∀ k, IsOpen (U k)) (cc : Fin N → ι)
    (hc : ∀ k, U k ⊆ Z.baseSet (cc k))
    (A : Finset (Finset (Fin N))) (hA : ∀ S ∈ A, S.Nonempty)
    {m : ℕ} (hm : m < Module.finrank ℝ F) :
    Subsingleton (Work.Thom.PieceCoh Z (⋃ S ∈ A, Work.Thom.finInter U S) m) := by
  classical
  have key : ∀ n : ℕ, ∀ A : Finset (Finset (Fin N)), A.card = n →
      (∀ S ∈ A, S.Nonempty) → ∀ m : ℕ, m < Module.finrank ℝ F →
        Subsingleton (PieceCoh Z (⋃ S ∈ A, finInter U S) m) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A hcard hAne m hm
    by_cases hA0 : A = ∅
    · rw [hA0, iUnion_finInter_empty]
      exact subsingleton_PieceCoh_of_isEmpty Z m ⟨fun x => x.2⟩
    · obtain ⟨S₀, hS₀mem⟩ := Finset.nonempty_iff_ne_empty.mpr hA0
      set A' : Finset (Finset (Fin N)) := A.erase S₀ with hA'def
      have hcard' : A'.card < n := by
        rw [hA'def, ← hcard]
        exact Finset.card_erase_lt_of_mem hS₀mem
      have hA'ne : ∀ S ∈ A', S.Nonempty := fun S hS => hAne S (Finset.mem_of_mem_erase hS)
      have hinsA : A = insert S₀ A' := by
        rw [hA'def]; exact (Finset.insert_erase hS₀mem).symm
      have hUnion : (⋃ S ∈ A, finInter U S)
          = finInter U S₀ ∪ (⋃ S ∈ A', finInter U S) := by
        rw [hinsA, iUnion_finInter_insert]
      set A'' : Finset (Finset (Fin N)) := A'.image (fun S => S₀ ∪ S) with hA''def
      have hInter : finInter U S₀ ∩ (⋃ S ∈ A', finInter U S)
          = ⋃ S ∈ A'', finInter U S := by
        rw [hA''def]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_image]
        constructor
        · rintro ⟨hx, i, hA'i, hxi⟩
          exact ⟨S₀ ∪ i, ⟨i, hA'i, rfl⟩, by rw [finInter_union]; exact ⟨hx, hxi⟩⟩
        · rintro ⟨i, ⟨a, ha, rfl⟩, hxi⟩
          rw [finInter_union] at hxi
          exact ⟨hxi.1, a, ha, hxi.2⟩
      have hA''card : A''.card < n := by
        have h1 : A''.card ≤ A'.card := by
          rw [hA''def]; exact Finset.card_image_le
        exact lt_of_le_of_lt h1 hcard'
      have hA''ne : ∀ S ∈ A'', S.Nonempty := by
        intro S hS
        rw [hA''def, Finset.mem_image] at hS
        obtain ⟨T, hT, hTS⟩ := hS
        rw [← hTS]
        exact Finset.Nonempty.mono Finset.subset_union_right (hA'ne T hT)
      have hS₀ne : S₀.Nonempty := hAne S₀ hS₀mem
      have hU' : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
          (zeroComplement Z) (Z.proj ⁻¹' finInter U S₀) m) := by
        haveI : Inhabited ι := ⟨cc hS₀ne.choose⟩
        have hsub : finInter U S₀ ⊆ Z.baseSet (cc hS₀ne.choose) := by
          have h1 : finInter U S₀ ⊆ finInter U {hS₀ne.choose} :=
            finInter_mono (Finset.singleton_subset_iff.mpr hS₀ne.choose_spec)
          rw [finInter_singleton] at h1
          exact h1.trans (hc hS₀ne.choose)
        exact subsingleton_PieceCoh_genFibre Z (cc hS₀ne.choose) hsub hm
      have hV' : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
          (zeroComplement Z) (Z.proj ⁻¹' (⋃ S ∈ A', finInter U S)) m) :=
        ih A'.card hcard' A' rfl hA'ne m hm
      have hUV : ∀ e, e + 1 = m → Subsingleton (Work.Cohomology.pdCohSub
          (TopCat.of Z.TotalSpace) (zeroComplement Z) ((Z.proj ⁻¹' finInter U S₀)
            ∩ (Z.proj ⁻¹' (⋃ S ∈ A', finInter U S))) e) := by
        intro e he
        have he' : e < Module.finrank ℝ F := by omega
        have hih := ih A''.card hA''card A'' rfl hA''ne e he'
        rw [← Set.preimage_inter, hInter]
        exact hih
      have hWopen : IsOpen (Z.proj ⁻¹' (⋃ S ∈ A, finInter U S)) :=
        (isOpen_iUnion_finInter hU A).preimage Z.continuous_proj
      have hUopen : IsOpen (Z.proj ⁻¹' finInter U S₀) :=
        (isOpen_finInter hU S₀).preimage Z.continuous_proj
      have hVopen : IsOpen (Z.proj ⁻¹' (⋃ S ∈ A', finInter U S)) :=
        (isOpen_iUnion_finInter hU A').preimage Z.continuous_proj
      have hUW : Z.proj ⁻¹' finInter U S₀ ⊆ Z.proj ⁻¹' (⋃ S ∈ A, finInter U S) :=
        Set.preimage_mono (by rw [hUnion]; exact Set.subset_union_left)
      have hVW : Z.proj ⁻¹' (⋃ S ∈ A', finInter U S) ⊆ Z.proj ⁻¹' (⋃ S ∈ A, finInter U S) :=
        Set.preimage_mono (by rw [hUnion]; exact Set.subset_union_right)
      have hcov : Z.proj ⁻¹' finInter U S₀ ∪ Z.proj ⁻¹' (⋃ S ∈ A', finInter U S)
          = Z.proj ⁻¹' (⋃ S ∈ A, finInter U S) := by
        rw [← Set.preimage_union, ← hUnion]
      exact Work.Cohomology.subsingleton_pdCohSub_union_clean (zeroComplement Z)
        (W := Z.proj ⁻¹' (⋃ S ∈ A, finInter U S))
        (U := Z.proj ⁻¹' finInter U S₀)
        (V := Z.proj ⁻¹' (⋃ S ∈ A', finInter U S))
        hWopen hUopen hVopen hUW hVW hcov m hU' hV' hUV
  exact key A.card A rfl hA m hm

end Work.Thom
