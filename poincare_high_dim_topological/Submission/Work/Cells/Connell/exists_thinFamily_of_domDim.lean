import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.Cells.Connell.Defs

/-!
# `exists_thinFamily_of_domDim`

A `d`-dimensional (`d + 1 ≤ n`) subset of a closed cube of size `β < 1` in `ℝⁿ` is covered by
finitely many *thin* sets, i.e. compact subsets of the open unit cube with empty interior.

This is the form in which the dimension hypothesis of Newman's engulfing theorem is consumed:
the `DomDim` cover exhibits `L` as a finite union of simplices with at most `d + 1 ≤ n` vertices,
and each such simplex has empty interior in `ℝⁿ` (it spans a proper affine subspace).
-/

open Set Metric

namespace Work.Cells.Connell

/-! ## Elementary facts about the sup-norm cubes -/

/-- The closed sup-norm cube is closed. -/
theorem isClosed_closedCube {n : ℕ} (r : ℝ) : IsClosed (PL.closedCube (n := n) r) := by
  have h : PL.closedCube (n := n) r = ⋂ i, {x : PL.E n | |x i| ≤ r} := by
    ext x; simp [PL.closedCube]
  rw [h]
  exact isClosed_iInter fun i =>
    isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).abs continuous_const

/-- A closed cube of size `< 1` sits in the open unit cube. -/
theorem closedCube_subset_openCube_lt_one {n : ℕ} {β : ℝ} (hβ : β < 1) :
    PL.closedCube (n := n) β ⊆ PL.openCube 1 := by
  intro x hx
  simp only [PL.closedCube, PL.openCube, Set.mem_ofPred_eq] at hx ⊢
  exact fun i => lt_of_le_of_lt (hx i) hβ

/-! ## A simplex with at most `n` vertices has empty interior -/

/-- A simplex spanned by at most `n` vertices of `ℝⁿ` has empty interior (it is contained in the
proper affine subspace it spans). -/
theorem interior_simp_eq_empty_of_card_le {n : ℕ} (s : Finset (PL.E n)) (h : s.card ≤ n) :
    interior (PL.simp s) = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  intro hne
  have hne' : (interior (convexHull ℝ ((s : Set (PL.E n))))).Nonempty := by
    rcases hne with ⟨x, hx⟩
    exact ⟨x, by simpa [PL.simp] using hx⟩
  have htop : affineSpan ℝ ((s : Set (PL.E n))) = ⊤ :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mp hne'
  have hfin : ((s : Set (PL.E n))).encard ≤ (Module.finrank ℝ (PL.E n) : ℕ∞) := by
    rw [Set.encard_coe_eq_coe_finsetCard, finrank_euclideanSpace, Fintype.card_fin]
    exact ENat.natCast_le_natCast.mpr h
  have hne_top := affineSpan_image_ne_top_of_encard_le_finrank ℝ (s := (s : Set (PL.E n)))
    s.finite_toSet hfin (id : PL.E n → PL.E n)
  rw [Set.image_id] at hne_top
  exact hne_top htop

/-! ## The main statement -/

theorem exists_thinFamily_of_domDim {n : ℕ} {L : Set (PL.E n)} {d : ℤ} (h : PL.DomDim L d)
    {β : ℝ} (hLβ : L ⊆ PL.closedCube β) (hβ : β < 1) (hd : d + 1 ≤ (n : ℤ)) :
    ∃ (ι : Type) (_ : Finite ι) (F : ι → Set (PL.E n)),
      ThinFamily F ∧ L ⊆ ⋃ i, F i := by
  obtain ⟨S, hScard, hLS⟩ := h
  refine ⟨↥S, inferInstance, fun s => closure (L ∩ PL.simp s.1), ?_, ?_⟩
  · intro s
    have hcard : s.1.card ≤ n := by
      have := hScard s.1 s.2
      omega
    have hcl : IsClosed (PL.simp s.1) := (PL.isCompact_simp s.1).isClosed
    have hsub : closure (L ∩ PL.simp s.1) ⊆ PL.simp s.1 :=
      closure_minimal Set.inter_subset_right hcl
    refine ⟨?_, ?_, ?_⟩
    · exact IsCompact.of_isClosed_subset (PL.isCompact_simp s.1) isClosed_closure hsub
    · calc closure (L ∩ PL.simp s.1) ⊆ closure (PL.closedCube β) :=
            closure_mono (Set.inter_subset_left.trans hLβ)
        _ = PL.closedCube β := (isClosed_closedCube β).closure_eq
        _ ⊆ PL.openCube 1 := closedCube_subset_openCube_lt_one hβ
    · have hle := interior_mono hsub
      rw [interior_simp_eq_empty_of_card_le s.1 hcard] at hle
      rw [Set.subset_empty_iff] at hle
      exact hle
  · intro x hx
    have hx' : x ∈ ⋃ s ∈ S, PL.simp s := hLS hx
    rw [PL.mem_iUnion_simp] at hx'
    obtain ⟨s, hsS, hxs⟩ := hx'
    exact Set.mem_iUnion.2 ⟨⟨s, hsS⟩, subset_closure ⟨hx, hxs⟩⟩

end Work.Cells.Connell
