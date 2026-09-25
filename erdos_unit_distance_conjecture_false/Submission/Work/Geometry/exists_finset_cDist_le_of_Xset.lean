import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts
import Submission.Work.Geometry.two_mul_cDist

/-!
# Projecting a coset of the lattice to one complex coordinate

For a CM field `K` and a complex infinite place `w₀`, the mixed space `ℝ^{r₁} × ℂ^{r₂}` maps to
`ℂ` by taking the `w₀`-coordinate.  On the coset `Xset K I R a` this map is *injective*: if two
points of the coset have the same `w₀`-coordinate, their difference lies in the lattice `Φ(I)`,
hence is `mixedEmbedding α` for some `α ∈ I`, and its `w₀`-coordinate is `w₀.embedding α = 0`;
injectivity of the complex embedding forces `α = 0`.

Consequently the coset can be modelled faithfully by a finite set `P ⊆ ℂ` of the same cardinality.
Moreover, an element `u` with `u · conj u = 1` has `‖w.embedding u‖ = 1` at *every* infinite place,
so the image of a pair of coset points differing by `mixedEmbedding u` is a unit-distance pair of
`P`.  Counting ordered pairs gives

`(PairSet K I R U a).ncard ≤ 2 * cDist P`,

which is the content of the main theorem below.
-/

namespace Work.Geometry

set_option linter.unusedVariables false

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

/-- Projection of the mixed space onto the coordinate of a complex infinite place `w`. -/
noncomputable def placeProj (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K)
    (hw : w.IsComplex) : mixedEmbedding.mixedSpace K → ℂ :=
  fun x => x.2 ⟨w, hw⟩

theorem placeProj_sub (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K)
    (hw : w.IsComplex) (x y : mixedEmbedding.mixedSpace K) :
    placeProj K w hw (x - y) = placeProj K w hw x - placeProj K w hw y := rfl

theorem placeProj_mixedEmbedding (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K)
    (hw : w.IsComplex) (u : K) :
    placeProj K w hw (mixedEmbedding K u) = w.embedding u := by
  exact NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex K u ⟨w, hw⟩

/-- For a coset `Xset K I R a` of the lattice `Φ(I)`, the `w₀`-coordinate is injective. -/
theorem placeProj_injOn_Xset (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (a : mixedEmbedding.mixedSpace K)
    (w₀ : InfinitePlace K) (hw₀ : w₀.IsComplex) :
    Set.InjOn (placeProj K w₀ hw₀) (Xset K I R a) := by
  have hdiff : ∀ {x y : mixedEmbedding.mixedSpace K},
      x ∈ Xset K I R a → y ∈ Xset K I R a → x - y ∈ Lattice K I := by
    intro x y hx hy
    have h := sub_mem hx.1 hy.1
    rwa [show x - a - (y - a) = x - y by abel] at h
  intro x hx y hy hxy
  obtain ⟨α, _hαI, hα⟩ := (mem_lattice I).mp (hdiff hx hy)
  have h1 : placeProj K w₀ hw₀ x - placeProj K w₀ hw₀ y = w₀.embedding α := by
    rw [← placeProj_sub, ← hα, placeProj_mixedEmbedding]
  have h2 : w₀.embedding α = 0 := by rw [← h1, hxy, sub_self]
  have hα0 : α = 0 := by
    have hw : w₀ α = 0 := by rw [← InfinitePlace.norm_embedding_eq, h2, norm_zero]
    rw [InfinitePlace.coe_apply] at hw
    exact w₀.1.eq_zero.mp hw
  have hxy0 : x - y = 0 := by rw [← hα, hα0, map_zero]
  exact sub_eq_zero.mp hxy0

/-- **A coset of the lattice projects to a finite point set of `ℂ` of the same cardinality, and
the unit-distance pairs of that set dominate the ordered pairs of coset points whose difference is
`mixedEmbedding u` for some `u` with `u · conj u = 1`.** -/
theorem exists_finset_cDist_le_of_Xset (K : Type*) [Field K] [NumberField K] [IsCMField K]
    (w₀ : InfinitePlace K) (hw₀ : w₀.IsComplex)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (U : Finset K) (a : mixedEmbedding.mixedSpace K)
    (hU : ∀ u ∈ U, u ∈ (I : Set K))
    (hU1 : ∀ u ∈ U, u * IsCMField.complexConj K u = 1)
    (hfin : (Xset K I R a).Finite) :
    ∃ P : Finset ℂ, P.card = (Xset K I R a).ncard ∧
      (PairSet K I R U a).ncard ≤ 2 * Work.Defs.cDist P := by
  have hInj := placeProj_injOn_Xset K I R a w₀ hw₀
  -- `PairSet` is a subset of `Xset × Xset`, hence finite.
  have hPfin : (PairSet K I R U a).Finite :=
    (hfin.prod hfin).subset (fun p hp => Set.mem_prod.mpr ⟨hp.1, hp.2.1⟩)
  refine ⟨(hfin.toFinset).image (placeProj K w₀ hw₀), ?_, ?_⟩
  · have hInjF : Set.InjOn (placeProj K w₀ hw₀)
        (↑(hfin.toFinset) : Set (mixedEmbedding.mixedSpace K)) := by
      intro x hx y hy hxy
      exact hInj ((Set.Finite.mem_toFinset hfin).mp hx) ((Set.Finite.mem_toFinset hfin).mp hy) hxy
    rw [Finset.card_image_of_injOn hInjF]
    exact (Set.ncard_eq_toFinset_card _ hfin).symm
  · rw [two_mul_cDist]
    -- The pair map `p ↦ (π p.1, π p.2)` is injective on `PairSet`.
    have hInjP : Set.InjOn (fun p => (placeProj K w₀ hw₀ p.1, placeProj K w₀ hw₀ p.2))
        (↑(hPfin.toFinset) : Set (mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K)) := by
      intro p hp q hq hpq
      have hp' := (Set.Finite.mem_toFinset hPfin).mp hp
      have hq' := (Set.Finite.mem_toFinset hPfin).mp hq
      exact Prod.ext (hInj hp'.1 hq'.1 (congrArg Prod.fst hpq))
        (hInj hp'.2.1 hq'.2.1 (congrArg Prod.snd hpq))
    have himg : (hPfin.toFinset.image
        (fun p => (placeProj K w₀ hw₀ p.1, placeProj K w₀ hw₀ p.2))).card = hPfin.toFinset.card :=
      Finset.card_image_of_injOn hInjP
    have hncard : (PairSet K I R U a).ncard =
        (hPfin.toFinset.image (fun p => (placeProj K w₀ hw₀ p.1, placeProj K w₀ hw₀ p.2))).card :=
      (Set.ncard_eq_toFinset_card _ hPfin).trans himg.symm
    rw [hncard]
    -- The pair map lands in the ordered unit-distance pairs of `P`.
    apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hp' := (Set.Finite.mem_toFinset hPfin).mp hp
    obtain ⟨hp1, hp2, u, huU, hdiff_u⟩ := hp'
    have hπdiff : placeProj K w₀ hw₀ p.2 - placeProj K w₀ hw₀ p.1 = w₀.embedding u := by
      rw [← placeProj_sub, hdiff_u, placeProj_mixedEmbedding]
    have hnorm1 : ‖w₀.embedding u‖ = 1 :=
      norm_embedding_eq_one_of_mul_complexConj u (hU1 u huU) w₀
    rw [Finset.mem_filter, Finset.mem_offDiag]
    show ((placeProj K w₀ hw₀ p.1 ∈ (hfin.toFinset).image (placeProj K w₀ hw₀) ∧
          (placeProj K w₀ hw₀ p.2 ∈ (hfin.toFinset).image (placeProj K w₀ hw₀) ∧
            placeProj K w₀ hw₀ p.1 ≠ placeProj K w₀ hw₀ p.2))) ∧
          ‖placeProj K w₀ hw₀ p.1 - placeProj K w₀ hw₀ p.2‖ = 1
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨p.1, (Set.Finite.mem_toFinset hfin).mpr hp1, rfl⟩
    · exact Finset.mem_image.mpr ⟨p.2, (Set.Finite.mem_toFinset hfin).mpr hp2, rfl⟩
    · intro hcon
      have hz0 : w₀.embedding u = 0 := by rw [← hπdiff, hcon, sub_self]
      rw [hz0, norm_zero] at hnorm1
      exact zero_ne_one hnorm1
    · rw [norm_sub_rev, hπdiff]
      exact hnorm1

end Work.Geometry
