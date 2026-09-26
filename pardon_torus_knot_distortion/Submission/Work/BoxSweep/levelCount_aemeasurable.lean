import Mathlib
import Submission.Work.Sweep.LevelCount
import Submission.Work.Sweep.MonotoneDecomp.exists_monotone_decomposition
import Submission.Work.Sweep.LevelCountTsum.levelCount_iUnion_eq_tsum

/-!
# Almost-everywhere measurability of the level count

For a `C¹` function `f` on an interval `[a, b]` (with continuous derivative `f'`)
and a measurable subset `S ⊆ [a, b]`, the level-counting function

  `y ↦ Work.Sweep.levelCount f S y = #(S ∩ f ⁻¹' {y})`

is almost everywhere measurable (for Lebesgue measure on the level `y`).

The proof decomposes `[a, b]` into the critical set `C` of `f` and a countable
pairwise disjoint family `D n` on each member of which `f` is strictly monotone.
On each `D n ∩ S` the function `f` is injective, so its level count is the
indicator function of the measurable image `f '' (D n ∩ S)`; the countable sum of
those indicators gives a *measurable* surrogate `G`.  The remaining part of `S`,
inside the critical set `C`, can only contribute at levels lying in `f '' C`,
which is a null set by Sard's theorem in one variable.  Hence `levelCount f S`
agrees with the measurable function `G` almost everywhere.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Work.BoxSweep

theorem levelCount_aemeasurable {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {S : Set ℝ}
    (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc a b)
    (hf' : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t) (hcont : ContinuousOn f' (Set.Icc a b)) :
    AEMeasurable (Work.Sweep.levelCount f S) := by
  classical
  obtain ⟨C, D, hCcomp, hCsub, hCcrit, hCshape, hDmeas, hDdisj, hDsub, hCdisj, hCcov, hDne,
    hDmono⟩ :=
    Work.Sweep.MonotoneDecomp.exists_monotone_decomposition f f' a b hab
      (fun t ht => (hf' t ht).hasDerivWithinAt) hcont
  -- Sard's theorem in one variable: the image of the critical set is null.
  have hcritnull : volume (f '' {t ∈ Set.Icc a b | f' t = 0}) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
      (f' := fun x => ContinuousLinearMap.toSpanSingleton ℝ (f' x)) ?_ ?_
    · intro x hx
      exact (hf' x hx.1).hasDerivWithinAt.mono (by intro y hy; exact hy.1)
    · intro x hx
      rw [hx.2]
      simp
  have hCnull : volume (f '' C) = 0 := by
    have hsub : f '' C ⊆ f '' {t ∈ Set.Icc a b | f' t = 0} ∪ ({f a, f b} : Set ℝ) := by
      rintro y ⟨x, hx, rfl⟩
      rcases hCshape hx with h | h
      · exact Or.inl ⟨x, ⟨hCsub hx, h⟩, rfl⟩
      · rcases h with h | h <;> subst h <;> exact Or.inr (by simp)
    exact measure_mono_null hsub
      (measure_union_null hcritnull ((Set.toFinite _).measure_zero volume))
  -- the pieces of `S` on which `f` is strictly monotone
  set E : ℕ → Set ℝ := fun n => D n ∩ S with hEdef
  have hEmeas : ∀ n, MeasurableSet (E n) := fun n => (hDmeas n).inter hS
  have hEdisj : Pairwise (Function.onFun Disjoint E) := fun m n hmn =>
    (hDdisj hmn).mono inter_subset_left inter_subset_left
  have hEunion : C ∩ S ∪ ⋃ n, E n = S := by
    have h1 : C ∩ S ∪ ⋃ n, E n = (C ∪ ⋃ n, D n) ∩ S := by
      rw [hEdef]
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion]
      constructor
      · rintro (⟨hx, hxS⟩ | ⟨n, hx, hxS⟩)
        · exact ⟨Or.inl hx, hxS⟩
        · exact ⟨Or.inr ⟨n, hx⟩, hxS⟩
      · rintro ⟨h | ⟨n, hn⟩, hxS⟩
        · exact Or.inl ⟨h, hxS⟩
        · exact Or.inr ⟨n, hn, hxS⟩
    rw [h1, hCcov, Set.inter_eq_right.mpr hSsub]
  have hEdisjC : Disjoint (C ∩ S) (⋃ n, E n) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxC, -⟩ hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact Set.disjoint_left.mp hCdisj hxC (Set.mem_iUnion_of_mem n hn.1)
  -- measurability of the level count on a single monotone piece
  have hEnmeas : ∀ n, Measurable (fun y => Work.Sweep.levelCount f (E n) y) := by
    intro n
    have hinj : InjOn f (E n) :=
      (hDmono n).elim (fun h => h.injOn.mono inter_subset_left)
        (fun h => h.injOn.mono inter_subset_left)
    rw [Work.Sweep.levelCount_eq_indicator_of_injOn hinj]
    have himg : MeasurableSet (f '' E n) := by
      rcases hDmono n with hmono | hanti
      · exact MeasurableSet.image_of_monotoneOn (hEmeas n)
          (hmono.monotoneOn.mono inter_subset_left)
      · exact MeasurableSet.image_of_antitoneOn (hEmeas n)
          (hanti.antitoneOn.mono inter_subset_left)
    exact measurable_const.indicator himg
  -- the measurable surrogate
  set G : ℝ → ℝ≥0∞ := fun y => ∑' n, Work.Sweep.levelCount f (E n) y with hG
  have hGmeas : Measurable G := by
    rw [hG]
    exact Measurable.tsum hEnmeas
  -- pointwise decomposition of the level count
  have hN : ∀ y, Work.Sweep.levelCount f S y = Work.Sweep.levelCount f (C ∩ S) y + G y := by
    intro y
    rw [hG]
    conv_lhs => rw [← hEunion]
    rw [Work.Sweep.levelCount_union hEdisjC y,
      Work.Sweep.LevelCountTsum.levelCount_iUnion_eq_tsum f E hEdisj y]
  -- the critical part vanishes at every level outside the null set `f '' C`
  have hCzero : ∀ y, y ∉ f '' C → Work.Sweep.levelCount f (C ∩ S) y = 0 := by
    intro y hy
    rw [Work.Sweep.levelCount_eq_zero_iff, Set.disjoint_left]
    rintro x ⟨hxC, -⟩ hxy
    exact hy ⟨x, hxC, hxy⟩
  have hsub : {y : ℝ | ¬ Work.Sweep.levelCount f S y = G y} ⊆ f '' C := by
    intro y hy
    by_contra hcon
    exact hy (by rw [hN y, hCzero y hcon, zero_add])
  have hae : (fun y => Work.Sweep.levelCount f S y) =ᵐ[volume] G := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    exact measure_mono_null hsub hCnull
  exact hGmeas.aemeasurable.congr hae.symm

end Work.BoxSweep
