import Mathlib
import Submission.Work.EKLComp.C8Defs

namespace Work.EKLCompSetup

/-- **Step 6** (EKL §4.4, first paragraph): a compact set `K ⊆ X₃` of positive measure such that
`K` has non-exceptional `α'_{01}(s)`-returns arbitrarily close to the identity, the displacement
never lying in the centraliser `L_{01}` of `U_{01}`.

`NonExceptional μ h01 2` supplies a null set `N` and the return property for every compact set
disjoint from `N`; `X₃` is compact with `μ(X₃) > 0` and, being Polish, `μ` is inner regular, so a
compact subset of `X₃` avoiding a measurable null cover of `N` still has positive measure. -/
theorem exists_return
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    [PolishSpace Work.EKLContract.X3]
    (D : Work.EKLComp.C8Setup μ)
    (hNE : Work.EKLContract.NonExceptional μ Work.EKLComp.h01 2) :
    ∃ K : Set Work.EKLContract.X3, IsCompact K ∧ K ⊆ D.X₃ ∧ 0 < μ K ∧
      ∀ δ : ℝ, 0 < δ → ∃ z ∈ K, ∃ s : ℝ, ∃ g ∈ (Work.EKLContract.V δ : Set Work.EKLContract.SL3),
        Work.EKLContract.aPrime 2 s • z ∈ K ∧ Work.EKLContract.aPrime 2 s • z = g • z ∧
        g ∉ Work.EKLContract.Lset Work.EKLComp.h01 := by
  obtain ⟨N₀, hN₀null, hret⟩ := hNE
  -- `μ X₃ > 0`: from the measure estimate `1 - (C+2)ε < μ X₃` of the setup.
  have hne0 : μ D.X₃ ≠ 0 := by
    intro h0
    have hreal : (μ D.X₃).toReal = 0 := by rw [h0]; simp
    have h1 := D.X₃_meas
    rw [hreal] at h1
    have h2 := D.ε_small_C
    linarith
  have hfin : μ D.X₃ ≤ 1 := by
    have h := MeasureTheory.measure_mono (μ := μ) (Set.subset_univ D.X₃)
    rwa [MeasureTheory.measure_univ] at h
  have hnetop : μ D.X₃ ≠ ⊤ := ne_top_of_le_ne_top (by simp) hfin
  -- a *measurable* null superset `B ⊇ N₀`
  set B : Set Work.EKLContract.X3 := MeasureTheory.toMeasurable μ N₀ with hBdef
  have hBN : N₀ ⊆ B := MeasureTheory.subset_toMeasurable μ N₀
  have hBmeas : MeasurableSet B := MeasureTheory.measurableSet_toMeasurable μ N₀
  have hBnull : μ B = 0 := by
    show μ (MeasureTheory.toMeasurable μ N₀) = 0
    rw [MeasureTheory.measure_toMeasurable, hN₀null]
  -- the measurable set `X₃ \ B` has the same measure as `X₃`, hence positive
  have hAmeas : MeasurableSet (D.X₃ \ B) := D.X₃_compact.measurableSet.diff hBmeas
  have hAeq : μ (D.X₃ \ B) = μ D.X₃ := MeasureTheory.measure_sdiff_null hBnull
  have hAne : μ (D.X₃ \ B) ≠ ⊤ := by rw [hAeq]; exact hnetop
  have hhalf : μ D.X₃ / 2 < μ D.X₃ := ENNReal.half_lt_self hne0 hnetop
  have hr : μ D.X₃ / 2 < μ (D.X₃ \ B) := by rw [hAeq]; exact hhalf
  -- inner regularity: a compact subset of `X₃ \ B` of positive measure
  obtain ⟨K, hKA, hKcomp, hKgt⟩ := hAmeas.exists_lt_isCompact_of_ne_top hAne hr
  have hKdisj : Disjoint K N₀ := by
    refine Set.disjoint_left.mpr fun x hxK hxN => ?_
    exact (hKA hxK).2 (hBN hxN)
  have hKpos : 0 < μ K := lt_of_le_of_lt zero_le hKgt
  exact ⟨K, hKcomp, fun x hx => (hKA hx).1, hKpos,
    fun δ hδ => hret K hKcomp hKdisj hKpos δ hδ⟩

end Work.EKLCompSetup
