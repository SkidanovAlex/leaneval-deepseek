import Mathlib
import ChallengeDeps
import Submission.Work.Sweep.LevelCount
import Submission.Work.Sweep.MonotoneDecomp.exists_monotone_decomposition
import Submission.Work.Sweep.CoareaMono.lintegral_levelCount_eq_of_strictMonoOn
import Submission.Work.Sweep.CoareaAnti.lintegral_levelCount_eq_of_strictAntiOn
import Submission.Work.Sweep.LevelCountTsum.levelCount_iUnion_eq_tsum

/-!
# The one-dimensional coarea inequality

The main result of this file is `lintegral_mul_levelCount_le_subset`: for a `C¹`
function `f` on an interval `[a, b]`, a measurable subset `S ⊆ [a, b]` and any
weight `w : ℝ → ℝ≥0∞`,

  `∫⁻ y, w y * #{t ∈ S : f t = y} ≤ ∫⁻ t in S, |f' t| * w (f t)`.

This is the coarea (or "area") formula in dimension one, in weighted form, which
is the version needed for the sweep: taking `w` to be the indicator of a range of
levels produces exactly the statement that the integral over the levels of the
number of intersections is bounded by the arclength of the part of the curve
lying between those levels.

The proof decomposes `[a, b]` into the critical set of `f` (whose image is a null
set, by Sard's theorem for one-variable functions, formalised in Mathlib as
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) and countably
many measurable pieces on which `f` is strictly monotone; on each piece the coarea
identity is the change of variables formula for a monotone function
(`Submission.Work.Sweep.CoareaMono`, `...CoareaAnti`), and the counts add up by
`Submission.Work.Sweep.LevelCountTsum`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Work.Sweep

/-- **One-dimensional coarea inequality (weighted form, restricted domain).**

If `f` is differentiable on `[a,b]` with derivative `f'`, `f'` is continuous on
`[a,b]`, and `S ⊆ [a,b]` is measurable, then for any weight `w : ℝ → ℝ≥0∞` the
integral over the levels `y` of `w y` times the number of parameters in `S`
mapping to `y` is at most the integral over `S` of `|f'|` weighted by `w ∘ f`. -/
theorem lintegral_mul_levelCount_le_subset {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {S : Set ℝ}
    (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc a b) {w : ℝ → ENNReal} (hw : AEMeasurable w)
    (hf' : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t) (hcont : ContinuousOn f' (Set.Icc a b)) :
    ∫⁻ y, w y * levelCount f S y ≤ ∫⁻ t in S, ENNReal.ofReal |f' t| * w (f t) := by
  classical
  obtain ⟨C, D, hCcomp, hCsub, hCcrit, hCshape, hDmeas, hDdisj, hDsub, hCdisj, hCcov, hDne,
    hDmono⟩ :=
    MonotoneDecomp.exists_monotone_decomposition f f' a b hab
      (fun t ht => (hf' t ht).hasDerivWithinAt) hcont
  -- Sard: the image of the critical set is null.
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
  have hfcont : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hCimg : MeasurableSet (f '' C) :=
    (hCcomp.image_of_continuousOn (hfcont.mono hCsub)).isClosed.measurableSet
  -- the majorant for the critical part
  set M : ℝ → ENNReal := (f '' C).indicator (fun _ => ⊤) with hMdef
  have hMmeas : Measurable M := measurable_const.indicator hCimg
  have hMle : ∫⁻ y, w y * M y ≤ 0 := by
    have hle : (fun y => w y * M y) ≤ M := fun y => by
      show w y * ((f '' C).indicator (fun _ => (⊤ : ENNReal)) y) ≤
        (f '' C).indicator (fun _ => (⊤ : ENNReal)) y
      by_cases hy : y ∈ f '' C <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
    calc ∫⁻ y, w y * M y ≤ ∫⁻ y, M y := lintegral_mono hle
      _ = 0 := by rw [hMdef, lintegral_indicator_const hCimg ⊤, hCnull, mul_zero]
  have hMexact : ∫⁻ y, w y * M y = 0 := le_antisymm hMle bot_le
  -- the pieces of the restriction of `f` to `S`
  set E : ℕ → Set ℝ := fun n => D n ∩ S with hEdef
  have hEmeas : ∀ n, MeasurableSet (E n) := fun n => (hDmeas n).inter hS
  have hEdisj : Pairwise (Function.onFun Disjoint E) := fun m n hmn =>
    (hDdisj hmn).mono (inter_subset_left) (inter_subset_left)
  have hEsub : ∀ n, E n ⊆ Set.Icc a b := fun n => (inter_subset_left).trans (hDsub n)
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
  -- measurability of the level counts of the pieces
  have hEnmeas : ∀ n, Measurable (fun y => levelCount f (E n) y) := by
    intro n
    have hinj : InjOn f (E n) :=
      (hDmono n).elim (fun h => h.injOn.mono inter_subset_left)
        (fun h => h.injOn.mono inter_subset_left)
    rw [levelCount_eq_indicator_of_injOn hinj]
    have himg : MeasurableSet (f '' E n) := by
      rcases hDmono n with hmono | hanti
      · exact MeasurableSet.image_of_monotoneOn (hEmeas n) (hmono.monotoneOn.mono inter_subset_left)
      · exact MeasurableSet.image_of_antitoneOn (hEmeas n) (hanti.antitoneOn.mono inter_subset_left)
    exact measurable_const.indicator himg
  -- the pointwise decomposition of the level count over `S`
  have hN : ∀ y, levelCount f S y = levelCount f (C ∩ S) y + levelCount f (⋃ n, E n) y := by
    intro y
    conv_lhs => rw [← hEunion]
    rw [levelCount_union hEdisjC y]
  have hle_C : ∀ y, levelCount f (C ∩ S) y ≤ M y := by
    intro y
    show levelCount f (C ∩ S) y ≤ (f '' C).indicator (fun _ => (⊤ : ENNReal)) y
    by_cases hy : y ∈ f '' C
    · rw [Set.indicator_of_mem hy]; exact le_top
    · have hz : levelCount f (C ∩ S) y = 0 := by
        rw [levelCount_eq_zero_iff, Set.disjoint_left]
        rintro x ⟨hxC, -⟩ hxy
        exact hy ⟨x, hxC, hxy⟩
      rw [Set.indicator_of_notMem hy, hz]
  -- the per-piece coarea identity
  have hterm : ∀ n, ∫⁻ y, w y * levelCount f (E n) y ≤
      ∫⁻ x in E n, ENNReal.ofReal |f' x| * w (f x) := by
    intro n
    rcases hDmono n with hmono | hanti
    · rw [CoareaMono.lintegral_levelCount_eq_of_strictMonoOn (hEmeas n)
        (hmono.mono inter_subset_left) (fun x hx => hf' x (hEsub n hx)) w]
      exact lintegral_mono fun x => by
        gcongr
        exact le_abs_self _
    · rw [CoareaAnti.lintegral_levelCount_eq_of_strictAntiOn (hEmeas n)
        (hanti.mono inter_subset_left) (fun x hx => hf' x (hEsub n hx)) w]
      exact lintegral_mono fun x => by
        gcongr
        exact neg_le_abs _
  calc ∫⁻ y, w y * levelCount f S y
      = ∫⁻ y, w y * (levelCount f (C ∩ S) y + levelCount f (⋃ n, E n) y) := by simp only [hN]
    _ ≤ ∫⁻ y, w y * (M y + levelCount f (⋃ n, E n) y) := by
        refine lintegral_mono fun y => ?_
        gcongr
        exact hle_C y
    _ = (∫⁻ y, w y * M y) + (∫⁻ y, w y * levelCount f (⋃ n, E n) y) := by
        have hsplit : (fun y => w y * (M y + levelCount f (⋃ n, E n) y)) =
            (fun y => w y * M y + w y * levelCount f (⋃ n, E n) y) := by
          funext y; rw [mul_add]
        rw [hsplit]
        exact lintegral_add_left' (f := fun y => w y * M y)
          (g := fun y => w y * levelCount f (⋃ n, E n) y) (hw.mul hMmeas.aemeasurable)
    _ = ∫⁻ y, w y * levelCount f (⋃ n, E n) y := by rw [hMexact, zero_add]
    _ = ∑' n, ∫⁻ y, w y * levelCount f (E n) y := by
        have hpt : ∀ y, w y * levelCount f (⋃ n, E n) y =
            ∑' n, w y * levelCount f (E n) y := by
          intro y
          rw [LevelCountTsum.levelCount_iUnion_eq_tsum f E hEdisj y, ENNReal.tsum_mul_left]
        simp only [hpt]
        exact lintegral_tsum (f := fun n y => w y * levelCount f (E n) y)
          (fun n => hw.mul (hEnmeas n).aemeasurable)
    _ ≤ ∑' n, ∫⁻ x in E n, ENNReal.ofReal |f' x| * w (f x) := ENNReal.tsum_le_tsum hterm
    _ = ∫⁻ x in ⋃ n, E n, ENNReal.ofReal |f' x| * w (f x) := by
        rw [lintegral_iUnion hEmeas hEdisj]
    _ ≤ ∫⁻ x in S, ENNReal.ofReal |f' x| * w (f x) := by
        refine lintegral_mono_set ?_
        intro x hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨n, hn⟩ := hx
        exact (inter_subset_right) hn

/-- **One-dimensional coarea inequality (weighted form).**

The special case of `lintegral_mul_levelCount_le_subset` in which the domain is
the whole interval `[a, b]`. -/
theorem lintegral_mul_levelCount_le (a b : ℝ) (hab : a ≤ b) (f f' : ℝ → ℝ) (w : ℝ → ENNReal)
    (hw : AEMeasurable w) (hf' : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hcont : ContinuousOn f' (Set.Icc a b)) :
    ∫⁻ y, w y * levelCount f (Set.Icc a b) y ≤
      ∫⁻ t in Set.Icc a b, ENNReal.ofReal |f' t| * w (f t) :=
  lintegral_mul_levelCount_le_subset hab measurableSet_Icc (Subset.refl _) hw hf' hcont

end Work.Sweep
