import Mathlib
import Submission.Work.Sweep.LevelCount
import Submission.Work.Sweep.Coarea

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Work.BoxSweep

/-- `levelCount` is additive over a finite disjoint union indexed by a finset. -/
lemma levelCount_iUnion_finset {β : Type*} [DecidableEq β] {f : ℝ → ℝ} (A : β → Set ℝ)
    (y : ℝ) : ∀ s : Finset β, (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) →
      Work.Sweep.levelCount f (⋃ i ∈ s, A i) y = ∑ i ∈ s, Work.Sweep.levelCount f (A i) y := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s has ih =>
      intro hdisj
      have hunion : (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
        constructor
        · rintro ⟨i, hi, hx⟩
          rcases hi with rfl | hi
          · exact Or.inl hx
          · exact Or.inr ⟨i, hi, hx⟩
        · rintro (hx | ⟨i, hi, hx⟩)
          · exact ⟨a, Or.inl rfl, hx⟩
          · exact ⟨i, Or.inr hi, hx⟩
      have hdisj' : Disjoint (A a) (⋃ i ∈ s, A i) := by
        rw [Set.disjoint_left]
        intro x hxa hx
        simp only [Set.mem_iUnion] at hx
        obtain ⟨i, hi, hxi⟩ := hx
        exact Set.disjoint_left.mp
          (hdisj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
            (fun hai => has (hai ▸ hi))) hxa hxi
      rw [hunion, Work.Sweep.levelCount_union hdisj' y,
        ih (fun i hi j hj hij =>
          hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij),
        Finset.sum_insert has]

/-- The level count of a `C¹` function on an interval, restricted to a measurable set,
is a.e. measurable (the Banach indicatrix of a `C¹` function on an interval). -/
lemma aemeasurable_levelCount {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {S : Set ℝ}
    (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc a b)
    (hf' : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t) (hcont : ContinuousOn f' (Set.Icc a b)) :
    AEMeasurable (Work.Sweep.levelCount f S) := by
  classical
  obtain ⟨C, D, hCcomp, hCsub, hCcrit, hCshape, hDmeas, hDdisj, hDsub, hCdisj, hCcov, hDne,
    hDmono⟩ :=
    Work.Sweep.MonotoneDecomp.exists_monotone_decomposition f f' a b hab
      (fun t ht => (hf' t ht).hasDerivWithinAt) hcont
  have hcritnull : volume (f '' {t ∈ Set.Icc a b | f' t = 0}) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
      (f' := fun x => ContinuousLinearMap.toSpanSingleton ℝ (f' x)) ?_ ?_
    · intro x hx
      exact (hf' x hx.1).hasDerivWithinAt.mono (by intro y hy; exact hy.1)
    · intro x hx
      rw [hx.2]; simp
  have hCnull : volume (f '' C) = 0 := by
    have hsub : f '' C ⊆ f '' {t ∈ Set.Icc a b | f' t = 0} ∪ ({f a, f b} : Set ℝ) := by
      rintro y ⟨x, hx, rfl⟩
      rcases hCshape hx with h | h
      · exact Or.inl ⟨x, ⟨hCsub hx, h⟩, rfl⟩
      · rcases h with h | h <;> subst h <;> exact Or.inr (by simp)
    exact measure_mono_null hsub
      (measure_union_null hcritnull ((Set.toFinite _).measure_zero volume))
  set A : Set ℝ := S ∩ C with hA
  set E : ℕ → Set ℝ := fun n => D n ∩ S with hE
  have hEmeas : ∀ n, MeasurableSet (E n) := fun n => (hDmeas n).inter hS
  have hEdisj : Pairwise (Function.onFun Disjoint E) := fun m n hmn =>
    (hDdisj hmn).mono Set.inter_subset_left Set.inter_subset_left
  have hEnmeas : ∀ n, AEMeasurable (Work.Sweep.levelCount f (E n)) := by
    intro n
    have hinj : InjOn f (E n) :=
      (hDmono n).elim (fun h => h.injOn.mono Set.inter_subset_left)
        (fun h => h.injOn.mono Set.inter_subset_left)
    have hm : Measurable (Work.Sweep.levelCount f (E n)) := by
      rw [Work.Sweep.levelCount_eq_indicator_of_injOn hinj]
      have himg : MeasurableSet (f '' E n) := by
        rcases hDmono n with hmono | hanti
        · exact MeasurableSet.image_of_monotoneOn (hEmeas n)
            (hmono.monotoneOn.mono Set.inter_subset_left)
        · exact MeasurableSet.image_of_antitoneOn (hEmeas n)
            (hanti.antitoneOn.mono Set.inter_subset_left)
      exact measurable_const.indicator himg
    exact hm.aemeasurable
  have hAUB : A ∪ ⋃ n, E n = S := by
    rw [hA, hE]
    have h1 : S ∩ C ∪ ⋃ n, D n ∩ S = (C ∪ ⋃ n, D n) ∩ S := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion]
      constructor
      · rintro (⟨hxS, hxC⟩ | ⟨n, hxD, hxS⟩)
        · exact ⟨Or.inl hxC, hxS⟩
        · exact ⟨Or.inr ⟨n, hxD⟩, hxS⟩
      · rintro ⟨hxC | ⟨n, hxD⟩, hxS⟩
        · exact Or.inl ⟨hxS, hxC⟩
        · exact Or.inr ⟨n, hxD, hxS⟩
    rw [h1, hCcov, Set.inter_eq_right.mpr hSsub]
  have hdisjA : Disjoint A (⋃ n, E n) := by
    rw [Set.disjoint_left]
    intro x hxA hx
    rw [hA] at hxA
    rw [hE] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨n, hxD, -⟩ := hx
    exact Set.disjoint_left.mp hCdisj hxA.2 (Set.mem_iUnion.mpr ⟨n, hxD⟩)
  have hAae : AEMeasurable (Work.Sweep.levelCount f A) := by
    have hae : (fun _ : ℝ => (0 : ℝ≥0∞)) =ᵐ[volume] Work.Sweep.levelCount f A := by
      have hnull : ∀ᵐ y ∂volume, y ∉ f '' C := by
        rw [MeasureTheory.ae_iff]
        have hset : {a : ℝ | ¬ a ∉ f '' C} = f '' C := by
          ext a; simp
        rw [hset]; exact hCnull
      filter_upwards [hnull] with y hy
      symm
      rw [Work.Sweep.levelCount_eq_zero_iff, Set.disjoint_left]
      rintro t htA hty
      exact hy ⟨t, htA.2, by simpa using hty⟩
    exact aemeasurable_const.congr hae
  have hBae : AEMeasurable (Work.Sweep.levelCount f (⋃ n, E n)) := by
    have hEq : Work.Sweep.levelCount f (⋃ n, E n) =
        fun y => ∑' n, Work.Sweep.levelCount f (E n) y := by
      funext y
      exact Work.Sweep.LevelCountTsum.levelCount_iUnion_eq_tsum f E hEdisj y
    rw [hEq]
    exact AEMeasurable.ennreal_tsum hEnmeas
  have hsplit : Work.Sweep.levelCount f S =
      fun y => Work.Sweep.levelCount f A y + Work.Sweep.levelCount f (⋃ n, E n) y := by
    funext y
    rw [← hAUB, Work.Sweep.levelCount_union hdisjA y]
  rw [hsplit]
  exact hAae.add hBae

theorem lintegral_levelCount_le_sum {ι : Type*} [Fintype ι] {g : ℝ → ℝ} {F : ι → ℝ → ℝ}
    {F' : ι → ℝ → ℝ} {S : ι → Set ℝ} {a b : ℝ} (hab : a ≤ b)
    (hS : ∀ k, MeasurableSet (S k)) (hSsub : ∀ k, S k ⊆ Set.Icc a b)
    (hdisj : Pairwise (Function.onFun Disjoint S))
    (hf' : ∀ k, ∀ t ∈ Set.Icc a b, HasDerivAt (F k) (F' k t) t)
    (hcont : ∀ k, ContinuousOn (F' k) (Set.Icc a b))
    (heq : ∀ k, ∀ t ∈ S k, F k t = g t)
    (hcov : ∀ t ∈ Set.Icc a b, g t ≠ 0 → ∃ k, t ∈ S k)
    {w : ℝ → ENNReal} (hw : AEMeasurable w) (hw0 : w 0 = 0) :
    ∫⁻ y, w y * Work.Sweep.levelCount g (Set.Icc a b) y
      ≤ ∑ k, ∫⁻ t in S k, ENNReal.ofReal |F' k t| * w (F k t) := by
  classical
  set T : Set ℝ := ⋃ k, S k with hT
  have hleveleq : ∀ y, y ≠ 0 → Work.Sweep.levelCount g (Set.Icc a b) y =
      Work.Sweep.levelCount g T y := by
    intro y hy
    have hset : Set.Icc a b ∩ g ⁻¹' {y} = T ∩ g ⁻¹' {y} := by
      ext t
      constructor
      · rintro ⟨htIcc, hgt⟩
        have hgt' : g t = y := by simpa using hgt
        obtain ⟨k, hk⟩ := hcov t htIcc (by rw [hgt']; exact hy)
        refine ⟨?_, hgt⟩
        rw [hT]
        exact Set.mem_iUnion.mpr ⟨k, hk⟩
      · rintro ⟨htT, hgt⟩
        rw [hT] at htT
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp htT
        exact ⟨hSsub k hk, hgt⟩
    rw [Work.Sweep.levelCount, Work.Sweep.levelCount, hset]
  have hTsum : ∀ y, Work.Sweep.levelCount g T y = ∑ k, Work.Sweep.levelCount (F k) (S k) y := by
    intro y
    have hT_eq : (⋃ i ∈ (Finset.univ : Finset ι), S i) = T := by
      rw [hT]; ext x; simp
    rw [← hT_eq, levelCount_iUnion_finset S y Finset.univ
      (fun i _ j _ hij => hdisj hij)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hset : S k ∩ g ⁻¹' {y} = S k ∩ (F k) ⁻¹' {y} := by
      ext t
      constructor
      · rintro ⟨ht, hgt⟩
        refine ⟨ht, ?_⟩
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hgt ⊢
        rw [heq k t ht]; exact hgt
      · rintro ⟨ht, hft⟩
        refine ⟨ht, ?_⟩
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hft ⊢
        rw [← heq k t ht]; exact hft
    rw [Work.Sweep.levelCount, Work.Sweep.levelCount, hset]
  have hw_eq : ∀ y, w y * Work.Sweep.levelCount g (Set.Icc a b) y =
      w y * Work.Sweep.levelCount g T y := by
    intro y
    by_cases hy : w y = 0
    · simp [hy]
    · rw [hleveleq y (fun h => hy (by rw [h, hw0]))]
  have hmeas : ∀ k, AEMeasurable (Work.Sweep.levelCount (F k) (S k)) :=
    fun k => aemeasurable_levelCount hab (hS k) (hSsub k) (hf' k) (hcont k)
  calc ∫⁻ y, w y * Work.Sweep.levelCount g (Set.Icc a b) y
      = ∫⁻ y, w y * Work.Sweep.levelCount g T y := lintegral_congr hw_eq
    _ = ∫⁻ y, w y * (∑ k, Work.Sweep.levelCount (F k) (S k) y) := by
        refine lintegral_congr fun y => ?_
        rw [hTsum y]
    _ = ∫⁻ y, ∑ k, w y * Work.Sweep.levelCount (F k) (S k) y := by
        refine lintegral_congr fun y => ?_
        rw [Finset.mul_sum]
    _ = ∑ k, ∫⁻ y, w y * Work.Sweep.levelCount (F k) (S k) y := by
        rw [lintegral_finsetSum']
        intro k _
        exact hw.mul (hmeas k)
    _ ≤ ∑ k, ∫⁻ t in S k, ENNReal.ofReal |F' k t| * w (F k t) := by
        refine Finset.sum_le_sum ?_
        intro k _
        exact Work.Sweep.lintegral_mul_levelCount_le_subset hab (hS k) (hSsub k) hw (hf' k)
          (hcont k)

end Work.BoxSweep
