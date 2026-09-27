import Mathlib
import Submission.Work.Mostow.VolDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Function

noncomputable section

variable {n : ℕ}

/-- **Local injectivity.** A `C¹` map whose derivative at a point is invertible is injective on
some open neighbourhood of that point (inverse function theorem). -/
theorem localInjOn_of_det_ne_zero {F : E n → E n} (hF : ContDiff ℝ 1 F) (x : E n)
    (hx : (fderiv ℝ F x).det ≠ 0) : ∃ U : Set (E n), IsOpen U ∧ x ∈ U ∧ Set.InjOn F U := by
  have hstrict : HasStrictFDerivAt F (fderiv ℝ F x) x := hF.hasStrictFDerivAt (by norm_num)
  let f' : E n ≃L[ℝ] E n := (fderiv ℝ F x).toContinuousLinearEquivOfDetNeZero hx
  have hcoe : (f' : E n →L[ℝ] E n) = fderiv ℝ F x :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  have hstrict' : HasStrictFDerivAt F (f' : E n →L[ℝ] E n) x := by rwa [hcoe]
  let e := hstrict'.toOpenPartialHomeomorph F
  refine ⟨e.source, e.open_source, hstrict'.mem_toOpenPartialHomeomorph_source, ?_⟩
  have he : (e : E n → E n) = F := HasStrictFDerivAt.toOpenPartialHomeomorph_coe hstrict'
  intro a ha b hb hab
  exact e.injOn ha hb (by rw [he]; exact hab)

/-- **Countable disjoint injective cover.** For a `C¹` map `F : E n → E n`, the set where the
Jacobian does not vanish is covered by countably many measurable pairwise disjoint sets on which
`F` is injective. -/
theorem injOnCover_det_ne_zero {F : E n → E n} (hF : ContDiff ℝ 1 F) :
    ∃ S : ℕ → Set (E n), (∀ k, MeasurableSet (S k)) ∧ (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
      (∀ k, Set.InjOn F (S k)) ∧ {x : E n | (fderiv ℝ F x).det ≠ 0} ⊆ ⋃ k, S k := by
  classical
  let O : Set (E n) := {x : E n | (fderiv ℝ F x).det ≠ 0}
  have hchoice : ∀ y ∈ O, ∃ U : Set (E n), IsOpen U ∧ y ∈ U ∧ Set.InjOn F U :=
    fun y hy => localInjOn_of_det_ne_zero hF y hy
  let V : E n → Set (E n) := fun y => if hy : y ∈ O then Classical.choose (hchoice y hy) else ∅
  have hVopen : ∀ y, IsOpen (V y) := by
    intro y
    by_cases hy : y ∈ O
    · simp only [V, dif_pos hy]
      exact (Classical.choose_spec (hchoice y hy)).1
    · simp only [V, dif_neg hy]; exact isOpen_empty
  have hVinj : ∀ y, Set.InjOn F (V y) := by
    intro y
    by_cases hy : y ∈ O
    · simp only [V, dif_pos hy]
      exact (Classical.choose_spec (hchoice y hy)).2.2
    · simp only [V, dif_neg hy]; exact Set.injOn_empty F
  have hVcover : O ⊆ ⋃ y, V y := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    simp only [V, dif_pos hx]
    exact (Classical.choose_spec (hchoice x hx)).2.1
  obtain ⟨f, hf⟩ :=
    (HereditarilyLindelofSpace.isLindelof O).indexed_countable_subcover V hVopen hVcover
  refine ⟨fun k => disjointed (fun k => V (f k)) k,
    fun k => MeasurableSet.disjointed (fun k => (hVopen (f k)).measurableSet) k,
    fun i j hij => disjoint_disjointed _ hij,
    fun k => (hVinj (f k)).mono (disjointed_subset _ _),
    fun x hx => by rw [iUnion_disjointed]; exact hf hx⟩

/-- The elementary identity behind the weighted area formula:
`ofReal (hjac F u) * hdens u = hjacLeb F u`. -/
theorem hjac_mul_hdens (F : E n → E n) (u : E n) :
    ENNReal.ofReal (hjac F u) * hdens u = hjacLeb F u := by
  rw [hjac_eq, hjacLeb]; simp only [hdens]
  have hpu : (0:ℝ) < tpart u := tpart_pos u
  have hpf : (0:ℝ) < tpart (F u) := tpart_pos (F u)
  have hA : 0 ≤ |(fderiv ℝ F u).det| * (tpart u / tpart (F u)) :=
    mul_nonneg (abs_nonneg _) (div_nonneg (le_of_lt hpu) (le_of_lt hpf))
  have hreal : |(fderiv ℝ F u).det| * (tpart u / tpart (F u)) * (tpart u)⁻¹
      = |(fderiv ℝ F u).det| * (tpart (F u))⁻¹ := by field_simp
  conv_lhs => rw [← ENNReal.ofReal_mul hA]
  rw [hreal, ENNReal.ofReal_mul (abs_nonneg _)]

/-- Rewriting a `volH`-integral of `ofReal (hjac F ·)` as a Lebesgue integral of `hjacLeb F`. -/
theorem volH_lintegral_eq {F : E n → E n} (hF : ContDiff ℝ 1 F) {s : Set (E n)}
    (hs : MeasurableSet s) :
    ∫⁻ u in s, ENNReal.ofReal (hjac F u) ∂(volH n)
      = ∫⁻ u in s, hjacLeb F u ∂(volume : Measure (E n)) := by
  have hφ : Measurable (fun u : E n => ENNReal.ofReal (hjac F u)) :=
    ENNReal.measurable_ofReal.comp (hjacContinuous n hF).measurable
  rw [volH_def]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul (volume : Measure (E n)) measurable_hdens hφ hs]
  simp only [Pi.mul_apply]
  rw [show (fun u : E n => hdens u * ENNReal.ofReal (hjac F u)) = (fun u => hjacLeb F u) from
    funext (fun u => by rw [mul_comm, hjac_mul_hdens])]

/-- The change-of-variables formula in the exact shape needed: for a measurable set on which `F`
is injective, `volH (F '' s)` is the Lebesgue integral of `hjacLeb F` over `s`. -/
theorem volH_image_of_injOn {F : E n → E n} (hF : ContDiff ℝ 1 F) {s : Set (E n)}
    (hs : MeasurableSet s) (hinj : Set.InjOn F s) :
    volH n (F '' s) = ∫⁻ u in s, hjacLeb F u ∂(volume : Measure (E n)) := by
  have hdiff : ∀ x ∈ s, HasFDerivWithinAt F (fderiv ℝ F x) s x := fun x _ =>
    ((hF.differentiable (by norm_num) x).hasFDerivAt).hasFDerivWithinAt
  have hmeasimg : MeasurableSet (F '' s) := measurable_image_of_fderivWithin hs hdiff hinj
  rw [volHApply n hmeasimg]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := (volume : Measure (E n))) hs hdiff hinj
    (hdens)]
  rfl

/-- Sard's lemma in the form used here: the image of the critical set of a `C¹` map is contained
in a measurable `volH`-null set. -/
theorem criticalImage_null {F : E n → E n} (hF : ContDiff ℝ 1 F) {A : Set (E n)}
    (hA : MeasurableSet A) :
    ∃ N : Set (E n), MeasurableSet N ∧ F '' (A ∩ {x | (fderiv ℝ F x).det = 0}) ⊆ N ∧
      volH n N = 0 := by
  set C : Set (E n) := A ∩ {x | (fderiv ℝ F x).det = 0} with hC
  have hCdet : ∀ x ∈ C, (fderiv ℝ F x).det = 0 := fun x hx => hx.2
  have hfd : ∀ x ∈ C, HasFDerivWithinAt F (fderiv ℝ F x) C x := fun x _ =>
    ((hF.differentiable (by norm_num) x).hasFDerivAt).hasFDerivWithinAt
  have hnull : (volume : Measure (E n)) (F '' C) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := (volume : Measure (E n))) hfd hCdet
  refine ⟨toMeasurable (volume : Measure (E n)) (F '' C), measurableSet_toMeasurable _ _,
    subset_toMeasurable _ _, ?_⟩
  rw [volHNull, measure_toMeasurable]
  exact hnull

/-- Weighted area formula for hyperbolic volume. The set `B` produced is a measurable superset of
`F '' A` whose `volH`-measure is bounded by the integral of `hjac` over `A`; the plain inequality
`volH n (F '' A) ≤ ∫⁻ u in A, ofReal (hjac F u) ∂volH n` follows immediately. -/
theorem areaFormula (n : ℕ) {F : E n → E n} (hF : ContDiff ℝ 1 F) {A : Set (E n)}
    (hA : MeasurableSet A) :
    ∃ B : Set (E n), MeasurableSet B ∧ F '' A ⊆ B ∧
      volH n B ≤ ∫⁻ u in A, ENNReal.ofReal (hjac F u) ∂(volH n) := by
  classical
  let O : Set (E n) := {x : E n | (fderiv ℝ F x).det ≠ 0}
  have hcont : Continuous (fun x : E n => (fderiv ℝ F x).det) :=
    ContinuousLinearMap.continuous_det.comp (hF.continuous_fderiv (by norm_num))
  have hOopen : IsOpen O := by
    have hEq : O = {x : E n | (fderiv ℝ F x).det = 0}ᶜ := by
      ext x; simp only [O, Set.mem_setOf_eq, Set.mem_compl_iff, ne_eq]
    rw [hEq]
    exact (isClosed_eq hcont continuous_const).isOpen_compl
  -- the countable injective cover of the non-critical set
  obtain ⟨S, hSmeas, hSdisj, hSinj, hScover⟩ := injOnCover_det_ne_zero hF
  let T : ℕ → Set (E n) := fun k => A ∩ S k
  have hTmeas : ∀ k, MeasurableSet (T k) := fun k => hA.inter (hSmeas k)
  have hTdisj : Pairwise (Disjoint on T) := fun i j hij =>
    (hSdisj i j hij).mono Set.inter_subset_right Set.inter_subset_right
  have hTinj : ∀ k, Set.InjOn F (T k) := fun k => (hSinj k).mono Set.inter_subset_right
  have hTcover : A ∩ O ⊆ ⋃ k, T k := by
    intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hScover hx.2)
    exact Set.mem_iUnion.mpr ⟨k, hx.1, hk⟩
  -- each piece
  have hkey : ∀ k, volH n (F '' T k) = ∫⁻ u in T k, ENNReal.ofReal (hjac F u) ∂(volH n) := by
    intro k
    rw [volH_image_of_injOn hF (hTmeas k) (hTinj k), ← volH_lintegral_eq hF (hTmeas k)]
  have hsum : ∑' k, volH n (F '' T k)
      = ∫⁻ u in ⋃ k, T k, ENNReal.ofReal (hjac F u) ∂(volH n) := by
    simp_rw [hkey]
    rw [lintegral_iUnion hTmeas hTdisj]
  have hgood : volH n (⋃ k, F '' T k)
      ≤ ∫⁻ u in A, ENNReal.ofReal (hjac F u) ∂(volH n) :=
    le_trans (measure_iUnion_le _)
      (le_trans hsum.le (lintegral_mono_set (Set.iUnion_subset fun k => Set.inter_subset_left)))
  -- the critical set
  obtain ⟨N, hNmeas, hNsub, hNnull⟩ := criticalImage_null hF hA
  have hAcrit : A \ O ⊆ A ∩ {x : E n | (fderiv ℝ F x).det = 0} := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    by_contra hd
    exact hx.2 hd
  refine ⟨(⋃ k, F '' T k) ∪ N, ?_, ?_, ?_⟩
  · exact (MeasurableSet.iUnion fun k =>
      measurable_image_of_fderivWithin (hTmeas k)
        (fun x _ => ((hF.differentiable (by norm_num) x).hasFDerivAt).hasFDerivWithinAt)
        (hTinj k)).union hNmeas
  · rintro y ⟨x, hxA, rfl⟩
    by_cases hxO : x ∈ O
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hTcover ⟨hxA, hxO⟩)
      exact Or.inl (Set.mem_iUnion.mpr ⟨k, Set.mem_image_of_mem F hk⟩)
    · exact Or.inr (hNsub ⟨x, hAcrit ⟨hxA, hxO⟩, rfl⟩)
  · calc volH n ((⋃ k, F '' T k) ∪ N)
        ≤ volH n (⋃ k, F '' T k) + volH n N := measure_union_le _ _
      _ = volH n (⋃ k, F '' T k) + 0 := by rw [hNnull]
      _ ≤ (∫⁻ u in A, ENNReal.ofReal (hjac F u) ∂(volH n)) + 0 := by
            exact add_le_add hgood le_rfl
      _ = ∫⁻ u in A, ENNReal.ofReal (hjac F u) ∂(volH n) := add_zero _

end

end Work.Mostow
