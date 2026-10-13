import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.StrongPersist.H6Aux.R.tendstoGT_of_hasDerivAt_integrableOn
import Submission.Work.FTS.StrongPersist.H6Aux.R.tendstoLT_of_hasDerivAt_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.R

open MeasureTheory Filter Set intervalIntegral

/-- Near `0`, the function `θ ↦ θ⁻¹` is not integrable: it is the boundary case of
`intervalIntegrable_inv_iff`. -/
private lemma not_integrableOn_inv_Ioc {δ : ℝ} (hδ : 0 < δ) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => θ⁻¹) (Set.Ioc 0 δ) := by
  intro h
  have h2 : IntervalIntegrable (fun θ : ℝ => θ⁻¹) volume (0 : ℝ) δ := by
    refine ⟨h, ?_⟩
    rw [Set.Ioc_eq_empty_of_le hδ.le]
    exact MeasureTheory.integrableOn_empty
  rcases (intervalIntegrable_inv_iff (a := (0 : ℝ)) (b := δ)).1 h2 with h' | h'
  · exact (ne_of_lt hδ) h'
  · exact h' (by rw [Set.uIcc_of_le hδ.le]; exact ⟨le_rfl, hδ.le⟩)

/-- The translate `θ ↦ (θ - π/2)⁻¹` is not integrable on `(π/2 - δ, π/2)`. -/
private lemma not_integrableOn_sub_inv_Ioc {δ : ℝ} (hδ : 0 < δ) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => (θ - Real.pi / 2)⁻¹)
      (Set.Ioc (Real.pi / 2 - δ) (Real.pi / 2)) := by
  intro h
  have hlt : Real.pi / 2 - δ < Real.pi / 2 := by linarith
  have h2 : IntervalIntegrable (fun θ : ℝ => (θ - Real.pi / 2)⁻¹) volume
      (Real.pi / 2 - δ) (Real.pi / 2) := by
    refine ⟨h, ?_⟩
    rw [Set.Ioc_eq_empty_of_le hlt.le]
    exact MeasureTheory.integrableOn_empty
  rcases (intervalIntegrable_sub_inv_iff (a := Real.pi / 2 - δ) (b := Real.pi / 2)
    (c := Real.pi / 2)).1 h2 with h' | h'
  · exact (ne_of_gt hδ) (by linarith : δ = 0)
  · exact h' (by rw [Set.uIcc_of_le hlt.le]; exact ⟨by linarith, le_rfl⟩)

/-- The left limit of `sin (2·) u` is nonnegative, and strictly positive only if `u` is not
integrable; since `u` is integrable, it vanishes. -/
private lemma limit_eq_zero_left {u : ℝ → ℝ} {L : ℝ}
    (hu : MeasureTheory.IntegrableOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ u θ)
    (hLtend : Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    L = 0 := by
  have hnonneg : 0 ≤ L := by
    refine ge_of_tendsto hLtend ?_
    filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)]
      with θ hθ
    exact mul_nonneg
      (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])))
      (hu0 θ hθ)
  by_contra hLne
  have hLpos : 0 < L := lt_of_le_of_ne hnonneg (Ne.symm hLne)
  have hL4pos : 0 < L / 4 := by linarith
  have hev : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), L / 2 < Real.sin (2 * θ) * u θ :=
    hLtend.eventually (Ioi_mem_nhds (by linarith : L / 2 < L))
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := min (ε / 2) (Real.pi / 4) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hδle : δ ≤ ε / 2 := min_le_left _ _
  have hδle2 : δ ≤ Real.pi / 4 := min_le_right _ _
  have hsub : Set.Ioc (0 : ℝ) δ ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ
    exact ⟨hθ.1.le, by linarith [hθ.2, hδle2, Real.pi_pos]⟩
  -- on `(0, δ]` the function `u` dominates `(L/4) θ⁻¹`
  have hbound : ∀ θ ∈ Set.Ioc (0 : ℝ) δ, ‖(L / 4) * θ⁻¹‖ ≤ ‖u θ‖ := by
    intro θ hθ
    have hθpos : 0 < θ := hθ.1
    have hθpi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hθ.1, by linarith [hθ.2, hδle2, Real.pi_pos]⟩
    have huθ : 0 ≤ u θ := hu0 θ hθpi
    rw [Real.norm_of_nonneg (mul_nonneg hL4pos.le (inv_nonneg.mpr hθ.1.le)),
      Real.norm_of_nonneg huθ]
    have hFθ : L / 2 < Real.sin (2 * θ) * u θ := by
      refine hε ?_ hθpos
      rw [Real.dist_eq, sub_zero, abs_of_pos hθpos]
      linarith [hθ.2, hδle, hεpos]
    have hsle : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith)
    have h3 : L / 2 < (2 * θ) * u θ :=
      lt_of_lt_of_le hFθ (mul_le_mul_of_nonneg_right hsle huθ)
    have h4 : L / (4 * θ) ≤ u θ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [h3]
    have h5 : (L / 4) * θ⁻¹ = L / (4 * θ) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    linarith [h4, h5]
  -- hence `θ ↦ θ⁻¹` would be integrable on `(0, δ]`, contradiction
  have hintu : MeasureTheory.IntegrableOn u (Set.Ioc (0 : ℝ) δ) := hu.mono_set hsub
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (L / 4) * θ⁻¹)
      (volume.restrict (Set.Ioc (0 : ℝ) δ)) := by
    refine ((continuousOn_const.mul ((continuousOn_id :
      ContinuousOn (fun x : ℝ => x) (Set.Ioc (0 : ℝ) δ)).inv₀ ?_)).aestronglyMeasurable
        measurableSet_Ioc)
    intro x hx; exact ne_of_gt hx.1
  have hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioc (0 : ℝ) δ)), ‖(L / 4) * θ⁻¹‖ ≤ ‖u θ‖ := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun θ hθ => hbound θ hθ)
  have hint1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (L / 4) * θ⁻¹) (Set.Ioc (0 : ℝ) δ) :=
    MeasureTheory.Integrable.mono hintu haesm hae
  have hint2 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ⁻¹) (Set.Ioc (0 : ℝ) δ) := by
    have h := MeasureTheory.Integrable.const_mul hint1 ((L / 4)⁻¹)
    have heq : (fun θ : ℝ => (L / 4)⁻¹ * ((L / 4) * θ⁻¹)) = fun θ : ℝ => θ⁻¹ := by
      funext θ
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hL4pos), one_mul]
    rwa [heq] at h
  exact (not_integrableOn_inv_Ioc hδpos) hint2

/-- The right limit of `sin (2·) u` is nonnegative, and strictly positive only if `u` is not
integrable; since `u` is integrable, it vanishes. -/
private lemma limit_eq_zero_right {u : ℝ → ℝ} {L : ℝ}
    (hu : MeasureTheory.IntegrableOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ u θ)
    (hLtend : Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L)) :
    L = 0 := by
  have hnonneg : 0 ≤ L := by
    refine ge_of_tendsto hLtend ?_
    filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)]
      with θ hθ
    exact mul_nonneg
      (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])))
      (hu0 θ hθ)
  by_contra hLne
  have hLpos : 0 < L := lt_of_le_of_ne hnonneg (Ne.symm hLne)
  have hL4pos : 0 < L / 4 := by linarith
  have hev : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      L / 2 < Real.sin (2 * θ) * u θ :=
    hLtend.eventually (Ioi_mem_nhds (by linarith : L / 2 < L))
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := min (ε / 2) (Real.pi / 4) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hδle : δ ≤ ε / 2 := min_le_left _ _
  have hδle2 : δ ≤ Real.pi / 4 := min_le_right _ _
  set a : ℝ := Real.pi / 2 - δ with hadef
  have hapos : 0 < a := by rw [hadef]; linarith [hδle2, Real.pi_pos]
  have halt : a < Real.pi / 2 := by rw [hadef]; linarith
  have hsub : Set.Ioc a (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ
    exact ⟨le_of_lt (lt_trans hapos hθ.1), hθ.2⟩
  -- on `(a, π/2]` the function `u` dominates `(L/4) (θ - π/2)⁻¹` up to sign
  have hbound : ∀ θ ∈ Set.Ioc a (Real.pi / 2), ‖(L / 4) * (θ - Real.pi / 2)⁻¹‖ ≤ ‖u θ‖ := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.2 with h | h
    · subst h; simp
    · have hθpos : 0 < θ := lt_trans hapos hθ.1
      have huθ : 0 ≤ u θ := hu0 θ ⟨hθpos, h⟩
      have hinv : (θ - Real.pi / 2)⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
      rw [Real.norm_of_nonpos (mul_neg_of_pos_of_neg hL4pos hinv).le,
        Real.norm_of_nonneg huθ]
      have hthis : -((L / 4) * (θ - Real.pi / 2)⁻¹) = (L / 4) * (Real.pi / 2 - θ)⁻¹ := by
        rw [show θ - Real.pi / 2 = -(Real.pi / 2 - θ) by ring, inv_neg]
        ring
      rw [hthis]
      have hsle : Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
        have h1 : 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) := by ring
        have h2 : (0 : ℝ) ≤ 2 * (Real.pi / 2 - θ) := by linarith
        calc Real.sin (2 * θ) = Real.sin (Real.pi - 2 * (Real.pi / 2 - θ)) := by rw [h1]
          _ = Real.sin (2 * (Real.pi / 2 - θ)) := Real.sin_pi_sub _
          _ ≤ 2 * (Real.pi / 2 - θ) := Real.sin_le h2
      have hFθ : L / 2 < Real.sin (2 * θ) * u θ := by
        refine hε ?_ h
        rw [Real.dist_eq, abs_of_neg (by linarith : θ - Real.pi / 2 < 0)]
        linarith [hθ.1, hδle, hεpos]
      have h3 : L / 2 < (2 * (Real.pi / 2 - θ)) * u θ :=
        lt_of_lt_of_le hFθ (mul_le_mul_of_nonneg_right hsle huθ)
      have h4 : L / (4 * (Real.pi / 2 - θ)) ≤ u θ := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [h3]
      have h5 : (L / 4) * (Real.pi / 2 - θ)⁻¹ = L / (4 * (Real.pi / 2 - θ)) := by
        simp only [div_eq_mul_inv, mul_inv]
        ring
      linarith [h4, h5]
  -- hence `θ ↦ (θ - π/2)⁻¹` would be integrable on `(a, π/2]`, contradiction
  have hintu : MeasureTheory.IntegrableOn u (Set.Ioc a (Real.pi / 2)) := hu.mono_set hsub
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (L / 4) * (θ - Real.pi / 2)⁻¹)
      (volume.restrict (Set.Ioc a (Real.pi / 2))) :=
    ((((measurable_id.sub measurable_const)).inv).const_mul (L / 4)).aestronglyMeasurable.restrict
  have hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioc a (Real.pi / 2))),
      ‖(L / 4) * (θ - Real.pi / 2)⁻¹‖ ≤ ‖u θ‖ := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun θ hθ => hbound θ hθ)
  have hint1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (L / 4) * (θ - Real.pi / 2)⁻¹)
      (Set.Ioc a (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono hintu haesm hae
  have hint2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (θ - Real.pi / 2)⁻¹)
      (Set.Ioc a (Real.pi / 2)) := by
    have h := MeasureTheory.Integrable.const_mul hint1 ((L / 4)⁻¹)
    have heq : (fun θ : ℝ => (L / 4)⁻¹ * ((L / 4) * (θ - Real.pi / 2)⁻¹))
        = fun θ : ℝ => (θ - Real.pi / 2)⁻¹ := by
      funext θ
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hL4pos), one_mul]
    rwa [heq] at h
  have hnot : ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => (θ - Real.pi / 2)⁻¹)
      (Set.Ioc a (Real.pi / 2)) := by
    rw [hadef]
    exact not_integrableOn_sub_inv_Ioc hδpos
  exact hnot hint2

/-- The left endpoint: `sin (2θ) u θ → 0` as `θ → 0⁺`. -/
private lemma left_tendsto {u v' : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ u θ)
    (hv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' => Real.sin (2 * θ') * u θ') (v' θ) θ)
    (hv' : MeasureTheory.IntegrableOn v' (Set.Icc 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hc0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hc2 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      HasDerivAt (fun θ => Real.sin (2 * θ) * u θ) (v' x) x :=
    fun x hx => hv x ⟨hx.1, by linarith [hx.2]⟩
  have hcont : ContinuousAt (fun θ => Real.sin (2 * θ) * u θ) (Real.pi / 4) :=
    (hv (Real.pi / 4) ⟨by linarith, by linarith⟩).continuousAt
  have hint : IntervalIntegrable v' volume (0 : ℝ) (Real.pi / 4) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc0.le]
    exact hv'.mono_set (Set.Icc_subset_Icc_right hc2.le)
  have hex := tendstoGT_of_hasDerivAt_integrableOn hc0 hderiv hcont hint
  set L : ℝ := Real.sin (2 * (Real.pi / 4)) * u (Real.pi / 4)
    - ∫ x in (0 : ℝ)..(Real.pi / 4), v' x with hL
  have hLtend : Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
    rw [hL]; exact hex
  have hLzero : L = 0 := limit_eq_zero_left hu hu0 hLtend
  rw [hLzero] at hLtend
  exact hLtend

/-- The right endpoint: `sin (2θ) u θ → 0` as `θ → (π/2)⁻`. -/
private lemma right_tendsto {u v' : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ u θ)
    (hv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' => Real.sin (2 * θ') * u θ') (v' θ) θ)
    (hv' : MeasureTheory.IntegrableOn v' (Set.Icc 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hc0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hc2 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hderiv : ∀ x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      HasDerivAt (fun θ => Real.sin (2 * θ) * u θ) (v' x) x :=
    fun x hx => hv x ⟨by linarith [hx.1], hx.2⟩
  have hcont : ContinuousAt (fun θ => Real.sin (2 * θ) * u θ) (Real.pi / 4) :=
    (hv (Real.pi / 4) ⟨by linarith, by linarith⟩).continuousAt
  have hint : IntervalIntegrable v' volume (Real.pi / 4) (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc2.le]
    exact hv'.mono_set (Set.Icc_subset_Icc_left hc0.le)
  have hex := tendstoLT_of_hasDerivAt_integrableOn hc2 hderiv hcont hint
  set L : ℝ := Real.sin (2 * (Real.pi / 4)) * u (Real.pi / 4)
    + ∫ x in (Real.pi / 4)..(Real.pi / 2), v' x with hL
  have hLtend : Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L) := by
    rw [hL]; exact hex
  have hLzero : L = 0 := limit_eq_zero_right hu hu0 hLtend
  rw [hLzero] at hLtend
  exact hLtend

theorem SinBoundaryTendsto {u v' : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ u θ)
    (hv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' => Real.sin (2 * θ') * u θ') (v' θ) θ)
    (hv' : MeasureTheory.IntegrableOn v' (Set.Icc 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
  ⟨left_tendsto hu hu0 hv hv', right_tendsto hu hu0 hv hv'⟩

end Work.FTS.StrongPersist.H6Aux.R
