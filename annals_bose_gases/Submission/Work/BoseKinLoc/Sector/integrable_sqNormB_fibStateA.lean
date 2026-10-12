import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Sector.integrable_sqNormB_fibState
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseKinLoc.Sector

set_option maxHeartbeats 1000000

/-- **The box mass of the fibre is integrable over the translated outside configurations.**  For a smooth state `Ψ` supported in the *translated* box `c + abox N L`, and any slot set `S`, the box mass `y ↦ sqNormB |S| ℓ (fibState S Ψ y)` of the fibre is integrable over the outside configurations of the translated ambient box `c + acube (max L ℓ)` that lie outside `acube ℓ`.  This is the translated-support version of `integrable_sqNormB_fibState`, needed by the assembly of the fibre bound (where the translation covariance `word_translate` moves the support of the state to the translated box `(-ℓu) + abox N L` while the sector box stays at the origin).  Proof: `Ψ` is smooth with compact support, hence bounded by some `M`, so the fibre box mass is uniformly bounded by `M² · vol(acube ℓ)`, while the integration region is contained in the bounded box `(c + acube (max L ℓ))^{SlotOut}` (of finite measure); a bounded measurable function on a finite-measure set is integrable.  (This boundedness route is cleaner than transporting the Fubini identity of `slotMassENN_eq_fibre`, whose slot coordinates are not shifted.) -/
theorem integrable_sqNormB_fibStateA {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {c : ℝ³} {L : ℝ}
    (S : Finset (Fin N)) {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ (fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) ''
      Submission.BoseGases.abox N L) :
    MeasureTheory.IntegrableOn (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
      Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y))
      (Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
        (((fun z : ℝ³ => c + z) '' Submission.BoseGases.acube (max L ℓ))
          ∩ (Submission.BoseGases.acube ℓ)ᶜ)) := by
  classical
  -- ## Step 1: the state is bounded (smooth and supported in a translate of the box)
  have hcont : Continuous (fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) := by
    fun_prop
  have hK : IsCompact ((fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) ''
      Submission.BoseGases.abox N L) :=
    (Work.UBBInputs9.B.abox_isCompact N L).image hcont
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hΨ.continuous.continuousOn
  have hbound : ∀ x : Submission.BoseGases.X N, ‖Ψ x‖ ≤ max M 0 := by
    intro x
    by_cases hx : x ∈ (fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) ''
        Submission.BoseGases.abox N L
    · exact le_trans (hM x hx) (le_max_left _ _)
    · -- off the support of `Ψ` the state vanishes
      have hx' : x ∉ tsupport Ψ := fun h => hx (hsupp h)
      have hzero : Ψ x = 0 := by
        by_contra hne
        exact hx' (subset_tsupport Ψ (Function.mem_support.mpr hne))
      rw [hzero, norm_zero]
      exact le_max_right _ _
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  -- ## Step 2: hence so is the fibre, and its box mass
  have hfib : ∀ (y : Work.PerSector.SlotOut N S → ℝ³) (x : Submission.BoseGases.X S.card),
      ‖fibState S Ψ y x‖ ≤ max M 0 := by
    intro y x
    rw [fibState_apply]
    exact hbound _
  have hs : (volume : Measure (Submission.BoseGases.X S.card)) (Submission.BoseGases.abox S.card ℓ)
      < ∞ := Submission.BoseGases.abox_lt_top S.card ℓ (le_of_lt hℓ)
  have hsq : ∀ y : Work.PerSector.SlotOut N S → ℝ³,
      ‖Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y)‖
        ≤ (max M 0) ^ 2 * (volume : Measure (Submission.BoseGases.X S.card)).real
            (Submission.BoseGases.abox S.card ℓ) := by
    intro y
    rw [Work.BoseKinLoc.sqNormB]
    refine (MeasureTheory.norm_setIntegral_le_of_norm_le_const (C := (max M 0) ^ 2) hs ?_).trans_eq ?_
    · intro x _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (fibState S Ψ y x))]
      have h := hfib y x
      rw [Real.norm_eq_abs] at h
      calc (fibState S Ψ y x) ^ 2 = |fibState S Ψ y x| ^ 2 := by rw [sq_abs]
        _ ≤ (max M 0) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    · rw [MeasureTheory.Measure.real_def]
  -- ## Step 3: measurability of the fibre box mass in the outside configuration
  have hmeasL : Measurable (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
      ∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
          (Submission.BoseGases.acube ℓ),
        ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2)) :=
    measurable_lintegral_slotFibre S (Submission.BoseGases.acube_measurable ℓ)
      hΨ.continuous.measurable
  have hpoint : ∀ y : Work.PerSector.SlotOut N S → ℝ³,
      Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y)
        = (∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
              (Submission.BoseGases.acube ℓ),
            ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2)).toReal := by
    intro y
    rw [sqNormB_fibState_eq_slotFibreMassReal S hΨ y]
    rfl
  have hmeas : AEStronglyMeasurable (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
      Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y))
      ((volume : Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
        (Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
          (((fun z : ℝ³ => c + z) '' Submission.BoseGases.acube (max L ℓ))
            ∩ (Submission.BoseGases.acube ℓ)ᶜ))) :=
    (hmeasL.ennreal_toReal.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall (fun y => (hpoint y).symm))
  -- ## Step 4: the integration region has finite measure
  have hρ'pos : 0 < max L ℓ := lt_of_lt_of_le hℓ (le_max_right L ℓ)
  have hAcube : ((fun z : ℝ³ => c + z) '' Submission.BoseGases.acube (max L ℓ))
      ⊆ Submission.BoseGases.acube (2 * ‖c‖ + Real.sqrt 3 * (max L ℓ)) := by
    rintro z ⟨w, hw, rfl⟩
    have hρnn : 0 ≤ 2 * ‖c‖ + Real.sqrt 3 * (max L ℓ) := by
      have := Real.sqrt_nonneg 3
      nlinarith [norm_nonneg c, le_of_lt hρ'pos, this]
    refine Submission.BoseGases.mem_acube_of_norm_le hρnn ?_
    have hw' : ∀ m : Fin 3, |w m| ≤ (max L ℓ) / 2 := by
      intro m
      rw [Submission.BoseGases.mem_acube_iff] at hw
      have hm := hw m
      rw [Set.mem_Icc] at hm
      exact abs_le.mpr ⟨by linarith [hm.1], hm.2⟩
    have hwn : ‖w‖ ≤ Real.sqrt 3 * ((max L ℓ) / 2) :=
      Submission.BoseGases.eucl_norm_le_of_abs_coord_le (by linarith) hw'
    have hsum : ‖c + w‖ ≤ ‖c‖ + Real.sqrt 3 * ((max L ℓ) / 2) :=
      le_trans (norm_add_le c w) (by linarith)
    have hhalf : (2 * ‖c‖ + Real.sqrt 3 * (max L ℓ)) / 2
        = ‖c‖ + Real.sqrt 3 * ((max L ℓ) / 2) := by ring
    rw [hhalf]
    exact hsum
  have hvol : (volume : Measure (Work.PerSector.SlotOut N S → ℝ³))
      (Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
        (Submission.BoseGases.acube (2 * ‖c‖ + Real.sqrt 3 * (max L ℓ))))
      = ∏ _i : Work.PerSector.SlotOut N S,
          (volume : Measure ℝ³) (Submission.BoseGases.acube (2 * ‖c‖ + Real.sqrt 3 * (max L ℓ))) := by
    rw [show Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
        (Submission.BoseGases.acube (2 * ‖c‖ + Real.sqrt 3 * (max L ℓ)))
        = Set.univ.pi (fun _ : Work.PerSector.SlotOut N S =>
            Submission.BoseGases.acube (2 * ‖c‖ + Real.sqrt 3 * (max L ℓ))) by
      ext z; simp [Work.PerSector.slotBox, Set.mem_pi]]
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  have hfin : (volume : Measure (Work.PerSector.SlotOut N S → ℝ³))
      (Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
        (((fun z : ℝ³ => c + z) '' Submission.BoseGases.acube (max L ℓ))
          ∩ (Submission.BoseGases.acube ℓ)ᶜ)) < ∞ := by
    refine lt_of_le_of_lt (MeasureTheory.measure_mono
      (Work.PerSector.Work.PerSector.slotBox_mono (Set.inter_subset_left.trans hAcube))) ?_
    rw [hvol]
    refine ENNReal.prod_lt_top (fun i _ => ?_)
    have hρnn : 0 ≤ 2 * ‖c‖ + Real.sqrt 3 * (max L ℓ) := by
      have := Real.sqrt_nonneg 3
      nlinarith [norm_nonneg c, le_of_lt hρ'pos, this]
    rw [Submission.BoseGases.acube_volume _ hρnn]
    exact ENNReal.ofReal_lt_top
  -- ## Step 5: a bounded measurable function on a set of finite measure is integrable
  exact MeasureTheory.IntegrableOn.of_bound hfin hmeas _
    (Filter.Eventually.of_forall hsq)

end Work.BoseKinLoc.Sector
