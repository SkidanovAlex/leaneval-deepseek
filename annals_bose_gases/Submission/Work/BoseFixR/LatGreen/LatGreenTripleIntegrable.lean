import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Submission.Work.BoseFixR.LatGreen.LatGreenParsevalBDefs
import Submission.Work.BoseFixR.LatGreen.integrableOn_period
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Real BigOperators ENNReal
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

/-! ## Auxiliary lemmas -/

/-- The closed cell is measurable. -/
lemma measurableSet_cell (ℓ : ℝ) : MeasurableSet (Work.BoseFixR.cell ℓ) := by
  rw [Work.BoseFixR.cell_eq_boxL ℓ]
  exact Work.BoseFixR.measurableSet_boxL ℓ

/-- `ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c = ENNReal.ofReal (a * b * c)` for
nonnegative `a`, `b`. -/
lemma ofReal_mul_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c = ENNReal.ofReal (a * b * c) := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb)]

/-- **The `1/‖u − n‖` comparison.**  If `latGreenSmooth` is bounded below by `-Mdom` off the
lattice, then for off-lattice `u` and every lattice label `n`,

`1/‖u − latVec n‖ ≤ 4π (latGreen u + max Mdom 0)`,

and `latGreen u + max Mdom 0 ≥ 0`.  The proof uses the periodicity of `latGreen` and the
decomposition `latGreen = 1/(4π‖·‖) + latGreenSmooth`. -/
theorem inv_dist_le_latGreen {Mdom : ℝ}
    (hlt : ∀ u : EuclideanSpace ℝ (Fin 3),
      (∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) →
        -Mdom ≤ Work.BoseFixR.LatGreen.latGreenSmooth u) :
    ∀ u : EuclideanSpace ℝ (Fin 3), (∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) →
      ∀ n : Fin 3 → ℤ,
        0 ≤ Work.BoseFixR.LatGreen.latGreen u + max Mdom 0 ∧
          1 / ‖u - Work.BoseFixR.LatGreen.latVec n‖
            ≤ 4 * Real.pi * (Work.BoseFixR.LatGreen.latGreen u + max Mdom 0) := by
  intro u hu n
  have hsub : u - latVec n ≠ 0 := fun h => hu n (sub_eq_zero.mp h)
  have hv : ∀ m : Fin 3 → ℤ, u - latVec n ≠ latVec m := by
    intro m hm
    refine hu (m + n) ?_
    have h2 : u = latVec m + latVec n := by rw [← hm]; abel
    rw [h2, latVec_add]
  have hsmooth : -max Mdom 0 ≤ latGreenSmooth (u - latVec n) := by
    have h := hlt (u - latVec n) hv
    have := le_max_left Mdom 0
    linarith
  have hper : latGreen (u - latVec n) = latGreen u := by
    simpa [sub_eq_add_neg, latVec_neg] using latGreen_periodic u (-n)
  have hLG : latGreen u = 1 / (4 * Real.pi * ‖u - latVec n‖) + latGreenSmooth (u - latVec n) := by
    rw [← hper, latGreenSmooth]
    ring
  have hpos : 0 < 1 / (4 * Real.pi * ‖u - latVec n‖) :=
    div_pos one_pos (mul_pos (by positivity) (norm_pos_iff.mpr hsub))
  have hkey : 1 / (4 * Real.pi * ‖u - latVec n‖) ≤ latGreen u + max Mdom 0 := by
    rw [hLG]; linarith
  constructor
  · linarith
  · have h4 : (0 : ℝ) < 4 * Real.pi := by positivity
    have hmul := mul_le_mul_of_nonneg_left hkey h4.le
    have heq : 4 * Real.pi * (1 / (4 * Real.pi * ‖u - latVec n‖)) = 1 / ‖u - latVec n‖ := by
      field_simp
    rwa [heq] at hmul

/-- **Almost every difference of two points of a cell is off the lattice.**  The set of
`p` with `ℓ⁻¹ • (p.1 - p.2) = latVec n` for some lattice label `n` is a countable union of
null sets (each such set meets every line `p.1 - p.2 = const` in a single point). -/
theorem ae_offLattice_sub {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ p ∂(MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)),
      ∀ n : Fin 3 → ℤ, ℓ⁻¹ • (p.1 - p.2) ≠ Work.BoseFixR.LatGreen.latVec n := by
  set μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)) :=
    MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ) with hμ
  have hρ : (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)
      : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
        = μ.prod μ :=
    (MeasureTheory.Measure.prod_restrict _ _).symm
  rw [hρ]
  have hnull : ∀ n : Fin 3 → ℤ,
      (μ.prod μ) {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
        ℓ⁻¹ • (p.1 - p.2) = latVec n} = 0 := by
    intro n
    have hT : MeasurableSet {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
        ℓ⁻¹ • (p.1 - p.2) = latVec n} :=
      (isClosed_eq (by fun_prop : Continuous fun p :
          EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => ℓ⁻¹ • (p.1 - p.2))
        continuous_const).measurableSet
    rw [MeasureTheory.Measure.prod_apply hT]
    have hsec : ∀ a : EuclideanSpace ℝ (Fin 3),
        μ (Prod.mk a ⁻¹' {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
            ℓ⁻¹ • (p.1 - p.2) = latVec n}) = 0 := by
      intro a
      have hsub : Prod.mk a ⁻¹' {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
            ℓ⁻¹ • (p.1 - p.2) = latVec n} ⊆ {a - ℓ • latVec n} := by
        intro b hb
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hb ⊢
        have h1 : ℓ • (ℓ⁻¹ • (a - b)) = ℓ • latVec n := by rw [hb]
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul] at h1
        rw [show b = a - (a - b) by abel, h1]
      exact MeasureTheory.measure_mono_null hsub (measure_singleton _)
    have hfun : (fun a : EuclideanSpace ℝ (Fin 3) =>
          μ (Prod.mk a ⁻¹' {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
            ℓ⁻¹ • (p.1 - p.2) = latVec n})) = fun _ => (0 : ℝ≥0∞) := funext hsec
    rw [hfun]
    simp
  rw [MeasureTheory.ae_iff]
  have hseteq : {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
        ¬ (∀ n : Fin 3 → ℤ, ℓ⁻¹ • (p.1 - p.2) ≠ latVec n)}
      = ⋃ n : Fin 3 → ℤ, {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
          ℓ⁻¹ • (p.1 - p.2) = latVec n} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, not_forall, not_ne_iff]
  rw [hseteq]
  exact MeasureTheory.measure_iUnion_null hnull

/-- **The large-`s` part of the heat-kernel integral is uniformly bounded.**  For every `u`,
`∫⁻_{s>1} |heatPeriod s u − 1| ds ≤ ofReal B`, with `B` independent of `u`. -/
theorem lintegral_Ioi_one_heatPeriod_sub_one :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
      ∫⁻ s in Set.Ioi (1 : ℝ),
          (ENNReal.ofReal |Work.BoseFixR.LatGreen.heatPeriod s u - 1|)
        ≤ ENNReal.ofReal B := by
  set K : ℝ := ∑' k : {k : Fin 3 → ℤ // k ≠ 0},
      Real.exp (-(‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact tsum_nonneg fun k => Real.exp_nonneg _
  refine ⟨K * Real.exp 1 * Real.exp (-1), by positivity, fun u => ?_⟩
  have hint : MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp (-s)) (Set.Ioi (1 : ℝ)) := by
    simpa only [neg_mul, one_mul] using exp_neg_integrableOn_Ioi (a := 1) (b := 1) one_pos
  calc ∫⁻ s in Set.Ioi (1 : ℝ), (ENNReal.ofReal |heatPeriod s u - 1|)
      ≤ ∫⁻ s in Set.Ioi (1 : ℝ), (ENNReal.ofReal (K * Real.exp 1 * Real.exp (-s))) := by
        apply MeasureTheory.lintegral_mono_ae
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
        refine ENNReal.ofReal_le_ofReal ?_
        have h := abs_heatPeriod_sub_one_le_exp (le_of_lt hs) u
        rwa [← hK] at h
    _ = ENNReal.ofReal (K * Real.exp 1)
          * ∫⁻ s in Set.Ioi (1 : ℝ), (ENNReal.ofReal (Real.exp (-s))) := by
        rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (K * Real.exp 1)) _
          ENNReal.ofReal_ne_top]
        apply MeasureTheory.lintegral_congr
        intro s
        rw [ENNReal.ofReal_mul (mul_nonneg hKnn (Real.exp_nonneg _))]
    _ = ENNReal.ofReal (K * Real.exp 1) * ENNReal.ofReal (Real.exp (-1)) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun s => Real.exp_nonneg _), integral_exp_neg_Ioi 1]
    _ = ENNReal.ofReal (K * Real.exp 1 * Real.exp (-1)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hKnn (Real.exp_nonneg _))]

/-- **The small-`s` part of the heat-kernel integral against the `latBox` domination.** -/
theorem lintegral_Ioc_one_le {Cdom : ℝ}
    (hdom : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u : EuclideanSpace ℝ (Fin 3),
      (∀ i : Fin 3, |u i| ≤ 2) → (∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) →
        ∫ s in Set.Ioc 0 ε, |Work.BoseFixR.LatGreen.heatPeriod s u - 1|
          ≤ Cdom * (1 + ∑ n ∈ Work.BoseFixR.LatGreen.latBox,
              1 / ‖u - Work.BoseFixR.LatGreen.latVec n‖)) :
    ∀ u : EuclideanSpace ℝ (Fin 3), (∀ i : Fin 3, |u i| ≤ 2) →
      (∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) →
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            (ENNReal.ofReal |Work.BoseFixR.LatGreen.heatPeriod s u - 1|)
          ≤ ENNReal.ofReal (Cdom * (1 + ∑ n ∈ Work.BoseFixR.LatGreen.latBox,
              1 / ‖u - Work.BoseFixR.LatGreen.latVec n‖)) := by
  intro u h2 hoff
  have hint : MeasureTheory.IntegrableOn (fun s : ℝ => |heatPeriod s u - 1|) (Set.Ioc 0 1) :=
    ((PeriodIntegrable hoff).mono_set Set.Ioc_subset_Ioi_self).abs
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun s => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hdom 1 zero_lt_one le_rfl u h2 hoff)

/-- **The pointwise `s`-integral bound.**  Combination of `lintegral_Ioc_one_le`,
`inv_dist_le_latGreen` and `lintegral_Ioi_one_heatPeriod_sub_one`: for off-lattice
`u` with `|u i| ≤ 2`,

`∫_0^∞ |heatPeriod s u − 1| ds ≤ ofReal Cdom (1 + #latBox (4π|latGreen u| + 4π max Mdom 0)) + ofReal B`.

This is the bound which hypothesis **(B)** integrates against `|P p₁ P p₂|`. -/
theorem lintegral_heatPeriod_sub_one_le {Cdom Mdom : ℝ}
    (hdom : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u : EuclideanSpace ℝ (Fin 3),
      (∀ i : Fin 3, |u i| ≤ 2) → (∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) →
        ∫ s in Set.Ioc 0 ε, |Work.BoseFixR.LatGreen.heatPeriod s u - 1|
          ≤ Cdom * (1 + ∑ n ∈ Work.BoseFixR.LatGreen.latBox,
              1 / ‖u - Work.BoseFixR.LatGreen.latVec n‖))
    (hlt : ∀ u : EuclideanSpace ℝ (Fin 3),
      (∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) →
        -Mdom ≤ Work.BoseFixR.LatGreen.latGreenSmooth u)
    {B0 : ℝ}
    (hB0 : ∀ u : EuclideanSpace ℝ (Fin 3),
      ∫⁻ s in Set.Ioi (1 : ℝ),
          (ENNReal.ofReal |Work.BoseFixR.LatGreen.heatPeriod s u - 1|)
        ≤ ENNReal.ofReal B0)
    {u : EuclideanSpace ℝ (Fin 3)} (hoff : ∀ n : Fin 3 → ℤ, u ≠ latVec n)
    (h2 : ∀ i : Fin 3, |u i| ≤ 2) :
    (∫⁻ s, (ENNReal.ofReal |heatPeriod s u - 1|)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
      ≤ ENNReal.ofReal Cdom * (1 + (Work.BoseFixR.LatGreen.latBox.card : ℝ≥0∞) *
          (ENNReal.ofReal (4 * Real.pi * |latGreen u|)
            + ENNReal.ofReal (4 * Real.pi * max Mdom 0)))
        + ENNReal.ofReal B0 := by
  have hSum : 0 ≤ ∑ n ∈ latBox, 1 / ‖u - latVec n‖ :=
    Finset.sum_nonneg fun n _ => div_nonneg zero_le_one (norm_nonneg _)
  have hSnn : 0 ≤ 1 + ∑ n ∈ latBox, 1 / ‖u - latVec n‖ := add_nonneg zero_le_one hSum
  have hsplit : (∫⁻ s, (ENNReal.ofReal |heatPeriod s u - 1|)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
      = (∫⁻ s in Set.Ioc (0 : ℝ) 1, (ENNReal.ofReal |heatPeriod s u - 1|))
        + (∫⁻ s in Set.Ioi (1 : ℝ), (ENNReal.ofReal |heatPeriod s u - 1|)) := by
    have h1 : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
      ext s
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h, _⟩ | h)
        · exact h
        · linarith
      · intro h
        by_cases h' : s ≤ 1
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr (lt_of_not_ge h')
    have h2' : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
      Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx')
    have h3 := MeasureTheory.Measure.restrict_union (μ := MeasureTheory.volume) h2'
      measurableSet_Ioi
    rw [h1] at h3
    rw [h3, MeasureTheory.lintegral_add_measure]
  have hP1 : (∫⁻ s in Set.Ioc (0 : ℝ) 1, (ENNReal.ofReal |heatPeriod s u - 1|))
      ≤ ENNReal.ofReal Cdom * (1 + (latBox.card : ℝ≥0∞) *
          (ENNReal.ofReal (4 * Real.pi * |latGreen u|)
            + ENNReal.ofReal (4 * Real.pi * max Mdom 0))) := by
    refine le_trans (lintegral_Ioc_one_le hdom u h2 hoff) ?_
    have hSbound : ENNReal.ofReal (1 + ∑ n ∈ latBox, 1 / ‖u - latVec n‖)
        ≤ 1 + (latBox.card : ℝ≥0∞) * (ENNReal.ofReal (4 * Real.pi * |latGreen u|)
            + ENNReal.ofReal (4 * Real.pi * max Mdom 0)) := by
      have hterm : ∀ n ∈ latBox, ENNReal.ofReal (1 / ‖u - latVec n‖)
          ≤ ENNReal.ofReal (4 * Real.pi * (latGreen u + max Mdom 0)) := fun n _ =>
        ENNReal.ofReal_le_ofReal (inv_dist_le_latGreen hlt u hoff n).2
      calc ENNReal.ofReal (1 + ∑ n ∈ latBox, 1 / ‖u - latVec n‖)
          = ENNReal.ofReal 1 + ENNReal.ofReal (∑ n ∈ latBox, 1 / ‖u - latVec n‖) :=
            ENNReal.ofReal_add zero_le_one hSum
        _ = 1 + ∑ n ∈ latBox, ENNReal.ofReal (1 / ‖u - latVec n‖) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => div_nonneg zero_le_one (norm_nonneg _)),
              ENNReal.ofReal_one]
        _ ≤ 1 + ∑ n ∈ latBox, ENNReal.ofReal (4 * Real.pi * (latGreen u + max Mdom 0)) := by
            refine add_le_add le_rfl ?_
            exact Finset.sum_le_sum fun n hn => hterm n hn
        _ = 1 + (latBox.card : ℝ≥0∞) *
              ENNReal.ofReal (4 * Real.pi * (latGreen u + max Mdom 0)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 1 + (latBox.card : ℝ≥0∞) * (ENNReal.ofReal (4 * Real.pi * |latGreen u|)
            + ENNReal.ofReal (4 * Real.pi * max Mdom 0)) := by
            refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le)
            have hC : 0 ≤ 4 * Real.pi * max Mdom 0 :=
              mul_nonneg (by positivity) (le_max_right Mdom 0)
            have hA : 0 ≤ 4 * Real.pi * |latGreen u| :=
              mul_nonneg (by positivity) (abs_nonneg _)
            rw [← ENNReal.ofReal_add hA hC]
            refine ENNReal.ofReal_le_ofReal ?_
            have hrw : 4 * Real.pi * (latGreen u + max Mdom 0)
                = 4 * Real.pi * latGreen u + 4 * Real.pi * max Mdom 0 := by ring
            rw [hrw]
            exact add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)) le_rfl
    calc ENNReal.ofReal (Cdom * (1 + ∑ n ∈ latBox, 1 / ‖u - latVec n‖))
        = ENNReal.ofReal Cdom * ENNReal.ofReal (1 + ∑ n ∈ latBox, 1 / ‖u - latVec n‖) := by
          rw [mul_comm Cdom _, ENNReal.ofReal_mul hSnn, mul_comm]
      _ ≤ ENNReal.ofReal Cdom * (1 + (latBox.card : ℝ≥0∞) *
            (ENNReal.ofReal (4 * Real.pi * |latGreen u|)
              + ENNReal.ofReal (4 * Real.pi * max Mdom 0))) := mul_le_mul_of_nonneg_left hSbound zero_le
  rw [hsplit]
  exact add_le_add hP1 (hB0 u)

/-- **The `ℓ²`-normalised factorisation** used to recognise hypothesis **(B)**:
`ofReal|P p₁| · ofReal|P p₂| · ofReal(4π|latGreen u|) = ofReal(4π/ℓ²) · ofReal|P p₁ P p₂ (ℓ² latGreen u)|`
with `u = ℓ⁻¹ • (p₁ − p₂)`. -/
theorem ofReal_fac {ℓ : ℝ} (hℓ : 0 < ℓ) (W : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|
        * ENNReal.ofReal (4 * Real.pi * |latGreen (ℓ⁻¹ • (p.1 - p.2))|)
      = ENNReal.ofReal (4 * Real.pi / ℓ ^ 2)
        * ENNReal.ofReal |period W ℓ p.1 * period W ℓ p.2
            * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (p.1 - p.2)))| := by
  have hℓ2 : (0 : ℝ) ≤ ℓ ^ 2 := by positivity
  have h4 : (0 : ℝ) ≤ 4 * Real.pi / ℓ ^ 2 := by positivity
  have habs : |period W ℓ p.1 * period W ℓ p.2 * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (p.1 - p.2)))|
      = |period W ℓ p.1| * |period W ℓ p.2|
        * (ℓ ^ 2 * |latGreen (ℓ⁻¹ • (p.1 - p.2))|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hℓ2]
  rw [ofReal_mul_three (abs_nonneg _) (abs_nonneg _), habs,
    ← ENNReal.ofReal_mul h4]
  congr 1
  field_simp
  try ring

/-! ## The main theorem -/

/-- **Absolute integrability of the heat-kernel form of the lattice-row integrand** (the Fubini
licence of `Work.BoseFixR.LatGreen.LatGreenParsevalB`).

With `P = period W ℓ` and `f_s(u) = heatPeriod s u − 1`, the function
`(s,p₁,p₂) ↦ P p₁ · P p₂ · f_s(ℓ⁻¹•(p₁ − p₂))` is integrable for the product of
`volume.restrict (Ioi 0)` and `volume.restrict (cell ℓ ×ˢ cell ℓ)`.

This is exactly the hypothesis needed to exchange the `s`-integration with the cell double
integral when writing the periodic Green kernel as `ℓ²∫_0^∞ f_s ds`; it is supplied by the two
domination hypotheses:

* `hdom`: `∫_{(0,ε]}|f_s(u)| ≤ Cdom(1 + Σ_{n∈latBox}1/‖u−n‖)` for `ε ≤ 1`, `u` off-lattice,
  `|u i| ≤ 2` (the statement proved in `HeatPeriodIocDomination`);
* `hlt`: `latGreenSmooth ≥ −Mdom` off the lattice (the statement proved in
  `LatGreenSmoothBddBelow`), which turns each `1/‖u − n‖` into `4π(latGreen u + Mdom)` by
  periodicity (`latGreen_periodic`) and `latGreen = 1/(4π‖·‖) + latGreenSmooth`;
* for `s ≥ 1` the exponential bound `|f_s(u)| ≤ D e^{−4π²s}` (`abs_heatPeriod_sub_one_le_exp`
  in `LGFormAux`).

Hence `∫_{(0,∞)×cell²}|P P f_s| ≤ C[(∫_{cell}|P|)² + ∬|PP·K_♯|] < ∞` using **(B)**, which is
exactly `∬|PP·K_♯| < ∞` with `K_♯ = ℓ²latGreen(ℓ⁻¹·)`.

The prover must also handle that `u = ℓ⁻¹•(p₁−p₂)` is *off-lattice only a.e.* on
`cell ℓ ×ˢ cell ℓ`: the union of the finitely many sets `p₁ − p₂ = ℓ n` (`n : ℤ³`) is
Lebesgue-null in `ℝ³ × ℝ³`, and the pointwise bounds above are only asserted off the lattice.
Note `|(ℓ⁻¹•(p₁−p₂)) i| ≤ 1 ≤ 2` for `p₁, p₂ ∈ cell ℓ`, so the `|u i| ≤ 2` hypothesis of `hdom`
is met; and `∫` of a nonnegative function with infinite integral is `0` in Lean, so the
exceptional set causes no difficulty. -/
theorem LatGreenTripleIntegrable {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    {Cdom Mdom : ℝ}
    (hlt : ∀ u : EuclideanSpace ℝ (Fin 3),
      (∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) →
        -Mdom ≤ Work.BoseFixR.LatGreen.latGreenSmooth u)
    (hdom : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u : EuclideanSpace ℝ (Fin 3),
      (∀ i : Fin 3, |u i| ≤ 2) → (∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) →
        ∫ s in Set.Ioc 0 ε, |Work.BoseFixR.LatGreen.heatPeriod s u - 1|
          ≤ Cdom * (1 + ∑ n ∈ Work.BoseFixR.LatGreen.latBox,
              1 / ‖u - Work.BoseFixR.LatGreen.latVec n‖))
    (hB : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        |Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))|)
      (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)) :
    MeasureTheory.Integrable
      (fun q : ℝ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Work.BoseFixR.LatGreen.period W ℓ q.2.1 * Work.BoseFixR.LatGreen.period W ℓ q.2.2
          * (Work.BoseFixR.LatGreen.heatPeriod q.1 (ℓ⁻¹ • (q.2.1 - q.2.2)) - 1))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ))) := by
  classical
  -- the periodisation is integrable on the cell
  have hPint : MeasureTheory.IntegrableOn (period W ℓ) (Work.BoseFixR.cell ℓ) :=
    integrableOn_period hℓ hW hper
  have hPmeas : AEMeasurable (period W ℓ) (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)) :=
    hPint.1.aemeasurable
  -- the two factors of the product measure
  set μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)) :=
    MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ) with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) with hν
  have hρ : (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)
      : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
        = μ.prod μ :=
    (MeasureTheory.Measure.prod_restrict _ _).symm
  rw [hρ]
  set F : ℝ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) → ℝ :=
    (fun q => period W ℓ q.2.1 * period W ℓ q.2.2
      * (heatPeriod q.1 (ℓ⁻¹ • (q.2.1 - q.2.2)) - 1)) with hF
  have hCmeas : Measurable (fun q : ℝ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      heatPeriod q.1 (ℓ⁻¹ • (q.2.1 - q.2.2))) :=
    measurable_heatPeriod_pair.comp
      (Measurable.prodMk measurable_fst
        (((continuous_snd.fst.sub continuous_snd.snd).const_smul ℓ⁻¹).measurable))
  have hAESM : AEStronglyMeasurable F (ν.prod (μ.prod μ)) := by
    rw [hF]
    exact (((hPmeas.comp_fst.comp_snd).mul (hPmeas.comp_snd.comp_snd)).mul
      ((hCmeas.sub measurable_const).aemeasurable)).aestronglyMeasurable
  refine ⟨hAESM, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_norm]
  -- the finite constants
  have hf : AEMeasurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal |period W ℓ x|) μ := hPmeas.norm.ennreal_ofReal
  have hf2 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|) (μ.prod μ) :=
    (hf.comp_fst).mul (hf.comp_snd)
  set cP : ℝ≥0∞ := ∫⁻ x, (ENNReal.ofReal |period W ℓ x|) ∂μ with hcP
  set CB : ℝ≥0∞ := ∫⁻ p, (ENNReal.ofReal |period W ℓ p.1 * period W ℓ p.2
      * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (p.1 - p.2)))|) ∂(μ.prod μ) with hCB
  obtain ⟨B0, hB0nn, hB0⟩ := lintegral_Ioi_one_heatPeriod_sub_one
  set Z0 : ℝ≥0∞ := ENNReal.ofReal Cdom *
      (1 + (latBox.card : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * max Mdom 0))
      + ENNReal.ofReal B0 with hZ0
  set kA : ℝ≥0∞ := (latBox.card : ℝ≥0∞) * ENNReal.ofReal Cdom with hkA
  have hcP_lt : cP < ⊤ := by
    rw [hcP, hμ]
    have h := hPint.2
    rw [MeasureTheory.hasFiniteIntegral_iff_norm] at h
    simpa [Real.norm_eq_abs] using h
  have hCB_lt : CB < ⊤ := by
    rw [hCB]
    have hB' : MeasureTheory.Integrable (fun p :
        EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        |period W ℓ p.1 * period W ℓ p.2 * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (p.1 - p.2)))|)
        (μ.prod μ) := by
      rw [← hρ]
      exact hB
    have h := hB'.2
    rw [MeasureTheory.hasFiniteIntegral_iff_norm] at h
    simpa [Real.norm_eq_abs] using h
  have hZ0_lt : Z0 < ⊤ := by
    rw [hZ0]
    refine ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_, ENNReal.ofReal_lt_top⟩
    exact ENNReal.add_lt_top.mpr
      ⟨by simp, ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top⟩
  have hkA_lt : kA < ⊤ := by
    rw [hkA]
    exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
  -- measurability of the integrand appearing in Tonelli's theorem
  have hAEmF : AEMeasurable (fun q :
      ℝ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      ENNReal.ofReal |F q|) (ν.prod (μ.prod μ)) :=
    hAESM.norm.aemeasurable.ennreal_ofReal
  -- the a.e. statement that `p` lies in the cell and that `u` is off the lattice
  have hae_off : ∀ᵐ p ∂(μ.prod μ),
      ∀ n : Fin 3 → ℤ, ℓ⁻¹ • (p.1 - p.2) ≠ latVec n := by
    rw [← hρ]
    exact ae_offLattice_sub hℓ
  have hae_cell : ∀ᵐ p ∂(μ.prod μ),
      p.1 ∈ Work.BoseFixR.cell ℓ ∧ p.2 ∈ Work.BoseFixR.cell ℓ := by
    rw [← hρ]
    filter_upwards [MeasureTheory.ae_restrict_mem
      ((measurableSet_cell ℓ).prod (measurableSet_cell ℓ))] with p hp
    rwa [Work.BoseFixR.cell_eq_boxL ℓ] at hp
  -- the pointwise (in `p`) bound of the `s`-integral
  have hbound : ∀ᵐ p ∂(μ.prod μ),
      (∫⁻ s, (ENNReal.ofReal |F (s, p)|) ∂ν)
        ≤ ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2| * Z0
          + kA * (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|
              * ENNReal.ofReal (4 * Real.pi * |latGreen (ℓ⁻¹ • (p.1 - p.2))|)) := by
    filter_upwards [hae_off, hae_cell] with p hoff hcell
    simp only [hF]
    have h2 : ∀ i : Fin 3, |(ℓ⁻¹ • (p.1 - p.2)) i| ≤ 2 := by
      intro i
      have hb1 : |p.1 i| ≤ ℓ / 2 := hcell.1 i
      have hb2 : |p.2 i| ≤ ℓ / 2 := hcell.2 i
      have hb3 : |(p.1 - p.2) i| ≤ ℓ := by
        simp only [Pi.sub_apply, WithLp.ofLp_sub]
        calc |p.1 i - p.2 i| ≤ |p.1 i| + |p.2 i| := by
              simpa [sub_eq_add_neg, abs_neg] using abs_add_le (p.1 i) (-(p.2 i))
          _ ≤ ℓ / 2 + ℓ / 2 := add_le_add hb1 hb2
          _ = ℓ := by ring
      rw [show (ℓ⁻¹ • (p.1 - p.2)) i = ℓ⁻¹ * (p.1 - p.2) i by simp, abs_mul,
        abs_of_pos (inv_pos.mpr hℓ)]
      have := mul_le_mul_of_nonneg_left hb3 (inv_nonneg.mpr hℓ.le)
      rw [inv_mul_cancel₀ (ne_of_gt hℓ)] at this
      linarith
    have hfac : (∫⁻ s, (ENNReal.ofReal |period W ℓ p.1 * period W ℓ p.2
          * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1)|) ∂ν)
        = (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|)
          * (∫⁻ s, (ENNReal.ofReal |heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1|) ∂ν) := by
      have hpw : ∀ s : ℝ, ENNReal.ofReal |period W ℓ p.1 * period W ℓ p.2
            * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1)|
          = (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|)
            * ENNReal.ofReal |heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1| := by
        intro s
        rw [abs_mul, abs_mul, ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (abs_nonneg _)),
          ENNReal.ofReal_mul (abs_nonneg _)]
      rw [MeasureTheory.lintegral_congr hpw,
        MeasureTheory.lintegral_const_mul' _
          (fun s : ℝ => ENNReal.ofReal |heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1|)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    rw [hfac]
    refine le_trans (mul_le_mul_of_nonneg_left
      (lintegral_heatPeriod_sub_one_le hdom hlt hB0 hoff h2) zero_le) (le_of_eq ?_)
    rw [hZ0, hkA]
    ring
  -- the `p`-integral of `|P p₁| |P p₂|`
  have hpint_eq : (∫⁻ p, (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|)
        ∂(μ.prod μ)) = cP * cP := by
    rw [hcP, MeasureTheory.lintegral_prod
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal |period W ℓ z.1| * ENNReal.ofReal |period W ℓ z.2|)
      ((hf.comp_fst).mul (hf.comp_snd))]
    exact MeasureTheory.lintegral_lintegral_mul hf hf
  -- the `p`-integral of the bound
  have hpint : (∫⁻ p, (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2| * Z0
        + kA * (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|
            * ENNReal.ofReal (4 * Real.pi * |latGreen (ℓ⁻¹ • (p.1 - p.2))|)))
        ∂(μ.prod μ))
      ≤ (cP * cP) * Z0 + kA * (ENNReal.ofReal (4 * Real.pi / ℓ ^ 2) * CB) := by
    have hAEm1 : AEMeasurable (fun p :
        EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2| * Z0) (μ.prod μ) :=
      hf2.mul aemeasurable_const
    have h4 : (∫⁻ p, (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|
          * ENNReal.ofReal (4 * Real.pi * |latGreen (ℓ⁻¹ • (p.1 - p.2))|)) ∂(μ.prod μ))
        = ENNReal.ofReal (4 * Real.pi / ℓ ^ 2) * CB := by
      rw [hCB]
      rw [MeasureTheory.lintegral_congr (fun p => ofReal_fac hℓ W p)]
      exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have h1 : (∫⁻ p, (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2| * Z0)
          ∂(μ.prod μ))
        = (∫⁻ p, (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|)
            ∂(μ.prod μ)) * Z0 :=
      MeasureTheory.lintegral_mul_const' Z0 _ (ne_of_lt hZ0_lt)
    have h2 : (∫⁻ p, (kA * (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|
          * ENNReal.ofReal (4 * Real.pi * |latGreen (ℓ⁻¹ • (p.1 - p.2))|))) ∂(μ.prod μ))
        = kA * (∫⁻ p, (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|
          * ENNReal.ofReal (4 * Real.pi * |latGreen (ℓ⁻¹ • (p.1 - p.2))|)) ∂(μ.prod μ)) :=
      MeasureTheory.lintegral_const_mul' kA _ (ne_of_lt hkA_lt)
    rw [MeasureTheory.lintegral_add_left' hAEm1, h1, hpint_eq, h2, h4]
  -- conclude
  have hmain : (∫⁻ q, (ENNReal.ofReal ‖F q‖) ∂(ν.prod (μ.prod μ)))
      ≤ (cP * cP) * Z0 + kA * (ENNReal.ofReal (4 * Real.pi / ℓ ^ 2) * CB) := by
    calc ∫⁻ q, (ENNReal.ofReal ‖F q‖) ∂(ν.prod (μ.prod μ))
        = ∫⁻ q, (ENNReal.ofReal |F q|) ∂(ν.prod (μ.prod μ)) := by
          apply MeasureTheory.lintegral_congr
          intro q
          rw [Real.norm_eq_abs]
      _ = ∫⁻ s, ∫⁻ p, (ENNReal.ofReal |F (s, p)|) ∂(μ.prod μ) ∂ν :=
          MeasureTheory.lintegral_prod _ hAEmF
      _ = ∫⁻ p, ∫⁻ s, (ENNReal.ofReal |F (s, p)|) ∂ν ∂(μ.prod μ) :=
          MeasureTheory.lintegral_lintegral_swap hAEmF
      _ ≤ ∫⁻ p, (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2| * Z0
            + kA * (ENNReal.ofReal |period W ℓ p.1| * ENNReal.ofReal |period W ℓ p.2|
                * ENNReal.ofReal (4 * Real.pi * |latGreen (ℓ⁻¹ • (p.1 - p.2))|)))
          ∂(μ.prod μ) :=
          MeasureTheory.lintegral_mono_ae hbound
      _ ≤ (cP * cP) * Z0 + kA * (ENNReal.ofReal (4 * Real.pi / ℓ ^ 2) * CB) := hpint
  have hfin : (cP * cP) * Z0 + kA * (ENNReal.ofReal (4 * Real.pi / ℓ ^ 2) * CB) < ⊤ := by
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top hcP_lt hcP_lt) hZ0_lt,
      ENNReal.mul_lt_top hkA_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCB_lt)⟩
  exact lt_of_le_of_lt hmain hfin

end Work.BoseFixR.LatGreen
