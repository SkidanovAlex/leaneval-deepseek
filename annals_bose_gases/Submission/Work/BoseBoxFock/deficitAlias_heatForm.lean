import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PhiTaylorQuant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.deficitAlias_heatForm` — the heat form of the aliasing deficit

For `ℓ > 0` and `g` smooth with `tsupport g ⊆ ball 0 (ℓ/2)` (so that the box frame identity
`frame_lattice_ball` applies, i.e. the lattice mass equals the continuum mass), the aliasing
deficit `3·S₁ − 2·R₁` (`S₁ = Σ_n ℓ⁻³‖k_n‖‖ĝ(k_n)‖²`, `R₁ = (2π)⁻³∫‖p‖‖ĝ(p)‖²`) has the **heat
representation**

`3S₁ − 2R₁ = (2√π)⁻¹ ∫₀^∞ t^{-3/2} ( 2·E(t) + R₀ − 3·Λ(t) ) dt`,

with `Λ(t) = latHeat ℓ t g`, `E(t) = contHeat g t` and `R₀ = (2π)⁻³∫‖ĝ‖²` (equivalently
`R₀ = Σ_n ℓ⁻³‖ĝ(k_n)‖²` by the frame identity).

This is a *formal* consequence of the two already-proved heat subordinations

* `lattice_heatSubordination` : `S₁ = (2√π)⁻¹∫₀^∞ t^{-3/2}(S₀ − Λ(t))dt`,
* `continuum_heatSubordination_v2` : `R₁ = (2√π)⁻¹∫₀^∞ t^{-3/2}(R₀ − E(t))dt`

together with the frame identity `S₀ = R₀` (`frame_lattice_ball`): indeed
`3(R₀ − Λ) − 2(R₀ − E) = R₀ + 2E − 3Λ`.

The only inputs not literally in those two theorems are the **integrability** of the two
nonnegative heat-deficit integrands `t^{-3/2}(S₀ − Λ(t))` and `t^{-3/2}(R₀ − E(t))` on `(0,∞)`
(needed to split the integral linearly), and the rewriting of the `Real.exp (-t * x)` spelling
used inside the two subordination statements into the `Real.exp (-(t * x))` spelling of the
definitions `latHeat`/`contHeat`.  Both integrability statements are proved here
(`integrableOn_heatDeficit_lat`, `integrableOn_heatDeficit_cont`): they are self-contained
`IntegrableOn` facts obtained by dominating the deficit by the explicit integrable profiles
`t ↦ (t S₂)·t^{-3/2}` on `(0,1]` and `t ↦ S₀·t^{-3/2}` on `(1,∞)` (lattice side; `S₂` the second
moment), resp. `t ↦ R₂·t^{-1/2}` and `t ↦ R₀·t^{-3/2}` (continuum side; `R₂ = (2π)⁻³∫‖p‖²‖ĝ‖²`).
-/

noncomputable section

open MeasureTheory Filter Metric

open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The two spellings of the heat contents -/

/-- `latHeat` in the `Real.exp (-t * ‖k‖²)`-spelling of `lattice_heatSubordination`. -/
lemma latHeat_eq_alt (ℓ : ℝ) (t : ℝ) (g : E3 → ℂ) :
    latHeat ℓ t g = ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Real.exp (-t * ‖kmomInt ℓ n‖ ^ 2)
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
  simp only [latHeat]
  exact tsum_congr (fun n => by rw [neg_mul])

/-- `contHeat` in the `Real.exp (-t * ‖p‖²)`-spelling of
`continuum_heatSubordination_v2`. -/
lemma contHeat_eq_alt (g : E3 → ℂ) (t : ℝ) :
    contHeat g t = ((2 * Real.pi) ^ 3)⁻¹ *
      ∫ p : E3, Real.exp (-t * ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
  simp only [contHeat]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall (fun p => by
    beta_reduce
    rw [neg_mul]))

/-! ## 2. Integrability of the lattice heat deficit -/

/-- **Integrability of the lattice heat deficit.**  With `a_n = ℓ⁻³‖ĝ(k_n)‖² ≥ 0` and
`Λ(t) = Σ_n a_n e^{-t‖k_n‖²}`, the deficit `t^{-3/2}(S₀ − Λ(t)) = t^{-3/2}Σ_n a_n(1 − e^{-t‖k_n‖²})`
is `≥ 0` and dominated by `t^{-1/2}S₂` on `(0,1]` (`1 − e^{-y} ≤ y`) and by `t^{-3/2}S₀` on
`(1,∞)`, both integrable; `Σ_n a_n` and `Σ_n a_n‖k_n‖²` converge by
`summable_lattice_kinFT_weight`. -/
lemma integrableOn_heatDeficit_lat {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun t : ℝ => t ^ (-(3/2) : ℝ) *
      ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        - latHeat ℓ t g)) (Set.Ioi 0) volume := by
  set a : (Fin 3 → ℤ) → ℝ := fun n => (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 with ha
  set x : (Fin 3 → ℤ) → ℝ := fun n => ‖kmomInt ℓ n‖ ^ 2 with hx
  have ha0 : ∀ n, 0 ≤ a n := fun n => by rw [ha]; positivity
  have haS : Summable a := by
    simpa [ha] using summable_lattice_kinFT_weight hℓ hg hgc 0
  have hx0 : ∀ n, 0 ≤ x n := fun n => by rw [hx]; positivity
  have hx2 : Summable (fun n => a n * x n) := by
    have h := summable_lattice_kinFT_weight hℓ hg hgc 2
    refine h.congr (fun n => ?_)
    simp only [ha, hx]
    ring
  set S : ℝ := ∑' n, a n with hS
  have hΛeq : ∀ t : ℝ, latHeat ℓ t g = ∑' n : Fin 3 → ℤ, a n * Real.exp (-(t * x n)) := by
    intro t
    simp only [latHeat, ha, hx]
    exact tsum_congr (fun n => by ring)
  have hpt : ∀ t : ℝ, 0 ≤ t → S - latHeat ℓ t g
      = ∑' n, a n * (1 - Real.exp (-(t * x n))) := by
    intro t ht
    have hheat : Summable (fun n => a n * Real.exp (-(t * x n))) := by
      refine Summable.of_nonneg_of_le (fun n => mul_nonneg (ha0 n) (Real.exp_nonneg _)) (fun n => ?_) haS
      exact mul_le_of_le_one_right (ha0 n) (Real.exp_le_one_iff.mpr (by nlinarith [ht, hx0 n]))
    rw [hS, hΛeq t, ← Summable.tsum_sub haS hheat]
    exact tsum_congr (fun n => by ring)
  have hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ S - latHeat ℓ t g := by
    intro t ht
    rw [hpt t ht]
    refine tsum_nonneg (fun n => mul_nonneg (ha0 n) (sub_nonneg.mpr ?_))
    rw [Real.exp_le_one_iff]; nlinarith [ht, hx0 n]
  have hbound : ∀ t : ℝ, 0 < t → S - latHeat ℓ t g ≤ t * (∑' n, a n * x n) := by
    intro t ht
    rw [hpt t ht.le]
    have hL : Summable (fun n => a n * (1 - Real.exp (-(t * x n)))) := by
      refine Summable.of_nonneg_of_le (fun n => mul_nonneg (ha0 n) (sub_nonneg.mpr ?_)) (fun n => ?_) haS
      · rw [Real.exp_le_one_iff]; nlinarith [ht.le, hx0 n]
      · exact mul_le_of_le_one_right (ha0 n) (by linarith [Real.exp_pos (-(t * x n))])
    have hR : Summable (fun n => t * (a n * x n)) := hx2.mul_left t
    have hle := Summable.tsum_le_tsum (f := fun n => a n * (1 - Real.exp (-(t * x n))))
      (g := fun n => t * (a n * x n)) (fun n => ?_) hL hR
    · rwa [Summable.tsum_mul_left t hx2] at hle
    · have hxe : 0 ≤ t * x n := mul_nonneg ht.le (hx0 n)
      have h1 : 1 - Real.exp (-(t * x n)) ≤ t * x n := by
        have := Real.one_sub_le_exp_neg (t * x n); linarith
      calc a n * (1 - Real.exp (-(t * x n))) ≤ a n * (t * x n) := mul_le_mul_of_nonneg_left h1 (ha0 n)
        _ = t * (a n * x n) := by ring
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (-(3/2) : ℝ) * (S - latHeat ℓ t g))
      (volume.restrict (Set.Ioi 0)) := by
    have hpow : AEStronglyMeasurable (fun t : ℝ => t ^ (-(3/2) : ℝ)) (volume.restrict (Set.Ioi 0)) :=
      (continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt hy))).aestronglyMeasurable measurableSet_Ioi
    have hΛ : AEStronglyMeasurable (fun t : ℝ => latHeat ℓ t g) (volume.restrict (Set.Ioi 0)) := by
      have hfun : (fun t : ℝ => latHeat ℓ t g) = fun t : ℝ => ∑' n, a n * Real.exp (-(t * x n)) :=
        funext hΛeq
      rw [hfun]
      refine AEStronglyMeasurable.tsum (fun n => ?_)
      exact (by fun_prop : Continuous (fun t : ℝ => a n * Real.exp (-(t * x n)))).aestronglyMeasurable
    exact hpow.mul (aestronglyMeasurable_const.sub hΛ)
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (g := fun t : ℝ => (∑' n, a n * x n) * t ^ (-(1:ℝ)/2)) ?_ ?_ ?_
    · have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1:ℝ)/2) (by norm_num)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
      exact h.const_mul _
    · exact hmeas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have h1 : 0 ≤ S - latHeat ℓ t g := hnn t ht0.le
      have h2 : S - latHeat ℓ t g ≤ t * (∑' n, a n * x n) := hbound t ht0
      have h3 : 0 ≤ t ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg ht0.le _
      rw [Real.norm_of_nonneg (mul_nonneg h3 h1)]
      calc t ^ (-(3 / 2) : ℝ) * (S - latHeat ℓ t g) ≤ t ^ (-(3 / 2) : ℝ) * (t * (∑' n, a n * x n)) :=
            mul_le_mul_of_nonneg_left h2 h3
        _ = (∑' n, a n * x n) * t ^ (-(1:ℝ)/2) := by
            nth_rewrite 2 [← Real.rpow_one t]
            rw [← mul_assoc, ← Real.rpow_add ht0]
            norm_num
            ring
  · refine Integrable.mono' (g := fun t : ℝ => S * t ^ (-(3/2) : ℝ)) ?_ ?_ ?_
    · have hbase : IntegrableOn (fun t : ℝ => t ^ (-(3/2) : ℝ)) (Set.Ioi 1) volume :=
        (integrableOn_Ioi_rpow_iff (s := (-(3/2) : ℝ)) (t := 1) (by norm_num)).mpr (by norm_num)
      exact hbase.const_mul S
    · exact hmeas.mono_measure (Measure.restrict_mono (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1)) le_rfl)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      have h1 : 0 ≤ S - latHeat ℓ t g := hnn t ht0.le
      have h2 : S - latHeat ℓ t g ≤ S := by
        rw [hpt t ht0.le, hS]
        refine Summable.tsum_le_tsum (f := fun n => a n * (1 - Real.exp (-(t * x n)))) (g := a)
          (fun n => ?_) ?_ haS
        · exact mul_le_of_le_one_right (ha0 n) (by linarith [Real.exp_pos (-(t * x n))])
        · refine Summable.of_nonneg_of_le (fun n => mul_nonneg (ha0 n) (sub_nonneg.mpr ?_)) (fun n => ?_) haS
          · rw [Real.exp_le_one_iff]; nlinarith [ht0.le, hx0 n]
          · exact mul_le_of_le_one_right (ha0 n) (by linarith [Real.exp_pos (-(t * x n))])
      have h3 : 0 ≤ t ^ (-(3/2) : ℝ) := Real.rpow_nonneg ht0.le _
      rw [Real.norm_of_nonneg (mul_nonneg h3 h1)]
      calc t ^ (-(3/2) : ℝ) * (S - latHeat ℓ t g) ≤ t ^ (-(3/2) : ℝ) * S := mul_le_mul_of_nonneg_left h2 h3
        _ = S * t ^ (-(3/2) : ℝ) := by ring

/-! ## 3. Integrability of the continuum heat deficit -/

/-- **Integrability of the continuum heat deficit.**  With `F = ‖ĝ‖²` integrable, second moment
integrable, `R₀ = (2π)⁻³∫F`, `R(t) = (2π)⁻³∫e^{-t‖p‖²}F`, the deficit `t^{-3/2}(R₀ − R(t))` is
`≥ 0` and dominated by `t^{-1/2}R₂` on `(0,1]` (`heatLossContinuum_le`) and by `t^{-3/2}R₀` on
`(1,∞)`. -/
lemma integrableOn_heatDeficit_cont {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun t : ℝ => t ^ (-(3/2) : ℝ) *
      ((((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2))
        - contHeat g t)) (Set.Ioi 0) volume := by
  set F : EuclideanSpace ℝ (Fin 3) → ℝ := fun p => ‖Submission.BoseGases.kinFT g p‖ ^ 2 with hF
  have hF0 : ∀ p, 0 ≤ F p := fun p => by rw [hF]; positivity
  have hFint : Integrable F := by
    simpa [hF] using SqrtKin.kinFT_sq_integrable (g := g) hg hgc
  have hW2 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 * F p) := by
    simpa [hF] using SqrtKin.kinFT_weight2_integrable (g := g) hg hgc
  set R0 : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, F p with hR0
  set R2 : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, ‖p‖ ^ 2 * F p with hR2
  set Rt : ℝ → ℝ := contHeat g with hRt
  have hRt_eq : ∀ t : ℝ, Rt t = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, Real.exp (-(t * ‖p‖ ^ 2)) * F p := by
    intro t; rw [hRt]; unfold contHeat; simp only [hF]
  have hsub : ∀ t : ℝ, 0 ≤ t → R0 - Rt t
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, (1 - Real.exp (-(t * ‖p‖ ^ 2))) * F p := by
    intro t ht
    have hB : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Real.exp (-(t * ‖p‖ ^ 2)) * F p) := by
      refine Integrable.mono' hFint (((Real.continuous_exp.comp ?_).aestronglyMeasurable).mul hFint.aestronglyMeasurable) ?_
      · fun_prop
      · filter_upwards with p
        have h1 : Real.exp (-(t * ‖p‖ ^ 2)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [ht, sq_nonneg ‖p‖]
        rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hF0 p))]
        exact mul_le_of_le_one_left (hF0 p) h1
    rw [hRt_eq t, hR0, ← mul_sub, ← integral_sub hFint hB]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    ring
  have hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ R0 - Rt t := by
    intro t ht
    rw [hsub t ht]
    refine mul_nonneg (by positivity) (integral_nonneg_of_ae (Filter.Eventually.of_forall (fun p => ?_)))
    exact mul_nonneg (sub_nonneg.mpr (by rw [Real.exp_le_one_iff]; nlinarith [ht, sq_nonneg ‖p‖])) (hF0 p)
  have hbound : ∀ t : ℝ, 0 < t → R0 - Rt t ≤ t * R2 := by
    intro t ht
    rw [hsub t ht.le, hR2]
    have h := heatLossContinuum_le (f := F) hF0 hW2 ht
    calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, (1 - Real.exp (-(t * ‖p‖ ^ 2))) * F p
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (t * ∫ p, ‖p‖ ^ 2 * F p) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = t * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p, ‖p‖ ^ 2 * F p) := by ring
  have hRtnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ Rt t := by
    intro t ht
    rw [hRt_eq t]
    refine mul_nonneg (by positivity) (integral_nonneg_of_ae (Filter.Eventually.of_forall (fun p => ?_)))
    exact mul_nonneg (Real.exp_nonneg _) (hF0 p)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (-(3/2) : ℝ) * (R0 - Rt t))
      (volume.restrict (Set.Ioi 0)) := by
    have hpow : AEStronglyMeasurable (fun t : ℝ => t ^ (-(3/2) : ℝ)) (volume.restrict (Set.Ioi 0)) :=
      (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))).aestronglyMeasurable measurableSet_Ioi
    have hInt : AEStronglyMeasurable (fun t : ℝ => ∫ p : EuclideanSpace ℝ (Fin 3),
        Real.exp (-(t * ‖p‖ ^ 2)) * F p) (volume.restrict (Set.Ioi 0)) := by
      have hjoint : AEStronglyMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
          Real.exp (-(z.1 * ‖z.2‖ ^ 2)) * F z.2) ((volume.restrict (Set.Ioi 0)).prod volume) := by
        refine ((Real.continuous_exp.comp ?_).aestronglyMeasurable).mul hFint.aestronglyMeasurable.comp_snd
        fun_prop
      exact AEStronglyMeasurable.integral_prod_right' hjoint
    have hRt' : AEStronglyMeasurable (fun t : ℝ => Rt t) (volume.restrict (Set.Ioi 0)) := by
      have : (fun t : ℝ => Rt t) = fun t : ℝ => ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p, Real.exp (-(t * ‖p‖ ^ 2)) * F p := funext hRt_eq
      rw [this]
      exact hInt.const_mul _
    exact hpow.mul (aestronglyMeasurable_const.sub hRt')
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (g := fun t : ℝ => R2 * t ^ (-(1:ℝ)/2)) ?_ ?_ ?_
    · have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1:ℝ)/2) (by norm_num)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
      exact h.const_mul R2
    · exact hmeas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have h1 : 0 ≤ R0 - Rt t := hnn t ht0.le
      have h2 : R0 - Rt t ≤ t * R2 := hbound t ht0
      have h3 : 0 ≤ t ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg ht0.le _
      rw [Real.norm_of_nonneg (mul_nonneg h3 h1)]
      calc t ^ (-(3 / 2) : ℝ) * (R0 - Rt t) ≤ t ^ (-(3 / 2) : ℝ) * (t * R2) := mul_le_mul_of_nonneg_left h2 h3
        _ = R2 * t ^ (-(1:ℝ)/2) := by
            nth_rewrite 2 [← Real.rpow_one t]
            rw [← mul_assoc, ← Real.rpow_add ht0]
            norm_num
            ring
  · refine Integrable.mono' (g := fun t : ℝ => R0 * t ^ (-(3/2) : ℝ)) ?_ ?_ ?_
    · have hbase : IntegrableOn (fun t : ℝ => t ^ (-(3/2) : ℝ)) (Set.Ioi 1) volume :=
        (integrableOn_Ioi_rpow_iff (s := (-(3/2) : ℝ)) (t := 1) (by norm_num)).mpr (by norm_num)
      exact hbase.const_mul R0
    · exact hmeas.mono_measure (Measure.restrict_mono (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1)) le_rfl)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      have h1 : 0 ≤ R0 - Rt t := hnn t ht0.le
      have h2 : R0 - Rt t ≤ R0 := by have := hRtnn t ht0.le; linarith
      have h3 : 0 ≤ t ^ (-(3/2) : ℝ) := Real.rpow_nonneg ht0.le _
      rw [Real.norm_of_nonneg (mul_nonneg h3 h1)]
      calc t ^ (-(3/2) : ℝ) * (R0 - Rt t) ≤ t ^ (-(3/2) : ℝ) * R0 := mul_le_mul_of_nonneg_left h2 h3
        _ = R0 * t ^ (-(3/2) : ℝ) := by ring

/-! ## 4. The pointwise identity -/

/-- The pointwise algebraic identity behind the heat form: with `S₀ = R₀` (the frame identity),
`R₀ + 2E(t) − 3Λ(t) = 3(R₀ − Λ(t)) − 2(R₀ − E(t))`, multiplied by `t^{-3/2}`. -/
lemma heatForm_pointwise {ℓ : ℝ} {g : E3 → ℂ}
    (hframe : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2) (t : ℝ) :
    t ^ (-(3/2) : ℝ) * (2 * contHeat g t + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        - 3 * latHeat ℓ t g)
      = 3 * (t ^ (-(3/2) : ℝ) * ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
          - latHeat ℓ t g))
        - 2 * (t ^ (-(3/2) : ℝ) * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2)
          - contHeat g t)) := by
  rw [← hframe]
  ring

/-! ## 5. The target -/

theorem deficitAlias_heatForm {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ/2)) :
    (3 : ℝ) * (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      - 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      = (2 * Real.sqrt Real.pi)⁻¹ * ∫ t in Set.Ioi 0, t ^ (-(3/2) : ℝ) *
          (2 * Work.BoseBoxFock.contHeat g t
            + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
                ‖Submission.BoseGases.kinFT g p‖ ^ 2)
            - 3 * Work.BoseBoxFock.latHeat ℓ t g) := by
  have hgc : HasCompactSupport g := by
    rw [HasCompactSupport, Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_tsupport g, Metric.isBounded_ball.subset hgsupp⟩
  have hframe := frame_lattice_ball hℓ hg hgc (hgsupp.trans (ball_subset_corpusBox_boxL hℓ))
  have hlat := lattice_heatSubordination hℓ hg hgsupp
  have hcont := continuum_heatSubordination_v2 hℓ hg hgsupp
  have hu := integrableOn_heatDeficit_lat hℓ hg hgc
  have hv := integrableOn_heatDeficit_cont hg hgc
  -- the two heat subordinations, rewritten into the exp-spelling of the definitions
  have hlat' : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      = (2 * Real.sqrt Real.pi)⁻¹ * ∫ t in Set.Ioi 0, t ^ (-(3/2) : ℝ) *
          ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
            - latHeat ℓ t g) := by
    rw [hlat]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show (-3/2 : ℝ) = -(3/2) from by norm_num, latHeat_eq_alt ℓ t g]
  have hcont' : ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2
      = (2 * Real.sqrt Real.pi)⁻¹ * ∫ t in Set.Ioi 0, t ^ (-(3/2) : ℝ) *
          ((((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2))
            - contHeat g t) := by
    rw [hcont]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show (-3/2 : ℝ) = -(3/2) from by norm_num, contHeat_eq_alt g t]
  -- linearity of the integral over the two (integrable) heat deficits
  have hI : ∫ t in Set.Ioi 0, t ^ (-(3/2) : ℝ) *
        (2 * contHeat g t + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2)
          - 3 * latHeat ℓ t g)
      = 3 * (∫ t in Set.Ioi 0, t ^ (-(3/2) : ℝ) *
          ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
            - latHeat ℓ t g))
        - 2 * (∫ t in Set.Ioi 0, t ^ (-(3/2) : ℝ) *
          ((((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2))
            - contHeat g t)) := by
    rw [show (fun t : ℝ => t ^ (-(3/2) : ℝ) *
          (2 * contHeat g t + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2)
            - 3 * latHeat ℓ t g))
        = (fun t : ℝ => 3 * (t ^ (-(3/2) : ℝ) *
            ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
              - latHeat ℓ t g))
          - 2 * (t ^ (-(3/2) : ℝ) *
            ((((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2))
              - contHeat g t)))
        from funext (heatForm_pointwise hframe)]
    rw [integral_sub (hu.const_mul 3) (hv.const_mul 2), integral_const_mul, integral_const_mul]
  calc 3 * (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        - 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      = 3 * ((2 * Real.sqrt Real.pi)⁻¹ * ∫ t in Set.Ioi 0, t ^ (-(3/2) : ℝ) *
            ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
              - latHeat ℓ t g))
        - 2 * ((2 * Real.sqrt Real.pi)⁻¹ * ∫ t in Set.Ioi 0, t ^ (-(3/2) : ℝ) *
            ((((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2))
              - contHeat g t)) := by
        rw [hlat', hcont']
    _ = (2 * Real.sqrt Real.pi)⁻¹ * ∫ t in Set.Ioi 0, t ^ (-(3/2) : ℝ) *
          (2 * contHeat g t + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2)
            - 3 * latHeat ℓ t g) := by
        rw [hI]; ring

end Work.BoseBoxFock
