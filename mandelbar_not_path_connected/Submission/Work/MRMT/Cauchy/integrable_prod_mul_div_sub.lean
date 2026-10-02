import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter Metric
open scoped ENNReal Topology

namespace Work.MRMT.Cauchy

/-- **The `lintegral` of `z ↦ ‖z‖⁻¹` over a ball centred at the origin.**

For every real `s`, `∫⁻ z in ball(0,s), ofReal(‖z‖⁻¹) = ofReal(2πs)` (the point `z = 0`, where
Lean's `‖z‖⁻¹ = 0`, is negligible; for `s ≤ 0` both sides are `0`).  Proved by the polar-coordinate
substitution `Complex.lintegral_comp_polarCoord_symm`. -/
theorem lintegral_ofReal_norm_inv_ball_aux (s : ℝ) :
    ∫⁻ z in Metric.ball (0 : ℂ) s, ENNReal.ofReal (‖z‖⁻¹) =
      ENNReal.ofReal (2 * Real.pi * s) := by
  have hpoint : ∀ p : ℝ × ℝ, p ∈ Complex.polarCoord.target →
      ENNReal.ofReal p.1 •
          (Metric.ball (0:ℂ) s).indicator (fun z => ENNReal.ofReal (‖z‖⁻¹))
            (Complex.polarCoord.symm p)
        = (if p.1 < s then (1:ℝ≥0∞) else 0) := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    rw [Set.indicator]
    simp only [Metric.mem_ball, dist_zero_right, hn]
    split_ifs with h
    · rw [smul_eq_mul, ← ENNReal.ofReal_mul hp1.le, mul_inv_cancel₀ hp1.ne', ENNReal.ofReal_one]
    · rw [smul_eq_mul, mul_zero]
  have hsecond : ∫⁻ p in Complex.polarCoord.target, (if p.1 < s then (1:ℝ≥0∞) else 0)
      = ENNReal.ofReal (2 * Real.pi * s) := by
    have hS : MeasurableSet (Set.Ioo (0:ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
      measurableSet_Ioo.prod measurableSet_Ioo
    have hfun : (Complex.polarCoord.target.indicator
          (fun p : ℝ×ℝ => if p.1 < s then (1:ℝ≥0∞) else 0))
        = (Set.Ioo (0:ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator (fun _ => (1:ℝ≥0∞)) := by
      funext p
      rw [Set.indicator, Set.indicator, Complex.polarCoord_target]
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      split_ifs <;> simp_all
    rw [← MeasureTheory.lintegral_indicator Complex.polarCoord.open_target.measurableSet, hfun,
        MeasureTheory.lintegral_indicator hS, MeasureTheory.setLIntegral_const]
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioo,
      Real.volume_Ioo]
    simp only [sub_zero, one_mul]
    rw [show Real.pi - -Real.pi = 2 * Real.pi by ring,
        ← ENNReal.ofReal_mul' (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    congr 1
    ring
  rw [← MeasureTheory.lintegral_indicator Metric.isOpen_ball.measurableSet,
      ← Complex.lintegral_comp_polarCoord_symm
        (f := (Metric.ball (0:ℂ) s).indicator (fun z => ENNReal.ofReal (‖z‖⁻¹)))]
  exact (MeasureTheory.setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
    hpoint).trans hsecond

/-- **Uniform bound for `‖w‖⁻¹` over a ball of radius `R`, any centre.**

For `R ≥ 0` and every `c : ℂ`, `∫⁻ w in ball(c,R), ofReal(‖w‖⁻¹) ≤ ofReal(8πR)`.  (The sharp
bound is `2πR` when `c = 0`; for `‖c‖ ≤ 3R` one uses `ball c R ⊆ ball 0 (4R)`, and for
`3R < ‖c‖` one bounds `‖w‖⁻¹ ≤ 1/(2R)` pointwise on `ball c R`.) -/
theorem lintegral_ofReal_norm_inv_ball_uniform_aux (R : ℝ) (hR : 0 ≤ R) (c : ℂ) :
    ∫⁻ w in Metric.ball c R, ENNReal.ofReal (‖w‖⁻¹) ≤ ENNReal.ofReal (8 * Real.pi * R) := by
  by_cases hcase : ‖c‖ ≤ 3 * R
  · have hsub : Metric.ball c R ⊆ Metric.ball (0:ℂ) (4*R) := by
      intro w hw
      rw [Metric.mem_ball, dist_zero_right]
      rw [Metric.mem_ball, dist_eq_norm] at hw
      calc ‖w‖ = ‖(w - c) + c‖ := by ring_nf
        _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
        _ < R + 3*R := by linarith
        _ = 4*R := by ring
    calc ∫⁻ w in Metric.ball c R, ENNReal.ofReal (‖w‖⁻¹)
        ≤ ∫⁻ w in Metric.ball (0:ℂ) (4*R), ENNReal.ofReal (‖w‖⁻¹) :=
          lintegral_mono_set hsub
      _ = ENNReal.ofReal (2 * Real.pi * (4*R)) := lintegral_ofReal_norm_inv_ball_aux (4*R)
      _ = ENNReal.ofReal (8 * Real.pi * R) := by congr 1; ring
  · rw [not_le] at hcase
    by_cases hR0 : R = 0
    · subst hR0
      simp
    · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
      have hpt : ∀ w ∈ Metric.ball c R,
          ENNReal.ofReal (‖w‖⁻¹) ≤ ENNReal.ofReal (1/(2*R)) := by
        intro w hw
        rw [Metric.mem_ball, dist_eq_norm] at hw
        have hn : ‖w‖ > 2*R := by
          have h1 : ‖c‖ ≤ ‖w - c‖ + ‖w‖ := by
            calc ‖c‖ = ‖(c - w) + w‖ := by ring_nf
              _ ≤ ‖c - w‖ + ‖w‖ := norm_add_le _ _
              _ = ‖w - c‖ + ‖w‖ := by rw [norm_sub_rev]
          linarith
        apply ENNReal.ofReal_le_ofReal
        rw [one_div]
        exact inv_anti₀ (by linarith) (le_of_lt hn)
      calc ∫⁻ w in Metric.ball c R, ENNReal.ofReal (‖w‖⁻¹)
          ≤ ∫⁻ w in Metric.ball c R, ENNReal.ofReal (1/(2*R)) :=
            setLIntegral_mono measurable_const hpt
        _ = ENNReal.ofReal (1/(2*R)) * volume (Metric.ball c R) :=
            MeasureTheory.setLIntegral_const _ _
        _ = ENNReal.ofReal (1/(2*R)) *
              (ENNReal.ofReal R ^ 2 * ENNReal.ofReal Real.pi) := by
            rw [Complex.volume_ball, ← ENNReal.ofReal_coe_nnreal (p := NNReal.pi),
              NNReal.coe_real_pi]
        _ ≤ ENNReal.ofReal (8 * Real.pi * R) := by
            rw [← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ R^2),
              ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/(2*R))]
            apply ENNReal.ofReal_le_ofReal
            have h2 : 2*R ≠ 0 := by positivity
            have heq : 1/(2*R) * (R^2 * Real.pi) = R/2 * Real.pi := by
              field_simp
            rw [heq]
            nlinarith [Real.pi_pos]

/-- **The logarithmic potential over a fixed ball, uniformly in the pole.**

`∫⁻ z in ball(0,R), ofReal(‖ζ - z‖⁻¹) ≤ ofReal(8πR)` for `R ≥ 0` and every `ζ : ℂ`, obtained from
the centred-uniform bound by the measure-preserving substitution `w = ζ - z`. -/
theorem lintegral_ofReal_norm_inv_sub_ball_aux (R : ℝ) (hR : 0 ≤ R) (ζ : ℂ) :
    ∫⁻ z in Metric.ball (0:ℂ) R, ENNReal.ofReal (‖ζ - z‖⁻¹) ≤
      ENNReal.ofReal (8 * Real.pi * R) := by
  rw [show (∫⁻ z in Metric.ball (0:ℂ) R, ENNReal.ofReal (‖ζ - z‖⁻¹))
        = ∫⁻ w in Metric.ball ζ R, ENNReal.ofReal (‖w‖⁻¹) from ?_]
  · exact lintegral_ofReal_norm_inv_ball_uniform_aux R hR ζ
  · have hT : MeasurePreserving (fun t : ℂ => ζ - t) volume volume :=
      Measure.measurePreserving_sub_left volume ζ
    have hmeas : Measurable ((Metric.ball ζ R).indicator
        (fun w => ENNReal.ofReal (‖w‖⁻¹))) :=
      (by fun_prop : Measurable (fun w : ℂ => ENNReal.ofReal (‖w‖⁻¹))).indicator
        Metric.isOpen_ball.measurableSet
    rw [← MeasureTheory.lintegral_indicator (Metric.isOpen_ball (x := (0:ℂ)) (ε := R)).measurableSet,
        ← MeasureTheory.lintegral_indicator (Metric.isOpen_ball (x := ζ) (ε := R)).measurableSet]
    rw [← hT.lintegral_comp
      (f := (Metric.ball ζ R).indicator (fun w => ENNReal.ofReal (‖w‖⁻¹))) hmeas]
    congr 1
    funext z
    have hmem : (ζ - z) ∈ Metric.ball ζ R ↔ z ∈ Metric.ball (0:ℂ) R := by
      simp only [Metric.mem_ball, dist_eq_norm]
      rw [show (ζ - z) - ζ = -z by ring, norm_neg, sub_zero]
    by_cases hz : z ∈ Metric.ball (0:ℂ) R
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hmem.mpr hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz (hmem.mp h))]

/-- **The Fubini integrand is integrable.**  For `ω ∈ L¹(ℂ)` and `ψ` smooth with compact
support, the function `p ↦ ω p.1 * ψ p.2 / (p.1 - p.2)` is integrable for the product of Lebesgue
measure with itself.  (This is what makes the double integral
`∫∫ ω ζ * ∂̄φ z / (ζ - z)` amenable to Fubini: integrating first in `z` over the compact support of
`ψ` costs nothing, because `1/‖ζ - z‖` is only logarithmically singular there.) -/
theorem integrable_prod_mul_div_sub (ω : ℂ → ℂ) (hω : MeasureTheory.Integrable ω MeasureTheory.volume)
    (ψ : ℂ → ℂ) (hψc : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun p : ℂ × ℂ => ω p.1 * ψ p.2 / (p.1 - p.2))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hAE : AEStronglyMeasurable (fun p : ℂ × ℂ => ω p.1 * ψ p.2 / (p.1 - p.2))
      (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℂ × ℂ => ω p.1) (volume.prod volume) :=
      hω.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : AEStronglyMeasurable (fun p : ℂ × ℂ => ψ p.2) (volume.prod volume) :=
      Measurable.aestronglyMeasurable (hψc.continuous.measurable.comp measurable_snd)
    have h3 : AEStronglyMeasurable (fun p : ℂ × ℂ => p.1 - p.2) (volume.prod volume) :=
      Measurable.aestronglyMeasurable (measurable_fst.sub measurable_snd)
    exact AEStronglyMeasurable.div₀ (h1.mul h2) h3
  refine ⟨hAE, ?_⟩
  obtain ⟨M₀, hM₀⟩ := hψs.isCompact.exists_bound_of_continuousOn hψc.continuous.continuousOn
  let M : ℝ := max M₀ 0
  have hMnn : 0 ≤ M := le_max_right _ _
  have hMbd : ∀ z, ‖ψ z‖ ≤ M := by
    intro z
    by_cases hz : z ∈ tsupport ψ
    · exact le_trans (hM₀ z hz) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact hMnn
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0:ℂ)).mp hψs.isCompact.isBounded
  let R : ℝ := max r 1
  have hR : 0 ≤ R := le_trans zero_le_one (le_max_right r 1)
  have hsupp : ∀ z, z ∉ Metric.ball (0:ℂ) R → ψ z = 0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hzt
    exact hz (Metric.ball_subset_ball (le_max_left r 1) (hr hzt))
  have hinner : ∀ ζ : ℂ, ∫⁻ z, ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)
      ≤ ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R) := by
    intro ζ
    have hpt : (fun z : ℂ => ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖))
        ≤ (fun z : ℂ => ENNReal.ofReal M *
            (Metric.ball (0:ℂ) R).indicator (fun z => ENNReal.ofReal (‖ζ - z‖⁻¹)) z) := by
      intro z
      change ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)
        ≤ ENNReal.ofReal M *
            (Metric.ball (0:ℂ) R).indicator (fun z => ENNReal.ofReal (‖ζ - z‖⁻¹)) z
      by_cases hz : z ∈ Metric.ball (0:ℂ) R
      · rw [Set.indicator_of_mem hz]
        calc ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)
            ≤ ENNReal.ofReal (M / ‖ζ - z‖) :=
              ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hMbd z) (norm_nonneg _))
          _ = ENNReal.ofReal M * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
              rw [div_eq_mul_inv, ENNReal.ofReal_mul hMnn]
      · rw [Set.indicator_of_notMem hz, mul_zero]
        simp [hsupp z hz]
    calc ∫⁻ z, ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)
        ≤ ∫⁻ z, ENNReal.ofReal M *
            (Metric.ball (0:ℂ) R).indicator (fun z => ENNReal.ofReal (‖ζ - z‖⁻¹)) z :=
          lintegral_mono hpt
      _ = ENNReal.ofReal M *
            ∫⁻ z, (Metric.ball (0:ℂ) R).indicator (fun z => ENNReal.ofReal (‖ζ - z‖⁻¹)) z :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal M *
            ∫⁻ z in Metric.ball (0:ℂ) R, ENNReal.ofReal (‖ζ - z‖⁻¹) := by
          rw [MeasureTheory.lintegral_indicator Metric.isOpen_ball.measurableSet]
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R) := by
          gcongr
          exact lintegral_ofReal_norm_inv_sub_ball_aux R hR ζ
  have hbound : ∫⁻ p : ℂ × ℂ, ‖ω p.1 * ψ p.2 / (p.1 - p.2)‖ₑ ∂(volume.prod volume)
      ≤ (∫⁻ ζ, ‖ω ζ‖ₑ ∂volume) * (ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R)) := by
    calc ∫⁻ p : ℂ × ℂ, ‖ω p.1 * ψ p.2 / (p.1 - p.2)‖ₑ ∂(volume.prod volume)
        = ∫⁻ ζ, ∫⁻ z, ENNReal.ofReal (‖ω ζ‖ * ‖ψ z‖ / ‖ζ - z‖) ∂volume ∂volume := by
          rw [MeasureTheory.lintegral_prod _ hAE.enorm]
          apply lintegral_congr; intro ζ
          apply lintegral_congr; intro z
          rw [← ofReal_norm, norm_div, norm_mul]
      _ = ∫⁻ ζ, ‖ω ζ‖ₑ * ∫⁻ z, ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖) ∂volume ∂volume := by
          apply lintegral_congr; intro ζ
          have he : (fun z : ℂ => ENNReal.ofReal (‖ω ζ‖ * ‖ψ z‖ / ‖ζ - z‖))
              = (fun z : ℂ => ‖ω ζ‖ₑ * ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)) := by
            funext z
            rw [div_eq_mul_inv, mul_assoc, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
            rfl
          rw [he, MeasureTheory.lintegral_const_mul' (‖ω ζ‖ₑ)
                (fun z : ℂ => ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)) (enorm_ne_top (x := ω ζ))]
      _ ≤ ∫⁻ ζ, ‖ω ζ‖ₑ * (ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R)) ∂volume := by
          apply lintegral_mono; intro ζ
          change ‖ω ζ‖ₑ * (∫⁻ z, ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖))
            ≤ ‖ω ζ‖ₑ * (ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R))
          gcongr
          exact hinner ζ
      _ = (∫⁻ ζ, ‖ω ζ‖ₑ ∂volume) * (ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R)) :=
          MeasureTheory.lintegral_mul_const'' _ hω.aestronglyMeasurable.enorm
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top hω.hasFiniteIntegral
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))

end Work.MRMT.Cauchy
