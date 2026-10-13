/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/XBallIterExistsAux/MajorantX.lean`

The *integrable majorant* of the parametric-integral argument: for an angular majorant `G` of the
slices of `W` (integrable on `(0,π/2)`, as produced by `ZSliceDomination` out of `HkMem α 1 W`),
the function

  `x = (θ,p₂) ↦ sin θ cos²θ · G (thShift θ p₂)`

is integrable for the compact product measure `Jmu ε` on `Iθ × [-ε,ε]`.

The two ingredients are

* the *angular substitution* bound `JepsHkMem.lintegral_thShift_le`,
  `∫⁻_θ U (thShift θ p) ≤ e^{3|p|} ∫⁻_θ U θ` — which holds for an arbitrary `U : ℝ → ℝ≥0∞` and
  needs no measurability — giving the finiteness of the integral after Tonelli in the swapped
  order (angle inner, shift outer);
* the absolute continuity of the pushforward of `Jmu ε` under the angular shift
  (`thShift_preimage_null`, from the same substitution bound): it is what lets an arbitrary
  `AEMeasurable` representative of `G` (which need not be honest on the boundary of `Iθ`) be
  replaced by a *measurable* one, i.e. it is what makes the composite `G ∘ thShift` a.e. strongly
  measurable.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux.PhiFam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Measurability of the angular shift -/

/-- `Real.tan` is measurable (it is `sin / cos`, so that Lean's totalised division gives a
genuine value everywhere). -/
theorem measurable_tan : Measurable Real.tan := by
  rw [show Real.tan = fun x : ℝ => Real.sin x / Real.cos x from
    funext Real.tan_eq_sin_div_cos]
  exact Real.measurable_sin.div Real.measurable_cos

/-- The angular shift `x ↦ thShift x.1 x.2` is (Borel) measurable. -/
theorem measurable_thShift :
    Measurable (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2) := by
  have hfun : (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2)
      = fun x : ℝ × ℝ => Real.arctan (Real.tan x.1 * Real.exp (-x.2)) := rfl
  rw [hfun]
  exact Real.measurable_arctan.comp
    ((measurable_tan.comp measurable_fst).mul (Real.measurable_exp.comp measurable_snd.neg))

/-- The angular shift with the second coordinate fixed is measurable. -/
theorem measurable_thShift_right (p₂ : ℝ) :
    Measurable (fun θ : ℝ => Work.FTS.StrongEps.thShift θ p₂) := by
  have hfun : (fun θ : ℝ => Work.FTS.StrongEps.thShift θ p₂)
      = fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-p₂)) := rfl
  rw [hfun]
  exact Real.measurable_arctan.comp (measurable_tan.mul measurable_const)

/-! ## The pushforward of `Jmu ε` under the angular shift is absolutely continuous -/

/-- **Preimages of null sets under the angular shift are null.**  For fixed `p₂` the substitution
bound `lintegral_thShift_le` applied to the indicator of `Z` gives
`(volume.restrict Iθ) {θ | thShift θ p₂ ∈ Z} ≤ e^{3|p₂|} · volume Z = 0`; Fubini in the swapped
order (angle inner, shift outer) then yields the statement. -/
theorem thShift_preimage_null {ε : ℝ} {Z : Set ℝ} (hZ : MeasurableSet Z)
    (hZ0 : (MeasureTheory.volume : MeasureTheory.Measure ℝ) Z = 0) :
    Jmu ε {x : ℝ × ℝ | Work.FTS.StrongEps.thShift x.1 x.2 ∈ Z} = 0 := by
  set A : Set (ℝ × ℝ) := {x | Work.FTS.StrongEps.thShift x.1 x.2 ∈ Z} with hA
  have hAmeas : MeasurableSet A := hZ.preimage measurable_thShift
  have hθmeas : ∀ p₂ : ℝ, MeasurableSet {θ : ℝ | Work.FTS.StrongEps.thShift θ p₂ ∈ Z} :=
    fun p₂ => hZ.preimage (measurable_thShift_right p₂)
  -- swap the product integral into the angle-inner order
  have hswap : Jmu ε A = ∫⁻ p₂, (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      {θ : ℝ | Work.FTS.StrongEps.thShift θ p₂ ∈ Z}
      ∂(MeasureTheory.volume.restrict (Set.Icc (-ε) ε)) := by
    rw [Jmu]
    rw [← MeasureTheory.lintegral_indicator_one
      (μ := (MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) hAmeas]
    rw [MeasureTheory.lintegral_prod_symm'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (ν := MeasureTheory.volume.restrict (Set.Icc (-ε) ε))
      (f := A.indicator (1 : ℝ × ℝ → ENNReal))
      (measurable_const.indicator hAmeas)]
    refine MeasureTheory.lintegral_congr fun p₂ => ?_
    rw [← MeasureTheory.lintegral_indicator_one
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (hθmeas p₂)]
    refine MeasureTheory.lintegral_congr fun θ => ?_
    by_cases h : Work.FTS.StrongEps.thShift θ p₂ ∈ Z <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hA, h]
  -- each inner integral vanishes
  have hzero : ∀ p₂ : ℝ, (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      {θ : ℝ | Work.FTS.StrongEps.thShift θ p₂ ∈ Z} = 0 := by
    intro p₂
    refine le_antisymm ?_ zero_le
    calc (MeasureTheory.volume.restrict Work.Spaces.Iθ)
          {θ : ℝ | Work.FTS.StrongEps.thShift θ p₂ ∈ Z}
        = ∫⁻ θ, Set.indicator {θ : ℝ | Work.FTS.StrongEps.thShift θ p₂ ∈ Z}
            (1 : ℝ → ENNReal) θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          (MeasureTheory.lintegral_indicator_one (hθmeas p₂)).symm
      _ ≤ ∫⁻ θ, Set.indicator Z (1 : ℝ → ENNReal) (Work.FTS.StrongEps.thShift θ p₂)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          refine MeasureTheory.lintegral_mono fun θ => ?_
          by_cases h : Work.FTS.StrongEps.thShift θ p₂ ∈ Z <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
      _ ≤ ENNReal.ofReal (Real.exp (3 * |p₂|))
            * ∫⁻ θ, Set.indicator Z (1 : ℝ → ENNReal) θ
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le
            (fun φ => Set.indicator Z (1 : ℝ → ENNReal) φ) p₂
      _ = 0 := by
          have h2 : ∫⁻ θ, Set.indicator Z (1 : ℝ → ENNReal) θ
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) = 0 := by
            rw [MeasureTheory.lintegral_indicator_one
              (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) hZ]
            rw [MeasureTheory.Measure.restrict_apply hZ]
            exact measure_mono_null Set.inter_subset_left hZ0
          rw [h2, mul_zero]
  rw [hswap]
  simp only [hzero, lintegral_zero]

/-- The complement of the open interval is null for the angular measure. -/
theorem measure_compl_Ioo_Jmu {ε : ℝ} :
    Jmu ε {x : ℝ × ℝ | x.1 ∉ Set.Ioo 0 (Real.pi / 2)} = 0 :=
  MeasureTheory.ae_iff.mp ae_mem_Ioo_Jmu

/-- The pushforward of `Jmu ε` under the angular shift is absolutely continuous with respect to
the angular measure on `(0,π/2)`. -/
theorem map_thShift_absolutelyContinuous {ε : ℝ} :
    (MeasureTheory.Measure.map (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2) (Jmu ε))
      ≪ (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [MeasureTheory.Measure.map_apply measurable_thShift hs]
  have hnull : (MeasureTheory.volume : MeasureTheory.Measure ℝ) (s ∩ Set.Ioo 0 (Real.pi / 2))
      = 0 := by
    rw [← MeasureTheory.Measure.restrict_apply hs]
    exact hs0
  refine measure_mono_null ?_ (measure_union_null
    (thShift_preimage_null (Z := s ∩ Set.Ioo 0 (Real.pi / 2))
      (MeasurableSet.inter hs measurableSet_Ioo) hnull)
    measure_compl_Ioo_Jmu)
  intro x hx
  by_cases hx1 : x.1 ∈ Set.Ioo 0 (Real.pi / 2)
  · exact Or.inl ⟨hx, Work.FTS.StrongEps.thShift_mem hx1⟩
  · exact Or.inr hx1

/-- The angular shift is quasi-measure-preserving, from `Jmu ε` to the angular measure. -/
theorem quasiMeasurePreserving_thShift {ε : ℝ} :
    MeasureTheory.Measure.QuasiMeasurePreserving
      (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2) (Jmu ε)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
  MeasureTheory.Measure.QuasiMeasurePreserving.mk measurable_thShift
    map_thShift_absolutelyContinuous

/-! ## The majorant is integrable -/

/-- An `IntegrableOn` function on `(0,π/2)` has a measurable representative agreeing with it
a.e. -/
theorem exists_measurable_rep_of_integrableOn {G : ℝ → ℝ}
    (hG : MeasureTheory.IntegrableOn G (Set.Ioo 0 (Real.pi / 2))) :
    ∃ G' : ℝ → ℝ, Measurable G' ∧
      G =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))] G' :=
  ⟨AEMeasurable.mk G hG.aemeasurable, AEMeasurable.measurable_mk _,
    AEMeasurable.ae_eq_mk _⟩

/-- The `ℋ¹`-majorant composed with the angular shift is integrable: after Tonelli (angle inner,
shift outer) the substitution bound controls the angle integral by `e^{3|p₂|}` times the
`L¹`-mass of the representative, and the outer integral is over the compact interval `[-ε,ε]`. -/
theorem integrable_shift_of_integrableOn {G : ℝ → ℝ} {ε : ℝ}
    (hG : MeasureTheory.IntegrableOn G (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.Integrable
      (fun x : ℝ × ℝ => G (Work.FTS.StrongEps.thShift x.1 x.2)) (Jmu ε) := by
  obtain ⟨G', hG'meas, hG'ae⟩ := exists_measurable_rep_of_integrableOn hG
  have hG'int : MeasureTheory.IntegrableOn G' (Set.Ioo 0 (Real.pi / 2)) := hG.congr hG'ae
  -- finiteness of the `lintegral` of the measurable representative composed with the shift
  have hfinite : ∫⁻ x : ℝ × ℝ, ENNReal.ofReal ‖G' (Work.FTS.StrongEps.thShift x.1 x.2)‖
      ∂(Jmu ε) < ⊤ := by
    rw [MeasureTheory.lintegral_congr fun x => by rw [Real.norm_eq_abs]]
    have hprod : ∫⁻ x : ℝ × ℝ, ENNReal.ofReal |G' (Work.FTS.StrongEps.thShift x.1 x.2)|
          ∂(Jmu ε)
        = ∫⁻ p₂ in Set.Icc (-ε) ε, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |G' (Work.FTS.StrongEps.thShift θ p₂)| := by
      rw [Jmu]
      exact MeasureTheory.lintegral_prod_symm'
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (ν := MeasureTheory.volume.restrict (Set.Icc (-ε) ε)) _
        (Measurable.ennreal_ofReal (hG'meas.comp measurable_thShift).abs)
    rw [hprod]
    set K : ENNReal := ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G' θ| with hK
    have hKfin : K < ⊤ := by
      rw [hK]
      rw [show (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G' θ|)
          = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal |G' θ| from by
        rw [show (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
            = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) from
          (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm]]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hG'int.abs
        (Filter.Eventually.of_forall fun θ => abs_nonneg _)]
      exact ENNReal.ofReal_lt_top
    have hinner : ∀ᵐ p₂ ∂(MeasureTheory.volume.restrict (Set.Icc (-ε) ε)),
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |G' (Work.FTS.StrongEps.thShift θ p₂)|)
          ≤ ENNReal.ofReal (Real.exp (3 * ε)) * K := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with p₂ hp
      have habs : |p₂| ≤ ε := abs_le.mpr hp
      calc (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |G' (Work.FTS.StrongEps.thShift θ p₂)|)
          ≤ ENNReal.ofReal (Real.exp (3 * |p₂|)) * K :=
            Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le
              (fun φ => ENNReal.ofReal |G' φ|) p₂
        _ ≤ ENNReal.ofReal (Real.exp (3 * ε)) * K :=
            mul_le_mul_of_nonneg_right
              (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))) zero_le
    calc ∫⁻ p₂ in Set.Icc (-ε) ε, (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |G' (Work.FTS.StrongEps.thShift θ p₂)|)
        ≤ ∫⁻ p₂ in Set.Icc (-ε) ε, ENNReal.ofReal (Real.exp (3 * ε)) * K :=
          MeasureTheory.lintegral_mono_ae hinner
      _ = ENNReal.ofReal (Real.exp (3 * ε)) * K * ENNReal.ofReal (2 * ε) := by
          rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
            Real.volume_Icc, show ε - (-ε) = 2 * ε by ring]
      _ < ⊤ := ENNReal.mul_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin) ENNReal.ofReal_lt_top
  have hInt' : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => G' (Work.FTS.StrongEps.thShift x.1 x.2)) (Jmu ε) := by
    refine ⟨(hG'meas.comp measurable_thShift).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs] using hfinite
  refine hInt'.congr ?_
  exact MeasureTheory.ae_eq_comp measurable_thShift.aemeasurable
    (map_thShift_absolutelyContinuous.ae_eq hG'ae.symm)

/-- **The majorant is integrable.** -/
theorem integrable_sinCos2_mul_shift_of_integrableOn {G : ℝ → ℝ} {ε : ℝ}
    (hG : MeasureTheory.IntegrableOn G (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.Integrable
      (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1
        * G (Work.FTS.StrongEps.thShift x.1 x.2)) (Jmu ε) := by
  refine MeasureTheory.Integrable.mono' ((integrable_shift_of_integrableOn hG).norm) ?_ ?_
  · have hcomp : AEMeasurable (fun x : ℝ × ℝ => G (Work.FTS.StrongEps.thShift x.1 x.2))
        (Jmu ε) :=
      AEMeasurable.comp_quasiMeasurePreserving hG.aemeasurable quasiMeasurePreserving_thShift
    have hsin : Continuous (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1) := by
      rw [show (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1)
          = fun x : ℝ × ℝ => Real.sin x.1 * Real.cos x.1 ^ 2 from rfl]
      fun_prop
    exact (hsin.measurable.aemeasurable.mul hcomp).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    have hsin : |Work.Elliptic.sinCos2 x.1| ≤ 1 := by
      rw [Work.Elliptic.sinCos2, abs_mul]
      calc |Real.sin x.1| * |Real.cos x.1 ^ 2| ≤ 1 * 1 :=
            mul_le_mul (Real.abs_sin_le_one _)
              (by rw [abs_of_nonneg (sq_nonneg _)]; exact Real.cos_sq_le_one x.1)
              (abs_nonneg _) zero_le_one
        _ = 1 := mul_one 1
    calc |Work.Elliptic.sinCos2 x.1| * |G (Work.FTS.StrongEps.thShift x.1 x.2)|
        ≤ 1 * |G (Work.FTS.StrongEps.thShift x.1 x.2)| :=
          mul_le_mul_of_nonneg_right hsin (abs_nonneg _)
      _ = ‖G (Work.FTS.StrongEps.thShift x.1 x.2)‖ := by
          rw [one_mul, Real.norm_eq_abs]

end Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux
