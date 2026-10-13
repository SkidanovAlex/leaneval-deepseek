/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AeSigmaUpgradeU` — the σ-upgrade of the `u`-norm, a.e. in `z`

The constrained σ-Poincaré inequality (`Work.FTS.EllipticEst.Honest.SigmaPoincare`) says that for
`f` of class `C¹` on `(0, π/2)` with `∫_θ f θ sinθcos²θ dθ = 0` and that moment honest,

  `∫⁻_θ f² σ ≤ C ∫⁻_θ (∂_θf)²,    σ θ = sin(2θ)^{-η}`.

For the fibres `f = u(z,·)` of an `AeData` datum, the solvability condition
`F_* u(z) = ∫_θ u(z,θ) sinθcos²θ dθ = 0` holds for almost every `z`, so the inequality holds
slicewise a.e.: the `σ`-weighted angular integral `∫⁻_θ u(z,θ)² σ θ` is controlled by the
*unweighted* angular integral `∫⁻_θ (∂_θu(z,θ))²`, the radial weight `w` being untouched.

This is step 1(c) of `Submission/Work/FTS/EllipticEst/H2W/Ae/NOTES_level0Ae.md`: it converts the
radial-only bounds (obtained from the radial energy inequality and the constrained slice gap
`9 ∫ u² ≤ ∫ (∂_θu)²`) into the `ρ = w²σ`-weighted bounds of the target.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Honest.SigmaPoincare
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Work.FTS.EllipticEst.Honest Work.FTS.EllipticEst.H2W.Ae

/-- **The slicewise σ-upgrade**, a.e. in `z`, for the fibres of an `AeData` datum: the
`σ`-weighted angular square integral of `u(z,·)` is controlled by the unweighted angular square
integral of `∂_θu(z,·)`.  The only extra input is the honesty of the moment
`θ ↦ u(z,θ) sinθcos²θ` (it holds whenever the fibre is bounded, e.g. from `HkMem α 0 (∂_θθu)`). -/
theorem AeSigmaUpgradeU_ae : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => u z θ * (Real.sin θ * Real.cos θ ^ 2))
          Work.Spaces.Iθ) →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          ≤ ENNReal.ofReal C
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) := by
  obtain ⟨C, hCpos, hC⟩ := SigmaPoincare
  refine ⟨C, hCpos, ?_⟩
  intro α u G h hint
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hint, AeData.momU h]
    with z hz hintz hmomz
  have hslice : ContDiffOn ℝ 1 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_slice u hz (h.smooth 1)
  have hmom : (∫ θ in Work.Spaces.Iθ, u z θ * Real.sin θ * Real.cos θ ^ 2) = 0 := by
    simpa only [Work.Elliptic.Fstar, Work.Elliptic.sinCos2, mul_assoc] using hmomz
  have hkey := hC (fun θ => u z θ) hslice hintz hmom
  simpa only [Work.Spaces.pth] using hkey

/-- **The integrated σ-upgrade**: multiplying the a.e. slicewise inequality by the radial weight
`w²` and integrating in `z` gives the `ρ`-form. -/
theorem AeSigmaUpgradeU : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => u z θ * (Real.sin θ * Real.cos θ ^ 2))
          Work.Spaces.Iθ) →
      (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
        ≤ ENNReal.ofReal C
          * (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ,
                    ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
  obtain ⟨C, hCpos, hC⟩ := AeSigmaUpgradeU_ae
  refine ⟨C, hCpos, ?_⟩
  intro α u G h hint
  have hae := hC α u G h hint
  have hIzm : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
  have haeI : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        ≤ ENNReal.ofReal C
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) := by
    rw [hIzm]
    exact hae
  have hmono : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (ENNReal.ofReal C * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [haeI] with z hz
    exact mul_le_mul_right hz _
  refine hmono.trans (le_of_eq ?_)
  rw [← MeasureTheory.lintegral_const_mul']
  · refine MeasureTheory.lintegral_congr fun z => ?_
    ring
  · exact ENNReal.ofReal_ne_top

/-! ## Discharging the honesty hypothesis -/

/-- **The fibre moment `θ ↦ u z θ · sinθcos²θ` is honest.**  The fibre is `C²` on the open
interval and `(∂_θθu)² σ` is integrable there (`HkMemSliceSqSigma`), so the fibre and its
derivative are bounded on the open interval; the product with the bounded profile
`sinθcos²θ` is therefore integrable. -/
theorem AeSliceMomentU_integrable (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => u z θ * (Real.sin θ * Real.cos θ ^ 2))
      Work.Spaces.Iθ := by
  have hsm : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_slice u hz (h.smooth 2)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv (fun θ' => u z θ') t) θ) ^ 2 * sEta θ)
      Work.Spaces.Iθ := by
    have h0 := HkMemSliceSqSigma h.memAng2 hz
    simpa only [Work.Spaces.pth, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Nat.reduceAdd] using h0
  obtain ⟨C, hCpos, hC⟩ := SliceBddSqSigma hsm h2
  have hbdd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖u z θ * (Real.sin θ * Real.cos θ ^ 2)‖ ≤ C := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hcos : |Real.cos θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.cos_sq_le_one θ]
    have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hsin2 : |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 := by
      nlinarith [abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ ^ 2)]
    have hu : |u z θ| ≤ C := by
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · rw [← h0, AeData.dirZero h z, abs_zero]; exact hCpos.le
      · rcases eq_or_lt_of_le hθ.2 with h1 | h1
        · rw [h1, AeData.dirPi h z, abs_zero]; exact hCpos.le
        · exact (hC θ ⟨h0, h1⟩).2
    calc |u z θ| * (|Real.sin θ| * |Real.cos θ ^ 2|) ≤ C * 1 :=
          mul_le_mul hu hsin2 (by positivity) hCpos.le
      _ = C := by ring
  refine MeasureTheory.IntegrableOn.of_bound (isCompact_Icc.measure_lt_top) ?_ C hbdd
  exact (aesm_of_contDiffOn_Ioo hsm).mul
    (by
      show AEStronglyMeasurable (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) _
      fun_prop)

/-- **The σ-upgrade of the `u`-norm, integrated, with the honesty hypothesis discharged.** -/
theorem AeSigmaUpgradeU_all : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
        ≤ ENNReal.ofReal C
          * (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ,
                    ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
  obtain ⟨C, hCpos, hC⟩ := AeSigmaUpgradeU
  refine ⟨C, hCpos, ?_⟩
  intro α u G h
  refine hC α u G h ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
  exact AeSliceMomentU_integrable α u G h hz

end Work.FTS.EllipticEst.H2W.AeProof
