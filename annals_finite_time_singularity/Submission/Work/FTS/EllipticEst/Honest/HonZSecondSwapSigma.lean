import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-- **The `σ`-weighted Tonelli exchange for `∂_z²Ψ`.**  For honest data `Hon α F Ψ`, the `θ`-first
iterated `lintegral` of `(1+z)^4 · (∂_z²Ψ)² · σ(θ)` (with `σ = sEta = sin(2θ)^{-η}`) is finite.

This is the Tonelli companion of the *outer* integrability component of `Hon.memA`
(`∫_z w(z)² ∫_θ (z²∂_z²Ψ)² σ < ∞`, whose integrand equals `(1+z)^4 (∂_z²Ψ)² σ` off `z = 0`),
the `θ`-`z` exchange needed to read off `∫⁻_z (1+z)^4 (∂_z²Ψ)² < ⊤` for a.e. `θ`.

Proof.  Write `A := z²∂_z²Ψ`.  By `Hon.memA` the `θ`-slice of `A` is `σ`-square integrable and the
outer `z`-integral of the `ℋ⁰`-integrand `HkIntegrand α 0 A` is finite, so
`∫⁻_z ofReal (∫_θ HkIntegrand α 0 A) < ⊤` (`Integrable.lintegral_lt_top`).  Converting the inner
`lintegral` to `ofReal` of the inner Bochner integral a.e. in `z`
(`ofReal_integral_eq_lintegral_ofReal`, from the honesty of the slices) and applying Tonelli
(`lintegral_lintegral_swap`, measurability from continuity on the open quadrant) gives the
`θ`-first integral.  Finally the level-`0` integrand of `A` is, off the null set `{z = 0}`,
`w(z)² z⁴ (∂_z²Ψ)² σ = (1+z)^4 (∂_z²Ψ)² σ` (`w z = (1+z)²/z²`), and `HkIntegrand_zero_eq'`
identifies `HkIntegrand α 0 A z θ` with `w(z)² (A²σ)`. -/
theorem HonZSecondSwapSigma (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) :
    (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((1 + z) ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)) < ⊤ := by
  have hSmΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.sm
  -- smoothness on the open quadrant of the datum `A = z²∂_z²Ψ`
  have hSmA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2) Work.FTS.EllipticEst.Q0
    exact ((contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2).mul (hSmΨ.pzIter 2)
  have hmemA : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    h.memA
  -- (0) the `z`-outer finiteness coming from the honesty of `A`
  have hZfin : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ))
      < ⊤ :=
    MeasureTheory.Integrable.lintegral_lt_top hmemA.2
  -- (1) the inner `lintegral` is `ofReal` of the inner Bochner integral, a.e. in `z`
  have hstep1 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iz
      from measurableSet_Ici)] with z hz
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmemA.1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
  -- (2) Tonelli: exchange the two integrations
  have hswap : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) :=
    MeasureTheory.lintegral_lintegral_swap
      (f := fun z θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ))
      (((Work.Spaces.aesm_of_continuousOn_Qd _ (hSmA.continuousOn_HkIntegrand α 0)
        ).aemeasurable).ennreal_ofReal)
  have hmid : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)) < ⊤ := by
    rw [← hswap, ← hstep1]
    exact hZfin
  -- (3) off the null set `{z = 0}` the `ℋ⁰`-integrand of `A` is the claimed integrand
  have hzne : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ≠ 0 := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    filter_upwards [show ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 from by
      rw [MeasureTheory.ae_iff]; simp] with z hz _
    exact hz
  have hpoint : ∀ z, z ≠ 0 → ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        = (1 + z) ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ := by
    intro z hz θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq' hθ _ z]
    have hw : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
      rw [Work.Spaces.w, div_pow]
      ring
    rw [hw]
    field_simp
  have hstep3 : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((1 + z) ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ
      from measurableSet_Icc)] with θ hθ
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hzne] with z hz
    rw [hpoint z hz θ hθ]
  rw [← hstep3]
  exact hmid

end

end Work.FTS.EllipticEst.Honest
