import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Prop.Ang2.AePpReduce
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeStep2Aux.aeMixedAe_mem_of_fin` — the reduction

For a datum `AeData α u G` (so `u` is `C^∞` on the open quadrant) the finiteness of the
*iterated* weighted Lebesgue integral

`X^𝓁 := ∫⁻ z in Iz, ∫⁻ θ in Iθ, ofReal ((z · ∂_z∂_θu)² σ(θ)) < ⊤`,  `σ = sin(2θ)^{-η}`,

implies both conjuncts of `aeMixedAe_mem`:

* the angular slices `θ ↦ (z · ∂_z∂_θu)² σ` are integrable for almost every `z > 0`, and
* the outer function `z ↦ ∫ θ in Iθ, (z · ∂_z∂_θu)² σ` is integrable on `Iz`.

The mathematics is Tonelli plus the fact that the integrand is continuous on the open
quadrant (so a.e. strongly measurable there) and nonnegative on `Iz × Iθ`.  Everything is
done in the product measure `mz.prod mθ`; the two endpoints `z = 0`, `θ = 0, π/2` are null
sets and are handled by `Measure.restrict_congr_set`.

The converse direction (the two conjuncts imply the finiteness, hence the equivalence) is
not needed downstream, and the *unconditional* statement `aeMixedAe_mem` (finiteness from
`AeData` alone) is the project's open `aePpFinite` crux, cf.
`Cores/AeStep2Aux/NOTES_aeMixedAe_mem.md`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

set_option autoImplicit false

/-! ## The two restricted measures of the quadrant -/

/-- `dz` restricted to `Iz = [0,∞)`. -/
private abbrev mz : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iz

/-- `dθ` restricted to `Iθ = [0,π/2]`. -/
private abbrev mth : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ

/-- The open quadrant of the elliptic estimates. -/
private abbrev quad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-! ## Almost everywhere strong measurability on the product -/

/-- A function whose uncurried form is continuous on the open quadrant is almost everywhere
strongly measurable for `mz.prod mth`: the product measure is the planar Lebesgue measure
restricted to the open quadrant (the two closed intervals `Iz`, `Iθ` differ from the open
ones by null sets). -/
private theorem quad_aesm_prod {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry F) quad) :
    AEStronglyMeasurable (Function.uncurry F) (mz.prod mth) := by
  have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm
  have hprod : mz.prod mth
      = (MeasureTheory.volume.prod MeasureTheory.volume).restrict quad := by
    show (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) = _
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Measure.set_prod_ae_eq hz hθ)
  rw [hprod]
  exact hcont.aestronglyMeasurable ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)

/-! ## The reduction -/

/-- **Finiteness of the iterated weighted `∫⁻` gives both conjuncts.**  If `F` is continuous
on the open quadrant, nonnegative for `θ ∈ Iθ`, and `∫⁻ z in Iz, ∫⁻ θ in Iθ, ofReal (F z θ)`
is finite, then the slices `θ ↦ F z θ` are integrable for almost every `z > 0` and the outer
integral `z ↦ ∫ θ in Iθ, F z θ` is integrable on `Iz`. -/
private theorem integrableOn_of_iterated_lintegral_lt_top (F : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (Function.uncurry F) quad)
    (hnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ F z θ)
    (hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (F z θ)) < ⊤) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) Work.Spaces.Iz := by
  have hmzprod : mz.prod mth
      = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    MeasureTheory.Measure.prod_restrict _ _
  have haesm : AEStronglyMeasurable (Function.uncurry F) (mz.prod mth) :=
    quad_aesm_prod hcont
  -- the angular variable lies in `Iθ` almost everywhere
  have hmemθ : ∀ᵐ p ∂(mz.prod mth), p.2 ∈ Work.Spaces.Iθ := by
    have hmI : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      measurableSet_Ici.prod measurableSet_Icc
    rw [hmzprod]
    exact (MeasureTheory.ae_restrict_mem hmI).mono (fun p hp => (Set.mem_prod.mp hp).2)
  have hnn_ae : 0 ≤ᵐ[mz.prod mth] Function.uncurry F :=
    hmemθ.mono fun p hp => hnn p.1 p.2 hp
  -- Tonelli identifies the product `∫⁻` with the iterated one
  have hmeas_ofReal : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Function.uncurry F p))
      (mz.prod mth) := haesm.aemeasurable.ennreal_ofReal
  have hton : (∫⁻ p, ENNReal.ofReal (Function.uncurry F p) ∂(mz.prod mth))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (F z θ) :=
    MeasureTheory.lintegral_prod _ hmeas_ofReal
  have hprod_fin : (∫⁻ p, ENNReal.ofReal (Function.uncurry F p) ∂(mz.prod mth)) < ⊤ := by
    rw [hton]; exact hfin
  have hint : MeasureTheory.Integrable (Function.uncurry F) (mz.prod mth) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm hnn_ae).mp (ne_of_lt hprod_fin)
  obtain ⟨hslice, -⟩ := (MeasureTheory.integrable_prod_iff haesm).mp hint
  refine ⟨?_, ?_⟩
  · -- transfer the a.e. statement from `mz` to `volume.restrict (Ioi 0)`
    have hμ : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) = mz :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))
    rw [hμ]
    filter_upwards [hslice] with z hz
    exact hz
  · exact MeasureTheory.Integrable.integral_prod_left hint

/-! ## The target -/

theorem aeMixedAe_mem_of_fin : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ)) < ⊤ →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz := by
  intro α u G hAe hfin
  -- `u` is `C^∞` on the open quadrant, hence so is `∂_z∂_θu`
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (fun n => Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hAe n)
  have hpz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pth u) p.1 p.2) quad :=
    ((hSO.pth).pz).continuousOn
  -- the angular weight `σ = sin(2θ)^{-η}` is continuous on the open quadrant
  have hsinpos : ∀ p ∈ quad, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hp2⟩ := Set.mem_prod.mp hp
    obtain ⟨hθ0, hθ1⟩ := Set.mem_Ioo.mp hp2
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsig : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.2) quad := by
    have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) quad :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    have h := hsin.rpow_const (p := -(Work.Spaces.eta))
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
    simpa only [Work.FTS.EllipticEst.AngSecond.sig] using h
  have hcont : ContinuousOn (Function.uncurry
      (fun z θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)) quad :=
    ((continuous_fst.continuousOn.mul hpz).pow 2).mul hsig
  refine integrableOn_of_iterated_lintegral_lt_top
    (fun z θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) hcont ?_ hfin
  intro z θ hθ
  exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)

end Work.FTS.EllipticEst.Cores.AeStep2Aux
