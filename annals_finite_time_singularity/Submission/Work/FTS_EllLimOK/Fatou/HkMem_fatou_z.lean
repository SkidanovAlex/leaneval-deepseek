import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.HkMem_fatou

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-! Copy of `HkMem_fatou` with the angular-slice hypothesis weakened from `≤ C` to the
`z`-local bound `≤ C * (1 + 1/z)` (the shape of `RulingELF.PkgMemSqH`).  `hTheta` is used only to
get finiteness of the angular lintegral of the limit, for which any real bound works. -/

theorem HkMem_fatou_z {α : ℝ} {k : ℕ} {C : ℝ} {un : ℕ → ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hMem : ∀ n, Work.Spaces.HkMem α k (un n))
    (hSq : ∀ n, Work.Spaces.HkSq α k (un n) ≤ C)
    (hTheta : ∀ n, ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ) ≤ C * (1 + 1 / z))
    (hmeas : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k u p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hconv : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (un n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i u z θ))) :
    Work.Spaces.HkMem α k u ∧ Work.Spaces.HkSq α k u ≤ C := by
  classical
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- the `HkSq`-half is exactly `HkSq_le_of_JConv`
  have hsq : Work.Spaces.HkSq α k u ≤ C :=
    HkSq_le_of_JConv (α := α) (k := k) (Ψn := un) (Ψ := u) (B := C) hMem hSq
      (fun j i hji z θ hq => hconv j i hji z θ hq)
  refine ⟨?_, hsq⟩
  -- (i) a.e. convergence in `θ`, for every fixed `z ∈ Iz`
  have hconv_ae : ∀ z ∈ Work.Spaces.Iz,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α k (un n) z θ) Filter.atTop
          (nhds (Work.Spaces.HkIntegrand α k u z θ)) :=
    fun z hz => HkMem_fatou_ae_tendsto (α := α) (k := k) hconv hz
  -- (ii) the angular slices of the limit integrand are a.e. strongly measurable
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ => Work.Spaces.HkIntegrand α k u z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have hlim : AEMeasurable
        (fun θ => Filter.liminf
          (fun n => Work.Spaces.HkIntegrand α k (un n) z θ) Filter.atTop)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      AEMeasurable.liminf (fun n => ((hMem n).1 z hz).aestronglyMeasurable.aemeasurable)
    refine hlim.congr ?_
    filter_upwards [hconv_ae z hz] with θ hθ
    exact hθ.liminf_eq
  -- (iii) Fatou in `θ`, for each fixed `z`
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ Filter.liminf (fun n => ∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) Filter.atTop := by
    intro z hz
    have hfat := MeasureTheory.lintegral_liminf_le'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (u := Filter.atTop)
      (f := fun n θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ))
      (fun n => ((hMem n).1 z hz).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    have hEq : (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => Filter.liminf
          (fun n => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ))
            Filter.atTop) := by
      filter_upwards [hconv_ae z hz] with θ hθ
      exact ((ENNReal.continuous_ofReal.tendsto
        (Work.Spaces.HkIntegrand α k u z θ)).comp hθ).liminf_eq.symm
    rw [MeasureTheory.lintegral_congr_ae hEq]
    exact hfat
  -- (iv) the resulting real inequality for each fixed `z`
  have hGle : ∀ z ∈ Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
        ≤ Filter.liminf (fun n => ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ))
              Filter.atTop := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
        = (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k u z θ)
        (hslice z hz).aestronglyMeasurable
    calc ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
        = ENNReal.ofReal ((∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)).toReal) := by rw [h1]
      _ ≤ (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := ENNReal.ofReal_toReal_le
      _ ≤ Filter.liminf (fun n => ∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) Filter.atTop := hinner z hz
      _ = Filter.liminf (fun n => ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ)) Filter.atTop := by
          refine Filter.liminf_congr (Filter.Eventually.of_forall fun n => ?_)
          exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMem n).1 z hz)
            (Filter.Eventually.of_forall fun θ =>
              Work.Spaces.HkIntegrand_nonneg α k (un n) z θ)).symm
  -- (v) the uniform bound on the angular lintegrals: finiteness of every slice
  have hlin_theta : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ ENNReal.ofReal (C * (1 + 1 / z)) := by
    intro z hz
    refine (hinner z hz).trans ?_
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    refine iSup_le fun n => ?_
    calc (⨅ i, ⨅ (_ : i ≥ n), (∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un i) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ (⨅ (_ : n ≥ n), (∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) := iInf_le _ n
      _ ≤ (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := iInf_le _ le_rfl
      _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMem n).1 z hz)
            (Filter.Eventually.of_forall fun θ =>
              Work.Spaces.HkIntegrand_nonneg α k (un n) z θ)).symm
      _ ≤ ENNReal.ofReal (C * (1 + 1 / z)) := ENNReal.ofReal_le_ofReal (hTheta n z hz)
  -- (vi) hence every angular slice of the limit integrand is integrable
  have hslice_int : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k u z θ) Work.Spaces.Iθ := by
    intro z hz
    refine ⟨(hslice z hz).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k u z θ)]
    exact lt_of_le_of_lt (hlin_theta z hz) ENNReal.ofReal_lt_top
  -- (vii) the `z`-function `z ↦ ∫⁻_θ ofReal (integrand)` is a.e. measurable, by Fubini
  have hmeas_lin : AEMeasurable
      (fun z => ∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    AEMeasurable.lintegral_prod_right
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ))
      hmeas.ennreal_ofReal
  -- (viii) hence so is the real `z`-function `z ↦ ∫_θ (integrand)`
  have hzmeas : AEMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine hmeas_lin.ennreal_toReal.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIz] with z hz
    exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k u z θ)
      (hslice z hz).aestronglyMeasurable).symm
  -- (ix) Fatou in `z`
  have hchain : (∫⁻ z, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) ≤ ENNReal.ofReal C := by
    have hFatouZ := MeasureTheory.lintegral_liminf_le'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) (u := Filter.atTop)
      (f := fun n z => ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ))
      (fun n => ((hMem n).2).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    refine le_trans (MeasureTheory.lintegral_mono_ae ?_) (le_trans hFatouZ ?_)
    · filter_upwards [MeasureTheory.ae_restrict_mem hIz] with z hz
      exact hGle z hz
    · rw [Filter.liminf_eq_iSup_iInf_of_nat]
      refine iSup_le fun n => ?_
      calc (⨅ i, ⨅ (_ : i ≥ n), (∫⁻ z, ENNReal.ofReal
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un i) z θ)
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)))
          ≤ (∫⁻ z, ENNReal.ofReal
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ)
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
            le_trans (iInf_le _ n) (iInf_le _ le_rfl)
        _ = ENNReal.ofReal (Work.Spaces.HkSq α k (un n)) :=
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMem n).2)
              (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg
                (fun θ => Work.Spaces.HkIntegrand_nonneg α k (un n) z θ))).symm
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hSq n)
  -- (x) hence the `z`-function is integrable, which is the second half of `HkMem`
  have hzint : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
      Work.Spaces.Iz := by
    refine ⟨hzmeas.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg
        (fun θ => Work.Spaces.HkIntegrand_nonneg α k u z θ))]
    exact lt_of_le_of_lt hchain ENNReal.ofReal_lt_top
  exact ⟨hslice_int, hzint⟩

end Work.FTS_EllLimOK
