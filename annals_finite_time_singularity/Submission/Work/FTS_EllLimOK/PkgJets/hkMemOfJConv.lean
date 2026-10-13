import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.HkSq_le_of_JConv
import Submission.Work.FTS_EllLimOK.HkMem_fatou
import Submission.Work.FTS_EllLimOK.JConvAux.ae_tendsto_HkIntegrand_slice
import Submission.Work.FTS_EllLimOK.JConvAux.ofReal_integral_le_liminf_ofReal_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ^0`-membership and the `ℋ^0`-bound along a pointwise convergent sequence

`hkMemOfJConv` is the `k = 0` instance of the Fatou step for the weighted Sobolev space
`ℋ^k` of the paper.  For `k = 0` the integrand `HkIntegrand α 0 f z θ` only involves the
*mixed slot* `D_z^0 D_θ^0 f = f` itself (the two sums carrying `D_θ` are empty: they are
guarded by `1 ≤ i` with `i + j ≤ 0`), so that plain pointwise convergence of `un n → u` on
the open quadrant -- rather than convergence of all the jets -- already suffices.

The proof is two nested Fatou arguments:

* **Fatou in `θ`**, for every fixed `z ∈ Iz`: the integrands converge a.e. in `θ`
  (`JConvAux.ae_tendsto_HkIntegrand_slice`, which reduces the integrand to the slots and
  handles the degenerate lines `z = 0`, `sin (2θ) = 0`, where both integrands vanish
  identically), and `JConvAux.ofReal_integral_le_liminf_ofReal_integral` converts the
  `ℝ≥0∞`-Fatou inequality into
  `ofReal (∫_θ F z) ≤ liminf_n ofReal (∫_θ F_n n z)`;
* **Fatou in `z`**, integrated against `volume.restrict Iz`: this bounds
  `∫⁻_z ofReal (∫_θ F z)` by `liminf_n ofReal (HkSq α 0 (un n)) ≤ ofReal C`.  The
  `z`-function `z ↦ ∫_θ F z` is a.e. measurable because `hmeas` gives the a.e.
  measurability of `z ↦ ∫⁻_θ ofReal (F z)` through `AEMeasurable.lintegral_prod_right`.

Finiteness of the resulting lintegral gives both halves at once: `HasFiniteIntegral` yields
the `z`-integrability of the slice integrals (the second half of `HkMem α 0 u`, the first
being the hypothesis `hslice`), and `integral_eq_lintegral_of_nonneg_ae` turns the bound into
`HkSq α 0 u ≤ C`.
-/

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

theorem hkMemOfJConv {α C : ℝ} {un : ℕ → ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hMem : ∀ n : ℕ, Work.Spaces.HkMem α 0 (un n))
    (hSq : ∀ n : ℕ, Work.Spaces.HkSq α 0 (un n) ≤ C)
    (hslice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 u z θ) Work.Spaces.Iθ)
    (hmeas : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n => un n z θ) Filter.atTop (𝓝 (u z θ))) :
    Work.Spaces.HkMem α 0 u ∧ Work.Spaces.HkSq α 0 u ≤ C := by
  classical
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hC0 : 0 ≤ C := le_trans (Work.Spaces.HkSq_nonneg α 0 (un 0)) (hSq 0)
  -- (0) the convergence hypothesis in the shape `JConvAux` expects: for `k = 0` the only
  -- mixed slot with `j + i ≤ 0` is `(j, i) = (0, 0)`, i.e. the function itself, and the two
  -- domains agree definitionally.
  have hconvQd : ∀ (j i : ℕ), j + i ≤ 0 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (un n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i u z θ)) := by
    intro j i hji z θ hq
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ i = 0 := by omega
    exact hconv z θ hq
  -- (i) a.e. convergence in `θ` of the integrands, for every fixed `z ∈ Iz`
  have hconv_ae : ∀ z ∈ Work.Spaces.Iz,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α 0 (un n) z θ) Filter.atTop
          (nhds (Work.Spaces.HkIntegrand α 0 u z θ)) :=
    fun z hz => Work.FTS_EllLimOK.JConvAux.ae_tendsto_HkIntegrand_slice
      (α := α) (k := 0) (Ψn := un) (Ψ := u) hconvQd hz
  -- (ii) Fatou in `θ`, in the `ℝ≥0∞`-form, for every fixed `z ∈ Iz`
  have hGle : ∀ z ∈ Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        ≤ Filter.liminf (fun n => ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (un n) z θ))
              Filter.atTop := by
    intro z hz
    exact Work.FTS_EllLimOK.JConvAux.ofReal_integral_le_liminf_ofReal_integral
      (a := fun n θ => Work.Spaces.HkIntegrand α 0 (un n) z θ)
      (A := fun θ => Work.Spaces.HkIntegrand α 0 u z θ)
      (fun n => (hMem n).1 z hz)
      (fun n θ => Work.Spaces.HkIntegrand_nonneg α 0 (un n) z θ)
      (hslice z hz).aestronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ)
      (hconv_ae z hz)
  -- (iii) the `z`-function `z ↦ ∫⁻_θ ofReal (integrand u z θ)` is a.e. measurable, by Fubini
  have hmeas_lin : AEMeasurable
      (fun z => ∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    AEMeasurable.lintegral_prod_right
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ))
      hmeas.ennreal_ofReal
  -- (iv) hence so is the real `z`-function `z ↦ ∫_θ integrand u z θ`
  have hzmeas : AEMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine hmeas_lin.ennreal_toReal.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIz] with z hz
    exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ)
      (hslice z hz).aestronglyMeasurable).symm
  -- (v) Fatou in `z`
  have hFatouZ := MeasureTheory.lintegral_liminf_le'
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) (u := Filter.atTop)
    (f := fun n z => ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (un n) z θ))
    (fun n => ((hMem n).2).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hchain : (∫⁻ z, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) ≤ ENNReal.ofReal C := by
    refine le_trans (MeasureTheory.lintegral_mono_ae ?_) (le_trans hFatouZ ?_)
    · rw [MeasureTheory.ae_restrict_iff' hIz]
      exact Filter.Eventually.of_forall fun z hz => hGle z hz
    · rw [Filter.liminf_eq_iSup_iInf_of_nat]
      refine iSup_le fun n => ?_
      calc (⨅ i, ⨅ (_ : i ≥ n), (∫⁻ z, ENNReal.ofReal
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (un i) z θ)
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)))
          ≤ (∫⁻ z, ENNReal.ofReal
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (un n) z θ)
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
            le_trans (iInf_le _ n) (iInf_le _ le_rfl)
        _ = ENNReal.ofReal (Work.Spaces.HkSq α 0 (un n)) :=
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMem n).2)
              (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg
                (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 (un n) z θ))).symm
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hSq n)
  -- (vi) finiteness of that lintegral gives the `z`-integrability of the slice integrals:
  -- the second half of `HkMem α 0 u`
  have hzmem : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      Work.Spaces.Iz := by
    refine ⟨hzmeas.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ))]
    exact lt_of_le_of_lt hchain ENNReal.ofReal_lt_top
  -- (vii) and it gives the bound on `HkSq α 0 u` as well
  have hsq : Work.Spaces.HkSq α 0 u ≤ C := by
    have h4 : Work.Spaces.HkSq α 0 u
        = (∫⁻ z, ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)).toReal := by
      rw [show Work.Spaces.HkSq α 0 u
          = (∫ z in Work.Spaces.Iz,
              ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) from rfl]
      exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg
          (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ))
        hzmeas.aestronglyMeasurable
    rw [h4]
    exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain)
      (by rw [ENNReal.toReal_ofReal hC0])
  exact ⟨⟨hslice, hzmem⟩, hsq⟩

end Work.FTS_EllLimOK.PkgJets
