/-
Copyright: work module for the Elgindi finite-time singularity project.

# The single mixed slot of `ℋ⁴`

For a datum `f` which is `C^∞` on the open quadrant and in the weighted space `ℋ⁴`
(`Work.FTS.EllipticEst.SmoothOpen f` and `Work.Spaces.HkMem α 4 f`), and for every
*single* mixed slot `D_z^j D_θ^i f` with `1 ≤ i` and `i + j ≤ 4`, the module proves
the three facts needed by the "sup port" assembly:

* its weighted `L²`-square (integration performed in the order `∫_θ ∫_z`) is at most
  `HkSq α 4 f` — it is one summand of the nonnegative `ℋ⁴`-integrand;
* the partially integrated function `θ ↦ ∫_z (D_z^jD_θ^i f · W)²` is integrable on `Iθ`;
* for almost every angle `θ` the radial slice `z ↦ (D_z^jD_θ^i f)² w²` is integrable
  on `Iz`.

Route.  `Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open` gives Tonelli for the whole
`ℋ⁴`-integrand of an open-class datum: `∫_θ ∫_z HkIntegrand α 4 f = HkSq α 4 f`, the
partially integrated `HkIntegrand` is `θ`-integrable, and for almost every `θ` its
radial slice is `z`-integrable.  Since a single mixed slot is one nonnegative summand of
`HkIntegrand` (`Work.Spaces.sq_le_HkIntegrand_mixed`), the a.e. finiteness of the radial
slice of the slot follows by dominated integrability, and the conversion from the slot
`(mixed · W)²` to `mixed² w²` is the identity
`sin(2θ)^γ · (mixed · W)² = mixed² w²` valid at every interior angle `θ ∈ (0,π/2)`
(an angular set of full measure in `Iθ`).  The `θ`-outer partial integral is then
dominated by the `θ`-integrable function `θ ↦ ∫_z HkIntegrand α 4 f z θ`, and a monotone
comparison of the iterated integrals finishes the first conjunct.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.SupPort

open MeasureTheory Set Filter
open scoped Real Topology

theorem slotM_open (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) ≤ Work.Spaces.HkSq α 4 f
    ∧ MeasureTheory.IntegrableOn (fun θ => ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ
    ∧ (∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun z => (Work.Spaces.mixed j i f z θ) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) := by
  classical
  -- Tonelli for the whole `ℋ⁴`-integrand, in the order `∫_θ ∫_z`
  obtain ⟨hHk_eq, hHk_int, hHk_slice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hf hmem
  -- almost every angle is interior
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π/2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0:ℝ))
      (b := Real.pi/2)] with σ h _
    exact h.mpr ‹σ ∈ Work.Spaces.Iθ›
  -- a.e. strong measurability of the uncurried weighted slot square
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      ((((hf.mixed j i).continuousOn).mul (Work.FTS.H2.continuousOn_Wt_Qd α)).pow 2)
  have hslice_meas : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.AEStronglyMeasurable
        (fun z => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := haesm.prodMk_right
  have hAESM_outer : MeasureTheory.AEStronglyMeasurable
      (fun θ => ∫ z in Work.Spaces.Iz, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := (haesm.prod_swap).integral_prod_right'
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iz)
    simpa only [Function.uncurry, Prod.swap_prod_mk] using h
  -- third conjunct: a.e. radial-slice integrability of `(D_z^j D_θ^i f)² w²`
  have hconv : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.mixed j i f z θ) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    filter_upwards [hHk_slice, hslice_meas, haeθ] with θ hHkint hmeas hθ
    have hs : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hgint : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz :=
      hHkint.mono' hmeas (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij)
    have hSS : (Real.sin (2*θ)) ^ (Work.Spaces.gam α)
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) = 1 := by
      rw [← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero]
    have hkey : ∀ z : ℝ, (Real.sin (2*θ)) ^ (Work.Spaces.gam α) * (Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 := by
      intro z
      have hWtsq : (Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.w z) ^ 2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) := by
        simpa [Work.Spaces.Wt, Work.Spaces.wTheta] using Work.FTS.H2.Wt_sq_Ioo α z θ hθ
      calc (Real.sin (2*θ)) ^ (Work.Spaces.gam α) * (Work.Spaces.Wt α z θ) ^ 2
          = (Real.sin (2*θ)) ^ (Work.Spaces.gam α)
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α))) := by rw [hWtsq]
        _ = ((Real.sin (2*θ)) ^ (Work.Spaces.gam α)
            * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α))) * (Work.Spaces.w z) ^ 2 := by ring
        _ = (Work.Spaces.w z) ^ 2 := by rw [hSS, one_mul]
    exact MeasureTheory.IntegrableOn.congr_fun
      (hgint.const_mul ((Real.sin (2*θ)) ^ (Work.Spaces.gam α)))
      (fun z _ => by
        calc (Real.sin (2*θ)) ^ (Work.Spaces.gam α)
              * (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.mixed j i f z θ) ^ 2
              * ((Real.sin (2*θ)) ^ (Work.Spaces.gam α) * (Work.Spaces.Wt α z θ) ^ 2) := by ring
          _ = (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by rw [hkey])
      measurableSet_Ici
  -- second conjunct: the partially integrated slot is `θ`-integrable
  have hGint : MeasureTheory.IntegrableOn
      (fun θ => ∫ z in Work.Spaces.Iz, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      Work.Spaces.Iθ := by
    refine Integrable.mono' hHk_int hAESM_outer ?_
    filter_upwards [hHk_slice] with θ hHkint
    have hle : (∫ z in Work.Spaces.Iz, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ z in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f z θ :=
      integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hHkint
        (Eventually.of_forall fun z => Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij)
    rw [Real.norm_of_nonneg (integral_nonneg fun z => sq_nonneg _)]
    exact hle
  -- first conjunct: monotone comparison of the two iterated integrals
  refine ⟨?_, hGint, hconv⟩
  have hle : (fun θ => ∫ z in Work.Spaces.Iz, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => ∫ z in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f z θ) := by
    filter_upwards [hHk_slice] with θ hHkint
    exact integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hHkint
      (Eventually.of_forall fun z => Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij)
  calc (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f z θ :=
        integral_mono_ae hGint hHk_int hle
    _ = Work.Spaces.HkSq α 4 f := hHk_eq

end Work.FTS.StrongEps.SupPort
