/-
# The two-dimensional radial integration by parts

The lemma `zIbpTwoD` is the `θ`-integrated form of the radial integration by parts
`radialIbpWild`:

  `∫_0^∞ w(z)² φ(z,θ) (z ∂_zψ(z,θ)) dz
     = ∫_0^∞ w(z)² (-(z ∂_zφ(z,θ)) - ((z-3)/(1+z)) φ(z,θ)) ψ(z,θ) dz`

for almost every `θ ∈ Iθ` (the hypotheses `hφ`, `hψ` are the `C¹`-regularity of the two
`z`-slices and `hf0`, `hf1` the vanishing of the flux `z w² φ ψ` at `0⁺` and at `+∞`), then
integrated once more over `θ`.

The route is the same as in the sibling `thetaIbpTwoD`, with the roles of `z` and `θ`
exchanged:

* the slicewise identities for a.e. `θ` are supplied by the (proved) one-dimensional
  `radialIbpWild`; the a.e.-slice integrability hypotheses come from the two *joint*
  integrability hypotheses `hint1`, `hint2` on `Iz ×ˢ Iθ` by Fubini
  (`MeasureTheory.Integrable.prod_left_ae`);
* the two-dimensional integrals are rewritten as the `θ`-outer iterated integrals by
  `MeasureTheory.setIntegral_prod` followed by `MeasureTheory.integral_integral_swap`,
  and the a.e. slice identities are integrated with `MeasureTheory.setIntegral_congr_ae`;
* `Iz = [0,∞)` and `Ioi 0` differ by the null set `{0}`, so the `z`-integrals over the two
  sets agree (`MeasureTheory.Ioi_ae_eq_Ici`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Prop.radialIbpWild

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-- **Fubini for the domain `Iz ×ˢ Iθ`, `θ`-outer**: the two-dimensional integral over
`Iz ×ˢ Iθ` equals the iterated integral with the `z`-integration innermost. -/
theorem setIntegral_prod_swap_IzIθ (F : ℝ × ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, F p)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, F (z, θ) := by
  have h1 : (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, F p)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F (z, θ) :=
    MeasureTheory.setIntegral_prod F hF
  rw [h1]
  have hInt : MeasureTheory.Integrable (Function.uncurry (fun z θ : ℝ => F (z, θ)))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hF
  exact MeasureTheory.integral_integral_swap hInt

/-- Integrability on `Iz ×ˢ Iθ` gives integrability of almost every `θ`-slice on `Ioi 0`
(note that a.e. `θ` lies in `Iθ`, and that `Ioi 0 ⊆ Iz`; the point `z = 0` is irrelevant). -/
theorem ae_integrableOn_slice_Ioi_of_integrableOn_prod {F : ℝ × ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => F (z, θ)) (Set.Ioi 0) := by
  have hF' : MeasureTheory.Integrable F
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hF
  filter_upwards [MeasureTheory.Integrable.prod_left_ae hF'] with θ hθ
  exact MeasureTheory.IntegrableOn.mono_set hθ (fun x hx => by
    simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    exact le_of_lt hx)

theorem zIbpTwoD {φ ψ : ℝ → ℝ → ℝ}
    (hint1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * φ p.1 p.2
      * (p.1 * deriv (fun z' => ψ z' p.2) p.1)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (-(p.1 * deriv (fun z' => φ z' p.2) p.1) - ((p.1 - 3) / (1 + p.1)) * φ p.1 p.2)
      * ψ p.1 p.2) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hφ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ContDiffOn ℝ 1 (fun z => φ z θ) (Set.Ioi 0))
    (hψ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ContDiffOn ℝ 1 (fun z => ψ z θ) (Set.Ioi 0))
    (hf0 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), Filter.Tendsto
      (fun z => z * (Work.Spaces.w z) ^ 2 * φ z θ * ψ z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hf1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), Filter.Tendsto
      (fun z => z * (Work.Spaces.w z) ^ 2 * φ z θ * ψ z θ) Filter.atTop (nhds 0)) :
    (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2 * φ p.1 p.2
        * (p.1 * deriv (fun z' => ψ z' p.2) p.1))
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * (-(p.1 * deriv (fun z' => φ z' p.2) p.1) - ((p.1 - 3) / (1 + p.1)) * φ p.1 p.2)
          * ψ p.1 p.2 := by
  -- both sides become `θ`-outer iterated integrals
  have hL := setIntegral_prod_swap_IzIθ _ hint1
  have hR := setIntegral_prod_swap_IzIθ _ hint2
  rw [hL, hR]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
  -- move all the almost-everywhere-in-`θ` hypotheses to the ambient measure
  have hφ' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp hφ
  have hψ' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp hψ
  have hf0' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp hf0
  have hf1' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp hf1
  have hs1' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp
    (ae_integrableOn_slice_Ioi_of_integrableOn_prod hint1)
  have hs2' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp
    (ae_integrableOn_slice_Ioi_of_integrableOn_prod hint2)
  filter_upwards [hφ', hψ', hf0', hf1', hs1', hs2'] with θ a b c d e f hmem
  -- the one-dimensional radial integration by parts on the slice at `θ`
  have h := radialIbpWild (a hmem) (b hmem) (e hmem) (f hmem) (c hmem) (d hmem)
  calc
    (∫ z in Work.Spaces.Iz, (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * φ p.1 p.2
        * (p.1 * deriv (fun z' => ψ z' p.2) p.1)) (z, θ))
        = ∫ z in Set.Ioi 0, (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * φ p.1 p.2
            * (p.1 * deriv (fun z' => ψ z' p.2) p.1)) (z, θ) :=
          (MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0:ℝ)))).symm
    _ = ∫ z in Set.Ioi 0, (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (-(p.1 * deriv (fun z' => φ z' p.2) p.1) - ((p.1 - 3) / (1 + p.1)) * φ p.1 p.2)
          * ψ p.1 p.2) (z, θ) := h
    _ = ∫ z in Work.Spaces.Iz, (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (-(p.1 * deriv (fun z' => φ z' p.2) p.1) - ((p.1 - 3) / (1 + p.1)) * φ p.1 p.2)
          * ψ p.1 p.2) (z, θ) :=
          MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0:ℝ)))

end Work.FTS.EllipticEst.Prop
