import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.HProductRule_Zsummand
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set Filter
open scoped Real Topology

/-- Integrability, and the value, of the product-measure integral of the top `D_z`-slot of
`g ∈ ℋ⁴`: `∫_{Iz × Iθ} (D_z⁴ g)² · w² · sin(2θ)^{-η} = L2Sq (D_z⁴ g · w / sin(2θ)^{η/2})`,
with the integrand integrable on the quadrant.

This is the `k = 0` case of the integrability hypothesis of `Work.FTS.H2.T2Hard` for
`Th = Thard g`, and the right-hand side is one of the summands of `HkIntegrand α 4 g`
(the `i = 4` term of its first sum: `Work.Spaces.sq_le_HkIntegrand_z`), so combined with
`Work.Spaces.L2Sq_DzIter_le_HkSq` it bounds the slot by `HkSq α 4 g`.

Route: the `D_z`-slot analogue of `Work.Spaces.bt_prod_integrable` (which does the mixed
slots with the weight `Wt α`).  `(D_z⁴ g)² w² sin(2θ)^{-η}` is jointly continuous on the open
quadrant `(0,∞) × (0,π/2)` and the complement of the quadrant in `Iz × Iθ` is null
(`Work.Spaces.aesm_mixed_Wt_sq_prod` shows this pattern); the angular slices are dominated by
the integrable slice `HkIntegrand α 4 g (z, ·)` (via `sq_le_HkIntegrand_z`) and the outer
integral by `hmem.2`, so `Work.Spaces.integrable_prod_of_iterated` gives the integrability and
the identification with the iterated integral.  The pointwise identity
`(D_z⁴ g)² w² sin(2θ)^{-η} = (D_z⁴ g · (w / sin(2θ)^{η/2}))²` is `rpow` algebra on `Iθ`
(`0 ≤ sin(2θ)`, `Work.Spaces.bt_rpow_sq`, `Real.rpow_neg`), and
`(volume : Measure (ℝ × ℝ)).restrict (Iz ×ˢ Iθ) = (volume.restrict Iz).prod (volume.restrict Iθ)`
is `Measure.prod_restrict` (`volume = volume.prod volume` definitionally on `ℝ × ℝ`). -/
theorem hard_sq_prod_z (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => (Work.Spaces.DzIter 4 g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.DzIter 4 g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
        = Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 4 g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
  -- The planar Lebesgue measure restricted to the quadrant is the product of the restricted
  -- one-dimensional measures on `Iz` and `Iθ` (`volume = volume.prod volume` definitionally
  -- on `ℝ × ℝ`).
  have hms : (volume : Measure (ℝ × ℝ)).restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      = (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) :=
    (Measure.prod_restrict Spaces.Iz Spaces.Iθ).symm
  -- Fubini–Tonelli inputs for the `D_z⁴`-slot: a.e. strong measurability of the integrand,
  -- integrability of every angular slice and of the iterated integral.
  have hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Spaces.DzIter 4 g p.1 p.2
        * (Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Spaces.eta / 2))) ^ 2)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) :=
    (Spaces.HPRZ.aesm_DzIter_H_weight_prod g hsm 4).pow 2
  obtain ⟨hslice, houter⟩ := Spaces.HPRZ.L2Mem_DzIter_H_weight α g hsm hmem 4 le_rfl
  obtain ⟨hFint, hFval⟩ := Spaces.integrable_prod_of_iterated
    (μ := volume.restrict Spaces.Iz) (ν := volume.restrict Spaces.Iθ)
    (G := fun z θ => (Spaces.DzIter 4 g z θ
      * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2)
    (fun z θ => sq_nonneg _) hAE
    (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hslice z hz) houter
  -- The two integrands agree on the quadrant.
  have hpt : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
      (Spaces.DzIter 4 g z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2
        = (Spaces.DzIter 4 g z θ) ^ 2 * (Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Spaces.eta)) := fun z _ θ hθ =>
    Spaces.sq_mul_div_rpow _ _ _ _ (Spaces.bt_sin_nonneg hθ) (ne_of_gt Spaces.eta_pos)
  have hmeas : MeasurableSet (Spaces.Iz ×ˢ Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  have hae : (fun p : ℝ × ℝ => (Spaces.DzIter 4 g p.1 p.2) ^ 2 * (Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Spaces.eta)))
      =ᵐ[volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)]
      (fun p : ℝ × ℝ => (Spaces.DzIter 4 g p.1 p.2
        * (Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Spaces.eta / 2))) ^ 2) := by
    filter_upwards [ae_restrict_mem hmeas] with p hp
    exact (hpt p.1 hp.1 p.2 hp.2).symm
  refine ⟨(hms ▸ hFint).congr hae.symm, ?_⟩
  calc ∫ p in Spaces.Iz ×ˢ Spaces.Iθ, (Spaces.DzIter 4 g p.1 p.2) ^ 2 * (Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Spaces.eta))
      = ∫ p in Spaces.Iz ×ˢ Spaces.Iθ, (Spaces.DzIter 4 g p.1 p.2
          * (Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Spaces.eta / 2))) ^ 2 :=
        integral_congr_ae hae
    _ = ∫ p, (Spaces.DzIter 4 g p.1 p.2
          * (Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Spaces.eta / 2))) ^ 2
          ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) :=
        congrArg (fun m : Measure (ℝ × ℝ) => ∫ p, (Spaces.DzIter 4 g p.1 p.2
          * (Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Spaces.eta / 2))) ^ 2 ∂m) hms
    _ = Spaces.L2Sq (fun z θ => Spaces.DzIter 4 g z θ
          * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) := by
        rw [hFval, Spaces.L2Sq]

end Work.FTS.H2
