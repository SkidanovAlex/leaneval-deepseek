import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set Filter
open scoped Real Topology

/-- Integrability, and the value, of the product-measure integral of a mixed slot of
`g ∈ ℋ⁴` in the normal form used by `Work.FTS.H2.T2Hard`:
`∫_{Iz × Iθ} (D_z^j D_θ^i g)² · w² · sin(2θ)^{-γ} = L2Sq (D_z^j D_θ^i g · Wt α)`, for
`1 ≤ i`, `i + j ≤ 4`.

This is `Work.Spaces.bt_prod_integrable` (which gives integrability of
`(D_z^j D_θ^i g · Wt α)²` on `(volume.restrict Iz).prod (volume.restrict Iθ)` and its value
`L2Sq (D_z^j D_θ^i g · Wt α)`) rewritten in the normal form `(mixed j i g)² w² sin(2θ)^{-γ}`
on `Iz ×ˢ Iθ` with the ambient restricted volume, which is what `T2Hard` asks for as the
`k ≥ 1` cases of its integrability hypothesis for `Th = Thard g`.

Route: `(mixed j i g · Wt α)² = (mixed j i g)² w² sin(2θ)^{-γ}` pointwise a.e. on `Iz ×ˢ Iθ`
(`Work.Spaces.bt_Wt_sq` and `mul_pow`), and
`(volume : Measure (ℝ × ℝ)).restrict (Iz ×ˢ Iθ) = (volume.restrict Iz).prod (volume.restrict Iθ)`
by `Measure.prod_restrict` (with `volume = volume.prod volume` definitionally on `ℝ × ℝ`);
then `Integrable.congr`/`IntegrableOn.congr_fun` and `integral_congr_ae`. -/
theorem hard_sq_prod_mixed (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α 4 g)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.mixed j i g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) := by
  obtain ⟨hint, hval⟩ := Work.Spaces.bt_prod_integrable α g hsm hmem j i hi hij
  -- `Iz ×ˢ Iθ` is a measurable set, and the ambient restricted volume is the product measure.
  have hmeas : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  have hmeasure : (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
    (Measure.prod_restrict Work.Spaces.Iz Work.Spaces.Iθ).symm
  -- The two integrands agree a.e.: `(mixed j i g · Wt α)² = (mixed j i g)² w² sin(2θ)^{-γ}`.
  have hae : (fun p : ℝ × ℝ => (Work.Spaces.mixed j i g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
      =ᵐ[(volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2) := by
    rw [← hmeasure]
    filter_upwards [ae_restrict_mem hmeas] with p hp
    have hθ : p.2 ∈ Work.Spaces.Iθ := hp.2
    rw [mul_pow, Work.Spaces.bt_Wt_sq α p.1 p.2 hα hθ]
    ring
  constructor
  · rw [IntegrableOn, hmeasure]
    exact hint.congr hae.symm
  · rw [hmeasure, integral_congr_ae hae]
    exact hval

end Work.FTS.H2
