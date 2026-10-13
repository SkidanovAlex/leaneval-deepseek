import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.CAux.integrableOn_GamK
import Submission.Work.FM.Core
import Submission.Work.FM.Core2
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L₁₂`-density of the profile `F_*` with exponent `pExp α = 3α`

Three facts about the profile `F_*(z,θ) = β (Γ(θ)/c(β)) 2z/(1+z)²` with `β = pExp α = 3α`:

* the angular density `θ ↦ K(θ) F_*(s,θ)/s` of `L₁₂` is integrable on `Iθ = [0,π/2]` for
  every `s > 0` (it is a constant multiple of the integrand `Γ(β)K` of the normalisation
  constant `c`);
* the radial density `s ↦ ∫_θ K(θ) F_*(s,θ)/s` is integrable on `(0,∞)`;
* that density is the elementary function `2β/(1+s)²`.

The last two are the `β = pExp α` instances of `Construction.L12dens_Fstar` and of
`MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn`.  The hypotheses `0 < α`, `α ≤ 1/3`
are exactly what is needed to discharge `0 < β` and `β ≤ 1`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXR5L.L12fAux

/-- The exponent `β = pExp α = 3α` of `F_*` satisfies `0 < β` under `0 < α`, and `β ≤ 1`
under `α ≤ 1/3`; both are the hypotheses needed to identify the `L₁₂`-density of `F_*`. -/
theorem Fstar_dens_facts {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    (∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.Construction.Fstar (Work.FTS.Regularity.pExp α) s θ / s)
      Work.Spaces.Iθ) ∧
    (MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)) (Set.Ioi 0)) ∧
    (∀ s : ℝ, 0 < s → Work.FM.L12dens Work.Spaces.K
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) s
      = 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2) := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  refine ⟨?_, ?_, ?_⟩
  · -- the angular density is a constant multiple of `Γ(β)K`, integrable on `Iθ`
    intro s _hs
    have hGK : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ * Work.Spaces.K θ)
        Work.Spaces.Iθ := Work.Spaces.CAux.integrableOn_GamK _ hβ
    have hscaled : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            * (Work.FM.Fstar s / s))
          * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ * Work.Spaces.K θ))
        Work.Spaces.Iθ := hGK.const_mul _
    refine hscaled.congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [Work.Construction.Fstar]
    ring
  · -- the radial density is `2β/(1+s)²`, integrable on `(0,∞)`
    change MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
      (Set.Ioi 0)
    exact Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hβ hβ1 0 le_rfl
  · -- the radial density is the elementary function `2β/(1+s)²`
    intro s hs
    have hkey := Work.Construction.L12dens_Fstar (α := Work.FTS.Regularity.pExp α) hβ hβ1 s
    have hFs : Work.FM.Fstar s / s = 2 / (1 + s) ^ 2 := by
      rw [Work.FM.Fstar]
      field_simp
    change Work.Construction.L12dens (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) s
      = 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
    rw [hkey, hFs]
    ring

end Work.FTS_RegExport.RXR5L.L12fAux
