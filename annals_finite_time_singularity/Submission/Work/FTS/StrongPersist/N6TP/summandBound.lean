import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSix
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSixTop
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6TP

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/- Per-summand bound of the level-six `D_z`-transport Leibniz expansion with a flat coefficient of order 5.

Context: I am assembling `N6Trans (IP6 1 … 1) α₂ Ct`, whose third clause is T3Clause6: for
`SmoothOpen f`, `WlInfMem α 6 f`, `CoefThMem 5 f`, `HQo α 6 g`, `HkMem α 7 g`, `DecayAll 6 g`,
  `|IP6 1…1 α (fun z θ => f z θ * Dz g z θ) g| ≤ Ct * α^{-1/2} * (WlInf α 6 f + CoefTh 5 f) * Xn6 α g ^ 2`.
`IP6 1…1` unfolds via `ip4_unfold_bound` into leaf slot pairings, so I need the per-slot
`D_z`-transport bound at level six, which I reduce (via `SixRoute.sixExpansion`, the exact Leibniz
expansion `mixed b a (f · D_z g) = Σ_{a₁≤a} Σ_{b₁≤b} C(a,a₁)C(b,b₁) · mixed b₁ a₁ f · mixed (b-b₁+1)(a-a₁) g`)
to this per-summand statement for every Leibniz index `(a₁,b₁)` with `a₁ ≤ a`, `b₁ ≤ b`, `a + b ≤ 6`.

It is true; the pieces are all in the workspace. Hints for the prover (branch on `(a₁,b₁)` and on
`a = 0` vs `1 ≤ a`):
* `(a₁,b₁) = (0,0)`: the integrand is `ρ·f·D_z(mixed b a g)·mixed b a g`; use `fluxFamSix`
  (`a+b ≤ 5`) resp. `fluxFamSixTop` (`a+b = 6`), both in `…N6Trans.SixRoute`, stated as
  `IntegrableOn … (Iz ×ˢ Iθ)` (convert with `Work.FTS.TransportS.prod_restrict_eq`).
* `a₁ = 0`, `b₁ ≥ 1`: `|D_z^{b₁} f| ≤ 1000·WlInf α 6 f` (`L6Core.dzIter_le_WlInf6`, `b₁ ≤ b ≤ 6`);
  then dominate the two `g`-factors by `HkIntegrand α 6 g` either with the weight `canonW eta`
  (when `a = 0`, `T2Sup.canonW_z_slot_le_gen`) or with `canonW (gam α)`
  (`T2Sup.canonW_mixed_slot_le_gen`, `a ≥ 1`), after `|G|·|Y| ≤ (G²+Y²)/2`.
* `1 ≤ a₁ ≤ a`: the σ-gain `Work.FTS.TransportS.flat_mixed_le 5` applied with
  `K := CoefTh 5 f` gives `|mixed b₁ a₁ f| ≤ C·sin(2θ)·CoefTh 5 f` (grades of `CoefTh` by
  `Work.FTS.H2.le_supAbsO`); with `ρ ≤ canonW (gam α)` one has
  `sin(2θ)·ρ ≤ canonW (gam α - 1) = canonW (α/10)`, and `α/10 ≤ eta`, `α/10 ≤ gam α` make both
  `g`-slots compatible with `HkIntegrand α 6 g` (`T2Sup.canonW_z_slot_le_gen` when `a₁ = a`, the
  second factor being the pure slot `D_z^{b-b₁+1} g`; `T2Sup.canonW_mixed_slot_le_gen` when `a₁ < a`),
  again after `|G|·|Y| ≤ (G²+Y²)/2` and `ρ ≤ canonW (gam α)` from `T3SlotAux.IsLeafW.le_canonW`.
* Integrability: `|integrand| ≤ const·HkIntegrand α 6 g` pointwise on the open quadrant and
  `Hon.integrable_HkIntegrand_prod_open` (product-integrability of `HkIntegrand`), plus a.e. strong
  measurability from continuity on the open quadrant (`Work.Spaces.aesm_of_continuousOn_Qd`,
  `Hon.continuousOn_mixed_Qd_open`); the integral bound is then `|∫| ≤ ∫|·| ≤ const·HkSq α 6 g`
  (`HkSq` is the product integral of `HkIntegrand`).
Each `canonW`-slot comparison is stated on the open quadrant (0 < z, 0 < θ < π/2), which is enough
(a null set). -/

/-- **The a.e.-pointwise domination package.**  If `F` is continuous on the open quadrant and
dominated pointwise there by `M · HkIntegrand α 6 g`, then `F` is product-integrable on
`Iz ×ˢ Iθ` (with respect to the product of the two restricted Lebesgue measures) and its
integral is bounded by `M · HkSq α 6 g`.

This is the common bookkeeping step of every non-exceptional Leibniz summand of
`summandBound`: the domination only holds on the open quadrant (`z > 0`), which is conull
inside `Iz ×ˢ Iθ`, and the a.e. strong measurability follows from continuity there. -/
theorem summand_ae_package {α : ℝ} {g : ℝ → ℝ → ℝ} {F : ℝ × ℝ → ℝ} {M : ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hmg : Work.Spaces.HkMem α 6 g)
    (hcont : ContinuousOn F (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ‖F (z, θ)‖ ≤ M * Work.Spaces.HkIntegrand α 6 g z θ) :
    MeasureTheory.Integrable F ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, F p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))| ≤ M * Work.Spaces.HkSq α 6 g := by
  obtain ⟨hHint, hHkval⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (k := 6) hsg hmg
  have haesm : MeasureTheory.AEStronglyMeasurable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd F hcont
  have hdom : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ‖F p‖ ≤ M * Work.Spaces.HkIntegrand α 6 g p.1 p.2 :=
    Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ hθ2 => hpt z θ hz hθ hθ2)
  have hdomint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      M * Work.Spaces.HkIntegrand α 6 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hHint.const_mul M
  have hFint : MeasureTheory.Integrable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hdomint.mono' haesm hdom
  refine ⟨hFint, ?_⟩
  calc |∫ p, F p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ ∫ p, |F p| ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := abs_integral_le_integral_abs
    _ ≤ ∫ p, M * Work.Spaces.HkIntegrand α 6 g p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        refine integral_mono_ae hFint.abs hdomint ?_
        filter_upwards [hdom] with p hp
        simpa only [Real.norm_eq_abs] using hp
    _ = M * Work.Spaces.HkSq α 6 g := by rw [integral_const_mul, hHkval]


end

end Work.FTS.StrongPersist.N6TP
