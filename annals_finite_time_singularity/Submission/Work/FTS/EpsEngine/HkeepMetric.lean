/-
Copyright: work module for the Elginda finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/HkeepMetric.lean`

**The metric clauses of `hkeepIter`/`hlimP`**: the `X = (EpsMem, EpsSq)`-size of a Picard slice
`h₀ + ∫₀^τ F (w_s) ds` is controlled by the datum's size and the size of the increment.

The class invariant `XBall` carries `EpsSq u ≤ R`; the triangle (AM–GM) inequality for `EpsSq`
costs a factor `2`, so the datum must be known at a *smaller* size `R₀` with `2R₀ + 2τ²B ≤ R`.
Both facts are recorded here in the exact form the engine's class preservation needs; the
increment itself is `VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.LimSmoothOpenEngine
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Work.FTS.StrongEps.EpsLocalPStar.VolterraAux

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsLocalPStar
open Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false

/-- **The `X`-size of a sum.**  If both summands are honest (`EpsMem`, plus a.e. strong
measurability of the weighted profiles for the sum) with sizes `R₀` and `L`, then their sum is
honest with size `2R₀ + 2L` — the AM–GM loss of the triangle inequality for `EpsSq`. -/
theorem EpsMem_EpsSq_add_le {α R₀ R L : ℝ} (hR : 2 * R₀ + 2 * L ≤ R)
    {f g : Fn} (hakf : AK α f) (hakg : AK α g) (hf : EpsMem α f) (hh : EpsSq α f ≤ R₀)
    (hg : EpsMem α g) (hg' : EpsSq α g ≤ L) :
    EpsMem α (fun z θ => f z θ + g z θ) ∧
      EpsSq α (fun z θ => f z θ + g z θ) ≤ R := by
  refine ⟨EpsMem_add hakf hakg hf hg, (EpsSq_add_le_of_mem hf hg).trans ?_⟩
  linarith

/-- **The `X`-size of a Picard slice.**  If the datum has size `R₀` and the increment
`G = ∫₀^τ F (w_s) ds` has size `≤ τ * (τ * B)` (bounded in `epsL2` by `B` along the curve), then
`h₀ + G` is honest of size `R` as soon as `2R₀ + 2 * (τ * (τ * B)) ≤ R`. -/
theorem EpsMem_EpsSq_add_intervalIntegral_le {α τ B R₀ R : ℝ} (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (hR : 2 * R₀ + 2 * (τ * (τ * B)) ≤ R) {G : ℝ → Fn} {h₀ : Fn}
    (hak : AK α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ))
    (hak₀ : AK α h₀) (hh₀ : EpsMem α h₀) (hR₀ : EpsSq α h₀ ≤ R₀)
    (hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2 * epsW α p.2.1 p.2.2)
      ((volume.restrict (Set.uIoc 0 τ)).prod DomM))
    (hbd : ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 τ)), epsL2 α (G s) ≤ ENNReal.ofReal B) :
    EpsMem α (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, G s z θ) ∧
      EpsSq α (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, G s z θ) ≤ R := by
  have hG := EpsMem_and_EpsSq_intervalIntegral_le (α := α) (τ := τ) (B := B) hτ hB hmeas hbd
  exact EpsMem_EpsSq_add_le hR hak₀ hak hh₀ hR₀ hG.1 hG.2

end Work.FTS.EpsEngine
