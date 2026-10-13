/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/EpsMem_and_EpsSq_le_of_ae_tendsto_mem.lean`

The weighted space `X` of the `ε`-scheme is closed under a.e. pointwise limits:

> if every `A m` is a member of `X` with `EpsSq α (A m) ≤ B` and `A m → Alim` pointwise a.e. on
> the domain `DomM`, then `Alim` is a member of `X` and `EpsSq α Alim ≤ B`.

This is the `hlimP`-type closure used by the limit step of the scheme.  The proof is Fatou's
lemma for the `ℝ≥0∞`-valued size `epsL2` (`EpsLocalPStar.epsL2`, the junk-free form of `EpsSq`).

One subtlety is specific to the *hypotheses* here (as opposed to the sibling
`VolterraAux.EpsMem_and_EpsSq_le_of_tendsto_ae`, which assumes a.e. strong measurability `AK2` of
each `A m`): `EpsMem α (A m)` gives a.e. strong measurability only of the *square*
`((A m)·epsW)²`, not of `(A m)·epsW` itself.  That is exactly what the argument needs: Fatou is
applied to the squared weighted profiles, and the a.e. limit `(Alim·epsW)²` of the a.e. strongly
measurable squares is itself a.e. strongly measurable, which (together with Fatou's finiteness
bound) *is* `EpsMem α Alim`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

set_option autoImplicit false

theorem EpsMem_and_EpsSq_le_of_ae_tendsto_mem {α B : ℝ} (hB : 0 ≤ B)
    {A : ℕ → Work.FTS.Galerkin.Fn} {Alim : Work.FTS.Galerkin.Fn}
    (hmem : ∀ m : ℕ, Work.FTS.StrongEps.EpsMem α (A m))
    (hbd : ∀ m : ℕ, Work.FTS.StrongEps.EpsSq α (A m) ≤ B)
    (hlim : Filter.Eventually (fun p : ℝ × ℝ =>
        Filter.Tendsto (fun m : ℕ => A m p.1 p.2) Filter.atTop (nhds (Alim p.1 p.2)))
      (MeasureTheory.ae Work.FTS.StrongEps.EpsLocalPStar.DomM)) :
    Work.FTS.StrongEps.EpsMem α Alim ∧ Work.FTS.StrongEps.EpsSq α Alim ≤ B := by
  -- ### the weighted sequence converges a.e. to the weighted limit
  have hlimW : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
      Filter.Tendsto (fun m : ℕ => A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
        Filter.atTop (nhds (Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)) :=
    hlim.mono fun p hp => hp.mul_const _
  -- ### the squared weighted profiles are a.e. strongly measurable
  have haesm : ∀ m : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      Work.FTS.StrongEps.EpsLocalPStar.DomM := fun m =>
    (Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2.mp (hmem m)).aestronglyMeasurable
  have haesmLim : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      Work.FTS.StrongEps.EpsLocalPStar.DomM :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop haesm
      (hlimW.mono fun p hp => hp.pow 2)
  -- ### Fatou for the `ℝ≥0∞`-valued size
  have hmeas : ∀ m : ℕ, AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
      Work.FTS.StrongEps.EpsLocalPStar.DomM := fun m =>
    ((haesm m).aemeasurable).ennreal_ofReal
  have hpt : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
      ENNReal.ofReal ((Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ≤ Filter.liminf (fun m : ℕ =>
            ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
          Filter.atTop := by
    filter_upwards [hlimW] with p hp
    have h1 : Filter.Tendsto (fun m : ℕ =>
        ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
        Filter.atTop
        (nhds (ENNReal.ofReal ((Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto
        ((Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)).comp (hp.pow 2)
    rw [h1.liminf_eq]
  have hfatou : Work.FTS.StrongEps.EpsLocalPStar.epsL2 α Alim
      ≤ Filter.liminf (fun m : ℕ => Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (A m))
          Filter.atTop := by
    unfold Work.FTS.StrongEps.EpsLocalPStar.epsL2
    exact (MeasureTheory.lintegral_mono_ae hpt).trans
      (MeasureTheory.lintegral_liminf_le' hmeas)
  have hbound : ∀ m : ℕ, Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (A m) ≤ ENNReal.ofReal B :=
    fun m => Work.FTS.StrongEps.EpsLocalPStar.epsL2_le_ofReal_of_mem (hmem m) (hbd m)
  have hb : Filter.liminf (fun m : ℕ => Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (A m))
      Filter.atTop ≤ ENNReal.ofReal B :=
    Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun m => hbound m)
  have hL2 : Work.FTS.StrongEps.EpsLocalPStar.epsL2 α Alim ≤ ENNReal.ofReal B :=
    hfatou.trans hb
  -- ### membership and the bound
  have hmemLim : Work.FTS.StrongEps.EpsMem α Alim := by
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2]
    refine ⟨haesmLim, ?_⟩
    exact (MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun p => sq_nonneg _)).mpr
        (lt_of_le_of_lt hL2 ENNReal.ofReal_lt_top)
  exact ⟨hmemLim,
    Work.FTS.StrongEps.EpsLocalPStar.EpsSq_le_of_epsL2_le_of_mem hB hmemLim hL2⟩

end Work.FTS.EpsEngine
