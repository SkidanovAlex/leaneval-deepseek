import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar.VolterraAux

theorem EpsMem_and_EpsSq_le_of_tendsto_ae {α B : ℝ} (hB : 0 ≤ B)
    {A : ℕ → Work.FTS.Galerkin.Fn} {Alim : Work.FTS.Galerkin.Fn}
    (hAK : ∀ m : ℕ, Work.FTS.StrongEps.EpsLocalPStar.AK2 α (A m))
    (hbd : ∀ m : ℕ, Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (A m) ≤ ENNReal.ofReal B)
    (hlim : Filter.Eventually (fun p : ℝ × ℝ =>
        Filter.Tendsto (fun m : ℕ => A m p.1 p.2) Filter.atTop (nhds (Alim p.1 p.2)))
      (MeasureTheory.ae Work.FTS.StrongEps.EpsLocalPStar.DomM)) :
    Work.FTS.StrongEps.EpsMem α Alim ∧ Work.FTS.StrongEps.EpsSq α Alim ≤ B := by
  -- the weighted sequence converges a.e. to the weighted limit
  have hlimW : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
      Filter.Tendsto (fun m : ℕ => A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
        Filter.atTop (nhds (Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)) :=
    hlim.mono fun p hp => hp.mul_const _
  -- hence the limit is a.e. strongly measurable as well
  have hAKlim : Work.FTS.StrongEps.EpsLocalPStar.AK2 α Alim :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop hAK hlimW
  refine Work.FTS.StrongEps.EpsLocalPStar.EpsMem_and_EpsSq_le_of_epsL2_le hB hAKlim ?_
  -- Fatou: `epsL2` of the limit is at most the `liminf` of the `epsL2`'s of the sequence
  have hmeas : ∀ m : ℕ, AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
      Work.FTS.StrongEps.EpsLocalPStar.DomM := fun m =>
    (((hAK m).pow 2).aemeasurable).ennreal_ofReal
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
  have hfatou : (∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal ((Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ∂Work.FTS.StrongEps.EpsLocalPStar.DomM)
      ≤ Filter.liminf (fun m : ℕ => ∫⁻ p : ℝ × ℝ,
            ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
            ∂Work.FTS.StrongEps.EpsLocalPStar.DomM) Filter.atTop :=
    (MeasureTheory.lintegral_mono_ae hpt).trans (MeasureTheory.lintegral_liminf_le' hmeas)
  have hb : Filter.liminf (fun m : ℕ => Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (A m))
      Filter.atTop ≤ ENNReal.ofReal B :=
    Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hbd)
  exact hfatou.trans hb

end Work.FTS.StrongEps.EpsLocalPStar.VolterraAux
