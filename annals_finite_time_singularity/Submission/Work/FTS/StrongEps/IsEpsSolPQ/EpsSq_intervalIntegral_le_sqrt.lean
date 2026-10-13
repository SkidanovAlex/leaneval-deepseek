import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsSqIntegralAux
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.IsEpsSolPQ

open Work.FTS.StrongEps.EpsLocalPStar

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- `EpsSq` is the single integral of the weighted square against the product measure
`DomM = (volume↾Iz).prod (volume↾Iθ)` (Fubini for the iterated set integral). -/
private theorem EpsSq_eq_integral_DomM {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsMem α f) :
    Work.FTS.StrongEps.EpsSq α f
      = ∫ p : ℝ × ℝ, (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 ∂DomM := by
  have hint : Integrable (fun p : ℝ × ℝ =>
      (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) DomM :=
    EpsMem_iff_integrable2.mp hf
  rw [Work.FTS.StrongEps.EpsSq, DomM]
  exact (MeasureTheory.integral_prod _ hint).symm

theorem EpsSq_intervalIntegral_le_sqrt {α a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    {w : Work.FTS.Galerkin.Fn} {G : ℝ → Work.FTS.Galerkin.Fn}
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => G q.1 q.2.1 q.2.2 * Work.FTS.StrongEps.epsW α q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM))
    (hGmem : Filter.Eventually (fun s : ℝ => Work.FTS.StrongEps.EpsMem α (G s))
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.uIoc a b))))
    (hBd : Filter.Eventually (fun s : ℝ => Work.FTS.StrongEps.EpsSq α (G s) ≤ B)
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.uIoc a b))))
    (hwmem : Work.FTS.StrongEps.EpsMem α w)
    (hw : Filter.Eventually (fun p : ℝ × ℝ => w p.1 p.2 = ∫ s in a..b, G s p.1 p.2)
      (MeasureTheory.ae Work.FTS.StrongEps.EpsLocalPStar.DomM)) :
    Work.FTS.StrongEps.EpsSq α w
      ≤ (∫ s in a..b, Real.sqrt (Work.FTS.StrongEps.EpsSq α (G s))) ^ 2 := by
  classical
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  -- the weighted curve, as a function of the pair `(s, p)`
  set F : ℝ → ℝ × ℝ → ℝ :=
    fun s p => G s p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2 with hF
  -- the parameter measure is finite
  haveI hνfin : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc a b)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc,
      abs_of_nonneg hba]
    exact ENNReal.ofReal_lt_top⟩
  -- the interval integral of a profile is the integral of its weighted slice: the weight is
  -- constant in the parameter
  have hslice : ∀ p : ℝ × ℝ, (∫ s in a..b, G s p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2
      = ∫ s, F s p ∂(MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    intro p
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab, hF]
    exact (MeasureTheory.integral_mul_const (Work.FTS.StrongEps.epsW α p.1 p.2)
      (fun s => G s p.1 p.2)).symm
  -- a.e. in `s`, the integral of the weighted square is the energy of the slice
  have hsq_eq : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      (∫ p, F s p ^ 2 ∂DomM) = Work.FTS.StrongEps.EpsSq α (G s) := by
    refine hGmem.mono fun s hs => ?_
    rw [EpsSq_eq_integral_DomM hs, hF]
  -- a.e. strong measurability of the slice energy
  have haesm : MeasureTheory.AEStronglyMeasurable (fun s => ∫ p, F s p ^ 2 ∂DomM)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    (hmeas.pow 2).integral_prod_right'
  -- the size is bounded by `√B` on the (finite) interval, hence integrable
  have hbdd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      ‖Real.sqrt (∫ p, F s p ^ 2 ∂DomM)‖ ≤ Real.sqrt B := by
    filter_upwards [hsq_eq, hBd] with s heq hle
    rw [heq, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_sqrt_iff hB).mpr hle
  have hint : Integrable (fun s => Real.sqrt (∫ p, F s p ^ 2 ∂DomM))
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    Integrable.of_bound (Real.continuous_sqrt.comp_aestronglyMeasurable haesm) (Real.sqrt B) hbdd
  -- the slices are square-integrable a.e. in the parameter
  have hsq : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      Integrable (fun p : ℝ × ℝ => F s p ^ 2) DomM :=
    hGmem.mono fun s hs => EpsMem_iff_integrable2.mp hs
  -- Minkowski's inequality for the `L²`-norm of the parameter integral
  obtain ⟨_, hmink⟩ := l2_integral_le (μ := DomM)
    (ν := MeasureTheory.volume.restrict (Set.uIoc a b)) (F := F) hmeas hsq hint
  -- the left-hand side is the norm of the parameter integral
  have hLHS : Work.FTS.StrongEps.EpsSq α w
      = ∫ p, (∫ s, F s p ∂(MeasureTheory.volume.restrict (Set.uIoc a b))) ^ 2 ∂DomM := by
    rw [EpsSq_eq_integral_DomM hwmem]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hw] with p hp
    rw [hp, hslice p]
  -- the right-hand side is the interval integral of the slice sizes
  have hRHS : (∫ s, Real.sqrt (∫ p, F s p ^ 2 ∂DomM)
        ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
      = ∫ s in a..b, Real.sqrt (Work.FTS.StrongEps.EpsSq α (G s)) := by
    have h' := hsq_eq
    rw [Set.uIoc_of_le hab] at h'
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
    exact MeasureTheory.integral_congr_ae (h'.mono fun s hs => congrArg Real.sqrt hs)
  calc Work.FTS.StrongEps.EpsSq α w
      = ∫ p, (∫ s, F s p ∂(MeasureTheory.volume.restrict (Set.uIoc a b))) ^ 2 ∂DomM := hLHS
    _ ≤ (∫ s, Real.sqrt (∫ p, F s p ^ 2 ∂DomM)
          ∂(MeasureTheory.volume.restrict (Set.uIoc a b))) ^ 2 := hmink
    _ = (∫ s in a..b, Real.sqrt (Work.FTS.StrongEps.EpsSq α (G s))) ^ 2 := by rw [hRHS]

end Work.FTS.StrongEps.IsEpsSolPQ