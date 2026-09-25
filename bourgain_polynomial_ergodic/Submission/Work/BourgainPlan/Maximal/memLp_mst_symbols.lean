import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.memLp_comp_iwRep
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp

namespace Work.BourgainPlan.Maximal

open MeasureTheory

/-- A continuous function is `MemLp ⊤` against Lebesgue measure restricted to the fundamental
domain `Ioc (-1/2) (1/2)`: that domain has finite measure and `g` is bounded on its compact
closure `Icc (-1/2) (1/2)`.  This is exactly the hypothesis consumed by `memLp_comp_iwRep`. -/
lemma memLp_restrict_Ioc_of_continuous {g : ℝ → ℂ} (hg : Continuous g) :
    MeasureTheory.MemLp g ⊤ (MeasureTheory.volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2))) := by
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2))) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-(1 / 2) : ℝ) (1 / 2)) hg.continuousOn
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x (Set.Ioc_subset_Icc_self hx)

/-- **The `L^∞`-classes of the MST symbols are available**: for `g := polyWeylKernel P N` and `g := polyProfile P N` (both continuous on `ℝ`) and for a continuous bump `η` scaled by `c`, the functions `ξ ↦ g (iwRep ξ)` and `ξ ↦ η (c · iwRep ξ)` are `MemLp ⊤` on the circle.  This discharges the `MemLp`-side hypotheses of the MST §3–§5 estimates (`mstWeyl`, `mstProf`, `mstEta`), through `memLp_comp_iwRep` — no measurability statement about `iwRep` is needed. -/
theorem memLp_mst_symbols (P : Polynomial ℤ) (N : ℕ) (c : ℝ) (η : ℝ → ℂ) (hη : Continuous η) :
    MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstWeyl P N) ⊤
        (AddCircle.haarAddCircle (T := 1)) ∧
      MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstProf P N) ⊤
        (AddCircle.haarAddCircle (T := 1)) ∧
      MeasureTheory.MemLp (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
          η (c * Work.BourgainPlan.Maximal.iwRep ξ)) ⊤
        (AddCircle.haarAddCircle (T := 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the density symbol `m_N = polyWeylKernel P N`, read on the circle
    exact memLp_comp_iwRep (g := polyWeylKernel P N)
      (memLp_restrict_Ioc_of_continuous (continuous_polyWeylKernel P N))
  · -- the oscillatory profile `Φ_N = polyProfile P N`, read on the circle
    exact memLp_comp_iwRep (g := polyProfile P N)
      (memLp_restrict_Ioc_of_continuous (continuous_polyProfile P N))
  · -- a continuous bump scaled by `c`
    exact memLp_comp_iwRep (g := fun x : ℝ => η (c * x))
      (memLp_restrict_Ioc_of_continuous (hη.comp (continuous_const.mul continuous_id)))

end Work.BourgainPlan.Maximal
