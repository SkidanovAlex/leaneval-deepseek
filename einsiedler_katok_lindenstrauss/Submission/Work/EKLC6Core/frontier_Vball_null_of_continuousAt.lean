import Mathlib
import Submission.Work.Misiurewicz.exists_null_frontier_Vball_radius

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open Work.EKLContract Work.EKLComp

noncomputable section

theorem frontier_Vball_null_of_continuousAt (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure ν] (z : Work.EKLContract.X3) {r : ℝ} (hr : 0 < r)
    (hcont : ContinuousAt (fun t : ℝ => (ν (Work.EKLComp.Vball t z)).toReal) r) :
    ν (frontier (Work.EKLComp.Vball r z)) = 0 := by
  have hfin_fr : ν (frontier (Vball r z)) ≠ ⊤ := measure_ne_top ν _
  have hfin_Ar : ν (Vball r z) ≠ ⊤ := measure_ne_top ν _
  have hdisj : Disjoint (frontier (Vball r z)) (Vball r z) := by
    have h : Disjoint (interior (Vball r z)) (frontier (Vball r z)) := disjoint_interior_frontier
    rw [(Work.Misiurewicz.isOpen_Vball z hr).interior_eq] at h
    exact h.symm
  have hmeasA : MeasurableSet (Vball r z) := (Work.Misiurewicz.isOpen_Vball z hr).measurableSet
  have hkey : ∀ s : ℝ, r < s → ν (frontier (Vball r z)) + ν (Vball r z) ≤ ν (Vball s z) := by
    intro s hrs
    calc ν (frontier (Vball r z)) + ν (Vball r z)
        = ν (frontier (Vball r z) ∪ Vball r z) := (measure_union hdisj hmeasA).symm
      _ ≤ ν (Vball s z) := by
          apply measure_mono
          intro y hy
          rcases hy with hy | hy
          · exact (Work.Misiurewicz.frontier_Vball_subset z hr hrs hy).1
          · exact Work.Misiurewicz.Vball_mono z (le_of_lt hrs) hy
  have hbound : ∀ s : ℝ, r < s →
      (ν (frontier (Vball r z))).toReal ≤ (ν (Vball s z)).toReal - (ν (Vball r z)).toReal := by
    intro s hrs
    have h := hkey s hrs
    have h1 : (ν (frontier (Vball r z)) + ν (Vball r z)).toReal ≤ (ν (Vball s z)).toReal :=
      ENNReal.toReal_mono (measure_ne_top ν _) h
    rw [ENNReal.toReal_add hfin_fr hfin_Ar] at h1
    linarith
  have hsmall : ∀ ε > 0, (ν (frontier (Vball r z))).toReal < ε := by
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
    have hdist : dist (r + δ / 2) r < δ := by
      rw [Real.dist_eq]
      have h2 : r + δ / 2 - r = δ / 2 := by ring
      rw [h2, abs_of_pos (by linarith : (0 : ℝ) < δ / 2)]
      linarith
    have hh := hδ hdist
    rw [Real.dist_eq] at hh
    have hmono' : (ν (Vball r z)).toReal ≤ (ν (Vball (r + δ / 2) z)).toReal :=
      ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Work.Misiurewicz.Vball_mono z (by linarith)))
    have hsub : (ν (Vball (r + δ / 2) z)).toReal - (ν (Vball r z)).toReal < ε := by
      rwa [abs_of_nonneg (sub_nonneg.mpr hmono')] at hh
    have hb := hbound (r + δ / 2) (by linarith)
    linarith
  have hz : (ν (frontier (Vball r z))).toReal = 0 := by
    refine le_antisymm ?_ ENNReal.toReal_nonneg
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    simpa using hsmall ε hε
  have hof := ENNReal.ofReal_toReal hfin_fr
  rw [hz, ENNReal.ofReal_zero] at hof
  exact hof.symm

end

end Work.EKLC6Core
