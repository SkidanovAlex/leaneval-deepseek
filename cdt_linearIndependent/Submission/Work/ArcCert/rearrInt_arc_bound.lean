import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.CNum.doubleInterval_block_bound
import Submission.Work.CNum.integrableOn_max_prod
import Submission.Work.CNum.blkDef

/-! Guidance from the project lead (the requester):

# Shared arc certificate, part 1 (used by BOTH Theorem C (CNum, H1) and Theorem A (ANum, H25))
Blockwise version of `Work.CNum.rearrInt_bridge` (Submission/Work/CNum/rearrInt_bridge.lean and its
helpers `doubleInterval_block_bound`, `blk_*`, `integrableOn_max_prod`): unfold `rearrInt` into the
finite sum over block pairs (k,k'), and apply the single-pair double-interval bound with TWO possibly
different functions `circleLog (φ k)`, `circleLog (φ k')` (generalise H1's lemma: its proof does not
use that the two functions coincide). Import and reuse H1's modules; do not rebuild them.
-/

namespace Work.ArcCert

open Submission.CDTPlan
open MeasureTheory
open scoped BigOperators

/-- Integrability on the half-open unit square of `(s,t) ↦ max (g₁ s) (g₂ t)` for two functions
that are continuous on `[0,1]`.  This is the two-function generalisation of
`Work.CNum.integrableOn_max_prod`: the proof never uses that the two functions coincide. -/
theorem integrableOn_max_prod_two {g₁ g₂ : ℝ → ℝ}
    (h₁ : ContinuousOn g₁ (Set.Icc (0:ℝ) 1)) (h₂ : ContinuousOn g₂ (Set.Icc (0:ℝ) 1)) :
    IntegrableOn (fun p : ℝ × ℝ => max (g₁ p.1) (g₂ p.2))
      (Set.Ioc (0:ℝ) 1 ×ˢ Set.Ioc (0:ℝ) 1) (volume.prod volume) := by
  set A : Set (ℝ × ℝ) := Set.Ioc (0:ℝ) 1 ×ˢ Set.Ioc (0:ℝ) 1 with hA
  set S : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 with hS
  have hmemS : ∀ p : ℝ × ℝ, p ∈ S ↔ p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2 ∈ Set.Icc (0:ℝ) 1 := by
    intro p; rw [hS]; exact Set.mem_prod
  have hmemA : ∀ p : ℝ × ℝ, p ∈ A ↔ p.1 ∈ Set.Ioc (0:ℝ) 1 ∧ p.2 ∈ Set.Ioc (0:ℝ) 1 := by
    intro p; rw [hA]; exact Set.mem_prod
  have hAS : A ⊆ S := by
    intro p hp
    rw [hmemS, hmemA] at *
    exact ⟨Set.Ioc_subset_Icc_self hp.1, Set.Ioc_subset_Icc_self hp.2⟩
  have hcont1 : ContinuousOn (fun p : ℝ × ℝ => g₁ p.1) S :=
    h₁.comp' continuous_fst.continuousOn (fun p hp => ((hmemS p).mp hp).1)
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => g₂ p.2) S :=
    h₂.comp' continuous_snd.continuousOn (fun p hp => ((hmemS p).mp hp).2)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => max (g₁ p.1) (g₂ p.2)) S := by
    simpa using hcont1.sup hcont2
  have hScompact : IsCompact S := by rw [hS]; exact isCompact_Icc.prod isCompact_Icc
  have hAmeas : MeasurableSet A := by rw [hA]; exact measurableSet_Ioc.prod measurableSet_Ioc
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => max (g₁ p.1) (g₂ p.2))
      ((volume.prod volume).restrict A) :=
    hcont.aestronglyMeasurable_of_subset_isCompact hScompact hAmeas hAS
  obtain ⟨C, hC⟩ := hScompact.exists_bound_of_continuousOn hcont
  refine IntegrableOn.of_bound ?_ haesm C ?_
  · rw [hA, Measure.prod_prod, Real.volume_Ioc]
    simp
  · filter_upwards [ae_restrict_mem hAmeas] with p hp
    exact hC p (hAS hp)

theorem rearrInt_arc_bound {l N : ℕ} (hN : 0 < N) (w : Fin (l + 1) → ℝ) (hw : ∀ k, 0 ≤ w k)
    (φ : Fin (l + 1) → ℂ → ℂ) (G : Fin (l + 1) → Fin N → ℝ)
    (hcont : ∀ k, ContinuousOn (circleLog (φ k)) (Set.Icc 0 1))
    (h : ∀ (k : Fin (l + 1)) (j : Fin N), ∀ t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N), circleLog (φ k) t ≤ G k j) :
    rearrInt w φ ≤ ∑ k, ∑ k', w k * w k' *
      ∑ j, ∑ j', (1 / (N : ℝ) ^ 2) * max (G k j) (G k' j') := by
  simp only [rearrInt]
  refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun k' _ => ?_))
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hw k) (hw k'))
  refine Work.CNum.doubleInterval_block_bound hN
    (fun s t => max (circleLog (φ k) s) (circleLog (φ k') t))
    (fun j j' => max (G k j) (G k' j')) ?_ ?_
  · exact integrableOn_max_prod_two (hcont k) (hcont k')
  · intro j j' s hs t ht
    exact max_le_max (h k j s (Set.Ioc_subset_Icc_self hs))
      (h k' j' t (Set.Ioc_subset_Icc_self ht))

end Work.ArcCert
