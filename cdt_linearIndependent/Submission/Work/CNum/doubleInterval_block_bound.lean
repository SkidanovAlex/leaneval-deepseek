import Mathlib
import Submission.Work.CNum.blkDef
import Submission.Work.CNum.blk_le_doubleSum_indicator
import Submission.Work.CNum.blk_step_integral

namespace Work.CNum

open MeasureTheory
open scoped BigOperators

theorem doubleInterval_block_bound {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ → ℝ) (c : Fin N → Fin N → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Ioc (0:ℝ) 1 ×ˢ Set.Ioc (0:ℝ) 1) (MeasureTheory.volume.prod MeasureTheory.volume))
    (h : ∀ k k' : Fin N, ∀ s ∈ Set.Ioc ((k:ℝ)/N) (((k:ℝ)+1)/N),
        ∀ t ∈ Set.Ioc ((k':ℝ)/N) (((k':ℝ)+1)/N), f s t ≤ c k k') :
    ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f s t ≤
      ∑ k : Fin N, ∑ k' : Fin N, (1/(N:ℝ)^2) * c k k' := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  simp only [intervalIntegral.integral_of_le h01]
  set Io : Set ℝ := Set.Ioc (0:ℝ) 1 with hIo
  have hIomeas : MeasurableSet Io := by rw [hIo]; exact measurableSet_Ioc
  have hpt : ∀ p ∈ Io ×ˢ Io, f p.1 p.2 ≤
      ∑ k : Fin N, ∑ k' : Fin N, (blk N k ×ˢ blk N k').indicator (fun _ => c k k') p :=
    blk_le_doubleSum_indicator hN h
  have hle : ∀ᵐ z ∂((volume.restrict Io).prod (volume.restrict Io)),
      f z.1 z.2 ≤ ∑ k : Fin N, ∑ k' : Fin N,
        (blk N k ×ˢ blk N k').indicator (fun _ => c k k') z := by
    rw [Measure.prod_restrict, MeasureTheory.ae_restrict_iff' (hIomeas.prod hIomeas)]
    exact Filter.Eventually.of_forall (fun p hp => hpt p hp)
  have hfin : IsFiniteMeasure (volume.restrict Io) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, hIo, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hSint : Integrable (fun z : ℝ × ℝ => ∑ k : Fin N, ∑ k' : Fin N,
      (blk N k ×ˢ blk N k').indicator (fun _ => c k k') z)
      ((volume.restrict Io).prod (volume.restrict Io)) := by
    refine MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin N))
      (f := fun k z => ∑ k' : Fin N, (blk N k ×ˢ blk N k').indicator (fun _ => c k k') z)
      (fun k _ => ?_)
    refine MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin N))
      (f := fun k' z => (blk N k ×ˢ blk N k').indicator (fun _ => c k k') z) (fun k' _ => ?_)
    exact (MeasureTheory.integrable_const_iff.mpr (Or.inr inferInstance)).indicator
      ((blk_measurable N k).prod (blk_measurable N k'))
  have hInt : Integrable (fun z : ℝ × ℝ => f z.1 z.2)
      ((volume.restrict Io).prod (volume.restrict Io)) := by
    rw [Measure.prod_restrict, hIo]
    exact hf
  have hFub := MeasureTheory.integral_prod (fun z : ℝ × ℝ => f z.1 z.2) hInt
  dsimp only at hFub
  have hStep : ∫ z, (∑ k : Fin N, ∑ k' : Fin N,
        (blk N k ×ˢ blk N k').indicator (fun _ => c k k') z)
        ∂((volume.restrict Io).prod (volume.restrict Io))
      = ∑ k : Fin N, ∑ k' : Fin N, (1/(N:ℝ)^2) * c k k' :=
    blk_step_integral c (volume.restrict Io) (fun k => by
      rw [hIo]; exact blk_restrict_volume hN k)
  calc ∫ s in Io, ∫ t in Io, f s t
      = ∫ z, f z.1 z.2 ∂((volume.restrict Io).prod (volume.restrict Io)) := hFub.symm
    _ ≤ ∫ z, (∑ k : Fin N, ∑ k' : Fin N,
            (blk N k ×ˢ blk N k').indicator (fun _ => c k k') z)
          ∂((volume.restrict Io).prod (volume.restrict Io)) :=
        MeasureTheory.integral_mono_ae hInt hSint hle
    _ = ∑ k : Fin N, ∑ k' : Fin N, (1/(N:ℝ)^2) * c k k' := hStep

end Work.CNum
