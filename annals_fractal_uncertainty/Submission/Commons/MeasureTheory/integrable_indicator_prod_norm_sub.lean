import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

open scoped Pointwise

namespace Commons.MeasureTheory

/-- **Integrability of a translate-difference on a product of compact sets.**  For a locally
integrable `V` and compact `K, L`, the function `(z, y) ↦ ‖V (z - y)‖`, cut off to `K × L`, is
integrable for the product of Lebesgue measure with itself. -/
theorem integrable_indicator_prod_norm_sub {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {V : (Fin d → ℂ) → E}
    (hV : MeasureTheory.LocallyIntegrable V
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    {K L : Set (Fin d → ℂ)} (hK : IsCompact K) (hL : IsCompact L) :
    MeasureTheory.Integrable ((K ×ˢ L).indicator
        (fun p : (Fin d → ℂ) × (Fin d → ℂ) => ‖V (p.1 - p.2)‖))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) := by
  classical
  have hKl : IsCompact (K + -L) := hK.add hL.neg
  -- The dominating function: `‖V‖` restricted to the compact set `K + -L`, times `1_L`.
  have hφ : MeasureTheory.Integrable ((K + -L).indicator (fun u : Fin d → ℂ => ‖V u‖))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
    rw [integrable_indicator_iff hKl.isClosed.measurableSet]
    exact (hV.integrableOn_isCompact hKl).norm
  have hψ : MeasureTheory.Integrable (L.indicator (fun _ : Fin d → ℂ => (1 : ℝ)))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
    rw [integrable_indicator_iff hL.isClosed.measurableSet]
    exact integrableOn_const (by simpa using hL.measure_lt_top.ne) (by simp)
  have hD : MeasureTheory.Integrable
      (fun q : (Fin d → ℂ) × (Fin d → ℂ) =>
        ((K + -L).indicator (fun u : Fin d → ℂ => ‖V u‖)) q.1 *
          (L.indicator (fun _ : Fin d → ℂ => (1 : ℝ))) q.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) :=
    hφ.mul_prod hψ
  -- Change of variables `q = (z - y, y)`: the target becomes supported on `(K + -L) × L`.
  set S : Set ((Fin d → ℂ) × (Fin d → ℂ)) := {q | (q.1 + q.2, q.2) ∈ K ×ˢ L} with hSdef
  set G : (Fin d → ℂ) × (Fin d → ℂ) → ℝ := S.indicator (fun q => ‖V q.1‖) with hGdef
  have hKLm : MeasurableSet (K ×ˢ L) :=
    hK.isClosed.measurableSet.prod hL.isClosed.measurableSet
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact hKLm.preimage (by fun_prop)
  have hGmeas : AEStronglyMeasurable G
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) := by
    rw [hGdef]
    refine AEStronglyMeasurable.indicator ?_ hSmeas
    have hcomp : (fun q : (Fin d → ℂ) × (Fin d → ℂ) => ‖V q.1‖)
        = (fun u : Fin d → ℂ => ‖V u‖) ∘ Prod.fst := rfl
    rw [hcomp]
    exact (hV.aestronglyMeasurable.norm).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst
  have hGint : MeasureTheory.Integrable G
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) := by
    refine Integrable.mono' hD hGmeas ?_
    filter_upwards with q
    rw [hGdef]
    by_cases h : q ∈ S
    · rw [Set.indicator_of_mem h]
      have hq : (q.1 + q.2, q.2) ∈ K ×ˢ L := by
        have := h; rw [hSdef] at this; exact this
      obtain ⟨h1, h2⟩ := Set.mem_prod.mp hq
      have hsub : q.1 ∈ K + -L := by
        have : q.1 = (q.1 + q.2) + (-q.2) := by abel
        rw [this]
        exact Set.add_mem_add h1 (Set.neg_mem_neg.mpr h2)
      rw [Set.indicator_of_mem hsub, Set.indicator_of_mem h2]
      simp
    · rw [Set.indicator_of_notMem h]
      simp only [norm_zero]
      exact mul_nonneg (Set.indicator_nonneg (fun u _ => norm_nonneg _) q.1)
        (Set.indicator_nonneg (fun v _ => by norm_num) q.2)
  -- Transfer back along the measure-preserving change of variables `(z,y) ↦ (z-y, y)`.
  have hT : MeasurePreserving (fun z : (Fin d → ℂ) × (Fin d → ℂ) => (z.1 - z.2, z.2))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) :=
    measurePreserving_sub_prod _ _
  have hcomp : MeasureTheory.Integrable
      (G ∘ (fun z : (Fin d → ℂ) × (Fin d → ℂ) => (z.1 - z.2, z.2)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) :=
    (hT.integrable_comp hGmeas).mpr hGint
  have key : (G ∘ (fun z : (Fin d → ℂ) × (Fin d → ℂ) => (z.1 - z.2, z.2)))
      = ((K ×ˢ L).indicator (fun p : (Fin d → ℂ) × (Fin d → ℂ) => ‖V (p.1 - p.2)‖)) := by
    funext z
    simp only [Function.comp_apply, hGdef, Set.indicator_apply]
    have hmem : (z.1 - z.2, z.2) ∈ S ↔ (z.1, z.2) ∈ K ×ˢ L := by
      rw [hSdef]; simp [sub_add_cancel]
    by_cases h : (z.1, z.2) ∈ K ×ˢ L
    · rw [if_pos (hmem.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (hmem.mp hh)), if_neg h]
  rw [key] at hcomp
  exact hcomp

end Commons.MeasureTheory