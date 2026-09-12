import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory
open Set

namespace Commons.Analysis.Measure

/-- Swapping the two coordinates of a doubly-indexed product preserves the iterated product
measure: the "transpose" map `(f i k) ↦ (f i k)` viewed as `(ι → κ → α) → (κ → ι → α)`
is measure preserving from `Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ))` to
`Measure.pi (fun _ : κ => Measure.pi (fun _ : ι => μ))`.

Both measures agree on the π-system of "double boxes", where the computation reduces to
swapping the order of the two finite products (`Finset.prod_comm'`). -/
theorem measurePreserving_pi_comm {ι κ : Type*} [Fintype ι] [Fintype κ]
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ] :
    MeasureTheory.MeasurePreserving (fun (f : ι → κ → α) (k : κ) (i : ι) => f i k)
      (MeasureTheory.Measure.pi (fun _ : ι => MeasureTheory.Measure.pi (fun _ : κ => μ)))
      (MeasureTheory.Measure.pi (fun _ : κ => MeasureTheory.Measure.pi (fun _ : ι => μ))) := by
  have hmeas : Measurable (fun (f : ι → κ → α) (k : κ) (i : ι) => f i k) := by
    refine measurable_pi_iff.mpr (fun k => ?_)
    refine measurable_pi_iff.mpr (fun i => ?_)
    exact (measurable_pi_apply k).comp (measurable_pi_apply i)
  refine ⟨hmeas, ?_⟩
  refine (Measure.pi_eq_generateFrom
    (μ := fun _ : κ => Measure.pi (fun _ : ι => μ))
    (C := fun _ : κ => pi univ '' pi univ (fun _ : ι => {s : Set α | MeasurableSet s}))
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => MeasureTheory.Measure.FiniteSpanningSetsIn.pi
      (fun _ : ι => μ.toFiniteSpanningSetsIn)) ?_).symm
  intro s hs
  choose u hu_mem hus using hs
  have hu_meas : ∀ k i, MeasurableSet (u k i) := by
    intro k i
    have := hu_mem k
    rw [mem_univ_pi] at this
    exact this i
  have hs' : s = fun k => pi univ (u k) := funext fun k => (hus k).symm
  rw [hs']
  rw [Measure.map_apply hmeas]
  · rw [show (fun (f : ι → κ → α) (k : κ) (i : ι) => f i k) ⁻¹'
        pi univ (fun k => pi univ (u k)) =
        pi univ (fun i => pi univ (fun k => u k i)) by
      ext f; simp only [mem_preimage, mem_pi, mem_univ, true_implies]
      exact forall_comm]
    simp only [Measure.pi_pi]
    rw [Finset.prod_comm' (s := Finset.univ) (t := fun _ => Finset.univ)
      (t' := Finset.univ) (s' := fun _ => Finset.univ)]
    simp
  · exact MeasurableSet.univ_pi (fun k => MeasurableSet.univ_pi (fun i => hu_meas k i))

end Commons.Analysis.Measure