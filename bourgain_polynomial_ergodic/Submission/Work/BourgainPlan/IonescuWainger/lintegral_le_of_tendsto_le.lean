import Mathlib
open Filter

namespace Work.BourgainPlan.IonescuWainger

/-- **Fatou-type bound.** If a sequence of a.e. measurable `ℝ≥0∞`-valued functions converges
pointwise to `g` and all its integrals are bounded by `K`, then the integral of `g` is bounded
by `K`. -/
theorem lintegral_le_of_tendsto_le {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {f : ℕ → α → ENNReal} {g : α → ENNReal} {K : ENNReal}
    (hf : ∀ j, AEMeasurable (f j) μ)
    (hconv : ∀ x, Filter.Tendsto (fun j => f j x) Filter.atTop (nhds (g x)))
    (hK : ∀ j, MeasureTheory.lintegral μ (f j) ≤ K) :
    MeasureTheory.lintegral μ g ≤ K := by
  have hlim : ∀ x, liminf (fun j => f j x) atTop = g x := fun x => (hconv x).liminf_eq
  calc MeasureTheory.lintegral μ g
      = MeasureTheory.lintegral μ (fun x => liminf (fun j => f j x) atTop) :=
        MeasureTheory.lintegral_congr fun x => (hlim x).symm
    _ ≤ liminf (fun j => MeasureTheory.lintegral μ (f j)) atTop :=
        MeasureTheory.lintegral_liminf_le' (μ := μ) (u := atTop) hf
    _ ≤ K := by
        rw [Filter.liminf_eq_iSup_iInf_of_nat]
        apply iSup_le
        intro n
        exact le_trans (iInf_le_of_le n (iInf_le_of_le le_rfl le_rfl)) (hK n)

end Work.BourgainPlan.IonescuWainger
