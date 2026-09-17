import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.MeasureTheory.Integral

open _root_.MeasureTheory

theorem integral_pi_fin_succAbove {α : Type*} [MeasurableSpace α] (ν : MeasureTheory.Measure α)
    [MeasureTheory.SigmaFinite ν] {n : ℕ} (i : Fin (n + 1)) (g : (Fin n → α) → α → ℝ)
    (hg : MeasureTheory.Integrable (fun p : (Fin n → α) × α => g p.1 p.2)
        ((MeasureTheory.Measure.pi (fun _ : Fin n => ν)).prod ν)) :
    ∫ ω : Fin (n + 1) → α,
        g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => α) i ω).2)
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => α) i ω).1)
        ∂(MeasureTheory.Measure.pi (fun _ : Fin (n + 1) => ν))
      = ∫ u, ∫ a, g u a ∂ν ∂(MeasureTheory.Measure.pi (fun _ : Fin n => ν)) := by
  let e : (Fin (n + 1) → α) ≃ᵐ (α × (Fin n → α)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => α) i
  have hmp : MeasureTheory.MeasurePreserving e
      (MeasureTheory.Measure.pi (fun _ : Fin (n+1) => ν))
      (ν.prod (MeasureTheory.Measure.pi (fun _ : Fin n => ν))) :=
    MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) i
  calc ∫ ω : Fin (n+1) → α, g (e ω).2 (e ω).1
          ∂(MeasureTheory.Measure.pi (fun _ : Fin (n+1) => ν))
      = ∫ p : α × (Fin n → α), g p.2 p.1
          ∂(ν.prod (MeasureTheory.Measure.pi (fun _ : Fin n => ν))) :=
        hmp.integral_comp' (fun p : α × (Fin n → α) => g p.2 p.1)
    _ = ∫ p : (Fin n → α) × α, g p.1 p.2
          ∂((MeasureTheory.Measure.pi (fun _ : Fin n => ν)).prod ν) :=
        MeasureTheory.integral_prod_swap (fun p : (Fin n → α) × α => g p.1 p.2)
    _ = ∫ u, ∫ a, g u a ∂ν ∂(MeasureTheory.Measure.pi (fun _ : Fin n => ν)) :=
        MeasureTheory.integral_prod _ hg

end Commons.MeasureTheory.Integral