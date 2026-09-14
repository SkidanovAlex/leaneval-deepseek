import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Commons.Analysis.MeasureTheory

open _root_.MeasureTheory Filter ENNReal
open scoped ENNReal Topology

theorem lintegral_ofReal_le_of_tendsto_of_nonneg {α : Type*} {m : MeasurableSpace α}
    {μ : MeasureTheory.Measure α} {f : ℕ → α → ℝ} {g : α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hnn : ∀ n x, 0 ≤ f n x) (hfi : ∀ n, MeasureTheory.Integrable (f n) μ)
    (hbd : ∀ n, MeasureTheory.integral μ (fun x => f n x) ≤ C)
    (hlim : Filter.Eventually (fun x => Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x)))
      (MeasureTheory.ae μ)) :
    MeasureTheory.lintegral μ (fun x => ENNReal.ofReal (g x)) ≤ ENNReal.ofReal C := by
  have h_ae_eq : (fun x => ENNReal.ofReal (g x)) =ᵐ[μ]
      (fun x => liminf (fun n => ENNReal.ofReal (f n x)) atTop) := by
    filter_upwards [hlim] with x hx
    exact ((ENNReal.continuous_ofReal.tendsto (g x)).comp hx).liminf_eq.symm
  rw [lintegral_congr_ae h_ae_eq]
  calc ∫⁻ x, liminf (fun n => ENNReal.ofReal (f n x)) atTop ∂μ
      ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hfi n).aemeasurable.ennreal_ofReal)
    _ = liminf (fun n => ENNReal.ofReal (∫ x, f n x ∂μ)) atTop := by
        congr 1 with n
        exact (ofReal_integral_eq_lintegral_ofReal (hfi n)
          (Eventually.of_forall (fun x => hnn n x))).symm
    _ ≤ ENNReal.ofReal C := by
        apply liminf_le_of_le (u := fun n => ENNReal.ofReal (∫ x, f n x ∂μ))
          ⟨(0 : ℝ≥0∞), Eventually.of_forall (fun n => bot_le)⟩
        intro b hb
        obtain ⟨n, hn⟩ := hb.exists
        exact le_trans hn (ENNReal.ofReal_le_ofReal (hbd n))

end Commons.Analysis.MeasureTheory