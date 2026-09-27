import Mathlib
import Submission.Work.EKLContract.Defs

namespace Work.EKLC6Core

open MeasureTheory in
theorem rect_mass_double {νT νU : MeasureTheory.Measure Work.EKLContract.SL3}
    {f : ℕ → Work.EKLContract.SL3 → ℝ} {f₀ : Work.EKLContract.SL3 → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf₀m : Measurable f₀)
    (hmeasG : ∀ n, Measurable (fun g => ∫⁻ u, ENNReal.ofReal (f n (g * u)) ∂νU))
    (hconv : ∀ x, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (f₀ x)))
    (hnn : ∀ n x, 0 ≤ f n x) (hmono : ∀ n x, f (n + 1) x ≤ f n x)
    (hfin_g : ∀ g, (∫⁻ u, ENNReal.ofReal (f 0 (g * u)) ∂νU) ≠ ⊤)
    (hfin_int : (∫⁻ g, (∫⁻ u, ENNReal.ofReal (f 0 (g * u)) ∂νU) ∂νT) ≠ ⊤) :
    Filter.Tendsto (fun n => ∫⁻ g, (∫⁻ u, ENNReal.ofReal (f n (g * u)) ∂νU) ∂νT)
      Filter.atTop (nhds (∫⁻ g, (∫⁻ u, ENNReal.ofReal (f₀ (g * u)) ∂νU) ∂νT)) := by
  have hanti : Antitone f := antitone_nat_of_succ_le hmono
  have hle : ∀ n x, f n x ≤ f 0 x := fun n x => hanti (Nat.zero_le n) x
  have inner : ∀ g, Filter.Tendsto (fun n => ∫⁻ u, ENNReal.ofReal (f n (g * u)) ∂νU)
      Filter.atTop (nhds (∫⁻ u, ENNReal.ofReal (f₀ (g * u)) ∂νU)) := by
    intro g
    refine tendsto_lintegral_of_dominated_convergence (μ := νU)
      (fun u => ENNReal.ofReal (f 0 (g * u))) ?_ ?_ (hfin_g g) ?_
    · intro n
      exact ENNReal.measurable_ofReal.comp ((hfm n).comp (by fun_prop))
    · intro n
      exact Filter.Eventually.of_forall
        (fun u => ENNReal.ofReal_le_ofReal (hle n (g * u)))
    · exact Filter.Eventually.of_forall
        (fun u => (ENNReal.continuous_ofReal.tendsto (f₀ (g * u))).comp (hconv (g * u)))
  refine tendsto_lintegral_of_dominated_convergence (μ := νT)
    (fun g => ∫⁻ u, ENNReal.ofReal (f 0 (g * u)) ∂νU) hmeasG ?_ hfin_int ?_
  · intro n
    exact Filter.Eventually.of_forall (fun g =>
      lintegral_mono (fun u => ENNReal.ofReal_le_ofReal (hle n (g * u))))
  · exact Filter.Eventually.of_forall inner

end Work.EKLC6Core
