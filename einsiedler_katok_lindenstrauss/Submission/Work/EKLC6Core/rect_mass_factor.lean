import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLC6Core.growth_glue

namespace Work.EKLC6Core

open MeasureTheory in
theorem rect_mass_factor {νT νU : MeasureTheory.Measure Work.EKLContract.SL3} {T U : Subgroup Work.EKLContract.SL3}
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hcarT : νT (T : Set Work.EKLContract.SL3)ᶜ = 0) (hcarU : νU (U : Set Work.EKLContract.SL3)ᶜ = 0)
    {AT AU : Set Work.EKLContract.SL3} (hATm : MeasurableSet AT) (hAUm : MeasurableSet AU)
    (hAT : AT ⊆ (T : Set Work.EKLContract.SL3)) (hAU : AU ⊆ (U : Set Work.EKLContract.SL3)) :
    ∫⁻ g, (∫⁻ u, (Set.indicator (Set.image2 (fun a b : Work.EKLContract.SL3 => a * b) AT AU)
        (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) (g * u)) ∂νU) ∂νT
      = νT AT * νU AU := by
  classical
  -- the measure `νT` is carried by `T`, and `νU` by `U`
  have hTae : ∀ᵐ g ∂νT, g ∈ T := by
    rw [MeasureTheory.ae_iff]; show νT (T : Set Work.EKLContract.SL3)ᶜ = 0; exact hcarT
  have hUae : ∀ᵐ u ∂νU, u ∈ U := by
    rw [MeasureTheory.ae_iff]; show νU (U : Set Work.EKLContract.SL3)ᶜ = 0; exact hcarU
  -- the inner integral, for `g ∈ T`
  have key : ∀ g ∈ T,
      ∫⁻ u, (Set.indicator (Set.image2 (fun a b : Work.EKLContract.SL3 => a * b) AT AU)
        (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) (g * u)) ∂νU
      = AT.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) g * νU AU := by
    intro g hg
    have hae : (fun u => Set.indicator (Set.image2 (fun a b : Work.EKLContract.SL3 => a * b) AT AU)
          (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) (g * u))
        =ᵐ[νU] (fun u => AT.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) g
          * AU.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) u) := by
      filter_upwards [hUae] with u hu
      have hmem := mem_image2_mul_iff hdisj hAT hAU hg hu
      simp only [Set.indicator_apply]
      by_cases hga : g ∈ AT
      · by_cases hua : u ∈ AU
        · rw [if_pos (hmem.mpr ⟨hga, hua⟩), if_pos hga, if_pos hua, mul_one]
        · rw [if_neg (fun h => hua (hmem.mp h).2), if_pos hga, if_neg hua, mul_zero]
      · rw [if_neg (fun h => hga (hmem.mp h).1), if_neg hga, zero_mul]
    calc ∫⁻ u, (Set.indicator (Set.image2 (fun a b : Work.EKLContract.SL3 => a * b) AT AU)
          (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) (g * u)) ∂νU
        = ∫⁻ u, AT.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) g
            * AU.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) u ∂νU :=
          lintegral_congr_ae hae
      _ = AT.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) g
            * ∫⁻ u, AU.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) u ∂νU :=
          lintegral_const_mul _ ((measurable_const : Measurable
            (fun _ : Work.EKLContract.SL3 => (1 : ENNReal))).indicator hAUm)
      _ = AT.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) g * νU AU := by
          exact congrArg (fun z => AT.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) g * z) (lintegral_indicator_one hAUm)
  -- the outer integral
  have hOut : (fun g => ∫⁻ u, (Set.indicator (Set.image2 (fun a b : Work.EKLContract.SL3 => a * b) AT AU)
        (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) (g * u)) ∂νU)
      =ᵐ[νT] (fun g => AT.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) g * νU AU) := by
    filter_upwards [hTae] with g hg
    exact key g hg
  calc ∫⁻ g, (∫⁻ u, (Set.indicator (Set.image2 (fun a b : Work.EKLContract.SL3 => a * b) AT AU)
        (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) (g * u)) ∂νU) ∂νT
      = ∫⁻ g, AT.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) g * νU AU ∂νT :=
        lintegral_congr_ae hOut
    _ = (∫⁻ g, AT.indicator (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) g ∂νT) * νU AU :=
        lintegral_mul_const _ ((measurable_const : Measurable
          (fun _ : Work.EKLContract.SL3 => (1 : ENNReal))).indicator hATm)
    _ = νT AT * νU AU := by
        exact congrArg (fun z => z * νU AU) (lintegral_indicator_one hATm)

end Work.EKLC6Core
