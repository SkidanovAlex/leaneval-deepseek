import Mathlib
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLProd

/-- If `ρ` is carried by a subgroup `T` (i.e. `ρ Tᶜ = 0`) and `g₀` commutes with every
element of `T`, then `ρ` is invariant under conjugation by `g₀`. -/
theorem map_conj_eq_of_carried {T : Subgroup Work.EKLContract.SL3} {g₀ : Work.EKLContract.SL3}
    (hcent : ∀ g ∈ T, g₀ * g = g * g₀) {ρ : MeasureTheory.Measure Work.EKLContract.SL3}
    (hρ : ρ (T : Set Work.EKLContract.SL3)ᶜ = 0) :
    ρ.map (fun g => g₀ * g * g₀⁻¹) = ρ := by
  have hf : (fun g : Work.EKLContract.SL3 => g₀ * g * g₀⁻¹) =ᵐ[ρ] id := by
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hρ] with g hg
    have hgT : g ∈ T := by simpa using hg
    rw [hcent g hgT, mul_assoc, mul_inv_cancel, mul_one]
    rfl
  simpa using MeasureTheory.Measure.map_congr hf

end Work.EKLProd
