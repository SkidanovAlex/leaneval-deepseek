import Mathlib
import Submission.Work.DSCOH.ShiftToolkit

namespace Work.DSCOH

set_option linter.unusedVariables false in
theorem fiber_sum {A : Type*} [CommRing A] {n : ℕ} {M : Type*} [AddCommMonoid M] [Module A M]
    (s : Finset (Fin n →₀ ℕ)) (ψ : (Fin n →₀ ℕ) → (Fin n → ℤ))
    (hinj : Set.InjOn ψ ↑s) (h : (Fin n →₀ ℕ) → A) (L : (Fin n → ℤ) → M) :
    ∑ β ∈ s.image ψ, (∑ v ∈ s.filter (fun v => ψ v = β), h v) • L β = ∑ v ∈ s, h v • L (ψ v) := by
  -- Group the sum over `s` by the fibres of `ψ`; on the fibre over `β`, the
  -- factor `L β` equals `L (ψ v)`.
  trans ∑ β ∈ s.image ψ, ∑ v ∈ s.filter (fun v => ψ v = β), h v • L (ψ v)
  · apply Finset.sum_congr rfl
    intro β _
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← (Finset.mem_filter.mp hv).2]
  · exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem ψ hi) _

end Work.DSCOH
