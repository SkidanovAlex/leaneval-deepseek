import Mathlib
import Submission.NK.Reconstruct.ellPart

namespace NK.Reconstruct

/-- **The ℓ-part is functorial**: a group homomorphism carries the ℓ-primary part of the source into
the ℓ-primary part of the target.  If `x ^ (ℓ ^ n) = 1` then `(f x) ^ (ℓ ^ n) = f (x ^ (ℓ ^ n)) = 1`,
so the defining exponent simply transports along `f`. -/
theorem ellPart_map_le {A B : Type*} [CommGroup A] [CommGroup B] (ℓ : ℕ) (f : A →* B) :
    (ellPart A ℓ).map f ≤ ellPart B ℓ := by
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨n, hn⟩ := ha
  exact ⟨n, by rw [← map_pow, hn, map_one]⟩

end NK.Reconstruct
