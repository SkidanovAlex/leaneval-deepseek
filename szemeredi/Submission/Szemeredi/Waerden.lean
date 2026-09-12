import Mathlib

namespace Szemeredi

/-- **Van der Waerden's theorem**: for every finite coloring of `ℕ` and every length `k`,
there is a monochromatic `k`-term arithmetic progression with positive common difference.

This is the classical (density-free) companion of Szemerédi's theorem: it follows here
from the Hales–Jewett theorem as formalized in mathlib
(`Combinatorics.exists_mono_homothetic_copy`). -/
theorem vanDerWaerden {κ : Type*} [Finite κ] (k : ℕ) (C : ℕ → κ) :
    ∃ a b : ℕ, 1 ≤ a ∧ ∃ c : κ, ∀ j : ℕ, j < k → C (a * j + b) = c := by
  obtain ⟨a, ha, b, c, hmono⟩ :=
    Combinatorics.exists_mono_homothetic_copy (M := ℕ) (S := Finset.range k) (C := C)
  refine ⟨a, b, ha, c, ?_⟩
  intro j hj
  have hj' : j ∈ Finset.range k := Finset.mem_range.mpr hj
  simpa [nsmul_eq_mul, add_comm, add_left_comm, add_assoc] using (hmono j hj')

end Szemeredi
