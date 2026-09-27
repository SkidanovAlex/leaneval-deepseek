import Mathlib
import Submission.Work.EKLC6Core.InjRadius
import Submission.Work.EKLComp.inv_mem_V

/-!
# `Work.EKLC6Core.smul_conj_mem_V`

The displacement neighbourhoods `V δ = {g : SL₃(ℝ) | ∀ i j, |g i j - 1 i j| < δ}` are stable
under conjugation, *quantitatively*, when the outer element is small relative to `1/2`:

    w ∈ V a, v ∈ V ρ, 0 < a ≤ 1/2, 0 ≤ ρ  ⟹  w v w⁻¹ ∈ V (ρ (1 + 33 a + 90 a²) + (11 a + 30 a²)).

## Proof

Write `u = w v`.  Two applications of `Work.EKLC6Core.V_mul_subset_V`
(`V s · V t ⊆ V (s + t + 3 s t)`, from `Work.EKLRelCross.entries_mul_sub_one_le`) with the
inversion bound `Work.EKLComp.inv_mem_V` (`w ∈ V a ⟹ w⁻¹ ∈ V (10 a)` for `a ≤ 1`) give

* `u = w v ∈ V (a + ρ + 3 a ρ)`,
* `w v w⁻¹ = u · w⁻¹ ∈ V ((a + ρ + 3 a ρ) + 10 a + 3 (a + ρ + 3 a ρ) (10 a))`,

and the radius of the second box is exactly the claimed one:

  `(a + ρ + 3aρ) + 10a + 30a (a + ρ + 3aρ) = 11a + 30a² + ρ (1 + 33a + 90a²)`.

All hypotheses are satisfied: `a > 0 ≤ ρ` make the radii nonnegative, and `a ≤ 1/2` is available
for the inversion bound.
-/

namespace Work.EKLC6Core

open Work.EKLContract

theorem smul_conj_mem_V {a ρ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) (hρ : 0 ≤ ρ)
    {w v : Work.EKLContract.SL3} (hw : w ∈ Work.EKLContract.V a)
    (hv : v ∈ Work.EKLContract.V ρ) :
    w * v * w⁻¹ ∈ Work.EKLContract.V (ρ * (1 + 33 * a + 90 * a ^ 2) + (11 * a + 30 * a ^ 2)) := by
  -- `w⁻¹` is still `10 a`-close to the identity.
  have hwinv : w⁻¹ ∈ Work.EKLContract.V (10 * a) :=
    Work.EKLComp.inv_mem_V ha (by linarith) hw
  -- first multiply: `w v ∈ V (a + ρ + 3 a ρ)`.
  have hmul : w * v ∈ Work.EKLContract.V (a + ρ + 3 * a * ρ) :=
    V_mul_subset_V (le_of_lt ha) hρ hw hv
  -- then multiply by `w⁻¹`.
  have h2 : w * v * w⁻¹ ∈ Work.EKLContract.V
      ((a + ρ + 3 * a * ρ) + 10 * a + 3 * (a + ρ + 3 * a * ρ) * (10 * a)) :=
    V_mul_subset_V (by nlinarith) (by linarith) hmul hwinv
  -- the two radii agree.
  have harith : (a + ρ + 3 * a * ρ) + 10 * a + 3 * (a + ρ + 3 * a * ρ) * (10 * a)
      = ρ * (1 + 33 * a + 90 * a ^ 2) + (11 * a + 30 * a ^ 2) := by ring
  rwa [harith] at h2

end Work.EKLC6Core
