import Mathlib
import Submission.Work.ORVonNeumann.Basic
import Submission.Work.ORLinnell.Basic

/-!
# The image of a directly finite von Neumann regular ring is division closed

Let `φ : V →+* U` be an injective ring homomorphism, `V` von Neumann regular and directly
finite (`a * b = 1 → b * a = 1`).  Then `φ.range` is division closed in `U`: whenever
`φ a * y = 1` for `y : U`, the element `y` already lies in `φ.range`.

The argument is the standard one.

* Choose `x` with `a * x * a = a` (von Neumann regularity of `V`).
* Then `p := φ a * φ x` satisfies `p * φ a = φ a`, hence
  `p = p * 1 = p * (φ a * y) = (p * φ a) * y = φ a * y = 1`.
* So `φ (a * x) = 1 = φ 1`, and injectivity gives `a * x = 1`; direct finiteness of `V`
  then gives `x * a = 1` as well.
* Finally `y = 1 * y = (φ x * φ a) * y = φ x * (φ a * y) = φ x ∈ φ.range`.

-/

namespace Work.ORBridgeLinnell

theorem isDivisionClosed_range {U V : Type*} [Ring U] [Ring V] (φ : V →+* U)
    (hφ : Function.Injective φ) (hV : Work.ORVonNeumann.VonNeumannRegular V)
    (hdf : ∀ a b : V, a * b = 1 → b * a = 1) : IsDivisionClosed φ.range := by
  intro x hx y hxy
  obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hx
  obtain ⟨x₀, hx₀⟩ := hV a
  -- `φ a * φ x₀` is an idempotent acting as a left identity on `φ a`
  have h1 : φ a * φ x₀ * φ a = φ a := by rw [← map_mul, ← map_mul, hx₀]
  -- hence it is `1`, because `φ a` has the right inverse `y`
  have hp : φ a * φ x₀ = 1 := by
    calc φ a * φ x₀ = φ a * φ x₀ * 1 := (mul_one _).symm
      _ = φ a * φ x₀ * (φ a * y) := by rw [← hxy]
      _ = (φ a * φ x₀ * φ a) * y := (mul_assoc (φ a * φ x₀) (φ a) y).symm
      _ = φ a * y := by rw [h1]
      _ = 1 := hxy
  -- injectivity of `φ` transports this back to `V`, where direct finiteness upgrades it
  have hax : a * x₀ = 1 := hφ (by rw [map_mul, hp, map_one])
  have hx₀a : x₀ * a = 1 := hdf a x₀ hax
  -- so `y` is forced to equal `φ x₀`
  have hy : y = φ x₀ := by
    calc y = 1 * y := (one_mul y).symm
      _ = (φ x₀ * φ a) * y := by rw [← map_mul, hx₀a, map_one]
      _ = φ x₀ * (φ a * y) := mul_assoc _ _ _
      _ = φ x₀ * 1 := by rw [hxy]
      _ = φ x₀ := mul_one _
  rw [hy]
  exact RingHom.mem_range_self φ x₀

end Work.ORBridgeLinnell
