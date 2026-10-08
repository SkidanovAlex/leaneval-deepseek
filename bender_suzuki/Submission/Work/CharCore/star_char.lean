import Mathlib
import Submission.Work.CharCore.star_trace_eq_trace_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.star_char`

For a complex representation `ρ` of a finite group `G` and any `g : G`,

`starRingEnd ℂ (ρ.character g) = ρ.character g⁻¹`,

i.e. the character value at `g⁻¹` is the complex conjugate of the value at `g`.
This is because `ρ g` has finite order (`g ^ |G| = 1`, hence `(ρ g) ^ |G| = 1`),
so all its eigenvalues are roots of unity, and `Work.CharCore.star_trace_eq_trace_pow`
identifies the conjugate of the trace with the trace of the inverse power.
-/

namespace Work.CharCore

theorem star_char {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    starRingEnd ℂ (ρ.character g) = ρ.character g⁻¹ := by
  have hcard : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨(1 : G)⟩
  have hle : 1 ≤ Fintype.card G := hcard
  -- `ρ g` has finite order
  have hT : (ρ g) ^ Fintype.card G = 1 := by
    rw [← map_pow, pow_card_eq_one, map_one]
  -- the key input: conjugate of the trace is the trace of the inverse power
  have hmain := star_trace_eq_trace_pow (ρ g) (Fintype.card G) hcard hT
  -- `ρ g⁻¹ = (ρ g) ^ (|G| - 1)`
  have hax : ρ g * (ρ g) ^ (Fintype.card G - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hle]
    exact hT
  have hsym : ρ g⁻¹ = (ρ g) ^ (Fintype.card G - 1) := by
    calc ρ g⁻¹ = ρ g⁻¹ * 1 := (mul_one _).symm
      _ = ρ g⁻¹ * (ρ g * (ρ g) ^ (Fintype.card G - 1)) := by rw [hax]
      _ = (ρ g⁻¹ * ρ g) * (ρ g) ^ (Fintype.card G - 1) := by rw [mul_assoc]
      _ = 1 * (ρ g) ^ (Fintype.card G - 1) := by rw [← map_mul, inv_mul_cancel, map_one]
      _ = (ρ g) ^ (Fintype.card G - 1) := one_mul _
  change starRingEnd ℂ (LinearMap.trace ℂ V (ρ g)) = LinearMap.trace ℂ V (ρ g⁻¹)
  rw [hmain, hsym]

end Work.CharCore
