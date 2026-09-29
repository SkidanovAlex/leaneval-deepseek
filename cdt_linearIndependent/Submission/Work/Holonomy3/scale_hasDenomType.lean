import Mathlib
import Submission.Work.Holonomy3.defs

/-!
# Scaling a series of denominator type by a rational number

If `f` has denominator type `K · n^e · ∏_j [1, …, b_j n + c]`, then so does `(q : ℚ)⁻¹ • f`:
multiplying the fixed integer factor `K` by `q` absorbs the scalar.  (The scalar `q⁻¹` itself is
not an integer, but `q · q⁻¹ = 1`, and the denominator type is only defined up to the choice of the
integer factor `K`.)

This is the denominator-type component of the "scale the whole family" step of the §6 holonomy
argument, where the `f i` are multiplied by a common rational normalisation.
-/

namespace Work.Holonomy3

/-- The `n`-th coefficient of a rational multiple of a power series. -/
theorem coeff_smul_inv {q : ℕ} (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n ((q : ℚ)⁻¹ • f) = (q : ℚ)⁻¹ * PowerSeries.coeff n f := by
  simp

/-- Scaling a power series by the inverse of a positive natural number preserves its denominator
type (with the integer factor `K` multiplied by `q`). -/
theorem scale_hasDenomType {r : ℕ} (q : ℕ) (hq : 0 < q) (e : ℕ) (b : Fin r → ℕ) (f : PowerSeries ℚ)
    (h : Submission.CDTPlan.HasDenomType e b f) :
    Submission.CDTPlan.HasDenomType e b ((q : ℚ)⁻¹ • f) := by
  obtain ⟨K, c, hK, hh⟩ := h
  refine ⟨q * K, c, Nat.mul_pos hq hK, fun n hn => ?_⟩
  obtain ⟨a, ha⟩ := hh n hn
  refine ⟨a, ?_⟩
  have hcoeff : PowerSeries.coeff n ((q : ℚ)⁻¹ • f) = (q : ℚ)⁻¹ * PowerSeries.coeff n f := by
    simp
  rw [hcoeff, ← ha, Nat.cast_mul]
  field_simp

end Work.Holonomy3
