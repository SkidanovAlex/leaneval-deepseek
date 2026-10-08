import Mathlib
import Submission.Work.DSTR.M110.SplitCase.CardRangeDefs

namespace Work.DSTR.M110.SplitCase

theorem sq_injOn_range_phi (F : Type*) [Field F] (σ : F ≃+* F)
    (hneg : ∀ u : Fˣ, Work.DSTR.M110.SplitCase.phiHom F σ u ≠ -1)
    {x y : Fˣ} (hx : x ∈ (Work.DSTR.M110.SplitCase.phiHom F σ).range)
    (hy : y ∈ (Work.DSTR.M110.SplitCase.phiHom F σ).range)
    (hxy : x ^ 2 = y ^ 2) : x = y := by
  -- The only square roots of `1` in the units of a field are `±1`; `-1` is excluded by `hneg`.
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  set z : Fˣ := phiHom F σ (u * v⁻¹) with hz
  -- `z² = φ(u v⁻¹)² = φ((u v⁻¹)²) = φ(u²) φ(v²)⁻¹ = 1`, since `φ(u)² = φ(v)²`.
  have hz2 : z ^ 2 = 1 := by
    have h : z ^ 2 = phiHom F σ (u ^ 2 * (v ^ 2)⁻¹) := by
      rw [hz, ← map_pow, mul_pow, inv_pow]
    rw [h, map_mul, map_inv, map_pow, map_pow, hxy, mul_inv_cancel]
  have hzne : z ≠ -1 := by rw [hz]; exact hneg (u * v⁻¹)
  have hmain : phiHom F σ u = z * phiHom F σ v := by
    rw [hz, ← map_mul, show (u * v⁻¹) * v = u from by group]
  rcases (Units.sq_eq_sq_iff_eq_or_eq_neg (a := z) (b := 1)).mp (by simpa using hz2) with
    hz1 | hzneg
  · rw [hmain, hz1, one_mul]
  · exact absurd hzneg hzne

end Work.DSTR.M110.SplitCase
