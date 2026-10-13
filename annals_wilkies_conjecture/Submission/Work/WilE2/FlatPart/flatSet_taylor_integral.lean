import Mathlib
import Submission.Work.WilE2.SardDefs

/-!
# Taylor's formula with integral remainder on the flat set

`flatSet f j` is the set of points at which every iterated derivative of `f` of orders `1, …, j`
vanishes (see `Work.WilE2.flatSet`).  Hence the Taylor expansion of order `j` of `f` at such a
point `x` has all its non-constant terms equal to zero, and Taylor's theorem with the integral
form of the remainder (`map_add_eq_sum_add_integral_iteratedFDeriv`, applied to the one-parameter
family `t ↦ f (x + t • (y - x))`) specialises to the *exact* identity

`f y - f x = (j!)⁻¹ ∫₀¹ (1 - t)^j · D^{j+1} f (x + t • (y - x)) (y - x, …, y - x) dt`.

This is the "flatness" input of the Sard/Rolle estimate on `flatSet f j`.
-/

namespace Work.WilE2.FlatPart

/-- The order-`j` Taylor sum of `f` at a point of `flatSet f j` collapses to its constant term:
all the terms of orders `1, …, j` vanish. -/
theorem sum_iteratedFDeriv_eq_of_mem_flatSet {n j : ℕ} (f : (Fin n → ℝ) → ℝ)
    {x y : Fin n → ℝ} (hx : x ∈ Work.WilE2.flatSet f j) :
    (∑ k ∈ Finset.range (j + 1), ((k.factorial : ℝ))⁻¹ •
        (iteratedFDeriv ℝ k f x) (fun _ => y - x)) = f x := by
  rw [Finset.sum_eq_single 0]
  · rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, iteratedFDeriv_zero_apply]
  · intro b hb hb0
    rw [hx b (by omega) (by simpa using hb), zero_apply, smul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem flatSet_taylor_integral {n j : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f) {x y : Fin n → ℝ} (hx : x ∈ flatSet f j) :
    f y - f x = ((Nat.factorial j : ℝ))⁻¹ * ∫ t in (0:ℝ)..1,
      (1 - t) ^ j * (iteratedFDeriv ℝ (j + 1) f (x + t • (y - x))) (fun _ : Fin (j + 1) => y - x) := by
  -- `f` is `C^{j+1}` on the segment `x + t • (y - x)`, `t ∈ [0,1]`
  have hft : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ ((j : ℕ) + 1) f (x + t • (y - x)) := by
    intro t _
    simpa using hf.contDiffAt (x := x + t • (y - x))
  have hxy : x + (y - x) = y := add_sub_cancel x y
  -- Taylor's theorem with integral remainder for the one-parameter family along the segment
  have key := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := x) (y := y - x) (n := j) hft
  rw [hxy] at key
  -- the Taylor sum at `x ∈ flatSet f j` is the constant term `f x`
  rw [sum_iteratedFDeriv_eq_of_mem_flatSet f hx] at key
  -- rewrite the scalar multiplication on `ℝ` as multiplication, in the integrand and outside
  have hI : (∫ t in (0:ℝ)..1,
        (1 - t)^j • (iteratedFDeriv ℝ (j+1) f (x + t • (y - x))) (fun _ : Fin (j+1) => y - x))
      = ∫ t in (0:ℝ)..1,
        (1 - t)^j * (iteratedFDeriv ℝ (j+1) f (x + t • (y - x))) (fun _ : Fin (j+1) => y - x) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [smul_eq_mul]
  rw [hI, smul_eq_mul] at key
  linarith [key]

end Work.WilE2.FlatPart
