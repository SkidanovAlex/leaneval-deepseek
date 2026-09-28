import Mathlib
import Submission.Work.HP.Lat.prim_bezout

namespace Work.HP.Sig2

open scoped BigOperators

/-- Two primitive integer vectors that are proportional over `ℚ` are equal up to sign.

Indeed, if `x = μ • y` over `ℚ` and `y` is primitive, Bézout expresses `1` as a `ℤ`-linear
combination of the entries of `y`, which shows that `μ` is an integer `m`; then `x i = m * y i`
for all `i`, so `m` divides every entry of `x`, hence divides `gcd x = 1`, hence `m = ±1`. -/
theorem eq_pm_of_prim_prop {ι : Type*} [Fintype ι] (x y : ι → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (μ : ℚ) (h : (fun i => (x i : ℚ)) = μ • (fun i => (y i : ℚ))) : x = y ∨ x = -y := by
  classical
  -- pointwise form of the proportionality
  have h' : ∀ i, (x i : ℚ) = μ * (y i : ℚ) := by
    intro i
    have := congrFun h i
    simpa using this
  -- Bézout for the primitive vector `y`
  obtain ⟨u, hu⟩ := Work.HP.Lat.prim_bezout y hy
  set m : ℤ := ∑ i, u i * x i with hm
  -- the transposed Bézout relation over `ℚ`
  have h1 : (∑ i, (u i : ℚ) * (y i : ℚ)) = 1 := by
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hu
    push_cast at hc
    simpa using hc
  -- `μ` is the integer `m`
  have hmu : μ = (m : ℚ) := by
    rw [hm]
    calc μ = μ * 1 := (mul_one μ).symm
      _ = μ * (∑ i, (u i : ℚ) * (y i : ℚ)) := by rw [h1]
      _ = ∑ i, (u i : ℚ) * (μ * (y i : ℚ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = ∑ i, (u i : ℚ) * (x i : ℚ) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [h' i]
      _ = ((∑ i, u i * x i : ℤ) : ℚ) := by push_cast; rfl
  -- hence `x = m • y` over `ℤ`
  have hxy : ∀ i, x i = m * y i := by
    intro i
    have hi := h' i
    rw [hmu] at hi
    exact_mod_cast hi
  -- `m` divides every entry of `x`, so it divides `gcd x = 1`
  have hmdvd : m ∣ 1 := by
    rw [← hx]
    exact Finset.dvd_gcd (fun i _ => ⟨y i, hxy i⟩)
  -- thus `m = ±1`
  rcases Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr hmdvd) with h1' | h1'
  · left; funext i; simp [hxy i, h1']
  · right; funext i; simp [hxy i, h1']

end Work.HP.Sig2
