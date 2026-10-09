import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `v`-adic valuation subring is fixed modulo `v`

Let `R` be a Dedekind domain with fraction field `K`, let `v` be a height one prime of `R`
(maximal ideal), and let `τ : K ≃+* K` be a ring automorphism which acts trivially on `R`
modulo `v`, i.e. `v (τ x - x) < 1` for every `x : R`.

We show that `τ` then acts trivially on the valuation subring `𝒪_v` of `K` modulo `v`:
for every `y ∈ 𝒪_v` one has `v (τ y - y) < 1`.

The proof writes an element `y` of the valuation ring as `y = n / d` with `n : R` and
`d ∉ v` (this is `IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer`).
Then
`τ y - y = ((τ n - n) * d - n * (τ d - d)) / (τ d * d)`,
the numerator lies in the maximal ideal because it is a sum of products of elements of `𝒪_v`
with elements of the maximal ideal, and `τ d` is a unit of `𝒪_v` (as `τ d - d` is in the
maximal ideal and `d` is a unit). Hence the quotient lies in the maximal ideal as well.
-/

namespace Work.SSGRoute.LevelInertiaProEll

open scoped algebraMap

theorem valuationSubringFixing {R : Type*} [CommRing R]
    [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) (τ : K ≃+* K)
    (hτ : ∀ x : R, (IsDedekindDomain.HeightOneSpectrum.valuation K v) (τ ↑x - ↑x) < 1)
    {y : K} (hy : y ∈ (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) :
    (IsDedekindDomain.HeightOneSpectrum.valuation K v) (τ y - y) < 1 := by
  set V := IsDedekindDomain.HeightOneSpectrum.valuation K v
  -- `y` lies in the valuation subring, so `V y ≤ 1`.
  have hy1 : V y ≤ 1 := hy
  -- Write `y = n / d` with `n : R` and `d` a unit at `v`.
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v y hy1
  set N : K := algebraMap R K n
  set D : K := algebraMap R K (d : R)
  -- `d`, hence `D`, is a unit at `v`: `V D = 1`.
  have hd1 : V D = 1 := by
    rw [show D = algebraMap R K (d : R) from rfl]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v (d : R)).2 d.2
  -- The two differences `τ n - n` and `τ d - d` lie in the maximal ideal.
  have hτN : V (τ N - N) < 1 := by
    rw [show N = algebraMap R K n from rfl]; exact hτ n
  have hτD : V (τ D - D) < 1 := by
    rw [show D = algebraMap R K (d : R) from rfl]; exact hτ (d : R)
  have hN1 : V N ≤ 1 := by
    rw [show N = algebraMap R K n from rfl]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v n
  -- The numerator `τ n * d - n * τ d` lies in the maximal ideal.
  have hA : V ((τ N - N) * D) < 1 := by
    rw [Valuation.map_mul, hd1, mul_one]; exact hτN
  have hB : V (N * (D - τ D)) < 1 := by
    rw [Valuation.map_mul]
    have hsub : V (D - τ D) < 1 := by rw [Valuation.map_sub_swap]; exact hτD
    calc V N * V (D - τ D) ≤ 1 * V (D - τ D) := mul_le_mul_left hN1 (V (D - τ D))
      _ = V (D - τ D) := one_mul _
      _ < 1 := hsub
  have hQ : V (τ N * D - N * τ D) < 1 := by
    have hsplit : τ N * D - N * τ D = (τ N - N) * D + N * (D - τ D) := by ring
    rw [hsplit]
    exact lt_of_le_of_lt (Valuation.map_add_le_max' V _ _) (max_lt hA hB)
  -- `τ D` is still a unit at `v`.
  have hτD1 : V (τ D) = 1 := by
    have h : V (τ D - D) < V D := by rw [hd1]; exact hτD
    have h2 := Valuation.map_add_eq_of_lt_right V h
    rw [sub_add_cancel, hd1] at h2
    exact h2
  have hden : V (τ D * D) = 1 := by rw [Valuation.map_mul, hτD1, hd1, mul_one]
  -- Multiplying `τ y - y` by the unit `τ D * D` clears the denominator.
  have hkey : (τ y - y) * (τ D * D) = τ N * D - N * τ D := by
    have hτnd : τ y * τ D = τ N := by rw [← map_mul, hnd]
    rw [sub_mul,
      show τ y * (τ D * D) = τ N * D from by rw [← mul_assoc, hτnd],
      show y * (τ D * D) = N * τ D from by rw [mul_comm (τ D) D, ← mul_assoc, hnd]]
  have hmul : V (τ y - y) * V (τ D * D) = V (τ N * D - N * τ D) := by
    rw [← Valuation.map_mul, hkey]
  calc V (τ y - y) = V (τ y - y) * 1 := (mul_one _).symm
    _ = V (τ y - y) * V (τ D * D) := by rw [hden]
    _ = V (τ N * D - N * τ D) := hmul
    _ < 1 := hQ

end Work.SSGRoute.LevelInertiaProEll
