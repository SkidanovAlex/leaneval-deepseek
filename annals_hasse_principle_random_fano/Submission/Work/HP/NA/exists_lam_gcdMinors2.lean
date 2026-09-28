import Mathlib
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.Defs

namespace Work.HP.NA

/-- Elementary content of the `p`-adic constraint `p^e ∣ gcdMinors2 u v` with `u` primitive at `p`:
some single integer `c` makes `v ≡ c·u (mod p^e)`, i.e. `p^e ∣ v j - c * u j` for every `j`.

Concretely, if `i₀` is an index with `p ∤ u i₀`, then `u i₀` is invertible mod `p^e`; taking
`x` with `x * u i₀ ≡ 1 (mod p^e)` and `c = v i₀ * x` works, because `p^e` divides the minor
`u i₀ * v j - u j * v i₀`. -/
theorem exists_lam_gcdMinors2 {ι : Type*} [Fintype ι] {p e : ℕ} (hp : p.Prime) (u v : ι → ℤ)
    (hu : ∃ i, ¬ (p : ℤ) ∣ u i) (h : (p : ℤ) ^ e ∣ Work.HP.gcdMinors2 u v) :
    ∃ c : ℤ, ∀ j, (p : ℤ) ^ e ∣ (v j - c * u j) := by
  obtain ⟨i0, hi0⟩ := hu
  have hmin := (Work.HP.NA.gcdMinors2_dvd_iff ((p : ℤ) ^ e) u v).mp h
  have hpz : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime (u i0) ((p : ℤ) ^ e) := Work.HP.NA.isCoprime_pow_of_not_dvd hpz hi0 e
  obtain ⟨x, y, hxy⟩ := hcop
  refine ⟨v i0 * x, fun j => ?_⟩
  have hx : (p : ℤ) ^ e ∣ x * u i0 - 1 := by
    have : x * u i0 - 1 = (-y) * (p : ℤ) ^ e := by linarith [hxy]
    rw [this]; exact dvd_mul_left _ _
  have h1 : (p : ℤ) ^ e ∣ (x * (u i0 * v j - u j * v i0)) :=
    dvd_mul_of_dvd_right (hmin i0 j) x
  have h2 : (p : ℤ) ^ e ∣ (x * u i0 - 1) * v j := dvd_mul_of_dvd_left hx (v j)
  have key : v j - (v i0 * x) * u j
      = x * (u i0 * v j - u j * v i0) - (x * u i0 - 1) * v j := by ring
  rw [key]
  exact dvd_sub h1 h2

end Work.HP.NA
