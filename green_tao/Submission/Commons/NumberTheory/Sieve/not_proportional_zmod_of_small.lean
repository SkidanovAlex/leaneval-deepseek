import Mathlib

namespace Commons.NumberTheory.Sieve

/-- Small integer vectors which are not rational multiples of each other stay non-proportional
modulo a large prime.  If `A A' : Fin t → ℤ` have `|A j|, |A' j| ≤ Amax` and `2 * Amax^2 < p`,
then any congruence `A' ≡ lam • A (mod p)` forces a rational proportionality `A' j = lam' * A j`
for all `j`.

Proof sketch: pick `j₀` with `A j₀ ≠ 0` (if there is none, then `lam' = 0` works and `h` is
contradicted by `A' = 0 = 0 * A`).  Set `lam' : ℚ := (A' j₀ : ℚ) / (A j₀ : ℚ)`.  From
`(A' j : ZMod p) = lam * (A j : ZMod p)` for `j` and for `j₀`, multiply the first by `(A j₀ : ZMod p)`
and the second by `(A j : ZMod p)` and subtract: `p ∣ A' j * A j₀ - A' j₀ * A j` in `ℤ`
(`ZMod.intCast_zmod_eq_zero_iff_dvd`).  But `|A' j * A j₀ - A' j₀ * A j| ≤ 2 * Amax^2 < p`, so the
difference is `0`; dividing by `A j₀ ≠ 0` gives `(A' j : ℚ) = lam' * (A j : ℚ)`, contradicting `h`. -/
theorem not_proportional_zmod_of_small {p : ℕ} [Fact p.Prime] {t Amax : ℕ}
    {A A' : Fin t → ℤ} (hA : ∀ j, (A j).natAbs ≤ Amax) (hA' : ∀ j, (A' j).natAbs ≤ Amax)
    (h2 : 2 * Amax ^ 2 < p)
    (h : ¬ ∃ lam : ℚ, ∀ j, (A' j : ℚ) = lam * (A j : ℚ)) :
    ∀ lam : ZMod p, (fun j => ((A' j : ℤ) : ZMod p)) ≠ lam • (fun j => ((A j : ℤ) : ZMod p)) := by
  intro lam hcong
  have hcong' : ∀ j, ((A' j : ℤ) : ZMod p) = lam * ((A j : ℤ) : ZMod p) := by
    intro j
    simpa using congrFun hcong j
  have hAmax_lt_p : Amax < p := by
    by_cases h0 : Amax = 0
    · omega
    · have h1 : 1 ≤ Amax := Nat.one_le_iff_ne_zero.mpr h0
      nlinarith [sq_nonneg (Amax : ℤ)]
  by_cases hz : ∃ j, A j ≠ 0
  · obtain ⟨j₀, hj₀⟩ := hz
    apply h
    refine ⟨(A' j₀ : ℚ) / (A j₀ : ℚ), fun j => ?_⟩
    have hkey : A' j * A j₀ = A' j₀ * A j := by
      have hzero : ((A' j * A j₀ - A' j₀ * A j : ℤ) : ZMod p) = 0 := by
        have hcast : ((A' j * A j₀ - A' j₀ * A j : ℤ) : ZMod p)
            = ((A' j : ℤ) : ZMod p) * ((A j₀ : ℤ) : ZMod p)
              - ((A' j₀ : ℤ) : ZMod p) * ((A j : ℤ) : ZMod p) := by
          push_cast
          ring
        rw [hcast, hcong' j, hcong' j₀]
        ring
      have hdiv : (p : ℤ) ∣ A' j * A j₀ - A' j₀ * A j :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
      have hbound : (A' j * A j₀ - A' j₀ * A j).natAbs ≤ 2 * Amax ^ 2 := by
        calc (A' j * A j₀ - A' j₀ * A j).natAbs
            ≤ (A' j * A j₀).natAbs + (A' j₀ * A j).natAbs := Int.natAbs_sub_le _ _
          _ = (A' j).natAbs * (A j₀).natAbs + (A' j₀).natAbs * (A j).natAbs := by
              rw [Int.natAbs_mul, Int.natAbs_mul]
          _ ≤ Amax * Amax + Amax * Amax :=
              Nat.add_le_add (Nat.mul_le_mul (hA' j) (hA j₀)) (Nat.mul_le_mul (hA' j₀) (hA j))
          _ = 2 * Amax ^ 2 := by ring
      have hlt : (A' j * A j₀ - A' j₀ * A j).natAbs < p := lt_of_le_of_lt hbound h2
      have hz0 : A' j * A j₀ - A' j₀ * A j = 0 := by
        by_contra hne
        have := Int.natAbs_le_of_dvd_ne_zero hdiv hne
        rw [Int.natAbs_natCast] at this
        omega
      linarith
    have hmul : (A' j : ℚ) * (A j₀ : ℚ) = (A' j₀ : ℚ) * (A j : ℚ) := by
      exact_mod_cast hkey
    have hden : (A j₀ : ℚ) ≠ 0 := by
      exact_mod_cast hj₀
    field_simp
    linarith
  · have hzall : ∀ j, A j = 0 := fun j => not_not.mp ((not_exists.mp hz) j)
    exfalso
    apply h
    refine ⟨0, fun j => ?_⟩
    have hAj : A j = 0 := hzall j
    have h0' : ((A' j : ℤ) : ZMod p) = 0 := by
      rw [hcong' j, hAj]
      simp
    have hdiv : (p : ℤ) ∣ A' j := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0'
    have hlt : (A' j).natAbs < p := lt_of_le_of_lt (hA' j) hAmax_lt_p
    have h00 : A' j = 0 := by
      by_contra hne
      have := Int.natAbs_le_of_dvd_ne_zero hdiv hne
      rw [Int.natAbs_natCast] at this
      omega
    rw [h00, hAj]
    simp

end Commons.NumberTheory.Sieve
