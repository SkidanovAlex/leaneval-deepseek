import Mathlib

/-!
# Comparing two rational approximations of a real number (Area A3, `Weil`)

If a real number `Λ` is approximated by a reduced fraction `a'/q'` at scale `D³/q'²`
and simultaneously by a reduced fraction `aD/qD` at scale `1/(qD · Q₀)` with `Q₀ ≥ 2q'`,
then the denominators are comparable: `q'/(2D³) ≤ qD`.

The proof is the standard "two approximants" argument.  Either the two fractions are
distinct, in which case the difference of the reduced fractions is bounded below by
`1/(q' qD)` (a nonzero integer over `q' qD`), which after multiplying out gives
`1 ≤ D³ qD/q' + q'/Q₀` and hence `1/2 ≤ D³ qD/q'`; or they are equal, in which case
reducedness forces `q' = qD` and the claim is immediate.
-/

namespace Work.A3.Weil

theorem comparable_densities {Λ : ℝ} {a' aD : ℤ} {q' qD Q₀ D : ℕ}
    (hq'1 : 1 ≤ q') (hcop' : IsCoprime a' q') (hqD1 : 1 ≤ qD) (hcopD : IsCoprime aD qD)
    (hD1 : 1 ≤ D) (hQ₀ : 2 * q' ≤ Q₀)
    (h1 : |Λ - (a' : ℝ) / (q' : ℝ)| ≤ (D : ℝ) ^ 3 / (q' : ℝ) ^ 2)
    (h2 : |Λ - (aD : ℝ) / (qD : ℝ)| ≤ 1 / ((qD : ℝ) * (Q₀ : ℝ))) :
    (q' : ℝ) / (2 * (D : ℝ) ^ 3) ≤ (qD : ℝ) := by
  have hq'pos : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast (show 0 < q' by omega)
  have hqDpos : (0 : ℝ) < (qD : ℝ) := by exact_mod_cast (show 0 < qD by omega)
  have hQ0pos : (0 : ℝ) < (Q₀ : ℝ) := by exact_mod_cast (show 0 < Q₀ by omega)
  -- the triangle inequality combining the two approximations
  have htri : |(a' : ℝ) / (q' : ℝ) - (aD : ℝ) / (qD : ℝ)| ≤
      (D : ℝ) ^ 3 / (q' : ℝ) ^ 2 + 1 / ((qD : ℝ) * (Q₀ : ℝ)) := by
    have h := abs_sub_le ((a' : ℝ) / (q' : ℝ)) Λ ((aD : ℝ) / (qD : ℝ))
    have h' : |(a' : ℝ) / (q' : ℝ) - Λ| = |Λ - (a' : ℝ) / (q' : ℝ)| := abs_sub_comm _ _
    rw [h'] at h
    exact le_trans h (add_le_add h1 h2)
  by_cases hc : a' * (qD : ℤ) = aD * (q' : ℤ)
  · -- equal fractions: reducedness forces equal denominators
    have hd1 : (q' : ℤ) ∣ (qD : ℤ) := by
      refine hcop'.symm.dvd_of_dvd_mul_left ?_
      exact ⟨aD, by rw [hc]; ring⟩
    have hd2 : (qD : ℤ) ∣ (q' : ℤ) := by
      refine hcopD.symm.dvd_of_dvd_mul_left ?_
      exact ⟨a', by rw [← hc]; ring⟩
    have hqe : q' = qD :=
      Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp hd1) (Int.natCast_dvd_natCast.mp hd2)
    rw [hqe]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (D : ℝ) ^ 3)]
    have hD3ge1 : (1 : ℝ) ≤ (D : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hD1)
    nlinarith [hqDpos.le, hD3ge1]
  · -- distinct fractions: the difference is at least 1/(q' qD)
    have hfe : (a' : ℝ) / (q' : ℝ) - (aD : ℝ) / (qD : ℝ) =
        ((a' * (qD : ℤ) - aD * (q' : ℤ) : ℤ) : ℝ) / ((q' : ℝ) * (qD : ℝ)) := by
      rw [div_sub_div _ _ hq'pos.ne' hqDpos.ne']
      push_cast
      ring
    have hge1 : (1 : ℝ) ≤ |((a' * (qD : ℤ) - aD * (q' : ℤ) : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast (Int.one_le_abs (sub_ne_zero.mpr hc))
    have hgap : (1 : ℝ) / ((q' : ℝ) * (qD : ℝ)) ≤
        |(a' : ℝ) / (q' : ℝ) - (aD : ℝ) / (qD : ℝ)| := by
      rw [hfe, abs_div, abs_of_pos (mul_pos hq'pos hqDpos)]
      exact div_le_div_of_nonneg_right hge1 (le_of_lt (mul_pos hq'pos hqDpos))
    have hbig : (1 : ℝ) ≤
        ((D : ℝ) ^ 3 / (q' : ℝ) ^ 2 + 1 / ((qD : ℝ) * (Q₀ : ℝ))) * ((q' : ℝ) * (qD : ℝ)) := by
      have hpos : (0 : ℝ) ≤ (q' : ℝ) * (qD : ℝ) := le_of_lt (mul_pos hq'pos hqDpos)
      have hone : (1 : ℝ) / ((q' : ℝ) * (qD : ℝ)) * ((q' : ℝ) * (qD : ℝ)) = 1 := by
        field_simp
      calc (1 : ℝ) = (1 : ℝ) / ((q' : ℝ) * (qD : ℝ)) * ((q' : ℝ) * (qD : ℝ)) := hone.symm
        _ ≤ |(a' : ℝ) / (q' : ℝ) - (aD : ℝ) / (qD : ℝ)| * ((q' : ℝ) * (qD : ℝ)) :=
              mul_le_mul_of_nonneg_right hgap hpos
        _ ≤ ((D : ℝ) ^ 3 / (q' : ℝ) ^ 2 + 1 / ((qD : ℝ) * (Q₀ : ℝ))) * ((q' : ℝ) * (qD : ℝ)) :=
              mul_le_mul_of_nonneg_right htri hpos
    have hbig' : (1 : ℝ) ≤ (D : ℝ) ^ 3 * (qD : ℝ) / (q' : ℝ) + (q' : ℝ) / (Q₀ : ℝ) := by
      have hsimp : ((D : ℝ) ^ 3 / (q' : ℝ) ^ 2 + 1 / ((qD : ℝ) * (Q₀ : ℝ))) * ((q' : ℝ) * (qD : ℝ))
          = (D : ℝ) ^ 3 * (qD : ℝ) / (q' : ℝ) + (q' : ℝ) / (Q₀ : ℝ) := by
        field_simp
      rwa [hsimp] at hbig
    have hQ0le : (q' : ℝ) / (Q₀ : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hQ0pos]
      have h2q : ((2 : ℝ) * (q' : ℝ)) ≤ (Q₀ : ℝ) := by exact_mod_cast hQ₀
      linarith
    have hD3qd : (1 : ℝ) / 2 ≤ (D : ℝ) ^ 3 * (qD : ℝ) / (q' : ℝ) := by
      linarith [hbig', hQ0le]
    have hle : (1 : ℝ) / 2 * (q' : ℝ) ≤ (D : ℝ) ^ 3 * (qD : ℝ) :=
      (le_div_iff₀ hq'pos).mp hD3qd
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (D : ℝ) ^ 3)]
    nlinarith [hle]

end Work.A3.Weil
