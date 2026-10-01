import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup

namespace Work.LinnikAreas.BGTZ

/-- For `p : ℕ` the complex power `p^{-1}` is the complex inverse of `p`. -/
lemma sieveLocal_cpow_neg_one (p : ℕ) : (p : ℂ) ^ (-(1 : ℂ)) = (p : ℂ)⁻¹ :=
  Complex.cpow_neg_one _

/-- For `p : ℕ` the complex power `p^{-2}` is the square of the complex inverse of `p`. -/
lemma sieveLocal_cpow_neg_two (p : ℕ) : (p : ℂ) ^ (-(2 * (1 : ℂ))) = ((p : ℂ)⁻¹) ^ 2 := by
  have h : (-(2 * (1 : ℂ))) = ((2 : ℂ) * (-1 : ℂ)) := by norm_num
  rw [h]
  exact (Complex.cpow_nat_mul (p : ℂ) 2 (-1 : ℂ)).trans (by rw [Complex.cpow_neg_one])

/-- The complex inverse of `p : ℕ` is the complex number `1/p`. -/
lemma sieveLocal_inv_eq_ofReal (p : ℕ) : (p : ℂ)⁻¹ = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
  norm_num

/-- **The local factor of the Selberg sieve at `s = 1` and the principal character, evaluated
at `χ₁` real quadratic, is a real number in `[0,1]`.**

Since `χ₁` is real we have `χ₁(p)² = 1` whenever `p` is a unit mod `q`, so `χ₁(p) ∈ {0,±1}`;
the principal character takes the value `1` on units and `0` elsewhere.  Hence the local factor
equals `2/p - 1/p²` (when `χ₁(p) = 1`, `p` a unit), `1/p²` (when `χ₁(p) = -1`) or `0` (when `p`
is not a unit mod `q`), and each of these lies in `[0,1]` for every `p : ℕ`. -/
theorem SieveLocalOneOne {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (p : ℕ) :
    0 ≤ (Work.LinnikAreas.BGTZ.sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p).re ∧
    (Work.LinnikAreas.BGTZ.sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p).re ≤ 1 ∧
    Work.LinnikAreas.BGTZ.sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p
      = (((Work.LinnikAreas.BGTZ.sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p).re : ℝ) : ℂ) := by
  -- the value of `χ₁` at `p` squares to the value of the principal character
  have hsq : (χ₁ (p : ZMod q)) ^ 2 = (1 : DirichletCharacter ℂ q) (p : ZMod q) := by
    rw [← MulChar.pow_apply' χ₁ (by norm_num : (2 : ℕ) ≠ 0) (p : ZMod q)]
    exact DFunLike.congr_fun hχ₁ (p : ZMod q)
  -- the principal character takes only the values `0` and `1`
  have hu : (1 : DirichletCharacter ℂ q) (p : ZMod q) = 1 ∨
      (1 : DirichletCharacter ℂ q) (p : ZMod q) = 0 := by
    by_cases h : IsUnit (p : ZMod q)
    · exact Or.inl (MulChar.one_apply h)
    · exact Or.inr (MulCharClass.map_nonunit (1 : DirichletCharacter ℂ q) h)
  have ht0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have ht1 : (p : ℝ)⁻¹ ≤ 1 := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; norm_num
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast h)
  have hc1 := sieveLocal_cpow_neg_one p
  have hc2 := sieveLocal_cpow_neg_two p
  have hz := sieveLocal_inv_eq_ofReal p
  rcases hu with h1u | h0u
  · -- `p` is a unit mod `q`, so `χ₁(p)² = 1` and `χ₁(p) = ±1`
    have hsq1 : (χ₁ (p : ZMod q)) ^ 2 = 1 := by rw [hsq, h1u]
    rcases sq_eq_one_iff.mp hsq1 with hx | hx
    · -- `χ₁(p) = 1`: the local factor is `2/p - 1/p²`
      have haver : (χ₁ (p : ZMod q)).re = 1 := by rw [hx]; norm_num
      have hv : sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p
          = ((2 * ((p : ℝ)⁻¹) - ((p : ℝ)⁻¹) ^ 2 : ℝ) : ℂ) := by
        simp only [sieveLocal, hc1, hc2, h1u, haver, hz]
        push_cast
        ring
      have hb0 : 0 ≤ 2 * ((p : ℝ)⁻¹) - ((p : ℝ)⁻¹) ^ 2 := by
        nlinarith [ht0, ht1, sq_nonneg ((p : ℝ)⁻¹)]
      have hb1 : 2 * ((p : ℝ)⁻¹) - ((p : ℝ)⁻¹) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg ((p : ℝ)⁻¹ - 1)]
      rw [hv]
      exact ⟨by rw [Complex.ofReal_re]; exact hb0,
             by rw [Complex.ofReal_re]; exact hb1,
             by rw [Complex.ofReal_re]⟩
    · -- `χ₁(p) = -1`: the local factor is `1/p²`
      have haver : (χ₁ (p : ZMod q)).re = -1 := by rw [hx]; norm_num
      have hv : sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p
          = ((((p : ℝ)⁻¹) ^ 2 : ℝ) : ℂ) := by
        simp only [sieveLocal, hc1, hc2, h1u, haver, hz]
        push_cast
        ring
      have hs0 : 0 ≤ ((p : ℝ)⁻¹) ^ 2 := sq_nonneg _
      have hs1 : ((p : ℝ)⁻¹) ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
      rw [hv]
      exact ⟨by rw [Complex.ofReal_re]; exact hs0,
             by rw [Complex.ofReal_re]; exact hs1,
             by rw [Complex.ofReal_re]⟩
  · -- `p` is not a unit mod `q`: the principal character vanishes and so does the local factor
    have hv : sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p = 0 := by
      simp only [sieveLocal, h0u]
      ring
    rw [hv]
    exact ⟨by simp, by simp, by simp⟩

end Work.LinnikAreas.BGTZ
