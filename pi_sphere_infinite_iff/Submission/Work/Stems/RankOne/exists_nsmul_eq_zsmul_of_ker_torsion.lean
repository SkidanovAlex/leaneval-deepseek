import Mathlib

namespace Work.Stems.RankOne

/-- If `g : A →+ ℚ` has torsion kernel and `g α ≠ 0`, then every `γ : A` is
commensurable with `α`: some positive multiple of `γ` is an integer multiple of
`α`. -/
theorem exists_nsmul_eq_zsmul_of_ker_torsion {A : Type*} [AddCommGroup A] (g : A →+ ℚ)
    (hg : ∀ a : A, g a = 0 → ∃ N : ℕ, 0 < N ∧ N • a = 0)
    {α : A} (hα : g α ≠ 0) (γ : A) :
    ∃ m : ℕ, 0 < m ∧ ∃ k : ℤ, m • γ = k • α := by
  let r : ℚ := g γ / g α
  have hr : r * g α = g γ := by
    dsimp [r]
    field_simp [hα]
  have hnum : (r.num : ℚ) = r * r.den := by
    have h := Rat.num_div_den r
    have hden : (r.den : ℚ) ≠ 0 := by positivity
    field_simp [hden] at h
    linarith
  have hkeyQ : (r.num : ℚ) * g α = (r.den : ℚ) * g γ := by
    rw [hnum]
    calc r * ↑r.den * g α = ↑r.den * (r * g α) := by ring
      _ = ↑r.den * g γ := by rw [hr]
  have hkey : (r.num : ℤ) • g α = (r.den : ℤ) • g γ := by
    rw [zsmul_eq_mul, zsmul_eq_mul]
    simpa using hkeyQ
  let δ : A := (r.den : ℤ) • γ - (r.num : ℤ) • α
  have hgδ : g δ = 0 := by
    dsimp [δ]
    rw [map_sub, map_zsmul, map_zsmul]
    rw [hkey]
    abel
  obtain ⟨N, hNpos, hNδ⟩ := hg δ hgδ
  have hsub : N • ((r.den : ℤ) • γ) - N • ((r.num : ℤ) • α) = 0 := by
    rw [← smul_sub]
    exact hNδ
  have heq : N • ((r.den : ℤ) • γ) = N • ((r.num : ℤ) • α) := sub_eq_zero.mp hsub
  refine ⟨N * r.den, Nat.mul_pos hNpos r.den_pos, (N : ℤ) * r.num, ?_⟩
  calc
    (N * r.den) • γ = ((N : ℤ) * (r.den : ℤ)) • γ := by
      rw [← natCast_zsmul γ (N * r.den)]
      exact congrArg (fun z : ℤ => z • γ) (Nat.cast_mul N r.den)
    _ = N • ((r.den : ℤ) • γ) := by
      rw [mul_zsmul]
      exact natCast_zsmul ((r.den : ℤ) • γ) N
    _ = N • ((r.num : ℤ) • α) := heq
    _ = ((N : ℤ) * r.num) • α := by
      rw [← natCast_zsmul ((r.num : ℤ) • α) N]
      exact (mul_zsmul α N r.num).symm

end Work.Stems.RankOne
