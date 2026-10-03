import Mathlib

namespace Work.ORHughesFree.NaturalExtension

/-- A matrix `N` over a ring whose nonzero entries only ever raise the residue
`modNat` by exactly one (i.e. `N x y ≠ 0 → (y.modNat : ℕ) = (x.modNat : ℕ) + 1`,
where `modNat : Fin (n * i) → Fin i` is reduction mod the inner size `i`) is
nilpotent, with `N ^ i = 0`.  The reason is that a nonzero entry of `N ^ k`
forces the two residues to differ by `k`, while residues lie in `[0, i)`. -/
theorem pow_eq_zero_of_colDeg_shift {R : Type*} [Ring R] {n i : ℕ}
    (N : Matrix (Fin (n * i)) (Fin (n * i)) R)
    (hN : ∀ x y : Fin (n * i), N x y ≠ 0 → (y.modNat : ℕ) = (x.modNat : ℕ) + 1) :
    N ^ i = 0 := by
  -- A nonzero entry of `N ^ k` shifts the residue by exactly `k`.
  have hpow : ∀ k : ℕ, ∀ x y : Fin (n * i), (N ^ k) x y ≠ 0 →
      (y.modNat : ℕ) = (x.modNat : ℕ) + k := by
    intro k
    induction k with
    | zero =>
      intro x y hne
      have hxy : x = y := by
        by_contra h
        exact hne (Matrix.one_apply_ne h)
      subst hxy
      simp
    | succ k ih =>
      intro x y hne
      rw [pow_succ, Matrix.mul_apply] at hne
      obtain ⟨z, hz⟩ : ∃ z, (N ^ k) x z * N z y ≠ 0 := by
        by_contra h
        simp only [not_exists, not_not] at h
        exact hne (Finset.sum_eq_zero fun z _ => h z)
      have hxz : (N ^ k) x z ≠ 0 := fun h => hz (by rw [h, zero_mul])
      have hzy : N z y ≠ 0 := fun h => hz (by rw [h, mul_zero])
      have h1 := ih x z hxz
      have h2 := hN z y hzy
      omega
  -- For `k = i` the residue would have to be `≥ i`, impossible for `Fin i`.
  ext x y
  rw [Matrix.zero_apply]
  by_contra h
  have h1 := hpow i x y h
  have h2 := y.modNat.isLt
  omega

end Work.ORHughesFree.NaturalExtension
