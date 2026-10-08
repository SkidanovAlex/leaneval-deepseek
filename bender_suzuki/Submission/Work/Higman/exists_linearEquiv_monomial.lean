import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- **Coordinate adjustment for the monomial form (Higman 1963, Lemma 11, final step).**  If
`Q α = c * α ^ (2 ^ i + 2 ^ j)` on `GF(2 ^ n)` with `c ≠ 0`, `i < j < n` and
`gcd (2 ^ (j - i) + 1, 2 ^ n - 1) = 1`, then an `𝔽₂`-linear change of coordinates turns `Q` into
the monomial `β ↦ β ^ (1 + 2 ^ (j - i))`: there is `φ` with `Q α = (φ α) ^ (1 + 2 ^ (j - i))`.

Indeed `2 ^ i + 2 ^ j = 2 ^ i * (1 + 2 ^ (j-i))` and one takes `φ = (· * λ) ∘ (· ^ (2^i))` with
`λ ^ (1 + 2 ^ (j-i)) = c`; such `λ ∈ GF(2^n)` exists because the map `x ↦ x ^ (1+2^(j-i))` is a
bijection on the cyclic group `GF(2^n)ˣ` when `gcd (1 + 2 ^ (j-i), 2 ^ n - 1) = 1`. -/
theorem exists_linearEquiv_monomial
    {n i j : ℕ} (hi : i < j) (hj : j < n)
    (hcop : (2 ^ (j - i) + 1).Coprime (2 ^ n - 1))
    (c : GaloisField 2 n) (hc : c ≠ 0)
    (Q : GaloisField 2 n → GaloisField 2 n)
    (hQ : ∀ α, Q α = c * α ^ (2 ^ i + 2 ^ j)) :
    ∃ φ : GaloisField 2 n ≃ₗ[ZMod 2] GaloisField 2 n,
      ∀ α, Q α = (φ α) ^ (1 + 2 ^ (j - i)) := by
  classical
  -- `n ≠ 0`, so that `GF(2^n)` has `2^n` elements and `2^n - 1` units.
  have hn : n ≠ 0 := by omega
  have hcardK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn
  have hcardU : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, hcardK]
  -- The exponent we want to invert.
  set m : ℕ := 1 + 2 ^ (j - i) with hm
  have hcopU : (Nat.card (GaloisField 2 n)ˣ).Coprime m := by
    rw [hcardU, hm, add_comm]
    exact hcop.symm
  -- Existence of the scalar `l` with `l ^ m = c`.
  obtain ⟨l, hl⟩ := (Nat.Coprime.pow_left_bijective hcopU).surjective (Units.mk0 c hc)
  have hlval : (l : GaloisField 2 n) ^ m = c := by
    have := congr_arg (Units.val) hl
    simpa using this
  -- The coordinate change `φ α = l * α ^ (2 ^ i)`.
  let f : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n :=
    { toFun := fun α => (l : GaloisField 2 n) * α ^ (2 ^ i)
      map_add' := by
        intro α β
        rw [add_pow_char_pow α β 2 i, mul_add]
      map_smul' := by
        intro r x
        have h01 : r = 0 ∨ r = 1 := by revert r; decide
        rcases h01 with h | h
        · subst h
          simp [zero_pow (pow_ne_zero i (by norm_num : (2:ℕ) ≠ 0))]
        · subst h; simp }
  have hker : ∀ α, f α = 0 → α = 0 := by
    intro α hα
    have h1 : (l : GaloisField 2 n) * α ^ (2 ^ i) = 0 := hα
    have h2 : α ^ (2 ^ i) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h (Units.ne_zero l)
      · exact h
    exact (pow_eq_zero_iff (pow_ne_zero i (by norm_num : (2:ℕ) ≠ 0))).mp h2
  have hinj : Function.Injective f := by
    intro α β h
    have h1 : f (α - β) = 0 := by rw [map_sub, h, sub_self]
    have h2 := hker (α - β) h1
    rwa [sub_eq_zero] at h2
  have hsurj : Function.Surjective f := (Finite.injective_iff_surjective).mp hinj
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro α
  rw [hQ α]
  have hcoe : (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩ : GaloisField 2 n → GaloisField 2 n) α
      = (l : GaloisField 2 n) * α ^ (2 ^ i) := rfl
  rw [hcoe, mul_pow, ← pow_mul, hlval]
  have hexp : 2 ^ i * m = 2 ^ i + 2 ^ j := by
    rw [hm, mul_add, mul_one, ← pow_add, Nat.add_sub_of_le (le_of_lt hi)]
  rw [hexp]

end Work.Higman
