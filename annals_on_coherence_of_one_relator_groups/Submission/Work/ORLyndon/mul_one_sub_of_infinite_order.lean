import Mathlib

namespace Work.ORLyndon

/-- If `c` has infinite order in a group, then the map `n ↦ c ^ n` on `ℕ` is injective. -/
theorem pow_injective_of_orderOf_eq_zero {G : Type*} [Group G] {c : G} (hc : orderOf c = 0) :
    Function.Injective (fun n : ℕ => c ^ n) := by
  rw [orderOf_eq_zero_iff'] at hc
  intro m n h
  rcases le_total m n with hmn | hnm
  · have h2 : c ^ (n - m) = 1 := by
      have h' : c ^ m = c ^ m * c ^ (n - m) := by
        rw [← pow_add, Nat.add_sub_cancel' hmn]
        exact h
      exact (mul_left_cancel (by rw [mul_one]; exact h')).symm
    rcases Nat.eq_or_lt_of_le hmn with heq | hlt
    · exact heq
    · exact absurd h2 (hc (n - m) (Nat.sub_pos_of_lt hlt))
  · have h2 : c ^ (m - n) = 1 := by
      have h' : c ^ n = c ^ n * c ^ (m - n) := by
        rw [← pow_add, Nat.add_sub_cancel' hnm]
        exact h.symm
      exact (mul_left_cancel (by rw [mul_one]; exact h')).symm
    rcases Nat.eq_or_lt_of_le hnm with heq | hlt
    · exact heq.symm
    · exact absurd h2 (hc (m - n) (Nat.sub_pos_of_lt hlt))

/-- In the group algebra `K[G]` of a group `G`, right multiplication by `1 - c` is injective
whenever `c` has infinite order.  Equivalently, `1 - c` is a non-zero-divisor (indeed `1 - c` is
not a zero divisor at all here).  The proof is the classical one: `b * (1 - c) = 0` forces
`b = b * c`, so every coefficient function is constant along the infinite orbit `x, x * c, x * c ^ 2,
…`; a finitely supported function constant on an infinite set must vanish. -/
theorem mul_one_sub_of_infinite_order {G : Type*} [Group G] {K : Type*} [Field K] {c : G}
    (hc : orderOf c = 0) :
    ∀ b : MonoidAlgebra K G, b * (1 - MonoidAlgebra.of K G c) = 0 → b = 0 := by
  have hpow_inj := pow_injective_of_orderOf_eq_zero hc
  intro b hb
  -- From `b * (1 - of c) = 0` deduce `b = b * of c`.
  have hbc : b = b * MonoidAlgebra.of K G c := by
    have hsub : b * (1 - MonoidAlgebra.of K G c) = b - b * MonoidAlgebra.of K G c := by
      rw [mul_sub, mul_one]
    rw [hsub, sub_eq_zero] at hb
    exact hb
  -- Hence every coefficient satisfies `b (x * c) = b x`.
  have hcoeff : ∀ x : G, b.coeff (x * c) = b.coeff x := by
    intro x
    conv_lhs => rw [hbc]
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_apply]
    simp
  by_contra hb0
  have hne : b.coeff ≠ 0 := by
    intro h
    exact hb0 (MonoidAlgebra.coeff_injective (by rw [h, MonoidAlgebra.coeff_zero]))
  -- Pick a group element in the support of `b`.
  obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.mpr hne
  -- The infinite set `{x * c ^ n}` is contained in the finite support.
  have hfmem : ∀ n : ℕ, x * c ^ n ∈ b.coeff.support := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
        have hstep : x * c ^ (n + 1) = (x * c ^ n) * c := by rw [pow_succ, ← mul_assoc]
        rw [hstep, Finsupp.mem_support_iff] at *
        rw [hcoeff]
        exact ih
  have hfinj : Function.Injective (fun n : ℕ => x * c ^ n) :=
    fun _ _ h => hpow_inj (mul_left_cancel h)
  have hrange : Set.range (fun n : ℕ => x * c ^ n) ⊆ (b.coeff.support : Set G) :=
    fun _ ⟨n, hn⟩ => hn ▸ hfmem n
  have hinf : (Set.range (fun n : ℕ => x * c ^ n)).Infinite :=
    Set.infinite_range_of_injective hfinj
  exact (Finset.finite_toSet b.coeff.support).not_infinite (hinf.mono hrange)

end Work.ORLyndon
