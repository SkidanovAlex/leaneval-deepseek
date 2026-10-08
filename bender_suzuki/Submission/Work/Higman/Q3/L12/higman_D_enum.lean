import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman.Q3.L12

/-! ## Auxiliary lemmas for the `D`-case enumeration -/

/-- A four-element multiset is `Nodup` iff its entries are pairwise distinct. -/
theorem nodup_four_ne {α : Type*} [DecidableEq α] {a b c d : α}
    (h : ({a, b, c, d} : Multiset α).Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have h' := h
  simp only [show ({a, b, c, d} : Multiset α) = a ::ₘ b ::ₘ c ::ₘ d ::ₘ 0 from rfl,
    Multiset.nodup_cons, Multiset.mem_cons, Multiset.nodup_zero, Multiset.notMem_zero,
    not_or, not_false_eq_true, and_true] at h'
  exact ⟨h'.1.1, h'.1.2.1, h'.1.2.2, h'.2.1.1, h'.2.1.2, h'.2.2⟩

/-- Converse of `nodup_four_ne`. -/
theorem nodup_four_of {α : Type*} [DecidableEq α] {a b c d : α} (h1 : a ≠ b) (h2 : a ≠ c)
    (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d) : ({a, b, c, d} : Multiset α).Nodup := by
  simp only [show ({a, b, c, d} : Multiset α) = a ::ₘ b ::ₘ c ::ₘ d ::ₘ 0 from rfl,
    Multiset.nodup_cons, Multiset.mem_cons, Multiset.nodup_zero, Multiset.notMem_zero,
    not_or, not_false_eq_true, and_true]
  exact ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩

theorem zmod_natCast_ne_zero {n x : ℕ} (hx : x < n) (h : x ≠ 0) :
    ((x : ℕ) : ZMod n) ≠ (0 : ZMod n) := by
  intro hh
  exact h (Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff x n).mp hh) hx)

theorem zmod_natCast_ne {n x y : ℕ} (hx : x < n) (hy : y < n) (h : x ≠ y) :
    ((x : ℕ) : ZMod n) ≠ ((y : ℕ) : ZMod n) := by
  intro hh
  exact h (Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff x y n).mp hh) hx hy)

theorem zmod_eq_zero_of_add_eq_left {n : ℕ} {x y : ZMod n} (h : x + y = x) : y = 0 := by
  have h' : x + y = x + 0 := by rw [add_zero]; exact h
  exact add_left_cancel h'

theorem zmod_eq_zero_of_add_eq_right {n : ℕ} {x y : ZMod n} (h : x + y = y) : x = 0 := by
  have h' : x + y = (0 : ZMod n) + y := by rw [zero_add]; exact h
  exact add_right_cancel h'

/-! ## Higman's enumeration -/

/-- **Higman's "the exponents must match" enumeration** (Higman 1963, p. 92, `D` case).

Let `n > 0`, let `r, s, i, j ∈ [0, n)` with `r ≠ 0`, `s ≠ 0`, `r + s ≢ 0` and `r ≢ s (mod n)`,
and suppose that the multisets of exponents `{i, i + s, j, j + r}` and `{0, r, s, r + s}` (all
reduced mod `n`) coincide.  Then, up to interchanging `(r, s, i, j)` with `(s, r, j, i)`,
`5 * r ≡ 0`, `s ≡ 2 * r`, `i ≡ 3 * r`, `j ≡ r (mod n)`. -/
theorem higman_D_enum {n r s i j : ℕ} (hn : 0 < n)
    (hr : r < n) (hs : s < n) (hi : i < n) (hj : j < n)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hrs : (r + s) % n ≠ 0) (hrms : (r + n - s) % n ≠ 0)
    (h : ({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ) = {0, r, s, (r + s) % n}) :
    (5 * r ≡ 0 [MOD n] ∧ s ≡ 2 * r [MOD n] ∧ i ≡ 3 * r [MOD n] ∧ j ≡ r [MOD n]) ∨
    (5 * s ≡ 0 [MOD n] ∧ r ≡ 2 * s [MOD n] ∧ j ≡ 3 * s [MOD n] ∧ i ≡ s [MOD n]) := by
  set a : ZMod n := (i : ZMod n) with ha
  set b : ZMod n := (j : ZMod n) with hb
  set R : ZMod n := (r : ZMod n) with hR
  set S : ZMod n := (s : ZMod n) with hS
  have hrs' : r ≠ s := by
    intro hh
    exact hrms (by rw [hh, Nat.add_sub_cancel_left, Nat.mod_self])
  have hρlt : (r + s) % n < n := Nat.mod_lt _ hn
  -- the hypothesis in `ZMod n`
  have hZ : ({a, a + S, b, b + R} : Multiset (ZMod n)) = {0, R, S, R + S} := by
    rw [ha, hb, hR, hS]
    have hc := congrArg (Multiset.map (fun x : ℕ => (x : ZMod n))) h
    have hL : (Multiset.map (fun x : ℕ => (x : ZMod n))
          ({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ))
        = ({(i : ZMod n), (i : ZMod n) + (s : ZMod n), (j : ZMod n),
            (j : ZMod n) + (r : ZMod n)} : Multiset (ZMod n)) := by
      rw [show ({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ)
          = i ::ₘ (i + s) % n ::ₘ j ::ₘ (j + r) % n ::ₘ 0 from rfl,
        show ({(i : ZMod n), (i : ZMod n) + (s : ZMod n), (j : ZMod n),
            (j : ZMod n) + (r : ZMod n)} : Multiset (ZMod n))
          = (i : ZMod n) ::ₘ ((i : ZMod n) + (s : ZMod n)) ::ₘ (j : ZMod n)
            ::ₘ ((j : ZMod n) + (r : ZMod n)) ::ₘ 0 from rfl]
      simp only [Multiset.map_cons, Multiset.map_zero, ZMod.natCast_mod, Nat.cast_add]
    have hR' : (Multiset.map (fun x : ℕ => (x : ZMod n)) ({0, r, s, (r + s) % n} : Multiset ℕ))
        = ({(0 : ZMod n), (r : ZMod n), (s : ZMod n),
            (r : ZMod n) + (s : ZMod n)} : Multiset (ZMod n)) := by
      rw [show ({0, r, s, (r + s) % n} : Multiset ℕ)
          = 0 ::ₘ r ::ₘ s ::ₘ (r + s) % n ::ₘ 0 from rfl,
        show ({(0 : ZMod n), (r : ZMod n), (s : ZMod n),
            (r : ZMod n) + (s : ZMod n)} : Multiset (ZMod n))
          = (0 : ZMod n) ::ₘ (r : ZMod n) ::ₘ (s : ZMod n)
            ::ₘ ((r : ZMod n) + (s : ZMod n)) ::ₘ 0 from rfl]
      simp only [Multiset.map_cons, Multiset.map_zero, ZMod.natCast_mod, Nat.cast_add,
        Nat.cast_zero]
    rw [hL, hR'] at hc
    exact hc
  -- distinctness of the right-hand side
  have h0R : (0 : ZMod n) ≠ R := by rw [hR]; exact (zmod_natCast_ne_zero hr hr0).symm
  have h0S : (0 : ZMod n) ≠ S := by rw [hS]; exact (zmod_natCast_ne_zero hs hs0).symm
  have hRS : R ≠ S := by rw [hR, hS]; exact zmod_natCast_ne hr hs hrs'
  have hRS0 : R + S ≠ 0 := by
    rw [hR, hS]
    have h1 : (r : ZMod n) + (s : ZMod n) = (((r + s) % n : ℕ) : ZMod n) := by
      rw [ZMod.natCast_mod, Nat.cast_add]
    rw [h1]
    exact zmod_natCast_ne_zero hρlt hrs
  have hR0 : R ≠ 0 := h0R.symm
  have hS0 : S ≠ 0 := h0S.symm
  have hRRS : R ≠ R + S := by
    intro hh
    have h1 : R + (0 : ZMod n) = R + S := by rw [add_zero]; exact hh
    exact hS0 (add_left_cancel h1).symm
  have hSRS : S ≠ R + S := by
    intro hh
    have h1 : S + (0 : ZMod n) = S + R := by rw [add_zero, add_comm]; exact hh
    exact hR0 (add_left_cancel h1).symm
  have h0RS : (0 : ZMod n) ≠ R + S := hRS0.symm
  have hRSS : R + S ≠ S := by
    intro hh
    exact hR0 (by linear_combination hh)
  have hRSR : R + S ≠ R := by
    intro hh
    exact hS0 (by linear_combination hh)
  have hBnodup : ({0, R, S, R + S} : Multiset (ZMod n)).Nodup :=
    nodup_four_of h0R h0S hRS0.symm hRS hRRS hSRS
  have hAnodup : ({a, a + S, b, b + R} : Multiset (ZMod n)).Nodup := by
    rw [hZ]; exact hBnodup
  -- `hne` : the pairwise distinctness of `a, a+S, b, b+R`
  have hne := nodup_four_ne hAnodup
  have hF : ({a, a + S, b, b + R} : Finset (ZMod n)) = {0, R, S, R + S} := by
    have h1 := congrArg Multiset.toFinset hZ
    simpa using h1
  have hamem : a ∈ ({0, R, S, R + S} : Finset (ZMod n)) := by rw [← hF]; simp
  have h2Smem : a + S ∈ ({0, R, S, R + S} : Finset (ZMod n)) := by rw [← hF]; simp
  -- every element of the right-hand set lies in the left-hand one
  have hmemR : R ∈ ({a, a + S, b, b + R} : Finset (ZMod n)) := by rw [hF]; simp
  have hmemS : S ∈ ({a, a + S, b, b + R} : Finset (ZMod n)) := by rw [hF]; simp
  have hmemRS : R + S ∈ ({a, a + S, b, b + R} : Finset (ZMod n)) := by rw [hF]; simp
  have hmem0 : (0 : ZMod n) ∈ ({a, a + S, b, b + R} : Finset (ZMod n)) := by rw [hF]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hamem h2Smem hmemR hmemS hmemRS hmem0
  rcases hamem with ha0 | haR | haS | haRS
  · -- ## `a = 0`
    rw [ha0] at hmemR hmemRS
    simp only [zero_add] at hmemR hmemRS
    have h1 : R = b ∨ R = b + R := by
      rcases hmemR with h | h | h | h
      · exact absurd h hR0
      · exact absurd h hRS
      · exact Or.inl h
      · exact Or.inr h
    have h2 : R + S = b ∨ R + S = b + R := by
      rcases hmemRS with h | h | h | h
      · exact absurd h hRS0
      · exact absurd (zmod_eq_zero_of_add_eq_right h) hR0
      · exact Or.inl h
      · exact Or.inr h
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso; exact hS0 (zmod_eq_zero_of_add_eq_left (by rw [← h1] at h2; exact h2))
    · exfalso; exact hRS.symm (add_left_cancel (by rw [← h1] at h2; exact h2))
    · exfalso; exact hRS0 (by rw [h2]; exact zmod_eq_zero_of_add_eq_right h1.symm)
    · exfalso; exact hS0 (zmod_eq_zero_of_add_eq_left
        (by rw [zmod_eq_zero_of_add_eq_right h1.symm, zero_add] at h2; exact h2))
  · -- ## `a = R`
    rw [haR] at hmemS hmem0
    have h1 : b = 0 ∨ b + R = 0 := by
      rcases hmem0 with h | h | h | h
      · exact absurd h.symm hR0
      · exact absurd h.symm hRS0
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have h2 : S = b ∨ S = b + R := by
      rcases hmemS with h | h | h | h
      · exact absurd h hRS.symm
      · exact absurd (zmod_eq_zero_of_add_eq_right h.symm) hR0
      · exact Or.inl h
      · exact Or.inr h
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso; exact hS0 (by rw [h2, h1])
    · exfalso; exact hRS.symm (by rw [h2, h1, zero_add])
    · exfalso; exact hRS0 (by rw [h2, add_comm]; exact h1)
    · exfalso; exact hS0 (by rw [h2]; exact h1)
  · -- ## `a = S`
    rw [haS] at h2Smem
    rcases h2Smem with h2S0 | h2SR | h2SS | h2SRS
    · -- `S + S = 0`
      rw [haS, h2S0] at hmemR hmemRS
      have h1 : R = b ∨ R = b + R := by
        rcases hmemR with h | h | h | h
        · exact absurd h hRS
        · exact absurd h hR0
        · exact Or.inl h
        · exact Or.inr h
      have h2 : R + S = b ∨ R + S = b + R := by
        rcases hmemRS with h | h | h | h
        · exact absurd (zmod_eq_zero_of_add_eq_right h) hR0
        · exact absurd h hRS0
        · exact Or.inl h
        · exact Or.inr h
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exfalso; exact hS0 (zmod_eq_zero_of_add_eq_left (by rw [← h1] at h2; exact h2))
      · exfalso; exact hRS.symm (add_left_cancel (by rw [← h1] at h2; exact h2))
      · exfalso; exact hRS0 (by rw [h2]; exact zmod_eq_zero_of_add_eq_right h1.symm)
      · exfalso; exact hS0 (zmod_eq_zero_of_add_eq_left
          (by rw [zmod_eq_zero_of_add_eq_right h1.symm, zero_add] at h2; exact h2))
    · -- `S + S = R`: the second alternative or a contradiction
      rw [haS, h2SR] at hmem0 hmemRS
      have h1 : b = 0 ∨ b + R = 0 := by
        rcases hmem0 with h | h | h | h
        · exact absurd h.symm hS0
        · exact absurd h.symm hR0
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      have h2 : R + S = b ∨ R + S = b + R := by
        rcases hmemRS with h | h | h | h
        · exact absurd (zmod_eq_zero_of_add_eq_right h) hR0
        · exact absurd (zmod_eq_zero_of_add_eq_left h) hS0
        · exact Or.inl h
        · exact Or.inr h
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exfalso; exact hRS0 (by rw [h2, h1])
      · exfalso; exact hS0 (zmod_eq_zero_of_add_eq_left (by rw [h1, zero_add] at h2; exact h2))
      · -- `b + R = 0`, `R + S = b`: the second alternative
        have hR2S : R = 2 * S := by rw [← h2SR]; ring
        have h5S : (5 : ZMod n) * S = 0 := by
          have h3 : R + S + R = 0 := by rw [h2]; exact h1
          rw [hR2S] at h3
          linear_combination h3
        have hb3S : b = 3 * S := by rw [← h2, hR2S]; ring
        refine Or.inr ⟨?_, ?_, ?_, ?_⟩
        · exact (ZMod.natCast_eq_natCast_iff (5 * s) 0 n).mp
            (by push_cast; rw [← hS]; exact h5S)
        · exact (ZMod.natCast_eq_natCast_iff r (2 * s) n).mp
            (by push_cast; rw [← hR, ← hS]; exact hR2S)
        · exact (ZMod.natCast_eq_natCast_iff j (3 * s) n).mp
            (by push_cast; rw [← hb, ← hS]; exact hb3S)
        · exact (ZMod.natCast_eq_natCast_iff i s n).mp (by rw [← ha, ← hS]; exact haS)
      · exfalso; exact hRS0 (by rw [h2, h1])
    · -- `S + S = S`
      exfalso
      exact hS0 (zmod_eq_zero_of_add_eq_left h2SS)
    · -- `S + S = R + S`
      exfalso
      exact hRS.symm (add_right_cancel h2SRS)
  · -- ## `a = R + S`
    rw [haRS] at h2Smem
    rcases h2Smem with h4a | h4b | h4c | h4d
    · -- `(R + S) + S = 0`: the first alternative or a contradiction
      rw [haRS, h4a] at hmemR hmemS
      have h1 : R = b ∨ R = b + R := by
        rcases hmemR with h | h | h | h
        · exact absurd h hRRS
        · exact absurd h hR0
        · exact Or.inl h
        · exact Or.inr h
      have h2 : S = b ∨ S = b + R := by
        rcases hmemS with h | h | h | h
        · exact absurd h hSRS
        · exact absurd h hS0
        · exact Or.inl h
        · exact Or.inr h
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exfalso; exact hRS (by rw [h1, ← h2])
      · -- `R = b`, `S = b + R`: the first alternative
        have hS2R : S = 2 * R := by rw [h2, h1]; ring
        have h5R : (5 : ZMod n) * R = 0 := by
          rw [hS2R] at h4a
          linear_combination h4a
        have ha3R : a = 3 * R := by rw [haRS, hS2R]; ring
        refine Or.inl ⟨?_, ?_, ?_, ?_⟩
        · exact (ZMod.natCast_eq_natCast_iff (5 * r) 0 n).mp
            (by push_cast; rw [← hR]; exact h5R)
        · exact (ZMod.natCast_eq_natCast_iff s (2 * r) n).mp
            (by push_cast; rw [← hS, ← hR]; exact hS2R)
        · exact (ZMod.natCast_eq_natCast_iff i (3 * r) n).mp
            (by push_cast; rw [← ha, ← hR]; exact ha3R)
        · exact (ZMod.natCast_eq_natCast_iff j r n).mp (by rw [← hb, ← hR]; exact h1.symm)
      · exfalso; exact hS0 (by rw [h2, zmod_eq_zero_of_add_eq_right h1.symm])
      · exfalso; exact hRS.symm (by rw [h2, zmod_eq_zero_of_add_eq_right h1.symm, zero_add])
    · -- `(R + S) + S = R`
      rw [haRS, h4b] at hmem0 hmemS
      have h1 : b = 0 ∨ b + R = 0 := by
        rcases hmem0 with h | h | h | h
        · exact absurd h.symm hRS0
        · exact absurd h.symm hR0
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      have h2 : S = b ∨ S = b + R := by
        rcases hmemS with h | h | h | h
        · exact absurd h hSRS
        · exact absurd h hRS.symm
        · exact Or.inl h
        · exact Or.inr h
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exfalso; exact hS0 (by rw [h2, h1])
      · exfalso; exact hRS.symm (by rw [h2, h1, zero_add])
      · exfalso; exact hRS0 (by rw [h2, add_comm]; exact h1)
      · exfalso; exact hS0 (by rw [h2]; exact h1)
    · -- `(R + S) + S = S`
      exfalso
      exact hRS0 (zmod_eq_zero_of_add_eq_right h4c)
    · -- `(R + S) + S = R + S`
      exfalso
      exact hS0 (zmod_eq_zero_of_add_eq_left h4d)

end Work.Higman.Q3.L12
