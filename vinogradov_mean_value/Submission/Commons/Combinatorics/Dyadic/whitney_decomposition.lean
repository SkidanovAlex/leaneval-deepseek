import Mathlib

namespace Commons.Combinatorics.Dyadic

/-!
# A dyadic (Whitney) decomposition for pairs of integers

For a pair of integers `a ≠ b` with `|a - b| ≥ 2` inside `[0, 2^N)` there is a unique
dyadic scale `n ∈ [2, N]` at which the two top-`n`-bits truncations of `a` and `b`
become separated, with the difference of the two truncated values equal to `2` or `3`
and with the two values lying in the same or adjacent dyadic half-blocks.
-/

/-! ## Elementary two-adic facts -/

/-- Truncating the level-`j` truncation at level `1` gives the level-`j+1` truncation. -/
private lemma div_pow_two_div_two (m j : ℕ) : m / 2 ^ j / 2 = m / 2 ^ (j + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-- The absolute difference of the level-`j` truncations is twice the absolute difference
of the level-`j+1` truncations, up to an error of at most one bit. -/
private lemma abs_abs_sub_two_mul_abs (m n : ℕ) :
    abs (abs ((m : ℤ) - (n : ℤ)) - 2 * abs (((m / 2 : ℕ) : ℤ) - ((n / 2 : ℕ) : ℤ))) ≤ 1 := by
  have hm : (m : ℤ) = 2 * ((m / 2 : ℕ) : ℤ) + ((m % 2 : ℕ) : ℤ) := by
    have h := Nat.div_add_mod m 2
    omega
  have hn : (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ) + ((n % 2 : ℕ) : ℤ) := by
    have h := Nat.div_add_mod n 2
    omega
  have hs : abs (((m % 2 : ℕ) : ℤ) - ((n % 2 : ℕ) : ℤ)) ≤ 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one n with h' | h' <;>
        rw [h, h'] <;> norm_num
  have hX : (m : ℤ) - (n : ℤ) =
      2 * (((m / 2 : ℕ) : ℤ) - ((n / 2 : ℕ) : ℤ)) +
        (((m % 2 : ℕ) : ℤ) - ((n % 2 : ℕ) : ℤ)) := by
    rw [hm, hn]; ring
  have hY : ((m : ℤ) - (n : ℤ)) - 2 * (((m / 2 : ℕ) : ℤ) - ((n / 2 : ℕ) : ℤ)) =
      ((m % 2 : ℕ) : ℤ) - ((n % 2 : ℕ) : ℤ) := by
    rw [hX]; ring
  calc abs (abs ((m : ℤ) - (n : ℤ)) - 2 * abs (((m / 2 : ℕ) : ℤ) - ((n / 2 : ℕ) : ℤ)))
      = abs (abs ((m : ℤ) - (n : ℤ)) -
          abs (2 * (((m / 2 : ℕ) : ℤ) - ((n / 2 : ℕ) : ℤ)))) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)]
    _ ≤ abs (((m : ℤ) - (n : ℤ)) - 2 * (((m / 2 : ℕ) : ℤ) - ((n / 2 : ℕ) : ℤ))) :=
        abs_abs_sub_abs_le_abs_sub _ _
    _ ≤ 1 := by rw [hY]; exact hs

/-- Consecutive truncated differences of two integers satisfy the two-adic step relation. -/
private lemma abs_div_sub_step (a b j : ℕ) :
    abs (abs (((a / 2 ^ j : ℕ) : ℤ) - ((b / 2 ^ j : ℕ) : ℤ)) -
        2 * abs (((a / 2 ^ (j + 1) : ℕ) : ℤ) - ((b / 2 ^ (j + 1) : ℕ) : ℤ))) ≤ 1 := by
  have h := abs_abs_sub_two_mul_abs (a / 2 ^ j) (b / 2 ^ j)
  rwa [div_pow_two_div_two a j, div_pow_two_div_two b j] at h

/-- If the difference of two integers has absolute value `2` or `3`, the smaller of the
two lies in one of the four positions determined by the larger one. -/
private lemma mem_four_of_abs_sub {i c : ℕ}
    (h : |(i : ℤ) - (c : ℤ)| = 2 ∨ |(i : ℤ) - (c : ℤ)| = 3) :
    c ∈ ({i - 3, i - 2, i + 2, i + 3} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases h with h | h
  · rw [abs_eq (by norm_num : (0 : ℤ) ≤ 2)] at h
    omega
  · rw [abs_eq (by norm_num : (0 : ℤ) ≤ 3)] at h
    omega

/-! ## The abstract stopping time -/

/-- Abstract dyadic stopping-time lemma: a nonnegative integer sequence which is
`2`-Lipschitz for the doubling map, starts at `≥ 2` and ends at `0`, has a unique
index `J` at which it is still `≥ 2` but has dropped to `≤ 1` at the next step; at
that index it is at most `3`. -/
private lemma exists_unique_index (v : ℕ → ℤ) (N : ℕ) (hN : 2 ≤ N) (hv : ∀ j, 0 ≤ v j)
    (h0 : 2 ≤ v 0) (hNv : v N = 0) (hstep : ∀ j, |v j - 2 * v (j + 1)| ≤ 1) :
    ∃ J : ℕ, J + 2 ≤ N ∧ 2 ≤ v J ∧ v J ≤ 3 ∧ v (J + 1) ≤ 1 ∧
      ∀ j : ℕ, j + 2 ≤ N → 2 ≤ v j → v j ≤ 3 → v (j + 1) ≤ 1 → j = J := by
  have hex : ∃ k, v (k + 1) ≤ 1 := ⟨N - 1, by
    rw [Nat.sub_add_cancel (by omega), hNv]; norm_num⟩
  have hmono : ∀ j, v (j + 1) ≤ v j := by
    intro j
    have h := hstep j
    rw [abs_le] at h
    by_cases hc : v (j + 1) ≤ 0
    · have := hv j; have := hv (j + 1); linarith
    · linarith [h.1, h.2]
  have hmono' : ∀ a b : ℕ, a ≤ b → v b ≤ v a := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact le_trans (hmono k) ih
  have hspec : v (Nat.find hex + 1) ≤ 1 := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → ¬ (v (m + 1) ≤ 1) := fun m hm => Nat.find_min hex hm
  have hge : 2 ≤ v (Nat.find hex) := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h]; exact h0
    · have hlt : Nat.find hex - 1 < Nat.find hex := by omega
      have hmin' := hmin (Nat.find hex - 1) hlt
      rw [Nat.sub_add_cancel h] at hmin'
      omega
  have hle3 : v (Nat.find hex) ≤ 3 := by
    have h := hstep (Nat.find hex)
    rw [abs_le] at h
    linarith [h.2, hspec]
  have hleN : Nat.find hex + 2 ≤ N := by
    have hle : Nat.find hex ≤ N - 1 := by
      refine Nat.find_le (show v (N - 1 + 1) ≤ 1 by
        rw [Nat.sub_add_cancel (by omega), hNv]; norm_num)
    have hne : Nat.find hex ≠ N - 1 := by
      intro heq
      have hN1 : v (N - 1) ≤ 1 := by
        have h := hstep (N - 1)
        rw [abs_le] at h
        have hz : v (N - 1 + 1) = 0 := by rw [Nat.sub_add_cancel (by omega), hNv]
        linarith [h.2, hz]
      have hlt : N - 2 < Nat.find hex := by omega
      have hc := hmin (N - 2) hlt
      rw [show N - 2 + 1 = N - 1 from by omega] at hc
      omega
    omega
  refine ⟨Nat.find hex, hleN, hge, hle3, hspec, ?_⟩
  intro j hj2 hjge hjle hjnext
  have h₁ : Nat.find hex ≤ j := by
    by_contra hcon
    have hcon' : j < Nat.find hex := not_le.mp hcon
    have := hmin j hcon'
    omega
  have h₂ : j ≤ Nat.find hex := by
    by_contra hcon
    have hcon' : Nat.find hex < j := not_le.mp hcon
    have := hmono' (Nat.find hex + 1) j (by omega)
    linarith
  omega

/-! ## The Whitney family -/

/-- The ambient box of triples `(n, x, y)` with `2 ≤ n ≤ N` and `x, y < 2^N`. -/
private def whitneyBox (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 2 N) ×ˢ ((Finset.range (2 ^ N)) ×ˢ (Finset.range (2 ^ N)))

/-- The Whitney family: triples `(n, x, y)` with `x, y < 2^n` whose difference is `2` or `3`
and which lie in the same or in adjacent dyadic half-blocks. -/
private def whitneySet (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (whitneyBox N).filter fun p =>
    (|(p.2.1 : ℤ) - (p.2.2 : ℤ)| = 2 ∨ |(p.2.1 : ℤ) - (p.2.2 : ℤ)| = 3) ∧
      |((p.2.1 / 2 : ℕ) : ℤ) - ((p.2.2 / 2 : ℕ) : ℤ)| ≤ 1 ∧ p.2.1 < 2 ^ p.1 ∧ p.2.2 < 2 ^ p.1

private lemma mem_whitneyBox {N n x y : ℕ} :
    (n, x, y) ∈ whitneyBox N ↔ 2 ≤ n ∧ n ≤ N ∧ x < 2 ^ N ∧ y < 2 ^ N := by
  rw [whitneyBox, Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_range,
    Finset.mem_range]
  tauto

private lemma mem_whitneySet {N n x y : ℕ} :
    (n, x, y) ∈ whitneySet N ↔
      2 ≤ n ∧ n ≤ N ∧ x < 2 ^ N ∧ y < 2 ^ N ∧
        (|(x : ℤ) - (y : ℤ)| = 2 ∨ |(x : ℤ) - (y : ℤ)| = 3) ∧
        |((x / 2 : ℕ) : ℤ) - ((y / 2 : ℕ) : ℤ)| ≤ 1 ∧ x < 2 ^ n ∧ y < 2 ^ n := by
  rw [whitneySet, Finset.mem_filter, mem_whitneyBox]
  tauto

/-- The difference of the level-`j` truncations, as an integer. -/
private def truncDiff (a b j : ℕ) : ℤ := |((a / 2 ^ j : ℕ) : ℤ) - ((b / 2 ^ j : ℕ) : ℤ)|

private lemma truncDiff_nonneg (a b j : ℕ) : 0 ≤ truncDiff a b j := abs_nonneg _
private lemma truncDiff_zero (a b : ℕ) : truncDiff a b 0 = |(a : ℤ) - (b : ℤ)| := by
  simp [truncDiff]
private lemma truncDiff_step (a b j : ℕ) : |truncDiff a b j - 2 * truncDiff a b (j + 1)| ≤ 1 := by
  simpa only [truncDiff] using abs_div_sub_step a b j

/-! ## The decomposition -/

theorem whitney_decomposition (N : ℕ) (hN : 2 ≤ N) :
    ∃ W : Finset (ℕ × ℕ × ℕ),
      (∀ p ∈ W, 2 ≤ p.1 ∧ p.1 ≤ N ∧ p.2.1 < 2 ^ p.1 ∧ p.2.2 < 2 ^ p.1 ∧
        (|(p.2.1 : ℤ) - (p.2.2 : ℤ)| = 2 ∨ |(p.2.1 : ℤ) - (p.2.2 : ℤ)| = 3)) ∧
      (∀ p ∈ W, |((p.2.1 / 2 : ℕ) : ℤ) - ((p.2.2 / 2 : ℕ) : ℤ)| ≤ 1) ∧
      (∀ n, 2 ≤ n → n ≤ N → ∀ i, i < 2 ^ n →
        (W.filter (fun p => p.1 = n ∧ (p.2.1 = i ∨ p.2.2 = i))).card ≤ 8) ∧
      (∀ a : ℕ, a < 2 ^ N → ∀ b : ℕ, b < 2 ^ N → 2 ≤ |(a : ℤ) - (b : ℤ)| →
        ∃! p : ℕ × ℕ × ℕ, p ∈ W ∧ a / 2 ^ (N - p.1) = p.2.1 ∧ b / 2 ^ (N - p.1) = p.2.2) := by
  refine ⟨whitneySet N, ?_, ?_, ?_, ?_⟩
  · rintro ⟨n, x, y⟩ hp
    rw [mem_whitneySet] at hp
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
    exact ⟨h1, h2, h7, h8, h5⟩
  · rintro ⟨n, x, y⟩ hp
    rw [mem_whitneySet] at hp
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
    exact h6
  · intro n hn2 hnN i hi
    have hsub : (whitneySet N).filter (fun p => p.1 = n ∧ (p.2.1 = i ∨ p.2.2 = i)) ⊆
        ({i - 3, i - 2, i + 2, i + 3} : Finset ℕ).biUnion
          (fun y => ({((n, i, y) : ℕ × ℕ × ℕ), ((n, y, i) : ℕ × ℕ × ℕ)} :
            Finset (ℕ × ℕ × ℕ))) := by
      rintro ⟨a, b, c⟩ hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpW, hp1, hp2⟩ := hp
      subst hp1
      rw [mem_whitneySet] at hpW
      obtain ⟨-, -, -, -, habs, -, -, -⟩ := hpW
      rw [Finset.mem_biUnion]
      rcases hp2 with hb | hc
      · subst hb
        exact ⟨c, mem_four_of_abs_sub habs, by simp⟩
      · subst hc
        refine ⟨b, ?_, ?_⟩
        · rcases habs with h | h
          · exact mem_four_of_abs_sub (Or.inl (by rw [abs_sub_comm]; exact h))
          · exact mem_four_of_abs_sub (Or.inr (by rw [abs_sub_comm]; exact h))
        · simp
    calc ((whitneySet N).filter (fun p => p.1 = n ∧ (p.2.1 = i ∨ p.2.2 = i))).card
        ≤ (({i - 3, i - 2, i + 2, i + 3} : Finset ℕ).biUnion
            (fun y => ({((n, i, y) : ℕ × ℕ × ℕ), ((n, y, i) : ℕ × ℕ × ℕ)} :
              Finset (ℕ × ℕ × ℕ)))).card := Finset.card_le_card hsub
      _ ≤ ∑ y ∈ ({i - 3, i - 2, i + 2, i + 3} : Finset ℕ),
            ({((n, i, y) : ℕ × ℕ × ℕ), ((n, y, i) : ℕ × ℕ × ℕ)} :
              Finset (ℕ × ℕ × ℕ)).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ ({i - 3, i - 2, i + 2, i + 3} : Finset ℕ), 2 := by
          apply Finset.sum_le_sum
          intro y _
          exact Finset.card_le_two
      _ = 2 * ({i - 3, i - 2, i + 2, i + 3} : Finset ℕ).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 8 := by
          have h4 : ({i - 3, i - 2, i + 2, i + 3} : Finset ℕ).card ≤ 4 := by
            have h₁ := Finset.card_insert_le (i - 3) ({i - 2, i + 2, i + 3} : Finset ℕ)
            have h₂ := Finset.card_insert_le (i - 2) ({i + 2, i + 3} : Finset ℕ)
            have h₃ := Finset.card_insert_le (i + 2) ({i + 3} : Finset ℕ)
            rw [Finset.card_singleton] at h₃
            omega
          omega
  · intro a ha b hb hab
    have hv : ∀ j, 0 ≤ truncDiff a b j := fun j => truncDiff_nonneg a b j
    have h0 : 2 ≤ truncDiff a b 0 := by rw [truncDiff_zero]; exact hab
    have hNv : truncDiff a b N = 0 := by
      have h1 : a / 2 ^ N = 0 := Nat.div_eq_of_lt ha
      have h2 : b / 2 ^ N = 0 := Nat.div_eq_of_lt hb
      simp [truncDiff, h1, h2]
    obtain ⟨J, hJ2, hJge, hJle, hJnext, huniq⟩ :=
      exists_unique_index (truncDiff a b) N hN hv h0 hNv (fun j => truncDiff_step a b j)
    have hJN : J ≤ N := by omega
    refine ⟨(N - J, a / 2 ^ J, b / 2 ^ J), ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [mem_whitneySet]
      refine ⟨by omega, by omega, by have := Nat.div_le_self a (2 ^ J); omega,
        by have := Nat.div_le_self b (2 ^ J); omega, ?_, ?_, ?_, ?_⟩
      · change (truncDiff a b J = 2) ∨ (truncDiff a b J = 3)
        rcases lt_or_ge (truncDiff a b J) 3 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      · rw [div_pow_two_div_two a J, div_pow_two_div_two b J]
        exact hJnext
      · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hJN]
        exact ha
      · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hJN]
        exact hb
    · show a / 2 ^ (N - (N - J)) = a / 2 ^ J
      rw [Nat.sub_sub_self hJN]
    · show b / 2 ^ (N - (N - J)) = b / 2 ^ J
      rw [Nat.sub_sub_self hJN]
    · intro q ⟨hqW, hq1, hq2⟩
      rw [mem_whitneySet] at hqW
      obtain ⟨hq2', hqN, -, -, habs, hfloor, -, -⟩ := hqW
      have hq1' : a / 2 ^ (N - q.1) = q.2.1 := hq1
      have hq2'' : b / 2 ^ (N - q.1) = q.2.2 := hq2
      have hjm : N - q.1 + 2 ≤ N := by
        have h := Nat.sub_le_sub_left hq2' N
        calc N - q.1 + 2 ≤ (N - 2) + 2 := Nat.add_le_add_right h 2
          _ = N := Nat.sub_add_cancel hN
      have hvj : 2 ≤ truncDiff a b (N - q.1) := by
        rw [truncDiff, hq1', hq2'']
        rcases habs with h | h <;> simp [h]
      have hvj3 : truncDiff a b (N - q.1) ≤ 3 := by
        rw [truncDiff, hq1', hq2'']
        rcases habs with h | h <;> simp [h]
      have hvj1 : truncDiff a b (N - q.1 + 1) ≤ 1 := by
        rw [truncDiff, ← div_pow_two_div_two a (N - q.1), ← div_pow_two_div_two b (N - q.1),
          hq1', hq2'']
        exact hfloor
      have hJeq : N - q.1 = J := huniq (N - q.1) hjm hvj hvj3 hvj1
      have hq1J : q.1 = N - J := by omega
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show q.1 = N - J
        omega
      · show q.2.1 = a / 2 ^ J
        rw [← hq1', hq1J, Nat.sub_sub_self hJN]
      · show q.2.2 = b / 2 ^ J
        rw [← hq2'', hq1J, Nat.sub_sub_self hJN]

end Commons.Combinatorics.Dyadic
