import Mathlib

namespace Commons.Lattice.Counting

/-- Every interval `[a, a + m)` of length `m` contains a multiple of `m`
(when `m ≥ 1`): the least multiple of `m` that is at least `a` is `< a + m`. -/
lemma divisibility_tower_mul_lt_add : ∀ a : ℕ, ∀ m : ℕ, 1 ≤ m →
    ∃ t : ℕ, a ≤ t * m ∧ t * m < a + m
  | 0, m, hm => by
      exact ⟨0, by omega⟩
  | a + 1, m, hm => by
      rcases divisibility_tower_mul_lt_add a m hm with ⟨t, hle, hlt⟩
      by_cases h : a + 1 ≤ t * m
      · exact ⟨t, h, by omega⟩
      · have heq : t * m = a := by omega
        refine ⟨t + 1, ?_, ?_⟩
        · calc
            a + 1 ≤ a + m := by omega
            _ = t * m + m := by rw [heq]
            _ = (t + 1) * m := by ring
        · calc
            (t + 1) * m = t * m + m := by ring
            _ = a + m := by rw [heq]
            _ < a + m + 1 := by omega
            _ = (a + 1) + m := by omega

/-- If `m ≥ 1` and `m < 2a`, then the interval `[a, 2a)` contains a multiple
of `m`. -/
lemma divisibility_tower_mul_between (a m : ℕ) (hm : 1 ≤ m) (h : m < 2 * a) :
    ∃ t : ℕ, a ≤ t * m ∧ t * m < 2 * a := by
  by_cases hma : m ≤ a
  · rcases divisibility_tower_mul_lt_add a m hm with ⟨t, hle, hlt⟩
    refine ⟨t, hle, ?_⟩
    calc
      t * m < a + m := hlt
      _ ≤ a + a := by omega
      _ = 2 * a := by ring
  · have ham : a < m := by omega
    refine ⟨1, ?_, ?_⟩
    · simpa using Nat.le_of_lt ham
    · simpa using h

/-- Generalised tower: given an admissible top value `m` with
`q d ≤ m < 2 * q d`, one can fill in `n k` for all `1 ≤ k ≤ d`. -/
lemma divisibility_tower_aux (d : ℕ) :
    ∀ (q : ℕ → ℕ),
      (∀ k : ℕ, 1 ≤ k → k ≤ d → 1 ≤ q k) →
      (∀ k : ℕ, 1 ≤ k → k < d → q (k + 1) ≤ q k) →
      ∀ m : ℕ, q d ≤ m → m < 2 * q d →
      ∃ n : ℕ → ℕ,
        n d = m ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ d → q k ≤ n k ∧ n k < 2 * q k) ∧
        (∀ k : ℕ, 1 ≤ k → k < d → n (k + 1) ∣ n k) := by
  induction d with
  | zero =>
      intro q hq hmono m hle hlt
      refine ⟨fun _ => m, rfl, ?_, ?_⟩
      · intro k hk1 hkd
        omega
      · intro k hk1 hkd
        omega
  | succ d ih =>
      intro q hq hmono m hle hlt
      by_cases hd0 : d = 0
      · subst d
        refine ⟨fun _ => m, rfl, ?_, ?_⟩
        · intro k hk1 hkd
          have hk : k = 1 := by omega
          subst k
          exact ⟨hle, hlt⟩
        · intro k hk1 hkd
          omega
      · have hd1 : 1 ≤ d := by omega
        -- top value m is positive: m ≥ q (d + 1) ≥ 1
        have hq_d1 : 1 ≤ q (d + 1) := hq (d + 1) (by omega) (by omega)
        have hm1 : 1 ≤ m := by omega
        -- m < 2 * q d by monotonicity at index d
        have hmono_d : q (d + 1) ≤ q d := hmono d hd1 (by omega)
        have hm_lt_qd : m < 2 * q d := by omega
        -- choose a multiple md of m inside [q d, 2 * q d)
        rcases divisibility_tower_mul_between (q d) m hm1 hm_lt_qd with
          ⟨t, hmd_ge, hmd_lt⟩
        let md : ℕ := t * m
        have hmd_ge' : q d ≤ md := hmd_ge
        have hmd_lt' : md < 2 * q d := hmd_lt
        have hmd_dvd : m ∣ md := by
          refine ⟨t, ?_⟩
          simp [md]
          exact Nat.mul_comm t m
        -- solve the subproblem on the first d levels
        have hq_d : ∀ k : ℕ, 1 ≤ k → k ≤ d → 1 ≤ q k := by
          intro k hk1 hkd
          exact hq k hk1 (by omega)
        have hmono_d' : ∀ k : ℕ, 1 ≤ k → k < d → q (k + 1) ≤ q k := by
          intro k hk1 hkd
          exact hmono k hk1 (by omega)
        rcases ih q hq_d hmono_d' md hmd_ge' hmd_lt' with
          ⟨n', hn'_top, hn'_bnd, hn'_dvd⟩
        -- extend n' by putting m on top at index d + 1
        let n : ℕ → ℕ := fun k => if k ≤ d then n' k else m
        have hsame : ∀ k : ℕ, k ≤ d → n k = n' k := by
          intro k hk
          simp [n, hk]
        have htop : n (d + 1) = m := by
          have hnot : ¬ d + 1 ≤ d := by omega
          simp [n, hnot]
        refine ⟨n, htop, ?_, ?_⟩
        · intro k hk1 hkd
          by_cases hkd' : k ≤ d
          · have hb := hn'_bnd k hk1 hkd'
            rw [hsame k hkd']
            exact hb
          · have hkeq : k = d + 1 := by omega
            subst k
            rw [htop]
            exact ⟨hle, hlt⟩
        · intro k hk1 hkd
          have hkd' : k ≤ d := by omega
          by_cases hk_eq_d : k = d
          · subst k
            rw [htop]
            rw [hsame d (by omega)]
            rw [hn'_top]
            exact hmd_dvd
          · have hk_lt_d : k < d := by omega
            have hb := hn'_dvd k hk1 hk_lt_d
            rw [hsame (k + 1) (by omega)]
            rw [hsame k hkd']
            exact hb

theorem divisibility_tower (d : ℕ) (hd : 1 ≤ d) (q : ℕ → ℕ)
    (hq : ∀ k : ℕ, 1 ≤ k → k ≤ d → 1 ≤ q k)
    (hmono : ∀ k : ℕ, 1 ≤ k → k < d → q (k + 1) ≤ q k) :
    ∃ n : ℕ → ℕ,
      n d = q d ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ d → q k ≤ n k ∧ n k < 2 * q k) ∧
      (∀ k : ℕ, 1 ≤ k → k < d → n (k + 1) ∣ n k) := by
  have hqd : 1 ≤ q d := hq d hd (by omega)
  have hlt : q d < 2 * q d := by omega
  rcases divisibility_tower_aux d q hq hmono (q d) (le_rfl) hlt with
    ⟨n, htop, hbnd, hdvd⟩
  exact ⟨n, htop, hbnd, hdvd⟩

end Commons.Lattice.Counting
