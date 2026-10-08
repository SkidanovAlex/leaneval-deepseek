import Mathlib

namespace Work.BSW.Char

/-- The "k = 3" arithmetic configuration of Bender's §2 cannot occur.

Concretely: there are no `n, d1, d2, d3` with `n ≥ 5`, `n ≡ 1 (mod 4)`, `3 ∣ n`,
`dᵢ ≥ 3`, `1 + d1² + d2² + d3² ≤ 12n` and `1 − 1/d1 − 1/d2 − 1/d3 = 8/(3n)`.

The proof is a finite check driven by two crudely sharp bounds:
since the `dᵢ ≥ 3` are not all `3` (otherwise the right-hand side would be `0`),
one of them is `≥ 4` and hence `1 − 1/d1 − 1/d2 − 1/d3 ≥ 1/12`, forcing `n ≤ 32`;
with `n ≡ 1 (mod 4)` and `3 ∣ n` this leaves `n = 9` or `n = 21`.
For `n = 21` the equation forces every `dᵢ ≤ 4`; for `n = 9` the inequality forces
every `dᵢ ≤ 9`.  Enumerating the resulting finitely many cases contradicts `heq`. -/
theorem k3_impossible (n : ℕ) (hn : 5 ≤ n) (hmod4 : n % 4 = 1) (h3dvd : 3 ∣ n)
    (d1 d2 d3 : ℕ) (hd1 : 3 ≤ d1) (hd2 : 3 ≤ d2) (hd3 : 3 ≤ d3)
    (hineq : 1 + d1 ^ 2 + d2 ^ 2 + d3 ^ 2 ≤ 12 * n)
    (heq : (1 : ℚ) - 1 / (d1 : ℚ) - 1 / (d2 : ℚ) - 1 / (d3 : ℚ) = 8 / (3 * (n : ℚ))) :
    False := by
  -- Not all of the `dᵢ` equal `3`: otherwise the equation reads `0 = 8/(3n)`.
  have hsome : 4 ≤ d1 ∨ 4 ≤ d2 ∨ 4 ≤ d3 := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2, h3⟩ := h
    have e1 : d1 = 3 := by omega
    have e2 : d2 = 3 := by omega
    have e3 : d3 = 3 := by omega
    rw [e1, e2, e3] at heq
    have hpos : (0 : ℚ) < 8 / (3 * (n : ℚ)) := by positivity
    linarith
  -- Consequently `1/d1 + 1/d2 + 1/d3 ≤ 11/12`, i.e. `8/(3n) ≥ 1/12`.
  have hsum_le : 1 / (d1 : ℚ) + 1 / (d2 : ℚ) + 1 / (d3 : ℚ) ≤ 11 / 12 := by
    have hb2 : 1 / (d2 : ℚ) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hd2
    have hb3 : 1 / (d3 : ℚ) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hd3
    have hb1 : 1 / (d1 : ℚ) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hd1
    rcases hsome with h | h | h
    · have : 1 / (d1 : ℚ) ≤ 1 / 4 := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast h
      linarith
    · have : 1 / (d2 : ℚ) ≤ 1 / 4 := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast h
      linarith
    · have : 1 / (d3 : ℚ) ≤ 1 / 4 := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast h
      linarith
  have hge : (1 : ℚ) / 12 ≤ 8 / (3 * (n : ℚ)) := by linarith
  -- So `n ≤ 32`, and `n ≡ 1 (mod 4)`, `3 ∣ n` then force `n = 9` or `n = 21`.
  have hn32 : n ≤ 32 := by
    have h3n : (0 : ℚ) < 3 * (n : ℚ) := by positivity
    rw [le_div_iff₀ h3n] at hge
    have : (n : ℚ) ≤ 32 := by linarith
    exact_mod_cast this
  have hn_cases : n = 9 ∨ n = 21 := by omega
  rcases hn_cases with h9 | h21
  · -- `n = 9`: the inequality gives `dᵢ ≤ 9`, leaving finitely many cases.
    subst h9
    have hin : 1 + d1 ^ 2 + d2 ^ 2 + d3 ^ 2 ≤ 108 := by
      have h := hineq
      norm_num at h
      exact h
    have h1le : d1 ≤ 9 := by
      have hd2sq : 9 ≤ d2 ^ 2 := by nlinarith [hd2]
      have hd3sq : 9 ≤ d3 ^ 2 := by nlinarith [hd3]
      have hd1sq : d1 ^ 2 ≤ 89 := by nlinarith
      nlinarith [hd1sq]
    have h2le : d2 ≤ 9 := by
      have hd1sq : 9 ≤ d1 ^ 2 := by nlinarith [hd1]
      have hd3sq : 9 ≤ d3 ^ 2 := by nlinarith [hd3]
      have hd2sq : d2 ^ 2 ≤ 89 := by nlinarith
      nlinarith [hd2sq]
    have h3le : d3 ≤ 9 := by
      have hd1sq : 9 ≤ d1 ^ 2 := by nlinarith [hd1]
      have hd2sq : 9 ≤ d2 ^ 2 := by nlinarith [hd2]
      have hd3sq : d3 ^ 2 ≤ 89 := by nlinarith
      nlinarith [hd3sq]
    interval_cases d1 <;> interval_cases d2 <;> interval_cases d3 <;> norm_num at heq
  · -- `n = 21`: the equation gives `1/dᵢ ≥ 13/63`, i.e. `dᵢ ≤ 4`, leaving 8 cases.
    subst h21
    have hb2 : 1 / (d2 : ℚ) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hd2
    have hb3 : 1 / (d3 : ℚ) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hd3
    have hb1 : 1 / (d1 : ℚ) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hd1
    have h1le : d1 ≤ 4 := by
      have key : (13 : ℚ) / 63 ≤ 1 / (d1 : ℚ) := by
        have h := heq
        norm_num at h
        linarith
      have hd1pos : (0 : ℚ) < (d1 : ℚ) := by positivity
      rw [le_div_iff₀ hd1pos] at key
      have hlt : (d1 : ℚ) < 5 := by linarith
      have : d1 < 5 := by exact_mod_cast hlt
      omega
    have h2le : d2 ≤ 4 := by
      have key : (13 : ℚ) / 63 ≤ 1 / (d2 : ℚ) := by
        have h := heq
        norm_num at h
        linarith
      have hd2pos : (0 : ℚ) < (d2 : ℚ) := by positivity
      rw [le_div_iff₀ hd2pos] at key
      have hlt : (d2 : ℚ) < 5 := by linarith
      have : d2 < 5 := by exact_mod_cast hlt
      omega
    have h3le : d3 ≤ 4 := by
      have key : (13 : ℚ) / 63 ≤ 1 / (d3 : ℚ) := by
        have h := heq
        norm_num at h
        linarith
      have hd3pos : (0 : ℚ) < (d3 : ℚ) := by positivity
      rw [le_div_iff₀ hd3pos] at key
      have hlt : (d3 : ℚ) < 5 := by linarith
      have : d3 < 5 := by exact_mod_cast hlt
      omega
    interval_cases d1 <;> interval_cases d2 <;> interval_cases d3 <;> norm_num at heq

end Work.BSW.Char
