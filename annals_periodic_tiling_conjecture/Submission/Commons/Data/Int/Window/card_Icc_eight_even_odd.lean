import Mathlib

namespace Commons.Data.Int.Window

open scoped BigOperators

/-- Cardinality of an explicit four-element integer finset with pairwise distinct
entries. -/
private lemma card_four (a b c d : ℤ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset ℤ).card = 4 := by
  have h1 : a ∉ ({b, c, d} : Finset ℤ) := by
    intro h; simp at h; omega
  have h2 : b ∉ ({c, d} : Finset ℤ) := by
    intro h; simp at h; omega
  have h3 : c ∉ ({d} : Finset ℤ) := by
    intro h; simp at h; omega
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem h3, Finset.card_singleton]

/-- Among eight consecutive integers `n, …, n+7` there are exactly four even and
exactly four odd integers. -/
theorem card_Icc_eight_even_odd (n : ℤ) :
    ((Finset.Icc n (n + 7)).filter (fun m : ℤ => Even m)).card = 4 ∧
      ((Finset.Icc n (n + 7)).filter (fun m : ℤ => Odd m)).card = 4 := by
  classical
  have hIcc : ∀ m : ℤ, m ∈ Finset.Icc n (n + 7) →
      m = n ∨ m = n + 1 ∨ m = n + 2 ∨ m = n + 3 ∨ m = n + 4 ∨
        m = n + 5 ∨ m = n + 6 ∨ m = n + 7 := by
    intro m hm
    have h1 : n ≤ m := (Finset.mem_Icc.mp hm).1
    have h2 : m ≤ n + 7 := (Finset.mem_Icc.mp hm).2
    omega
  by_cases hn : Even n
  · have hE : (Finset.Icc n (n + 7)).filter (fun m : ℤ => Even m) = {n, n + 2, n + 4, n + 6} := by
      ext m
      constructor
      · intro hm
        have hmem := (Finset.mem_filter.mp hm).1
        have hev : Even m := (Finset.mem_filter.mp hm).2
        rcases hIcc m hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simp
        · exfalso; grind
        · simp
        · exfalso; grind
        · simp
        · exfalso; grind
        · simp
        · exfalso; grind
      · intro hm
        have hdis : m = n ∨ m = n + 2 ∨ m = n + 4 ∨ m = n + 6 := by simpa using hm
        rcases hdis with rfl | rfl | rfl | rfl
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, hn⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
    have hO : (Finset.Icc n (n + 7)).filter (fun m : ℤ => Odd m) = {n + 1, n + 3, n + 5, n + 7} := by
      ext m
      constructor
      · intro hm
        have hmem := (Finset.mem_filter.mp hm).1
        have hod : Odd m := (Finset.mem_filter.mp hm).2
        rcases hIcc m hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exfalso; grind
        · simp
        · exfalso; grind
        · simp
        · exfalso; grind
        · simp
        · exfalso; grind
        · simp
      · intro hm
        have hdis : m = n + 1 ∨ m = n + 3 ∨ m = n + 5 ∨ m = n + 7 := by simpa using hm
        rcases hdis with rfl | rfl | rfl | rfl
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
    rw [hE, hO]
    constructor
    · exact card_four n (n + 2) (n + 4) (n + 6) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
    · exact card_four (n + 1) (n + 3) (n + 5) (n + 7) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
  · have hn' : Odd n := Int.not_even_iff_odd.mp hn
    have hE : (Finset.Icc n (n + 7)).filter (fun m : ℤ => Even m) = {n + 1, n + 3, n + 5, n + 7} := by
      ext m
      constructor
      · intro hm
        have hmem := (Finset.mem_filter.mp hm).1
        have hev : Even m := (Finset.mem_filter.mp hm).2
        rcases hIcc m hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exfalso; grind
        · simp
        · exfalso; grind
        · simp
        · exfalso; grind
        · simp
        · exfalso; grind
        · simp
      · intro hm
        have hdis : m = n + 1 ∨ m = n + 3 ∨ m = n + 5 ∨ m = n + 7 := by simpa using hm
        rcases hdis with rfl | rfl | rfl | rfl
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
    have hO : (Finset.Icc n (n + 7)).filter (fun m : ℤ => Odd m) = {n, n + 2, n + 4, n + 6} := by
      ext m
      constructor
      · intro hm
        have hmem := (Finset.mem_filter.mp hm).1
        have hod : Odd m := (Finset.mem_filter.mp hm).2
        rcases hIcc m hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simp
        · exfalso; grind
        · simp
        · exfalso; grind
        · simp
        · exfalso; grind
        · simp
        · exfalso; grind
      · intro hm
        have hdis : m = n ∨ m = n + 2 ∨ m = n + 4 ∨ m = n + 6 := by simpa using hm
        rcases hdis with rfl | rfl | rfl | rfl
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, hn'⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, by grind⟩
    rw [hE, hO]
    constructor
    · exact card_four (n + 1) (n + 3) (n + 5) (n + 7) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
    · exact card_four n (n + 2) (n + 4) (n + 6) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)

end Commons.Data.Int.Window
