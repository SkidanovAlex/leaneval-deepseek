import Mathlib
import Submission.Work.Holonomy3.comp_defs

/-!
# The degree-lex minimal exponent of a nonzero coefficient family

Given a family `c : (Fin d →₀ ℕ) → ℂ` of coefficients with `c` not identically zero, the paper's
vanishing-filtration argument needs a *distinguished* exponent `n` of the support:

* `n` has minimal **total degree** among the exponents of the support, and
* among the exponents of that degree, `n` is the **lexicographically minimal** one, where the
  lexicographic order on `Fin d →₀ ℕ` is the order in which the *first* coordinate is the most
  significant (so the disjunction in the statement is `n <lex m` spelled out: either `m = n`, or
  `m` and `n` agree below some index `j` and `n j < m j`).

This is `Work.Holonomy3.exists_lexmin_minimal`.  The proof is a single well-founded-recursion step
for the order `≺` on exponents given by comparing the total degree first and then the lexicographic
order: `degLexKey s = toLex (s.degree, toLex s)`, an element of `Lex (ℕ × Lex (Fin d →₀ ℕ))`.
That order is well-founded (`Prod.Lex.instWellFoundedLTLex` together with
`Finsupp.Lex.wellFoundedLT` for the finite index type `Fin d`), so the set of keys of the support
has a minimal element `k`; any `n` of the support with `degLexKey n = k` is the required exponent.
-/

namespace Work.Holonomy3

noncomputable section

/-- The **degree-lex key** of an exponent `s`: the total degree first, then the exponent itself in
the lexicographic order (first coordinate most significant).  This is the order `≺` of the paper's
vanishing filtration. -/
def degLexKey {d : ℕ} (s : Fin d →₀ ℕ) : Lex (ℕ × Lex (Fin d →₀ ℕ)) := toLex (s.degree, toLex s)

/-- Unfolding of the comparison of the degree-lex keys. -/
theorem degLexKey_lt_iff {d : ℕ} (s t : Fin d →₀ ℕ) :
    degLexKey s < degLexKey t ↔ s.degree < t.degree ∨ (s.degree = t.degree ∧ toLex s < toLex t) :=
  Prod.Lex.toLex_lt_toLex

/-- Unfolding of the non-strict comparison of the degree-lex keys. -/
theorem degLexKey_le_iff {d : ℕ} (s t : Fin d →₀ ℕ) :
    degLexKey s ≤ degLexKey t ↔ s.degree < t.degree ∨ (s.degree = t.degree ∧ toLex s ≤ toLex t) :=
  Prod.Lex.toLex_le_toLex

/-- The lexicographic comparison `toLex n ≤ toLex m` written out as the disjunction of the
statement: either `m = n`, or the two exponents agree below some index `j` and `n j < m j`
(so `n` precedes `m` lexicographically). -/
theorem toLex_le_iff_lex {d : ℕ} {m n : Fin d →₀ ℕ} :
    toLex n ≤ toLex m ↔
      m = n ∨ ∃ j : Fin d, (∀ i : Fin d, i < j → m i = n i) ∧ n j < m j := by
  rw [le_iff_lt_or_eq, Finsupp.Lex.lt_iff]
  simp only [ofLex_toLex]
  constructor
  · rintro (⟨j, hj, hlt⟩ | h)
    · exact Or.inr ⟨j, fun i hi => (hj i hi).symm, hlt⟩
    · exact Or.inl (by have h' := congrArg ofLex h; simpa using h'.symm)
  · rintro (rfl | ⟨j, hj, hlt⟩)
    · exact Or.inr rfl
    · exact Or.inl ⟨j, fun i hi => (hj i hi).symm, hlt⟩

/-- **Existence of the degree-lex minimal exponent of a nonzero coefficient family.**  If
`c : (Fin d →₀ ℕ) → ℂ` is not identically zero, there is an exponent `n` with `c n ≠ 0` of minimal
total degree, and which is lexicographically minimal among the exponents of that degree. -/
theorem exists_lexmin_minimal {d : ℕ} (c : (Fin d →₀ ℕ) → ℂ) (hc : ∃ n, c n ≠ 0) :
    ∃ n : Fin d →₀ ℕ, c n ≠ 0 ∧ (∀ m : Fin d →₀ ℕ, m.degree < n.degree → c m = 0) ∧
      ∀ m : Fin d →₀ ℕ, m.degree = n.degree → c m ≠ 0 →
        m = n ∨ ∃ j : Fin d, (∀ i : Fin d, i < j → m i = n i) ∧ n j < m j := by
  classical
  obtain ⟨n₀, hn₀⟩ := hc
  -- a minimal key among the exponents of the support
  obtain ⟨k, ⟨n, hcn, hnk⟩, hmin⟩ :=
    WellFounded.has_min (r := fun a b : Lex (ℕ × Lex (Fin d →₀ ℕ)) => a < b) wellFounded_lt
      {q | ∃ m : Fin d →₀ ℕ, c m ≠ 0 ∧ degLexKey m = q} ⟨degLexKey n₀, n₀, hn₀, rfl⟩
  -- `n` is degree-lex minimal among the exponents of the support
  have hmin' : ∀ m : Fin d →₀ ℕ, c m ≠ 0 → degLexKey n ≤ degLexKey m := by
    intro m hm
    have h1 : ¬ degLexKey m < k := hmin _ ⟨m, hm, rfl⟩
    rw [← hnk] at h1
    exact le_of_not_gt h1
  refine ⟨n, hcn, ?_, ?_⟩
  · -- there is no exponent of smaller degree in the support
    intro m hmdeg
    by_contra hne
    have h1 := hmin' m hne
    rw [degLexKey_le_iff] at h1
    rcases h1 with h | ⟨h, _⟩ <;> omega
  · -- among the exponents of that degree, `n` is lexicographically minimal
    intro m hmdeg hne
    have h1 := hmin' m hne
    rw [degLexKey_le_iff] at h1
    rcases h1 with h | ⟨_, h⟩
    · omega
    · exact toLex_le_iff_lex.mp h

end

end Work.Holonomy3
