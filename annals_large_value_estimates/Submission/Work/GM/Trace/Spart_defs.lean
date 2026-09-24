import Submission.Work.GM.Trace.Defs

/-!
# Auxiliary objects for the `S₁` bound (GM Proposition 5.1)

This file collects the small combinatorial API around

* `rho m` -- the unique non-zero coordinate of `m : ℤ × ℤ × ℤ` when `nzCount m = 1`
  (and the third coordinate otherwise),

together with the injectivity statements that let sums over `Finset`s of such `m`
be reindexed by the non-zero coordinate.  `Work.GM.Trace.Spart_one_bound` (GM Prop 5.1)
and the lemmas it is assembled from all use this vocabulary.
-/

namespace Work.GM.Trace

open Submission.GM

/-- The unique non-zero coordinate of `m` when `nzCount m = 1` (for other `m` it is the
third coordinate). -/
def rho (m : ℤ × ℤ × ℤ) : ℤ := if m.1 ≠ 0 then m.1 else if m.2.1 ≠ 0 then m.2.1 else m.2.2

theorem rho_of_ne_zero {m : ℤ × ℤ × ℤ} (h : m.1 ≠ 0) : rho m = m.1 := by simp [rho, h]

theorem rho_of_fst_eq_zero {m : ℤ × ℤ × ℤ} (h : m.1 = 0) (h' : m.2.1 ≠ 0) :
    rho m = m.2.1 := by simp [rho, h, h']

theorem rho_of_fst_snd_eq_zero {m : ℤ × ℤ × ℤ} (h : m.1 = 0) (h' : m.2.1 = 0) :
    rho m = m.2.2 := by simp [rho, h, h']

/-- Structure of the `m : ℤ³` with `nzCount m = 1`: exactly one coordinate is non-zero. -/
theorem nzCount_one_cases (m : ℤ × ℤ × ℤ) (h : nzCount m = 1) :
    (m.1 ≠ 0 ∧ m.2.1 = 0 ∧ m.2.2 = 0) ∨
      (m.1 = 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 = 0) ∨
      (m.1 = 0 ∧ m.2.1 = 0 ∧ m.2.2 ≠ 0) := by
  unfold nzCount at h
  by_cases h1 : m.1 = 0 <;> by_cases h2 : m.2.1 = 0 <;> by_cases h3 : m.2.2 = 0 <;>
    simp_all <;> omega

theorem nzCount_one_of_fst_ne_zero {m : ℤ × ℤ × ℤ} (hm : nzCount m = 1) (h : m.1 ≠ 0) :
    m.2.1 = 0 ∧ m.2.2 = 0 := by
  rcases nzCount_one_cases m hm with ⟨_, h2, h3⟩ | ⟨h1, _, _⟩ | ⟨h1, _, _⟩
  · exact ⟨h2, h3⟩
  · exfalso; exact h h1
  · exfalso; exact h h1

theorem nzCount_one_of_snd_ne_zero {m : ℤ × ℤ × ℤ} (hm : nzCount m = 1) (h : m.1 = 0)
    (h2 : m.2.1 ≠ 0) : m.2.2 = 0 := by
  rcases nzCount_one_cases m hm with ⟨h1, _, _⟩ | ⟨_, _, h3⟩ | ⟨_, h2', _⟩
  · exfalso; exact h1 h
  · exact h3
  · exfalso; exact h2 h2'

theorem nzCount_one_ne_zero (m : ℤ × ℤ × ℤ) (h : nzCount m = 1) :
    m.1 ≠ 0 ∨ m.2.1 ≠ 0 ∨ m.2.2 ≠ 0 := by
  rcases nzCount_one_cases m h with ⟨h1, _, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, h3⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-- `rho` is non-zero on the `nzCount = 1` locus. -/
theorem rho_ne_zero (m : ℤ × ℤ × ℤ) (h : nzCount m = 1) : rho m ≠ 0 := by
  rcases nzCount_one_cases m h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [rho_of_ne_zero h1]; exact h1
  · rw [rho_of_fst_eq_zero h1 h2]; exact h2
  · rw [rho_of_fst_snd_eq_zero h1 h2]; exact h3

theorem one_le_abs_rho (m : ℤ × ℤ × ℤ) (h : nzCount m = 1) : 1 ≤ |rho m| := by
  rcases lt_or_gt_of_ne (rho_ne_zero m h) with hlt | hgt
  · rw [abs_of_neg hlt]; omega
  · rw [abs_of_pos hgt]; omega

/-- On the `nzCount = 1` locus, `m` is determined by its first coordinate when that is
non-zero. -/
theorem eq_of_nzCount_one_of_fst_eq {m m' : ℤ × ℤ × ℤ} (hm : nzCount m = 1)
    (hm' : nzCount m' = 1) (h : m.1 = m'.1) (hne : m.1 ≠ 0) : m = m' := by
  have h1 := nzCount_one_of_fst_ne_zero hm hne
  have h1' := nzCount_one_of_fst_ne_zero hm' (by rwa [← h])
  have h2 : m.2.1 = m'.2.1 := by rw [h1.1, h1'.1]
  have h3 : m.2.2 = m'.2.2 := by rw [h1.2, h1'.2]
  exact Prod.ext h (Prod.ext h2 h3)

/-- On the `nzCount = 1` locus, `m` is determined by its second coordinate when the first
coordinate is zero and the second non-zero. -/
theorem eq_of_nzCount_one_of_snd_eq {m m' : ℤ × ℤ × ℤ} (hm : nzCount m = 1)
    (hm' : nzCount m' = 1) (h0 : m.1 = 0) (h : m.2.1 = m'.2.1) (hne : m.2.1 ≠ 0) :
    m = m' := by
  have h0' : m'.1 = 0 := by
    rcases nzCount_one_cases m' hm' with ⟨g1, g2, g3⟩ | ⟨g1, _, _⟩ | ⟨g1, g2, g3⟩
    · exfalso; exact hne (h.trans g2)
    · exact g1
    · exfalso; exact hne (h.trans g2)
  have h1 := nzCount_one_of_snd_ne_zero hm h0 hne
  have h1' := nzCount_one_of_snd_ne_zero hm' h0' (by rwa [← h])
  have h3 : m.2.2 = m'.2.2 := by rw [h1, h1']
  exact Prod.ext (by rw [h0, h0']) (Prod.ext h h3)

/-- On the `nzCount = 1` locus, `m` is determined by its third coordinate when the first two
coordinates are zero. -/
theorem eq_of_nzCount_one_of_thd_eq {m m' : ℤ × ℤ × ℤ} (hm : nzCount m = 1)
    (hm' : nzCount m' = 1) (h0 : m.1 = 0) (h0' : m.2.1 = 0) (h : m.2.2 = m'.2.2) :
    m = m' := by
  have g0 : m.2.2 ≠ 0 := by
    rcases nzCount_one_cases m hm with ⟨g, _, _⟩ | ⟨_, g, _⟩ | ⟨_, _, g⟩
    · exfalso; exact g h0
    · exfalso; exact g h0'
    · exact g
  rcases nzCount_one_cases m' hm' with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
  · exfalso; exact g0 (h.trans g3)
  · exfalso; exact g0 (h.trans g3)
  · exact Prod.ext (by rw [h0, g1]) (Prod.ext (by rw [h0', g2]) h)

/-- A useful form: for `nzCount m = 1` the invariant `rho m` is one of the three coordinates. -/
theorem rho_eq_fst_or_snd_or_thd (m : ℤ × ℤ × ℤ) (h : nzCount m = 1) :
    rho m = m.1 ∨ rho m = m.2.1 ∨ rho m = m.2.2 := by
  rcases nzCount_one_cases m h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl (rho_of_ne_zero h1)
  · exact Or.inr (Or.inl (rho_of_fst_eq_zero h1 h2))
  · exact Or.inr (Or.inr (rho_of_fst_snd_eq_zero h1 h2))

/-- The index of the (unique) non-zero coordinate of `m`, for `nzCount m = 1`. -/
def fam (m : ℤ × ℤ × ℤ) : Fin 3 := if m.1 ≠ 0 then 0 else if m.2.1 ≠ 0 then 1 else 2

theorem fam_eq_zero {m : ℤ × ℤ × ℤ} (h : m.1 ≠ 0) : fam m = 0 := by simp [fam, h]

theorem fam_eq_one {m : ℤ × ℤ × ℤ} (h : m.1 = 0) (h' : m.2.1 ≠ 0) : fam m = 1 := by
  simp [fam, h, h']

theorem fam_eq_two {m : ℤ × ℤ × ℤ} (h : m.1 = 0) (h' : m.2.1 = 0) : fam m = 2 := by
  simp [fam, h, h']

end Work.GM.Trace
