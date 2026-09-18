import Submission.DS.Case1

open scoped Nat ENNReal NNReal
open Set MeasureTheory
open DuffinSchaefferConjecture

/-!
# Truncation invariance of 𝒦 (paper §2, Case 2 opening step)

Replacing `ψ` by `min ψ (1/2)` does not change the set `𝒦 ψ`: if `ψ(q) ≥ 1/2` infinitely
often then both `𝒦`s are `[0,1]` (Case 1), and otherwise the two functions agree on a
cofinite set, which cannot change which points lie in infinitely many solution sets.
-/

namespace Submission.DS

/-- Two sets of a type that agree on a cofinite set are simultaneously infinite. -/
lemma infinite_iff_of_eventually_mem_iff {α : Type*} {A B : Set α}
    (h : ∀ᶠ x in Filter.cofinite, x ∈ A ↔ x ∈ B) : A.Infinite ↔ B.Infinite := by
  classical
  let S : Set α := {x | ¬ (x ∈ A ↔ x ∈ B)}
  have hSfin : S.Finite := by
    simpa [S] using (Filter.eventually_cofinite.mp h)
  have hmem : ∀ x, x ∉ S → (x ∈ A ↔ x ∈ B) := by
    intro x hx
    by_contra hc
    exact hx (by simpa [S] using hc)
  constructor
  · intro hA hBfin
    have hsub : A ⊆ B ∪ S := by
      intro x hx
      by_cases hxS : x ∈ S
      · exact Or.inr hxS
      · exact Or.inl ((hmem x hxS).1 hx)
    have hfin : (B ∪ S).Finite := hBfin.union hSfin
    exact hA (hfin.subset hsub)
  · intro hB hAfin
    have hsub : B ⊆ A ∪ S := by
      intro x hx
      by_cases hxS : x ∈ S
      · exact Or.inr hxS
      · exact Or.inl ((hmem x hxS).2 hx)
    have hfin : (A ∪ S).Finite := hAfin.union hSfin
    exact hB (hfin.subset hsub)

/-- The per-denominator solution set depends only on the value of `ψ` at `q`. -/
lemma Bq_eq_of_apply_eq {ψ χ : ℕ+ → ℝ≥0} (q : ℕ+) (h : ψ q = χ q) : Bq ψ q = Bq χ q := by
  ext x
  unfold Bq
  constructor <;> intro hx
  · rcases hx with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [Kfib, inequality_1_7, h] using ha
  · rcases hx with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [Kfib, inequality_1_7, h] using ha

/-- If `ψ` and `χ` agree on all but finitely many denominators, then `𝒦 ψ = 𝒦 χ`. -/
lemma K_eq_of_cofinite_eq {ψ χ : ℕ+ → ℝ≥0} (h : ∀ᶠ q in Filter.cofinite, ψ q = χ q) :
    𝒦 ψ = 𝒦 χ := by
  classical
  let S : Set ℕ+ := {q | ¬ ψ q = χ q}
  have hSfin : S.Finite := by
    simpa [S] using (Filter.eventually_cofinite.mp h)
  have hagree : ∀ q, q ∉ S → ψ q = χ q := by
    intro q hq
    by_contra hc
    exact hq (by simpa [S] using hc)
  ext x
  rw [mem_K_iff, mem_K_iff]
  have hLim : x ∈ limsupDenoms (Bq ψ) ↔ x ∈ limsupDenoms (Bq χ) := by
    unfold limsupDenoms
    change {q : ℕ+ | x ∈ Bq ψ q}.Infinite ↔ {q : ℕ+ | x ∈ Bq χ q}.Infinite
    apply infinite_iff_of_eventually_mem_iff
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset hSfin
    intro q hq
    by_contra hqS
    exact hq (by
      have hB : x ∈ Bq ψ q ↔ x ∈ Bq χ q := by rw [Bq_eq_of_apply_eq q (hagree q hqS)]
      simpa using hB)
  constructor
  · intro hx
    rcases hx with ⟨hx01, hxlim⟩
    exact ⟨hx01, hLim.mp hxlim⟩
  · intro hx
    rcases hx with ⟨hx01, hxlim⟩
    exact ⟨hx01, hLim.mpr hxlim⟩

/-- Replacing `ψ` by `min ψ (1/2)` leaves `𝒦 ψ` unchanged (paper §2, Case 2). -/
lemma K_eq_K_min_half (ψ : ℕ+ → ℝ≥0) :
    𝒦 ψ = 𝒦 (fun q : ℕ+ => min (ψ q) (1 / 2 : ℝ≥0)) := by
  classical
  by_cases hBig : {q : ℕ+ | (1 / 2 : ℝ≥0) ≤ ψ q}.Infinite
  · rw [K_eq_Icc_of_half_infinite ψ hBig]
    rw [K_eq_Icc_of_half_infinite (fun q : ℕ+ => min (ψ q) (1 / 2 : ℝ≥0))]
    apply Set.Infinite.mono
    · intro q hq
      change (1 / 2 : ℝ≥0) ≤ min (ψ q) (1 / 2 : ℝ≥0)
      have hψq : (1 / 2 : ℝ≥0) ≤ ψ q := hq
      rw [min_eq_right hψq]
    · exact hBig
  · apply K_eq_of_cofinite_eq
    rw [Filter.eventually_cofinite]
    have hBfin : ({q : ℕ+ | (1 / 2 : ℝ≥0) ≤ ψ q}).Finite := not_not.mp hBig
    apply Set.Finite.subset hBfin
    intro q hq
    change (1 / 2 : ℝ≥0) ≤ ψ q
    by_contra hnot
    have hlt : ψ q < (1 / 2 : ℝ≥0) := lt_of_not_ge hnot
    exact hq (Eq.symm (min_eq_left (le_of_lt hlt)))


/-- `min ψ (1/2)`: the truncation of `ψ` at level `1/2`. -/
noncomputable def psiHalf (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : ℝ≥0 := min (ψ q) (1 / 2 : ℝ≥0)

lemma psiHalf_le_half (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : psiHalf ψ q ≤ (1 / 2 : ℝ≥0) := by
  exact min_le_right _ _

lemma psiHalf_le_self (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : psiHalf ψ q ≤ ψ q := by
  exact min_le_left _ _

lemma psiHalf_of_le_half {ψ : ℕ+ → ℝ≥0} {q : ℕ+} (h : ψ q ≤ (1 / 2 : ℝ≥0)) :
    psiHalf ψ q = ψ q := by
  exact min_eq_left h

/-- The set of `q` at which `ψ(q) ≥ 1/2`. -/
def bigQ (ψ : ℕ+ → ℝ≥0) : Set ℕ+ := {q : ℕ+ | (1 / 2 : ℝ≥0) ≤ ψ q}

/-- `K_eq_K_min_half` in terms of `psiHalf`. -/
lemma K_eq_K_psiHalf (ψ : ℕ+ → ℝ≥0) : 𝒦 ψ = 𝒦 (psiHalf ψ) := by
  unfold psiHalf
  exact K_eq_K_min_half ψ

end Submission.DS
