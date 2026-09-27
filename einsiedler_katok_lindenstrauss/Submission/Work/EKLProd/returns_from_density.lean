import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# Density of returns implies simultaneous returns

`Work.EKLProd.returns_from_density`: if two points `x`, `z` both visit the complement of `K`
with density at most `1/3` along the forward orbit of `a`, then the two orbits meet `K`
simultaneously at arbitrarily large times.

The proof is elementary: the number of indices `j < n` with `a^j • x ∉ K` is exactly the sum of
the indicator of `Kᶜ` evaluated at `a^j • x`, so the hypothesis bounds it by `n/3`.  For a block
of indices `[N, M)` with `M = 3N + 1`, at most `M/3` of the indices of the block can miss `K` for
`x`, and at most `M/3` for `z`; if no index of the block hit `K` for both points, the block would
be covered by the two `Kᶜ`-index sets and hence have at most `2M/3 < M - N` elements, which is
false.  Hence a simultaneous hit exists in the block.
-/

open Classical

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-- The sum of the indicator of `Kᶜ` along the orbit of `y` counts the times the orbit is
outside `K`. -/
theorem sum_indicator_orbit_eq_card_filter {a : SL3} {K : Set X3} (y : X3) (n : ℕ) :
    (∑ j ∈ Finset.range n, (Kᶜ.indicator (fun _ => (1 : ℝ))) (a^j • y))
      = ((((Finset.range n).filter (fun j => a^j • y ∉ K)).card : ℕ) : ℝ) := by
  rw [← Finset.sum_boole (fun j => a^j • y ∉ K) (Finset.range n)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Set.indicator_apply]
  by_cases h : a^j • y ∈ K <;> simp [h, Set.mem_compl_iff]

/-- Complements of the two `Kᶜ`-index sets cover a block of indices only if the block is short:
for `M = 3N + 1` this forces a simultaneous return to `K` inside `[N, M)`. -/
theorem returns_from_density {a : Work.EKLContract.SL3} {K : Set Work.EKLContract.X3}
    {x z : Work.EKLContract.X3}
    (hx : ∀ n : ℕ, 0 < n → (∑ j ∈ Finset.range n, (Kᶜ.indicator (fun _ => (1 : ℝ))) (a^j • x)) ≤ (1/3) * n)
    (hz : ∀ n : ℕ, 0 < n → (∑ j ∈ Finset.range n, (Kᶜ.indicator (fun _ => (1 : ℝ))) (a^j • z)) ≤ (1/3) * n) :
    ∀ N : ℕ, ∃ n ≥ N, a^n • x ∈ K ∧ a^n • z ∈ K := by
  intro N
  set M : ℕ := 3 * N + 1 with hM
  have hxp : 0 < M := by omega
  -- cardinality bound for `x`
  have hxcard : ((Finset.range M).filter (fun j => a^j • x ∉ K)).card * 3 ≤ M := by
    have h := hx M hxp
    rw [sum_indicator_orbit_eq_card_filter x M] at h
    have h' : ((((Finset.range M).filter (fun j => a^j • x ∉ K)).card * 3 : ℕ) : ℝ) ≤ (M : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast h'
  -- cardinality bound for `z`
  have hzcard : ((Finset.range M).filter (fun j => a^j • z ∉ K)).card * 3 ≤ M := by
    have h := hz M hxp
    rw [sum_indicator_orbit_eq_card_filter z M] at h
    have h' : ((((Finset.range M).filter (fun j => a^j • z ∉ K)).card * 3 : ℕ) : ℝ) ≤ (M : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast h'
  by_contra hcon
  have hcon' : ∀ n : ℕ, N ≤ n → ¬ (a^n • x ∈ K ∧ a^n • z ∈ K) :=
    fun n hn h => hcon ⟨n, hn, h⟩
  -- if no index of `[N, M)` is a simultaneous return, that block is covered by the two
  -- `Kᶜ`-index sets of `x` and `z`
  have hsub : Finset.Ico N M ⊆ (Finset.range M).filter (fun j => a^j • x ∉ K) ∪
      (Finset.range M).filter (fun j => a^j • z ∉ K) := by
    intro j hj
    obtain ⟨hjN, hjM⟩ := Finset.mem_Ico.mp hj
    have hjrange : j ∈ Finset.range M := Finset.mem_range.mpr hjM
    have hnot := hcon' j hjN
    by_cases hxK : a^j • x ∈ K
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hjrange, fun hzK => hnot ⟨hxK, hzK⟩⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hjrange, hxK⟩))
  have hcard : (Finset.Ico N M).card ≤
      ((Finset.range M).filter (fun j => a^j • x ∉ K)).card +
      ((Finset.range M).filter (fun j => a^j • z ∉ K)).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have h1 : (Finset.Ico N M).card = M - N := by simp
  -- `M = 3N+1` makes the three inequalities incompatible
  omega

end Work.EKLProd
