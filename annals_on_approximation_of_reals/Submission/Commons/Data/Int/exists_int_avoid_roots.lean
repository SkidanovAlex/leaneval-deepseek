import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval

open Polynomial
open scoped BigOperators

namespace Commons.Data.Int

noncomputable section

/-- An integer lies in the window `[-L, L]` iff its real cast has absolute value at most `L`. -/
private lemma mem_int_window_iff_abs (L : ℕ) (z : ℤ) :
    z ∈ Finset.Icc (-(L : ℤ)) (L : ℤ) ↔ |(z : ℝ)| ≤ (L : ℝ) := by
  simp only [Finset.mem_Icc]
  constructor
  · intro hz
    rw [abs_le]
    constructor
    · exact_mod_cast hz.1
    · exact_mod_cast hz.2
  · intro habs
    rw [abs_le] at habs
    constructor
    · exact_mod_cast habs.1
    · exact_mod_cast habs.2

/-- The window `[-L, L]` contains exactly `2*L+1` integers. -/
private lemma card_int_window (L : ℕ) : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
  rw [Int.card_Icc]
  rw [show (((L : ℤ) + 1) - (-(L : ℤ))) = ((2 * L + 1 : ℕ) : ℤ) by omega]
  exact Int.toNat_natCast (2 * L + 1)

/-- If a finite family of nonzero real polynomials has total natDegree sum less than
the number of integers in the window `[-L, L]`, then some integer in that window
avoids being a real root of every polynomial. -/
theorem exists_int_avoid_roots {m : ℕ} (ps : Fin m → ℝ[X]) (hps : ∀ i, ps i ≠ 0)
    (L : ℕ) (hcard : (∑ i : Fin m, (ps i).natDegree) < 2 * L + 1) :
    ∃ z : ℤ, |(z : ℝ)| ≤ (L : ℝ) ∧ ∀ i : Fin m, (ps i).eval (z : ℝ) ≠ 0 := by
  classical
  by_cases hm : m = 0
  · subst m
    refine ⟨0, by norm_num, ?_⟩
    intro i
    exact Fin.elim0 i
  let W : Finset ℤ := Finset.Icc (-(L : ℤ)) (L : ℤ)
  let Wr : Finset ℝ := W.image (fun z : ℤ => (z : ℝ))
  -- the window points (as reals) that are roots of the polynomial `ps i`
  let R (i : Fin m) : Finset ℝ := Wr.filter (fun x : ℝ => (ps i).IsRoot x)
  have hR_card (i : Fin m) : (R i).card ≤ (ps i).natDegree := by
    refine Polynomial.card_le_degree_of_subset_roots ?_
    intro x hx
    rw [Polynomial.mem_roots']
    have hxmem : x ∈ Wr ∧ (ps i).IsRoot x := by simpa [R] using hx
    exact ⟨hps i, hxmem.2⟩
  have hsum_le : (∑ i : Fin m, (R i).card) ≤ ∑ i : Fin m, (ps i).natDegree := by
    exact Finset.sum_le_sum (fun i _ => hR_card i)
  by_contra h
  -- If every window point is a root of some `ps i`, we reach a counting contradiction.
  have hwin : ∀ z : ℤ, |(z : ℝ)| ≤ (L : ℝ) → ∃ i : Fin m, (ps i).IsRoot (z : ℝ) := by
    intro z hz
    by_contra hn
    apply h
    refine ⟨z, hz, ?_⟩
    intro i hzi
    exact hn ⟨i, by simpa [Polynomial.IsRoot] using hzi⟩
  let U : Finset ℝ := Finset.univ.biUnion R
  have hWr_subset_U : Wr ⊆ U := by
    intro x hx
    rw [Finset.mem_biUnion]
    rcases (Finset.mem_image.mp hx) with ⟨z, hzW, rfl⟩
    have habs : |(z : ℝ)| ≤ (L : ℝ) := (mem_int_window_iff_abs L z).1 hzW
    rcases hwin z habs with ⟨i, hi⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    dsimp [R]
    exact Finset.mem_filter.mpr ⟨hx, hi⟩
  have hU_le : U.card ≤ ∑ i : Fin m, (R i).card := by
    simpa using (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin m))) (t := R))
  have hWr_le : Wr.card ≤ U.card := Finset.card_le_card hWr_subset_U
  have hcardWr : Wr.card = 2 * L + 1 := by
    dsimp [Wr, W]
    rw [Finset.card_image_of_injective]
    · exact card_int_window L
    · exact Int.cast_injective
  have hlt : Wr.card < Wr.card := by
    calc
      Wr.card ≤ U.card := hWr_le
      _ ≤ ∑ i : Fin m, (R i).card := hU_le
      _ ≤ ∑ i : Fin m, (ps i).natDegree := hsum_le
      _ < 2 * L + 1 := hcard
      _ = Wr.card := hcardWr.symm
  omega

end

end Commons.Data.Int