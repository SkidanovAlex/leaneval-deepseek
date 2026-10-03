import Mathlib
import Submission.Work.ORLyndon.exists_rat_between

namespace Work.ORLyndon

/-- Splitting a sum over a finite type into the term at a distinguished point `k`
plus the sum over the complement subtype. -/
theorem sum_univ_eq_add_sum_ne {κ : Type*} [Fintype κ] [DecidableEq κ] (k : κ) (f : κ → ℚ) :
    ∑ j, f j = f k + ∑ j : {j : κ // j ≠ k}, f j.1 := by
  rw [← Finset.sum_subtype (Finset.univ.erase k) (by intro x; simp) f]
  conv_lhs => rw [show (Finset.univ : Finset κ) = insert k (Finset.univ.erase k) from by
        rw [Finset.insert_erase (Finset.mem_univ k)]]
  rw [Finset.sum_insert (Finset.notMem_erase k _)]

/-- Elementary algebra behind the strict separation of the two families of linear
inequalities in `fm_step`: from `b * c < a * d` with `0 < a` and `b < 0` the
normalised values `-c / a` and `-d / b` are strictly ordered. -/
theorem neg_div_lt_neg_div {a b c d : ℚ} (ha : 0 < a) (hb : b < 0) (h : b * c < a * d) :
    -c / a < -d / b := by
  have key : d / b < c / a := by
    rw [lt_div_iff₀ ha, div_mul_eq_mul_div, div_lt_iff_of_neg hb]
    linarith [h]
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact key

/-- **Farkas step for one-relator coherence.**

Given a finite family of rows `a i : κ → ℚ`, a distinguished index `k`, and rationals
`y` on the complement of `k`, suppose that
* every row `i` with `a i k = 0` is positive on `y` (`hP`), and
* every positive row `i` and negative row `i'` at `k` satisfy the strict inequality
  `a i' k * (a i · y) < a i k * (a i' · y)` (`hM`).

Then the rows can be made strictly positive simultaneously by adjusting only the `k`-th
coordinate: there is `x` with `∑ j, a i j * x j > 0` for every `i`. The proof keeps
`x j = y j` for `j ≠ k` and chooses `x k` strictly between
`max_{a i k > 0} (-(a i · y)/a i k)` (a lower bound) and
`min_{a i k < 0} (-(a i · y)/a i k)` (an upper bound); `hM` is exactly the statement that
every lower bound is strictly below every upper bound, so `exists_rat_between` supplies the
required rational. -/
theorem fm_step {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : Type*} [Fintype ι]
    (a : ι → κ → ℚ) (k : κ) (y : {j : κ // j ≠ k} → ℚ)
    (hP : ∀ i, a i k = 0 → 0 < ∑ j : {j : κ // j ≠ k}, a i j.1 * y j)
    (hM : ∀ i i', 0 < a i k → a i' k < 0 →
      (∑ j : {j : κ // j ≠ k}, (a i' k) * a i j.1 * y j) <
        (∑ j : {j : κ // j ≠ k}, (a i k) * a i' j.1 * y j)) :
    ∃ x : κ → ℚ, ∀ i, 0 < ∑ j, a i j * x j := by
  classical
  -- Value of row `i` against `y` on the complement of `k`.
  set b : ι → ℚ := fun i => ∑ j : {j : κ // j ≠ k}, a i j.1 * y j with hb
  -- Pull the constant `c` out of the sum appearing in `hM`.
  have hLb : ∀ (i : ι) (c : ℚ),
      (∑ j : {j : κ // j ≠ k}, c * a i j.1 * y j) = c * b i := by
    intro i c
    rw [hb]
    show (∑ j : {j : κ // j ≠ k}, c * a i j.1 * y j) =
      c * ∑ j : {j : κ // j ≠ k}, a i j.1 * y j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- `hM` rewritten in terms of `b`.
  have hMb : ∀ i i', 0 < a i k → a i' k < 0 → a i' k * b i < a i k * b i' := by
    intro i i' hi hi'
    have h := hM i i' hi hi'
    rw [hLb i (a i' k), hLb i' (a i k)] at h
    exact h
  -- Strict separation of the lower bounds from the upper bounds.
  have hsep : ∀ i i', 0 < a i k → a i' k < 0 → -b i / a i k < -b i' / a i' k :=
    fun i i' hi hi' => neg_div_lt_neg_div hi hi' (hMb i i' hi hi')
  -- The lower bounds (from rows positive at `k`) as a finset of rationals.
  set P : Finset ℚ :=
    (Finset.univ.filter (fun i => 0 < a i k)).image (fun i => -b i / a i k) with hPdef
  -- The upper bounds (from rows negative at `k`) as a finset of rationals.
  set N : Finset ℚ :=
    (Finset.univ.filter (fun i => a i k < 0)).image (fun i => -b i / a i k) with hNdef
  have hPN : ∀ p ∈ P, ∀ q ∈ N, p < q := by
    intro p hp q hq
    rw [hPdef] at hp
    rw [hNdef] at hq
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨i', hi', rfl⟩
    exact hsep i i' (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hi').2
  -- A rational lying strictly above all of `P` and strictly below all of `N`.
  obtain ⟨xk, hxkP, hxkN⟩ := exists_rat_between P N hPN
  -- The extension of `y` to `κ` with the `k`-th coordinate replaced by `xk`.
  let x : κ → ℚ := fun j => if h : j = k then xk else y ⟨j, h⟩
  have hxk : x k = xk := by simp [x]
  have hxj : ∀ j : {j : κ // j ≠ k}, x j.1 = y j := by
    intro j
    have hne : ¬ (j.1 = k) := j.2
    simp only [x]
    rw [dif_neg hne]
  refine ⟨x, ?_⟩
  intro i
  -- Split the total sum over `κ` into the `k`-term and the sum over the complement,
  -- where `x` agrees with `y`.
  rw [sum_univ_eq_add_sum_ne k (fun j => a i j * x j), hxk]
  have hsum : (∑ j : {j : κ // j ≠ k}, a i j.1 * x j.1) = b i := by
    rw [hb]
    show (∑ j : {j : κ // j ≠ k}, a i j.1 * x j.1) = ∑ j, a i j.1 * y j
    apply Finset.sum_congr rfl
    intro j _
    rw [hxj j]
  rw [hsum]
  -- It remains to show `0 < a i k * xk + b i`.
  rcases lt_trichotomy (a i k) 0 with hlt | heq | hgt
  · -- `a i k < 0`: `xk` is below the upper bound `-b i / a i k`.
    have hmem : -b i / a i k ∈ N := by
      rw [hNdef]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩, rfl⟩
    have hlt' : xk < -b i / a i k := hxkN _ hmem
    have hne : a i k ≠ 0 := ne_of_lt hlt
    have hval : a i k * (-b i / a i k) = -b i := by field_simp
    have h2 : a i k * (-b i / a i k) < a i k * xk := mul_lt_mul_of_neg_left hlt' hlt
    rw [hval] at h2
    linarith
  · -- `a i k = 0`: the positivity is exactly `hP`.
    rw [heq, zero_mul, zero_add]
    exact hP i heq
  · -- `0 < a i k`: `xk` is above the lower bound `-b i / a i k`.
    have hmem : -b i / a i k ∈ P := by
      rw [hPdef]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hgt⟩, rfl⟩
    have hlt' : -b i / a i k < xk := hxkP _ hmem
    have hne : a i k ≠ 0 := ne_of_gt hgt
    have hval : a i k * (-b i / a i k) = -b i := by field_simp
    have h2 : a i k * (-b i / a i k) < a i k * xk := mul_lt_mul_of_pos_left hlt' hgt
    rw [hval] at h2
    linarith

end Work.ORLyndon
