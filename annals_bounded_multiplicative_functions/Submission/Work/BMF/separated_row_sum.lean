import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bounded row sums for `1`-separated families of points on the line

We prove that for any finite family of points of `ℝ` that is pairwise separated by at
least `1`, the row sums `∑_j 1 / (1 + (t i - t j)^2)` are bounded by an absolute
constant.  This is elementary input for localisation and mean-value arguments.

Strategy: for a fixed `i`, group the terms with `t j > t i` and those with `t j < t i` by
the integer part of the offset `|t j - t i|`.  Two points of a `1`-separated set cannot have
offsets whose floors lie in the same unit interval, so the grouping makes the sum a sum over
*distinct* positive integers, and the elementary bound `∑ 1/n² ≤ 2` finishes the job.
-/

namespace Work.BMF

/-- `∑_{n ∈ A} 1/n² ≤ 2` for any finite set `A` of positive natural numbers. -/
lemma sum_inv_sq_le_two (A : Finset ℕ) (hA : ∀ n ∈ A, 1 ≤ n) :
    (∑ n ∈ A, 1 / ((n : ℝ) ^ 2)) ≤ 2 := by
  have hsub : A ⊆ Finset.Icc 1 (A.sup id) := by
    intro n hn
    rw [Finset.mem_Icc]
    exact ⟨hA n hn, Finset.le_sup (f := id) hn⟩
  have key : ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 (M + 1), 1 / ((n : ℝ) ^ 2)) ≤ 2 - 1 / ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero =>
      have hI : Finset.Icc 1 (0 + 1) = ({1} : Finset ℕ) := by simp
      rw [hI, Finset.sum_singleton]
      norm_num
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := M + 1) (by omega)]
      push_cast
      have hstep : 1 / (((M : ℝ) + 1 + 1) ^ 2) ≤ 1 / ((M : ℝ) + 1) - 1 / ((M : ℝ) + 1 + 1) := by
        have hsplit : 1 / ((M : ℝ) + 1) - 1 / ((M : ℝ) + 1 + 1)
            = 1 / (((M : ℝ) + 1) * ((M : ℝ) + 1 + 1)) := by
          rw [div_sub_div _ _ (ne_of_gt (show (0 : ℝ) < (M : ℝ) + 1 by positivity))
            (ne_of_gt (show (0 : ℝ) < (M : ℝ) + 1 + 1 by positivity))]
          ring_nf
        rw [hsplit]
        apply one_div_le_one_div_of_le
          (show (0 : ℝ) < ((M : ℝ) + 1) * ((M : ℝ) + 1 + 1) by positivity)
        nlinarith [Nat.cast_nonneg (α := ℝ) M]
      linarith [ih, hstep]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro i _ _; positivity)) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.le_succ (A.sup id))) (by intro i _ _; positivity)) ?_
  refine le_trans (key (A.sup id)) ?_
  have hnn : (0 : ℝ) ≤ 1 / (((A.sup id : ℕ) : ℝ) + 1) := by positivity
  linarith

/-- For an `s`-indexed family of reals `u` that is `1`-separated and takes values `≥ 1`,
the sum of `1/(1 + (u a)^2)` is at most `2`. -/
lemma separated_sum_le_two {α : Type*} [DecidableEq α] (s : Finset α) (u : α → ℝ)
    (hpos : ∀ a ∈ s, 1 ≤ u a)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 1 ≤ |u a - u b|) :
    (∑ a ∈ s, 1 / (1 + (u a) ^ 2)) ≤ 2 := by
  have hterm : ∀ a ∈ s, 1 / (1 + (u a) ^ 2) ≤ 1 / ((⌊u a⌋₊ : ℝ) ^ 2) := by
    intro a ha
    have h1 : (1 : ℝ) ≤ u a := hpos a ha
    have hfl : (1 : ℝ) ≤ ((⌊u a⌋₊ : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ ⌊u a⌋₊ := Nat.le_floor (by exact_mod_cast h1)
      exact_mod_cast this
    have hle : (((⌊u a⌋₊ : ℕ) : ℝ)) ^ 2 ≤ 1 + (u a) ^ 2 := by
      have hfu : ((⌊u a⌋₊ : ℕ) : ℝ) ≤ u a := Nat.floor_le (by linarith)
      nlinarith [hfu, hfl]
    exact one_div_le_one_div_of_le (by positivity) hle
  have hinj : Set.InjOn (fun a => ⌊u a⌋₊) ↑s := by
    intro a ha b hb hab
    change ⌊u a⌋₊ = ⌊u b⌋₊ at hab
    by_contra hne
    have hsa : (1 : ℝ) ≤ |u a - u b| := hsep a ha b hb hne
    have ha1 : ((⌊u a⌋₊ : ℕ) : ℝ) ≤ u a := Nat.floor_le (by linarith [hpos a ha])
    have ha2 : u a < ((⌊u a⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (u a)
    have hb1 : ((⌊u b⌋₊ : ℕ) : ℝ) ≤ u b := Nat.floor_le (by linarith [hpos b hb])
    have hb2 : u b < ((⌊u b⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (u b)
    rw [hab] at ha1 ha2
    have hlt : |u a - u b| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    linarith
  calc (∑ a ∈ s, 1 / (1 + (u a) ^ 2))
      ≤ ∑ a ∈ s, 1 / ((⌊u a⌋₊ : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = ∑ n ∈ s.image (fun a => ⌊u a⌋₊), 1 / ((n : ℝ) ^ 2) :=
        (Finset.sum_image (f := fun n : ℕ => 1 / ((n : ℝ) ^ 2))
          (g := fun a : α => ⌊u a⌋₊) hinj).symm
    _ ≤ 2 := sum_inv_sq_le_two _
        (by
          intro n hn
          rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
          exact Nat.le_floor (by exact_mod_cast hpos a ha))

/-- Row sums over a `1`-separated set of points of the line are bounded by `5`. -/
theorem separated_row_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℕ) (t : Fin R → ℝ),
      (∀ i j : Fin R, i ≠ j → 1 ≤ |t i - t j|) →
      ∀ i : Fin R, ∑ j : Fin R, 1 / (1 + (t i - t j) ^ 2) ≤ C := by
  refine ⟨5, by norm_num, ?_⟩
  intro R t ht i
  have hsplit : (∑ j : Fin R, 1 / (1 + (t i - t j) ^ 2))
      = (∑ j ∈ Finset.univ.filter (fun j : Fin R => t i < t j), 1 / (1 + (t i - t j) ^ 2))
        + (∑ j ∈ Finset.univ.filter (fun j : Fin R => ¬ t i < t j),
            1 / (1 + (t i - t j) ^ 2)) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin R => t i < t j)
      (fun j : Fin R => 1 / (1 + (t i - t j) ^ 2))).symm
  rw [hsplit]
  have hnot : Finset.univ.filter (fun j : Fin R => ¬ t i < t j)
      = insert i (Finset.univ.filter (fun j : Fin R => t j < t i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      by_cases hji : j = i
      · exact Or.inl hji
      · refine Or.inr ?_
        have hne : t j ≠ t i := by
          intro heq
          have h1 := ht j i hji
          rw [heq, sub_self, abs_zero] at h1
          linarith
        exact lt_of_le_of_ne (not_lt.mp hj) hne
    · rintro (rfl | h)
      · exact lt_irrefl _
      · exact not_lt.mpr (le_of_lt h)
  rw [hnot, Finset.sum_insert (by simp),
    show 1 / (1 + (t i - t i) ^ 2) = 1 from by rw [sub_self]; norm_num]
  have hA2 : (∑ j ∈ Finset.univ.filter (fun j : Fin R => t i < t j),
      1 / (1 + (t i - t j) ^ 2)) ≤ 2 := by
    calc (∑ j ∈ Finset.univ.filter (fun j : Fin R => t i < t j),
          1 / (1 + (t i - t j) ^ 2))
        = ∑ j ∈ Finset.univ.filter (fun j : Fin R => t i < t j),
            1 / (1 + (t j - t i) ^ 2) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show (t i - t j) ^ 2 = (t j - t i) ^ 2 by ring]
      _ ≤ 2 := by
          apply separated_sum_le_two
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            have hne : i ≠ j := by intro h; rw [h] at hj; exact lt_irrefl _ hj
            have h1 := ht i j hne
            rw [abs_of_neg (by linarith)] at h1
            linarith
          · intro a ha b hb hab
            have h1 := ht a b hab
            have hsub : (t a - t i) - (t b - t i) = t a - t b := by ring
            rw [hsub]
            exact h1
  have hB2 : (∑ j ∈ Finset.univ.filter (fun j : Fin R => t j < t i),
      1 / (1 + (t i - t j) ^ 2)) ≤ 2 := by
    apply separated_sum_le_two
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hne : j ≠ i := by intro h; rw [h] at hj; exact lt_irrefl _ hj
      have h1 := ht j i hne
      rw [abs_of_neg (by linarith)] at h1
      linarith
    · intro a ha b hb hab
      have h1 := ht a b hab
      have hsub : (t i - t a) - (t i - t b) = t b - t a := by ring
      rw [hsub]
      rwa [abs_sub_comm]
  linarith

end Work.BMF
