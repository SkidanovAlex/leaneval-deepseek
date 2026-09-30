import Mathlib
import Submission.Work.BMF.SD.powQuot_def
import Submission.Work.BMF.SD.powQuot_mul
import Submission.Work.BMF.SD.powQuot_bound
import Submission.Work.BMF.SD.sum_bound_perturb

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A one-step integer approximation for a short-interval polynomial difference

Let `q, L, k` be naturals with `1 ≤ q ≤ L` and let `a j` (`2 ≤ j ≤ k`) be reals which are
`C₂ / L^j`-close to multiples of `1/q`:

`|q * a j - m j| ≤ C₂ / L^j`  for some integer `m j`.

For any `n` with `n + q ≤ 2L` the increment
`∑_{j=2}^{k} a j * ((n+q)^j - n^j)`
is then within `4^(k+1) * C₂ / L` of an integer.

The integer is `∑_{j} m j * powQuot n q j`, where `powQuot n q j = ((n+q)^j - n^j)/q` is the
explicit integral representative from `Work.BMF.SD.powQuot_def`; the error is controlled by
`|(n+q)^j - n^j| ≤ 4^j L^(j-1) · q` for `2 ≤ j`, and finally by the geometric-sum estimate
`∑_{j=2}^{k} 4^j ≤ 4^(k+1)`.
-/

set_option linter.unusedVariables false

namespace Work.BMF.SD

theorem a_one_bound_perturb (k : ℕ) (q L : ℕ) (a : ℕ → ℝ) (C₂ : ℝ)
    (hq : 1 ≤ q) (hL : 1 ≤ L) (hqL : (q:ℝ) ≤ (L:ℝ)) (hC₂ : 0 ≤ C₂)
    (hcoeff : ∀ j ∈ Finset.Icc 2 k, ∃ m : ℤ, |(q:ℝ) * a j - m| ≤ C₂ / (L:ℝ)^j)
    (n : ℕ) (hn : ((n + q : ℕ) : ℝ) ≤ 2 * L) :
    ∃ M : ℤ, |(∑ j ∈ Finset.Icc 2 k, a j * ((((n+q:ℕ):ℝ)^j) - ((n:ℝ)^j))) - M|
        ≤ (4:ℝ)^(k+1) * C₂ / (L:ℝ) := by
  classical
  -- a total choice of the integer `m j` witnessing `hcoeff`
  have hex : ∀ j : ℕ, ∃ m : ℤ, j ∈ Finset.Icc 2 k → |(q:ℝ) * a j - (m : ℝ)| ≤ C₂ / (L:ℝ)^j := by
    intro j
    by_cases hj : j ∈ Finset.Icc 2 k
    · exact ⟨Classical.choose (hcoeff j hj), fun _ => Classical.choose_spec (hcoeff j hj)⟩
    · exact ⟨0, fun h => absurd h hj⟩
  let mm : ℕ → ℤ := fun j => Classical.choose (hex j)
  have hm : ∀ j (hj : j ∈ Finset.Icc 2 k), |(q:ℝ) * a j - (mm j : ℝ)| ≤ C₂ / (L:ℝ)^j := by
    intro j hj
    exact Classical.choose_spec (hex j) hj
  have hnq : n + q ≤ 2 * L := by exact_mod_cast hn
  refine ⟨∑ j ∈ Finset.Icc 2 k, mm j * powQuot n q j, ?_⟩
  -- `(n+q)^j - n^j = q * powQuot n q j`
  have hE : ∀ j, (q:ℝ) * (powQuot n q j : ℝ) = ((n+q:ℕ):ℝ)^j - (n:ℝ)^j := by
    intro j
    have h4 := powQuot_mul n q j
    exact_mod_cast h4
  -- rewrite the difference as a single sum of small terms
  have hsplit : (∑ j ∈ Finset.Icc 2 k, a j * (((n+q:ℕ):ℝ)^j - (n:ℝ)^j))
      - ((∑ j ∈ Finset.Icc 2 k, mm j * powQuot n q j : ℤ) : ℝ)
      = ∑ j ∈ Finset.Icc 2 k, (a j * (q:ℝ) - (mm j : ℝ)) * (powQuot n q j : ℝ) := by
    rw [Int.cast_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Int.cast_mul, ← hE j]
    ring
  rw [hsplit]
  calc |∑ j ∈ Finset.Icc 2 k, (a j * (q:ℝ) - (mm j : ℝ)) * (powQuot n q j : ℝ)|
      ≤ ∑ j ∈ Finset.Icc 2 k, |(a j * (q:ℝ) - (mm j : ℝ)) * (powQuot n q j : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.Icc 2 k, |a j * (q:ℝ) - (mm j : ℝ)| * |(powQuot n q j : ℝ)| := by
        apply Finset.sum_congr rfl; intro j hj; rw [abs_mul]
    _ ≤ ∑ j ∈ Finset.Icc 2 k, (C₂ / (L:ℝ)^j) * ((4:ℝ)^j * (L:ℝ)^(j-1)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
        have hj1 : 1 ≤ j := by omega
        apply mul_le_mul
        · simpa [mul_comm] using hm j hj
        · exact powQuot_bound n q j L hj1 hnq
        · exact abs_nonneg _
        · positivity
    _ ≤ (4:ℝ)^(k+1) * C₂ / (L:ℝ) := sum_bound_perturb k L C₂ hL hC₂

end Work.BMF.SD
