import Mathlib
import Submission.Work.Peluse.Holds.ExpPET.Defs
import Submission.Work.Peluse.BoxNorm.cubeTerm_tsum_finite

namespace Work.Peluse.ExpA

open scoped BigOperators

open Work.Peluse.Holds.ExpPET

/-- Iterated conjugation does not change the norm. -/
private lemma norm_iterate_star (k : ℕ) (z : ℂ) : ‖(star^[k]) z‖ = ‖z‖ := by
  induction k with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- The all-false sign pattern has weight `0`. -/
private lemma weight_zeros (s : ℕ) : Work.Peluse.weight (zeros s) = 0 := by
  simp [Work.Peluse.weight, zeros]

/-- The corner shift of the all-false sign pattern. -/
private lemma cubeShift_zeros {s : ℕ} (κ n n' : Fin s → ℤ) :
    cubeShift κ n n' (zeros s) = ∑ i : Fin s, n' i * κ i := by
  simp [cubeShift, zeros]

/-- The `tsum` of the cube term is at most the cardinality of the support of `f`: the factor of the
cube term at the all-false sign pattern is `f (x + ∑ᵢ n'ᵢκᵢ)`, so the cube term vanishes unless `x`
lies in the (at most `#S`-element) translate `S - ∑ᵢ n'ᵢκᵢ` of the support, and on that set it is
bounded by `1` in modulus. -/
theorem expCubeTsumLe {s : ℕ} (κ n n' : Fin s → ℤ) {f : ℤ → ℂ} {S : Finset ℤ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsupp : ∀ x : ℤ, x ∉ S → f x = 0) :
    ‖∑' x : ℤ, Work.Peluse.Holds.ExpPET.expCube κ n n' f x‖ ≤ (S.card : ℝ) := by
  classical
  set A : ℤ := ∑ i : Fin s, n' i * κ i with hA
  set T : Finset ℤ := S.image (fun y => y - A) with hT
  have hcs : cubeShift κ n n' (zeros s) = A := by rw [cubeShift_zeros, hA]
  -- the cube term vanishes off the translate `T` of the support
  have hvanish : ∀ x : ℤ, x ∉ T → Work.Peluse.Holds.ExpPET.expCube κ n n' f x = 0 := by
    intro x hx
    have hxA : x + A ∉ S := by
      intro hmem
      exact hx (by rw [hT]; exact Finset.mem_image.mpr ⟨x + A, hmem, by ring⟩)
    have hfac : f (x + cubeShift κ n n' (zeros s)) = 0 := by
      rw [hcs]
      exact hsupp _ hxA
    rw [Work.Peluse.Holds.ExpPET.expCube]
    exact Finset.prod_eq_zero (Finset.mem_univ (zeros s))
      (by rw [weight_zeros, Function.iterate_zero_apply]; exact hfac)
  -- the cube term is bounded by `1` everywhere
  have hexp : ∀ x : ℤ, ‖Work.Peluse.Holds.ExpPET.expCube κ n n' f x‖ ≤ 1 := by
    intro x
    rw [Work.Peluse.Holds.ExpPET.expCube, norm_prod]
    refine Finset.prod_le_one₀ (fun ω _ => norm_nonneg _) (fun ω _ => ?_)
    rw [norm_iterate_star]
    exact hf _
  rw [tsum_eq_sum (s := T) hvanish]
  calc ‖∑ x ∈ T, Work.Peluse.Holds.ExpPET.expCube κ n n' f x‖
      ≤ ∑ x ∈ T, ‖Work.Peluse.Holds.ExpPET.expCube κ n n' f x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ T, (1 : ℝ) := Finset.sum_le_sum fun x _ => hexp x
    _ = (T.card : ℝ) := by simp
    _ ≤ (S.card : ℝ) := by
        rw [hT]
        exact_mod_cast Finset.card_image_le

end Work.Peluse.ExpA
