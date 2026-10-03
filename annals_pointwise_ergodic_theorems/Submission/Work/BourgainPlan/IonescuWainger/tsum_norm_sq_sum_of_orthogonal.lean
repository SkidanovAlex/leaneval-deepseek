import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Sum

/-!
# Pythagoras for a finite family of pairwise orthogonal `ℓ²(ℤ)`-functions

If `g i : ℤ → ℂ` (`i` in a finite type `ι`) are square summable and pairwise orthogonal in the
`ℓ²` pairing `⟨h, k⟩ = ∑' m, h m * star (k m)`, then the squared `ℓ²`-norm of their sum is the sum
of the squared `ℓ²`-norms:

`∑' m, ‖∑ i, g i m‖ ^ 2 = ∑ i, ∑' m, ‖g i m‖ ^ 2`.

The proof expands `‖∑ i, g i m‖ ^ 2 = (∑ i, g i m) * star (∑ i, g i m)` as a double sum
`∑ i, ∑ j, g i m * star (g j m)` and exchanges the (absolutely convergent) `tsum` with the two
finite sums; the off-diagonal terms vanish by orthogonality.
-/

open scoped BigOperators

namespace Work.BourgainPlan.IonescuWainger

/-- For a complex number, `z * star z` is the (real) square of its norm, cast to `ℂ`.  Recorded
here because `Complex.mul_conj` is phrased with `starRingEnd` and so does not rewrite under `star`
directly. -/
theorem mul_star_eq_ofReal_norm_sq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq]
  exact Complex.mul_conj z

/-- The real part of `z * star z` is `‖z‖ ^ 2`. -/
theorem re_mul_star_eq_norm_sq (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  rw [mul_star_eq_ofReal_norm_sq, Complex.ofReal_re]

theorem tsum_norm_sq_sum_of_orthogonal {ι : Type*} [Fintype ι] {g : ι → ℤ → ℂ}
    (hg : ∀ i, Memℓp (g i) 2)
    (horth : ∀ i j : ι, i ≠ j → ∑' m : ℤ, g i m * star (g j m) = 0) :
    ∑' m : ℤ, ‖∑ i, g i m‖ ^ 2 = ∑ i, ∑' m : ℤ, ‖g i m‖ ^ 2 := by
  -- Each `‖g i ·‖ ^ 2` is summable.
  have hsq : ∀ i, Summable (fun m : ℤ => ‖g i m‖ ^ 2) := by
    intro i
    have h := (memℓp_gen_iff (p := 2) (by norm_num)).mp (hg i)
    simpa [Real.rpow_two] using h
  -- Hence each pairing `g i m * star (g j m)` is (absolutely) summable.
  have hprod : ∀ i j : ι, Summable (fun m : ℤ => g i m * star (g j m)) := by
    intro i j
    have h2 : Summable (fun m : ℤ => ‖g i m‖ * ‖g j m‖) := by
      refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun m => ?_) ((hsq i).add (hsq j))
      nlinarith [sq_nonneg (‖g i m‖ - ‖g j m‖)]
    refine Summable.of_norm (h2.congr (fun m => ?_))
    simp
  -- The inner finite sums are summable.
  have hsum2 : ∀ i, Summable (fun m : ℤ => ∑ j, g i m * star (g j m)) := fun i =>
    summable_sum (fun j _ => hprod i j)
  -- So is the product of the total sum with its conjugate.
  have hGG : Summable (fun m : ℤ => (∑ i, g i m) * star (∑ i, g i m)) := by
    have heq : (fun m : ℤ => (∑ i, g i m) * star (∑ i, g i m))
        = fun m => ∑ i, ∑ j, g i m * star (g j m) := by
      funext m
      rw [star_sum, Finset.sum_mul_sum]
    rw [heq]
    exact summable_sum (fun i _ => hsum2 i)
  -- The central complex identity.
  have key : (∑' m : ℤ, (∑ i, g i m) * star (∑ i, g i m))
      = ∑ i, ((∑' m : ℤ, ‖g i m‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : (∑' m : ℤ, (∑ i, g i m) * star (∑ i, g i m))
        = ∑' m : ℤ, ∑ i, ∑ j, g i m * star (g j m) :=
      tsum_congr (fun m => by rw [star_sum, Finset.sum_mul_sum])
    rw [h1, Summable.tsum_finsetSum (fun i _ => hsum2 i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Summable.tsum_finsetSum (fun j _ => hprod i j)]
    rw [Finset.sum_eq_single i (fun j _ hj => horth i j hj.symm)
        (fun h => absurd (Finset.mem_univ i) h)]
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun m => mul_star_eq_ofReal_norm_sq _)
  -- Taking real parts converts the complex identity into the goal.
  have hre : (∑' m : ℤ, (∑ i, g i m) * star (∑ i, g i m)).re
      = ∑' m : ℤ, ‖∑ i, g i m‖ ^ 2 := by
    rw [← Complex.reCLM_apply]
    rw [ContinuousLinearMap.map_tsum Complex.reCLM hGG]
    exact tsum_congr (fun m => by rw [Complex.reCLM_apply]; exact re_mul_star_eq_norm_sq _)
  rw [← hre, key]
  rw [← Complex.ofReal_sum]
  simp

end Work.BourgainPlan.IonescuWainger
