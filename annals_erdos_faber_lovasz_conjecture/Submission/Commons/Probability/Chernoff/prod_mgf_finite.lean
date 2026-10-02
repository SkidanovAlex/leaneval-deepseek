import Mathlib.Analysis.Complex.Exponential

namespace Commons.Probability.Chernoff

open Finset

theorem prod_mgf_finite (m : ℕ) (p X : Fin m → ℝ) (t : ℝ) :
    (∑ s : Fin m → Bool, (∏ i : Fin m, (if s i then p i else 1 - p i)) *
        Real.exp (t * ∑ i : Fin m, (if s i then X i else 0)))
      = ∏ i : Fin m, ((1 - p i) + p i * Real.exp (t * X i)) := by
  classical
  let g : Fin m → Bool → ℝ := fun i b =>
    (if b then p i else 1 - p i) * Real.exp (t * (if b then X i else 0))
  have step1 : (∑ s : Fin m → Bool, (∏ i : Fin m, (if s i then p i else 1 - p i)) *
        Real.exp (t * ∑ i : Fin m, (if s i then X i else 0)))
      = ∑ s : Fin m → Bool, ∏ i : Fin m, g i (s i) := by
    apply Finset.sum_congr rfl
    intro s _
    have hexp : Real.exp (t * ∑ i : Fin m, (if s i then X i else 0))
        = ∏ i : Fin m, Real.exp (t * (if s i then X i else 0)) := by
      rw [Finset.mul_sum, Real.exp_sum]
    rw [hexp, ← Finset.prod_mul_distrib]
  have step2 : (∑ s : Fin m → Bool, ∏ i : Fin m, g i (s i))
      = ∏ i : Fin m, ∑ b : Bool, g i b := by
    have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset Bool)) (g := g)
    rw [Fintype.piFinset_univ] at h
    simpa using h
  have step3 : ∀ i : Fin m, (∑ b : Bool, g i b)
      = (1 - p i) + p i * Real.exp (t * X i) := by
    intro i
    have htrue : g i true = p i * Real.exp (t * X i) := by simp [g]
    have hfalse : g i false = 1 - p i := by simp [g]
    rw [Fintype.sum_bool, htrue, hfalse]
    ring
  rw [step1, step2]
  exact Finset.prod_congr rfl (fun i _ => step3 i)

end Commons.Probability.Chernoff