import Mathlib
import Submission.Work.Pi6.EFACTS.FibreCoh
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cohomology ring of the fibre, with a nonzero generator

`Work.Pi6.EFACTS.fibreCoh` (from `K2ZFacts` + the `K(ℤ,2)`-structure of `fib g3`) gives a generator
`x` of `H²(fib g3)` with `H^{2k}(fib g3) = ℤ·x^k` for `k ≤ 4` and `H^{odd}(fib g3) = 0`.  This file
records the same statement with the additional (easily derived) fact that `x ≠ 0`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Pi6.EFACTS

noncomputable section

/-- If every element is a unique multiple of `y`, then `y ≠ 0`. -/
theorem ne_zero_of_unique_multiple {M : Type} [AddCommGroup M] (y : M)
    (h : ∀ a : M, ∃! n : ℤ, a = n • y) : y ≠ 0 := by
  obtain ⟨n, _, huniq⟩ := h y
  intro hy
  have h1 : (1 : ℤ) = n := huniq 1 (by show y = 1 • y; rw [one_smul])
  have h0 : (0 : ℤ) = n := huniq 0 (by show y = 0 • y; rw [zero_smul]; exact hy)
  omega

theorem cpow_one_eq {X : Type} [TopologicalSpace X] (x : Coh ℤ X 2) : cpow x 1 = x := by
  show Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) 0 2
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) x = x
  exact Work.Cohomology.cupH'_one_left ℤ (TopCat.toSSet.obj (TopCat.of X)) 2 x

/-- **The fibre's cohomology ring, with a nonzero generator**, from `K2ZFacts` and the
`K(ℤ,2)`-structure of `fib g3`. -/
theorem fibreRing {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) (x₀ : fib g3)
    (hfib : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 11 (fib g3) x₀)
    (hZ : Work.Pi6.K2ZFacts) :
    ∃ x : Coh ℤ (fib g3) 2,
      x ≠ 0 ∧
      (∀ k : ℕ, k ≤ 4 → ∀ a : Coh ℤ (fib g3) (2 * k), ∃! n : ℤ, a = n • cpow x k) ∧
      (∀ k : ℕ, k ≤ 4 → Subsingleton (Coh ℤ (fib g3) (2 * k + 1))) := by
  obtain ⟨x, hmult, hodd⟩ := (fibreCoh g3 x₀ hfib hZ).1
  have hx : x ≠ 0 := by
    have h := ne_zero_of_unique_multiple (cpow x 1)
      (fun a => hmult 1 (by norm_num) a)
    rwa [cpow_one_eq x] at h
  exact ⟨x, hx, hmult, hodd⟩

end

end Work.Pi6.EFACTS
