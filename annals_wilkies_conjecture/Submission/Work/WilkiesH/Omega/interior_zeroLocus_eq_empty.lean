import Mathlib
import Submission.Work.WilkiesH.Defs

/-!
# The zero set of a nonzero real polynomial has empty interior

For a nonzero polynomial `P` in `n` real variables, the zero set
`{x : Fin n → ℝ | P.eval x = 0}` has empty interior.

The proof is the classical one.  If the zero set contained an interior point `x`, it
would be a neighbourhood of `x`, hence would contain a metric ball `ball x ε` with
`ε > 0`.  By `ball_pi` and `Real.ball_eq_Ioo`, that ball is the product of the open
intervals `Ioo (x i - ε) (x i + ε)`, each of which is infinite.  So `P` would vanish
on a product-of-infinite-sets box, and `MvPolynomial.funext_set` (function
extensionality for polynomials over an infinite integral domain) forces `P = 0`,
contradicting `hP`.
-/

set_option autoImplicit false

namespace Work.WilkiesH.Omega

theorem interior_zeroLocus_eq_empty {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0) : interior {x : Fin n → ℝ | P.eval x = 0} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  -- membership in the interior means the zero set is a neighbourhood of `x`
  rw [mem_interior_iff_mem_nhds] at hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hx
  -- the ball around `x` is a product of intervals, all of them infinite
  have hvan : ∀ y ∈ Set.univ.pi (fun i => Set.Ioo (x i - ε) (x i + ε)), P.eval y = 0 := by
    intro y hy
    apply hball
    rw [ball_pi x hε, Set.mem_pi]
    intro i _
    rw [Real.ball_eq_Ioo]
    exact (Set.mem_pi.mp hy) i (Set.mem_univ i)
  -- a polynomial vanishing on a box with infinite sides is zero
  have hP0 : P = 0 := MvPolynomial.funext_set (p := P) (q := 0)
    (fun i => Set.Ioo (x i - ε) (x i + ε)) (fun i => Set.Ioo_infinite (by linarith))
    (fun y hy => by simpa using hvan y hy)
  exact hP hP0

end Work.WilkiesH.Omega
