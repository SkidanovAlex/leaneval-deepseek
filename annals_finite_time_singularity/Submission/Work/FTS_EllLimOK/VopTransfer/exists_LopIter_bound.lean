import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.VopTransfer

/-- A function which is `C^k` for every `k : ℕ` (finite order smoothness — note that `⊤` in
this Mathlib means *analytic*, which is not assumed) has `C^k` iterates of the angular
operator `Lop u = sin(2θ) · u'`.

Proved by induction on the number of iterates: the derivative of a `C^{k+1}` function is
`C^k` (`ContDiff.deriv'`), and `sin(2·)` is smooth. -/
private lemma contDiff_lopIter (u : ℝ → ℝ) (hu : ∀ k : ℕ, ContDiff ℝ k u) :
    ∀ r k : ℕ, ContDiff ℝ k (Work.Spaces.Lop^[r] u) := by
  intro r
  induction r with
  | zero => intro k; simpa using hu k
  | succ r ih =>
    intro k
    rw [Function.iterate_succ_apply']
    have h2 : ContDiff ℝ k (deriv (Work.Spaces.Lop^[r] u)) :=
      ContDiff.deriv' (ih (k + 1))
    exact (by fun_prop : ContDiff ℝ k (fun θ : ℝ => Real.sin (2 * θ))).mul h2

theorem exists_LopIter_bound (u : ℝ → ℝ) (hu : ∀ k : ℕ, ContDiff ℝ k u) (A : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ≤ A, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter r u θ| ≤ B := by
  have hsmooth : ∀ r k : ℕ, ContDiff ℝ k (Work.Spaces.Lop^[r] u) := contDiff_lopIter u hu
  have hcont : ∀ r : ℕ, Continuous (Work.Spaces.Lop^[r] u) := fun r => (hsmooth r 0).continuous
  -- every iterate is continuous, hence bounded on the compact interval `Iθ = [0, π/2]`
  choose C hC using fun r : ℕ =>
    IsCompact.exists_bound_of_continuousOn isCompact_Icc (hcont r).continuousOn
  refine ⟨∑ r ∈ Finset.range (A + 1), max 0 (C r), ?_, ?_⟩
  · exact Finset.sum_nonneg fun r _ => le_max_left _ _
  · intro r hr θ hθ
    show |(Work.Spaces.Lop^[r] u) θ| ≤ _
    have hmem : r ∈ Finset.range (A + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hr)
    have h1 : |(Work.Spaces.Lop^[r] u) θ| ≤ max 0 (C r) := by
      have h := hC r θ hθ
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_right _ _)
    exact le_trans h1 (Finset.single_le_sum (fun i _ => le_max_left (0 : ℝ) (C i)) hmem)

end Work.FTS_EllLimOK.VopTransfer
