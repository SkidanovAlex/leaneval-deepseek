import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EllExist.Honesty.RadGreenDzuDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

-- `Dzu` (in `Work.FTS.EllExist.Honesty.RadGreenDzuDefs`) is the univariate operator
-- `(z ∂_z)^i` on `ℝ → ℝ`.  Claim: if `c` is `C^{n+1}` on `(0,∞)` then each `Dzu t c` with
-- `t ≤ n` is differentiable at every point of `(0,∞)`.
-- ROUTE: prove the stronger uniform statement `ContDiffOn ℝ m (Dzu t c) (Ioi 0)` whenever
-- `ContDiffOn ℝ (t+m) c (Ioi 0)`, by induction on `t`: `Dzu (t+1) c = fun z => z * deriv (Dzu t c) z`,
-- and `ContDiffOn.deriv_of_isOpen isOpen_Ioi` lowers the order by one, `contDiffOn_id` gives
-- `z ↦ z`, `ContDiffOn.mul` multiplies the two.

/-- The uniform form of the claim, in the sharp shape needed by the induction: if `c` is
`C^{m+t}` on `(0,∞)` (the order `m` being an element of `WithTop ℕ∞`, so that it can be
lowered by one at each step) then `Dzu t c = (z ∂_z)^t c` is `C^m` there.

The induction is on `t`; the step uses
`Dzu (t+1) c = fun z => z * deriv (Dzu t c) z` together with `ContDiffOn.deriv_of_isOpen`
and `ContDiffOn.mul` (`z ↦ z` is smooth on `(0,∞)`). -/
theorem contDiffOn_Dzu (c : ℝ → ℝ) (t : ℕ) (m : WithTop ℕ∞)
    (hc : ContDiffOn ℝ (m + t) c (Set.Ioi 0)) :
    ContDiffOn ℝ m (Dzu t c) (Set.Ioi 0) := by
  induction t generalizing m with
  | zero => simpa using hc
  | succ n ih =>
      have h2 : ContDiffOn ℝ (m + 1) (Dzu n c) (Set.Ioi 0) :=
        ih (m + 1) (by
          have hh : ((m + 1 : WithTop ℕ∞) + (n : WithTop ℕ∞)) = (m + ↑(Nat.succ n)) := by
            push_cast
            abel
          exact hh.symm ▸ hc)
      have h3 : ContDiffOn ℝ m (deriv (Dzu n c)) (Set.Ioi 0) :=
        h2.deriv_of_isOpen isOpen_Ioi le_rfl
      have h4 : ContDiffOn ℝ m (id : ℝ → ℝ) (Set.Ioi 0) := contDiffOn_id
      have h5 : ContDiffOn ℝ m (fun z : ℝ => z * deriv (Dzu n c) z) (Set.Ioi 0) :=
        h4.mul h3
      simpa [Dzu_succ] using h5

theorem dzu_differentiableAt (c : ℝ → ℝ) (n : ℕ)
    (hc : ContDiffOn ℝ (n + 1) c (Set.Ioi 0)) :
    ∀ t ≤ n, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (Work.FTS.EllExist.Honesty.Dzu t c) z := by
  intro t ht z hz
  -- `c` is `C^{t + (n - t + 1)}`, so `Dzu t c` is `C^{n-t+1}`, with `n - t + 1 ≥ 1`.
  have hle : n - t + 1 + t = n + 1 := by omega
  have hcast : ((n - t + 1 : ℕ) : WithTop ℕ∞) + (t : WithTop ℕ∞) = ((n + 1 : ℕ) : WithTop ℕ∞) := by
    rw [← Nat.cast_add, hle]
  have h : ContDiffOn ℝ ((n - t + 1 : ℕ) : WithTop ℕ∞) (Dzu t c) (Set.Ioi 0) :=
    contDiffOn_Dzu c t _ (hcast.symm ▸ hc)
  have hn : ((n - t + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (by omega : n - t + 1 ≠ 0)
  have hd : DifferentiableOn ℝ (Dzu t c) (Set.Ioi 0) := h.differentiableOn hn
  exact hd.differentiableAt (isOpen_Ioi.mem_nhds hz)

end Work.FTS.EllExist.Honesty
