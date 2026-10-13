import Mathlib
import Submission.Work.DSM4p.Chart
import Submission.Work.DSM4p.ChartUnit

namespace Work.DSM4p

universe a

/-- Iterated form of the root relation `x_k(m) = x_{k+1}(m)^p` of `chartGen_succ_pow`:
`x_k(m) = x_{k+d}(m)^(p^d)`. -/
theorem chartGen_add_root {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (gr : ℕ → B) (hgr : Work.DSM4p.IsRootSystem p gr) (ϖ : ℕ → B)
    (hϖ : Work.DSM4p.IsRootSystem p ϖ) (m k d : ℕ) :
    Work.DSM4p.chartGen hgr ϖ m k =
      Work.DSM4p.chartGen hgr ϖ m (k + d) ^ p ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [ih, chartGen_succ_pow hgr hϖ m (k + d), Nat.add_assoc, ← pow_mul, pow_succ']

theorem chartGen_root_pow {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (gr : ℕ → B) (hgr : Work.DSM4p.IsRootSystem p gr) (ϖ : ℕ → B)
    (hϖ : Work.DSM4p.IsRootSystem p ϖ) (m J J' : ℕ) (h : J ≤ J') :
    Work.DSM4p.chartGen hgr ϖ m J = Work.DSM4p.chartGen hgr ϖ m J' ^ p ^ (J' - J) := by
  have hkey := chartGen_add_root gr hgr ϖ hϖ m J (J' - J)
  rw [show J + (J' - J) = J' by omega] at hkey
  exact hkey

end Work.DSM4p
