import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_one

namespace Work.PL.Approx.Cutoff

open Set Metric

/-- If `f` and `g` are `ε'`-close on the simplex `PL.simp s`, `g` maps `x ∈ PL.simp s` into the
closed cube of radius `α`, and `α + 4 ε' ≤ a < b`, then the cutoff `cubeCut a b` equals `1`
on `f`-image of `PL.simp s`. -/
lemma cubeCut_eq_one_of_mem {N n : ℕ} (s : Finset (PL.E N)) (x : PL.E N) (f g : PL.E N → PL.E n)
    {α a b ε' : ℝ} (hαb : α + 4 * ε' ≤ a) (hab : a < b) (hε' : 0 < ε') (hx : x ∈ PL.simp s)
    (hgx : g x ∈ PL.closedCube α) (hg : ∀ y ∈ PL.simp s, dist (g y) (f y) < ε')
    (hf : ∀ y ∈ PL.simp s, dist (f y) (f x) < ε') :
    ∀ y ∈ PL.simp s, cubeCut a b (f y) = 1 := by
  intro y hy
  apply cubeCut_eq_one hab
  intro i
  have hfy : |(f y) i - (f x) i| < ε' :=
    lt_of_le_of_lt (PiLp.dist_apply_le (f y) (f x) i) (hf y hy)
  have hfx : |(f x) i - (g x) i| < ε' :=
    lt_of_le_of_lt (PiLp.dist_apply_le (f x) (g x) i)
      ((dist_comm (f x) (g x)).trans_lt (hg x hx))
  have hgxi : |(g x) i| ≤ α := hgx i
  have h1 := neg_abs_le ((g x) i)
  have h2 := le_abs_self ((g x) i)
  have hfy' := abs_lt.mp hfy
  have hfx' := abs_lt.mp hfx
  exact le_of_lt (abs_lt.mpr ⟨by linarith, by linarith⟩)

end Work.PL.Approx.Cutoff
