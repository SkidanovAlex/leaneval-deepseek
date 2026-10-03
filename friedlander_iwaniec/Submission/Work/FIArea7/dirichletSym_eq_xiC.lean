import Mathlib
import Submission.Work.FIArea7.sum_xiGaussMod_units
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- **The Dirichlet symbol is the `xiC` function of the residue class mod a multiple of `|w|²`.**
`Work.FIArea7.xiC q w p` is the Dirichlet symbol `ξ_w` read on a pair `p ∈ (Z/q)²`, and
`Work.FIArea7.DirichletSym w z = (Re(wz) | |w|²)`.  When `q` is a multiple of `|w|²` the two agree:

  `ξ_w(z) = xiC q w (z.re mod q, z.im mod q)`.

This is what lets the box sum `Σ_z ξ_{w₁}(z)ξ_{w₂}(z)` be identified with the `xiC` box sum of
`Work.FIArea7.sum_xiC_gBox_exact` (take `q = |w₁|²|w₂|²`).  Proof: `ZMod.val` reduces each
coordinate mod `q`, hence mod `|w|²`, and `Re(wz) = w.re·z.re − w.im·z.im` is a `ℤ`-linear
combination, so the two Jacobi symbols have congruent upper arguments modulo the common lower
argument `|w|²` (`jacobiSym` is periodic in the upper argument; the existing
`Work.FIArea7.xiC_eq_dirichletSym` and `Work.FIArea7.dirichletSym_periodic` do the work). -/
theorem dirichletSym_eq_xiC (q : ℕ) [NeZero q] (w z : GaussianInt)
    (hdvd : Work.FIPlan.gnorm w ∣ q) :
    xiC q w ((z.re : ZMod q), (z.im : ZMod q)) = (DirichletSym w z : ℂ) := by
  -- The canonical lift `pairToGI q (z.re, z.im)` is `z` modulo `q`.
  have hdvd' : (((q : ℕ) : ℤ) : GaussianInt) ∣ pairToGI q ((z.re : ZMod q), (z.im : ZMod q)) - z := by
    apply dvd_of_casts_eq <;> simp [pairToGI]
  -- Read `xiC` as `DirichletSym` on that lift; `|w|² ∣ q` makes `ξ_w` periodic, so the two agree.
  rw [xiC_eq_dirichletSym, dirichletSym_periodic hdvd hdvd']

end Work.FIArea7
