import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.Weyl_factor
import Submission.Work.BMF.recursion.integral_normSq_eq_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary objects for the first Hölder step `Tdbl ≤ J_{S,k}(Q)^{1-1/S}`

This file collects the definitions used in the proof of
`Work.BMF.recursion.Tdbl_le_rpow` (Wooley, *On Vinogradov's mean value theorem II*,
Michigan Math. J. **40** (1993), 175–180, §2, case (a)).

`Tdbl S k Q` counts the matching pairs of `S`-tuples in `[1,Q]` whose first two coordinates agree
on both sides.  Such a pair is encoded by

* `Idx S Q = Tup (S-2) Q × Finset.Icc 1 Q`: the pair `(x,v)` stands for the `S`-tuple
  `(v, v, x₀, …, x_{S-3})`;
* `Phi S k Q (x,v) = powerSums k x + 2 • mom1 k v`: the moment vector of that tuple, so that
  `Tdbl = #{((i,j)) : Phi i = Phi j}`;
* `Duo k Q = Σ_{v ∈ [1,Q]} mFourier (2 • mom1 k v)`: the "doubled" Weyl sum, so that the exponential
  sum over `Idx S Q` factorises as `ExpSum (s := S-2) · Duo`;
* `Wnorm k Q`, `Dnorm k Q`: the moduli of `Weyl k Q` and of `Duo k Q`, which are the two functions
  the `L^p` Hölder step is applied to.
-/

set_option autoImplicit false

namespace Work.BMF.recursion

open scoped BigOperators

noncomputable section

/-- Index set for the mean-value identity computing `Tdbl`: a tail `(S-2)`-tuple together with the
repeated value `v`; the pair `(x,v)` corresponds to the `S`-tuple `(v, v, x₀, …, x_{S-3})`. -/
abbrev Idx (S Q : ℕ) : Type := Tup (S - 2) Q × Finset.Icc 1 Q

/-- The moment vector of the `S`-tuple `(v, v, x₀, …, x_{S-3})`, i.e. `powerSums x + 2 • mom1 v`. -/
def Phi (S k Q : ℕ) (i : Idx S Q) : Fin (k + 1) → ℤ :=
  Submission.Vinogradov.powerSums k i.1 + (2 : ℤ) • mom1 k i.2.1

/-- The "doubled" one-variable Weyl sum `Σ_{v ∈ [1,Q]} e(θ · 2 • mom1 v)`. -/
def Duo (k Q : ℕ) : UnitAddTorus (Fin (k + 1)) → ℂ :=
  fun θ => ∑ v ∈ Finset.Icc 1 Q, UnitAddTorus.mFourier ((2 : ℤ) • mom1 k v) θ

/-- `θ ↦ ‖Weyl k Q θ‖`, the modulus of the single-variable Weyl sum. -/
def Wnorm (k Q : ℕ) : UnitAddTorus (Fin (k + 1)) → ℝ := fun θ => ‖Weyl k Q θ‖

/-- `θ ↦ ‖Duo k Q θ‖`. -/
def Dnorm (k Q : ℕ) : UnitAddTorus (Fin (k + 1)) → ℝ := fun θ => ‖Duo k Q θ‖

end

end Work.BMF.recursion
