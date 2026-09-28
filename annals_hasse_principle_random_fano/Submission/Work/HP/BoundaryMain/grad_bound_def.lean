import Mathlib

/-!
# `Work.HP.BoundaryMain.gradBound`

An explicit uniform upper bound for the coefficients `c i = a (smon d n hd j i)` (`i : Fin (n+1)`)
of the `n+1` "special" monomials `x_j^{d-1}x_i` of an integer form `a`, given that the gradient of
`f_a` at a point `y` with `y_j ≠ 0` has Euclidean norm at most `C`.

The bound is read off the decomposition `gradF_decomp` of `∇f_a(y)`: the coefficients `c i` for
`i ≠ j` are pinned by the `i`-th gradient inequality, and then `c j` is pinned by the `j`-th one:

* `Kp = |y_j|^{d-1}`,
* `U i = (C + |B i|) / Kp`, where `B i = ∂_i f_{zeroS j a}(y)` is the `i`-th component of the
  gradient of the "free part" of `a`,
* `c i ≤ |U i|` for `i ≠ j`, and
* `c j ≤ |(C + |B j| + |y_j|^{d-2} (d-1) ∑_{i≠j} |U i| |y_i|) / (d Kp)|`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.BoundaryMain

/-- Explicit uniform bound for the coefficients of the special monomials `x_j^{d-1}x_i`. -/
def gradBound (d n : ℕ) (C : ℝ) (y : Fin (n + 1) → ℝ) (j : Fin (n + 1))
    (B : Fin (n + 1) → ℝ) : ℝ :=
  max (∑ k : Fin (n + 1), |(C + |B k|) / |y j| ^ (d - 1)|)
    |(C + |B j| + |y j| ^ (d - 2) * ((d : ℝ) - 1)
        * (∑ i ∈ Finset.univ.erase j, |(C + |B i|) / |y j| ^ (d - 1)| * |y i|))
      / ((d : ℝ) * |y j| ^ (d - 1))|

end Work.HP.BoundaryMain
