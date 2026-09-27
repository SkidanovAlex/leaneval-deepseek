import Mathlib
import Submission.Work.KT.Fund.kappa_hopf_defs

/-!
# `Work.KT.Fund.kappa_hopf_graphproj` — the orthogonal projection onto the graph of `F₀`

For a lift `F` of a unit `u` to the disc, `graphProj F` is the orthogonal projection onto the
graph of `F`.  Here `F₀ = !![g]` is the explicit `1 × 1` lift of the disc coordinate `z`, with
`g = c/(1+s)` (`c` the coordinate, `s = √(1-‖c‖²)` the height).  The abstract computation
`graphProj_one` expresses `graphProj !![f]` in terms of any two-sided inverse `w` of
`1 + (star f) f`; for `f = g` one has `1 + (star g) g = 2 cHeightInv` (this is `F0_gram`), whose
inverse is `halfC * (1 + cHeight)`, because `2 * halfC = 1` and `cHeightInv * (1 + cHeight) = 1`.
This file evaluates the resulting `2 × 2` matrix explicitly, in the form needed for the Hopf
clutching analysis (`kappa_hopf`): the entries are expressed through `cCoord`, `cHeight` and
`halfC`.
-/

namespace Work.KT.Fund

theorem kappa_hopf_graphproj (X : Type) [TopologicalSpace X] :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (graphProj C(X × Ball ℂ, ℂ) (F0 X))
      = !![(1 + cHeight X) * halfC X, star (cCoord X) * halfC X;
           cCoord X * halfC X, (1 - cHeight X) * halfC X] := by
  -- `w = halfC * (1 + cHeight)` is the two-sided inverse of `1 + (star g) g = 2 * cHeightInv`.
  have h1 : (1 + star (gFun X) * gFun X) * (halfC X * (1 + cHeight X)) = 1 := by
    rw [F0_gram X]
    rw [show (2 * cHeightInv X) * (halfC X * (1 + cHeight X))
        = (2 * halfC X) * (cHeightInv X * (1 + cHeight X)) by ring]
    rw [two_mul_halfC X, hUnit_inv_mul X, one_mul]
  have h2 : (halfC X * (1 + cHeight X)) * (1 + star (gFun X) * gFun X) = 1 := by
    rw [F0_gram X]
    rw [show (halfC X * (1 + cHeight X)) * (2 * cHeightInv X)
        = (2 * halfC X) * ((1 + cHeight X) * cHeightInv X) by ring]
    rw [two_mul_halfC X, hUnit_mul X, one_mul]
  -- The abstract `1 × 1` formula for `graphProj`, evaluated at `f = g`, `w = halfC * (1 + cHeight)`.
  rw [show F0 X = !![gFun X] from rfl,
    graphProj_one (gFun X) (halfC X * (1 + cHeight X)) h1 h2]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · show halfC X * (1 + cHeight X) = (1 + cHeight X) * halfC X
    exact mul_comm _ _
  · -- `(0,1)`: `w * star g = star cCoord * halfC`, using `(1 + cHeight) * cHeightInv = 1`.
    show halfC X * (1 + cHeight X) * star (gFun X) = star (cCoord X) * halfC X
    rw [star_gFun X]
    rw [show halfC X * (1 + cHeight X) * (star (cCoord X) * cHeightInv X)
        = (halfC X * star (cCoord X)) * ((1 + cHeight X) * cHeightInv X) by ring]
    rw [hUnit_mul X, mul_one]
    ring
  · -- `(1,0)`: `g * w = cCoord * halfC`, using `cHeightInv * (1 + cHeight) = 1`.
    show gFun X * (halfC X * (1 + cHeight X)) = cCoord X * halfC X
    rw [gFun]
    rw [show (cCoord X * cHeightInv X) * (halfC X * (1 + cHeight X))
        = (cCoord X * halfC X) * (cHeightInv X * (1 + cHeight X)) by ring]
    rw [hUnit_inv_mul X, mul_one]
  · -- `(1,1)`: `g * w * star g = (1 - cHeight) * halfC`, using `star_cCoord_mul_cCoord`.
    show gFun X * (halfC X * (1 + cHeight X)) * star (gFun X) = (1 - cHeight X) * halfC X
    rw [star_gFun X, gFun]
    rw [show (cCoord X * cHeightInv X) * (halfC X * (1 + cHeight X)) * (star (cCoord X) * cHeightInv X)
        = (cCoord X * star (cCoord X)) * halfC X
            * ((cHeightInv X * (1 + cHeight X)) * cHeightInv X) by ring]
    rw [hUnit_inv_mul X, one_mul]
    rw [show cCoord X * star (cCoord X) = (1 - cHeight X) * (1 + cHeight X) by
          rw [mul_comm, star_cCoord_mul_cCoord X]; ring]
    rw [show (1 - cHeight X) * (1 + cHeight X) * halfC X * cHeightInv X
        = (1 - cHeight X) * halfC X * ((1 + cHeight X) * cHeightInv X) by ring]
    rw [hUnit_mul X, mul_one]

end Work.KT.Fund
