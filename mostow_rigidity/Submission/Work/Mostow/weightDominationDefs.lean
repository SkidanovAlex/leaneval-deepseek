import Mathlib

/-!
# Shared definitions for `Work.Mostow.weightDomination`

`blkProj e i v` is the projection of `v` onto the `i`-th "block"
`span {e (i,0), e (i,1)}` of the orthonormal basis `e : Fin r × Fin 2 → E (2 * r)`.
-/

open scoped BigOperators

namespace Work.Mostow

noncomputable section

/-- The projection of `v` onto the `i`-th block of the orthonormal basis `e`. -/
def blkProj {r : ℕ} (e : OrthonormalBasis (Fin r × Fin 2) ℝ (EuclideanSpace ℝ (Fin (2 * r))))
    (i : Fin r) (v : EuclideanSpace ℝ (Fin (2 * r))) : EuclideanSpace ℝ (Fin (2 * r)) :=
  (inner ℝ (e (i, Fin.castSucc 0)) v) • e (i, Fin.castSucc 0) +
    (inner ℝ (e (i, 1)) v) • e (i, 1)

end

end Work.Mostow
