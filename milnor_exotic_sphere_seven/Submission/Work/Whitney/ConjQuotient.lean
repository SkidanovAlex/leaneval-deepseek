import Mathlib
import Submission.Work.Whitney.ConjDefs
import Submission.Work.Thom.QuotientLin

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Conjugation commutes with the linear algebra of the tautological quotient

The tautological quotient `Q = π^*V/ℂ·s` of a complex bundle over its punctured total space is
trivialised by the map `Work.Thom.quoFun k w` of `Submission/Work/Thom/QuotientLin.lean`, with the
filling `Work.Thom.fillFun k` as its section.  For the **conjugate** bundle `V̄`
(`Work.Whitney.conjCore`) the tautological section is the conjugate of that of `V`, so the
trivialisation data of `Q_V̄` are the conjugates of those of `Q_V`:

* `Work.Whitney.conjC_fillFun` — conjugation commutes with the filling `fillFun`;
* `Work.Whitney.conjC_dropFun` — and with the coordinate-dropping `dropFun`;
* `Work.Whitney.conjC_quoFun` — **and with `quoFun`**, i.e. the tautological quotient of a conjugate
  bundle is the conjugate of the tautological quotient.

These are the pointwise identities behind the isomorphism
`bundleComap (tautQuotient (conjCore Z)) (conjPunct Z) ≅ conjCore (tautQuotient Z)`, which is the
geometric input of the sign theorem `c_j(V̄) = (-1)^j c_j(V)`.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {n : ℕ}

/-- The standard basis vectors have real coordinates, hence are fixed by conjugation. -/
theorem conjC_basisVec (k : Fin n) : conjC n (basisVec k) = basisVec k := by
  ext i
  rw [conjC_coord]
  by_cases h : i = k <;> simp [basisVec, h]

/-- The coordinate form of `Work.Whitney.conjC_coord` in terms of `WithLp.ofLp`. -/
theorem conjC_ofLp (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    (conjC n v).ofLp i = star (v.ofLp i) := conjC_coord n v i

/-- **Conjugation commutes with `Work.Thom.fillFun`.** -/
theorem conjC_fillFun (k : Fin (n + 1)) (z : EuclideanSpace ℂ (Fin n)) :
    conjC (n + 1) (fillFun k z) = fillFun k (conjC n z) := by
  have h : conjC (n + 1) (∑ m : Fin n, z.ofLp m • basisVec (k.succAbove m))
      = ∑ m : Fin n, (conjC n z).ofLp m • basisVec (k.succAbove m) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [conjC_smul, conjC_basisVec, conjC_ofLp]
  simpa only [fillFun] using h

/-- **Conjugation commutes with `Work.Thom.dropFun`.** -/
theorem conjC_dropFun (k : Fin (n + 1)) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    conjC n (dropFun k u) = dropFun k (conjC (n + 1) u) := by
  ext m
  rw [conjC_coord, dropFun_apply, dropFun_apply, conjC_coord]

/-- **Conjugation commutes with `Work.Thom.quoFun`**: the quotient projection along the conjugate of
`w` of the conjugate of `u` is the conjugate of the quotient projection of `u` along `w`. -/
theorem conjC_quoFun (k : Fin (n + 1)) (w u : EuclideanSpace ℂ (Fin (n + 1))) :
    conjC n (quoFun k w u) = quoFun k (conjC (n + 1) w) (conjC (n + 1) u) := by
  ext m
  rw [conjC_coord, quoFun_apply, quoFun_apply, conjC_coord, conjC_coord, conjC_coord, conjC_coord]
  rw [star_sub, StarMul.star_mul, star_div₀]
  ring

end

end Work.Whitney
