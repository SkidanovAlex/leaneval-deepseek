import Mathlib
import Submission.Work.MotV.Machinery
import Submission.Work.MotC2.AffPlace
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

variable {N : Type*} [Field N]

/-- The affine place of a nonsingular point `(c,d)` lies in `ptsOf` as soon as `c` is a root of
the norm of a nonzero element `a` of the coordinate ring: `ptsOf E hInf (norm a)` is
`{point at infinity} ∪ ⋃_{c root of norm a} (places above x = c)`.

Pure bookkeeping about `Work.MotV.ptsOf`, `Work.MotV.fibrePlaces`, `Work.MotV.quad`.

Route. `Work.MotV.ptsOf E hInf p = insert ⟨MotC2.infPlace E, hInf⟩
(p.roots.toFinset.biUnion (fibrePlaces E))`. With `p := Algebra.norm (Polynomial N) a`, get
`c ∈ p.roots.toFinset` from `hc` and `p ≠ 0`: `Multiset.mem_toFinset.mpr
((Polynomial.mem_roots hne).mpr hc)`, where `hne` comes from `ha` via `Algebra.norm_ne_zero_iff.mpr
ha` (supply `Module.Finite (Polynomial N) (CoordinateRing E)` locally as
`Module.Finite.of_basis (CoordinateRing.basis E)`; `Module.Free` and `IsDomain` are instances).
`Finset.mem_biUnion` reduces the goal to
`⟨MotC2.affPlaceAt E c d, hplace⟩ ∈ Work.MotV.fibrePlaces E c`. Unwinding `fibrePlaces` (a
`Finset.biUnion` over `(Work.MotV.quad E c).roots.toFinset`, the `d'`-th fibre being
`{⟨MotC2.affPlaceAt E c d', (MotC2.AffPlace N E c d' hns).1⟩}` when `Equation E c d'` holds and
`∅` otherwise), this needs `d ∈ (quad E c).roots.toFinset` — from `Equation E c d`
(`(WeierstrassCurve.Affine.equation_iff_nonsingular).mpr h`), unfolding `Work.MotV.quad` to
`X^2 + C (a₁*c+a₃)*X - C (c^3+a₂c^2+a₄c+a₆)` and using `Polynomial.mem_roots` plus `quad E c ≠ 0`
(it is monic of degree two) — and the equality of the two `Work.MotV.Place` elements, which is
`Subtype.ext rfl` by proof irrelevance. (statement `theorem`: `Work.MotV.memPtsOfAffPlace`) -/
theorem memPtsOfAffPlace {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (a : WeierstrassCurve.Affine.CoordinateRing E) (ha : a ≠ 0)
    (hInf : Work.MotC2.IsRatPlace E (Work.MotC2.infPlace E))
    (c d : N) (h : WeierstrassCurve.Affine.Nonsingular E c d)
    (hplace : Work.MotC2.IsRatPlace E (Work.MotC2.affPlaceAt E c d))
    (hc : (Algebra.norm (Polynomial N) a).IsRoot c) :
    (⟨Work.MotC2.affPlaceAt E c d, hplace⟩ : Work.MotV.Place N E) ∈
      Work.MotV.ptsOf E hInf (Algebra.norm (Polynomial N) a) := by
  classical
  -- The norm of a nonzero element of the (finite free) coordinate ring is nonzero.
  have hne : Algebra.norm (Polynomial N) a ≠ 0 := by
    have hfin : Module.Finite (Polynomial N) (CoordinateRing E) :=
      Module.Finite.of_basis (CoordinateRing.basis E)
    exact Algebra.norm_ne_zero_iff.mpr ha
  have hcmem : c ∈ (Algebra.norm (Polynomial N) a).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr hc)
  -- The equation `W(c,d) = 0` holds at the nonsingular point.
  have hEq : Equation E c d := (equation_iff_nonsingular (W := E)).mpr h
  -- `quad E c` is monic of degree two, hence nonzero.
  have hqne : quad E c ≠ 0 := by
    have hdeg : (Polynomial.C (E.a₁ * c + E.a₃) * Polynomial.X -
        Polynomial.C (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆)).degree <
        (2 : WithBot ℕ) := by
      rw [sub_eq_add_neg, ← Polynomial.C_neg]
      refine lt_of_le_of_lt Polynomial.degree_linear_le ?_
      norm_num
    have hmonic : (quad E c).Monic := by
      rw [quad, add_sub_assoc]
      exact Polynomial.monic_X_pow_add hdeg
    exact hmonic.ne_zero
  -- `d` is a root of `quad E c`.
  have hev : (quad E c).eval d = d ^ 2 + (E.a₁ * c + E.a₃) * d -
      (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆) := by
    simp only [quad, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  have hd_eval : (quad E c).eval d = 0 := by
    rw [hev]
    rw [equation_iff] at hEq
    linear_combination (norm := first | refl_ring1 | ring1) hEq
  have hdroot : d ∈ (quad E c).roots :=
    (Polynomial.mem_roots hqne).mpr (Polynomial.IsRoot.def.mpr hd_eval)
  rw [ptsOf, Finset.mem_insert]
  right
  rw [Finset.mem_biUnion]
  refine ⟨c, hcmem, ?_⟩
  rw [fibrePlaces]
  simp only [Finset.mem_biUnion, Multiset.mem_toFinset]
  exact ⟨d, hdroot, by
    rw [dite_eq_left hEq, Finset.mem_singleton]⟩

end Work.MotV
