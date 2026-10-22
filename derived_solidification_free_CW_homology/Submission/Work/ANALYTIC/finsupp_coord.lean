import Mathlib
import Submission.Work.ANALYTIC.BoundedSeqC
import Submission.Work.ATOM.Defs

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint

namespace Work.ANALYTIC

open _root_.LightCondensed
open Opposite

/-- A map `u : ∗ ⟶ S` out of the one-point light profinite set is the constant map at the point
`u s`, for any point `s` of `∗`.  (The point `∗` has a unique point, so `u` is determined by its
value there.) -/
lemma ptAt_eq_of_apply {S : LightProfinite.{0}} (u : Work.ATOM.pt ⟶ S)
    (s : ↥Work.ATOM.pt.toTop) : u = Work.ATOM.ptAt (u s) := by
  apply ConcreteCategory.hom_ext
  intro x
  rw [Work.ATOM.ptAt_apply]

/-- The `m`-th coordinate at a point of a finite combination of the elements
`boundedSeq.map u.op deltaElem` (`u : ∗ ⟶ ℕ∪{∞}`) of `∏^bnd ℤ(∗)` is the coefficient of `u = ptAt m`.

Here `boundedSeq = ∏^bnd ℤ` is the sheaf of uniformly bounded families of continuous `ℤ`-valued
functions (`Work.ANALYTIC.boundedSeq_obj_obj`), `deltaElem` is the element `n ↦ δ_n` of
`boundedSeq(ℕ∪{∞})`, and `(boundedSeq.map u.op deltaElem).1 m s = deltaFun m (u ())`.

Route: the `m`-th coordinate is `ℤ`-linear, so the `Finsupp.sum` computes to
`∑_u c u • deltaFun m (u ())`; the only `u : ∗ ⟶ ℕ∪{∞}` with `u () = ↑m` is `ptAt (↑m)`, and all
other terms vanish. -/
theorem finsupp_coord (c : (Work.ATOM.pt ⟶ LightProfinite.NatUnionInfty) →₀ ℤ) (m : ℕ)
    (s : ↥Work.ATOM.pt.toTop) :
    (c.sum (fun u n => n • Work.ANALYTIC.boundedSeq.obj.map u.op Work.ANALYTIC.deltaElem)).1 m s
      = c (Work.ATOM.ptAt (OnePoint.some m)) := by
  classical
  have step1 : (c.sum (fun u n =>
        n • Work.ANALYTIC.boundedSeq.obj.map u.op Work.ANALYTIC.deltaElem)).1 m s
      = ∑ u ∈ c.support, c u * Work.ANALYTIC.deltaFun m (u s) := by
    let ev : ↥(Work.ANALYTIC.boundedSeq.obj.obj (Opposite.op Work.ATOM.pt)) →+ ℤ :=
      { toFun := fun x => x.1 m s, map_zero' := rfl, map_add' := fun _ _ => rfl }
    change ev (c.sum (fun u n =>
      n • Work.ANALYTIC.boundedSeq.obj.map u.op Work.ANALYTIC.deltaElem)) = _
    simp only [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_zsmul, smul_eq_mul]
    rfl
  rw [step1]
  have hterm : ∀ u : Work.ATOM.pt ⟶ LightProfinite.NatUnionInfty,
      c u * Work.ANALYTIC.deltaFun m (u s)
        = if u = Work.ATOM.ptAt (OnePoint.some m) then c u else 0 := by
    intro u
    by_cases hu : u = Work.ATOM.ptAt (OnePoint.some m)
    · rw [if_pos hu, hu, Work.ATOM.ptAt_apply, Work.ANALYTIC.deltaFun_at, mul_one]
    · rw [if_neg hu]
      have hne : u s ≠ OnePoint.some m := by
        intro h
        have h2 := ptAt_eq_of_apply u s
        rw [h] at h2
        exact hu h2
      rw [Work.ANALYTIC.deltaFun_eq, if_neg hne, mul_zero]
  rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_ite_eq']
  by_cases hb : Work.ATOM.ptAt (OnePoint.some m) ∈ c.support
  · rw [if_pos hb]
  · rw [if_neg hb]
    have h0 : c (Work.ATOM.ptAt (OnePoint.some m)) = 0 := by simpa using hb
    rw [h0]

end Work.ANALYTIC

/-- The statement of `Work.ANALYTIC.Work.ANALYTIC.finsupp_coord` under the name
`Work.ANALYTIC.finsupp_coord`, which is the name derived from the module path
`Submission.Work.ANALYTIC.finsupp_coord`. -/
theorem finsupp_coord (c : (Work.ATOM.pt ⟶ LightProfinite.NatUnionInfty) →₀ ℤ) (m : ℕ)
    (s : ↥Work.ATOM.pt.toTop) :
    (c.sum (fun u n => n • Work.ANALYTIC.boundedSeq.obj.map u.op Work.ANALYTIC.deltaElem)).1 m s
      = c (Work.ATOM.ptAt (OnePoint.some m)) :=
  _root_.Work.ANALYTIC.Work.ANALYTIC.finsupp_coord c m s

end Work.ANALYTIC
