import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SpecLin.Points.ptDiv_complete
import Submission.Work.SymQuot.DivBaseInst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

/-! ## Splitting an effective divisor over an algebraically closed field

Let `C` be a curve over a field `K` and let `L` be an algebraically closed extension of `K`.
An effective divisor `E` on `C_L` of degree `n` is a sum of `n` point divisors `[y m]` of
`L`-points `y m` of `C`: over an algebraically closed field every place of `C_L` has residue
degree one, hence is a point divisor (`Work.SpecLin.Points.ptDiv_complete`), and removing one
such point divisor lowers the degree by one.

The lemmas below are the elementary facts behind this: over an algebraically closed field all
places have residue degree one, and the degree of `Div.single Q 1` is that residue degree. -/

/-- **Over an algebraically closed field every place of a curve has residue degree one.**

The residue degree of a place `Q` is the `L`-dimension of its residue field
(`Work.CurveBasics.Place.degree_eq_finrank`), which is positive
(`Work.CurveBasics.Place.residueDegree_pos`), hence finite; a finite extension of an
algebraically closed field is trivial, so the dimension is one. -/
theorem residueDegree_eq_one_of_isAlgClosed {L : Type u} [Field L] [IsAlgClosed L]
    (C : Work.CurveBasics.Curve L) (Q : C.Place) :
    C.hom.residueDegree Q.point = 1 := by
  have hdeg := Work.CurveBasics.Place.degree_eq_finrank (C := C) Q
  have hpos := Work.CurveBasics.Place.residueDegree_pos (C := C) Q
  have hfinrank_pos : 0 < Module.finrank L (C.left.residueField Q.point) := by
    rw [← hdeg]; exact hpos
  have hfd : FiniteDimensional L (C.left.residueField Q.point) :=
    FiniteDimensional.of_finrank_pos hfinrank_pos
  haveI : Algebra.IsIntegral L (C.left.residueField Q.point) :=
    Algebra.IsIntegral.of_finite L _
  have hbij : Function.Bijective (algebraMap L (C.left.residueField Q.point)) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral _
      (fun x => Algebra.IsIntegral.isIntegral x)
  have h1 : Module.finrank L (C.left.residueField Q.point) = 1 := by
    have hle : L ≃ₗ[L] (C.left.residueField Q.point) :=
      LinearEquiv.ofBijective (Algebra.linearMap L _) hbij
    have h2 := LinearEquiv.finrank_eq hle
    rw [Module.finrank_self] at h2
    exact h2.symm
  show Q.degree = 1
  rw [hdeg, h1]

/-- **Splitting of an effective divisor on `C_L` over an algebraically closed `L`.**

An effective divisor `E` on `C_L` of degree `n` is the sum of the point divisors of `n`
`L`-points of `C`.  Induction on `n`: for `n = 0` effectivity forces `E = 0`; for `n + 1 > 0`
pick a place `Q` in the support of `E`; over the algebraically closed `L` the divisor
`Div.single Q 1` is effective of degree one, so it is `[p]` for an `L`-point `p`
(`Work.SpecLin.Points.ptDiv_complete`); `E - [p]` is effective of degree `n`, and the
induction hypothesis plus `Fin.cons` finish. -/
theorem exists_ptDiv_sum_of_effective {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {L : Type u} [Field L] [Algebra K L] [IsAlgClosed L] (n : ℕ)
    (E : Work.SpecLin.Dv C L) (hE : E.IsEffective)
    (hdeg : (C.baseChange L).deg E = (n : ℤ)) :
    ∃ y : Fin n → Work.SpecLin.CurveFPt C L, E = ∑ m, Work.SpecLin.ptDiv (y m) := by
  induction n generalizing E with
  | zero =>
      have h0 : (C.baseChange L).deg E = 0 := by rw [hdeg]; norm_num
      have hE0 : E = 0 :=
        (Work.CurveBasics.Divisor.deg_eq_zero_iff (C := C.baseChange L) hE).mp h0
      exact ⟨Fin.elim0, by rw [hE0]; simp⟩
  | succ n ih =>
      have hne : E ≠ 0 := by
        intro h0
        rw [h0, Work.CurveBasics.Curve.deg_zero] at hdeg
        exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) hdeg.symm
      obtain ⟨Q, hQmem⟩ := Finsupp.support_nonempty_iff.mpr hne
      have hQpos : 1 ≤ E Q := by
        have h1 : 0 ≤ E Q := hE Q
        have h2 : E Q ≠ 0 := Finsupp.mem_support_iff.mp hQmem
        omega
      have hresdeg : (C.baseChange L).hom.residueDegree Q.point = 1 :=
        residueDegree_eq_one_of_isAlgClosed (C.baseChange L) Q
      have hsingle_eff : (Work.CurveBasics.Curve.Div.single Q 1).IsEffective := by
        intro W
        rw [Work.CurveBasics.Curve.Div.single, Finsupp.single_apply]
        split_ifs with h
        · norm_num
        · norm_num
      have hdeg_single : (C.baseChange L).deg (Work.CurveBasics.Curve.Div.single Q 1) = 1 := by
        rw [Work.CurveBasics.Curve.deg_single, hresdeg]; norm_num
      obtain ⟨p, hp⟩ := Work.SpecLin.Points.ptDiv_complete (C := C) (F := L)
        (Work.CurveBasics.Curve.Div.single Q 1) hsingle_eff hdeg_single
      have hle : Work.CurveBasics.Curve.Div.le (Work.SpecLin.ptDiv p) E := by
        rw [Work.CurveBasics.Curve.Div.le_iff]
        intro W
        rw [hp, Work.CurveBasics.Curve.Div.single, Finsupp.single_apply]
        split_ifs with h
        · rw [← h]; exact hQpos
        · exact hE W
      have hLeff : (E - Work.SpecLin.ptDiv p).IsEffective := hle
      have hdeg' : (C.baseChange L).deg (E - Work.SpecLin.ptDiv p) = (n : ℤ) := by
        rw [Work.CurveBasics.Curve.deg_sub, hdeg, hp, hdeg_single]
        push_cast; ring
      obtain ⟨y', hy'⟩ := ih (E - Work.SpecLin.ptDiv p) hLeff hdeg'
      refine ⟨Fin.cons p y', ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hy']
      abel

open CategoryTheory Limits AlgebraicGeometry in
theorem exists_ptDiv_sum_of_div {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] {L : Type u} [Field L] [Algebra K L] [Algebra F L]
    [IsScalarTower K F L] [IsAlgClosed L] (D : Work.SpecLin.Dv C F) (hD : D.IsEffective)
    {n : ℕ} (hdeg : (C.baseChange F).deg D = n) :
    ∃ y : Fin n → Work.SpecLin.CurveFPt C L,
      Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F L) D = ∑ m, Work.SpecLin.ptDiv (y m) := by
  obtain ⟨y, hy⟩ := exists_ptDiv_sum_of_effective (K := K) (C := C) (L := L) n
    (Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F L) D)
    (Work.SpecLin.DivBase.isEffective_bc _ hD)
    (by rw [Work.SpecLin.DivBase.deg_bc, hdeg])
  exact ⟨y, hy⟩

end Work.SymQuot.DivOf.Complete
