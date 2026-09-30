/-
Area AV: the scaled `𝔾_m`-action on `ℙ¹` — setup.

This file collects the elementary definitions used to build the scaling action
`ℙ¹ ⊗ 𝔾_m ⟶ ℙ¹`:
* `chartRing k i` is the ring of the chart `D₊(Xᵢ)` of `ℙ¹ = Proj k[X₀,X₁]`;
* `thetaRing k i` is the chart-level action `X_{other i}/Xᵢ ↦ (X_{other i}/Xᵢ) ⊗ T^{±1}`;
* `chartObjHom k i` is the open immersion of the chart into `ℙ¹`.
-/
import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.ProjectiveLine
import Submission.Work.AbVar.TestObjects
import Submission.Work.AbVar.ProjectiveLine.chart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MvPolynomial HomogeneousLocalization
open scoped MonoidalCategory TensorProduct

namespace Work.AbVar.P1Action

/-- The ring of the chart `D₊(Xᵢ)` of `ℙ¹`. -/
abbrev chartRing (k : Type*) [Field k] (i : Fin 2) : Type _ :=
  Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)

/-- The index different from `i`. -/
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

lemma other_ne (i : Fin 2) : other i ≠ i := by fin_cases i <;> decide

lemma eq_other {i j : Fin 2} (h : j ≠ i) : j = other i := by
  fin_cases i <;> fin_cases j <;> simp_all [other]

lemma other_zero : other 0 = 1 := rfl

lemma other_one : other 1 = 0 := rfl

/-- The exponent of `T` in the chart formula on `D₊(Xᵢ)`: `1` for `i = 1` (the coordinate
`X₀/X₁` is multiplied by `T`) and `-1` for `i = 0` (the coordinate `X₁/X₀` is divided by `T`). -/
def thetaExp : Fin 2 → ℤ := fun i => if i = 0 then -1 else 1

lemma thetaExp_zero : thetaExp 0 = -1 := rfl
lemma thetaExp_one : thetaExp 1 = 1 := rfl

/-- `p1BaseEquiv` agrees with `constToZero`. -/
lemma p1BaseEquiv_toRingHom_eq (k : Type*) [Field k] :
    (Work.AbVar.p1BaseEquiv k).toRingHom = Work.AbVar.ProjectiveLine.constToZero (R := k) := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  rfl

/-- The chart-level action: the ring endomorphism of the chart ring tensored with `k[T;T⁻¹]`
multiplying the chart coordinate by `T^{±1}`. -/
noncomputable def thetaRing (k : Type*) [Field k] (i : Fin 2) :
    chartRing k i →+* (chartRing k i ⊗[k] LaurentPolynomial k) :=
  (Polynomial.aeval
      (Work.AbVar.ProjectiveLine.awayU (R := k) i (other i) ⊗ₜ[k]
        LaurentPolynomial.T (thetaExp i))).toRingHom.comp
    (Work.AbVar.ProjectiveLine.awayToPoly (R := k) i)

/-- The chart coordinate `X_{other i}/Xᵢ` maps to itself times `T^{±1}`. -/
lemma thetaRing_awayU (k : Type*) [Field k] (i : Fin 2) :
    thetaRing k i (Work.AbVar.ProjectiveLine.awayU (R := k) i (other i))
      = Work.AbVar.ProjectiveLine.awayU (R := k) i (other i) ⊗ₜ[k]
          LaurentPolynomial.T (thetaExp i) := by
  rw [thetaRing, RingHom.comp_apply,
    ← Work.AbVar.ProjectiveLine.polyToAway_X (R := k) (i := i) (j := other i),
    Work.AbVar.ProjectiveLine.awayToPoly_awayU (R := k) (other_ne i)]
  exact Polynomial.aeval_X _

/-- `thetaRing` fixes the base `k`. -/
lemma thetaRing_algebraMap (k : Type*) [Field k] (i : Fin 2) (c : k) :
    thetaRing k i (algebraMap k (chartRing k i) c)
      = algebraMap k (chartRing k i ⊗[k] LaurentPolynomial k) c := by
  rw [thetaRing, RingHom.comp_apply, Work.AbVar.ProjectiveLine.awayToPoly_algMap]
  change (Polynomial.aeval
      (Work.AbVar.ProjectiveLine.awayU (R := k) i (other i) ⊗ₜ[k]
        LaurentPolynomial.T (thetaExp i))) (Polynomial.C c) = _
  rw [Polynomial.aeval_C]

/-- The chart `D₊(Xᵢ)` of `ℙ¹`, as an open immersion into `ℙ¹`. -/
def chartObjHom (k : Type*) [Field k] (i : Fin 2) :
    Spec (CommRingCat.of (chartRing k i)) ⟶ (Work.AbVar.P1 k).left :=
  Proj.awayι (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)
    (Work.AbVar.ProjectiveLine.X_mem_stdG i) (by norm_num)

lemma chartObjHom_eq_awayι (k : Type*) [Field k] (i : Fin 2) :
    chartObjHom k i = Proj.awayι (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)
      (Work.AbVar.ProjectiveLine.X_mem_stdG i) (by norm_num) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The structure map of the chart, composed with the structure map of `ℙ¹`, is the structure
map of the chart ring. -/
lemma chartObjHom_hom (k : Type*) [Field k] (i : Fin 2) :
    chartObjHom k i ≫ (Work.AbVar.P1 k).hom
      = Spec.map (CommRingCat.ofHom (algebraMap k (chartRing k i))) := by
  have h1 : chartObjHom k i ≫ Proj.toSpecZero (Work.AbVar.ProjectiveLine.StdG k)
      = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
          (Work.AbVar.ProjectiveLine.StdG k) (Submonoid.powers (MvPolynomial.X i)))) :=
    Proj.awayι_toSpecZero _ _ _ _
  have h2 : (HomogeneousLocalization.fromZeroRingHom (Work.AbVar.ProjectiveLine.StdG k)
        (Submonoid.powers (MvPolynomial.X i))).comp (Work.AbVar.p1BaseEquiv k).toRingHom
      = algebraMap k (chartRing k i) := by
    rw [p1BaseEquiv_toRingHom_eq]
    rfl
  calc chartObjHom k i ≫ (Work.AbVar.P1 k).hom
      = chartObjHom k i ≫ (Proj.toSpecZero (Work.AbVar.ProjectiveLine.StdG k)
          ≫ Spec.map (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom)) := by
        rw [Work.AbVar.p1_hom]
    _ = (chartObjHom k i ≫ Proj.toSpecZero (Work.AbVar.ProjectiveLine.StdG k))
          ≫ Spec.map (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom) :=
        (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
            (Work.AbVar.ProjectiveLine.StdG k) (Submonoid.powers (MvPolynomial.X i))))
          ≫ Spec.map (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom) := by
        rw [h1]
    _ = Spec.map (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom
            (Work.AbVar.ProjectiveLine.StdG k) (Submonoid.powers (MvPolynomial.X i))).comp
            (Work.AbVar.p1BaseEquiv k).toRingHom)) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    _ = Spec.map (CommRingCat.ofHom (algebraMap k (chartRing k i))) := by
        rw [h2]

end Work.AbVar.P1Action
