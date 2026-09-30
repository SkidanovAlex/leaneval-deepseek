/-
Area AV: the projective line is smooth over a field.

`Work.AbVar.P1 k` is `Proj` of `k[X₀,X₁]` with the standard grading, and the chart `D₊(X_i)` of this
Proj has coordinate ring `Away 𝒜 (X i)`, which is a polynomial ring over `k` in the coordinate
`X_j/X_i` (`j ≠ i`), see `Submission/Work/AbVar/ProjectiveLine/chart.lean`.  Hence each chart is
smooth, so `P1 k ⟶ Spec k` is smooth (`Work.AbVar.ProjectiveLine.smoothToSpecZero`).
-/
import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.ProjectiveLine
import Submission.Work.AbVar.ProjectiveLine.chart
import Submission.Work.AbVar.ProjectiveLine.awaySurjective
import Submission.Work.AbVar.ProjectiveLine.smoothToSpecZero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.AbVar.ProjectiveLine

open AlgebraicGeometry MvPolynomial HomogeneousLocalization

section Chart

variable {R : Type*} [CommRing R]

/-- `1 - i` on `Fin 2`. -/
def otherIdx (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

lemma otherIdx_ne (i : Fin 2) : otherIdx i ≠ i := by fin_cases i <;> decide

/-- The chart ring `Away 𝒜 (X_i)` is smooth over `R`: it is a polynomial ring in `X_j/X_i`. -/
theorem smooth_awayAlg {i j : Fin 2} (hij : j ≠ i) :
    RingHom.Smooth (awayAlg (R := R) i) := by
  have hbij : Function.Bijective (polyToAway (R := R) i j) :=
    ⟨polyToAway_injective hij, awaySurjective hij⟩
  let e : Polynomial R ≃ₐ[R] Away (StdG R) (MvPolynomial.X i) := AlgEquiv.ofBijective _ hbij
  have h1 : Algebra.IsStandardSmooth R (Polynomial R) :=
    Algebra.IsStandardSmooth.of_algEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1))
  have h2 : Algebra.IsStandardSmooth R (Away (StdG R) (MvPolynomial.X i)) :=
    Algebra.IsStandardSmooth.of_algEquiv e
  have h3 : (algebraMap R (Away (StdG R) (MvPolynomial.X i))).IsStandardSmooth :=
    RingHom.isStandardSmooth_algebraMap.mpr h2
  have h4 : (awayAlg (R := R) i).IsStandardSmooth := by rwa [algebraMap_awayAlg] at h3
  exact h4.smooth

/-- The chart ring structure map `↧(𝒜 0) ⟶ Away 𝒜 (X_i)` is smooth. -/
theorem smooth_fromZero {i j : Fin 2} (hij : j ≠ i) :
    RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom (StdG R)
      (Submonoid.powers (MvPolynomial.X i : Poly2 R))) := by
  have h := smooth_awayAlg (R := R) hij
  have h' := (RingHom.Smooth.respectsIso).2 (awayAlg (R := R) i)
    (constToZeroEquiv (R := R)).symm h
  have heq : (awayAlg (R := R) i).comp (constToZeroEquiv (R := R)).symm.toRingHom
      = HomogeneousLocalization.fromZeroRingHom (StdG R) (Submonoid.powers (MvPolynomial.X i)) := by
    apply RingHom.ext
    intro a
    have hsymm : (constToZero (R := R)) ((constToZeroEquiv (R := R)).symm a) = a := by
      have h0 := RingEquiv.apply_symm_apply (constToZeroEquiv (R := R)) a
      rwa [constToZeroEquiv_apply] at h0
    show HomogeneousLocalization.fromZeroRingHom (StdG R) (Submonoid.powers (MvPolynomial.X i))
      ((constToZero (R := R)) ((constToZeroEquiv (R := R)).symm a)) = _
    rw [hsymm]
  rwa [heq] at h'

/-- Every standard chart of `Proj R[X₀,X₁]` is smooth over `Spec ↧(𝒜 0)`. -/
theorem smooth_fromZeroRingHom (i : Fin 2) :
    RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom (StdG R)
      (Submonoid.powers (MvPolynomial.X i : Poly2 R))) :=
  smooth_fromZero (otherIdx_ne i)

end Chart

open CategoryTheory in
theorem smooth {k : Type*} [Field k] : AlgebraicGeometry.Smooth (Work.AbVar.P1 k).hom := by
  have hchart : ∀ i : Fin 2, RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (Submonoid.powers (MvPolynomial.X i : Poly2 k))) :=
    fun i => smooth_fromZeroRingHom (R := k) i
  have h1 : Smooth (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)) :=
    smoothToSpecZero k hchart
  have h2 : Smooth (Spec.map (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom)) := by
    have hhom : (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom).hom.Smooth :=
      (RingHom.IsStandardSmoothOfRelativeDimension.equiv (Work.AbVar.p1BaseEquiv k)
        ).isStandardSmooth.smooth
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr hhom
  rw [Work.AbVar.p1_hom k]
  exact MorphismProperty.comp_mem _ _ _ h1 h2

end Work.AbVar.ProjectiveLine
