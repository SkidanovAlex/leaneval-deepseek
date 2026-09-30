/-
Area AV: `P¹` is smooth over its base field.
-/
import Mathlib
import Submission.Work.AbVar.P1Chart.Basic
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


open AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CategoryTheory

noncomputable section

universe u

namespace Work.AbVar.P1Chart

section Chart

variable {R : Type*} [CommRing R]

/-- The chart ring `Away 𝒜 (X_i)` is smooth over `R`: it is a polynomial ring in `X_j/X_i`. -/
theorem smooth_awayAlg {i j : Fin 2} (hij : j ≠ i) :
    RingHom.Smooth (ProjectiveLine.awayAlg (R := R) i) := by
  have hbij : Function.Bijective (ProjectiveLine.polyToAway (R := R) i j) :=
    ⟨ProjectiveLine.polyToAway_injective hij, ProjectiveLine.awaySurjective hij⟩
  let e : Polynomial R ≃ₐ[R] Away (ProjectiveLine.StdG R) (MvPolynomial.X i) :=
    AlgEquiv.ofBijective _ hbij
  have h1 : Algebra.IsStandardSmooth R (Polynomial R) :=
    Algebra.IsStandardSmooth.of_algEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1))
  have h2 : Algebra.IsStandardSmooth R (Away (ProjectiveLine.StdG R) (MvPolynomial.X i)) :=
    Algebra.IsStandardSmooth.of_algEquiv e
  have h3 : (algebraMap R (Away (ProjectiveLine.StdG R) (MvPolynomial.X i))).IsStandardSmooth :=
    RingHom.isStandardSmooth_algebraMap.mpr h2
  have h4 : (ProjectiveLine.awayAlg (R := R) i).IsStandardSmooth := by
    rwa [ProjectiveLine.algebraMap_awayAlg] at h3
  exact h4.smooth

/-- The chart ring structure map `↧(𝒜 0) ⟶ Away 𝒜 (X_i)` is smooth. -/
theorem smooth_fromZero {i j : Fin 2} (hij : j ≠ i) :
    RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom (ProjectiveLine.StdG R)
      (Submonoid.powers (MvPolynomial.X i : ProjectiveLine.Poly2 R))) := by
  have h := smooth_awayAlg (R := R) hij
  have h' := (RingHom.Smooth.respectsIso).2 (ProjectiveLine.awayAlg (R := R) i)
    (ProjectiveLine.constToZeroEquiv (R := R)).symm h
  have heq : (ProjectiveLine.awayAlg (R := R) i).comp
        (ProjectiveLine.constToZeroEquiv (R := R)).symm.toRingHom
      = HomogeneousLocalization.fromZeroRingHom (ProjectiveLine.StdG R)
          (Submonoid.powers (MvPolynomial.X i)) := by
    apply RingHom.ext
    intro a
    have hsymm : (ProjectiveLine.constToZero (R := R))
        ((ProjectiveLine.constToZeroEquiv (R := R)).symm a) = a := by
      have h0 := RingEquiv.apply_symm_apply (ProjectiveLine.constToZeroEquiv (R := R)) a
      rwa [ProjectiveLine.constToZeroEquiv_apply] at h0
    show HomogeneousLocalization.fromZeroRingHom (ProjectiveLine.StdG R)
      (Submonoid.powers (MvPolynomial.X i))
      ((ProjectiveLine.constToZero (R := R))
        ((ProjectiveLine.constToZeroEquiv (R := R)).symm a)) = _
    rw [hsymm]
  rwa [heq] at h'

/-- Every standard chart of `Proj R[X₀,X₁]` is smooth over `Spec ↧(𝒜 0)`. -/
theorem smooth_fromZeroRingHom (i : Fin 2) :
    RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom (ProjectiveLine.StdG R)
      (Submonoid.powers (MvPolynomial.X i : ProjectiveLine.Poly2 R))) :=
  smooth_fromZero (other_ne i)

end Chart

/-- The projective line over a field is smooth over the field. -/
theorem smooth {k : Type u} [Field k] :
    AlgebraicGeometry.Smooth (Work.AbVar.P1 k).hom := by
  have hchart : ∀ i : Fin 2, RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))) :=
    fun i => smooth_fromZeroRingHom (R := k) i
  have h1 : Smooth (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)) :=
    ProjectiveLine.smoothToSpecZero k hchart
  have h2 : Smooth (Spec.map (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom)) := by
    have hhom : (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom).hom.Smooth :=
      (RingHom.IsStandardSmoothOfRelativeDimension.equiv (Work.AbVar.p1BaseEquiv k)
        ).isStandardSmooth.smooth
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr hhom
  rw [Work.AbVar.p1_hom k]
  exact MorphismProperty.comp_mem _ _ _ h1 h2

end Work.AbVar.P1Chart
