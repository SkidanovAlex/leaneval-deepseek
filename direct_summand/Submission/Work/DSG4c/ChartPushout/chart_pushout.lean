import Mathlib
import Submission.Work.DSG4c.Basic
import Submission.Work.DSG4c.ChartPushout.Assembly
import Submission.Work.DSG4c.ChartPushout.chartToPoly_surjective
import Submission.Work.DSG4c.ChartPushout.chartToPolyT_surjective
import Submission.Work.DSG4c.ChartPushout.chartToPolyT_comp_map

namespace Work.DSG4c.ChartPushout

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry Limits MvPolynomial
universe u
/-- Base change of the `i`-th standard chart of `ℙᴺ`: the canonical square with corners
`A`, `A'`, `Away (PGr A N) (X i)` and `Away (PGr A' N) (coeffExt ψ (X i))` is a pushout.
Suggested route: identify `Away (MvPolynomial.homogeneousSubmodule σ A) (X i)` with the
quotient `A[x] ⧸ Ideal.span {X i - 1}` (dehomogenization, `X j ↦ X j / X i`), and use that
base change of a quotient of a polynomial ring is the quotient of the base-changed polynomial
ring (`Algebra.TensorProduct.tensorQuotientEquiv` together with `MvPolynomial`-tensor-product
identifications). -/
theorem chart_pushout (A A' : Type u) [CommRing A] [CommRing A'] (ψ : A →+* A') (N : ℕ)
    (i : Fin (N+1)) :
    IsPushout (CommRingCat.ofHom ψ) (CommRingCat.ofHom (Work.DSG4c.chartMap A N i))
      (CommRingCat.ofHom (Work.DSG4c.chartMapT A A' ψ N i))
      (CommRingCat.ofHom (Work.DSG4c.awayMapChart A A' ψ N i)) := by
  have hinj : Function.Injective (chartToPoly A N i) := fun x y h => by
    rw [← polyToChart_chartToPoly A N i x, h, polyToChart_chartToPoly A N i y]
  have hinjT : Function.Injective (chartToPolyT A A' ψ N i) := fun x y h => by
    rw [← polyToChartT_chartToPoly A A' ψ N i x, h, polyToChartT_chartToPoly A A' ψ N i y]
  refine (isPushout_poly A A' ψ N i).of_iso (Iso.refl (CommRingCat.of A))
    (Iso.refl (CommRingCat.of A'))
    (RingEquiv.toCommRingCatIso
      (RingEquiv.ofBijective (chartToPoly A N i) ⟨hinj, chartToPoly_surjective A N i⟩))
    (RingEquiv.toCommRingCatIso
      (RingEquiv.ofBijective (chartToPolyT A A' ψ N i)
        ⟨hinjT, chartToPolyT_surjective A A' ψ N i⟩))
    ?_ ?_ ?_ ?_
  · simp
  · rw [RingEquiv.toCommRingCatIso_hom, ← CommRingCat.ofHom_comp]
    congr 1
    exact RingHom.ext (fun a => chartToPoly_C A N i a)
  · rw [RingEquiv.toCommRingCatIso_hom, ← CommRingCat.ofHom_comp]
    congr 1
    exact RingHom.ext (fun a => chartToPolyT_C A A' ψ N i a)
  · rw [RingEquiv.toCommRingCatIso_hom, RingEquiv.toCommRingCatIso_hom, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (chartToPolyT_comp_map A A' ψ N i)

end Work.DSG4c.ChartPushout
