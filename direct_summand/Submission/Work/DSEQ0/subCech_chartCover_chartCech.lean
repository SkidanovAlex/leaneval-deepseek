import Mathlib
import Submission.Work.DSEQ0.ChartCompare
import Submission.Work.DSEQ0.ChartCover
import Submission.Work.DSCOH.chartCech_finite_vanishing
import Submission.Work.DSEQP.vanishing_ideal_chart
import Submission.Work.DSEQP.gf_bridge

namespace Work.DSEQ0

universe a

theorem subCech_chartCover_chartCech (A : Type a) [CommRing A] [IsNoetherianRing A] (N : ℕ)
    (X : AlgebraicGeometry.Scheme.{a}) (i : X ⟶ DSMap.PSpace A N)
    [AlgebraicGeometry.IsClosedImmersion i] :
    ∃ (M : Type a) (h1 : AddCommGroup M) (h2 : Module A M)
      (h3 : Module (MvPolynomial (Fin (N + 1)) A) M)
      (h4 : IsScalarTower A (MvPolynomial (Fin (N + 1)) A) M)
      (ℳ : ℕ → Submodule A M)
      (h5 : DirectSum.Decomposition ℳ)
      (h6 : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) ℳ)
      (h7 : Module.Finite (MvPolynomial (Fin (N + 1)) A) M),
      letI := h1; letI := h2; letI := h3; letI := h4; letI := h5; letI := h6; letI := h7
      ∀ q : ℕ, Nonempty ((SubCech (A := A) (X := X) (f := chartCoverToSpec A N i)
          (chartCover A N i)).homology q
        ≅ (Work.DSCOH.chartCech (A := A) (n := N + 1) (M := M) ℳ).homology q) := by sorry

end Work.DSEQ0
