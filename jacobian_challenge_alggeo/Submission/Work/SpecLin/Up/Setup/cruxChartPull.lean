/-
# Namespace mirror of `Work.SpecLin.Setup.cruxChartPull`

This file is an exact copy of `Submission/Work/SpecLin/Setup/cruxChartPull.lean` (module `Work.SpecLin.Setup.cruxChartPull`), changed in exactly three ways:

* a `namespace Up` / `end Up` pair is inserted immediately inside the file's own namespace, so
  that every declaration `Work.SpecLin.<Area>.<x>` of the original appears here as
  `Work.SpecLin.<Area>.Up.<x>` (this avoids a name clash with the original, which cannot be
  removed: the original is part of the shared library);
* references to declarations *of the mirrored modules* are rewritten accordingly (full and
  area-relative forms), and imports of those modules point at their mirrors;
* an import of `Core/linEquiv_of_sections_of_chart.lean` (the module that *states* the
  affine-chart theorem) is replaced by an import of the upstream vocabulary module
  `Core/chartVocab.lean`, which declares the same chart algebra under the same names.

The point of the mirror is to break the import cycle
`vocabulary -> statement -> ... -> proof modules -> vocabulary`: the proof modules used to take
their vocabulary from the module that states the theorem, and this made a proof of that theorem
unreachable.  The mathematics is unchanged: the mirror is a verbatim copy of verified code.

The statements of the mirrored theorems mention only names that are *upstream* of the mirror, so
`Work.SpecLin.Core.Up.chartSpecialisation` (module
`Submission.Work.SpecLin.Up.Core.chartSpecialisation`) has literally the statement of
`Work.SpecLin.Core.linEquiv_of_sections_of_chart`, which is proved from it.
-/
import Mathlib
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Core.chartVocab
import Submission.Work.SpecLin.Up.Alt.chartMap
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.BaseChange.krullDim_le_one
import Submission.Work.SpecLin.Setup.smoothSections
import Submission.Work.SpecLin.Setup.hartogsRelativeCurve
import Submission.Work.SpecLin.Alt.not_isField_chartSections

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.SpecLin.Setup
namespace Up

open CategoryTheory AlgebraicGeometry

universe u

/-- **The abstract crux, assembled from the Hartogs/`S2` half.**

This is the statement of `Work.SpecLin.Setup.cruxPITdomain` (the same crux in the abstract
language `B = A ⊗[K] R`), but assembled directly from the single "regularity" statement
`Work.SpecLin.Setup.hartogsRelativeCurve`, applied to `u` and to `u⁻¹`.  Stating it here keeps
`cruxChartPull` down to one commutative-algebra input, the Hartogs/`S2` statement for the
relative curve (the principal ideal statement `Work.SpecLin.Setup.exists_height_one_prime` is
*not* needed for the unit step). -/
theorem cruxAux {K : Type u} [Field K] (A : Type u) [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] [Algebra.Smooth K A] [Ring.KrullDimLE 1 A]
    (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (N : Ideal (TensorProduct K A R)) [N.IsMaximal]
    (hPN : ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))) ≤ N)
    (u : FractionRing (TensorProduct K A R))
    (hP : Work.SpecLin.Alt.IsUnitAt u ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (hht : ∀ p : Ideal (TensorProduct K A R), p.IsPrime → p.height = 1 → p ≤ N →
      Work.SpecLin.Alt.IsUnitAt u p) :
    Work.SpecLin.Alt.IsUnitAt u N := by
  refine ⟨?_, ?_⟩
  · exact Work.SpecLin.Setup.hartogsRelativeCurve (K := K) A hA R N hPN u hP.1
      (fun p hp hp1 hpN => (hht p hp hp1 hpN).1)
  · exact Work.SpecLin.Setup.hartogsRelativeCurve (K := K) A hA R N hPN u⁻¹ hP.2
      (fun p hp hp1 hpN => (hht p hp hp1 hpN).2)

/-- **The crux of the affine-chart core of specialisation of linear equivalence.**

`R` is a valuation ring which is a `K`-algebra, `W` a nonempty affine chart of a curve `C/K`,
`B = Γ(C,W) ⊗[K] R` the relative chart (a domain), `P = 𝔪_R·B = chartFibrePrime R W` the prime
of the generic point of the special fibre, and `N ⊇ P` a maximal ideal (a closed point of the
chart `W_κ` of the special fibre).  The claim is that a rational function `u ∈ Frac B` which is a
unit at `P` and at every height-one prime `p ≤ N` is a unit at `N`.

Equivalently (see `Setup/NOTES_crux_helpers.md`, `Setup/cruxPITdomain.lean`,
`Setup/exists_height_one_prime.lean`, `Alt/cruxUnit.lean`, which state the same result in the
abstract `A ⊗[K] R` language): if `a ∈ B`, `a ∉ P`, `a ∈ N`, then some height-one prime
`p ≤ N` contains `a` (Krull's principal ideal result for the localisation of a finitely
generated flat algebra with one-dimensional fibres over a valuation ring).

NOTE.  `ChartTensor R W = Γ(C,W) ⊗[K] R`; the hypotheses `Algebra.FiniteType K Γ(C,W)`,
`Ring.KrullDimLE 1 Γ(C,W)` (so `dim = 1`, since `Γ(C,W)` is not a field),
`Algebra.Smooth K Γ(C,W)` (`Setup/smoothSections`), `IsDomain (B)` and
`IsDomain (B ⧸ P)` (geometric irreducibility) are all available in the workspace, so this is
exactly the specialised form of the abstract statements above.

A possible route is the dimension theory already available in the workspace:
`Alt.fibres_ringKrullDim_tensor_eq` (`dim B = dim R + 1`) together with
`Alt.ringKrullDim_quotient_span_singleton_eq_of_fibres` (`dim (B ⧸ (a)) = dim R`), which give
`ht ((a)) = 1`, and then a minimal prime of `(a)` lying inside `N` has height one. -/
theorem cruxChartPull {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    [Nonempty W] [IsDomain (Work.SpecLin.Core.chartTensor R W)]
    (N : Ideal (Work.SpecLin.Core.chartTensor R W)) (hN : N.IsMaximal)
    (hPN : Work.SpecLin.Core.chartFibrePrime R W ≤ N)
    (u : FractionRing (Work.SpecLin.Core.chartTensor R W)) (hu : u ≠ 0)
    (hP : Work.SpecLin.Alt.IsUnitAt u (Work.SpecLin.Core.chartFibrePrime R W))
    (hht : ∀ p : Ideal (Work.SpecLin.Core.chartTensor R W), p.IsPrime → p.height = 1 →
      p ≤ N → Work.SpecLin.Alt.IsUnitAt u p) :
    Work.SpecLin.Alt.IsUnitAt u N := by
  -- The chart `B = Γ(C,W) ⊗[K] R` is the base change of the coordinate ring `A = Γ(C,W)`,
  -- which is a finitely generated, smooth, one-dimensional `K`-algebra, and the fibre
  -- `A ⊗[K] κ` is a domain (geometric irreducibility of the chart).  So we may apply the
  -- abstract crux `Work.SpecLin.Setup.cruxPITdomain` to `A = Γ(C,W)`.
  haveI hft : Algebra.FiniteType K Γ(C.left, W) :=
    Work.CurveBasics.BaseChange.finiteType_sections C W hW
  haveI hsm : Algebra.Smooth K Γ(C.left, W) :=
    Work.SpecLin.Setup.smoothSections C W hW
  haveI hdim : Ring.KrullDimLE 1 Γ(C.left, W) :=
    Work.CurveBasics.BaseChange.krullDimLE_sections C W hW
  -- `Γ(C,W)` is not a field, so its Krull dimension is not `0`: it is the coordinate ring of a
  -- nonempty affine chart of a proper curve, which contains a closed point.
  have hA : ¬ Ring.KrullDimLE 0 Γ(C.left, W) := by
    intro h0
    exact Work.SpecLin.Alt.not_isField_chartSections C W hW
      (Ring.isField_iff_maximal_bot.mpr
        (Ring.krullDimLE_zero_iff.mp h0 ⊥ Ideal.isPrime_bot))
  -- Geometric irreducibility: the special fibre `A ⊗[K] κ` is a domain.
  haveI hκ : IsDomain (TensorProduct K Γ(C.left, W) (IsLocalRing.ResidueField R)) :=
    Work.CurveBasics.Curve.isDomain_tensor_sections C hW (IsLocalRing.ResidueField R)
  haveI : N.IsMaximal := hN
  exact cruxAux (K := K) (A := Γ(C.left, W)) hA R N hPN u hP hht

end Up
end Work.SpecLin.Setup

