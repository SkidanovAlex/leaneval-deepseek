import Mathlib
import Submission.Work.SpecLin.Alt.cruxUnit
import Submission.Work.SpecLin.Alt.notMem_sup_maximal_sq
import Submission.Work.SpecLin.Alt.isPrincipal_sectionPrime_localization
import Submission.Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_alt
import Submission.Work.SpecLin.Alt.sectionPrime_sup_fibrePrime_eq_of_le
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart
import Submission.Work.SpecLin.Alt.chartDictionary
import Submission.Work.SpecLin.Core.ordChart
import Submission.Work.SpecLin.Core.ord_germ_eq_iff_mem_pow
import Submission.Work.SpecLin.Core.mem_primeIdealOf_ptToPoint_iff
import Submission.Work.SpecLin.Core.section_prime_sup_fibre_quot
import Submission.Work.SpecLin.Core.sectionPrime_genFibre_eq_ker
import Submission.Work.SpecLin.Setup.chartCoreDivPull

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Alt

universe u

/-- **Specialisation of linear equivalence over a valuation ring, affine-chart case.**

`R` is a `K`-valuation ring, `W ⊆ C` an affine open of the curve containing the images of the
`R`-points `s m`, `t m`, and `h ≠ 0` on `C_F` (`F = FractionRing R`) has
`div h = Σ_m [s_m^F] − Σ_m [t_m^F]` on `C_F`, where `[p] = Work.SpecLin.ptDiv p`.  Then the
divisors `Σ_m [s̄_m]` and `Σ_m [t̄_m]` of the special fibres on `C_κ` (`κ = ResidueField R`) are
linearly equivalent. -/
theorem chartCoreDivAux {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hs : ∀ m, Set.range (s m).left.base ⊆ (W : Set C.left))
    (ht : ∀ m, Set.range (t m).left.base ⊆ (W : Set C.left))
    (h : (C.baseChange (FractionRing R)).functionField) (hh : h ≠ 0)
    (hdiv : (C.baseChange (FractionRing R)).div h
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (t m)))) :
    Work.SpecLin.LinEquiv C
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) (s m)))
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) (t m))) :=
  Work.SpecLin.Setup.chartCoreDivPull (K := K) (C := C) (n := n) R W hW s t hs ht h hh hdiv

end Work.SpecLin.Alt
