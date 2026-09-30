import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Setup
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map
import Submission.Work.SpecLin.Content.isPrincipal_of_fg_of_cyclic_map_quotient
import Submission.Work.CurveBasics.All
import Submission.Work.SpecLin.Alt.chartCoreDivAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SpecLin.Alt

/-
**Specialisation of linear equivalence, affine-chart form.**

`R` is a valuation ring which is a `K`-algebra, `W ⊆ C` is an affine open, and
`s t : Fin n → Spec R ⟶ C` are two `n`-tuples of `R`-points of a curve `C` whose images all lie
in `W`.  If the divisors `Σ_m [s_m]` and `Σ_m [t_m]` of the generic fibres on `C_F`
(`F = Frac R`) are linearly equivalent, then the divisors `Σ_m [s̄_m]` and `Σ_m [t̄_m]` of the
special fibres on `C_κ` (`κ = ResidueField R`) are linearly equivalent.  Here
`[p] = Work.SpecLin.ptDiv p` is the concrete divisor of the closed point of `C_F` attached to
the `F`-point `p` (`Submission/Work/SpecLin/Points/Basic.lean`), and
`Work.SpecLin.RPt.map e p = specOfMap e ≫ p`; in particular
`RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (s m) = genPt R ≫ s m` and
`RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) (s m) = closedPt R ≫ s m`.

Guidance for the prover (added by the requester).
* This is the *content* of `Work.SpecLin.Core.linEquiv_of_sections_of_chart` (same file:
  `Submission/Work/SpecLin/Core/linEquiv_of_sections_of_chart.lean`), which is `sorry`-stubbed
  together with `Work.SpecLin.Core.linEquiv_of_sections` and
  `Work.SpecLin.Setup.linEquiv_of_sections_core`; do NOT prove this goal by applying one of them
  (the resulting proof would depend on `sorryAx` and the final axiom check would fail).
* A *very* detailed 4-step proof plan is in the docstring of
  `Work.SpecLin.Core.linEquiv_of_sections_of_chart`; use it.  The definitions built there
  (`Work.SpecLin.Core.chartTensor = A ⊗_K R`, `Work.SpecLin.Core.evChart`,
  `Work.SpecLin.Core.sectionPrime = ker(B →_K R)`) are proved and may be used, as is
  `Work.SpecLin.Core.rgMap` (`Γ(C,W) →ₐ[K] R` induced by an `R`-point whose image lies in `W`,
  file `Submission/Work/SpecLin/Core/linEquiv_of_sections.lean`).
* The two commutative-algebra inputs are already proved:
  `Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map` (content normalisation) and
  `Work.SpecLin.Content.isPrincipal_of_fg_of_cyclic_map_quotient` (Nakayama: the section ideals
  are locally principal).  The place/order/divisor/base-change machinery of area `CB` is in
  `Submission/Work/CurveBasics/`.
* The statement is the chart case of `Work.SpecLin.Alt.coreGen`
  (`Submission/Work/SpecLin/Alt/coreGen.lean`); the latter is being proved in parallel and is the
  linchpin of area `PR` (`Work.SpecLin.Core.linEquiv_of_sections` is derived from it).  A proof of
  *this* goal is useful even if that attempt fails.
* You may add helper results and further files under `Submission/Work/SpecLin/Alt/` (avoid the
  file names `coreGen.lean` and `coreGen2.lean`).
-/
theorem chartCore {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hs : ∀ m, Set.range (s m).left.base ⊆ (W : Set C.left))
    (ht : ∀ m, Set.range (t m).left.base ⊆ (W : Set C.left))
    (hF : Work.SpecLin.LinEquiv C
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.RPt.map
        (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)))
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.RPt.map
        (IsScalarTower.toAlgHom K R (FractionRing R)) (t m)))) :
    Work.SpecLin.LinEquiv C
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.RPt.map
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) (s m)))
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.RPt.map
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) (t m))) := by
  obtain ⟨h, hh, hdiv⟩ := hF
  exact Work.SpecLin.Alt.chartCoreDivAux R W hW s t hs ht h hh hdiv

end Work.SpecLin.Alt
