import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.not_hasMinimalPresentation_of_not_finiteDimensional

/-!
# `Work.ClassFieldTower.Vacuity` -- machine-checked refutation of the ABSTRACT-presentation certificate

**READ THIS BEFORE USING `GolodShafarevichCertificate` / `ShafarevichKochInput` /
`GeneratorRankInput` / `DeficiencyBoundInput`.**

Those definitions in `Defs.lean`/`Main.lean` build the arithmetic input on

    `HasMinimalPresentation (galoisGroup M) d r`,

i.e. on `G_∅ = Gal(F_∅/F)` having a finite presentation as an **abstract** group.  This is
**unsatisfiable** whenever `F_∅/F` is infinite:

* `HasMinimalPresentation G d r` exhibits `G ≃* FreeGroup α ⧸ normalClosure rel` with `α` finite,
  so `G` is **countable**;
* an infinite profinite Galois group is **uncountable**
  (`not_hasMinimalPresentation_of_not_finiteDimensional`).

Consequently `GolodShafarevichCertificate F M d r ∧ Infinite (galoisGroup M)` is refuted below
for every `F`, `M`, `d`, `r` -- the same failure mode as
`Commons.GroupTheory.ProPGroup.infinite_of_presentation_of_algebra_data`, machine-checked in
`Submission/GroupTheory/GolodShafarevichCriterion` as
`delivered_hdata_package_unsatisfiable`.

**Use `Work.ClassFieldTower.ProTwoTowerInput` and `Work.ClassFieldTower.ProTwo` instead**, where
the presentation is of an abstract group whose finite `2`-quotients are realized by unramified
extensions of `F` -- the classical, satisfiable formulation.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **The abstract-presentation certificate pins `G_∅` to be countable.** -/
theorem countable_of_hasMinimalPresentation {G : Type*} [Group G] {d r : ℕ}
    (h : HasMinimalPresentation G d r) : Countable G := by
  obtain ⟨α, iα, iD, rel, -, -, ⟨e⟩, -⟩ := h
  haveI : Countable (FreeGroup α) := inferInstance
  haveI : Countable (FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) :=
    Quotient.countable
  exact Countable.of_equiv _ e.toEquiv.symm

/-- **THE REFUTATION.**  For a number field `F` and any `M : MaximalUnramifiedProP F 2`, there is
no `d`, `r` for which `G_∅` has an abstract minimal presentation *and* is infinite.  In other
words `GolodShafarevichCertificate F M d r ∧ Infinite (galoisGroup M)` is unsatisfiable, so the
certificate of `Defs.lean` cannot be used as the arithmetic input of the tower. -/
theorem golodShafarevichCertificate_and_infinite_unsatisfiable {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) (d r : ℕ) :
    ¬ (GolodShafarevichCertificate F M d r ∧ Infinite (MaximalUnramifiedProP.galoisGroup M)) := by
  rintro ⟨hcert, hinf⟩
  by_cases hfd : FiniteDimensional F M.K
  · haveI : FiniteDimensional F M.K := hfd
    haveI : Finite (M.K ≃ₐ[F] M.K) := by
      haveI : Fintype (M.K ≃ₐ[F] M.K) := AlgEquiv.fintype F M.K
      infer_instance
    haveI : Infinite (M.K ≃ₐ[F] M.K) := hinf
    exact not_finite (M.K ≃ₐ[F] M.K)
  · exact not_hasMinimalPresentation_of_not_finiteDimensional hfd d r hcert.presentation

/-- **Consequence: the old wall is unsatisfiable.** -/
theorem not_infiniteHilbertTwoClassFieldTower : ¬ InfiniteHilbertTwoClassFieldTower := by
  rintro ⟨F, iF, iNF, M, d, r, hcert, hinf⟩
  letI : Field F := iF
  letI : NumberField F := iNF
  exact golodShafarevichCertificate_and_infinite_unsatisfiable M d r ⟨hcert, hinf⟩

end Work.ClassFieldTower
