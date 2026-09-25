import Mathlib
import Submission.Work.ShafarevichKoch.ValueTheorem.InflSystem

/-!
# `Work.ShafarevichKoch.ValueTheorem.LevelFormula` -- `H²_cont` is the level quotient

**Namespace** `Work.ShafarevichKoch`; module `Submission.Work.ShafarevichKoch.ValueTheorem.LevelFormula`.

At a level `U` whose inflation already covers `H²_cont(Γ,𝔽₂)` (`(H2InflTwo U).range = ⊤`, which
exists as soon as `H²_cont(Γ,𝔽₂)` is finite --
`Work.ShafarevichKoch.exists_openNormal_H2InflTwo_range_eq_top`), the continuous cohomology is the
quotient of the finite group `H²(Γ ⧸ U, 𝔽₂)` by the kernel of the inflation:

`H²_cont(Γ,𝔽₂) ≅ H²(Γ ⧸ U, 𝔽₂) ⧸ ker (H2InflTwo U)`

(first isomorphism theorem, since `H2InflTwo U` is then surjective).  Combined with the finite-level
transgression (`Work.HopfGaschutz.card_contH2_eq_card_relFrattiniQuotient`,
`Work.ConCohomology.ker_H2Res_eq_range_tg`) this computes the relation rank `r(G_∅)` from the
*finite* data of one level -- the form in which the classical value theorem is attacked.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.ShafarevichKoch

open Work.ConCohomology

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **The collapse makes the inflation surjective.** -/
theorem H2InflTwo_surjective_of_range_eq_top {U : OpenNormalSubgroup Γ}
    (hU : (H2InflTwo U).range = ⊤) : Function.Surjective (H2InflTwo U) := by
  intro x
  have : x ∈ (H2InflTwo U).range := by rw [hU]; exact AddSubgroup.mem_top x
  simpa using this

/-- **`H²_cont(Γ,𝔽₂)` is the quotient of the level `H²(Γ ⧸ U,𝔽₂)` by the kernel of the
inflation**, at a level whose inflation covers `H²_cont(Γ,𝔽₂)`. -/
noncomputable def contH2EquivLevelQuotient {U : OpenNormalSubgroup Γ}
    (hU : (H2InflTwo U).range = ⊤) :
    H2 Γ (ZMod 2) ≃+ ((H2 (Γ ⧸ U.toSubgroup) (ZMod 2)) ⧸ (H2InflTwo U).ker) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective (H2InflTwo U)
    (H2InflTwo_surjective_of_range_eq_top hU)).symm

/-- **The cardinality form**: at a collapsing level, `#H²_cont(Γ,𝔽₂)` is the size of the quotient of
the level by the kernel of the inflation. -/
theorem natCard_contH2_eq_natCard_levelQuotient {U : OpenNormalSubgroup Γ}
    (hU : (H2InflTwo U).range = ⊤) :
    Nat.card (H2 Γ (ZMod 2))
      = Nat.card ((H2 (Γ ⧸ U.toSubgroup) (ZMod 2)) ⧸ (H2InflTwo U).ker) :=
  Nat.card_congr (contH2EquivLevelQuotient hU).toEquiv

end Work.ShafarevichKoch
