/-
Copyright (c) 2025. All rights reserved.

# The dictionary: embedding problems over `ℚ` versus the abstract setting

This file collects the translations between the three formulations of the paper's conditions.

* **(a)** `E.IsSolvable` — the embedding problem `E : Submission.EmbeddingProblem ℚ` has a
  *proper solution*;
* **(c)** a *surjective lift* `ψ : G_ℚ →* E.G` with open kernel and `M.pi ∘ ψ = restrictHom M.L`
  — i.e. `Work.AbsoluteGalois.HasSurjectiveLift E`;
* **(b)** a *plain lift* (equivalently, by `Work.AbsoluteGalois.exists_lift_iff_pullbackCocycle_mem_B2`,
  the pulled back extension class being a coboundary).

The classical equivalences are

* `Work.AbsoluteGalois.isSolvable_iff_hasSurjectiveLift` — `(a) ↔ (c)`;
* `Work.AbsoluteGalois.hasSurjectiveLift_imp_pullbackCocycle_mem_B2` — `(c) → (b)`, i.e. a
  proper solution has vanishing obstruction.

The purpose of this file is the same dictionary stated in the language of the abstract setting
`Work.Properness.Setup` with `closureToSetup`:

* `Work.Properness.isSolvable_imp_hasProperLift` — `(a) → (c)` in the abstract language;
* `Work.Properness.isSolvable_imp_pullbackCocycle_mem_B2` — `(a) → (b)`;
* `Work.Properness.hasProperLift_imp_hasLift` — `(c) → (b)` in the abstract language (forgetting
  the obstruction calculus).

None of these has a converse: `Work.Properness.HasProperLift` (a lift whose kernel image is `A`)
is strictly stronger than `Setup.HasLift`, see
`Work.Properness.hasLift_not_imp_hasProperLift` and the split embedding problem
`Work.Properness.section_lift_not_isProper`.

## A remark on topology

`Work.AbsoluteGalois.HasSurjectiveLift` (hence `E.IsSolvable`) asks for an **open kernel**, a
condition taken from the profinite topology on `G_ℚ`; the abstract `Setup` carries no topology, so
`Setup.IsProper ψ` only asks for surjectivity.  For the *continuous* homomorphisms produced by
Galois theory the two agree (a finite-index kernel of a continuous homomorphism into a finite
group is open), and all the paper's solutions are continuous by construction.  This is why the
abstract setting can drop the openness condition without loss for the paper's argument; the
one direction that is formalised below — `IsSolvable → HasProperLift` — does not need it.
-/
import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.BridgeDefs
import Submission.Work.Properness.hasLift_iff_pullbackCocycle_mem_B2
import Submission.Work.Properness.hasSurjectiveLift_iff_exists_properLift
import Submission.Work.Properness.hasSurjectiveLift_imp_hasProperLift
import Submission.Work.AbsoluteGalois.Lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

open scoped Classical

noncomputable section

universe u v w

/-- **(a) → (c)**: a solution of the embedding problem yields a proper lift in the abstract
setting.  (`E.IsSolvable ↔ M.HasSurjectiveLift` by
`Work.AbsoluteGalois.isSolvable_iff_hasSurjectiveLift`, and a surjective lift is in particular a
proper lift, `Work.Properness.hasSurjectiveLift_imp_hasProperLift`.) -/
theorem isSolvable_imp_hasProperLift {E : Submission.EmbeddingProblem ℚ} (M : E.ClosureModel)
    (hcomm : ∀ a b : M.pi.ker, a * b = b * a) (h : E.IsSolvable) :
    (closureToSetup M hcomm).HasProperLift :=
  hasSurjectiveLift_imp_hasProperLift M hcomm
    ((Work.AbsoluteGalois.isSolvable_iff_closureModel_hasSurjectiveLift E M).mp h)

/-- **(c) → (b)**: properness is stronger than solvability, abstractly: a proper lift is a lift. -/
theorem hasProperLift_imp_hasLift {S : Setup.{u, v, w}} (h : S.HasProperLift) : S.HasLift := by
  obtain ⟨ψ, _⟩ := h
  exact ⟨ψ⟩

/-- **(a) → (b)** at the level of the obstruction calculus: a solution of the embedding problem
has vanishing obstruction — the extension class of `E`, pulled back along the restriction map,
is a coboundary in `H²(G_ℚ, ker π)`.

This is the abstract-setting form of
`Work.AbsoluteGalois.hasSurjectiveLift_imp_pullbackCocycle_mem_B2`, combined with the equivalence
of a solution with a surjective lift.  The converse fails: a plain lift exists whenever the
extension splits, but that is not a proper solution — see
`Work.Properness.hasLift_not_imp_hasProperLift`. -/
theorem isSolvable_imp_pullbackCocycle_mem_B2 {E : Submission.EmbeddingProblem ℚ}
    (M : E.ClosureModel) (hcomm : ∀ a b : M.pi.ker, a * b = b * a) (h : E.IsSolvable) :
    letI : CommGroup M.pi.ker := { (inferInstance : Group M.pi.ker) with mul_comm := hcomm }
    letI := Work.AbsoluteGalois.kernelModule M hcomm
    letI := DistribMulAction.compHom (Additive M.pi.ker) (Work.AbsoluteGalois.restrictHom M.L)
    (Work.AbsoluteGalois.pullbackCocycle (Work.AbsoluteGalois.restrictHom M.L)
      (Work.AbsoluteGalois.sectionCocycle M.pi M.normalizedSection M.normalizedSection_spec)
      ∈ Work.GroupCohomology.B2 (Field.absoluteGaloisGroup ℚ) (Additive M.pi.ker)) := by
  letI : CommGroup M.pi.ker := { (inferInstance : Group M.pi.ker) with mul_comm := hcomm }
  letI : DistribMulAction (↥M.L ≃ₐ[ℚ] ↥M.L) (Additive M.pi.ker) :=
    Work.AbsoluteGalois.kernelModule M hcomm
  letI : DistribMulAction (Field.absoluteGaloisGroup ℚ) (Additive M.pi.ker) :=
    DistribMulAction.compHom (Additive M.pi.ker) (Work.AbsoluteGalois.restrictHom M.L)
  exact Work.AbsoluteGalois.hasSurjectiveLift_imp_pullbackCocycle_mem_B2 M hcomm
    ((Work.AbsoluteGalois.isSolvable_iff_hasSurjectiveLift E).mp h)

end

end Work.Properness
