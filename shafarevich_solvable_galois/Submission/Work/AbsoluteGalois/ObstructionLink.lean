/-
Copyright (c) 2025. All rights reserved.

# The obstruction calculus for embedding problems over `ℚ`

This file assembles the group-cohomological obstruction calculus for an embedding problem
`E : Submission.EmbeddingProblem ℚ` with **abelian kernel** `A = ker E.π` (equivalently
`ker M.pi` for a closure model `M`), in the language of the absolute Galois group.

Choosing a normalized set-theoretic section `s` of `M.pi : E.G →* Gal(M.L/ℚ)` produces the
`2`-cocycle `sectionCocycle M.pi s` with values in `A` (a `Gal(M.L/ℚ)`-module by conjugation), the
**extension class** of `E`.  Its pullback along the restriction map `ρ = restrictHom M.L` is the
`2`-cocycle `pullbackCocycle ρ (sectionCocycle M.pi s)` on `G_ℚ`.  The classical statement of the
obstruction calculus is then

* `exists_lift_iff_pullbackCocycle_mem_B2`: a *lift* of `M.pi` along `ρ` (a homomorphism
  `ψ : G_ℚ →* E.G` with `M.pi.comp ψ = restrictHom M.L`, i.e. a splitting of the fibre product
  `pullback E M`) exists if and only if the pulled back class is a **coboundary**, i.e. the
  obstruction `ρ^*(class of E) ∈ H²(G_ℚ, A)` vanishes;

* `hasSurjectiveLift_imp_pullbackCocycle_mem_B2`: a *surjective* lift (a solution of `E`, see
  `Work.AbsoluteGalois.isSolvable_iff_hasSurjectiveLift`) therefore has vanishing obstruction;
  the converse fails, because a surjective lift is strictly stronger than a lift — e.g. a split
  embedding problem has zero class, hence a lift, but need not be solvable.

## Main declarations

* `Work.AbsoluteGalois.ClosureModel.pickSection`, `ClosureModel.normalizedSection` — (normalized)
  set-theoretic sections of `M.pi`, with `pickSection_spec`, `normalizedSection_spec`,
  `normalizedSection_one`;
* `Work.AbsoluteGalois.exists_lift_iff_pullbackCocycle_mem_B2`;
* `Work.AbsoluteGalois.hasSurjectiveLift_imp_pullbackCocycle_mem_B2`.
-/
import Mathlib
import Submission.EmbeddingProblem
import Submission.Work.GroupCohomology.Basic
import Submission.Work.AbsoluteGalois.Basic
import Submission.Work.AbsoluteGalois.Realization
import Submission.Work.AbsoluteGalois.ClosureModel
import Submission.Work.AbsoluteGalois.Embedding
import Submission.Work.AbsoluteGalois.Lift
import Submission.Work.AbsoluteGalois.Obstruction
import Submission.Work.AbsoluteGalois.Cohomology
import Submission.Work.AbsoluteGalois.twisted_splitting_iff_mem_B2
import Submission.Work.AbsoluteGalois.pullbackCocycle_mem_Z2
import Submission.Work.AbsoluteGalois.pullbackCocycle_mem_B2
import Submission.Work.AbsoluteGalois.sectionCocycle_mem_Z2
import Submission.Work.AbsoluteGalois.exists_hom_lift_iff_pullbackCocycle_mem_B2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

namespace EmbeddingProblem

namespace ClosureModel

variable {E : EmbeddingProblem ℚ} (M : E.ClosureModel)

/-- A set-theoretic section of the projection `M.pi : E.G →* Gal(M.L/ℚ)` (which exists since
`M.pi` is surjective). -/
noncomputable def pickSection : (↥M.L ≃ₐ[ℚ] ↥M.L) → E.G :=
  fun q => Classical.choose (M.pi_surjective q)

lemma pickSection_spec (q : ↥M.L ≃ₐ[ℚ] ↥M.L) : M.pi (M.pickSection q) = q :=
  Classical.choose_spec (M.pi_surjective q)

/-- The **normalized** section of `M.pi`: `pickSection` corrected so that `1 ↦ 1`. -/
noncomputable def normalizedSection : (↥M.L ≃ₐ[ℚ] ↥M.L) → E.G :=
  fun q => M.pickSection q * (M.pickSection 1)⁻¹

lemma normalizedSection_spec (q : ↥M.L ≃ₐ[ℚ] ↥M.L) : M.pi (M.normalizedSection q) = q := by
  rw [normalizedSection, map_mul, map_inv, pickSection_spec M q, pickSection_spec M 1, inv_one,
    mul_one]

@[simp]
lemma normalizedSection_one : M.normalizedSection 1 = 1 := by
  rw [normalizedSection, mul_inv_cancel]

end ClosureModel

end EmbeddingProblem

end Submission

namespace Work.AbsoluteGalois

open scoped Classical

set_option warn.classDefReducibility false

noncomputable section

variable {E : Submission.EmbeddingProblem ℚ} (M : E.ClosureModel)

/-- The module structure on the abelian kernel of `M.pi`, by conjugation of `Gal(M.L/ℚ)`. -/
noncomputable def kernelModule (hcomm : ∀ a b : M.pi.ker, a * b = b * a) :
    DistribMulAction (↥M.L ≃ₐ[ℚ] ↥M.L) (Additive M.pi.ker) :=
  kernelAction M.pi M.normalizedSection M.normalizedSection_spec M.normalizedSection_one hcomm

/-- **The obstruction calculus.**  A lift of the embedding problem `E` along the restriction map
`restrictHom M.L` exists if and only if the extension class of `E`, pulled back along the
restriction map, is a coboundary: the obstruction `ρ^*(class of E) ∈ H²(G_ℚ, ker E.π)` vanishes. -/
theorem exists_lift_iff_pullbackCocycle_mem_B2 (hcomm : ∀ a b : M.pi.ker, a * b = b * a) :
    letI : CommGroup M.pi.ker := { (inferInstance : Group M.pi.ker) with mul_comm := hcomm }
    letI := kernelModule M hcomm
    letI := DistribMulAction.compHom (Additive M.pi.ker) (restrictHom M.L)
    ((∃ ψ : Field.absoluteGaloisGroup ℚ →* E.G,
        M.pi.comp ψ = restrictHom M.L) ↔
      pullbackCocycle (restrictHom M.L)
        (sectionCocycle M.pi M.normalizedSection M.normalizedSection_spec)
        ∈ GroupCohomology.B2 (Field.absoluteGaloisGroup ℚ) (Additive M.pi.ker)) := by
  letI : CommGroup M.pi.ker := { (inferInstance : Group M.pi.ker) with mul_comm := hcomm }
  letI : DistribMulAction (↥M.L ≃ₐ[ℚ] ↥M.L) (Additive M.pi.ker) := kernelModule M hcomm
  letI : DistribMulAction (Field.absoluteGaloisGroup ℚ) (Additive M.pi.ker) :=
    DistribMulAction.compHom (Additive M.pi.ker) (restrictHom M.L)
  exact exists_hom_lift_iff_pullbackCocycle_mem_B2 M.pi M.normalizedSection
    M.normalizedSection_spec M.normalizedSection_one hcomm (restrictHom M.L)

/-- **A solution of an embedding problem has vanishing obstruction.**  If `E` has a surjective
lift (equivalently, by `Work.AbsoluteGalois.isSolvable_iff_hasSurjectiveLift`, if `E` is solvable),
then the extension class of `E` pulls back to a coboundary along the restriction map:
the pulled back obstruction class in `H²(G_ℚ, ker E.π)` vanishes.

The converse is false: a *split* embedding problem has vanishing class (a plain lift exists, see
`exists_lift_iff_pullbackCocycle_mem_B2`) but its solution requires a surjective lift, which need
not exist. -/
theorem hasSurjectiveLift_imp_pullbackCocycle_mem_B2 (hcomm : ∀ a b : M.pi.ker, a * b = b * a)
    (h : HasSurjectiveLift E) :
    letI : CommGroup M.pi.ker := { (inferInstance : Group M.pi.ker) with mul_comm := hcomm }
    letI := kernelModule M hcomm
    letI := DistribMulAction.compHom (Additive M.pi.ker) (restrictHom M.L)
    pullbackCocycle (restrictHom M.L)
      (sectionCocycle M.pi M.normalizedSection M.normalizedSection_spec)
      ∈ GroupCohomology.B2 (Field.absoluteGaloisGroup ℚ) (Additive M.pi.ker) := by
  letI : CommGroup M.pi.ker := { (inferInstance : Group M.pi.ker) with mul_comm := hcomm }
  letI : DistribMulAction (↥M.L ≃ₐ[ℚ] ↥M.L) (Additive M.pi.ker) := kernelModule M hcomm
  letI : DistribMulAction (Field.absoluteGaloisGroup ℚ) (Additive M.pi.ker) :=
    DistribMulAction.compHom (Additive M.pi.ker) (restrictHom M.L)
  exact (exists_lift_iff_pullbackCocycle_mem_B2 M hcomm).mp
    (HasSurjectiveLift.exists_lift E M h)

end

end Work.AbsoluteGalois
