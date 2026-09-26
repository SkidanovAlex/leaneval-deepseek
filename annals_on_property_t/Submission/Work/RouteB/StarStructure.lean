import Submission.Helpers
import Mathlib

open OnPropertyT Submission.Helpers
open scoped BigOperators

set_option autoImplicit false

/-!
# The group-ring involution of `ChallengeDeps` as a star-ring structure

`ChallengeDeps` equips `MonoidAlgebra ℝ G` with the involution
`star = MonoidAlgebra.mapDomain (·⁻¹)` **only as a bare `Star` instance**, so
Mathlib's entire `star` API (`star_sum`, `star_mul`, `star_smul`, `star_pow`,
`star_neg`, …) is unavailable: every identity has to be reproved by hand (as
`Submission/Helpers.lean` does).

The purpose of this file is to register the accompanying structure:
`InvolutiveStar`, `StarAddMonoid`, `StarMul`, `StarRing`, `StarModule ℝ`, and
`StarOrderedRing`-free basics.  After importing this module, all of Mathlib's
star lemmas apply to `ℝG` with the `ChallengeDeps` star.

Only *proofs* of the structure fields are added here; the `Star` instance
itself remains the one from `ChallengeDeps` (the instances below are given low
priority so that instance search keeps picking it).
-/

namespace Submission.RouteB

variable {G : Type*} [Group G]

noncomputable instance (priority := 10) instInvolutiveStar : InvolutiveStar (MonoidAlgebra ℝ G) where
  star_involutive := Helpers.star_star

noncomputable instance (priority := 10) instStarAddMonoid : StarAddMonoid (MonoidAlgebra ℝ G) where
  star_add := Helpers.star_add

noncomputable instance (priority := 10) instStarMul : StarMul (MonoidAlgebra ℝ G) where
  star_mul := Helpers.star_mul

noncomputable instance (priority := 10) instStarRing : StarRing (MonoidAlgebra ℝ G) where
  star_mul := Helpers.star_mul
  star_add := Helpers.star_add

noncomputable instance (priority := 10) instStarModule : StarModule ℝ (MonoidAlgebra ℝ G) where
  star_smul := Helpers.star_smul

end Submission.RouteB
