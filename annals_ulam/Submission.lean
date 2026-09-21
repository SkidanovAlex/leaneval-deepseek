import ChallengeDeps
import Submission.Helpers
import Submission.Odd.Leaf
import Submission.Commons.Geometry.Ulam.floating_body_exists_even_leaf

open Ulam
open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission

theorem theorem_1 (hd : 3 ≤ d) : letI : NeZero d := ⟨by omega⟩
    ∃ K : BodyOfRevolution d, IsStrictlyConvexBody K.body ∧ ¬ IsCentrallySymmetric K.body ∧
      FloatsInEquilibriumInEveryOrientationAtLevel K.body (volume.real K.body / 2) := by
  letI : NeZero d := ⟨by omega⟩
  by_cases heven : Even d
  · -- even dimensions: the local perturbation construction (complete in the commons)
    obtain ⟨R₁, R₂, f, hsupp, hsm, hconc, hstrict, hcomp, hinter, hnonc, hfloat⟩ :=
      Commons.Geometry.Ulam.floating_body_exists_even_leaf (d := d) hd heven
    refine ⟨⟨R₁, R₂, f, hsupp, hsm, hconc⟩, ⟨hstrict, hcomp, hinter⟩, hnonc, ?_⟩
    intro ξ H
    exact hfloat ξ H.t H.vol
  · -- odd dimensions
    have hodd : Odd d := Nat.not_even_iff_odd.mp heven
    obtain ⟨R₁, R₂, f, hsupp, hsm, hconc, hstrict, hcomp, hinter, hnonc, hfloat⟩ :=
      Submission.Odd.odd_floating_body_exists_leaf (d := d) hd hodd
    refine ⟨⟨R₁, R₂, f, hsupp, hsm, hconc⟩, ⟨hstrict, hcomp, hinter⟩, hnonc, ?_⟩
    intro ξ H
    exact hfloat ξ H.t H.vol

end Submission
