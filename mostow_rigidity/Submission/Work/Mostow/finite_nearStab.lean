import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.nearStabDefs
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.abs_mat_le_tpart_actO
import Submission.Work.Mostow.isCompact_matBallToPO

/-!
# The near-stabiliser of the origin is finite

For a discrete subgroup `Γ ≤ PO n 1` and a radius `R`, the set of `γ ∈ Γ` with
`hdist 0 (γ • 0) ≤ R` is finite.

The argument is the standard properness of the orbit map `g ↦ g • 0`, made explicit:

* `abs_mat_le_tpart_actO` bounds every entry of a representing matrix of `A ∈ O(n,1)` by
  `tpart (actO A 0) = √(1 + ‖A • 0‖²)`, so `{g | hdist 0 (g • 0) ≤ R}` is contained in the image in
  `PO n 1` of the bounded set of matrices `matBall n (cosh R)` (`nearStab_orbitBall_subset`);
* that image is compact (`isCompact_matBallToPO`);
* a discrete subgroup of a Hausdorff topological group meets every compact set in a finite set
  (`Subgroup.tendsto_coe_cofinite_of_isDiscrete` composed with `tendsto_cofinite_cocompact_iff`).

The Hausdorff instance for `PO n 1` is the one built in `Submission/Work/Mostow/HaarBase.lean`
(`instT2SpacePO`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Topology

/-- The set of elements displacing the origin by at most `R` is contained in the image in `PO n 1`
of the set of `O(n,1)`-matrices all of whose entries are bounded by `cosh R`. -/
theorem nearStab_orbitBall_subset {n : ℕ} (R : ℝ) :
    {g : PO n 1 | hdist (0 : E n) (g • (0 : E n)) ≤ R} ⊆
      matBallToPO n (Real.cosh (max R 0)) := by
  intro g hg
  have hmat : mat (rep g) ∈ matBall n (Real.cosh (max R 0)) := by
    refine ⟨?_, O1_form_col (rep g), O1_form_row (rep g)⟩
    intro i j
    have h1 := abs_mat_le_tpart_actO (rep g) i j
    have h2 : actO (rep g) (0 : E n) = g • (0 : E n) := rfl
    rw [h2] at h1
    rw [← cosh_hdist_zero] at h1
    refine le_trans h1 (Real.cosh_le_cosh.mpr ?_)
    rw [abs_of_nonneg (hdist_nonneg 0 (g • (0 : E n))), abs_of_nonneg (le_max_right R 0)]
    exact le_trans hg (le_max_left R 0)
  rw [matBallToPO, Set.mem_image]
  refine ⟨⟨mat (rep g), hmat⟩, Set.mem_univ _, ?_⟩
  have hEq : O1.ofMatrix (mat (rep g)) ⟨hmat.2.1, hmat.2.2⟩ = rep g := by
    apply Subtype.ext
    exact mat_O1_ofMatrix (mat (rep g)) ⟨hmat.2.1, hmat.2.2⟩
  show ((O1.ofMatrix (mat (rep g)) ⟨hmat.2.1, hmat.2.2⟩ : O1 n) : PO n 1) = g
  rw [hEq]
  exact Quotient.out_eq g

theorem finite_nearStab {n : ℕ} (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hdisc : IsDiscrete (SetLike.coe Γ)) (R : ℝ) :
    {γ : Γ | Submission.Mostow.hdist (0 : Submission.Mostow.E n)
      ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n)) ≤ R}.Finite := by
  have hK : IsCompact (matBallToPO n (Real.cosh (max R 0))) := isCompact_matBallToPO _
  have htend : Filter.Tendsto ((↑) : Γ → PO n 1) Filter.cofinite (Filter.cocompact (PO n 1)) :=
    Subgroup.tendsto_coe_cofinite_of_isDiscrete Γ hdisc
  have hfin : {γ : Γ | (γ : PO n 1) ∈ matBallToPO n (Real.cosh (max R 0))}.Finite :=
    (tendsto_cofinite_cocompact_iff.mp htend) _ hK
  exact hfin.subset (fun γ hγ => nearStab_orbitBall_subset R hγ)

end Work.Mostow
