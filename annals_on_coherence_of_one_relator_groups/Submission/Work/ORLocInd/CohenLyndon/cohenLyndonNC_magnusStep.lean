import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.NCForm
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.ORLocInd.CohenLyndon.magnusStepDefs
import Submission.Work.ORLocInd.CohenLyndon.cohenLyndonNC_hnn
import Submission.Work.ORLocInd.CohenLyndon.magnusStep.magW_disjoint_magA
import Submission.Work.ORLocInd.CohenLyndon.magnusStep.magW_disjoint_magB
import Submission.Work.ORLocInd.CohenLyndon.magnusStep.not_isProperPower_magW
import Submission.Work.ORLocInd.CohenLyndon.magnusStep.cohenLyndonNC_of_mulEquiv

namespace Work.ORLocInd.CohenLyndon

open Work.OROneRel

universe u

/-- **Case 1 of the Cohen--Lyndon induction: the Magnus (HNN) step.**

Let `α` be a generating type, `r ∈ F(α)` cyclically reduced and *not a proper power*, and `t : α` a
letter occurring in `r` with exponent sum zero (`σ_t r = 0`).  Assume the Cohen--Lyndon property
for all *shorter* relators over all generating types (the strong induction hypothesis `IH`).  Then
`r` is Cohen--Lyndon aspherical in `F(α)`.

The proof is the Magnus decomposition: with `α' := ({a : α // a ≠ t}) × ℤ`, the Magnus rewriting
`r' := magRewRel t r` of `r` lives in the free group on the decorations occurring in the rewriting
(a set with bounded index range), `relatorNorm r' < relatorNorm r`, and `F(α)` is the HNN extension
of that free group along the two "index-shift" subgroups `A, B` with stable letter `t`; the map
`a ↦ of (a,0)` (`a ≠ t`), `t ↦ stable letter` is that isomorphism and sends `r` to `of r'`.  The
induction hypothesis applies to `r'`, the HNN transfer
(`Work.ORLocInd.CohenLyndon.cohenLyndonNC_hnn`) transfers the Cohen--Lyndon property to `of r'`,
and the isomorphism transports it back to `r`.  The Freiheitssatz provides the hypotheses
`⟪r'⟫ ∩ A = ⟂`, `⟪r'⟫ ∩ B = ⟂` of the transfer. -/
theorem cohenLyndonNC_magnusStep {α : Type u} [DecidableEq α] (r : FreeGroup α) (t : α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hpp : ¬ Work.OROneRel.IsProperPower r)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (hσ : Work.OROneRel.sigma t r = 1)
    (IH : ∀ (γ : Type u) [DecidableEq γ] (s : FreeGroup γ), ¬ Work.OROneRel.IsProperPower s →
      s ≠ 1 → Work.OROneRel.relatorNorm s < Work.OROneRel.relatorNorm r →
      Work.CohenLyndon.CohenLyndonNC s) :
    Work.CohenLyndon.CohenLyndonNC r := by
  classical
  have h1 : r ≠ 1 := Work.OROneRel.ne_one_of_not_isProperPower hpp
  have heps : eps t r = 0 := (eps_eq_zero_iff_sigma_eq_one t r).mpr hσ
  -- the induction hypothesis applies to the Magnus rewriting
  have hne : magW t r ≠ 1 := magW_ne_one t r hcyc h1 ht heps
  have hipp : ¬ IsProperPower (magW t r) := magnusStep.not_isProperPower_magW r t hpp heps
  have hlt : relatorNorm (magW t r) < relatorNorm r := magW_relatorNorm_lt t r ht
  have hCLw : Work.CohenLyndon.CohenLyndonNC (magW t r) :=
    IH (magS t r) (magW t r) hipp hne hlt
  -- the Freiheitssatz input for the HNN transfer
  have hdisA := magnusStep.magW_disjoint_magA r t hcyc h1 ht heps
  have hdisB := magnusStep.magW_disjoint_magB r t hcyc h1 ht heps
  have hCLof : Work.CohenLyndon.CohenLyndonNC
      (HNNExtension.of (magW t r) : magHNN t r) :=
    cohenLyndonNC_hnn (magA t r) (magB t r) (magPhi t r) hne hCLw hdisA hdisB
  -- transport back along the Magnus decomposition `F α ≃* magHNN`
  refine (magnusStep.cohenLyndonNC_of_mulEquiv (magIso t r) r) ?_
  rw [magIso_self t r heps]
  exact hCLof

end Work.ORLocInd.CohenLyndon
