import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.homogeneous_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.NSM

open scoped commutatorElement

set_option linter.unusedVariables false

/-- `Ω₁(P) = A ^ (2)` is irreducible under `ξ`: a `ξ`-invariant subgroup of `A ^ (2)` is
either trivial or all of `A ^ (2)`.

This is a direct consequence of the irreducibility of `A ⊓ Ω₁(P)` under `ξ`
(`Work.Higman.invariant_subgroup_inf_omega1`), using `A ^ (2) ≤ A` and
`Ω₁(P) = A ^ (2)`: any `ξ`-invariant `T ≤ A ^ (2)` is a `ξ`-invariant subgroup of
`A ⊓ Ω₁(P)`, hence equals `⊥` or `A ⊓ Ω₁(P) = A ^ (2)`. -/
theorem powSubA2Irreducible {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hOmega : Work.Higman.omega1 P = Work.Higman.powSub A 2) :
    ∀ T : Subgroup P, T ≤ Work.Higman.powSub A 2 →
      T.map (h.xi : MulAut P).toMonoidHom = T → T = ⊥ ∨ T = Work.Higman.powSub A 2 := by
  intro T hT hTin
  -- `A ^ (2) ≤ A`, so `T ≤ A ⊓ Ω₁(P)`.
  have h2le : Work.Higman.powSub A 2 ≤ A := Work.Higman.powSub_le (n := 2) (by norm_num)
  have hTle : T ≤ A ⊓ Work.Higman.omega1 P := by
    refine le_inf (le_trans hT h2le) ?_
    rw [hOmega]; exact hT
  rcases Work.Higman.invariant_subgroup_inf_omega1 h A hTle hTin with h | h
  · exact Or.inl h
  · right
    rw [h, hOmega]
    exact inf_eq_right.mpr h2le

end Work.Higman.NSM
