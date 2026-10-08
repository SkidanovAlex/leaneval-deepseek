import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.center_eq_omega1_new

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- In a Suzuki 2-group the centre is elementary abelian: every central element squares to `1`.

Higman (1963), *Suzuki 2-groups*, Theorem 1, proves `Ω₁(P) = Z(P)`, i.e. the centre consists
exactly of the elements of order dividing two; here that is available as
`Work.Higman.center_eq_omega1_new` (derived from Higman's Lemma 9, `higman9_exists_new`, together
with the Gorenstein–Thompson argument `equivariant_bihom_trivial`).  A central element `z`
therefore lies in `Ω₁(P)`, so `z ^ 2 = 1`, which is the assertion. -/
theorem center_sq_eq_one {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) :
    ∀ z : P, z ∈ Subgroup.center P → z * z = 1 := by
  intro z hz
  have hz' : z ∈ omega1 P := by
    rw [← center_eq_omega1_new h]
    exact hz
  have h2 : z ^ 2 = 1 := h.mem_omega1.mp hz'
  rwa [pow_two] at h2

end Work.Higman
