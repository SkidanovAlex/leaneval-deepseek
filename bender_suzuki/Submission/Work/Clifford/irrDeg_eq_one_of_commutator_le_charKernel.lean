import Mathlib
import Submission.Work.CohApps.sum_irr_deg_sq_le_ker
import Submission.Work.CharCore.irrDeg_eq_one_of_commutative

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Irreducible characters trivial on the commutator subgroup have degree one

If `θ` is an irreducible complex character of a finite group `Y` whose kernel contains a normal
subgroup `M ⊇ ⁅Y, Y⁆`, then `θ` has degree `1`.

Indeed `M` is normal with `⁅Y, Y⁆ ≤ M`, so the quotient `Y ⧸ M` is commutative
(`Subgroup.Normal.quotient_commutative_iff_commutator_le`).  Since `M` lies in the kernel of `θ`,
the character descends to an irreducible character of the quotient
(`Work.CohApps.exists_irr_quotient_of_le_ker`), inflation preserving degrees
(`Work.CohApps.irrDeg_inflateFun`); an irreducible character of a commutative group has degree
one (`Work.CharCore.irrDeg_eq_one_of_commutative`).
-/

set_option linter.style.haveILetI false

namespace Work.Clifford

theorem irrDeg_eq_one_of_commutator_le_charKernel {Y : Type*} [Group Y] [Fintype Y]
    {M : Subgroup Y} [M.Normal] (hM : _root_.commutator Y ≤ M) {θ : Y → ℂ}
    (hθ : θ ∈ Work.CharCore.Irr Y) (hker : (M : Set Y) ⊆ Work.CharCore.charKernel θ) :
    Work.CharCore.irrDeg θ = 1 := by
  classical
  haveI : Fintype (Y ⧸ M) := QuotientGroup.fintype M
  haveI : IsMulCommutative (Y ⧸ M) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hM
  obtain ⟨χ', hχ', hinf⟩ := Work.CohApps.exists_irr_quotient_of_le_ker M hθ hker
  rw [← hinf, Work.CohApps.irrDeg_inflateFun M hχ']
  exact Work.CharCore.irrDeg_eq_one_of_commutative hχ'

end Work.Clifford
