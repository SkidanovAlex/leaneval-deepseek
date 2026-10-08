import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.linear_char_iff_deg_one
import Submission.Work.Clifford.irrDeg_eq_one_of_commutator_le_charKernel

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausPSL2.Feit

theorem linear_of_trivial_on_Q {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥H]
    {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q) {lc : H → ℂ}
    (hlc : lc ∈ Work.CharCore.Irr H) (hlcQ : ∀ x : H, (x : G) ∈ Q → lc x = 1) :
    ∃ φ : ↥H →* ℂˣ, ∀ x : ↥H, lc x = (φ x : ℂ) := by
  -- `1 ∈ Q`, so the hypothesis applied at the identity gives `lc 1 = 1`: the degree of `lc`
  -- is already known to be one.
  have h1 : lc 1 = 1 := hlcQ 1 (by simpa using Q.one_mem)
  have hdeg : Work.CharCore.irrDeg lc = 1 := by
    have hcast : (Work.CharCore.irrDeg lc : ℂ) = ((1 : ℕ) : ℂ) := by
      rw [← Work.CharCore.irrDeg_spec hlc, h1]
      norm_num
    exact_mod_cast hcast
  exact (Work.CharCore.linear_char_iff_deg_one hlc).mp hdeg

end Work.ZassenhausPSL2.Feit
