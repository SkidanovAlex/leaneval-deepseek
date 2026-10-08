import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `C_G(y) ≤ H` for `y ∈ Q#` (Feit's `C(y) ⊆ M × H`, Hypothesis II (i), `h = 1`)

`Q` is T.I. in `G` (`isTI_Q`), so an element `c` outside `H` has `Q ∩ cQc⁻¹ = 1`.  If `c`
centralises `y ∈ Q#`, then `y = c y c⁻¹ ∈ Q ⊓ conj c Q`, forcing `y = 1` unless `c ∈ H`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

theorem centralizer_le_H {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    {y : G} (hy : y ∈ Q) (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≤ H := by
  intro c hc
  by_contra hcH
  have hcQ : y ∈ Submission.Blueprint.conj c Q := by
    refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
    have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    simp [MulAut.conj_apply, hcy]
  have : y ∈ Q ⊓ Submission.Blueprint.conj c Q := ⟨hy, hcQ⟩
  rw [isTI_Q h hz c hcH] at this
  exact hy1 (Subgroup.mem_bot.mp this)

end Work.ZassenhausTwoGroup
