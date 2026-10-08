import Mathlib
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.conj_notMem` — `t x t ∉ H` for `x ∈ Q#`

If `t x t ∈ H` then, since `t` is an involution, `x = t (t x t) t` is `H^t`-conjugate to an
element of `H`, i.e. `x ∈ conj t H`; with `x ∈ Q ≤ H` this forces `x ∈ Q ∩ D = 1`.
So `t x t` lies outside `H` for every `x ∈ Q#`, which is what makes the `f`-map well defined.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem conj_notMem {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {x : G} (hx : x ∈ Q) (hx1 : x ≠ 1) :
    t * x * t ∉ H := by
  intro hcon
  have h2 : t * t = 1 := mul_self_eq_one h
  have hxm : x ∈ conj t H := by
    rw [mem_conj_iff]
    exact ⟨t * x * t, hcon, by simpa only [inv_eq_self h] using involution_conj (e := x) h2⟩
  have hmem : x ∈ Q ⊓ twoPoint H t :=
    ⟨hx, mem_twoPoint_iff.mpr ⟨h.le hx, hxm⟩⟩
  rw [h.inf_eq] at hmem
  exact hx1 (Subgroup.mem_bot.mp hmem)

end Work.RankOneUniqueness
