import Mathlib
import Submission.Work.Skeleton.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

/-- A minimal counterexample to the odd order theorem has a proper nontrivial subgroup: its
bottom subgroup is not a coatom of the subgroup lattice.

Indeed, if `⊥` were a coatom then the subgroup lattice would be `{⊥, ⊤}`; picking a
nontrivial element `a` this forces `Subgroup.zpowers a = ⊤`, so `G` is cyclic, hence
commutative — contradicting the nonabelianity of a minimal counterexample. -/
theorem minSimpleOdd_not_isCoatom_bot {G : Type*} [Group G] [Finite G] (h : MinSimpleOdd G) :
    ¬ IsCoatom (⊥ : Subgroup G) := by
  intro hc
  haveI : Nontrivial G := h.nontrivial
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  -- a nontrivial element generates the whole group
  have hzp : Subgroup.zpowers a = ⊤ := by
    have hne : Subgroup.zpowers a ≠ ⊥ := by
      intro hbot
      have : a ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers a
      exact ha (Subgroup.mem_bot.mp this)
    have hlt : (⊥ : Subgroup G) < Subgroup.zpowers a := bot_lt_iff_ne_bot.mpr hne
    exact (hc.lt_iff).mp hlt
  haveI : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨a, hzp⟩
  exact h.not_isMulCommutative (IsCyclic.isMulCommutative (α := G))

end Work.Skeleton
