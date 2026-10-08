import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

open Classical

/-- A nontrivial solvable group possesses a nontrivial normal subgroup that is abelian
(namely the last non-vanishing term of the derived series). -/
theorem exists_normal_commutative_ne_bot {G : Type*} [Group G] [Group.IsSolvable G]
    [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ IsMulCommutative ↥N := by
  classical
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable G).solvable
  have hex : ∃ m, derivedSeries G m = ⊥ := ⟨n, hn⟩
  have hm_eq : derivedSeries G (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hm_min : ∀ k, k < Nat.find hex → derivedSeries G k ≠ ⊥ :=
    fun k hk => Nat.find_min hex hk
  have htop : (⊤ : Subgroup G) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    exact hx (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top x))
  have hm_ne_zero : Nat.find hex ≠ 0 := by
    intro h
    rw [h, derivedSeries_zero] at hm_eq
    exact htop hm_eq
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne_zero
  have hD_ne_bot : derivedSeries G m' ≠ ⊥ := by
    apply hm_min
    omega
  have hcomm : ⁅derivedSeries G m', derivedSeries G m'⁆ = ⊥ := by
    rw [← derivedSeries_succ, ← Nat.succ_eq_add_one, ← hm', hm_eq]
  exact ⟨derivedSeries G m', derivedSeries_normal G m', hD_ne_bot,
    Subgroup.commutator_self_eq_bot_iff.mp hcomm⟩

theorem fitting_ne_bot (G : Type*) [Group G] [Finite G] [Group.IsSolvable G] [Nontrivial G] :
    Work.Fitting.fitting G ≠ ⊥ := by
  obtain ⟨N, hNnormal, hNne, hNcomm⟩ := exists_normal_commutative_ne_bot (G := G)
  have hnil : Group.IsNilpotent ↥N := @CommGroup.isNilpotent ↥N inferInstance hNcomm
  have hle : N ≤ fitting G := le_fitting hNnormal hnil
  intro hbot
  exact hNne (le_bot_iff.mp (hbot ▸ hle))

end Work.Fitting
