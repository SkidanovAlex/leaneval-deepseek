import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.normalizer_eq_stabilizer_of_isPGroup_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Commons.GroupTheory.Bender

theorem card_sylow_two_eq_index_stabilizer_of_isPGroup_of_odd_index {G Ω : Type*} [Group G]
    [Finite G] [MulAction G Ω] [Finite Ω] (htrans : MulAction.IsPretransitive G Ω)
    (hne : 1 < Nat.card Ω) (heven : Even (Nat.card G))
    (hinv : ∀ t : G, orderOf t = 2 → ∃! x : Ω, t • x = x) (α : Ω) {U : Subgroup G}
    (hU2 : IsPGroup 2 U) (hnot : ¬ 2 ∣ U.index) (hUB : U ≤ MulAction.stabilizer G α)
    (hBn : MulAction.stabilizer G α ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card (Sylow 2 G) = (MulAction.stabilizer G α).index := by
  -- `U` is nontrivial: otherwise its index is `Nat.card G`, which is even.
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.index_bot] at hnot
    exact hnot heven.two_dvd
  -- Hence `N_G(U) = Stab_G(α)`.
  have hN : Subgroup.normalizer (U : Set G) = MulAction.stabilizer G α :=
    normalizer_eq_stabilizer_of_isPGroup_two htrans hne heven hinv α hU2 hUne hUB hBn
  -- `U` is a Sylow `2`-subgroup of `G`.
  let P : Sylow 2 G := hU2.toSylow hnot
  have hP : (P : Subgroup G) = U := rfl
  haveI : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex P
  rw [Sylow.card_eq_index_normalizer P]
  have hPset : (P : Set G) = (U : Set G) := congrArg (fun s : Subgroup G => (s : Set G)) hP
  rw [hPset, hN]

end Commons.GroupTheory.Bender
