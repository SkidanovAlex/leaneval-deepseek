import Mathlib
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.DoubleTransitivity.Sec5

theorem sylow_iSup_eq {G : Type} [Group G] [Finite G] {D : Subgroup G}
    (Q : ∀ p : ℕ, Subgroup G)
    (hQ : ∀ p, p.Prime → Work.DoubleTransitivity.IsSylowSubgroupOf p (Q p) D) :
    D = ⨆ p : {p : ℕ // p.Prime}, Q p.1 := by
  -- Write `J` for the join of the chosen Sylow subgroups.
  set J : Subgroup G := ⨆ p : {p : ℕ // p.Prime}, Q p.1 with hJ
  -- Every `Q p` is contained in `D`, so `J ≤ D`.
  have hJle : J ≤ D := by
    rw [hJ]
    exact iSup_le fun p => (hQ p.1 p.2).1
  -- Each `Q p` sits inside `J`.
  have hQle : ∀ p (hp : p.Prime), Q p ≤ J := by
    intro p hp
    rw [hJ]
    exact le_iSup (fun q : {p : ℕ // p.Prime} => Q q.1) ⟨p, hp⟩
  -- No prime divides the relative index of `J` in `D`: a prime `p` dividing it would also
  -- divide the relative index of `Q p` in `D`, contradicting that `Q p` is Sylow in `D`.
  have hnotdvd : ∀ p, p.Prime → ¬ p ∣ J.relIndex D := by
    intro p hp hpdvd
    have hQi : ¬ p ∣ (Q p).relIndex D := (hQ p hp).2.2
    exact hQi (by
      rw [← Subgroup.relIndex_mul_relIndex (Q p) J D (hQle p hp) hJle]
      exact dvd_mul_of_dvd_right hpdvd _)
  -- Hence the relative index of `J` in `D` is `1`.
  have hrel : J.relIndex D = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    exact hnotdvd p hp hpdvd
  have hDle : D ≤ J := Subgroup.relIndex_eq_one.mp hrel
  exact le_antisymm hDle hJle

end Work.DoubleTransitivity.Sec5
