import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup.Symplectic

theorem orderOf_pow_eq_of_not_dvd {G : Type*} [Group G] {p m s : ℕ} (hp : p.Prime) {a : G}
    (hoa : orderOf a = p ^ m) (hs : ¬ p ∣ s) : orderOf (a ^ s) = p ^ m := by
  have hcop : (orderOf a).Coprime s := by
    rw [hoa]
    exact (hp.coprime_iff_not_dvd.mpr hs).pow_left m
  rw [hcop.orderOf_pow, hoa]

end Work.PGroup.Symplectic
