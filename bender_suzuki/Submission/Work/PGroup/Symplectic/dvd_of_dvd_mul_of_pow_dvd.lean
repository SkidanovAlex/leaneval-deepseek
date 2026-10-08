import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup.Symplectic

theorem dvd_of_dvd_mul_of_pow_dvd {p m t v : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hv : p ^ (m - 1) ∣ v) (hv' : ¬ p ^ m ∣ v) (h : p ^ m ∣ t * v) : p ∣ t := by
  have hp0 : 0 < p := hp.pos
  have hpm1 : 0 < p ^ (m - 1) := pow_pos hp0 _
  have hpmm : p ^ m = p ^ (m - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  obtain ⟨v', rfl⟩ := hv
  have hpv' : ¬ p ∣ v' := by
    intro hd
    exact hv' (by rw [hpmm]; exact mul_dvd_mul_left _ hd)
  obtain ⟨k, hk⟩ := h
  have h1 : p ^ (m - 1) * (t * v') = p ^ (m - 1) * (p * k) := by
    have h2 : p ^ (m - 1) * (t * v') = p ^ m * k := by rw [← hk]; ring
    rw [h2, hpmm]
    ring
  have hcancel : t * v' = p * k := Nat.eq_of_mul_eq_mul_left hpm1 h1
  have hdvd : p ∣ t * v' := by rw [hcancel]; exact dvd_mul_right p k
  exact ((hp.dvd_mul).mp hdvd).resolve_right hpv'

end Work.PGroup.Symplectic
