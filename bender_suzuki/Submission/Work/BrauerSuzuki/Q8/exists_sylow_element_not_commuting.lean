import Mathlib
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

/-- In a generalized quaternion group of order `8` — i.e. `Q₈` — an element of order `4` is
never central: an element of `⟨τ⟩` of order `4` is inverted by `ρ`, while an element outside
`⟨τ⟩` inverts `τ` and therefore does not commute with `τ`. -/
theorem exists_sylow_element_not_commuting {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx4 : orderOf x = 4) :
    ∃ s ∈ (S : Subgroup G), s * x ≠ x * s := by
  let y : ↥S := ⟨x, hxS⟩
  have hy4 : orderOf y = 4 := by
    rw [← Subgroup.orderOf_coe y]
    exact hx4
  have hbas := Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d
  obtain ⟨s, hs⟩ : ∃ s : ↥S, s * y ≠ y * s := by
    by_cases hx : y ∈ Subgroup.zpowers d.tau
    · refine ⟨d.rho, ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hconj : d.rho * y * d.rho⁻¹ = y⁻¹ := by
        rw [← hk, ← conj_zpow (a := d.rho) (b := d.tau) (i := k), d.rho_conj, inv_zpow]
      have hyne : y⁻¹ ≠ y := by
        intro hinv
        have hy2 : y * y = 1 := (mul_eq_one_iff_inv_eq).mpr hinv
        have hdvd : orderOf y ∣ 2 :=
          orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hy2)
        have hle : orderOf y ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
        omega
      intro hcomm
      exact hyne (by rw [← hconj, hcomm]; group)
    · refine ⟨d.tau, ?_⟩
      have hconj : y * d.tau * y⁻¹ = d.tau⁻¹ := (hbas.2.2.2.2 y hx).2
      intro hcomm
      have heq : d.tau⁻¹ = d.tau := by
        rw [← hconj, ← hcomm]
        group
      have h2' : d.tau * d.tau = 1 := (mul_eq_one_iff_inv_eq).mpr heq
      have hdvd : orderOf d.tau ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2')
      have ho4 : orderOf d.tau = 4 := by rw [d.tau_order, h2]; norm_num
      rw [ho4] at hdvd
      have hle : 4 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
  exact ⟨(s : G), s.2, fun hcon => hs (Subtype.ext (by simpa using hcon))⟩

end Work.BrauerSuzuki.Q8
