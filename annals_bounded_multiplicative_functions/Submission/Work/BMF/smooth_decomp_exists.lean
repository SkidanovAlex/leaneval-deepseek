import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem smooth_decomp_exists (r n : ℕ) (hn : 1 ≤ n) :
    ∃ s m : ℕ, (∀ q, q.Prime → q ∣ s → q ∣ r) ∧ s * m = n ∧ m.Coprime r := by
  have hn0 : n ≠ 0 := by omega
  -- `D` is the set of divisors of `n` that are coprime to `r`.
  let D : Finset ℕ := n.divisors.filter (fun d => d.Coprime r)
  have h1D : 1 ∈ D :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hn0, Nat.coprime_one_left r⟩
  have hDne : D.Nonempty := ⟨1, h1D⟩
  -- `m` is the largest element of `D`; `s` is the complementary factor `n / m`.
  let m : ℕ := D.max' hDne
  have hmD : m ∈ D := Finset.max'_mem D hDne
  obtain ⟨hmdvd, hmcop⟩ := Finset.mem_filter.mp hmD
  have hmdvd' : m ∣ n := (Nat.mem_divisors.mp hmdvd).1
  refine ⟨n / m, m, ?_, ?_, ?_⟩
  · -- every prime factor of `s = n / m` divides `r`
    intro q hqp hqs
    by_contra hqr
    have hqcop : q.Coprime r := (hqp.coprime_iff_not_dvd).mpr hqr
    have hqmdvd : q * m ∣ n := by
      have hnm : n = m * (n / m) := (Nat.mul_div_cancel' hmdvd').symm
      rw [hnm, mul_comm q m]
      exact mul_dvd_mul_left m hqs
    have hqmcop : (q * m).Coprime r := hqcop.mul_left hmcop
    have hmem : q * m ∈ D :=
      Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hqmdvd, hn0⟩, hqmcop⟩
    have hle : q * m ≤ m := Finset.le_max' D (q * m) hmem
    have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmdvd' (by omega)
    have hlt : m < q * m := by
      calc m = 1 * m := (one_mul m).symm
        _ < q * m := Nat.mul_lt_mul_of_pos_right (by have := hqp.two_le; omega) hmpos
    omega
  · exact Nat.div_mul_cancel hmdvd'
  · exact hmcop

end Work.BMF
