import Mathlib
import Submission.Work.HP.MMDefs

namespace Work.HP.SstarAux

theorem dvd_mul_iff_dvd_div_gcd (ℓ Q : ℕ) (hℓ : 1 ≤ ℓ) (L : ℤ) :
    ((Q : ℤ) ∣ (ℓ : ℤ) * L) ↔ ((Q / Nat.gcd ℓ Q : ℕ) : ℤ) ∣ L := by
  set g : ℕ := Nat.gcd ℓ Q with hg
  set Q' : ℕ := Q / g with hQ'
  set ℓ' : ℕ := ℓ / g with hℓ'
  have hgpos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_left Q (by omega)
  have hgQ : g ∣ Q := by rw [hg]; exact Nat.gcd_dvd_right ℓ Q
  have hgℓ : g ∣ ℓ := by rw [hg]; exact Nat.gcd_dvd_left ℓ Q
  have hgne : (g : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hQeq : (Q : ℤ) = (g : ℤ) * (Q' : ℤ) := by
    rw [hQ', ← Nat.cast_mul, Nat.mul_comm, Nat.div_mul_cancel hgQ]
  have hℓeq : (ℓ : ℤ) = (g : ℤ) * (ℓ' : ℤ) := by
    rw [hℓ', ← Nat.cast_mul, Nat.mul_comm, Nat.div_mul_cancel hgℓ]
  have hcop : Nat.Coprime Q' ℓ' := by
    rw [hQ', hℓ']
    exact (Nat.coprime_div_gcd_div_gcd (m := ℓ) (n := Q) hgpos).symm
  have hiscop : IsCoprime (Q' : ℤ) (ℓ' : ℤ) := hcop.isCoprime
  rw [hQeq, hℓeq]
  rw [show (g : ℤ) * (ℓ' : ℤ) * L = (g : ℤ) * ((ℓ' : ℤ) * L) by ring]
  rw [mul_dvd_mul_iff_left hgne]
  exact ⟨fun h => hiscop.dvd_of_dvd_mul_left h,
    fun h => dvd_mul_of_dvd_right h (ℓ' : ℤ)⟩

end Work.HP.SstarAux
