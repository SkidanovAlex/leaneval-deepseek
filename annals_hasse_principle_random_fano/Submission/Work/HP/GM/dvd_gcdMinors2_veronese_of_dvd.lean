import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.NA.exists_lam_gcdMinors2
import Submission.Work.HP.EE.veronese_swap

set_option linter.unusedVariables false

namespace Work.HP.GM

theorem dvd_gcdMinors2_veronese_of_dvd (d n p e : ℕ) (hp : p.Prime) (x y : Fin (n + 1) → ℤ)
    (hx : ∃ i : Fin (n + 1), ¬ (p : ℤ) ∣ x i)
    (h : (p : ℤ) ^ e ∣ Work.HP.gcdMinors2 x y) :
    (p : ℤ) ^ e ∣ Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y) := by
  classical
  rw [Work.HP.NA.gcdMinors2_dvd_iff]
  intro m m'
  have hmin : ∀ i j : Fin (n + 1), (p : ℤ) ^ e ∣ (x i * y j - x j * y i) :=
    (Work.HP.NA.gcdMinors2_dvd_iff ((p : ℤ) ^ e) x y).mp h
  have hrel : ∀ i j : Fin (n + 1),
      ((x i : ZMod (p ^ e)) * (y j : ZMod (p ^ e))
        = (x j : ZMod (p ^ e)) * (y i : ZMod (p ^ e))) := by
    intro i j
    have h1 : (((x i * y j - x j * y i : ℤ)) : ZMod (p ^ e)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa [Nat.cast_pow] using hmin i j
    rw [Int.cast_sub, Int.cast_mul, Int.cast_mul] at h1
    exact sub_eq_zero.mp h1
  have hswap := veronese_swap (R := ZMod (p ^ e)) (fun i => (x i : ZMod (p ^ e)))
    (fun i => (y i : ZMod (p ^ e))) hrel d (fun i => (m.1 i : ℕ)) (fun i => (m'.1 i : ℕ)) m.2 m'.2
  have hmain : (((Work.HP.veronese d n x m * Work.HP.veronese d n y m'
      - Work.HP.veronese d n x m' * Work.HP.veronese d n y m : ℤ)) : ZMod (p ^ e)) = 0 := by
    rw [Int.cast_sub, Int.cast_mul, Int.cast_mul]
    simp only [Work.HP.veronese, Int.cast_prod, Int.cast_pow]
    rw [hswap, sub_self]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ e)).mp hmain
  simpa [Nat.cast_pow] using this

end Work.HP.GM
