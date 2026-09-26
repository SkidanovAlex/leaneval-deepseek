import Mathlib
import Submission.Work.SG.SGRepDefs

namespace Work.SG.CzAux

open Work.SG.Data

/-- Combining integer quotients: if `n` divides each of `p, q, r`, then the quotient of a
linear combination is the linear combination of the quotients. -/
theorem mul_ediv_lin3 (a b c p q r n : ℤ) (hp : n ∣ p) (hq : n ∣ q) (hr : n ∣ r) :
    a * (p / n) + b * (q / n) + c * (r / n) = (a * p + b * q + c * r) / n := by
  rw [← Int.mul_ediv_assoc a hp, ← Int.mul_ediv_assoc b hq, ← Int.mul_ediv_assoc c hr]
  rw [Int.add_ediv_of_dvd_left (dvd_add (dvd_mul_of_dvd_right hp a) (dvd_mul_of_dvd_right hq b)),
      Int.add_ediv_of_dvd_left (dvd_mul_of_dvd_right hp a)]

theorem mulV_ediv (A : Work.SG.Data.M3) (v : Work.SG.Data.V3) (n : ℤ)
    (h : Work.SG.Data.V3.dvd n v = true) :
    Work.SG.Data.M3.mulV A (Work.SG.Data.V3.ediv v n)
      = Work.SG.Data.V3.ediv (Work.SG.Data.M3.mulV A v) n := by
  unfold Work.SG.Data.V3.dvd at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hx, hy⟩, hz⟩ := h
  rw [beq_iff_eq] at hx hy hz
  obtain ⟨vx, vy, vz⟩ := v
  have dx : n ∣ vx := Int.dvd_of_emod_eq_zero hx
  have dy : n ∣ vy := Int.dvd_of_emod_eq_zero hy
  have dz : n ∣ vz := Int.dvd_of_emod_eq_zero hz
  simp only [Work.SG.Data.M3.mulV, Work.SG.Data.V3.ediv, Work.SG.Data.V3.mk.injEq]
  exact ⟨mul_ediv_lin3 A.a A.b A.c vx vy vz n dx dy dz,
         mul_ediv_lin3 A.d A.e A.f vx vy vz n dx dy dz,
         mul_ediv_lin3 A.g A.h A.i vx vy vz n dx dy dz⟩

end Work.SG.CzAux
