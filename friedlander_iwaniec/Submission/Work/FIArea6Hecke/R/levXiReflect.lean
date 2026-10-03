import Mathlib
import Submission.Work.FIArea6Hecke.R.levelHeckeDefs
import Submission.Work.FIArea5.S16Hecke.heckeFE_defs

namespace Work.FIArea6Hecke.R

open scoped ComplexConjugate

/-- `star` of a nonnegative real base raised to a complex power: `conj (B^z) = B^(conj z)`. -/
lemma star_thetaB_cpow {B : ℝ} (hB : 0 ≤ B) (z : ℂ) :
    star ((B : ℂ) ^ z) = (B : ℂ) ^ (star z) := by
  simpa only [starRingEnd_apply] using
    Work.FIArea5.S16Hecke.starRingEnd_cpow_ofReal (u := B) hB z

theorem levXiReflect (B : ℝ) (hB : 0 < B) (f : ℝ → ℂ) (m : ℕ) (A : ℂ)
    (hconst : A * star A * ((B : ℂ) ^ ((m : ℂ) + 1)) = 1) :
    ∀ t : ℂ, thetaXi B f m A t = A * ((B : ℂ) ^ ((m : ℂ) + 1 - t)) *
        star (thetaXi B f m A ((m : ℂ) + 1 - star t)) := by
  have hB0 : (B : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt hB
  intro t
  have hs : (m : ℂ) + 1 - ((m : ℂ) + 1 - star t) = star t := by ring
  -- `conj (Ξ(m+1-conj t)) = E(t) + conj A · B^t · A(t)`
  have hkey : star (thetaXi B f m A ((m : ℂ) + 1 - star t))
      = thetaE B f m t + star A * (B : ℂ) ^ t * thetaA B f t := by
    rw [thetaXi]
    simp only [star_add, star_mul]
    rw [star_thetaA B f m t, star_thetaE B f m t, hs,
      star_thetaB_cpow hB.le (star t), star_star]
    ring
  rw [hkey, thetaXi]
  -- `B^{m+1-t} · B^t = B^{m+1}`
  have hpow : (B : ℂ) ^ ((m : ℂ) + 1 - t) * (B : ℂ) ^ t
      = (B : ℂ) ^ ((m : ℂ) + 1) := by
    rw [← Complex.cpow_add ((m : ℂ) + 1 - t) t hB0]
    congr 1
    ring
  rw [mul_add]
  rw [show A * ((B : ℂ) ^ ((m : ℂ) + 1 - t)) *
        (star A * (B : ℂ) ^ t * thetaA B f t)
        = (A * star A * (((B : ℂ) ^ ((m : ℂ) + 1 - t)) * (B : ℂ) ^ t)) *
          thetaA B f t by ring]
  rw [hpow, hconst, one_mul]
  ring

end Work.FIArea6Hecke.R
