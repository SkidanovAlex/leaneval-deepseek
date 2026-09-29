import Mathlib
import Submission.Work.CLift.bridge
import Submission.Work.CLift.q4_roots
import Submission.Work.CLift.phiC_modulus

namespace Work.CLift

open Work.CLift Submission.CDTPlan Metric

/-- Cast form of the division defining `yOf r = r²/(r-1)`. -/
lemma ofReal_yOf_div (r : ℝ) :
    (r : ℂ) ^ 2 / ((r : ℂ) - 1) = ((yOf r : ℝ) : ℂ) := by
  have h : ((r : ℂ) - 1) = ((r - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_pow, ← Complex.ofReal_div, yOf]

/-- If a lift `Φ` of `φ_C` takes at `z` the real value `x`, then `φ_C(z²) = yOf x = x²/(x-1)`:
indeed `x` and `Φ(-z)` have both sum and product equal to `φ_C(z²)`, so `φ_C(z²)·(x-1) = x²`. -/
lemma lift_eq_real {Φ : ℂ → ℂ}
    (hΦ : ∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = phiC (z ^ 2) ∧ Φ z * Φ (-z) = phiC (z ^ 2))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {x : ℝ} (hx : Φ z = (x : ℂ)) :
    phiC (z ^ 2) = ((yOf x : ℝ) : ℂ) := by
  have h1 : (x : ℂ) + Φ (-z) = phiC (z ^ 2) := by rw [← hx]; exact (hΦ z hz).1
  have h2 : (x : ℂ) * Φ (-z) = phiC (z ^ 2) := by rw [← hx]; exact (hΦ z hz).2
  have h3 : Φ (-z) = phiC (z ^ 2) - (x : ℂ) := by
    rw [eq_sub_iff_add_eq, add_comm]; exact h1
  have h4 : (x : ℂ) * (phiC (z ^ 2) - (x : ℂ)) = phiC (z ^ 2) := by rw [← h3]; exact h2
  have key : phiC (z ^ 2) * ((x : ℂ) - 1) = (x : ℂ) ^ 2 := by linear_combination h4
  have hne1 : (x : ℂ) ≠ 1 := by
    intro hh
    rw [hh] at key
    simp at key
  rw [eq_div_of_mul_eq (sub_ne_zero.mpr hne1) key]
  exact ofReal_yOf_div x

theorem Phi_ne_root (m n : ℕ) (ra rb rab r0 : ℤ) (hL : CLocation) (hN : CNumerics)
    (hM : HauptFacts) (hP : PsiCFacts) (hAdm : CAdm m n) (hRel : CRel m n ra rb rab r0)
    (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = phiC (z ^ 2) ∧ Φ z * Φ (-z) = phiC (z ^ 2))
    (hΦ0 : ∀ z ∈ ball (0 : ℂ) 1, Φ z = 0 → z = 0)
    (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) (hzr : 3.2e-4 < ‖z‖)
    (s1 s2 : ℝ) (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1) :
    Φ z ≠ (xRoot m n s1 s2 : ℂ) := by
  intro hcon
  -- `Φ z` is a real number, so `φ_C(z²) = yOf (xRoot m n s1 s2)`
  have hcr : phiC (z ^ 2) = ((yOf (xRoot m n s1 s2) : ℝ) : ℂ) :=
    lift_eq_real hΦ hz hcon
  have hnorm : ‖phiC (z ^ 2)‖ = |yOf (xRoot m n s1 s2)| := by
    rw [hcr]; simp
  have hz1 : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
  have hz2le : ‖z ^ 2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  obtain ⟨hup, hlow⟩ := phiC_modulus hM hP hN
  obtain ⟨hmm, hpp, hpm, hmp⟩ := hL m n hAdm.1 hAdm.2.1 hAdm.2.2.1 hAdm.2.2.2
  -- the three large values of `yOf (xRoot …)` exceed the bound `700000` for `‖phiC‖`
  rcases hs1 with h1 | h1 <;> rcases hs2 with h2 | h2
  · rw [h1, h2] at hnorm
    have h := hup (z ^ 2) hz2le
    rw [hnorm] at h
    linarith
  · rw [h1, h2] at hnorm
    have h := hup (z ^ 2) hz2le
    rw [hnorm] at h
    linarith
  · rw [h1, h2] at hnorm
    have h := hup (z ^ 2) hz2le
    rw [hnorm] at h
    linarith
  · -- `|yOf (xRoot m n (-1) (-1))| ≤ 10⁻²⁰` forces `‖z‖ ≤ 10⁻³·⁵ < 3.2·10⁻⁴`
    rw [h1, h2] at hnorm
    have hle : ‖phiC (z ^ 2)‖ ≤ 1 / 10 ^ 20 := by rw [hnorm]; exact hmm
    have hlo := hlow (z ^ 2) hz2le
    rw [norm_pow] at hlo
    have hzsq : ‖z‖ ^ 2 ≤ 1 / 10 ^ 7 := by nlinarith
    have hgt : (1 / 10 ^ 7 : ℝ) < ‖z‖ ^ 2 := by
      have hprod : 0 < (‖z‖ - 3.2e-4) * (‖z‖ + 3.2e-4) := by
        apply mul_pos <;> linarith [norm_nonneg z, hzr]
      have h32 : (1 / 10 ^ 7 : ℝ) < (3.2e-4) ^ 2 := by norm_num
      nlinarith [hprod, h32]
    linarith

end Work.CLift
