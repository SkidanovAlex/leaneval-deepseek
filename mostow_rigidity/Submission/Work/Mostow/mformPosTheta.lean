import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.StabHoroForm

/-!
# Positivity of the Minkowski form on the orthogonal complement of two null vectors

Let `a ≠ b` be two boundary points (`Sph n`).  The two null vectors `theta a = (a,1)` and
`theta b = (b,1)` span a hyperbolic (signature `(1,1)`) plane, so their common orthogonal
complement in `ℝ^{Fin n ⊕ Fin 1}` (equipped with the Minkowski form `mform`) is positive definite.

The proof is a two-line computation.  Writing `z = (u,t)` with `u = hspat z : E n` and
`t = htime z`, the condition `mform z (theta a) = 0` reads `⟪u,a⟫ = t`; since `‖a‖ = 1` this gives

`mform z z = ‖u‖² - t² = ‖u - t • a‖² ≥ 0`,

and the same with `b` in place of `a`.  If `mform z z = 0` then both `u = t • a` and `u = t • b`,
whence `t • (a - b) = 0`; as `a ≠ b` this forces `t = 0` and then `u = 0`, i.e. `z = 0`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- The Minkowski form of `z` against itself in spatial/time coordinates. -/
lemma mformPos_hspat_self (z : Fin n ⊕ Fin 1 → ℝ) :
    mform z z = ‖hspat z‖ ^ 2 - htime z ^ 2 := by
  rw [mform_eq, real_inner_self_eq_norm_sq]; ring

/-- Pairing with the null vector `theta ξ` in spatial/time coordinates. -/
lemma mformPos_theta_eq (z : Fin n ⊕ Fin 1 → ℝ) (ξ : E n) :
    mform z (theta ξ) = inner ℝ (hspat z) ξ - htime z := by
  rw [mform_eq, hspat_theta, htime_theta, mul_one]

/-- If `‖a‖ = 1` and `⟪u,a⟫ = t` then `‖u - t • a‖ ^ 2 = ‖u‖ ^ 2 - t ^ 2`. -/
lemma mformPos_norm_sub_smul_sq (u a : E n) (t : ℝ) (hna : ‖a‖ = 1)
    (hia : inner ℝ u a = t) :
    ‖u - t • a‖ ^ 2 = ‖u‖ ^ 2 - t ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, hia, norm_smul, hna, mul_one, Real.norm_eq_abs,
    sq_abs]
  ring

lemma mformPosTheta {n : ℕ} {a b : Submission.Mostow.E n} (ha : a ∈ Submission.Mostow.Sph n)
    (hb : b ∈ Submission.Mostow.Sph n) (hab : a ≠ b)
    {z : Fin n ⊕ Fin 1 → ℝ} (hza : Work.Mostow.mform z (Work.Mostow.theta a) = 0)
    (hzb : Work.Mostow.mform z (Work.Mostow.theta b) = 0) (hz : z ≠ 0) :
    0 < Work.Mostow.mform z z := by
  have hna : ‖a‖ = 1 := (mem_Sph_iff a).1 ha
  have hib : inner ℝ (hspat z) b = htime z := by
    have h := hzb; rw [mformPos_theta_eq] at h; linarith
  have hia : inner ℝ (hspat z) a = htime z := by
    have h := hza; rw [mformPos_theta_eq] at h; linarith
  have hsq : mform z z = ‖hspat z - htime z • a‖ ^ 2 := by
    rw [mformPos_hspat_self, mformPos_norm_sub_smul_sq (hna := hna) (hia := hia)]
  have hnn : 0 ≤ mform z z := by rw [hsq]; positivity
  refine lt_of_le_of_ne hnn ?_
  intro hzero
  exfalso
  have hpa : hspat z = htime z • a := by
    have h1 : ‖hspat z - htime z • a‖ = 0 := by
      have : (‖hspat z - htime z • a‖) ^ 2 = 0 := by rw [← hsq]; exact hzero.symm
      exact sq_eq_zero_iff.mp this
    exact sub_eq_zero.mp (norm_eq_zero.mp h1)
  have hpb : hspat z = htime z • b := by
    have hsqb : mform z z = ‖hspat z - htime z • b‖ ^ 2 := by
      rw [mformPos_hspat_self, mformPos_norm_sub_smul_sq (hna := (mem_Sph_iff b).1 hb) (hia := hib)]
    have h1 : ‖hspat z - htime z • b‖ = 0 := by
      have : (‖hspat z - htime z • b‖) ^ 2 = 0 := by rw [← hsqb]; exact hzero.symm
      exact sq_eq_zero_iff.mp this
    exact sub_eq_zero.mp (norm_eq_zero.mp h1)
  have hsub : htime z • (a - b) = 0 := by
    rw [smul_sub, ← hpa, ← hpb, sub_self]
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have ht0 : htime z = 0 := by
    rcases smul_eq_zero.mp hsub with h | h
    · exact h
    · exact absurd h hne
  have hu0 : hspat z = 0 := by rw [hpa, ht0, zero_smul]
  apply hz
  funext j
  rcases j with i | k
  · have : hspat z i = 0 := by rw [hu0]; simp
    exact this
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    simpa [htime] using ht0

end

end Work.Mostow
