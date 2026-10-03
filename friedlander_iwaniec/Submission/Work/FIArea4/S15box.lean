/-
# Area 4 / FI §15: the "size of the box" structural fact

The middle range (10.16) `X < d` and `4dX < |Δ(z₁,z₂)|` is non-empty only for *small* moduli
when `z₁, z₂` lie in the same polar box (5.14) of angle `2πθ`: the determinant bound (6.2)
`|Δ| ≤ 2πθ|z₁||z₂|` (proved as `absDelta_le_sector`) gives

  `4dX < |Δ| ≤ 4πθN`,  i.e.  `d·X < πθN`.

This is the "size of the box" saving of §15: the number of admissible `d` is at most
`πθN/X + 1`, uniformly in the pair.  It is what makes the trivial estimates of the non-primitive
and near-diagonal configurations affordable, and it is the reason the box's smallness `θ` enters
the counting in §15.
-/
import Mathlib
import Submission.Work.FITop.Defs
import Submission.Work.FITop3.Defs3
import Submission.Work.FIArea4.S15arith
import Submission.Work.FIArea4.absDelta_le_sector

namespace Work.FIArea4

open scoped BigOperators

/-- `θ ≤ 1` for every admissible set-up. -/
lemma theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  have hlogx : 1 < Real.log (Pa.x : ℝ) := log_x_gt_one Pa
  rw [Pa.hθ]
  have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt hlogx)
    (show -Pa.A' ≤ 0 by linarith [Pa.hA', Pa.hA])
  simpa [Real.rpow_zero] using h

/-- **(6.2)+cut, box form**: if `z₁, z₂` are in the same polar box (5.14) and `4dX < |Δ(z₁,z₂)|`
then `d·X < 4πθN`. -/
theorem d_mul_X_lt_four (Pa : Work.FITop.Params) (φ : ℝ) (X : ℕ) {z1 z2 : GaussianInt} {d : ℕ}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (hcut : 4 * d * X < Work.FIPlan.absDelta z1 z2) :
    (d : ℝ) * X < 4 * Real.pi * Pa.θ * Pa.N := by
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hN1 : 1 ≤ Pa.N := Pa.hN1
  have hN0 : 0 ≤ Pa.N := by linarith
  have hg1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ 2 * Pa.N := by
    have hle : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h1.2.2.1
    nlinarith
  have hg2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ 2 * Pa.N := by
    have hle : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h2.2.2.1
    nlinarith
  have hs1 : Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) ≤ Real.sqrt (2 * Pa.N) :=
    Real.sqrt_le_sqrt hg1
  have hs2 : Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) ≤ Real.sqrt (2 * Pa.N) :=
    Real.sqrt_le_sqrt hg2
  have hsq : Real.sqrt (2 * Pa.N) * Real.sqrt (2 * Pa.N) = 2 * Pa.N := by
    have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 * Pa.N by positivity)
    rw [sq] at h
    exact h
  have hprod : Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
        * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))
      ≤ Real.sqrt (2 * Pa.N) * Real.sqrt (2 * Pa.N) :=
    mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsec := absDelta_le_sector Pa φ h1 h2
  have hDelta : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := by
    calc ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
        ≤ 2 * Real.pi * Pa.θ * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
            * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := hsec
      _ = 2 * Real.pi * Pa.θ * (Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
            * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) := by ring
      _ ≤ 2 * Real.pi * Pa.θ * (Real.sqrt (2 * Pa.N) * Real.sqrt (2 * Pa.N)) := by
          apply mul_le_mul_of_nonneg_left hprod
          positivity
      _ = 4 * Real.pi * Pa.θ * Pa.N := by rw [hsq]; ring
  have hcast : ((4 * d * X : ℕ) : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    exact_mod_cast hcut
  have hcast' : ((4 * d * X : ℕ) : ℝ) = 4 * (d : ℝ) * (X : ℝ) := by push_cast; ring
  rw [hcast'] at hcast
  linarith

/-- **The "size of the box" saving of §15**: for a pair in the same polar box, an admissible
modulus obeys `d·X < 4πθN`; for `1 ≤ X` this reads `d < 4πθN/X`. -/
theorem d_mul_X_lt (Pa : Work.FITop.Params) (φ : ℝ) (X : ℕ) (hX1 : 1 ≤ X) {z1 z2 : GaussianInt}
    {d : ℕ}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (hcut : 4 * d * X < Work.FIPlan.absDelta z1 z2) :
    (d : ℝ) < 4 * Real.pi * Pa.θ * Pa.N / X := by
  have h := d_mul_X_lt_four Pa φ X h1 h2 hcut
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  rw [lt_div_iff₀ hX0]
  exact h

end Work.FIArea4
