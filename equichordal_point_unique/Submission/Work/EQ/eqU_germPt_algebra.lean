import Mathlib
import Submission.Work.EQ.Defs

namespace Work.EQ

/-- Explicit point algebra for the half-map `eqU` (`Submission/Work/EQ/Defs.lean`).  Let
`a > 0`, `p < 0 < q - p`, `0 < s - q` be real and suppose
`(q - p) * (s - q) + a * q * (s - p) * √(1 + q²) = 0` (the germ recurrence with `p = h t`,
`q = h (λt)`, `s = h (λ²t)`).  Then `eqU a` maps the point with coordinates
`(a q/(q-p) - a/2, a p q/(q-p))` to the point with coordinates `(a s/(s-q) - a/2, a q s/(s-q))`.

Proof outline: `P - a/2 = c (1 + i q)` with `c = a p/(q-p) < 0`, so `‖P - a/2‖ = -c √(1+q²)` and
`(P - a/2)/‖P - a/2‖ = -(1 + i q)/√(1+q²)`.  Hence `eqU a P = -P - (1+iq)/√(1+q²)`, whose real
part is `-a q/(q-p) + a/2 - 1/√(1+q²)` and imaginary part `-a p q/(q-p) - q/√(1+q²)`.  The
recurrence is equivalent to `1/√(1+q²) = -a p/(q-p) - a s/(s-q)`; substituting gives the claim. -/
theorem eqU_germPt_algebra {a p q s : ℝ} (ha : 0 < a) (hp : p < 0)
    (hqp : 0 < q - p) (hsq : 0 < s - q)
    (hFE : (q - p) * (s - q) + a * q * (s - p) * Real.sqrt (1 + q ^ 2) = 0) :
    eqU a ((a * q / (q - p) - a / 2 : ℂ) + (a * p * q / (q - p) : ℂ) * Complex.I)
      = ((a * s / (s - q) - a / 2 : ℂ) + (a * q * s / (s - q) : ℂ) * Complex.I) := by
  have hqp' : q - p ≠ 0 := ne_of_gt hqp
  have hsq' : s - q ≠ 0 := ne_of_gt hsq
  have hqpc : ((q:ℂ) - (p:ℂ)) ≠ 0 := by rw [← Complex.ofReal_sub]; exact_mod_cast hqp'
  have hsqc : ((s:ℂ) - (q:ℂ)) ≠ 0 := by rw [← Complex.ofReal_sub]; exact_mod_cast hsq'
  set Z : ℂ := (a * q / (q - p) - a / 2 : ℂ) + (a * p * q / (q - p) : ℂ) * Complex.I with hZ
  set W : ℂ := (a * s / (s - q) - a / 2 : ℂ) + (a * q * s / (s - q) : ℂ) * Complex.I with hW
  set c : ℝ := a * p / (q - p) with hcdef
  have hcneg : c < 0 := by
    rw [hcdef]; exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha hp) hqp
  have hcne : c ≠ 0 := ne_of_lt hcneg
  have hcnec : (c:ℂ) ≠ 0 := by exact_mod_cast hcne
  set rn : ℝ := Real.sqrt (1 + q^2) with hrndef
  have hrnpos : 0 < rn := by rw [hrndef]; exact Real.sqrt_pos.mpr (by positivity)
  have hrnne : rn ≠ 0 := ne_of_gt hrnpos
  have hrnnec : (rn:ℂ) ≠ 0 := by exact_mod_cast hrnne
  have hz : Z - ((a/2 : ℝ) : ℂ) = (c:ℂ) * (1 + (q:ℂ) * Complex.I) := by
    rw [hZ, hcdef]; push_cast; field_simp; ring
  have hure : (Z - ((a/2 : ℝ) : ℂ)).re = c := by rw [hz]; simp
  have huim : (Z - ((a/2 : ℝ) : ℂ)).im = c * q := by rw [hz]; simp
  have hns : ‖Z - ((a/2 : ℝ) : ℂ)‖^2 = c^2 * (1 + q^2) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hure, huim]; ring
  have hnorm : ‖Z - ((a/2 : ℝ) : ℂ)‖ = -c * rn := by
    have h1 : ‖Z - ((a/2 : ℝ) : ℂ)‖ = Real.sqrt (c^2 * (1+q^2)) := by
      rw [← Real.sqrt_sq (norm_nonneg (Z - ((a/2 : ℝ) : ℂ))), hns]
    rw [h1, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_neg hcneg, hrndef]
  have hmain : rn * (-a * q * (s - p)) = (q - p) * (s - q) := by
    linarith [hFE]
  have hx : -a * p / (q - p) - a * s / (s - q) = (-a * q * (s - p)) / ((q - p) * (s - q)) := by
    field_simp; ring
  have key : rn * (-a * p / (q - p) - a * s / (s - q)) = 1 := by
    rw [hx, mul_div_assoc', hmain, div_self (mul_ne_zero hqp' hsq')]
  have hrel : rn⁻¹ = -a * p / (q - p) - a * s / (s - q) := inv_eq_of_mul_eq_one_right key
  have hdivinv : ∀ z : ℂ, z / (rn:ℂ) = z * ((rn⁻¹ : ℝ) : ℂ) := by
    intro z; rw [div_eq_mul_inv, Complex.ofReal_inv]
  have hnc : ((‖Z - ((a/2 : ℝ) : ℂ)‖:ℝ):ℂ) = (-(c:ℂ)) * (rn:ℂ) := by
    rw [hnorm]; push_cast; ring
  have hdiv : (Z - ((a/2 : ℝ) : ℂ)) / ((‖Z - ((a/2 : ℝ) : ℂ)‖:ℝ):ℂ)
      = -(1 + (q:ℂ) * Complex.I)/(rn:ℂ) := by
    rw [hnc, hz]
    have hprod : (-(c:ℂ)) * (rn:ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hcnec) hrnnec
    field_simp
  have hfinal : -Z + -(1 + (q:ℂ) * Complex.I)/(rn:ℂ) = W := by
    rw [hdivinv, hrel, hZ, hW]
    push_cast
    field_simp
    ring
  rw [eqU, hdiv]
  exact hfinal

end Work.EQ
