import Mathlib
import Submission.Work.CNum.exp_phi_eq
import Submission.Work.CNum.ArcsinChord
import Submission.Work.CNum.phi_strictMono

/-!
# `Work.CNum.PhiChord`

On the cusp arc `C₁` of the unit circle parametrised by `θ ∈ (-α, α)` (`α = alpR`), the boundary
value of the contour map is `ψ_C(e^{iθ}) = (3/4) exp(i φ(θ))` with `φ = phiR` (`exp_phi_eq`,
`phiChord_psiC_eq_smul_Wfun`).  Hence the chord length of the `ψ_C`-image of two points is exactly

`(4/3) ‖ψ_C(e^{iθ₂}) - ψ_C(e^{iθ₁})‖ = ‖exp(i φ(θ₂)) - exp(i φ(θ₁))‖ = 2 sin((φ(θ₂)-φ(θ₁))/2)`,

so `φ(θ₂) - φ(θ₁) = 2 arcsin(D/2)` where `D` is the left-hand side, and the elementary chord bound
`ArcsinChord` (`2 arcsin u ≤ 2u + u³/3 + u⁵/5` on `[0, 1/4]`) gives

`φ(θ₂) - φ(θ₁) ≤ D + D³/12 + D⁵/160`

whenever `D ≤ 1/2` (which forces `D/2 ≤ 1/4`).  The hypothesis `D ≤ 1/2` is also what rules out
the "long way round": `φ` maps `(-α, α)` onto an interval of length `π + α ≤ 3π/2`, so a chord of
length `≤ 1/2` cannot come from `φ(θ₂) - φ(θ₁) ≥ π` (there `2 sin(Δ/2) ≥ √2`).
-/

namespace Work.CNum

/-- `ψ_C = (3/4) · W` (the definitional identity `√ = (·)^{1/2}` and `ring`); local copy of
`Work.CNum.psiC_eq_smul_Wfun`. -/
private lemma phiChord_psiC_eq_smul_Wfun (z : ℂ) :
    Submission.CDTPlan.psiC z = (3 / 4) * Wfun z := by
  unfold Submission.CDTPlan.psiC Submission.CDTPlan.lune Wfun Ra AR BR dR cR
  rw [Complex.sqrt]
  push_cast
  ring_nf

/-- The chord length of two points of the unit circle: `‖e^{ia} - e^{ib}‖ = 2 |sin ((a-b)/2)|`. -/
lemma phiChord_chord_norm (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖
      = 2 * |Real.sin ((a - b) / 2)| := by
  have hfac : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hfac, Complex.norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- Upper bound for `φ = phiR`: `φ(θ) < 3π/2 + α/2` on the arc. -/
private lemma phiChord_phiR_lt {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    phiR θ < 3 * Real.pi / 2 + alpR / 2 := by
  have h1 : θ / 2 < alpR / 2 := by linarith [h.2]
  have h2 : Real.arctan (QR θ / PR θ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  simp only [phiR]
  linarith

/-- Lower bound for `φ = phiR`: `π/2 - α/2 < φ(θ)` on the arc. -/
private lemma phiChord_phiR_gt {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Real.pi / 2 - alpR / 2 < phiR θ := by
  have h1 : -alpR / 2 < θ / 2 := by linarith [h.1]
  have h2 : -(Real.pi / 2) < Real.arctan (QR θ / PR θ) := Real.neg_pi_div_two_lt_arctan _
  simp only [phiR]
  linarith

/-- `α = arccos γ ≤ π/2` because `γ ≥ 0`. -/
private lemma phiChord_alpR_le : alpR ≤ Real.pi / 2 :=
  (Real.arccos_le_pi_div_two (x := gamR)).mpr (by norm_num [gamR, AR, cR])

theorem PhiChord {θ₁ θ₂ : ℝ} (h1 : θ₁ ∈ Set.Ioo (-Work.CNum.alpR) Work.CNum.alpR) (h2 : θ₂ ∈ Set.Ioo (-Work.CNum.alpR) Work.CNum.alpR) (h12 : θ₁ ≤ θ₂) (hD : (4 / 3) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ))) - Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖ ≤ 1 / 2) : Work.CNum.phiR θ₂ - Work.CNum.phiR θ₁ ≤ (4 / 3) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ))) - Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖ + ((4 / 3) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ))) - Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖) ^ 3 / 12 + ((4 / 3) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ))) - Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖) ^ 5 / 160 := by
  set e₁ : ℂ := Complex.exp (Complex.I * (θ₁ : ℂ)) with he₁
  set e₂ : ℂ := Complex.exp (Complex.I * (θ₂ : ℂ)) with he₂
  set U : ℝ := ‖Wfun e₂ - Wfun e₁‖ with hU
  -- The `(4/3)‖ψ_C ...‖` occurring in the statement is exactly `U`.
  have hKeyE : (4 / 3) * ‖Submission.CDTPlan.psiC e₂ - Submission.CDTPlan.psiC e₁‖ = U := by
    rw [hU, phiChord_psiC_eq_smul_Wfun e₂, phiChord_psiC_eq_smul_Wfun e₁]
    rw [show (3 / 4 : ℂ) * Wfun e₂ - (3 / 4) * Wfun e₁
        = (3 / 4) * (Wfun e₂ - Wfun e₁) by ring]
    rw [norm_mul, show ‖((3 : ℂ) / 4)‖ = 3 / 4 by norm_num]
    ring
  have hKey : (4 / 3) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ))) -
        Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖ = U := by
    rw [← he₁, ← he₂]
    exact hKeyE
  have hDhalf : U ≤ 1 / 2 := by
    rw [← hKeyE]
    exact hD
  -- Monotonicity of `φ` on the arc.
  have hφle : phiR θ₁ ≤ phiR θ₂ := phi_strictMono.monotoneOn h1 h2 h12
  -- The values of `Wfun` at the two points.
  have hW₁ : Wfun e₁ = Complex.exp (Complex.I * (phiR θ₁ : ℂ)) := by
    rw [he₁]; exact (exp_phi_eq h1).symm
  have hW₂ : Wfun e₂ = Complex.exp (Complex.I * (phiR θ₂ : ℂ)) := by
    rw [he₂]; exact (exp_phi_eq h2).symm
  -- The range of `φ` on the arc has length `π + α ≤ 3π/2`.
  have hΔlt : phiR θ₂ - phiR θ₁ < 3 * Real.pi / 2 := by
    have hlt := phiChord_phiR_lt h2
    have hgt := phiChord_phiR_gt h1
    have halp := phiChord_alpR_le
    linarith
  -- `U` is the chord length `2 sin(Δ/2)`.
  have hUval : U = 2 * Real.sin ((phiR θ₂ - phiR θ₁) / 2) := by
    rw [hU, hW₂, hW₁, phiChord_chord_norm]
    congr 1
    apply abs_of_nonneg
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · linarith [hΔlt, Real.pi_pos]
  -- The chord is short, so `Δ/2 ≤ π/2` (otherwise `2 sin(Δ/2) ≥ √2 > 1/2`).
  have hhalf_le : (phiR θ₂ - phiR θ₁) / 2 ≤ Real.pi / 2 := by
    by_contra hcon
    have hcon' : Real.pi / 2 < (phiR θ₂ - phiR θ₁) / 2 := not_le.mp hcon
    have hΔu : (phiR θ₂ - phiR θ₁) / 2 ≤ 3 / 4 * Real.pi := by linarith [hΔlt]
    have hsin_ge : Real.sqrt 2 / 2 ≤ Real.sin ((phiR θ₂ - phiR θ₁) / 2) := by
      have hx1 : Real.pi / 4 ≤ Real.pi - (phiR θ₂ - phiR θ₁) / 2 := by linarith
      have hx2 : Real.pi - (phiR θ₂ - phiR θ₁) / 2 ≤ Real.pi / 2 := by linarith
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4)
        (y := Real.pi - (phiR θ₂ - phiR θ₁) / 2) (by linarith [Real.pi_pos]) hx2 hx1
      rwa [Real.sin_pi_sub, Real.sin_pi_div_four] at h
    have hsqrt : (1 / 2 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (x := 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]; norm_num
    rw [hUval] at hDhalf
    linarith
  -- Hence `φ(θ₂) - φ(θ₁) = 2 arcsin (U/2)`.
  have harc : 2 * Real.arcsin (U / 2) = phiR θ₂ - phiR θ₁ := by
    have hsin_eq : Real.sin ((phiR θ₂ - phiR θ₁) / 2) = U / 2 := by rw [hUval]; ring
    have hlow : -(Real.pi / 2) ≤ (phiR θ₂ - phiR θ₁) / 2 := by linarith
    have hmid : Real.arcsin (U / 2) = (phiR θ₂ - phiR θ₁) / 2 := by
      rw [← hsin_eq]
      exact Real.arcsin_sin hlow hhalf_le
    linarith
  -- The elementary chord bound.
  rw [hKey, ← harc]
  have hU0 : 0 ≤ U := norm_nonneg _
  have hquarter : U / 2 ≤ 1 / 4 := by linarith
  have h0 : 0 ≤ U / 2 := by linarith
  have hchord := ArcsinChord h0 hquarter
  have h3 : (U / 2) ^ 3 / 3 ≤ U ^ 3 / 12 := by
    rw [div_pow]
    nlinarith [mul_nonneg hU0 (mul_nonneg hU0 hU0)]
  have h5 : (U / 2) ^ 5 / 5 = U ^ 5 / 160 := by ring
  linarith

end Work.CNum
