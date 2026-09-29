/-
# The `ℓ²` solution of the dual equation from a reducible cocycle (`TMPuig`)

Let `B : ℝ → SL(2,ℝ)` be `1`-periodic, analytic, of determinant `1`, and suppose it
conjugates the almost Mathieu cocycle to a constant rotation:
`B (x+α) * tmR λ E x = rot c * B x` (with `c` in turns).

We prove that then the *dual* almost Mathieu equation (coupling `1/λ`, phase `c`,
energy `E/λ`)

`u (n+1) + u (n-1) + (2/λ) cos (2π (nα + c)) u n = (E/λ) u n`

has a nonzero `ℓ²(ℤ)` solution.

The construction: `w = (1,-i)` is an eigenvector of `rot c` with eigenvalue
`e^{2πic}`, so `x ↦ B x⁻¹ *ᵥ w` is `1`-periodic (`det B = 1`), and its first
component `V x = B x 1 1 + i * B x 0 1` is never zero.  The conjugacy turns the
one-step relation `tmR λ E x *ᵥ (B x⁻¹ *ᵥ w) = e^{2πic} *ᵥ (B (x+α)⁻¹ *ᵥ w)` into
the second order equation

`e^{2πic} V (x+α) + e^{-2πic} V (x-α) + 2λ cos (2πx) V x = E V x`

for the periodic function `V` (`dual_functional`).  Taking Fourier coefficients
(`dualV_cF_recurrence`) gives the dual equation, and Parseval
(`dualV_parseval`) gives the `ℓ²` property together with nontriviality: `V` is
continuous, periodic and everywhere nonzero, so the `L²` norm of `V` is positive
and some Fourier coefficient is nonzero.
-/
import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMPuig.Defs
import Submission.Work.TMPuig.DualDefs
import Submission.Work.TMPuig.FourierAux
import Submission.Work.TMPuig.dualV_cF_recurrence
import Submission.Work.TMPuig.dualV_parseval

open Matrix
open Set

noncomputable section

namespace Work.TMPuig

/-! ## 1. The complexified cocycle and the eigenvector `(1,-i)` of `rot c` -/

theorem dualC_mul (M N : Matrix (Fin 2) (Fin 2) ℝ) : dualC (M * N) = dualC M * dualC N := by
  ext i j
  simp only [dualC, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

theorem dualC_det (M : Matrix (Fin 2) (Fin 2) ℝ) : (dualC M).det = ((M.det : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [dualC, Matrix.map_apply]
  push_cast
  ring

theorem dualC_rot (c : ℝ) :
    dualC (Work.TMContract.rot c)
      = !![(Real.cos (2 * Real.pi * c) : ℂ), -(Real.sin (2 * Real.pi * c) : ℂ);
           (Real.sin (2 * Real.pi * c) : ℂ), (Real.cos (2 * Real.pi * c) : ℂ)] := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [dualC, Work.TMContract.rot]

theorem dualE_eq (c : ℝ) :
    dualE c = (Real.cos (2 * Real.pi * c) : ℂ) + (Real.sin (2 * Real.pi * c) : ℂ) * Complex.I := by
  rw [dualE, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem dualE_mul_negI (c : ℝ) :
    dualE c * (-Complex.I)
      = (Real.sin (2 * Real.pi * c) : ℂ) - (Real.cos (2 * Real.pi * c) : ℂ) * Complex.I := by
  rw [dualE, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-- `rot c` acts on the eigenvector `dualW = (1,-i)` by the scalar `e^{2πic}`. -/
theorem rot_mulVec_w (c : ℝ) : dualC (Work.TMContract.rot c) *ᵥ dualW = dualE c • dualW := by
  rw [dualC_rot]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, dualW, Fin.sum_univ_two]
  · rw [dualE_eq]; push_cast; ring
  · rw [show -(dualE c * Complex.I) = dualE c * (-Complex.I) by ring, dualE_mul_negI]
    push_cast; ring

/-! ## 2. The vector `dualU B x = B x⁻¹ *ᵥ dualW` and the one-step relation -/

/-- `dualU B x = B x⁻¹ *ᵥ dualW` (written out using `det B x = 1`). -/
theorem dualC_mulVec_dualU (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hdet : ∀ x, (B x).det = 1) (x : ℝ) : dualC (B x) *ᵥ dualU B x = dualW := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, dualU, dualV, dualW, dualC, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  · have h := hdet x
    rw [Matrix.det_fin_two] at h
    push_cast
    ring_nf
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_one]
    exact congrArg Complex.ofReal h
  · have h := hdet x
    rw [Matrix.det_fin_two] at h
    push_cast
    ring_nf
    rw [show (↑(B x 1 0) * Complex.I * ↑(B x 0 1) - ↑(B x 1 1) * Complex.I * ↑(B x 0 0))
        = -((↑(B x 0 0 * B x 1 1 - B x 0 1 * B x 1 0) : ℂ) * Complex.I) by push_cast; ring, h]
    simp

/-- The conjugacy, complexified. -/
theorem dual_conj_complex {α lam E c : ℝ} {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hconj : ∀ x, B (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot c * B x) (x : ℝ) :
    dualC (B (x + α)) * dualC (Work.TMContract.tmR lam E x)
      = dualC (Work.TMContract.rot c) * dualC (B x) := by
  rw [← dualC_mul, ← dualC_mul, hconj x]

/-- One step of the duality: `tmR λ E x *ᵥ (B x⁻¹ *ᵥ w) = e^{2πic} *ᵥ (B (x+α)⁻¹ *ᵥ w)`. -/
theorem dual_step {α lam E c : ℝ} {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ x, (B x).det = 1)
    (hconj : ∀ x, B (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot c * B x) (x : ℝ) :
    dualC (Work.TMContract.tmR lam E x) *ᵥ dualU B x = dualE c • dualU B (x + α) := by
  refine Matrix.mulVec_injective_of_isUnit (A := dualC (B (x + α))) ?_ ?_
  · rw [Matrix.isUnit_iff_isUnit_det, dualC_det, hdet, Complex.ofReal_one]
    exact isUnit_one
  · have hL : dualC (B (x + α)) *ᵥ (dualC (Work.TMContract.tmR lam E x) *ᵥ dualU B x)
        = dualE c • dualW := by
      rw [Matrix.mulVec_mulVec, dual_conj_complex hconj x, ← Matrix.mulVec_mulVec,
        dualC_mulVec_dualU B hdet x, rot_mulVec_w]
    have hR : dualC (B (x + α)) *ᵥ (dualE c • dualU B (x + α)) = dualE c • dualW := by
      rw [Matrix.mulVec_smul, dualC_mulVec_dualU B hdet (x + α)]
    rw [hL, hR]

theorem mulVec_tmR_zero (lam E x : ℝ) (v : Fin 2 → ℂ) :
    (dualC (Work.TMContract.tmR lam E x) *ᵥ v) 0
      = ((E - 2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * v 0 - v 1 := by
  simp [Matrix.mulVec, dotProduct, dualC, Work.TMContract.tmR, Fin.sum_univ_two]
  ring

theorem mulVec_tmR_one (lam E x : ℝ) (v : Fin 2 → ℂ) :
    (dualC (Work.TMContract.tmR lam E x) *ᵥ v) 1 = v 0 := by
  simp [Matrix.mulVec, dotProduct, dualC, Work.TMContract.tmR, Fin.sum_univ_two]

/-! ## 3. The Bloch equation for `V` -/

/-- The one-dimensional (`V`) form of `dual_step`. -/
theorem dual_functional {α lam E c : ℝ} {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ x, (B x).det = 1)
    (hconj : ∀ x, B (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot c * B x) (x : ℝ) :
    dualE c * dualV B (x + α) + (dualE c)⁻¹ * dualV B (x - α)
      + ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * dualV B x
      = (E : ℂ) * dualV B x := by
  have h0 : ((E - 2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * (dualU B x) 0 - (dualU B x) 1
      = dualE c * (dualU B (x + α)) 0 := by
    have h := congrFun (dual_step hdet hconj x) 0
    rw [mulVec_tmR_zero] at h
    simpa only [Pi.smul_apply, smul_eq_mul] using h
  have h1 : ∀ y, (dualU B y) 0 = dualE c * (dualU B (y + α)) 1 := by
    intro y
    have h := congrFun (dual_step hdet hconj y) 1
    rw [mulVec_tmR_one] at h
    simpa only [Pi.smul_apply, smul_eq_mul] using h
  simp only [dualU_zero] at h0
  have h1' : ∀ y, dualV B y = dualE c * (dualU B (y + α)) 1 := by
    intro y; rw [← dualU_zero B y]; exact h1 y
  have h1x : dualV B (x - α) = dualE c * (dualU B x) 1 := by
    have := h1' (x - α)
    simpa [sub_add_cancel] using this
  have hV1 : (dualU B x) 1 = (dualE c)⁻¹ * dualV B (x - α) := by
    rw [h1x, ← mul_assoc, inv_mul_cancel₀ (dualE_ne_zero c), one_mul]
  rw [hV1] at h0
  rw [h0.symm]
  push_cast
  ring

/-! ## 4. Continuity, periodicity and nonvanishing of `V` -/

theorem continuous_dualV {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hB : ∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) univ) : Continuous (dualV B) := by
  have h11 : Continuous (fun x : ℝ => B x 1 1) := continuousOn_univ.mp (hB 1 1).continuousOn
  have h01 : Continuous (fun x : ℝ => B x 0 1) := continuousOn_univ.mp (hB 0 1).continuousOn
  unfold dualV
  exact (Complex.continuous_ofReal.comp h11).add
    (continuous_const.mul (Complex.continuous_ofReal.comp h01))

theorem periodic_dualV {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hper : ∀ x, B (x + 1) = B x) :
    ∀ x, dualV B (x + 1) = dualV B x := by
  intro x
  simp only [dualV, hper x]

/-- `det B x = 1` makes `V x` nonzero: `V x = 0` would force the second column of `B x` to
vanish. -/
theorem dualV_ne_zero {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hdet : ∀ x, (B x).det = 1) (x : ℝ) :
    dualV B x ≠ 0 := by
  intro h
  have hre : B x 1 1 = 0 := by
    have := congrArg Complex.re h
    simpa [dualV] using this
  have him : B x 0 1 = 0 := by
    have := congrArg Complex.im h
    simpa [dualV] using this
  have hd := hdet x
  rw [Matrix.det_fin_two, hre, him] at hd
  norm_num at hd

/-! ## 5. Assembly

The two Fourier-analytic inputs are the delegated lemmas `dualV_cF_recurrence` (the
recurrence for the Fourier coefficients of the Bloch function) and `dualV_parseval`
(square summability and nonvanishing of those coefficients). -/

theorem dual_l2_solution (α lam E c : ℝ) (hlam : lam ≠ 0)
    {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hB : ∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) univ)
    (hper : ∀ x, B (x + 1) = B x) (hdet : ∀ x, (B x).det = 1)
    (hconj : ∀ x, B (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot c * B x) :
    ∃ u : ℤ → ℂ, u ≠ 0 ∧ Summable (fun n : ℤ => ‖u n‖ ^ 2) ∧
      ∀ n : ℤ, u (n + 1) + u (n - 1)
        + ((2 / lam) * Real.cos (2 * Real.pi * ((n : ℝ) * α + c)) - E / lam) * u n = 0 := by
  have hcont : Continuous (dualV B) := continuous_dualV hB
  have hperV : ∀ x, dualV B (x + 1) = dualV B x := periodic_dualV hper
  have hneV : ∀ x, dualV B x ≠ 0 := dualV_ne_zero hdet
  have hfun := dual_functional hdet hconj
  obtain ⟨hsumm, hnz⟩ := dualV_parseval hcont hperV hneV
  refine ⟨cF (dualV B), ?_, hsumm, ?_⟩
  · intro hzero
    obtain ⟨n, hn⟩ := hnz
    exact hn (by simp [hzero])
  · intro n
    have h := dualV_cF_recurrence hcont hperV hfun n
    have hlamC : (lam : ℂ) ≠ 0 := by
      intro hc
      exact hlam (Complex.ofReal_injective (by simpa using hc))
    have hcast : ((2 * Real.cos (2 * Real.pi * ((n : ℝ) * α + c)) : ℝ) : ℂ)
        = 2 * (Real.cos (2 * Real.pi * ((n : ℝ) * α + c)) : ℂ) := by
      push_cast
      ring
    rw [hcast] at h
    -- divide the recurrence by `lam`
    have hstep : cF (dualV B) (n + 1) + cF (dualV B) (n - 1)
        = ((E : ℂ) - 2 * (Real.cos (2 * Real.pi * ((n : ℝ) * α + c)) : ℂ))
            * cF (dualV B) n / (lam : ℂ) := by
      rw [eq_div_iff hlamC]
      linear_combination h
    rw [hstep]
    field_simp
    ring

end Work.TMPuig
