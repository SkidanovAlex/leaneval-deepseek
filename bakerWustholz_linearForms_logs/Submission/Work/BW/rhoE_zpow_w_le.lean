import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.zpow_sq_le_exp_posLog
import Submission.Work.BW.zpow_sq_le_exp_posLog_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Place bound for the Kummer square-root powers: with `ρ_j² = φ(α'_j)` in `L = ℚ(φ(K),ρ)`
(the `hexp` hypothesis), `w (ρ_j)^{s·e} ≤ exp(z·D·log⁺(w(α'_j)^{sign s}))` for `z = |s|/2^{J+1}`,
whenever `e·2^J ≤ D` (so `|s|e/2 ≤ zD`) and `D ≥ 0`; the base is sign-aware: `w(α'_j)` for
`s ≥ 0` and `(w(α'_j))⁻¹` for `s ≤ 0`. Uses `w(ρ_j)² = w(α'_j)` (multiplicativity of the place),
`w(ρ_j) = √(w(α'_j)) ≥ 0`, and the elementary `x^a ≤ exp(b log⁺x)` for `0 ≤ a ≤ b`, resp.
`x^{-a} ≤ exp(b log⁺(1/x))`. -/
theorem rhoE_zpow_w_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {v : ℕ} {Lm : Fin r → Fin n → ℤ} {α' : Fin r → K}
    (hexp : ∀ j, Complex.exp (lamP φ α v Lm j) = φ (α' j))
    [inst : NumberField (EL φ (rhoC φ α v Lm))]
    (w : NumberField.InfinitePlace (EL φ (rhoC φ α v Lm)))
    (J : ℕ) (j : Fin r) (s : ℤ) (e : ℕ) (D : ℝ) (hD : 0 ≤ D) (he : (e : ℝ) * 2 ^ J ≤ D) :
    w (rhoE φ (rhoC φ α v Lm) j) ^ (s * (e : ℤ))
      ≤ Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * D
          * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j))
             else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog) := by
  -- The Kummer relation `ρ_j² = φ(α'_j)`, lifted to `L` and pushed through the place `w`.
  have hρ : ∀ j, (rhoC φ α v Lm) j ^ 2 = φ (α' j) :=
    fun j => rhoC_sq α v Lm (φ := φ) (α' := α') hexp j
  have hsq := rhoE_sq (φ := φ) (ρ := rhoC φ α v Lm) (η := α') hρ j
  have hsq2 : (w (rhoE φ (rhoC φ α v Lm) j)) ^ 2
      = w (inclE φ (rhoC φ α v Lm) (α' j)) := by
    rw [← map_pow w (rhoE φ (rhoC φ α v Lm) j) 2, hsq]
  -- The base of the place is nonzero: `φ (α'_j) = exp (lamP …) ≠ 0`.
  have hϕne : φ (α' j) ≠ 0 := by rw [← hexp j]; exact Complex.exp_ne_zero _
  have hincl_ne : inclE φ (rhoC φ α v Lm) (α' j) ≠ 0 := by
    intro h
    exact hϕne (by
      have := congrArg (fun z : EL φ (rhoC φ α v Lm) => (z : ℂ)) h
      simpa using this)
  have hBpos : 0 < w (rhoE φ (rhoC φ α v Lm) j) := by
    apply NumberField.InfinitePlace.pos_iff.mpr
    intro h
    have := congrArg (fun z : EL φ (rhoC φ α v Lm) => (z : ℂ)) h
    simp only [rhoE_coe, IntermediateField.coe_zero] at this
    exact Complex.exp_ne_zero _ this
  -- Arithmetic: `e ≤ D / 2^J` and `|s| ≥ 0`.
  have h2J : (0 : ℝ) < 2 ^ J := by positivity
  have hE : (e : ℝ) ≤ D / 2 ^ J := by rw [le_div_iff₀ h2J]; exact he
  by_cases hs : 0 ≤ s
  · -- `s ≥ 0`: the base is `w (α'_j)` itself.
    rw [if_pos hs]
    refine zpow_sq_le_exp_posLog hBpos hsq2 (s * (e : ℤ)) _ ?_ ?_
    · exact mul_nonneg hs (Int.natCast_nonneg e)
    · have hsabs : (s : ℝ) ≤ ((|s| : ℤ) : ℝ) := by rw [Int.cast_abs]; exact le_abs_self _
      have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg e
      calc ((s * (e : ℤ) : ℤ) : ℝ) / 2 = (s : ℝ) * (e : ℝ) / 2 := by push_cast; ring
        _ ≤ ((|s| : ℤ) : ℝ) * (e : ℝ) / 2 := by nlinarith
        _ = ((|s| : ℤ) : ℝ) / 2 * (e : ℝ) := by ring
        _ ≤ ((|s| : ℤ) : ℝ) / 2 * (D / 2 ^ J) :=
              mul_le_mul_of_nonneg_left hE (by positivity)
        _ = ((|s| : ℤ) : ℝ) / 2 / 2 ^ J * D := by ring
  · -- `s < 0`: the base is `(w (α'_j))⁻¹`.
    rw [if_neg hs]
    refine zpow_sq_le_exp_posLog_inv hBpos hsq2 (s * (e : ℤ)) _ ?_ ?_
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hs)) (Int.natCast_nonneg e)
    · have hslt : s < 0 := lt_of_not_ge hs
      have hsneg : (s : ℝ) < 0 := by exact_mod_cast hslt
      have hsabs : -((s : ℝ)) = ((|s| : ℤ) : ℝ) := by rw [Int.cast_abs, abs_of_neg hsneg]
      calc -(((s * (e : ℤ) : ℤ) : ℝ)) / 2 = (-(s : ℝ)) * (e : ℝ) / 2 := by push_cast; ring
        _ = ((|s| : ℤ) : ℝ) * (e : ℝ) / 2 := by rw [hsabs]
        _ = ((|s| : ℤ) : ℝ) / 2 * (e : ℝ) := by ring
        _ ≤ ((|s| : ℤ) : ℝ) / 2 * (D / 2 ^ J) :=
              mul_le_mul_of_nonneg_left hE (by positivity)
        _ = ((|s| : ℤ) : ℝ) / 2 / 2 ^ J * D := by ring

end Work.BW
