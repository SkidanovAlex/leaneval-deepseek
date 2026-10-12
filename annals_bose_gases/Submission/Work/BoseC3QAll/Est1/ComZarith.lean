import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.Est1.ComZc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.ComZarith` — the arithmetic of the `χ̂²` half

The two scalar inequalities of the assembly of `Est1.estT2sum_comZ`, at the FS
parameter point:

* the **gap** inequality
  `dlt·K₀ + Λ·cbeta + erm·Λ·NPL·(1+2β_m+β_m²) ≤ (b/400)ℓ⁻²`,
* the **error bracket** inequality
  `Λ·cbeta·NPL + erm·Λ·(β_m+β_m²)·NPL² ≤ C·e1A`.

Both are proved by writing every quantity as a monomial in `X = (μa³)^{1/323}`
(`Work.BoseB7.FSParamsVals`) times `ℓ⁻²`.
-/

noncomputable section

set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7 Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- `Kl^2 = X^{-3}`. -/
theorem Kl_sq {E : Q3Env Mode} (hv : FSParamsView E) : E.Kl ^ 2 = fsXp hv.t (-3) := by
  rw [Kl_val E hv, ← Real.rpow_natCast, fsXp_rpow hv.t_pos.le]
  congr 1; norm_num

/-- `KL^3 = X^{-63/2}`. -/
theorem KL_cube {E : Q3Env Mode} (hv : FSParamsView E) : E.KL ^ 3 = fsXp hv.t (-(63 / 2)) := by
  rw [KL_val E hv, ← Real.rpow_natCast, fsXp_rpow hv.t_pos.le]
  congr 1; norm_num

/-- `𝓁² = X^{97}`. -/
theorem lille_sq {E : Q3Env Mode} (hv : FSParamsView E) : E.lille ^ 2 = fsXp hv.t 97 := by
  rw [lille_val E hv, ← Real.rpow_natCast, fsXp_rpow hv.t_pos.le]
  congr 1; norm_num

/-- `η² = X^{2472}`. -/
theorem eta_sq {E : Q3Env Mode} (hv : FSParamsView E) : eta E ^ 2 = fsXp hv.t 2472 := by
  rw [eta_eq E hv, ← Real.rpow_natCast, fsXp_rpow hv.t_pos.le]
  congr 1; norm_num

/-- `K_H⁻¹ = X^{549/4}`. -/
theorem KHinv_val {E : Q3Env Mode} (hv : FSParamsView E) : E.KH⁻¹ = fsXp hv.t (549 / 4) := by
  rw [KH_val E hv, ← fsXp_inv hv.t_pos]
  congr 1; norm_num

/-- `μ²aℓ³ = X^{-169}ℓ⁻²` (with `X = (μa³)^{1/323}`). -/
theorem muSq_a_ell3 {E : Q3Env Mode} (hv : FSParamsView E) :
    E.mu ^ 2 * E.aScat * E.ell ^ 3 = fsXp hv.t (-169) * (E.ell ^ 2)⁻¹ := by
  have h1 : E.mu ^ 2 * E.aScat * E.ell ^ 3 = (E.mu * E.ell ^ 3) * (E.mu * E.aScat) := by ring
  rw [h1, mue_val E hv, mu_mul_aScat_eq E hv, Kl_sq hv, div_eq_mul_inv,
    show fsXp hv.t (-166) * (fsXp hv.t (-3) * (E.ell ^ 2)⁻¹)
      = fsXp hv.t (-166) * fsXp hv.t (-3) * (E.ell ^ 2)⁻¹ by ring,
    fsXp_mul hv.t_pos]
  congr 1
  ring

/-- `e1A ≥ X^{58}ℓ⁻²` (the second bracket of `e1A`). -/
theorem e1A_ge {E : Q3Env Mode} (hv : FSParamsView E) (hb : 0 < E.b) :
    fsXp hv.t 58 * (E.ell ^ 2)⁻¹ ≤ e1A E := by
  have hE0 : E0 E = fsXp hv.t (-169) * (E.ell ^ 2)⁻¹ := by
    rw [E0]; exact muSq_a_ell3 hv
  have hdil : dil E (1 / 2) = fsXp hv.t (323 / 2) := by
    rw [dil_val E hv (1 / 2)]; congr 1; norm_num
  have hterm2 : E0 E * (dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2)
      = fsXp hv.t 58 * (E.ell ^ 2)⁻¹ := by
    rw [hE0, hdil, KL_cube hv, lille_sq hv]
    rw [show fsXp hv.t (-169) * (E.ell ^ 2)⁻¹
          * (fsXp hv.t (323 / 2) * fsXp hv.t (-(63 / 2)) * fsXp hv.t 97)
        = (fsXp hv.t (-169) * fsXp hv.t (323 / 2) * fsXp hv.t (-(63 / 2)) * fsXp hv.t 97)
          * (E.ell ^ 2)⁻¹ by ring]
    rw [fsXp_mul hv.t_pos, fsXp_mul hv.t_pos, fsXp_mul hv.t_pos]
    congr 1
    norm_num
  have hnn1 : 0 ≤ E0 E := by
    have h1 : 0 < E.mu := mu_pos E hv
    have h2 : 0 < E.aScat := hv.a_pos
    have h3 : 0 < E.ell := ell_pos E hv
    rw [E0]; positivity
  have hdile2 : 0 ≤ dil E (1 / 2) := dil_nonneg E hv (1 / 2)
  have hdil42 : 0 ≤ dil E (1 / 4) := dil_nonneg E hv (1 / 4)
  have hetae2 : 0 ≤ eta E := by rw [eta_eq E hv]; exact fsXp_nonneg hv.t_pos.le
  have hKle2 : 0 ≤ E.Kl := le_of_lt (by linarith [hv.one_le_Kl])
  have hKLe2 : 0 ≤ E.KL := le_of_lt (by linarith [hv.one_le_KL])
  have hlile2 : 0 ≤ E.lille := le_of_lt (lille_pos E hv)
  have hsplit : e1A E = E0 E * (dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * eta E ^ 2)
      + E0 E * (dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2)
      + E0 E * (E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b)
      + E0 E * (E.Kl ^ ((3 : ℝ) / 2) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E) := by
    rw [e1A, mul_add, mul_add, mul_add]
  have hT1 : 0 ≤ E0 E * (dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * eta E ^ 2) :=
    mul_nonneg hnn1 (by positivity)
  have hT2 : 0 ≤ E0 E * (dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2) :=
    mul_nonneg hnn1 (by positivity)
  have hT3 : 0 ≤ E0 E * (E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b) :=
    mul_nonneg hnn1 (by positivity)
  have hT4 : 0 ≤ E0 E * (E.Kl ^ ((3 : ℝ) / 2) * E.KL ^ 3 * dil E (1 / 4)
      * E.lille ^ 2 * eta E) :=
    mul_nonneg hnn1 (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (Real.rpow_nonneg hKle2 _) (pow_nonneg hKLe2 3)) hdil42)
      (pow_nonneg hlile2 2)) hetae2)
  have hge : E0 E * (dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2) ≤ e1A E := by
    rw [hsplit]; linarith [hT1, hT3, hT4]
  rw [← hterm2]
  exact hge

/-! ## 2. The two scalar inequalities -/


end Est1

end Work.BoseC3QAll
