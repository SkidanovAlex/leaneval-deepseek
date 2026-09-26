import Mathlib
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.jInvariantFun_cusp_second

/-!
# The cusp asymptotics of `(j(τ) - j(z))⁻¹` to second order

With `E = Ept z = e^{πiz}` (so `‖E‖ = e^{-π Im z}`) and `q = E² = e^{2πiz}`, the modular
`j`-invariant has the cusp expansion

`j(z) = q⁻¹ + 744 + O(‖q‖)`,  i.e.  `j(z) = E(z)^{-2} + 744 + O(‖E(z)‖²)`

(`Work.Asymptotics.jInvariantFun_cusp_second`).  Fixing `τ` in a compact set `K`, so that
`j(τ)` is bounded, and writing `w = E(z)`, `A = j(τ) - 744` and

`ε = j(z) - w⁻² - 744`,  `‖ε‖ ≤ M ‖w‖²`,

the expansion says `j(τ) - j(z) = -w⁻² (1 - X)` with `X = A w² - ε w²`; here
`‖X‖ ≤ (Q + M) ‖w‖²` with `Q` a bound for `‖j(τ) - 744‖` on `K`, so `‖X‖ ≤ 1/2` once
`‖w‖` is small.  Hence

`(j(τ) - j(z))⁻¹ = -w² (1 - X)⁻¹`  and
`(j(τ) - j(z))⁻¹ + w² - (744 - j(τ)) w⁴ = w⁴ (1 - X)⁻¹ (ε - A X)`,

and the right-hand side is `O(‖w‖⁶)` since `‖(1 - X)⁻¹‖ ≤ 2`, `‖ε‖ ≤ M ‖w‖²` and
`‖A X‖ ≤ Q (Q + M) ‖w‖²`.  This is the `j`-analogue of the divisor estimates
`Work.Asymptotics.cusp_inv_divisor_second` used in the contour analysis of the CKMRV
kernels.

The main theorem `cusp_invJ_second` is proved here; the algebraic rearrangement of the
inverse is the private lemma `inv_second_order_identity`.
-/

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Manifold MatrixGroups

noncomputable section

/-- **Algebraic core of the inversion of the second-order cusp expansion.**
For `w ≠ 0`, `A`, `ε ∈ ℂ` with `1 - (A w² - ε w²) ≠ 0` one has
`((A + 744) - (w⁻² + 744 + ε))⁻¹ + w² - (744 - (A + 744)) w⁴
    = w⁴ (1 - (A w² - ε w²))⁻¹ (ε - A (A w² - ε w²))`. -/
private lemma inv_second_order_identity (w A eps : ℂ) (hw : w ≠ 0)
    (h1 : 1 - (A * w^2 - eps * w^2) ≠ 0) :
    ((A + 744) - ((w⁻¹)^2 + 744 + eps))⁻¹ + w^2 - (744 - (A + 744)) * w^4
      = w^4 * (1 - (A * w^2 - eps * w^2))⁻¹ * (eps - A * (A * w^2 - eps * w^2)) := by
  set X : ℂ := A * w^2 - eps * w^2 with hXdef
  have hsub : (w⁻¹)^2 * w^2 = 1 := by rw [inv_pow]; field_simp
  have hfac : (A + 744) - ((w⁻¹)^2 + 744 + eps) = -(w⁻¹)^2 * (1 - X) := by
    rw [show -(w⁻¹)^2 * (1 - X) = -(w⁻¹)^2 + (w⁻¹)^2 * w^2 * A - (w⁻¹)^2 * w^2 * eps by
      rw [hXdef]; ring]
    rw [hsub]; ring
  have hinv : ((A + 744) - ((w⁻¹)^2 + 744 + eps))⁻¹ = -w^2 * (1 - X)⁻¹ := by
    rw [hfac, mul_inv, inv_neg, inv_pow, inv_inv]
  rw [hinv]
  have h744 : 744 - (A + 744) = -A := by ring
  rw [h744]
  field_simp
  ring_nf
  rw [hXdef]
  field_simp
  ring

theorem cusp_invJ_second {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ T : ℝ, 0 < T ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (τ : UpperHalfPlane), τ ∈ K → ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖(Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹
            + (Work.Residues.Ept z) ^ 2 - (744 - Work.Kernels.jInvariantFun τ) * (Work.Residues.Ept z) ^ 4‖
          ≤ C * ‖Work.Residues.Ept z‖ ^ 6 := by
  obtain ⟨T₀, M, hT₀, hM, hExp⟩ := jInvariantFun_cusp_second
  -- `j` is continuous on `ℍ`, hence bounded on the compact set `K`.
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Kernels.jInvariantFun := by
    have h4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Kernels.E4Fun :=
      ModularFormClass.holo ModularForm.E₄
    have hD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Work.Kernels.DeltaFun :=
      ModularFormClass.holo
        (CuspForm.discriminant : CuspForm (Matrix.SpecialLinearGroup.mapGL ℝ).range 12)
    exact (h4.pow 3).div hD (fun w => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero w)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hmd.continuous.continuousOn
  set Q : ℝ := max B 0 + 744 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; linarith [le_max_right B 0]
  have hQM : 0 < Q + M := by linarith
  set T : ℝ := max T₀ (Real.log (2 * (Q + M)) / (2 * Real.pi)) with hTdef
  set C : ℝ := 2 * (M + Q * (Q + M)) with hCdef
  have hT0T : T₀ ≤ T := by rw [hTdef]; exact le_max_left _ _
  have hlog : Real.log (2 * (Q + M)) ≤ 2 * Real.pi * T := by
    have h1 : Real.log (2 * (Q + M)) / (2 * Real.pi) ≤ T := by
      rw [hTdef]; exact le_max_right _ _
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    have h3 : 2 * Real.pi * (Real.log (2 * (Q + M)) / (2 * Real.pi)) = Real.log (2 * (Q + M)) := by
      field_simp
    linarith [h2, h3]
  have hsmall : Real.exp (-(2 * Real.pi * T)) ≤ 1 / (2 * (Q + M)) := by
    have hexp : 2 * (Q + M) ≤ Real.exp (2 * Real.pi * T) := by
      rw [← Real.exp_log (show (0 : ℝ) < 2 * (Q + M) by positivity)]
      exact Real.exp_le_exp.mpr hlog
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) (by positivity : (0 : ℝ) < 2 * (Q + M))).mpr hexp
  refine ⟨T, lt_of_lt_of_le hT₀ hT0T, C, ?_, ?_⟩
  · rw [hCdef]; nlinarith [hM, hQpos, hQM]
  · intro τ hτK z hz
    have hTz : T₀ ≤ z.im := le_trans hT0T hz
    set E : ℂ := Work.Residues.Ept z with hEdef
    have hEne : E ≠ 0 := by rw [hEdef]; exact Work.Residues.Ept_ne_zero z
    have hEnorm : ‖E‖ = Real.exp (-(Real.pi * z.im)) := by
      rw [hEdef]; exact Work.Residues.norm_Ept z
    have hE2 : ‖E‖ ^ 2 = Real.exp (-(2 * Real.pi * z.im)) := by
      rw [hEnorm, sq, ← Real.exp_add]; congr 1; ring
    have hEle : ‖E‖ ≤ 1 := by
      rw [hEnorm]
      exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, z.im_pos])
    have hE2le : ‖E‖ ^ 2 ≤ 1 / (2 * (Q + M)) := by
      rw [hE2]
      exact le_trans (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hz, hTdef])) hsmall
    -- the expansion of `j`
    have hexp := hExp z hTz
    set eps : ℂ := Work.Kernels.jInvariantFun z - (E⁻¹) ^ 2 - 744 with hepsdef
    have heps_le : ‖eps‖ ≤ M * ‖E‖ ^ 2 := by
      rw [hepsdef]; simpa only [hEdef] using hexp
    set A : ℂ := Work.Kernels.jInvariantFun τ - 744 with hAdef
    have hA_le : ‖A‖ ≤ Q := by
      rw [hAdef]
      calc ‖Work.Kernels.jInvariantFun τ - 744‖
          ≤ ‖Work.Kernels.jInvariantFun τ‖ + ‖(744 : ℂ)‖ := norm_sub_le _ _
        _ = ‖Work.Kernels.jInvariantFun τ‖ + 744 := by norm_num
        _ ≤ max B 0 + 744 := by
            have h := hB τ hτK
            linarith [le_max_left B 0]
        _ = Q := by rw [hQdef]
    -- the small quantity `X`
    have hE2one : ‖E‖ ^ 2 ≤ 1 := by
      rw [sq]
      calc ‖E‖ * ‖E‖ ≤ 1 * 1 := mul_le_mul hEle hEle (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    set X : ℂ := A * E ^ 2 - eps * E ^ 2 with hXdef
    have hX_le : ‖X‖ ≤ (Q + M) * ‖E‖ ^ 2 := by
      rw [hXdef, show A * E ^ 2 - eps * E ^ 2 = (A - eps) * E ^ 2 by ring,
        norm_mul, norm_pow]
      have h4 : 0 ≤ ‖E‖ ^ 2 := by positivity
      have h5 : ‖A‖ * ‖E‖ ^ 2 ≤ Q * ‖E‖ ^ 2 := mul_le_mul_of_nonneg_right hA_le h4
      have h6 : ‖eps‖ * ‖E‖ ^ 2 ≤ M * ‖E‖ ^ 2 * ‖E‖ ^ 2 :=
        mul_le_mul_of_nonneg_right heps_le h4
      have h7 : M * ‖E‖ ^ 2 * ‖E‖ ^ 2 ≤ M * ‖E‖ ^ 2 := by
        have h8 := mul_le_mul_of_nonneg_left hE2one (le_of_lt hM)
        nlinarith [h8, h4]
      calc ‖A - eps‖ * ‖E‖ ^ 2 ≤ (‖A‖ + ‖eps‖) * ‖E‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (norm_sub_le _ _) h4
        _ = ‖A‖ * ‖E‖ ^ 2 + ‖eps‖ * ‖E‖ ^ 2 := by ring
        _ ≤ Q * ‖E‖ ^ 2 + M * ‖E‖ ^ 2 * ‖E‖ ^ 2 := add_le_add h5 h6
        _ ≤ Q * ‖E‖ ^ 2 + M * ‖E‖ ^ 2 := by linarith [h7]
        _ = (Q + M) * ‖E‖ ^ 2 := by ring
    have hXhalf : ‖X‖ ≤ 1 / 2 := by
      have h1 : (Q + M) * ‖E‖ ^ 2 ≤ 1 / 2 := by
        have h2 := mul_le_mul_of_nonneg_left hE2le (le_of_lt hQM)
        have h3 : (Q + M) * (1 / (2 * (Q + M))) = 1 / 2 := by field_simp
        linarith [h2, h3]
      linarith [hX_le, h1]
    have h1X : 1 - X ≠ 0 := by
      intro h0
      have h := norm_add_le ((1 : ℂ) - X) X
      have hsum : ((1 : ℂ) - X) + X = 1 := by ring
      rw [hsum, norm_one] at h
      rw [h0, norm_zero] at h
      linarith [hXhalf]
    -- the identity
    have hid := inv_second_order_identity E A eps hEne (by rw [← hXdef]; exact h1X)
    have hgoal : (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹
          + E ^ 2 - (744 - Work.Kernels.jInvariantFun τ) * E ^ 4
        = E ^ 4 * (1 - X)⁻¹ * (eps - A * X) := by
      have h1 : Work.Kernels.jInvariantFun τ = A + 744 := by rw [hAdef]; ring
      have h2 : Work.Kernels.jInvariantFun z = (E⁻¹) ^ 2 + 744 + eps := by rw [hepsdef]; ring
      rw [h1, h2, hXdef]
      exact hid
    rw [hgoal]
    -- the estimate
    have hinv : ‖(1 - X)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have hpos : 0 < ‖1 - X‖ := norm_pos_iff.mpr h1X
      have h2 : (1 : ℝ) / 2 ≤ ‖1 - X‖ := by
        have h := norm_add_le ((1 : ℂ) - X) X
        have hsum : ((1 : ℂ) - X) + X = 1 := by ring
        rw [hsum, norm_one] at h
        linarith [hXhalf]
      have h3 := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 1 / 2)).mpr h2
      norm_num at h3
      exact h3
    have hnum : ‖eps - A * X‖ ≤ (M + Q * (Q + M)) * ‖E‖ ^ 2 := by
      have h1 : ‖eps - A * X‖ ≤ ‖eps‖ + ‖A * X‖ := norm_sub_le _ _
      have h2 : ‖A * X‖ ≤ Q * ((Q + M) * ‖E‖ ^ 2) := by
        rw [norm_mul]
        exact mul_le_mul hA_le hX_le (norm_nonneg _) (le_of_lt hQpos)
      nlinarith [h1, h2, heps_le]
    calc ‖E ^ 4 * (1 - X)⁻¹ * (eps - A * X)‖
        = ‖E‖ ^ 4 * ‖(1 - X)⁻¹‖ * ‖eps - A * X‖ := by
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ ‖E‖ ^ 4 * 2 * ((M + Q * (Q + M)) * ‖E‖ ^ 2) := by
          have h1 : (0 : ℝ) ≤ ‖E‖ ^ 4 := by positivity
          have h4 : (0 : ℝ) ≤ ‖eps - A * X‖ := norm_nonneg _
          have hA1 : ‖E‖ ^ 4 * ‖(1 - X)⁻¹‖ ≤ ‖E‖ ^ 4 * 2 :=
            mul_le_mul_of_nonneg_left hinv h1
          exact mul_le_mul hA1 hnum h4 (by positivity)
      _ = C * ‖E‖ ^ 6 := by rw [hCdef]; ring

end

end Work.Asymptotics
