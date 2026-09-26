/-
# The cone-separated (off-spike) bound for the tile kernel: the assembly

`Work.Asymptotics.offspike_bound_general` bounds `K(τ,ζ) - (n/2π)/(ζ - w)` for **general**
`ζ ∈ ℍ` (not just `ζ = i t`) satisfying the cone hypotheses: with `z = S ζ` in the cone
`{1 ≤ Im z}`, within distance `1` of `u = S w` and at distance `≥ 1/8` from `u` modulo the
parabolic translations `ℤ`.

The three inputs are the analytic cone bounds

* `hDiv` : `c (1 + e^{2π(Im u - Im z)}) ≤ ‖Δ(z)(j(n+w) - j(z))‖`  (the divisor lower bound),
* `hXi`  : `‖Ξ_d(n+w, z)‖ ≤ C (scale w)^N (1 + e^{2π(Im u - Im z)})`,
* `hNc`  : `‖Ncusp(n+w, z)‖ ≤ C (scale w)^N (1 + e^{c(Im u - Im z)})`, `c < 2π`,

all of which are proved elsewhere (`tile_divisor_lower_cone`, `tileXi_poly`,
`tileNcusp_cone`).

Route.  Set `z := S • ζ`, `u := S • w` and `τ := n +ᵥ w`, `ρ := e^{2π(Im u - Im z)}`.  The
cleared identity (`two_KfunClear_S_eq_eight` / `..._twentyfour`) together with
`KfunClear = growthPrefactor · Kfun` gives, after cancelling `Δ(τ)` and powers of `z`,
the *complex* identity

  `2 z² Δ(z)(jτ - jz) K(τ,ζ) = Ξ_d(τ,z)/c_d + Ncusp(τ,z)`  (d = 8),

resp. `2 z^{10} Δ(z)(jτ - jz) K(τ,ζ) = Ξ₂₄(τ,z)/c₂₄ + Ncusp(τ,z)` (d = 24).

Taking norms and bounding the numerator by `hXi` + `hNc` (using `‖z‖ ≥ 1` and the fact that
`|Im u - Im z| ≤ ‖z - u‖ ≤ 1` turns the `Ncusp` exponential into a constant factor times
`1 + ρ`), then dividing by the divisor lower bound `hDiv` gives `‖K(τ,ζ)‖ ≤ C (scale w)^N`.
The principal part is bounded by `8/π (scale w)²` using
`‖ζ - w‖ = ‖z - u‖/(‖z‖‖u‖) ≥ (1/8)/(2 (scale w)²)`.
-/
import Mathlib
import Submission.Work.Asymptotics.TileCone.Basic
import Submission.Work.Asymptotics.tile_divisor_lower_cone
import Submission.Work.Asymptotics.tileXi_poly
import Submission.Work.Asymptotics.tile_pp_window_core

noncomputable section

open UpperHalfPlane ModularGroup

namespace Work.Asymptotics

open Work.Kernels

/-! ## The cleared identity as an identity of complex numbers -/

/-- `KfunClear = growthPrefactor · Kfun` off the coincidence set. -/
lemma KfunClear_eq_growthPrefactor_mul (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) (h : jInvariantFun τ ≠ jInvariantFun z) :
    KfunClear ℓ d τ z = growthPrefactor d τ z * Kfun ℓ d τ z := by
  rw [KfunClear, Kfun, ClearLink.KPlusClear_eq_smul d hd τ z h,
    ClearLink.KMinusClear_eq_smul ℓ d hd τ z h]
  ring

/-- The `c`-normalisation constant of the tile expansion, `c₈` or `c₂₄`. -/
def cdConst (d : ℕ) : ℂ := if d = 8 then cEight else cTwentyFour

/-- The norm of `cdConst d`. -/
def cdNorm (d : ℕ) : ℝ := if d = 8 then ‖cEight‖ else ‖cTwentyFour‖

lemma cdConst_ne_zero (d : ℕ) (hd : d = 8 ∨ d = 24) : cdConst d ≠ 0 := by
  rcases hd with rfl | rfl
  · rw [cdConst, if_pos rfl]; exact cEight_ne_zero
  · rw [cdConst, if_neg (by norm_num)]; exact cTwentyFour_ne_zero

lemma cdNorm_pos (d : ℕ) (hd : d = 8 ∨ d = 24) : 0 < cdNorm d := by
  rcases hd with rfl | rfl
  · rw [cdNorm, if_pos rfl]; exact norm_pos_iff.mpr cEight_ne_zero
  · rw [cdNorm, if_neg (by norm_num)]; exact norm_pos_iff.mpr cTwentyFour_ne_zero

lemma norm_cdConst (d : ℕ) (hd : d = 8 ∨ d = 24) : ‖cdConst d‖ = cdNorm d := by
  rcases hd with rfl | rfl
  · rw [cdConst, cdNorm, if_pos rfl, if_pos rfl]
  · rw [cdConst, cdNorm, if_neg (by norm_num), if_neg (by norm_num)]

lemma if_div_eq (d : ℕ) (hd : d = 8 ∨ d = 24) (X8 X24 : ℂ) :
    (if d = 8 then X8 / cEight else X24 / cTwentyFour)
      = (if d = 8 then X8 else X24) * (cdConst d)⁻¹ := by
  rcases hd with rfl | rfl
  · rw [if_pos rfl, if_pos rfl, cdConst, if_pos rfl, div_eq_mul_inv]
  · rw [if_neg (by norm_num), if_neg (by norm_num), cdConst, if_neg (by norm_num),
      div_eq_mul_inv]

/-- **The cleared identity, cleared of `Δ(τ)` and powers of `z`.**  With `τ` the tile point and
`z` the cone variable (so that `S • z` is the original `ζ`), the kernel satisfies

`2 · z^{2} (d = 8) resp. z^{10} (d = 24) · Δ(z)(j(τ) - j(z)) · K(τ, S•z) = Ξ_d(τ,z)/c_d + Ncusp`.

This is the exact form in which the divisor lower bound cancels the exponentials. -/
lemma cleared_norm_relation (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) (h : jInvariantFun τ ≠ jInvariantFun z) :
    2 * ‖(z : ℂ)‖ ^ (if d = 8 then 2 else 10)
        * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖
        * ‖Kfun ℓ d τ (ModularGroup.S • z)‖
      = ‖(if d = 8 then Xi8 τ z / cEight else Xi24 τ z / cTwentyFour) + Ncusp ℓ d τ z‖ := by
  have hjS : jInvariantFun (ModularGroup.S • z) = jInvariantFun z :=
    KernelFacts.jInvariantFun_S_smul z
  have hj' : jInvariantFun τ ≠ jInvariantFun (ModularGroup.S • z) := by
    rw [hjS]; exact h
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  have hΔτ0 : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hbase : (2 * (z : ℂ) ^ (if d = 8 then 2 else 10)
        * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))
        * Kfun ℓ d τ (ModularGroup.S • z))
      = (if d = 8 then Xi8 τ z / cEight else Xi24 τ z / cTwentyFour) + Ncusp ℓ d τ z := by
    rcases hd with rfl | rfl
    · -- dimension 8
      have hid := two_KfunClear_S_eq_eight ℓ τ z h
      have hg := KfunClear_eq_growthPrefactor_mul ℓ 8 (Or.inl rfl) τ (ModularGroup.S • z) hj'
      rw [hg, growthPrefactor, if_pos rfl, pow_one, DeltaFun_S_smul_eq, hjS] at hid
      have h2 : ((z : ℂ) ^ 10 * DeltaFun τ)
            * (2 * (z : ℂ) ^ 2 * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))
                * Kfun ℓ 8 τ (ModularGroup.S • z))
          = ((z : ℂ) ^ 10 * DeltaFun τ)
            * (Xi8 τ z / cEight + Ncusp ℓ 8 τ z) := by
        rw [← hid]
        ring
      exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 10 hz0) hΔτ0) h2
    · -- dimension 24
      have hid := two_KfunClear_S_eq_twentyfour ℓ τ z h
      have hg := KfunClear_eq_growthPrefactor_mul ℓ 24 (Or.inr rfl) τ (ModularGroup.S • z) hj'
      rw [hg, growthPrefactor, if_neg (by norm_num), DeltaFun_S_smul_eq, hjS] at hid
      have h2 : ((z : ℂ) ^ 14 * DeltaFun τ * DeltaFun z)
            * (2 * (z : ℂ) ^ 10 * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))
                * Kfun ℓ 24 τ (ModularGroup.S • z))
          = ((z : ℂ) ^ 14 * DeltaFun τ * DeltaFun z)
            * (Xi24 τ z / cTwentyFour + Ncusp ℓ 24 τ z) := by
        rw [← hid]
        ring
      exact mul_left_cancel₀
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 14 hz0) hΔτ0)
          (ClassicalFacts.DeltaFun_ne_zero z)) h2
  have hh := congrArg (fun x : ℂ => ‖x‖) hbase
  simpa only [norm_mul, norm_pow, Complex.norm_ofNat] using hh

/-! ## The assembly -/

/-- **The cone-separated bound, general `ζ`.**

With `z = S • ζ` in the cone `{1 ≤ Im z}` and at distance `≥ 1/8` from `u = S • w` modulo the
parabolic translations `ℤ`, the kernel differs from the principal part of its translate pole
`ζ = w` by at most a power of `scale w`.

No upper bound on the distance `‖z - u‖` is assumed: the principal part is controlled through
`‖ζ - w‖ = ‖z - u‖/(‖z‖‖u‖)` and `‖z - u‖/‖z‖ ≥ (1/8)/(‖u‖ + 1/8)`, which is all that is needed.
The hypothesis on `Ncusp` carries `0 ≤ c`, so that `1 + e^{c(Im u - Im z)} ≤ 1 + e^{2π(Im u - Im z)}`
unconditionally. -/
theorem offspike_bound_general (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hDiv : ∃ c : ℝ, 0 < c ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane), 1 ≤ z.im →
        (∀ k : ℤ, (1 / 8 : ℝ) ≤
          ‖(z : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖) →
        c * (1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)))
          ≤ ‖Work.Kernels.DeltaFun z *
              (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z)‖)
    (hXi : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane), 1 ≤ z.im →
        ‖(if d = 8 then Xi8 ((n : ℝ) +ᵥ w) z else Xi24 ((n : ℝ) +ᵥ w) z)‖
          ≤ C * (Work.Kernels.scale w) ^ N
              * (1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im))))
    (hNc : ∃ c C N : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ c ∧ c < 2 * Real.pi ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane), 1 ≤ z.im →
        ‖Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
          ≤ C * (Work.Kernels.scale w) ^ N
              * (1 + Real.exp (c * ((ModularGroup.S • w).im - z.im)))) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (ζ : UpperHalfPlane),
        1 ≤ ((ModularGroup.S • ζ : UpperHalfPlane)).im →
        (∀ k : ℤ, (1 / 8 : ℝ) ≤
          ‖((ModularGroup.S • ζ : UpperHalfPlane) : ℂ)
            - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖) →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
        ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨cD, hcD, hDiv⟩ := hDiv
  obtain ⟨Cx, Nx, hCx, hNx, hXi⟩ := hXi
  obtain ⟨cN, CN, NN, hCN, hNN, hcN0, hcN, hNc⟩ := hNc
  set N' : ℝ := max Nx NN with hN'
  set Ctot : ℝ := Cx / cdNorm d + 2 * CN with hCtot
  have hcdN : 0 < cdNorm d := cdNorm_pos d hd
  have hCtot_pos : 0 < Ctot := by
    rw [hCtot]
    have h1 : 0 < Cx / cdNorm d := div_pos hCx hcdN
    linarith
  refine ⟨Ctot / (2 * cD) + 8 / Real.pi, max N' 2, ?_, ?_, ?_⟩
  · have h2cD : 0 < 2 * cD := by linarith
    exact add_nonneg (div_nonneg hCtot_pos.le h2cD.le) (by positivity)
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_right _ _)
  intro w hw n hn ζ hcone hsep
  set z : ℍ := ModularGroup.S • ζ with hzdef
  set u : ℍ := ModularGroup.S • w with hudef
  set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
  set A : ℝ := u.im - z.im with hAdef
  set ρ : ℝ := Real.exp (2 * Real.pi * A) with hρdef
  have hzi : 1 ≤ z.im := hcone
  have hρpos : 0 < ρ := by rw [hρdef]; exact Real.exp_pos _
  have hρ1 : 0 ≤ 1 + ρ := by linarith
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  have hu0 : (u : ℂ) ≠ 0 := u.ne_zero
  have hzc : (z : ℂ) = -((ζ : ℂ))⁻¹ := by
    rw [hzdef, modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  have huc : (u : ℂ) = -((w : ℂ))⁻¹ := by
    rw [hudef, modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  have hζ0 : (ζ : ℂ) ≠ 0 := ζ.ne_zero
  have hw0' : (w : ℂ) ≠ 0 := w.ne_zero
  have hζz : (ζ : ℂ) = -((z : ℂ))⁻¹ := by
    have h1 : (z : ℂ) * (ζ : ℂ) = -1 := by
      rw [hzc, neg_mul, inv_mul_cancel₀ hζ0]
    have h2 : (z : ℂ) * (-((z : ℂ))⁻¹) = -1 := by
      rw [mul_neg, mul_inv_cancel₀ hz0]
    exact mul_left_cancel₀ hz0 (h1.trans h2.symm)
  have hwu : (w : ℂ) = -((u : ℂ))⁻¹ := by
    have h1 : (u : ℂ) * (w : ℂ) = -1 := by
      rw [huc, neg_mul, inv_mul_cancel₀ hw0']
    have h2 : (u : ℂ) * (-((u : ℂ))⁻¹) = -1 := by
      rw [mul_neg, mul_inv_cancel₀ hu0]
    exact mul_left_cancel₀ hu0 (h1.trans h2.symm)
  have hznorm1 : 1 ≤ ‖(z : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (z : ℂ)
    rw [UpperHalfPlane.coe_im, abs_of_pos (by linarith : (0:ℝ) < z.im)] at h
    linarith
  have hwim_le : w.im ≤ ‖(w : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (w : ℂ)
    rw [UpperHalfPlane.coe_im, abs_of_pos w.im_pos] at h
    exact h
  have hscw : 1 ≤ Work.Kernels.scale w := one_le_scale w
  have hsc0 : 0 ≤ Work.Kernels.scale w := le_trans zero_le_one hscw
  have hnu0 : 0 < ‖(u : ℂ)‖ := norm_pos_iff.mpr hu0
  have hu_le : ‖(u : ℂ)‖ ≤ Work.Kernels.scale w := by
    have hun : ‖(u : ℂ)‖ = (‖(w : ℂ)‖)⁻¹ := by rw [huc, norm_neg, norm_inv]
    rw [hun]
    have hsc : (w.im)⁻¹ ≤ Work.Kernels.scale w := by
      rw [Work.Kernels.scale]; linarith [hwim_le, norm_nonneg (w : ℂ)]
    have h2' : (‖(w : ℂ)‖)⁻¹ ≤ (w.im)⁻¹ := by
      rw [inv_le_inv₀ (by linarith [hwim_le, w.im_pos]) w.im_pos]
      exact hwim_le
    linarith
  -- `1 + e^{cN A} ≤ 2 (1 + ρ)`, using `0 ≤ cN < 2π`
  have hexpA : 1 + Real.exp (cN * A) ≤ 2 * (1 + ρ) := by
    rcases le_or_gt 0 A with hA | hA
    · have h : cN * A ≤ 2 * Real.pi * A := by nlinarith
      have h2 := Real.exp_le_exp.mpr h
      rw [hρdef.symm] at h2
      linarith
    · have h : cN * A ≤ 0 := by nlinarith
      have h2 := Real.exp_le_exp.mpr h
      rw [Real.exp_zero] at h2
      linarith
  -- the coincidence is impossible
  have hjne : jInvariantFun τ ≠ jInvariantFun z := by
    intro heq
    have hb := hDiv w hw n hn z hzi (fun k => hsep k)
    have h0 : ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ = 0 := by
      rw [heq, sub_self, mul_zero, norm_zero]
    rw [h0] at hb
    have hpos : 0 < cD * (1 + ρ) := mul_pos hcD (by linarith)
    linarith
  have hSz : ModularGroup.S • z = ζ := by rw [hzdef, S_smul_S_smul]
  -- the cleared identity
  have hrel := cleared_norm_relation ℓ d hd τ z hjne
  rw [hSz] at hrel
  -- the divisor lower bound
  have hdiv' := hDiv w hw n hn z hzi (fun k => hsep k)
  -- the numerator bound
  have hnum : ‖(if d = 8 then Xi8 τ z / cEight else Xi24 τ z / cTwentyFour) + Ncusp ℓ d τ z‖
      ≤ Ctot * (Work.Kernels.scale w) ^ N' * (1 + ρ) := by
    have hsplit : (if d = 8 then Xi8 τ z / cEight else Xi24 τ z / cTwentyFour)
        = (if d = 8 then Xi8 τ z else Xi24 τ z) * (cdConst d)⁻¹ :=
      if_div_eq d hd (Xi8 τ z) (Xi24 τ z)
    have hX := hXi w hw n hn z hzi
    have hN := hNc w hw n hn z hzi
    have hpNx : (Work.Kernels.scale w) ^ Nx ≤ (Work.Kernels.scale w) ^ N' := by
      rw [hN']; exact Real.rpow_le_rpow_of_exponent_le hscw (le_max_left _ _)
    have hpNN : (Work.Kernels.scale w) ^ NN ≤ (Work.Kernels.scale w) ^ N' := by
      rw [hN']; exact Real.rpow_le_rpow_of_exponent_le hscw (le_max_right _ _)
    have hAgn0 : 0 ≤ Cx / cdNorm d := div_nonneg hCx.le hcdN.le
    have h1 : Cx * (Work.Kernels.scale w) ^ Nx * (1 + ρ) * (cdNorm d)⁻¹
        ≤ Cx / cdNorm d * (Work.Kernels.scale w) ^ N' * (1 + ρ) := by
      have h4 : Cx / cdNorm d * (Work.Kernels.scale w) ^ Nx * (1 + ρ)
          ≤ Cx / cdNorm d * (Work.Kernels.scale w) ^ N' * (1 + ρ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpNx hAgn0) hρ1
      have h5 : Cx * (Work.Kernels.scale w) ^ Nx * (1 + ρ) * (cdNorm d)⁻¹
          = Cx / cdNorm d * (Work.Kernels.scale w) ^ Nx * (1 + ρ) := by
        rw [div_eq_mul_inv]; ring
      rw [h5]; exact h4
    have h2 : 2 * CN * (Work.Kernels.scale w) ^ NN * (1 + ρ)
        ≤ 2 * CN * (Work.Kernels.scale w) ^ N' * (1 + ρ) := by
      have h6 : 2 * CN * (Work.Kernels.scale w) ^ NN ≤ 2 * CN * (Work.Kernels.scale w) ^ N' :=
        mul_le_mul_of_nonneg_left hpNN (by positivity)
      exact mul_le_mul_of_nonneg_right h6 hρ1
    have hNbound : ‖Ncusp ℓ d τ z‖ ≤ 2 * CN * (Work.Kernels.scale w) ^ NN * (1 + ρ) := by
      refine le_trans hN ?_
      have h6 : CN * (Work.Kernels.scale w) ^ NN * (1 + Real.exp (cN * A))
          ≤ CN * (Work.Kernels.scale w) ^ NN * (2 * (1 + ρ)) :=
        mul_le_mul_of_nonneg_left hexpA (mul_nonneg hCN.le (Real.rpow_nonneg hsc0 _))
      refine le_trans h6 (le_of_eq ?_)
      ring
    calc ‖(if d = 8 then Xi8 τ z / cEight else Xi24 τ z / cTwentyFour) + Ncusp ℓ d τ z‖
        ≤ ‖(if d = 8 then Xi8 τ z else Xi24 τ z) * (cdConst d)⁻¹‖
            + ‖Ncusp ℓ d τ z‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ = ‖(if d = 8 then Xi8 τ z else Xi24 τ z)‖ * (cdNorm d)⁻¹
            + ‖Ncusp ℓ d τ z‖ := by
          rw [norm_mul, norm_inv, norm_cdConst d hd]
      _ ≤ Cx * (Work.Kernels.scale w) ^ Nx * (1 + ρ) * (cdNorm d)⁻¹
            + 2 * CN * (Work.Kernels.scale w) ^ NN * (1 + ρ) := by
          have h1' : ‖(if d = 8 then Xi8 τ z else Xi24 τ z)‖ * (cdNorm d)⁻¹
              ≤ Cx * (Work.Kernels.scale w) ^ Nx * (1 + ρ) * (cdNorm d)⁻¹ :=
            mul_le_mul_of_nonneg_right hX (inv_nonneg.mpr hcdN.le)
          linarith
      _ ≤ Ctot * (Work.Kernels.scale w) ^ N' * (1 + ρ) := by
          rw [hCtot]
          calc Cx * (Work.Kernels.scale w) ^ Nx * (1 + ρ) * (cdNorm d)⁻¹
                + 2 * CN * (Work.Kernels.scale w) ^ NN * (1 + ρ)
              ≤ Cx / cdNorm d * (Work.Kernels.scale w) ^ N' * (1 + ρ)
                + 2 * CN * (Work.Kernels.scale w) ^ N' * (1 + ρ) := add_le_add h1 h2
            _ = (Cx / cdNorm d + 2 * CN) * (Work.Kernels.scale w) ^ N' * (1 + ρ) := by ring
  -- the kernel bound
  have hKbound : ‖Kfun ℓ d τ ζ‖ ≤ Ctot / (2 * cD) * (Work.Kernels.scale w) ^ N' := by
    have hzpow1 : 1 ≤ ‖(z : ℂ)‖ ^ (if d = 8 then 2 else 10) := one_le_pow₀ hznorm1
    have hQ0 : 0 ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := norm_nonneg _
    have hK0 : 0 ≤ ‖Kfun ℓ d τ ζ‖ := norm_nonneg _
    have hstep1 : 2 * cD * (1 + ρ) * ‖Kfun ℓ d τ ζ‖
        ≤ 2 * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ * ‖Kfun ℓ d τ ζ‖ :=
      mul_le_mul_of_nonneg_right (by linarith [hdiv'] : 2 * cD * (1 + ρ)
        ≤ 2 * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖) hK0
    have hstep2 : 2 * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ * ‖Kfun ℓ d τ ζ‖
        ≤ 2 * ‖(z : ℂ)‖ ^ (if d = 8 then 2 else 10)
            * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ * ‖Kfun ℓ d τ ζ‖ := by
      have h2 : 2 * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖
          ≤ 2 * ‖(z : ℂ)‖ ^ (if d = 8 then 2 else 10)
              * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by
        nlinarith [hzpow1, hQ0]
      exact mul_le_mul_of_nonneg_right h2 hK0
    have hKN : 2 * cD * (1 + ρ) * ‖Kfun ℓ d τ ζ‖
        ≤ Ctot * (Work.Kernels.scale w) ^ N' * (1 + ρ) :=
      le_trans (le_trans hstep1 hstep2) (le_trans (le_of_eq hrel) hnum)
    have h3 : (1 + ρ) * (2 * cD * ‖Kfun ℓ d τ ζ‖)
        ≤ (1 + ρ) * (Ctot * (Work.Kernels.scale w) ^ N') := by
      have e1 : (1 + ρ) * (2 * cD * ‖Kfun ℓ d τ ζ‖)
          = 2 * cD * (1 + ρ) * ‖Kfun ℓ d τ ζ‖ := by ring
      have e2 : (1 + ρ) * (Ctot * (Work.Kernels.scale w) ^ N')
          = Ctot * (Work.Kernels.scale w) ^ N' * (1 + ρ) := by ring
      rw [e1, e2]; exact hKN
    have h4 : 2 * cD * ‖Kfun ℓ d τ ζ‖ ≤ Ctot * (Work.Kernels.scale w) ^ N' :=
      le_of_mul_le_mul_left h3 (by linarith : (0:ℝ) < 1 + ρ)
    have h5 : ‖Kfun ℓ d τ ζ‖ ≤ Ctot * (Work.Kernels.scale w) ^ N' / (2 * cD) := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * cD)]
      linarith
    calc ‖Kfun ℓ d τ ζ‖ ≤ Ctot * (Work.Kernels.scale w) ^ N' / (2 * cD) := h5
      _ = Ctot / (2 * cD) * (Work.Kernels.scale w) ^ N' := by ring
  -- the principal part bound
  have hsubst : (ζ : ℂ) - (w : ℂ) = ((z : ℂ) - (u : ℂ)) * (((z : ℂ) * (u : ℂ))⁻¹) := by
    rw [hζz, hwu]
    field_simp
    ring
  have hzu_ge : (1 / 8 : ℝ) ≤ ‖(z : ℂ) - (u : ℂ)‖ := by
    have := hsep 0
    simpa using this
  have hnsub : ‖(ζ : ℂ) - (w : ℂ)‖
      = ‖(z : ℂ) - (u : ℂ)‖ / (‖(z : ℂ)‖ * ‖(u : ℂ)‖) := by
    rw [hsubst, norm_mul, norm_inv, norm_mul, div_eq_mul_inv]
  have hzn0 : 0 < ‖(z : ℂ)‖ := by linarith [hznorm1]
  have htri : ‖(z : ℂ)‖ ≤ ‖(u : ℂ)‖ + ‖(z : ℂ) - (u : ℂ)‖ := by
    calc ‖(z : ℂ)‖ = ‖(u : ℂ) + ((z : ℂ) - (u : ℂ))‖ := by ring_nf
      _ ≤ ‖(u : ℂ)‖ + ‖(z : ℂ) - (u : ℂ)‖ := norm_add_le _ _
  have hkey : (1 / 8) * ‖(z : ℂ)‖ ≤ (‖(u : ℂ)‖ + 1 / 8) * ‖(z : ℂ) - (u : ℂ)‖ := by
    nlinarith [hzu_ge, htri, hnu0]
  have hDpos : 0 < (‖(u : ℂ)‖ + 1 / 8) * ‖(u : ℂ)‖ := mul_pos (by linarith) hnu0
  have hζw_ge : (1 / 8 : ℝ) / ((‖(u : ℂ)‖ + 1 / 8) * ‖(u : ℂ)‖) ≤ ‖(ζ : ℂ) - (w : ℂ)‖ := by
    have h1 : (1 / 8 : ℝ) / (‖(u : ℂ)‖ + 1 / 8) ≤ ‖(z : ℂ) - (u : ℂ)‖ / ‖(z : ℂ)‖ := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < ‖(u : ℂ)‖ + 1 / 8) hzn0]
      linarith [hkey]
    have h2 : (1 / 8 : ℝ) / ((‖(u : ℂ)‖ + 1 / 8) * ‖(u : ℂ)‖)
        = (1 / 8 : ℝ) / (‖(u : ℂ)‖ + 1 / 8) / ‖(u : ℂ)‖ := by
      rw [div_eq_mul_inv, mul_inv_rev]
      ring
    have h3 : ‖(ζ : ℂ) - (w : ℂ)‖ = ‖(z : ℂ) - (u : ℂ)‖ / ‖(z : ℂ)‖ / ‖(u : ℂ)‖ := by
      rw [hnsub, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [h2, h3]
    exact (div_le_div_iff_of_pos_right hnu0).mpr h1
  have hζw_pos : 0 < ‖(ζ : ℂ) - (w : ℂ)‖ := by
    have h : 0 < (1 / 8 : ℝ) / ((‖(u : ℂ)‖ + 1 / 8) * ‖(u : ℂ)‖) :=
      div_pos (by norm_num) hDpos
    linarith
  have hζw_inv : ‖((ζ : ℂ) - (w : ℂ))⁻¹‖ ≤ 16 * (Work.Kernels.scale w) ^ 2 := by
    have h3 : ‖(ζ : ℂ) - (w : ℂ)‖⁻¹
        ≤ ((1 / 8 : ℝ) / ((‖(u : ℂ)‖ + 1 / 8) * ‖(u : ℂ)‖))⁻¹ := by
      rw [inv_le_inv₀ hζw_pos (div_pos (by norm_num) hDpos)]
      exact hζw_ge
    have h4 : ((1 / 8 : ℝ) / ((‖(u : ℂ)‖ + 1 / 8) * ‖(u : ℂ)‖))⁻¹
        = 8 * ((‖(u : ℂ)‖ + 1 / 8) * ‖(u : ℂ)‖) := by rw [inv_div]; ring
    have h5 : (‖(u : ℂ)‖ + 1 / 8) * ‖(u : ℂ)‖ ≤ 2 * (Work.Kernels.scale w) ^ 2 := by
      have h6 : ‖(u : ℂ)‖ + 1 / 8 ≤ 2 * Work.Kernels.scale w := by linarith
      calc (‖(u : ℂ)‖ + 1 / 8) * ‖(u : ℂ)‖
          ≤ (2 * Work.Kernels.scale w) * Work.Kernels.scale w :=
            mul_le_mul h6 hu_le hnu0.le (by linarith)
        _ = 2 * (Work.Kernels.scale w) ^ 2 := by ring
    calc ‖((ζ : ℂ) - (w : ℂ))⁻¹‖ = ‖(ζ : ℂ) - (w : ℂ)‖⁻¹ := norm_inv _
      _ ≤ ((1 / 8 : ℝ) / ((‖(u : ℂ)‖ + 1 / 8) * ‖(u : ℂ)‖))⁻¹ := h3
      _ = 8 * ((‖(u : ℂ)‖ + 1 / 8) * ‖(u : ℂ)‖) := h4
      _ ≤ 16 * (Work.Kernels.scale w) ^ 2 := by linarith [h5]
  have hpp : ‖((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
      ≤ (8 / Real.pi) * (Work.Kernels.scale w) ^ (2 : ℝ) := by
    have hn_norm : ‖(n : ℂ)‖ = 1 := by rcases hn with h | h <;> (rw [h]; norm_num)
    have h1 : ‖(n : ℂ) / (2 * (Real.pi : ℂ))‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_div, hn_norm, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, one_div]
    rw [norm_mul, h1]
    calc (2 * Real.pi)⁻¹ * ‖((ζ : ℂ) - (w : ℂ))⁻¹‖
        ≤ (2 * Real.pi)⁻¹ * (16 * (Work.Kernels.scale w) ^ 2) :=
          mul_le_mul_of_nonneg_left hζw_inv (by positivity)
      _ = 8 / Real.pi * (Work.Kernels.scale w) ^ (2 : ℝ) := by
          rw [Real.rpow_two]; ring
  -- final assembly
  have hN1 : (Work.Kernels.scale w) ^ N' ≤ (Work.Kernels.scale w) ^ (max N' 2) :=
    Real.rpow_le_rpow_of_exponent_le hscw (le_max_left _ _)
  have hN2 : (Work.Kernels.scale w) ^ ((2:ℝ)) ≤ (Work.Kernels.scale w) ^ (max N' 2) :=
    Real.rpow_le_rpow_of_exponent_le hscw (le_max_right _ _)
  have hC1 : 0 ≤ Ctot / (2 * cD) := div_nonneg hCtot_pos.le (by linarith)
  have hC2 : 0 ≤ 8 / Real.pi := by positivity
  calc ‖Kfun ℓ d τ ζ - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
      ≤ ‖Kfun ℓ d τ ζ‖ + ‖((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖ :=
        norm_sub_le _ _
    _ ≤ Ctot / (2 * cD) * (Work.Kernels.scale w) ^ N'
          + (8 / Real.pi) * (Work.Kernels.scale w) ^ (2 : ℝ) := add_le_add hKbound hpp
    _ ≤ Ctot / (2 * cD) * (Work.Kernels.scale w) ^ (max N' 2)
          + (8 / Real.pi) * (Work.Kernels.scale w) ^ (max N' 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hN1 hC1) (mul_le_mul_of_nonneg_left hN2 hC2)
    _ = (Ctot / (2 * cD) + 8 / Real.pi) * (Work.Kernels.scale w) ^ (max N' 2) := by ring

/-- **The off-spike bound, with the divisor and `Ξ` inputs discharged.**  The two hypotheses
`hDiv` and `hXi` of `offspike_bound_general` are supplied by the proved
`tile_divisor_lower_cone` and `tileXi_poly`; only the `Ncusp` cone bound remains. -/
theorem offspike_bound_E (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hNc : ∃ c C N : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ c ∧ c < 2 * Real.pi ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane), 1 ≤ z.im →
        ‖Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
          ≤ C * (Work.Kernels.scale w) ^ N
              * (1 + Real.exp (c * ((ModularGroup.S • w).im - z.im)))) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (ζ : UpperHalfPlane),
        1 ≤ ((ModularGroup.S • ζ : UpperHalfPlane)).im →
        (∀ k : ℤ, (1 / 8 : ℝ) ≤
          ‖((ModularGroup.S • ζ : UpperHalfPlane) : ℂ)
            - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖) →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
        ≤ C * (Work.Kernels.scale w) ^ N :=
  offspike_bound_general ℓ d hd tile_divisor_lower_cone (tileXi_poly ℓ d hd) hNc

/-- **The off-spike bound on the contour `ζ = i t`.**  In terms of the cone variable
`z = S • ζ = i/t` the off-spike condition reads `dist(i/t - S • w, ℤ) ≥ 1/8`.

The cone hypothesis `1 ≤ Im (S • ζ)` is automatic from `t ≤ 1`, and the conclusion is exactly
the tile principal-part bound for the contour points that are *off* the spike
(`dist(S ζ - S w, ℤ) ≥ 1/8`); the spike itself is the remaining case. -/
theorem offspike_window_bound (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hNc : ∃ c C N : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ c ∧ c < 2 * Real.pi ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane), 1 ≤ z.im →
        ‖Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
          ≤ C * (Work.Kernels.scale w) ^ N
              * (1 + Real.exp (c * ((ModularGroup.S • w).im - z.im)))) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ t : ℝ, w.im / 2 ≤ t → t ≤ 1 →
        (∀ k : ℤ, (1 / 8 : ℝ) ≤
          ‖Complex.I / (t : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)
            - ((k : ℤ) : ℂ)‖) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
        ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C₀, N₀, hC₀, hN₀, hb⟩ := offspike_bound_E ℓ d hd hNc
  refine ⟨C₀, N₀, hC₀, hN₀, ?_⟩
  intro w hw n hn t h1 h2 hsep
  have ht : 0 < t := lt_of_lt_of_le (by linarith [w.im_pos]) h1
  have hcoe : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  -- the `S`-image of the contour point is `i/t`
  have hS : ((ModularGroup.S • Work.Kernels.imagAxis t ht : ℍ) : ℂ) = Complex.I * ((t : ℂ))⁻¹ := by
    rw [modular_S_smul, UpperHalfPlane.coe_mk, inv_neg, hcoe]
    field_simp
    rw [Complex.I_sq]
    ring
  have him : (Complex.I * ((t : ℂ))⁻¹).im = 1 / t := by
    rw [Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.normSq_ofReal,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    norm_num
  have hone : 1 ≤ ((ModularGroup.S • Work.Kernels.imagAxis t ht : ℍ)).im := by
    rw [← UpperHalfPlane.coe_im, hS, him]
    exact one_le_one_div ht h2
  have hb' := hb w hw n hn (Work.Kernels.imagAxis t ht) hone
    (fun k => by rw [hS]; exact hsep k)
  rw [Work.Kernels.Kaxis, dif_pos ht, hcoe] at *
  exact hb'

end Work.Asymptotics
