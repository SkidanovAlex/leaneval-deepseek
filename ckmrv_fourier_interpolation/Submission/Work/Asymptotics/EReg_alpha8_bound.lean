import Mathlib
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.ERegDefs
import Submission.Work.Asymptotics.EReg_identities
import Submission.Work.Asymptotics.EReg_atom_bounds

/-!
# Power bounds for the `d = 8` cusp coefficients on the CKMRV `E`-tile

Writing `αᵢ = Alpha ℓ 8 i τ` (`Work.Asymptotics.Alpha`), `U = θ₀₀⁴`, `V = θ₁₀⁴`,
`W = θ₀₁⁴`, `𝓛 = ℓ.L`, `𝓛_S = ℓ.L_S`, this file proves that on the cusp-`0` tile
`EReg = {τ | 3/2 ≤ (S • τ).im}` the three quantities `α₀`, `α₂` and `α₁ - α₂ j` are bounded
by a power of `scale τ`:

  `α₀ = E₄`,  `α₂ = ψ₄`,  `α₁ - α₂·j = -(9/2)(E₄²/Δ)(𝓛·UV²W + 𝓛_S·UVW²)`,

the last identity coming from the exact factorisations of `Work.Asymptotics.EReg_identities`
(`ξ₂E₆ - ξ₄E₄ = -(9/2)UV²W` and `(ξ₂|₂S)E₆ - (ξ₄|₄S)E₄ = -(9/2)UVW²`), together with
`E₁₄ = E₄²E₆` and `j = E₄³/Δ`.  The two `tS τ²` factors carried by `𝓛·UV²W` and by
`𝓛_S·UVW²` cancel against the `tS τ²` in the *lower* bound `‖Δ‖ ≥ c·tS τ²`, giving a pure
power of `scale τ`.

All analytic input is `Work.Asymptotics.EReg_atom_bounds`.
-/

noncomputable section

open UpperHalfPlane ModularGroup
open scoped ModularForm

namespace Work.Asymptotics

open Work.Kernels (scale)

/-! ## Two elementary classes of power bounds -/

/-- `PD τ X c m` is the power bound `‖X‖ ≤ c (scale τ)^m`. -/
private def PD (τ : ℍ) (X : ℂ) (c : ℝ) (m : ℕ) : Prop := ‖X‖ ≤ c * (scale τ) ^ m

/-- `PT τ X c m k` is the power bound `‖X‖ ≤ c (scale τ)^m (tS τ)^k`. -/
private def PT (τ : ℍ) (X : ℂ) (c : ℝ) (m k : ℕ) : Prop :=
  ‖X‖ ≤ c * (scale τ) ^ m * tS τ ^ k

private lemma PD_mul {τ : ℍ} {X Y : ℂ} {a c : ℝ} {m₁ m₂ : ℕ}
    (hX : PD τ X a m₁) (hY : PD τ Y c m₂) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    PD τ (X * Y) (a * c) (m₁ + m₂) := by
  have ha0 : (0 : ℝ) ≤ a * (scale τ) ^ m₁ :=
    mul_nonneg ha (pow_nonneg (Work.Kernels.scale_pos τ).le m₁)
  have h : ‖X * Y‖ ≤ (a * (scale τ) ^ m₁) * (c * (scale τ) ^ m₂) := by
    rw [norm_mul]
    exact mul_le_mul hX hY (norm_nonneg Y) ha0
  refine le_trans h ?_
  rw [pow_add]
  exact le_of_eq (by ring)

private lemma PD_add {τ : ℍ} {X Y : ℂ} {a c : ℝ} {m : ℕ}
    (hX : PD τ X a m) (hY : PD τ Y c m) : PD τ (X + Y) (a + c) m := by
  calc ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := norm_add_le _ _
    _ ≤ a * (scale τ) ^ m + c * (scale τ) ^ m := add_le_add hX hY
    _ = (a + c) * (scale τ) ^ m := by ring

private lemma PD_sub {τ : ℍ} {X Y : ℂ} {a c : ℝ} {m : ℕ}
    (hX : PD τ X a m) (hY : PD τ Y c m) : PD τ (X - Y) (a + c) m := by
  calc ‖X - Y‖ ≤ ‖X‖ + ‖Y‖ := norm_sub_le _ _
    _ ≤ a * (scale τ) ^ m + c * (scale τ) ^ m := add_le_add hX hY
    _ = (a + c) * (scale τ) ^ m := by ring

private lemma PD_neg {τ : ℍ} {X : ℂ} {a : ℝ} {m : ℕ} (hX : PD τ X a m) : PD τ (-X) a m := by
  rw [PD] at hX ⊢
  rwa [norm_neg]

private lemma PD_sq {τ : ℍ} {X : ℂ} {a : ℝ} {m : ℕ} (ha : 0 ≤ a) (hX : PD τ X a m) :
    PD τ (X ^ 2) (a ^ 2) (m + m) := by
  have h : ‖X ^ 2‖ ≤ (a * (scale τ) ^ m) ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hX 2
  refine le_trans h ?_
  rw [pow_two, pow_two, pow_add]
  exact le_of_eq (by ring)

private lemma PD_mono {τ : ℍ} {X : ℂ} {a b : ℝ} {m m' : ℕ}
    (h : PD τ X a m) (hab : a ≤ b) (hmm : m ≤ m') (hb : 0 ≤ b) : PD τ X b m' :=
  le_trans h (mul_le_mul hab (pow_le_pow_right₀ (Work.Kernels.one_le_scale τ) hmm)
    (pow_nonneg (Work.Kernels.scale_pos τ).le m) hb)

private lemma PD_two (τ : ℍ) : PD τ (2 : ℂ) 2 0 := by
  rw [PD]
  norm_num

private lemma PD_of_PT {τ : ℍ} {X : ℂ} {c : ℝ} {m k : ℕ} (h : PT τ X c m k) (hc : 0 ≤ c) :
    PD τ X c m := by
  show ‖X‖ ≤ c * (scale τ) ^ m
  refine le_trans h ?_
  exact mul_le_of_le_one_right
    (mul_nonneg hc (pow_nonneg (Work.Kernels.scale_pos τ).le m))
    (pow_le_one₀ (tS_nonneg τ) (tS_le_one τ) : tS τ ^ k ≤ 1)

private lemma PT_of_PD {τ : ℍ} {X : ℂ} {c : ℝ} {m : ℕ} (h : PD τ X c m) : PT τ X c m 0 := by
  show ‖X‖ ≤ c * (scale τ) ^ m * tS τ ^ 0
  rw [PD] at h
  simpa using h

private lemma PT_mul {τ : ℍ} {X Y : ℂ} {a c : ℝ} {m₁ k₁ m₂ k₂ : ℕ}
    (hX : PT τ X a m₁ k₁) (hY : PT τ Y c m₂ k₂) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    PT τ (X * Y) (a * c) (m₁ + m₂) (k₁ + k₂) := by
  have ha0 : (0 : ℝ) ≤ a * (scale τ) ^ m₁ * tS τ ^ k₁ :=
    mul_nonneg (mul_nonneg ha (pow_nonneg (Work.Kernels.scale_pos τ).le m₁))
      (pow_nonneg (tS_nonneg τ) k₁)
  have h : ‖X * Y‖ ≤
      (a * (scale τ) ^ m₁ * tS τ ^ k₁) * (c * (scale τ) ^ m₂ * tS τ ^ k₂) := by
    rw [norm_mul]
    exact mul_le_mul hX hY (norm_nonneg Y) ha0
  refine le_trans h ?_
  rw [pow_add, pow_add]
  exact le_of_eq (by ring)

private lemma PT_sq {τ : ℍ} {X : ℂ} {a : ℝ} {m k : ℕ} (ha : 0 ≤ a) (hX : PT τ X a m k) :
    PT τ (X ^ 2) (a ^ 2) (m + m) (k + k) := by
  have h : ‖X ^ 2‖ ≤ (a * (scale τ) ^ m * tS τ ^ k) ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hX 2
  refine le_trans h ?_
  rw [pow_two, pow_two, pow_add, pow_add]
  exact le_of_eq (by ring)

private lemma PT_mono {τ : ℍ} {X : ℂ} {a b : ℝ} {m k m' k' : ℕ}
    (h : PT τ X a m k) (hab : a ≤ b) (hmm : m ≤ m') (hkk : k' ≤ k) (hb : 0 ≤ b) :
    PT τ X b m' k' := by
  have hd : (scale τ) ^ m ≤ (scale τ) ^ m' := pow_le_pow_right₀ (Work.Kernels.one_le_scale τ) hmm
  have ht : tS τ ^ k ≤ tS τ ^ k' := pow_le_pow_of_le_one (tS_nonneg τ) (tS_le_one τ) hkk
  have hb' : (0 : ℝ) ≤ b * (scale τ) ^ m' :=
    mul_nonneg hb (pow_nonneg (Work.Kernels.scale_pos τ).le m')
  calc ‖X‖ ≤ a * (scale τ) ^ m * tS τ ^ k := h
    _ ≤ b * (scale τ) ^ m' * tS τ ^ k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hab hd (pow_nonneg (Work.Kernels.scale_pos τ).le m) hb)
          (pow_nonneg (tS_nonneg τ) k)
    _ ≤ b * (scale τ) ^ m' * tS τ ^ k' := mul_le_mul_of_nonneg_left ht hb'

/-! ## Conversion and combination lemmas -/

/-- Enlarge the constant and the exponent of a plain power bound. -/
private lemma pow_bound_mono {τ : ℍ} {X : ℂ} {c K : ℝ} {m M : ℕ}
    (h : ‖X‖ ≤ c * (scale τ) ^ m) (hcK : c ≤ K) (hK : 0 ≤ K) (hm : m ≤ M) :
    ‖X‖ ≤ K * (scale τ) ^ M :=
  le_trans h (mul_le_mul hcK (pow_le_pow_right₀ (Work.Kernels.one_le_scale τ) hm)
    (pow_nonneg (Work.Kernels.scale_pos τ).le m) hK)

/-- Multiplying a power bound by a nonnegative real constant. -/
private lemma const_mul_bound {τ : ℍ} {X : ℂ} {c : ℝ} {m : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (h : ‖X‖ ≤ c * (scale τ) ^ m) : ‖(r : ℂ) * X‖ ≤ (r * c) * (scale τ) ^ m := by
  calc ‖(r : ℂ) * X‖ = r * ‖X‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
    _ ≤ r * (c * (scale τ) ^ m) := mul_le_mul_of_nonneg_left h hr
    _ = (r * c) * (scale τ) ^ m := by ring

/-- The sharp lower bound `‖Δ τ‖ ≥ c·tS τ²` on the `E`-tile, obtained by transporting the
cusp-`0` lower bound through `S`. -/
private theorem EReg_Delta_lower8 : ∃ c : ℝ, 0 < c ∧ ∀ τ : ℍ, τ ∈ EReg →
    c * tS τ ^ 2 ≤ ‖Work.Kernels.DeltaFun τ‖ := by
  obtain ⟨cΔ, hcΔ, hΔ⟩ := Work.Asymptotics.DeltaFun_lower
  refine ⟨(3 / 2 : ℝ) ^ 12 * cΔ, by positivity, fun τ hτ => ?_⟩
  have hw1 : (1 : ℝ) ≤ (ModularGroup.S • τ).im := le_trans (by norm_num) hτ
  have hb : cΔ * tS τ ^ 2 ≤ ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ := by
    have h := hΔ _ hw1
    rw [show ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ = tS τ ^ 2 from
      (EReg_tpar_S_sq_eq τ).symm] at h
    exact h
  have hn : (3 / 2 : ℝ) ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ := EReg_norm_S_ge τ hτ
  have h12 : (3 / 2 : ℝ) ^ 12 ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 12 :=
    pow_le_pow_left₀ (by norm_num) hn 12
  rw [EReg_Delta_S τ, norm_mul, norm_pow]
  calc (3 / 2 : ℝ) ^ 12 * cΔ * tS τ ^ 2
      = (3 / 2 : ℝ) ^ 12 * (cΔ * tS τ ^ 2) := by ring
    _ ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 12
          * ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ :=
        mul_le_mul h12 hb (by positivity) (by positivity)

/-- Inverting the lower bound for `Δ`. -/
private lemma Delta_inv_le {τ : ℍ} {c : ℝ} (hc : 0 < c)
    (hΔ : c * tS τ ^ 2 ≤ ‖Work.Kernels.DeltaFun τ‖) :
    ‖(Work.Kernels.DeltaFun τ)⁻¹‖ ≤ c⁻¹ * (tS τ ^ 2)⁻¹ := by
  rw [norm_inv]
  have hpos : 0 < c * tS τ ^ 2 := mul_pos hc (pow_pos (tS_pos τ) 2)
  calc ‖Work.Kernels.DeltaFun τ‖⁻¹ ≤ (c * tS τ ^ 2)⁻¹ := inv_anti₀ hpos hΔ
    _ = c⁻¹ * (tS τ ^ 2)⁻¹ := by rw [mul_inv]

/-- Dividing a `(tS τ)^k`-carrying bound, `k ≥ 2`, by `Δ`, using the sharp lower bound
`‖Δ‖ ≥ c·tS²`. -/
private lemma PT_mul_Delta_inv {τ : ℍ} {x : ℂ} {B c : ℝ} {m k : ℕ}
    (hx : PT τ x B m k) (hk : 2 ≤ k) (hc : 0 < c)
    (hΔ : c * tS τ ^ 2 ≤ ‖Work.Kernels.DeltaFun τ‖) (hB : 0 ≤ B) :
    PD τ (x * (Work.Kernels.DeltaFun τ)⁻¹) (B / c) m := by
  have ht2 : tS τ ^ k ≤ tS τ ^ 2 := pow_le_pow_of_le_one (tS_nonneg τ) (tS_le_one τ) hk
  have hB0 : (0 : ℝ) ≤ B * (scale τ) ^ m :=
    mul_nonneg hB (pow_nonneg (Work.Kernels.scale_pos τ).le m)
  have hx' : ‖x‖ ≤ B * (scale τ) ^ m * tS τ ^ 2 :=
    le_trans hx (mul_le_mul_of_nonneg_left ht2 hB0)
  have hDinv := Delta_inv_le hc hΔ
  have hts : (0 : ℝ) < tS τ ^ 2 := pow_pos (tS_pos τ) 2
  rw [PD, norm_mul]
  calc ‖x‖ * ‖(Work.Kernels.DeltaFun τ)⁻¹‖
      ≤ (B * (scale τ) ^ m * tS τ ^ 2) * (c⁻¹ * (tS τ ^ 2)⁻¹) :=
        mul_le_mul hx' hDinv (norm_nonneg _) (by positivity)
    _ = B / c * (scale τ) ^ m := by
        rw [show (B * (scale τ) ^ m * tS τ ^ 2) * (c⁻¹ * (tS τ ^ 2)⁻¹)
              = B * c⁻¹ * (scale τ) ^ m * (tS τ ^ 2 * (tS τ ^ 2)⁻¹) from by ring,
          mul_inv_cancel₀ (ne_of_gt hts), mul_one, div_eq_mul_inv]

/-! ## The `d = 8` coefficients -/

private lemma Alpha8_zero (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 8 0 τ = Work.Kernels.E4Fun τ := by
  simp [Alpha, Work.Kernels.psiVec, vlen, Work.Kernels.fk]

private lemma Alpha8_two (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 8 2 τ = Work.Kernels.psi4 ℓ τ := by
  simp [Alpha, Work.Kernels.psiVec, vlen, Work.Kernels.fk]

private lemma Alpha8_one (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 8 1 τ = Work.Kernels.psi2 ℓ τ * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) := by
  simp [Alpha, Work.Kernels.psiVec, vlen, Work.Kernels.fk]

private lemma psi2_expand (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.psi2 ℓ τ
      = (Work.Kernels.UFun τ + Work.Kernels.WFun τ) * ℓ.L τ
        - (Work.Kernels.UFun τ + Work.Kernels.VFun τ) * ℓ.L_S τ := by
  rw [Work.Kernels.psi2, Work.Kernels.KernelFacts.xi2Fun_slash_S,
    show Work.Kernels.xi2Fun τ = Work.Kernels.UFun τ + Work.Kernels.WFun τ from rfl]
  ring

private lemma psi4_expand (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.psi4 ℓ τ
      = (Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2)
          * ℓ.L τ
        + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2)
          * ℓ.L_S τ := by
  rw [Work.Kernels.psi4, Work.Kernels.KernelFacts.xi4S_apply,
    show Work.Kernels.xi4Fun τ
      = Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2
      from rfl]

/-- `ψ₂E₆ - ψ₄E₄ = -(9/2)(𝓛·UV²W + 𝓛_S·UVW²)`, the cancellation identity of the `E`-order
estimate (the `d = 8` counterpart of `Alpha24_diff`). -/
private lemma psi2E6_sub_psi4E4 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ
      - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ
      = -(9 / 2 : ℂ)
        * (ℓ.L τ * (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2 * Work.Kernels.WFun τ)
          + ℓ.L_S τ * (Work.Kernels.UFun τ * Work.Kernels.VFun τ * Work.Kernels.WFun τ ^ 2)) := by
  obtain ⟨h1, h2, -, -⟩ := EReg_identities τ
  have h1' : (Work.Kernels.UFun τ + Work.Kernels.WFun τ) * Work.Kernels.E6Fun τ
      - (Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2)
        * Work.Kernels.E4Fun τ
      = -(9 / 2 : ℂ) * (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2 * Work.Kernels.WFun τ) :=
    h1
  have h2' : (-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * Work.Kernels.E6Fun τ
      - (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2)
        * Work.Kernels.E4Fun τ
      = -(9 / 2 : ℂ)
        * (Work.Kernels.UFun τ * Work.Kernels.VFun τ * Work.Kernels.WFun τ ^ 2) := by
    simpa only [Work.Kernels.KernelFacts.xi2Fun_slash_S τ, Work.Kernels.KernelFacts.xi4S_apply τ]
      using h2
  rw [psi2_expand ℓ τ, psi4_expand ℓ τ]
  have hid : ((Work.Kernels.UFun τ + Work.Kernels.WFun τ) * ℓ.L τ
        - (Work.Kernels.UFun τ + Work.Kernels.VFun τ) * ℓ.L_S τ)
        * Work.Kernels.E6Fun τ
      - ((Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2)
            * ℓ.L τ
          + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
              - 2 * Work.Kernels.WFun τ ^ 2) * ℓ.L_S τ)
        * Work.Kernels.E4Fun τ
      = ℓ.L τ
          * ((Work.Kernels.UFun τ + Work.Kernels.WFun τ) * Work.Kernels.E6Fun τ
            - (Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
                - 2 * Work.Kernels.VFun τ ^ 2) * Work.Kernels.E4Fun τ)
        + ℓ.L_S τ
          * ((-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * Work.Kernels.E6Fun τ
            - (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
                - 2 * Work.Kernels.WFun τ ^ 2) * Work.Kernels.E4Fun τ) := by
    ring
  rw [hid, h1', h2']
  ring

/-- `α₁ - α₂ j = -(9/2)(E₄²/Δ)(𝓛·UV²W + 𝓛_S·UVW²)`. -/
private lemma Alpha8_diff (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 8 1 τ - Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ
      = -(9 / 2 : ℂ) * (Work.Kernels.E4Fun τ ^ 2 / Work.Kernels.DeltaFun τ)
          * (ℓ.L τ * (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2 * Work.Kernels.WFun τ)
            + ℓ.L_S τ
              * (Work.Kernels.UFun τ * Work.Kernels.VFun τ * Work.Kernels.WFun τ ^ 2)) := by
  have hkey := psi2E6_sub_psi4E4 ℓ τ
  have hL : Alpha ℓ 8 1 τ - Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ
      = (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ
          - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 3) / Work.Kernels.DeltaFun τ := by
    rw [Alpha8_one ℓ τ, Alpha8_two ℓ τ,
      show Work.Kernels.jInvariantFun τ
        = Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ from rfl]
    ring
  rw [hL, show Work.Kernels.E14Fun τ = Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ from rfl]
  rw [show Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
        - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 3
      = Work.Kernels.E4Fun τ ^ 2 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ
          - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ) from by ring]
  rw [hkey]
  ring

/-! ## The main bound -/

theorem EReg_alpha8_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.EReg →
      ‖Work.Asymptotics.Alpha ℓ 8 0 τ‖ ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Asymptotics.Alpha ℓ 8 2 τ‖ ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Asymptotics.Alpha ℓ 8 1 τ
          - Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := EReg_atom_bounds ℓ
  obtain ⟨cd, hcd, hΔlow⟩ := EReg_Delta_lower8
  obtain ⟨C1, hCC1, hC1ge1⟩ : ∃ C1 : ℝ, C ≤ C1 ∧ 1 ≤ C1 :=
    ⟨max C 1, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, N ≤ (n : ℝ) := ⟨Nat.ceil N, Nat.le_ceil N⟩
  have hC1pos : 0 < C1 := lt_of_lt_of_le zero_lt_one hC1ge1
  have hC1nn : (0 : ℝ) ≤ C1 := hC1pos.le
  set K : ℝ := C1 + 8 * C1 ^ 3 + 9 * C1 ^ 7 / cd + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have h2 : (0 : ℝ) ≤ 8 * C1 ^ 3 := by positivity
    have h3 : (0 : ℝ) ≤ 9 * C1 ^ 7 / cd := by positivity
    linarith
  have hKnn : (0 : ℝ) ≤ K := hKpos.le
  have hKge1 : C1 ≤ K := by
    rw [hKdef]
    have h2 : (0 : ℝ) ≤ 8 * C1 ^ 3 := by positivity
    have h3 : (0 : ℝ) ≤ 9 * C1 ^ 7 / cd := by positivity
    linarith
  have hKge2 : 8 * C1 ^ 3 ≤ K := by
    rw [hKdef]
    have h3 : (0 : ℝ) ≤ 9 * C1 ^ 7 / cd := by positivity
    linarith
  have hKge3 : 9 * C1 ^ 7 / cd ≤ K := by
    rw [hKdef]
    have h2 : (0 : ℝ) ≤ 8 * C1 ^ 3 := by positivity
    linarith
  refine ⟨K, ((14 * n + 1 : ℕ) : ℝ), hKpos, by positivity, fun τ hτ => ?_⟩
  obtain ⟨hU, hV, hW, hE4, hE6, hΔu, _hΔl, hL, hLS, hj, _hjΔ⟩ := hb τ hτ
  have hdpos : (0 : ℝ) < scale τ := Work.Kernels.scale_pos τ
  have hd1 : (1 : ℝ) ≤ scale τ := Work.Kernels.one_le_scale τ
  have hdN : (scale τ) ^ N ≤ (scale τ) ^ n := by
    rw [← Real.rpow_natCast (scale τ) n]
    exact Real.rpow_le_rpow_of_exponent_le hd1 hn
  -- plain power bounds for the atoms
  have hUpd : PD τ (Work.Kernels.UFun τ) C1 n :=
    le_trans hU (mul_le_mul hCC1 hdN (Real.rpow_nonneg hdpos.le N) hC1nn)
  have hVpd : PD τ (Work.Kernels.VFun τ) C1 n :=
    le_trans hV (mul_le_mul hCC1 hdN (Real.rpow_nonneg hdpos.le N) hC1nn)
  have hE4pd : PD τ (Work.Kernels.E4Fun τ) C1 n :=
    le_trans hE4 (mul_le_mul hCC1 hdN (Real.rpow_nonneg hdpos.le N) hC1nn)
  have hE6pd : PD τ (Work.Kernels.E6Fun τ) C1 n :=
    le_trans hE6 (mul_le_mul hCC1 hdN (Real.rpow_nonneg hdpos.le N) hC1nn)
  have hLSpd : PD τ (ℓ.L_S τ) C1 n :=
    le_trans hLS (mul_le_mul hCC1 hdN (Real.rpow_nonneg hdpos.le N) hC1nn)
  have hWpd : PD τ (Work.Kernels.WFun τ) C1 n := by
    refine le_trans hW ?_
    calc C * (scale τ) ^ N * tS τ ≤ C1 * (scale τ) ^ n * tS τ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hCC1 hdN (Real.rpow_nonneg hdpos.le N) hC1nn) (tS_nonneg τ)
      _ ≤ C1 * (scale τ) ^ n :=
          mul_le_of_le_one_right (mul_nonneg hC1nn (pow_nonneg hdpos.le n)) (tS_le_one τ)
  have hLpd : PD τ (ℓ.L τ) C1 n := by
    refine le_trans hL ?_
    calc C * (scale τ) ^ N * tS τ ≤ C1 * (scale τ) ^ n * tS τ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hCC1 hdN (Real.rpow_nonneg hdpos.le N) hC1nn) (tS_nonneg τ)
      _ ≤ C1 * (scale τ) ^ n :=
          mul_le_of_le_one_right (mul_nonneg hC1nn (pow_nonneg hdpos.le n)) (tS_le_one τ)
  -- squares
  have hU2 : PD τ (Work.Kernels.UFun τ ^ 2) (C1 ^ 2) (n + n) := PD_sq hC1nn hUpd
  have hW2 : PD τ (Work.Kernels.WFun τ ^ 2) (C1 ^ 2) (n + n) := PD_sq hC1nn hWpd
  have hV2 : PD τ (Work.Kernels.VFun τ ^ 2) (C1 ^ 2) (n + n) := PD_sq hC1nn hVpd
  have h2V2 : PD τ ((2 : ℂ) * Work.Kernels.VFun τ ^ 2) (2 * C1 ^ 2) (n + n) :=
    PD_mono (PD_mul (PD_two τ) hV2 (by norm_num) (by positivity)) le_rfl (by omega)
      (by positivity)
  have h2W2 : PD τ ((2 : ℂ) * Work.Kernels.WFun τ ^ 2) (2 * C1 ^ 2) (n + n) :=
    PD_mono (PD_mul (PD_two τ) hW2 (by norm_num) (by positivity)) le_rfl (by omega)
      (by positivity)
  -- the `tS`-carrying bounds of `𝓛` and `W`
  have hLpt : PT τ (ℓ.L τ) C1 n 1 := by
    show ‖ℓ.L τ‖ ≤ C1 * (scale τ) ^ n * tS τ ^ 1
    calc ‖ℓ.L τ‖ ≤ C * (scale τ) ^ N * tS τ := hL
      _ ≤ C1 * (scale τ) ^ n * tS τ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hCC1 hdN (Real.rpow_nonneg hdpos.le N) hC1nn) (tS_nonneg τ)
      _ = C1 * (scale τ) ^ n * tS τ ^ 1 := by rw [pow_one]
  have hWpt : PT τ (Work.Kernels.WFun τ) C1 n 1 := by
    show ‖Work.Kernels.WFun τ‖ ≤ C1 * (scale τ) ^ n * tS τ ^ 1
    calc ‖Work.Kernels.WFun τ‖ ≤ C * (scale τ) ^ N * tS τ := hW
      _ ≤ C1 * (scale τ) ^ n * tS τ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hCC1 hdN (Real.rpow_nonneg hdpos.le N) hC1nn) (tS_nonneg τ)
      _ = C1 * (scale τ) ^ n * tS τ ^ 1 := by rw [pow_one]
  refine ⟨?_, ?_, ?_⟩
  · -- `α₀ = E₄`
    rw [Alpha8_zero ℓ τ, Real.rpow_natCast]
    exact pow_bound_mono hE4pd hKge1 hKnn (by omega)
  · -- `α₂ = ψ₄`
    rw [Alpha8_two ℓ τ, psi4_expand ℓ τ, Real.rpow_natCast]
    have hin1 : PD τ (Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
        - 2 * Work.Kernels.VFun τ ^ 2) ((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) (n + n) :=
      PD_sub (PD_add hU2 hW2) h2V2
    have hin2 : PD τ (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
        - 2 * Work.Kernels.WFun τ ^ 2) ((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) (n + n) :=
      PD_sub (PD_add hU2 hV2) h2W2
    have hs1 : PD τ ((Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
        - 2 * Work.Kernels.VFun τ ^ 2) * ℓ.L τ) (((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) * C1)
        ((n + n) + n) := PD_mul hin1 hLpd (by positivity) hC1nn
    have hs2 : PD τ ((Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
        - 2 * Work.Kernels.WFun τ ^ 2) * ℓ.L_S τ) (((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) * C1)
        ((n + n) + n) := PD_mul hin2 hLSpd (by positivity) hC1nn
    have hpsi : PD τ ((Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
          - 2 * Work.Kernels.VFun τ ^ 2) * ℓ.L τ
        + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
          - 2 * Work.Kernels.WFun τ ^ 2) * ℓ.L_S τ)
        ((((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) * C1)
          + (((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) * C1)) ((n + n) + n) := PD_add hs1 hs2
    refine pow_bound_mono hpsi ?_ hKnn (by omega)
    have e1 : ((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) * C1
        + (((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) * C1) = 8 * C1 ^ 3 := by ring
    rw [e1]
    exact hKge2
  · -- `α₁ - α₂ j`
    rw [Alpha8_diff ℓ τ, Real.rpow_natCast]
    rw [show -(9 / 2 : ℂ) * (Work.Kernels.E4Fun τ ^ 2 / Work.Kernels.DeltaFun τ)
          * (ℓ.L τ * (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2 * Work.Kernels.WFun τ)
            + ℓ.L_S τ
              * (Work.Kernels.UFun τ * Work.Kernels.VFun τ * Work.Kernels.WFun τ ^ 2))
        = -((9 / 2 : ℂ)
          * ((Work.Kernels.E4Fun τ ^ 2
                * (ℓ.L τ
                  * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2)
                    * Work.Kernels.WFun τ)))
              * (Work.Kernels.DeltaFun τ)⁻¹
            + (Work.Kernels.E4Fun τ ^ 2
                * (ℓ.L_S τ
                  * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ)
                    * Work.Kernels.WFun τ ^ 2)))
              * (Work.Kernels.DeltaFun τ)⁻¹)) from by ring]
    rw [norm_neg, show (9 / 2 : ℂ) = ((9 / 2 : ℝ) : ℂ) by norm_num]
    have hUpt : PT τ (Work.Kernels.UFun τ) C1 n 0 := PT_of_PD hUpd
    have hVpt : PT τ (Work.Kernels.VFun τ) C1 n 0 := PT_of_PD hVpd
    have hE4pt : PT τ (Work.Kernels.E4Fun τ) C1 n 0 := PT_of_PD hE4pd
    have hL_Spt : PT τ (ℓ.L_S τ) C1 n 0 := PT_of_PD hLSpd
    have hV2pt : PT τ (Work.Kernels.VFun τ ^ 2) (C1 ^ 2) (n + n) 0 := PT_of_PD hV2
    have hE4sq : PT τ (Work.Kernels.E4Fun τ ^ 2) (C1 ^ 2) (2 * n) 0 :=
      PT_mono (PT_sq hC1nn hE4pt) le_rfl (by omega) (by omega) (by positivity)
    have hW2t : PT τ (Work.Kernels.WFun τ ^ 2) (C1 ^ 2) (n + n) (1 + 1) := PT_sq hC1nn hWpt
    -- first term: `E₄²·(𝓛·(UV²W))`
    have ha1 : PT τ (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2) (C1 * C1 ^ 2) (3 * n) 0 :=
      PT_mono (PT_mul hUpt hV2pt hC1nn (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have hb1 : PT τ ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2)
        * Work.Kernels.WFun τ) ((C1 * C1 ^ 2) * C1) (4 * n) 1 :=
      PT_mono (PT_mul ha1 hWpt (by positivity) hC1nn) le_rfl (by omega) (by omega)
        (by positivity)
    have hc1 : PT τ (ℓ.L τ
        * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2) * Work.Kernels.WFun τ))
        (C1 * ((C1 * C1 ^ 2) * C1)) (5 * n) 2 :=
      PT_mono (PT_mul hLpt hb1 hC1nn (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have hx1 : PT τ (Work.Kernels.E4Fun τ ^ 2
        * (ℓ.L τ * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2)
          * Work.Kernels.WFun τ)))
        (C1 ^ 2 * (C1 * ((C1 * C1 ^ 2) * C1))) (7 * n) 2 :=
      PT_mono (PT_mul hE4sq hc1 (by positivity) (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have hPD1 : PD τ (Work.Kernels.E4Fun τ ^ 2
        * (ℓ.L τ * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2)
          * Work.Kernels.WFun τ))
        * (Work.Kernels.DeltaFun τ)⁻¹)
        (C1 ^ 2 * (C1 * ((C1 * C1 ^ 2) * C1)) / cd) (7 * n) :=
      PT_mul_Delta_inv hx1 (by omega) hcd (hΔlow τ hτ) (by positivity)
    -- second term: `E₄²·(𝓛_S·(UVW²))`
    have ha2 : PT τ (Work.Kernels.UFun τ * Work.Kernels.VFun τ) (C1 * C1) (3 * n) 0 :=
      PT_mono (PT_mul hUpt hVpt hC1nn hC1nn) le_rfl (by omega) (by omega) (by positivity)
    have hb2 : PT τ ((Work.Kernels.UFun τ * Work.Kernels.VFun τ) * Work.Kernels.WFun τ ^ 2)
        ((C1 * C1) * C1 ^ 2) (5 * n) 2 :=
      PT_mono (PT_mul ha2 hW2t (by positivity) (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have hc2 : PT τ (ℓ.L_S τ
        * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ) * Work.Kernels.WFun τ ^ 2))
        (C1 * ((C1 * C1) * C1 ^ 2)) (6 * n) 2 :=
      PT_mono (PT_mul hL_Spt hb2 hC1nn (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have hx2 : PT τ (Work.Kernels.E4Fun τ ^ 2
        * (ℓ.L_S τ * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ)
          * Work.Kernels.WFun τ ^ 2)))
        (C1 ^ 2 * (C1 * ((C1 * C1) * C1 ^ 2))) (8 * n) 2 :=
      PT_mono (PT_mul hE4sq hc2 (by positivity) (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have hPD2 : PD τ (Work.Kernels.E4Fun τ ^ 2
        * (ℓ.L_S τ * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ)
          * Work.Kernels.WFun τ ^ 2))
        * (Work.Kernels.DeltaFun τ)⁻¹)
        (C1 ^ 2 * (C1 * ((C1 * C1) * C1 ^ 2)) / cd) (8 * n) :=
      PT_mul_Delta_inv hx2 (by omega) hcd (hΔlow τ hτ) (by positivity)
    have hPD1' : PD τ (Work.Kernels.E4Fun τ ^ 2
        * (ℓ.L τ * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2)
          * Work.Kernels.WFun τ))
        * (Work.Kernels.DeltaFun τ)⁻¹)
        (C1 ^ 2 * (C1 * ((C1 * C1 ^ 2) * C1)) / cd) (8 * n) :=
      PD_mono hPD1 le_rfl (by omega) (by positivity)
    have hsum : PD τ (Work.Kernels.E4Fun τ ^ 2
          * (ℓ.L τ * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2)
            * Work.Kernels.WFun τ))
          * (Work.Kernels.DeltaFun τ)⁻¹
        + Work.Kernels.E4Fun τ ^ 2
          * (ℓ.L_S τ * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ)
            * Work.Kernels.WFun τ ^ 2))
          * (Work.Kernels.DeltaFun τ)⁻¹)
        (C1 ^ 2 * (C1 * ((C1 * C1 ^ 2) * C1)) / cd
          + C1 ^ 2 * (C1 * ((C1 * C1) * C1 ^ 2)) / cd) (8 * n) := PD_add hPD1' hPD2
    have hconst := const_mul_bound (τ := τ) (r := 9 / 2) (by norm_num) hsum
    refine pow_bound_mono hconst ?_ hKnn (by omega)
    have e1 : C1 ^ 2 * (C1 * ((C1 * C1 ^ 2) * C1)) = C1 ^ 7 := by ring
    have e2 : C1 ^ 2 * (C1 * ((C1 * C1) * C1 ^ 2)) = C1 ^ 7 := by ring
    rw [e1, e2]
    have e3 : (9 / 2) * (C1 ^ 7 / cd + C1 ^ 7 / cd) = 9 * C1 ^ 7 / cd := by ring
    rw [e3]
    exact hKge3

end Work.Asymptotics
