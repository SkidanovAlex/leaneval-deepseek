import Mathlib
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.ERegDefs
import Submission.Work.Asymptotics.EReg_identities
import Submission.Work.Asymptotics.EReg_atom_bounds

/-!
# Power bounds for the `d = 24` cusp coefficients on the CKMRV `E`-tile

Writing `αᵢ = Alpha ℓ 24 i τ` (`Work.Asymptotics.Alpha`), `U = θ₀₀⁴`, `V = θ₁₀⁴`,
`W = θ₀₁⁴`, `𝓛 = ℓ.L`, `𝓛_S = ℓ.L_S`, this file proves that on the cusp-`0` tile
`EReg = {τ | 3/2 ≤ (S • τ).im}` the four quantities `α₀`, `α₂`, `α₁ - α₂` and
`j(α₁ - α₂)` are bounded by a power of `scale τ`:

  `α₀ = Δ`,   `α₂ = ψ₄·E₈`,   `α₁ - α₂ = -(9/2)E₄(𝓛·UV²W + 𝓛_S·UVW²)`,

the last identity coming from the exact factorisations of
`Work.Asymptotics.EReg_identities` (`ξ₄E₈ - ξ₂E₁₀ = (9/2)UV²WE₄` and
`(ξ₄|₄S)E₈ - (ξ₂|₂S)E₁₀ = (9/2)UVW²E₄`), which display the cusp-`0` cancellation.
The `j`-clause is bounded using `‖j τ‖·tS τ² ≤ C(scale τ)^N` together with the `tS`
factors carried by `𝓛` and `W`, so that the two `tS τ²` factors cancel.

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

/-- Adding two power bounds at the cost of adding the exponents. -/
private lemma add_bound_coarse {τ : ℍ} {Y₁ Y₂ : ℂ} {c₁ c₂ : ℝ} {m₁ m₂ : ℕ}
    (h₁ : ‖Y₁‖ ≤ c₁ * (scale τ) ^ m₁) (h₂ : ‖Y₂‖ ≤ c₂ * (scale τ) ^ m₂)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    ‖Y₁ + Y₂‖ ≤ (c₁ + c₂) * (scale τ) ^ (m₁ + m₂) := by
  have h₁' : ‖Y₁‖ ≤ c₁ * (scale τ) ^ (m₁ + m₂) :=
    le_trans h₁ (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (Work.Kernels.one_le_scale τ) (Nat.le_add_right m₁ m₂)) hc₁)
  have h₂' : ‖Y₂‖ ≤ c₂ * (scale τ) ^ (m₁ + m₂) :=
    le_trans h₂ (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (Work.Kernels.one_le_scale τ) (Nat.le_add_left m₂ m₁)) hc₂)
  calc ‖Y₁ + Y₂‖ ≤ ‖Y₁‖ + ‖Y₂‖ := norm_add_le _ _
    _ ≤ c₁ * (scale τ) ^ (m₁ + m₂) + c₂ * (scale τ) ^ (m₁ + m₂) := add_le_add h₁' h₂'
    _ = (c₁ + c₂) * (scale τ) ^ (m₁ + m₂) := by ring

/-- Multiplying a power bound by a nonnegative real constant. -/
private lemma const_mul_bound {τ : ℍ} {X : ℂ} {c : ℝ} {m : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (h : ‖X‖ ≤ c * (scale τ) ^ m) : ‖(r : ℂ) * X‖ ≤ (r * c) * (scale τ) ^ m := by
  calc ‖(r : ℂ) * X‖ = r * ‖X‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
    _ ≤ r * (c * (scale τ) ^ m) := mul_le_mul_of_nonneg_left h hr
    _ = (r * c) * (scale τ) ^ m := by ring

/-- The `tS τ²`-cancellation: `‖j‖ tS² ≤ A (scale τ)^{m₀}` and a bound of `p` carrying
`(tS τ)^k` with `k ≥ 2` give `‖j p‖ ≤ A B (scale τ)^{m₀ + m}`. -/
private lemma j_mul_PT {τ : ℍ} {j p : ℂ} {A B : ℝ} {m₀ m k : ℕ}
    (hj : ‖j‖ * tS τ ^ 2 ≤ A * (scale τ) ^ m₀) (hp : PT τ p B m k) (hk : 2 ≤ k)
    (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ‖j * p‖ ≤ A * B * (scale τ) ^ (m₀ + m) := by
  have hts : 0 < tS τ ^ 2 := pow_pos (tS_pos τ) 2
  have hA0 : (0 : ℝ) ≤ A * (scale τ) ^ m₀ :=
    mul_nonneg hA (pow_nonneg (Work.Kernels.scale_pos τ).le m₀)
  have hB0 : (0 : ℝ) ≤ B * (scale τ) ^ m :=
    mul_nonneg hB (pow_nonneg (Work.Kernels.scale_pos τ).le m)
  have htk : tS τ ^ k ≤ tS τ ^ 2 := pow_le_pow_of_le_one (tS_nonneg τ) (tS_le_one τ) hk
  have hp' : ‖p‖ ≤ B * (scale τ) ^ m * tS τ ^ 2 :=
    le_trans hp (mul_le_mul_of_nonneg_left htk hB0)
  have key : ‖j‖ * ‖p‖ * tS τ ^ 2 ≤ A * B * (scale τ) ^ (m₀ + m) * tS τ ^ 2 := by
    calc ‖j‖ * ‖p‖ * tS τ ^ 2 = (‖j‖ * tS τ ^ 2) * ‖p‖ := by ring
      _ ≤ (A * (scale τ) ^ m₀) * ‖p‖ := mul_le_mul_of_nonneg_right hj (norm_nonneg p)
      _ ≤ (A * (scale τ) ^ m₀) * (B * (scale τ) ^ m * tS τ ^ 2) :=
          mul_le_mul_of_nonneg_left hp' hA0
      _ = A * B * (scale τ) ^ (m₀ + m) * tS τ ^ 2 := by rw [pow_add]; ring
  rw [norm_mul]
  exact le_of_mul_le_mul_right key hts

/-! ## The `d = 24` coefficients -/

private lemma Alpha24_zero (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 24 0 τ = Work.Kernels.DeltaFun τ := by
  simp [Alpha, Work.Kernels.psiVec, vlen, Work.Kernels.fk]

private lemma Alpha24_two (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 24 2 τ = Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ := by
  simp [Alpha, Work.Kernels.psiVec, vlen, Work.Kernels.fk]

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

/-- `α₁ - α₂ = -(9/2)E₄(𝓛·UV²W + 𝓛_S·UVW²)`, the cancellation identity of the `E`-order
estimate. -/
private lemma Alpha24_diff (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ
      = -(9 / 2 : ℂ) * Work.Kernels.E4Fun τ
          * (ℓ.L τ * (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2 * Work.Kernels.WFun τ)
            + ℓ.L_S τ
              * (Work.Kernels.UFun τ * Work.Kernels.VFun τ * Work.Kernels.WFun τ ^ 2)) := by
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
  have hA1 : Alpha ℓ 24 1 τ
      = Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ) := by
    simp [Alpha, Work.Kernels.psiVec, vlen, Work.Kernels.fk]
  have hA2 : Alpha ℓ 24 2 τ = Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2 := by
    simp [Alpha, Work.Kernels.psiVec, vlen, Work.Kernels.fk]
  have hp2 : Work.Kernels.psi2 ℓ τ = (Work.Kernels.UFun τ + Work.Kernels.WFun τ) * ℓ.L τ
      - (Work.Kernels.UFun τ + Work.Kernels.VFun τ) * ℓ.L_S τ := by
    rw [Work.Kernels.psi2, Work.Kernels.KernelFacts.xi2Fun_slash_S,
      show Work.Kernels.xi2Fun τ = Work.Kernels.UFun τ + Work.Kernels.WFun τ from rfl]
    ring
  have hp4 : Work.Kernels.psi4 ℓ τ
      = (Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2)
          * ℓ.L τ
        + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2)
          * ℓ.L_S τ := psi4_expand ℓ τ
  rw [hA1, hA2, hp2, hp4]
  have hid : ((Work.Kernels.UFun τ + Work.Kernels.WFun τ) * ℓ.L τ
        - (Work.Kernels.UFun τ + Work.Kernels.VFun τ) * ℓ.L_S τ)
        * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
      - ((Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2)
            * ℓ.L τ
          + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
              - 2 * Work.Kernels.WFun τ ^ 2) * ℓ.L_S τ)
        * Work.Kernels.E4Fun τ ^ 2
      = Work.Kernels.E4Fun τ
          * (ℓ.L τ
              * ((Work.Kernels.UFun τ + Work.Kernels.WFun τ) * Work.Kernels.E6Fun τ
                - (Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
                    - 2 * Work.Kernels.VFun τ ^ 2) * Work.Kernels.E4Fun τ)
            + ℓ.L_S τ
              * ((-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * Work.Kernels.E6Fun τ
                - (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
                    - 2 * Work.Kernels.WFun τ ^ 2) * Work.Kernels.E4Fun τ)) := by
    ring
  rw [hid, h1', h2']
  ring

open Work.Kernels (scale)

theorem EReg_alpha24_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.EReg →
      ‖Work.Asymptotics.Alpha ℓ 24 0 τ‖ ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Asymptotics.Alpha ℓ 24 2 τ‖ ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Asymptotics.Alpha ℓ 24 1 τ - Work.Asymptotics.Alpha ℓ 24 2 τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Kernels.jInvariantFun τ
          * (Work.Asymptotics.Alpha ℓ 24 1 τ - Work.Asymptotics.Alpha ℓ 24 2 τ)‖
        ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := EReg_atom_bounds ℓ
  obtain ⟨C1, hCC1, hC1ge1⟩ : ∃ C1 : ℝ, C ≤ C1 ∧ 1 ≤ C1 :=
    ⟨max C 1, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, N ≤ (n : ℝ) := ⟨Nat.ceil N, Nat.le_ceil N⟩
  have hC1pos : 0 < C1 := lt_of_lt_of_le zero_lt_one hC1ge1
  have hC1nn : (0 : ℝ) ≤ C1 := hC1pos.le
  have hKpos : (0 : ℝ) < 9 * C1 ^ 7 + 1 := by positivity
  have hKnn : (0 : ℝ) ≤ 9 * C1 ^ 7 + 1 := hKpos.le
  have hC17 : (1 : ℝ) ≤ C1 ^ 7 := one_le_pow₀ hC1ge1
  have hC1_4 : C1 ^ 4 ≤ C1 ^ 7 := pow_le_pow_right₀ hC1ge1 (by norm_num)
  have hC1_5 : C1 ^ 5 ≤ C1 ^ 7 := pow_le_pow_right₀ hC1ge1 (by norm_num)
  have hC1_6 : C1 ^ 6 ≤ C1 ^ 7 := pow_le_pow_right₀ hC1ge1 (by norm_num)
  have hC1_1 : C1 ≤ C1 ^ 7 := by
    simpa using pow_le_pow_right₀ hC1ge1 (show (1 : ℕ) ≤ 7 by norm_num)
  refine ⟨9 * C1 ^ 7 + 1, ((14 * n + 1 : ℕ) : ℝ), hKpos, by positivity, fun τ hτ => ?_⟩
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
  have hΔpd : PD τ (Work.Kernels.DeltaFun τ) C1 n := by
    refine le_trans hΔu ?_
    calc C * (scale τ) ^ N * tS τ ^ 2 ≤ C1 * (scale τ) ^ n * tS τ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hCC1 hdN (Real.rpow_nonneg hdpos.le N) hC1nn)
            (pow_nonneg (tS_nonneg τ) 2)
      _ ≤ C1 * (scale τ) ^ n :=
          mul_le_of_le_one_right (mul_nonneg hC1nn (pow_nonneg hdpos.le n))
            (pow_le_one₀ (tS_nonneg τ) (tS_le_one τ) : tS τ ^ 2 ≤ 1)
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
  -- the `tS`-carrying bounds of `𝓛`, `𝓛_S` and `W`
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
  -- the `j`-bound
  have hjA : ‖Work.Kernels.jInvariantFun τ‖ * tS τ ^ 2 ≤ C1 * (scale τ) ^ n :=
    le_trans hj (mul_le_mul hCC1 hdN (Real.rpow_nonneg hdpos.le N) hC1nn)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `α₀ = Δ`
    rw [Alpha24_zero ℓ τ, Real.rpow_natCast]
    refine pow_bound_mono hΔpd ?_ hKnn (by omega)
    nlinarith [hC1_1, hC17]
  · -- `α₂ = ψ₄ E₈`
    rw [Alpha24_two ℓ τ, psi4_expand ℓ τ, Real.rpow_natCast]
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
    have hE8pd : PD τ (Work.Kernels.E8Fun τ) (C1 ^ 2) (n + n) := PD_sq hC1nn hE4pd
    have hpsi : PD τ ((Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
          - 2 * Work.Kernels.VFun τ ^ 2) * ℓ.L τ
        + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
          - 2 * Work.Kernels.WFun τ ^ 2) * ℓ.L_S τ)
        ((((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) * C1)
          + (((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) * C1)) ((n + n) + n) := PD_add hs1 hs2
    have hfin : PD τ (((Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
          - 2 * Work.Kernels.VFun τ ^ 2) * ℓ.L τ
        + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
          - 2 * Work.Kernels.WFun τ ^ 2) * ℓ.L_S τ) * Work.Kernels.E8Fun τ)
        (((((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) * C1)
          + (((C1 ^ 2 + C1 ^ 2) + 2 * C1 ^ 2) * C1)) * C1 ^ 2) (((n + n) + n) + (n + n)) :=
      PD_mul hpsi hE8pd (by positivity) (by positivity)
    refine pow_bound_mono hfin ?_ hKnn (by omega)
    nlinarith [hC1_5, hC17, hC1ge1]
  · -- `α₁ - α₂`
    rw [Alpha24_diff ℓ τ, Real.rpow_natCast]
    rw [show -(9 / 2 : ℂ) * Work.Kernels.E4Fun τ *
          (ℓ.L τ * (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2 * Work.Kernels.WFun τ)
            + ℓ.L_S τ
              * (Work.Kernels.UFun τ * Work.Kernels.VFun τ * Work.Kernels.WFun τ ^ 2))
        = -((9 / 2 : ℂ) * (Work.Kernels.E4Fun τ
              * (ℓ.L τ
                * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2) * Work.Kernels.WFun τ))
            + Work.Kernels.E4Fun τ
              * (ℓ.L_S τ
                * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ) * Work.Kernels.WFun τ ^ 2))))
        from by ring]
    rw [norm_neg, show (9 / 2 : ℂ) = ((9 / 2 : ℝ) : ℂ) by norm_num]
    have hUV2 : PD τ (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2) (C1 * C1 ^ 2) (3 * n) :=
      PD_mono (PD_mul hUpd hV2 hC1nn (by positivity)) le_rfl (by omega) (by positivity)
    have hUV2W : PD τ ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2) * Work.Kernels.WFun τ)
        ((C1 * C1 ^ 2) * C1) (4 * n) :=
      PD_mono (PD_mul hUV2 hWpd (by positivity) hC1nn) le_rfl (by omega) (by positivity)
    have hq1 : PD τ (ℓ.L τ
        * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2) * Work.Kernels.WFun τ))
        (C1 * ((C1 * C1 ^ 2) * C1)) (5 * n) :=
      PD_mono (PD_mul hLpd hUV2W hC1nn (by positivity)) le_rfl (by omega) (by positivity)
    have hp1 : PD τ (Work.Kernels.E4Fun τ
        * (ℓ.L τ * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2) * Work.Kernels.WFun τ)))
        (C1 * (C1 * ((C1 * C1 ^ 2) * C1))) (7 * n) :=
      PD_mono (PD_mul hE4pd hq1 hC1nn (by positivity)) le_rfl (by omega) (by positivity)
    have hUV : PD τ (Work.Kernels.UFun τ * Work.Kernels.VFun τ) (C1 * C1) (3 * n) :=
      PD_mono (PD_mul hUpd hVpd hC1nn hC1nn) le_rfl (by omega) (by positivity)
    have hUVW2 : PD τ ((Work.Kernels.UFun τ * Work.Kernels.VFun τ) * Work.Kernels.WFun τ ^ 2)
        ((C1 * C1) * C1 ^ 2) (5 * n) :=
      PD_mono (PD_mul hUV hW2 (by positivity) (by positivity)) le_rfl (by omega) (by positivity)
    have hq2 : PD τ (ℓ.L_S τ
        * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ) * Work.Kernels.WFun τ ^ 2))
        (C1 * ((C1 * C1) * C1 ^ 2)) (6 * n) :=
      PD_mono (PD_mul hLSpd hUVW2 hC1nn (by positivity)) le_rfl (by omega) (by positivity)
    have hp2 : PD τ (Work.Kernels.E4Fun τ
        * (ℓ.L_S τ * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ) * Work.Kernels.WFun τ ^ 2)))
        (C1 * (C1 * ((C1 * C1) * C1 ^ 2))) (7 * n) :=
      PD_mono (PD_mul hE4pd hq2 hC1nn (by positivity)) le_rfl (by omega) (by positivity)
    have hsum := PD_add hp1 hp2
    have hconst := const_mul_bound (τ := τ) (r := 9 / 2) (by norm_num) hsum
    refine pow_bound_mono hconst ?_ hKnn (by omega)
    nlinarith [hC1_6, hC17, hC1ge1]
  · -- `j · (α₁ - α₂)`
    rw [Alpha24_diff ℓ τ, Real.rpow_natCast]
    rw [show Work.Kernels.jInvariantFun τ * (-(9 / 2 : ℂ) * Work.Kernels.E4Fun τ *
          (ℓ.L τ * (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2 * Work.Kernels.WFun τ)
            + ℓ.L_S τ
              * (Work.Kernels.UFun τ * Work.Kernels.VFun τ * Work.Kernels.WFun τ ^ 2)))
        = -((9 / 2 : ℂ) * ((Work.Kernels.jInvariantFun τ
              * (Work.Kernels.E4Fun τ
                * (ℓ.L τ
                  * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2)
                    * Work.Kernels.WFun τ))))
            + (Work.Kernels.jInvariantFun τ
              * (Work.Kernels.E4Fun τ
                * (ℓ.L_S τ
                  * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ)
                    * Work.Kernels.WFun τ ^ 2)))))) from by ring]
    rw [norm_neg, show (9 / 2 : ℂ) = ((9 / 2 : ℝ) : ℂ) by norm_num]
    have hUpt : PT τ (Work.Kernels.UFun τ) C1 n 0 := PT_of_PD hUpd
    have hVpt : PT τ (Work.Kernels.VFun τ) C1 n 0 := PT_of_PD hVpd
    have hV2pt : PT τ (Work.Kernels.VFun τ ^ 2) (C1 ^ 2) (n + n) 0 := PT_of_PD hV2
    have hE4pt : PT τ (Work.Kernels.E4Fun τ) C1 n 0 := PT_of_PD hE4pd
    have hL_Spt : PT τ (ℓ.L_S τ) C1 n 0 := PT_of_PD hLSpd
    have hW2t : PT τ (Work.Kernels.WFun τ ^ 2) (C1 ^ 2) (n + n) (1 + 1) := PT_sq hC1nn hWpt
    have ha1 : PT τ (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2) (C1 * C1 ^ 2) (3 * n) 0 :=
      PT_mono (PT_mul hUpt hV2pt hC1nn (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have hb1 : PT τ ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2) * Work.Kernels.WFun τ)
        ((C1 * C1 ^ 2) * C1) (4 * n) 1 :=
      PT_mono (PT_mul ha1 hWpt (by positivity) hC1nn) le_rfl (by omega) (by omega)
        (by positivity)
    have hc1 : PT τ (ℓ.L τ
        * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2) * Work.Kernels.WFun τ))
        (C1 * ((C1 * C1 ^ 2) * C1)) (5 * n) 2 :=
      PT_mono (PT_mul hLpt hb1 hC1nn (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have hp1 : PT τ (Work.Kernels.E4Fun τ
        * (ℓ.L τ * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2) * Work.Kernels.WFun τ)))
        (C1 * (C1 * ((C1 * C1 ^ 2) * C1))) (7 * n) 2 :=
      PT_mono (PT_mul hE4pt hc1 hC1nn (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have ha2 : PT τ (Work.Kernels.UFun τ * Work.Kernels.VFun τ) (C1 * C1) (3 * n) 0 :=
      PT_mono (PT_mul hUpt hVpt hC1nn hC1nn) le_rfl (by omega) (by omega) (by positivity)
    have hb2 : PT τ ((Work.Kernels.UFun τ * Work.Kernels.VFun τ) * Work.Kernels.WFun τ ^ 2)
        ((C1 * C1) * C1 ^ 2) (5 * n) (1 + 1) :=
      PT_mono (PT_mul ha2 hW2t (by positivity) (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have hc2 : PT τ (ℓ.L_S τ
        * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ) * Work.Kernels.WFun τ ^ 2))
        (C1 * ((C1 * C1) * C1 ^ 2)) (6 * n) 2 :=
      PT_mono (PT_mul hL_Spt hb2 hC1nn (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have hp2 : PT τ (Work.Kernels.E4Fun τ
        * (ℓ.L_S τ * ((Work.Kernels.UFun τ * Work.Kernels.VFun τ) * Work.Kernels.WFun τ ^ 2)))
        (C1 * (C1 * ((C1 * C1) * C1 ^ 2))) (7 * n) 2 :=
      PT_mono (PT_mul hE4pt hc2 hC1nn (by positivity)) le_rfl (by omega) (by omega)
        (by positivity)
    have hY1 := j_mul_PT hjA hp1 (by omega) (by positivity) hC1nn
    have hY2 := j_mul_PT hjA hp2 (by omega) (by positivity) hC1nn
    have hsum := PD_add hY1 hY2
    have hconst := const_mul_bound (τ := τ) (r := 9 / 2) (by norm_num) hsum
    refine pow_bound_mono hconst ?_ hKnn (by omega)
    nlinarith [hC17, hC1ge1]

