import Submission.Work.FunctionalEquations.KernelSchwartz.growth_combination
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow


/-!
# Growth bounds for the two `τ`-combinations of the interpolation kernel

This file proves `Work.FunctionalEquations.KernelSchwartz.growth_combination`: the
elementary analytic observation (CKMRV, Section 3) that the pointwise `τ`-combinations

* `Φ τ - τ (Φ (τ+1) - Φ τ)`, and
* `Φ (τ+1) - Φ τ`

of a family `Φ : ℂ → (ℝⁿ → ℂ)`, whose radial derivatives obey a growth bound of the form
`α (Im τ)^{-β} + γ ‖τ‖^δ` on the upper half plane (`α, β, γ, δ ≥ 0`), again obey such a
bound, in the normalised form `C (1 + (Im τ)^{-1} + ‖τ‖)^N`.

The proof has three parts.

* `radialDeriv ℓ` is linear in the function, so the radial derivative of either
  combination is the corresponding linear combination of `radialDeriv ℓ (Φ τ)` and
  `radialDeriv ℓ (Φ (τ+1))`; this is where smoothness of `Φ` in `x` is used.
* Each of `(Im τ)^{-β}` and `‖τ‖^δ` is bounded by `(1 + (Im τ)^{-1} + ‖τ‖)^{⌈·⌉₊}`, and
  the same bound holds for `τ` replaced by `τ + 1` (whose imaginary part is unchanged),
  up to the factor `2 ^ N`.
* The resulting bounds for `Φ τ` and `Φ (τ + 1)` are combined, using
  `‖τ‖ ≤ 1 + (Im τ)^{-1} + ‖τ‖`, which costs one extra power of the weight.

## Main result

* `Work.FunctionalEquations.KernelSchwartz.growth_combination`
-/

namespace Work.FunctionalEquations.KernelSchwartz

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ### Linearity of `radialDeriv` -/

/-- The profile `r ↦ F (realIncl r)` of a smooth function on `ℝⁿ` is smooth. -/
theorem contDiff_profile_of_contDiff {F : E n → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun r : ℝ => F (realIncl (n := n) r)) := by
  refine hF.comp ?_
  have h2 : (realIncl (n := n)) = fun s : ℝ => s • realIncl (n := n) 1 :=
    funext (fun s => Work.Sampling.realIncl_eq_smul (n := n) s)
  rw [h2]
  exact contDiff_id.smul contDiff_const

/-- The `ℓ`-th derivative of the profile of a difference is the difference of the
`ℓ`-th derivatives of the profiles. -/
theorem iteratedDeriv_profile_sub {F G : E n → ℂ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (ℓ : ℕ) (r : ℝ) :
    iteratedDeriv ℓ (fun s : ℝ => (fun y : E n => F y - G y) (realIncl (n := n) s)) r
      = iteratedDeriv ℓ (fun s : ℝ => F (realIncl (n := n) s)) r
        - iteratedDeriv ℓ (fun s : ℝ => G (realIncl (n := n) s)) r := by
  have h1 : (fun s : ℝ => (fun y : E n => F y - G y) (realIncl (n := n) s))
      = ((fun s : ℝ => F (realIncl (n := n) s))
          - fun s : ℝ => G (realIncl (n := n) s)) := rfl
  rw [h1]
  exact iteratedDeriv_sub ((contDiff_profile_of_contDiff hF).of_le coe_le_smooth).contDiffAt
    ((contDiff_profile_of_contDiff hG).of_le coe_le_smooth).contDiffAt

/-- The `ℓ`-th derivative of the profile of a constant multiple is the constant multiple
of the `ℓ`-th derivative of the profile. -/
theorem iteratedDeriv_profile_const_mul {G : E n → ℂ} (hG : ContDiff ℝ ∞ G) (c : ℂ) (ℓ : ℕ)
    (r : ℝ) :
    iteratedDeriv ℓ (fun s : ℝ => c * ((fun y : E n => G y) (realIncl (n := n) s))) r
      = c * iteratedDeriv ℓ (fun s : ℝ => G (realIncl (n := n) s)) r :=
  iteratedDeriv_const_mul c ((contDiff_profile_of_contDiff hG).of_le coe_le_smooth).contDiffAt

/-- `radialDeriv` is additive in the function. -/
theorem radialDeriv_sub (ℓ : ℕ) {F G : E n → ℂ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (x : E n) :
    radialDeriv ℓ (fun y => F y - G y) x = radialDeriv ℓ F x - radialDeriv ℓ G x := by
  simp only [radialDeriv]
  exact iteratedDeriv_profile_sub hF hG ℓ ‖x‖

/-- `radialDeriv` is homogeneous in the function. -/
theorem radialDeriv_const_mul (ℓ : ℕ) {G : E n → ℂ} (hG : ContDiff ℝ ∞ G) (c : ℂ) (x : E n) :
    radialDeriv ℓ (fun y : E n => c * G y) x = c * radialDeriv ℓ G x := by
  simp only [radialDeriv]
  exact iteratedDeriv_profile_const_mul hG c ℓ ‖x‖

/-- `radialDeriv` of the pointwise combination `F - c (G - H)`, in the shape in which it
occurs in `growth_combination`. -/
theorem radialDeriv_combination (ℓ : ℕ) (c : ℂ) {F G H : E n → ℂ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : E n) :
    radialDeriv ℓ (fun y : E n => F y - c * (G y - H y)) x
      = radialDeriv ℓ F x - c * (radialDeriv ℓ G x - radialDeriv ℓ H x) := by
  have hGH : ContDiff ℝ ∞ (fun y : E n => G y - H y) := hG.sub hH
  have hcGH : ContDiff ℝ ∞ (fun y : E n => c * (G y - H y)) := by
    simpa [smul_eq_mul] using hGH.const_smul c
  have key : radialDeriv ℓ (fun y : E n => F y - (fun y : E n => c * (G y - H y)) y) x
      = radialDeriv ℓ F x - c * (radialDeriv ℓ G x - radialDeriv ℓ H x) := by
    rw [radialDeriv_sub ℓ hF hcGH x, radialDeriv_const_mul ℓ hGH c x,
      radialDeriv_sub ℓ hG hH x]
  exact key

/-! ### Normalising the growth hypothesis -/

/-- The normalised growth condition used in the conclusion of `growth_combination`:
for every `k`, `ℓ` there are `C ≥ 0` and `N ≥ 0` with
`‖x‖^k ‖D^ℓ (Φ τ) x‖ ≤ C (1 + (Im τ)^{-1} + ‖τ‖)^N` on the upper half plane. -/
def PhiBound (Φ : ℂ → E n → ℂ) : Prop :=
  ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
    ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      ‖x‖ ^ k * ‖radialDeriv ℓ (Φ τ) x‖ ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N

/-- `y ^ (-β) ≤ u ^ N` for `0 < y`, `0 ≤ β`, `y⁻¹ ≤ u`, `1 ≤ u` and `⌈β⌉₊ ≤ N`. -/
theorem rpow_neg_le_of_ceil {y β u N : ℝ} (hy : 0 < y) (hβ : 0 ≤ β) (hu : y⁻¹ ≤ u)
    (hu1 : 1 ≤ u) (hN : (⌈β⌉₊ : ℝ) ≤ N) : y ^ (-β) ≤ u ^ N := by
  have h1 : y ^ (-β) = y⁻¹ ^ β := by
    rw [Real.rpow_neg hy.le, Real.inv_rpow hy.le]
  have h2 : y⁻¹ ^ β ≤ u ^ β := Real.rpow_le_rpow (inv_nonneg.mpr hy.le) hu hβ
  have h3 : u ^ β ≤ u ^ ((⌈β⌉₊ : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (Nat.le_ceil β)
  have h4 : u ^ ((⌈β⌉₊ : ℕ) : ℝ) ≤ u ^ N := Real.rpow_le_rpow_of_exponent_le hu1 hN
  calc y ^ (-β) = y⁻¹ ^ β := h1
    _ ≤ u ^ β := h2
    _ ≤ u ^ ((⌈β⌉₊ : ℕ) : ℝ) := h3
    _ ≤ u ^ N := h4

/-- `y ^ δ ≤ u ^ N` for `0 ≤ y ≤ u`, `1 ≤ u`, `0 ≤ δ` and `⌈δ⌉₊ ≤ N`. -/
theorem rpow_le_of_ceil {y δ u N : ℝ} (hy : 0 ≤ y) (hyu : y ≤ u) (hu1 : 1 ≤ u) (hδ : 0 ≤ δ)
    (hN : (⌈δ⌉₊ : ℝ) ≤ N) : y ^ δ ≤ u ^ N := by
  calc y ^ δ ≤ u ^ δ := Real.rpow_le_rpow hy hyu hδ
    _ ≤ u ^ ((⌈δ⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (Nat.le_ceil δ)
    _ ≤ u ^ N := Real.rpow_le_rpow_of_exponent_le hu1 hN

/-- The raw hypothesis of `growth_combination` implies `PhiBound`. -/
theorem phiBound_of_raw {Φ : ℂ → E n → ℂ}
    (h : ∀ k ℓ : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : ℂ) (x : E n), 0 < τ.im →
        ‖x‖ ^ k * ‖radialDeriv ℓ (Φ τ) x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ) :
    PhiBound Φ := by
  intro k ℓ
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hb⟩ := h k ℓ
  refine ⟨α + γ, ((⌈β⌉₊ + ⌈δ⌉₊ : ℕ) : ℝ), by positivity, by positivity, ?_⟩
  intro τ x hτ
  have hbase : 0 ≤ 1 + (τ.im)⁻¹ + ‖τ‖ := by
    have h1 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr hτ.le
    have h2 : 0 ≤ ‖τ‖ := norm_nonneg τ
    linarith
  have hu1 : 1 ≤ 1 + (τ.im)⁻¹ + ‖τ‖ := by
    have h1 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr hτ.le
    have h2 : 0 ≤ ‖τ‖ := norm_nonneg τ
    linarith
  have hNβ : (⌈β⌉₊ : ℝ) ≤ ((⌈β⌉₊ + ⌈δ⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right ⌈β⌉₊ ⌈δ⌉₊
  have hNδ : (⌈δ⌉₊ : ℝ) ≤ ((⌈β⌉₊ + ⌈δ⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left ⌈δ⌉₊ ⌈β⌉₊
  have hβb : τ.im ^ (-β) ≤ (1 + (τ.im)⁻¹ + ‖τ‖) ^ (((⌈β⌉₊ + ⌈δ⌉₊ : ℕ) : ℝ)) :=
    rpow_neg_le_of_ceil hτ hβ (by linarith [norm_nonneg (τ : ℂ)]) hu1 hNβ
  have hδb : ‖τ‖ ^ δ ≤ (1 + (τ.im)⁻¹ + ‖τ‖) ^ (((⌈β⌉₊ + ⌈δ⌉₊ : ℕ) : ℝ)) :=
    rpow_le_of_ceil (norm_nonneg τ) (by linarith [inv_nonneg.mpr hτ.le]) hu1 hδ hNδ
  calc ‖x‖ ^ k * ‖radialDeriv ℓ (Φ τ) x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ := hb τ x hτ
    _ ≤ α * (1 + (τ.im)⁻¹ + ‖τ‖) ^ (((⌈β⌉₊ + ⌈δ⌉₊ : ℕ) : ℝ))
        + γ * (1 + (τ.im)⁻¹ + ‖τ‖) ^ (((⌈β⌉₊ + ⌈δ⌉₊ : ℕ) : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hβb hα) (mul_le_mul_of_nonneg_left hδb hγ)
    _ = (α + γ) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ (((⌈β⌉₊ + ⌈δ⌉₊ : ℕ) : ℝ)) := by ring

/-! ### Shifting `τ` by one -/

/-- Shifting `τ` by `1` does not change `Im τ`, and increases `‖τ‖` by at most `1`, so
the weight `1 + (Im τ)^{-1} + ‖τ‖` is at most doubled. -/
theorem rpow_shift_le (τ : ℂ) (hτ : 0 < τ.im) {N : ℝ} (hN : 0 ≤ N) :
    (1 + ((τ + 1).im)⁻¹ + ‖τ + 1‖) ^ N ≤ 2 ^ N * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := by
  have him : (τ + 1).im = τ.im := by simp [Complex.add_im]
  have hbase : 0 ≤ 1 + (τ.im)⁻¹ + ‖τ‖ := by
    have h1 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr hτ.le
    have h2 : 0 ≤ ‖τ‖ := norm_nonneg τ
    linarith
  have hle : 1 + ((τ + 1).im)⁻¹ + ‖τ + 1‖ ≤ 2 * (1 + (τ.im)⁻¹ + ‖τ‖) := by
    have h1 : ((τ + 1).im)⁻¹ = (τ.im)⁻¹ := by rw [him]
    have h2 : ‖τ + 1‖ ≤ ‖τ‖ + 1 := by
      calc ‖τ + 1‖ ≤ ‖τ‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖τ‖ + 1 := by simp
    have h3 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr hτ.le
    have h4 : 0 ≤ ‖τ‖ := norm_nonneg τ
    rw [h1]
    linarith
  have h0 : 0 ≤ 1 + ((τ + 1).im)⁻¹ + ‖τ + 1‖ := by
    have h1 : ((τ + 1).im)⁻¹ = (τ.im)⁻¹ := by rw [him]
    have h3 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr hτ.le
    have h4 : 0 ≤ ‖(τ + 1 : ℂ)‖ := norm_nonneg _
    rw [h1]
    linarith
  calc (1 + ((τ + 1).im)⁻¹ + ‖τ + 1‖) ^ N ≤ (2 * (1 + (τ.im)⁻¹ + ‖τ‖)) ^ N :=
        Real.rpow_le_rpow h0 hle hN
    _ = 2 ^ N * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := Real.mul_rpow (by norm_num) hbase

/-- The normalised bound for `Φ τ` transports to `Φ (τ + 1)`, at the cost of a factor
`2 ^ N`. -/
theorem shifted_bound {Φ : ℂ → E n → ℂ} {k ℓ : ℕ} {C N : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hb : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      ‖x‖ ^ k * ‖radialDeriv ℓ (Φ τ) x‖ ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N)
    (τ : ℂ) (x : E n) (hτ : 0 < τ.im) :
    ‖x‖ ^ k * ‖radialDeriv ℓ (Φ (τ + 1)) x‖
      ≤ (C * 2 ^ N) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := by
  have hτ1 : 0 < (τ + 1).im := by simpa [Complex.add_im] using hτ
  have h1 := hb (τ + 1) x hτ1
  have h2 : (1 + ((τ + 1).im)⁻¹ + ‖τ + 1‖) ^ N ≤ 2 ^ N * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N :=
    rpow_shift_le τ hτ hN
  calc ‖x‖ ^ k * ‖radialDeriv ℓ (Φ (τ + 1)) x‖
      ≤ C * (1 + ((τ + 1).im)⁻¹ + ‖τ + 1‖) ^ N := h1
    _ ≤ C * (2 ^ N * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N) := mul_le_mul_of_nonneg_left h2 hC
    _ = (C * 2 ^ N) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := by ring

/-! ### The arithmetic core of the combination -/

/-- Arithmetic core of the estimate for `Φ τ - τ (Φ (τ+1) - Φ τ)`: if `W a ≤ C u^N` and
`W (a + b) ≤ D u^N` with `W, a, b ≥ 0`, `t ≤ u` and `1 ≤ u`, then
`W (a + t (a + b)) ≤ (C + D) u^{N+1}`. -/
theorem combination_core {W a b t C D N u : ℝ} (hW : 0 ≤ W) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : 0 ≤ C) (hu1 : 1 ≤ u) (htu : t ≤ u)
    (hA : W * a ≤ C * u ^ N) (hAB : W * (a + b) ≤ D * u ^ N) :
    W * (a + t * (a + b)) ≤ (C + D) * u ^ (N + 1) := by
  have hu0 : 0 ≤ u := le_trans zero_le_one hu1
  have hupos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hWab : 0 ≤ W * (a + b) := mul_nonneg hW (by linarith)
  have h2 : t * (W * (a + b)) ≤ u * (W * (a + b)) := mul_le_mul_of_nonneg_right htu hWab
  have h3 : u * (W * (a + b)) ≤ u * (D * u ^ N) := mul_le_mul_of_nonneg_left hAB hu0
  have hpow : u * u ^ N = u ^ (N + 1) := by
    calc u * u ^ N = u ^ (1 : ℝ) * u ^ N := by rw [Real.rpow_one]
      _ = u ^ ((1 : ℝ) + N) := (Real.rpow_add hupos 1 N).symm
      _ = u ^ (N + 1) := by ring_nf
  have h4 : u * (D * u ^ N) = D * u ^ (N + 1) := by
    rw [← hpow]
    ring
  have h5 : C * u ^ N ≤ C * u ^ (N + 1) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)) hC
  calc W * (a + t * (a + b)) = W * a + t * (W * (a + b)) := by ring
    _ ≤ C * u ^ N + u * (W * (a + b)) := add_le_add hA h2
    _ ≤ C * u ^ N + u * (D * u ^ N) := add_le_add (le_refl _) h3
    _ = C * u ^ N + D * u ^ (N + 1) := by rw [h4]
    _ ≤ C * u ^ (N + 1) + D * u ^ (N + 1) := add_le_add h5 (le_refl _)
    _ = (C + D) * u ^ (N + 1) := by ring

/-! ### The two combinations -/

/-- The difference `Φ (τ+1) - Φ τ` satisfies the normalised growth bound. -/
theorem phiBound_diff {Φ : ℂ → E n → ℂ} (hΦs : ∀ τ : ℂ, ContDiff ℝ ∞ (Φ τ))
    (h : PhiBound Φ) :
    PhiBound (fun τ y => Φ (τ + 1) y - Φ τ y) := by
  intro k ℓ
  obtain ⟨C, N, hC, hN, hb⟩ := h k ℓ
  refine ⟨C * 2 ^ N + C, N, by positivity, hN, ?_⟩
  intro τ x hτ
  change ‖x‖ ^ k * ‖radialDeriv ℓ (fun y : E n => Φ (τ + 1) y - Φ τ y) x‖ ≤ _
  have hlin : radialDeriv ℓ (fun y : E n => Φ (τ + 1) y - Φ τ y) x
      = radialDeriv ℓ (Φ (τ + 1)) x - radialDeriv ℓ (Φ τ) x :=
    radialDeriv_sub ℓ (hΦs (τ + 1)) (hΦs τ) x
  rw [hlin]
  have h0 : ‖x‖ ^ k * ‖radialDeriv ℓ (Φ τ) x‖ ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := hb τ x hτ
  have hsh : ‖x‖ ^ k * ‖radialDeriv ℓ (Φ (τ + 1)) x‖
      ≤ (C * 2 ^ N) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := shifted_bound hC hN hb τ x hτ
  have hW : 0 ≤ ‖x‖ ^ k := pow_nonneg (norm_nonneg x) k
  have hsum : ‖x‖ ^ k * (‖radialDeriv ℓ (Φ (τ + 1)) x‖ + ‖radialDeriv ℓ (Φ τ) x‖)
      ≤ (C * 2 ^ N + C) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := by
    calc ‖x‖ ^ k * (‖radialDeriv ℓ (Φ (τ + 1)) x‖ + ‖radialDeriv ℓ (Φ τ) x‖)
        = ‖x‖ ^ k * ‖radialDeriv ℓ (Φ (τ + 1)) x‖
          + ‖x‖ ^ k * ‖radialDeriv ℓ (Φ τ) x‖ := by ring
      _ ≤ (C * 2 ^ N) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N + C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N :=
          add_le_add hsh h0
      _ = (C * 2 ^ N + C) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := by ring
  exact le_trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hW) hsum

/-- The combination `Φ τ - τ (Φ (τ+1) - Φ τ)` satisfies the normalised growth bound. -/
theorem phiBound_combo {Φ : ℂ → E n → ℂ} (hΦs : ∀ τ : ℂ, ContDiff ℝ ∞ (Φ τ))
    (h : PhiBound Φ) :
    PhiBound (fun τ y => Φ τ y - τ * (Φ (τ + 1) y - Φ τ y)) := by
  intro k ℓ
  obtain ⟨C, N, hC, hN, hb⟩ := h k ℓ
  refine ⟨C + (C * 2 ^ N + C), N + 1, by positivity, by linarith, ?_⟩
  intro τ x hτ
  change ‖x‖ ^ k
      * ‖radialDeriv ℓ (fun y : E n => Φ τ y - τ * (Φ (τ + 1) y - Φ τ y)) x‖ ≤ _
  have hlin : radialDeriv ℓ (fun y : E n => Φ τ y - τ * (Φ (τ + 1) y - Φ τ y)) x
      = radialDeriv ℓ (Φ τ) x
        - τ * (radialDeriv ℓ (Φ (τ + 1)) x - radialDeriv ℓ (Φ τ) x) :=
    radialDeriv_combination ℓ τ (hΦs τ) (hΦs (τ + 1)) (hΦs τ) x
  rw [hlin]
  have h0 : ‖x‖ ^ k * ‖radialDeriv ℓ (Φ τ) x‖ ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := hb τ x hτ
  have hsh : ‖x‖ ^ k * ‖radialDeriv ℓ (Φ (τ + 1)) x‖
      ≤ (C * 2 ^ N) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := shifted_bound hC hN hb τ x hτ
  have hW : 0 ≤ ‖x‖ ^ k := pow_nonneg (norm_nonneg x) k
  have hu1 : 1 ≤ 1 + (τ.im)⁻¹ + ‖τ‖ := by
    have h1 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr hτ.le
    have h2 : 0 ≤ ‖τ‖ := norm_nonneg τ
    linarith
  have htu : ‖τ‖ ≤ 1 + (τ.im)⁻¹ + ‖τ‖ := by
    have h1 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr hτ.le
    linarith
  have hBA : ‖x‖ ^ k * (‖radialDeriv ℓ (Φ τ) x‖ + ‖radialDeriv ℓ (Φ (τ + 1)) x‖)
      ≤ (C * 2 ^ N + C) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := by
    calc ‖x‖ ^ k * (‖radialDeriv ℓ (Φ τ) x‖ + ‖radialDeriv ℓ (Φ (τ + 1)) x‖)
        = ‖x‖ ^ k * ‖radialDeriv ℓ (Φ τ) x‖
          + ‖x‖ ^ k * ‖radialDeriv ℓ (Φ (τ + 1)) x‖ := by ring
      _ ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N + (C * 2 ^ N) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N :=
          add_le_add h0 hsh
      _ = (C * 2 ^ N + C) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N := by ring
  have hstep : ‖radialDeriv ℓ (Φ τ) x
        - τ * (radialDeriv ℓ (Φ (τ + 1)) x - radialDeriv ℓ (Φ τ) x)‖
      ≤ ‖radialDeriv ℓ (Φ τ) x‖
        + ‖τ‖ * (‖radialDeriv ℓ (Φ (τ + 1)) x‖ + ‖radialDeriv ℓ (Φ τ) x‖) := by
    calc ‖radialDeriv ℓ (Φ τ) x
          - τ * (radialDeriv ℓ (Φ (τ + 1)) x - radialDeriv ℓ (Φ τ) x)‖
        ≤ ‖radialDeriv ℓ (Φ τ) x‖
          + ‖τ * (radialDeriv ℓ (Φ (τ + 1)) x - radialDeriv ℓ (Φ τ) x)‖ := norm_sub_le _ _
      _ = ‖radialDeriv ℓ (Φ τ) x‖
          + ‖τ‖ * ‖radialDeriv ℓ (Φ (τ + 1)) x - radialDeriv ℓ (Φ τ) x‖ := by rw [norm_mul]
      _ ≤ ‖radialDeriv ℓ (Φ τ) x‖
          + ‖τ‖ * (‖radialDeriv ℓ (Φ (τ + 1)) x‖ + ‖radialDeriv ℓ (Φ τ) x‖) :=
          add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg τ))
  calc ‖x‖ ^ k * ‖radialDeriv ℓ (Φ τ) x
          - τ * (radialDeriv ℓ (Φ (τ + 1)) x - radialDeriv ℓ (Φ τ) x)‖
      ≤ ‖x‖ ^ k * (‖radialDeriv ℓ (Φ τ) x‖
          + ‖τ‖ * (‖radialDeriv ℓ (Φ (τ + 1)) x‖ + ‖radialDeriv ℓ (Φ τ) x‖)) :=
        mul_le_mul_of_nonneg_left hstep hW
    _ = ‖x‖ ^ k * (‖radialDeriv ℓ (Φ τ) x‖
        + ‖τ‖ * (‖radialDeriv ℓ (Φ τ) x‖ + ‖radialDeriv ℓ (Φ (τ + 1)) x‖)) := by ring
    _ ≤ (C + (C * 2 ^ N + C)) * (1 + (τ.im)⁻¹ + ‖τ‖) ^ (N + 1) :=
        combination_core (W := ‖x‖ ^ k) (a := ‖radialDeriv ℓ (Φ τ) x‖)
          (b := ‖radialDeriv ℓ (Φ (τ + 1)) x‖) (t := ‖τ‖) (C := C)
          (D := C * 2 ^ N + C) (N := N) (u := 1 + (τ.im)⁻¹ + ‖τ‖)
          hW (norm_nonneg _) (norm_nonneg _) hC hu1 htu h0 hBA

/-! ### The main result -/

theorem growth_combination {n : ℕ} [NeZero n] (Φ : ℂ → E n → ℂ)
    (hΦ_smooth : ∀ τ : ℂ, ContDiff ℝ ∞ (Φ τ))
    (hΦ : ∀ k ℓ : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : ℂ) (x : E n), 0 < τ.im →
        ‖x‖ ^ k * ‖radialDeriv ℓ (fun y : E n => Φ τ y) x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ) :
    (∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N' : ℝ, 0 ≤ C ∧ 0 ≤ N' ∧
      ∀ (τ : ℂ) (x : E n), 0 < τ.im →
        ‖x‖ ^ k * ‖radialDeriv ℓ (fun y : E n => Φ τ y - τ * (Φ (τ+1) y - Φ τ y)) x‖
          ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N') ∧
    (∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N' : ℝ, 0 ≤ C ∧ 0 ≤ N' ∧
      ∀ (τ : ℂ) (x : E n), 0 < τ.im →
        ‖x‖ ^ k * ‖radialDeriv ℓ (fun y : E n => Φ (τ+1) y - Φ τ y) x‖
          ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N') := by
  have hraw : ∀ k ℓ : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : ℂ) (x : E n), 0 < τ.im →
        ‖x‖ ^ k * ‖radialDeriv ℓ (Φ τ) x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ := hΦ
  have hP : PhiBound (n := n) Φ := phiBound_of_raw hraw
  exact ⟨phiBound_combo hΦ_smooth hP, phiBound_diff hΦ_smooth hP⟩

end

end Work.FunctionalEquations.KernelSchwartz


end Work.CKFinal.Shadow
