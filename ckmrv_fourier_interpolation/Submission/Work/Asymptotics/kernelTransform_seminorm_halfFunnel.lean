/-
# The `r`-seminorm bound for the CKMRV contour transform on the half funnel

This is the target `Work.Asymptotics.kernelTransform_seminorm_halfFunnel`: the CKMRV
moderate-growth bound `(★)` for the `r`-seminorms of the naive contour integral
`kernelTransform (Kfun ℓ d) τ ·` on the region `{τ ∈ 𝒟 : 1/2 ≤ Im τ}` of the `Γ(2)`-fundamental
domain.

The half funnel splits at the level `Im τ = 2` into two regions and the bound is assembled from
the two corresponding statements:

* `{τ ∈ 𝒟 : 2 ≤ Im τ}` — the *funnel*, whose seminorm bound is the sibling statement
  `Work.Asymptotics.kernelTransform_seminorm_funnel` (imported below; it is the cusp-`∞` part of
  CKMRV Proposition 4.6, proved by shifting the contour to the `α`-contours of Section 5);
* `{τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2}` — the bounded "low" strip, whose seminorm bound is the delegated
  lemma `Work.Asymptotics.halfFunnel_lowRegion`.  Here `‖τ‖ ≤ √5`, so the two middle ingredients
  of the paper's proof are the compact part of Proposition 4.6 (`kernelTransform_seminorm_on_compact`)
  and the residue analysis at the poles `z = τ ∓ 1` near the bad lines `Re τ = ±1`.

The two statements are then merged into a *single* pair of constants `(α, β, γ, δ)`: since
`Im τ ≥ 1/2` on the whole region, taking `β = 0` and `α` the (bounded) value of the low-strip
estimate, `γ = α₁ + γ₁` and `δ = δ₁` dominates both branches — see the explicit constants (and
the two elementary `rpow` estimates `(Im τ)^{-β₂} ≤ 2^{β₂}`, `‖τ‖^{δ₂} ≤ 3^{δ₂}`, valid on the
low strip) in the proof below.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.kernelTransform_seminorm_funnel
-- NOTE: the low-strip pillar `Work.Asymptotics.HalfFunnel.halfFunnel_lowRegion` is proved in
-- `Submission/Work/Asymptotics/HalfFunnel/halfFunnel_lowRegion.lean`, but that module's import
-- closure contains `MiddleRange.Main`, which collides with `KPlusXiDefs` (the two declare the same
-- `Work.Asymptotics.continuous_jInvariantFun`), and the funnel side's closure contains
-- `KPlusXiDefs`.  The import below is the collision-free *copy* of that development, obtained by
-- duplicating every module of the low-strip closure whose own closure meets `MiddleRange.Main`
-- into `Submission/Work/HFN/` with the clashing declarations made `private` and all imports
-- redirected to the copies -- the same device that `Submission/Work/HFN/seminormK_cusp0_half.lean`
-- uses.  The copy declares the very same name
-- `Work.Asymptotics.HalfFunnel.halfFunnel_lowRegion`, so the call below is unchanged.
import Submission.Work.HFN.HalfFunnel.halfFunnel_lowRegion

namespace Work.Asymptotics

theorem kernelTransform_seminorm_halfFunnel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
  intro k l
  -- the funnel branch
  obtain ⟨α₁, β₁, γ₁, δ₁, hα₁, hβ₁, hγ₁, hδ₁, hhi⟩ :=
    kernelTransform_seminorm_funnel ℓ d hd k l
  -- the bounded low-strip branch
  obtain ⟨α₂, β₂, γ₂, δ₂, hα₂, hβ₂, hγ₂, hδ₂, hlo⟩ :=
    Work.HFN.HalfFunnel.halfFunnel_lowRegion ℓ d hd k l
  refine ⟨α₂ * 2 ^ β₂ + γ₂ * 3 ^ δ₂, 0, α₁ + γ₁, δ₁, by positivity, le_rfl,
    by positivity, hδ₁, ?_⟩
  intro τ r hτ hτhalf
  have hτpos : 0 < τ.im := τ.im_pos
  by_cases him : τ.im ≤ 2
  · -- ### the low strip `1/2 ≤ Im τ ≤ 2`
    have hb := hlo τ r hτ hτhalf him
    -- `(Im τ)^{-β₂} ≤ 2^{β₂}` because `Im τ ≥ 1/2` and `β₂ ≥ 0`
    have hpow : (τ.im) ^ (-β₂) ≤ (2 : ℝ) ^ β₂ := by
      have h1 : (τ.im) ^ (-β₂) ≤ ((1 : ℝ) / 2) ^ (-β₂) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
      have h2 : ((1 : ℝ) / 2) ^ (-β₂) = (2 : ℝ) ^ β₂ := by
        have h3 : ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ := by norm_num
        rw [h3, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
      rwa [h2] at h1
    -- `‖τ‖ ≤ 3` on the low strip
    have hnorm : ‖(τ : ℂ)‖ ≤ 3 := by
      have hmem := Work.Asymptotics.mem_DomainD.mp hτ
      have hreabs : -1 < τ.re ∧ τ.re < 1 := ⟨hmem.1, hmem.2.1⟩
      have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        ring
      have h9 : ‖(τ : ℂ)‖ ^ 2 ≤ 9 := by
        have h1 : τ.re ^ 2 < 1 := by nlinarith [hreabs.1, hreabs.2]
        have h2 : τ.im ^ 2 ≤ 4 := by nlinarith [hτpos.le]
        rw [hsq]; linarith
      nlinarith [norm_nonneg (τ : ℂ)]
    have hpow2 : (‖(τ : ℂ)‖) ^ δ₂ ≤ (3 : ℝ) ^ δ₂ :=
      Real.rpow_le_rpow (norm_nonneg _) hnorm hδ₂
    have hle : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
        ≤ α₂ * 2 ^ β₂ + γ₂ * 3 ^ δ₂ := by
      calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
            Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
          ≤ α₂ * (τ.im) ^ (-β₂) + γ₂ * (‖(τ : ℂ)‖) ^ δ₂ := hb
        _ ≤ α₂ * 2 ^ β₂ + γ₂ * 3 ^ δ₂ := by
            have h1 := mul_le_mul_of_nonneg_left hpow hα₂
            have h2 := mul_le_mul_of_nonneg_left hpow2 hγ₂
            linarith
    rw [neg_zero, Real.rpow_zero, mul_one]
    have hrest : (0 : ℝ) ≤ (α₁ + γ₁) * (‖(τ : ℂ)‖) ^ δ₁ :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
    linarith
  · -- ### the funnel `2 ≤ Im τ`
    simp only [not_le] at him
    have hhi' := hhi τ r hτ (le_of_lt him)
    have h1 : (τ.im) ^ (-β₁) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hnorm1 : (1 : ℝ) ≤ ‖(τ : ℂ)‖ :=
      le_trans (by linarith) (Work.Kernels.im_le_coe_norm τ)
    have h3 : (1 : ℝ) ≤ (‖(τ : ℂ)‖) ^ δ₁ := Real.one_le_rpow hnorm1 hδ₁
    have hmid : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
        ≤ (α₁ + γ₁) * (‖(τ : ℂ)‖) ^ δ₁ := by
      have hγ' : γ₁ ≤ γ₁ * (‖(τ : ℂ)‖) ^ δ₁ := by
        calc γ₁ = γ₁ * 1 := (mul_one γ₁).symm
          _ ≤ γ₁ * (‖(τ : ℂ)‖) ^ δ₁ := mul_le_mul_of_nonneg_left h3 hγ₁
      have hα' : α₁ ≤ α₁ * (‖(τ : ℂ)‖) ^ δ₁ := by
        calc α₁ = α₁ * 1 := (mul_one α₁).symm
          _ ≤ α₁ * (‖(τ : ℂ)‖) ^ δ₁ := mul_le_mul_of_nonneg_left h3 hα₁
      calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
            Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
          ≤ α₁ * (τ.im) ^ (-β₁) + γ₁ * (‖(τ : ℂ)‖) ^ δ₁ := hhi'
        _ ≤ α₁ * 1 + γ₁ * (‖(τ : ℂ)‖) ^ δ₁ := by
            have := mul_le_mul_of_nonneg_left h1 hα₁
            linarith
        _ ≤ (α₁ + γ₁) * (‖(τ : ℂ)‖) ^ δ₁ := by
            have h2 : α₁ * 1 ≤ α₁ * (‖(τ : ℂ)‖) ^ δ₁ := by simpa using hα'
            linarith
    rw [neg_zero, Real.rpow_zero, mul_one]
    have hrest : (0 : ℝ) ≤ α₂ * 2 ^ β₂ + γ₂ * 3 ^ δ₂ := by positivity
    linarith

end Work.Asymptotics
