import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.FireFix.Prime.physVort_support
import Submission.Work.FTS.FireFix.Prime.physVort_bound
import Submission.Work.FTS.FireFix.Prime.PhysVortHolderSlice
import Submission.Work.FTS.FireFix.Prime.physVort_holder_time
import Submission.Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound
import Submission.Work.FTS.FireFix.Prime.physVort_timeDeriv_aesm
import Submission.Work.FTS.FireFix.Prime.profFullHolder
import Submission.Work.FTS.FireFix.Prime.profFullBounds
import Submission.Work.FTS.FireFix.Prime.dzProfFullUniform
import Submission.Work.FTS.FireFix.Prime.dzProfFullZero
import Submission.Work.FTS.FireFix.Prime.dtgZero
import Submission.Work.FTS.FireFix.Prime.clockBounds
import Submission.Work.FTS.FireFix.Prime.clockLipschitz
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.FireFix.Prime.PvbPartA

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology

open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-! ## Part B: the `τ`-Hölder continuity of `∂_τω` -/

/-- The `z`-slope of the self-similar variable in the form used below. -/
theorem pvb_zSlope_eq {α : ℝ} {B : ℝ → ℝ} {ρ s : ℝ} (hB : B s ≠ 0) :
    zSlope α B ρ s = -((ρ ^ pExp α / B s) * (deriv B s / B s)) := by
  rw [zSlope]
  field_simp

/-- `pzProf` is the `z`-derivative of the full profile. -/
theorem pvb_pzProf_eq_deriv {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) {z θ τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) :
    pzProf α g z θ τ = deriv (fun z' => profFull α g z' θ τ) z := by
  have h1 := (dzProfFullUniform h z hz).1 z θ τ hz hθ hτ
  rw [pzProf, h1]
  rfl

/-- The absolute value of the odd extension is the absolute value of the profile at `|θ|`. -/
theorem pvb_profOdd_abs_eq (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) :
    |profOdd α g z θ τ| = |profFull α g z |θ| τ| := by
  by_cases hθ : 0 ≤ θ
  · rw [profOdd, if_pos hθ, abs_of_nonneg hθ]
  · rw [profOdd, if_neg hθ, abs_of_neg (not_le.mp hθ), abs_neg]

/-- The odd extension vanishes where the profile does. -/
theorem pvb_profOdd_eq_zero {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ}
    (h : profFull α g z |θ| τ = 0) : profOdd α g z θ τ = 0 := by
  by_cases hθ : 0 ≤ θ
  · have hθ' : |θ| = θ := abs_of_nonneg hθ
    rw [profOdd, if_pos hθ]
    rw [hθ'] at h
    exact h
  · have hθ' : |θ| = -θ := abs_of_neg (not_le.mp hθ)
    rw [profOdd, if_neg hθ]
    rw [hθ'] at h
    rw [h, neg_zero]

/-- The odd extension of two points differs by the difference of the profiles at `|θ|`. -/
theorem pvb_profOdd_sub (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z z' θ τ τ' : ℝ) :
    |profOdd α g z θ τ - profOdd α g z' θ τ'|
      = |profFull α g z |θ| τ - profFull α g z' |θ| τ'| := by
  by_cases hθ : 0 ≤ θ
  · rw [profOdd, if_pos hθ, profOdd, if_pos hθ, abs_of_nonneg hθ]
  · rw [profOdd, if_neg hθ, profOdd, if_neg hθ, abs_of_neg (not_le.mp hθ)]
    rw [show -profFull α g z (-θ) τ - -profFull α g z' (-θ) τ'
        = -(profFull α g z (-θ) τ - profFull α g z' (-θ) τ') by ring, abs_neg]

/-- **The explicit form of `dProfOdd`**: the slope of the self-similar variable times the
`z`-derivative of the profile, plus the `τ`-derivative of the perturbation, with the sign of the
odd extension in `θ`. -/
theorem pvb_dProfOdd_eq {α : ℝ} {B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {ρ θ τ : ℝ}
    (hB : B τ ≠ 0) :
    dProfOdd α B g ρ θ τ
      = (if 0 ≤ θ then (1 : ℝ) else -1)
        * (-((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
            * (deriv B τ / B τ)
          + deriv (fun s => g (ρ ^ pExp α / B τ) |θ| s) τ) := by
  rw [dProfOdd]
  have hsl := pvb_zSlope_eq (α := α) (B := B) (ρ := ρ) (s := τ) hB
  by_cases hθ : 0 ≤ θ
  · rw [if_pos hθ, if_pos hθ, abs_of_nonneg hθ, hsl]
    ring
  · rw [if_neg hθ, if_neg hθ, abs_of_neg (not_le.mp hθ), hsl]
    ring

/-! ### The `τ`-Hölder estimate for `∂_τω` -/

/-- **Interpolation on a bounded strip**: `d ≤ S^(1-α)·d^α` for `0 ≤ d ≤ S` and `0 < α ≤ 1`. -/
theorem pvb_self_le_rpow {α S d : ℝ} (hd : 0 ≤ d) (hdS : d ≤ S) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    d ≤ S ^ (1 - α) * d ^ α := by
  rcases eq_or_lt_of_le hd with h | h
  · rw [← h]
    simp [Real.zero_rpow, hα0.ne']
  · have h1 : d = d ^ (1 - α) * d ^ α := by
      rw [← Real.rpow_add h, show 1 - α + α = 1 by ring, Real.rpow_one]
    have h2 : d ^ (1 - α) ≤ S ^ (1 - α) := Real.rpow_le_rpow hd hdS (by linarith)
    have h3 : 0 ≤ d ^ α := Real.rpow_nonneg hd _
    calc d = d ^ (1 - α) * d ^ α := h1
      _ ≤ S ^ (1 - α) * d ^ α := mul_le_mul_of_nonneg_right h2 h3

theorem pvb_clockData {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} (h : RegPkg' α S A B g) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |(A τ)⁻¹ - (A τ')⁻¹| ≤ C * |τ - τ'| ^ α) ∧
      (∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
        |deriv A τ / (A τ) ^ 2 - deriv A τ' / (A τ') ^ 2| ≤ C * |τ - τ'| ^ α) ∧
      (∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
        |deriv B τ / B τ - deriv B τ' / B τ'| ≤ C * |τ - τ'| ^ α) := by
  obtain ⟨a₀, a₁, ha₀, hAb⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hBb⟩ := h.hBb
  obtain ⟨a₂, ha₂⟩ := h.hAd
  obtain ⟨b₂, hb₂⟩ := h.hBd
  obtain ⟨a₃, ha₃⟩ := h.hAdh
  obtain ⟨b₃, hb₃⟩ := h.hBdh
  obtain ⟨Kb, hKb0, hKb⟩ := clockLipschitz h
  set A2 : ℝ := max a₂ 0 with hA2def
  set A3 : ℝ := max a₃ 0 with hA3def
  set B2 : ℝ := max b₂ 0 with hB2def
  set B3 : ℝ := max b₃ 0 with hB3def
  set K' : ℝ := S ^ (1 - α) with hK'def
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_rfl, h.hS.le⟩
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ (le_trans (hAb 0 h0mem).1 (hAb 0 h0mem).2)
  have hb₁0 : 0 < b₁ := lt_of_lt_of_le hb₀ (le_trans (hBb 0 h0mem).1 (hBb 0 h0mem).2)
  have hA20 : 0 ≤ A2 := le_max_right _ _
  have hA30 : 0 ≤ A3 := le_max_right _ _
  have hB20 : 0 ≤ B2 := le_max_right _ _
  have hB30 : 0 ≤ B3 := le_max_right _ _
  have hK'0 : 0 ≤ K' := by rw [hK'def]; exact Real.rpow_nonneg h.hS.le _
  have hA2 : ∀ τ ∈ Set.Icc 0 S, |deriv A τ| ≤ A2 :=
    fun τ hτ => le_trans (ha₂ τ hτ) (le_max_left _ _)
  have hB2 : ∀ τ ∈ Set.Icc 0 S, |deriv B τ| ≤ B2 :=
    fun τ hτ => le_trans (hb₂ τ hτ) (le_max_left _ _)
  have hA3 : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |deriv A τ - deriv A τ'| ≤ A3 * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => le_trans (ha₃ τ hτ τ' hτ') (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (abs_nonneg _) α))
  have hB3 : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |deriv B τ - deriv B τ'| ≤ B3 * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => le_trans (hb₃ τ hτ τ' hτ') (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (abs_nonneg _) α))
  have hAlip : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |A τ - A τ'| ≤ a₂ * |τ - τ'| :=
    abs_sub_le_of_deriv_bound h.hAdiff ha₂
  have hK1 : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |τ - τ'| ≤ K' * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ'
    have h1 : |τ - τ'| ≤ S := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hτ.1, hτ.2, hτ'.1, hτ'.2]
    have := pvb_self_le_rpow (abs_nonneg _) h1 h.hα (le_trans h.hα13 (by norm_num))
    rwa [hK'def]
  set C : ℝ := A2 / a₀ ^ 2 * K' + (A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4
      + (B3 * b₁ + B2 * Kb * K') / b₀ ^ 2 with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ A2 / a₀ ^ 2 * K' := by positivity
    have h2 : 0 ≤ (A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4 := by positivity
    have h3 : 0 ≤ (B3 * b₁ + B2 * Kb * K') / b₀ ^ 2 := by positivity
    linarith
  have hterm1 : A2 / a₀ ^ 2 * K' ≤ C := by
    rw [hCdef]
    have h2 : 0 ≤ (A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4 := by positivity
    have h3 : 0 ≤ (B3 * b₁ + B2 * Kb * K') / b₀ ^ 2 := by positivity
    linarith
  have hterm2 : (A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ A2 / a₀ ^ 2 * K' := by positivity
    have h3 : 0 ≤ (B3 * b₁ + B2 * Kb * K') / b₀ ^ 2 := by positivity
    linarith
  have hterm3 : (B3 * b₁ + B2 * Kb * K') / b₀ ^ 2 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ A2 / a₀ ^ 2 * K' := by positivity
    have h2 : 0 ≤ (A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4 := by positivity
    linarith
  refine ⟨C, hC0, ?_, ?_, ?_⟩
  · intro τ hτ τ' hτ'
    have hAτ : 0 < A τ := h.hA τ hτ
    have hAτ' : 0 < A τ' := h.hA τ' hτ'
    have hnum : |A τ' - A τ| ≤ A2 * |τ - τ'| := by
      rw [abs_sub_comm]
      exact le_trans (hAlip τ hτ τ' hτ')
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    have hden : a₀ ^ 2 ≤ A τ * A τ' := by
      have h1 := (hAb τ hτ).1
      have h2 := (hAb τ' hτ').1
      nlinarith [mul_le_mul h1 h2 ha₀.le hAτ.le]
    have hkey : |(A τ)⁻¹ - (A τ')⁻¹| = |A τ' - A τ| / (A τ * A τ') := by
      rw [inv_sub_inv (ne_of_gt hAτ) (ne_of_gt hAτ'), abs_div, abs_of_pos (mul_pos hAτ hAτ')]
    rw [hkey]
    have h1 : |A τ' - A τ| / (A τ * A τ') ≤ A2 * |τ - τ'| / (A τ * A τ') :=
      div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos hAτ hAτ'))
    have h2 : A2 * |τ - τ'| / (A τ * A τ') ≤ A2 * |τ - τ'| / a₀ ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg hA20 (abs_nonneg _)) (by positivity) hden
    have h3 : A2 * |τ - τ'| / a₀ ^ 2 ≤ A2 / a₀ ^ 2 * K' * |τ - τ'| ^ α := by
      calc A2 * |τ - τ'| / a₀ ^ 2 = (A2 / a₀ ^ 2) * |τ - τ'| := by ring
        _ ≤ (A2 / a₀ ^ 2) * (K' * |τ - τ'| ^ α) :=
            mul_le_mul_of_nonneg_left (hK1 τ hτ τ' hτ') (div_nonneg hA20 (by positivity))
        _ = A2 / a₀ ^ 2 * K' * |τ - τ'| ^ α := by ring
    have h4 : A2 / a₀ ^ 2 * K' * |τ - τ'| ^ α ≤ C * |τ - τ'| ^ α :=
      mul_le_mul_of_nonneg_right hterm1 (Real.rpow_nonneg (abs_nonneg _) α)
    exact le_trans (le_trans h1 h2) (le_trans h3 h4)
  · intro τ hτ τ' hτ'
    have hAτ : 0 < A τ := h.hA τ hτ
    have hAτ' : 0 < A τ' := h.hA τ' hτ'
    have hnum : |deriv A τ * (A τ') ^ 2 - deriv A τ' * (A τ) ^ 2|
        ≤ A3 * a₁ ^ 2 * |τ - τ'| ^ α + A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α := by
      have hsplit : deriv A τ * (A τ') ^ 2 - deriv A τ' * (A τ) ^ 2
          = (deriv A τ - deriv A τ') * (A τ') ^ 2
            + deriv A τ' * ((A τ') ^ 2 - (A τ) ^ 2) := by ring
      rw [hsplit]
      have h1 : |(deriv A τ - deriv A τ') * (A τ') ^ 2| ≤ A3 * a₁ ^ 2 * |τ - τ'| ^ α := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (A τ'))]
        calc |deriv A τ - deriv A τ'| * (A τ') ^ 2 ≤ (A3 * |τ - τ'| ^ α) * a₁ ^ 2 :=
              mul_le_mul (hA3 τ hτ τ' hτ') (by nlinarith [(hAb τ' hτ').2, ha₁0.le])
                (sq_nonneg _) (mul_nonneg hA30 (Real.rpow_nonneg (abs_nonneg _) α))
          _ = A3 * a₁ ^ 2 * |τ - τ'| ^ α := by ring
      have h2 : |deriv A τ' * ((A τ') ^ 2 - (A τ) ^ 2)|
          ≤ A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α := by
        rw [abs_mul]
        have hsq : |(A τ') ^ 2 - (A τ) ^ 2| ≤ 2 * a₁ * A2 * K' * |τ - τ'| ^ α := by
          have hfac : (A τ') ^ 2 - (A τ) ^ 2 = (A τ' - A τ) * (A τ' + A τ) := by ring
          rw [hfac, abs_mul]
          have hb1 : |A τ' - A τ| ≤ A2 * |τ - τ'| := by
            rw [abs_sub_comm]
            exact le_trans (hAlip τ hτ τ' hτ')
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
          have hb2 : |A τ' + A τ| ≤ 2 * a₁ := by
            have h1 := (hAb τ hτ).2
            have h2 := (hAb τ' hτ').2
            rw [abs_le]
            constructor <;> linarith
          calc |A τ' - A τ| * |A τ' + A τ| ≤ (A2 * |τ - τ'|) * (2 * a₁) :=
                mul_le_mul hb1 hb2 (abs_nonneg _) (mul_nonneg hA20 (abs_nonneg _))
            _ = 2 * a₁ * A2 * |τ - τ'| := by ring
            _ ≤ 2 * a₁ * A2 * (K' * |τ - τ'| ^ α) :=
                mul_le_mul_of_nonneg_left (hK1 τ hτ τ' hτ') (by positivity)
            _ = 2 * a₁ * A2 * K' * |τ - τ'| ^ α := by ring
        calc |deriv A τ'| * |(A τ') ^ 2 - (A τ) ^ 2|
            ≤ A2 * (2 * a₁ * A2 * K' * |τ - τ'| ^ α) :=
              mul_le_mul (hA2 τ' hτ') hsq (abs_nonneg _) hA20
          _ = A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α := by ring
      exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
    have hkey : deriv A τ / (A τ) ^ 2 - deriv A τ' / (A τ') ^ 2
        = (deriv A τ * (A τ') ^ 2 - deriv A τ' * (A τ) ^ 2)
            / ((A τ) ^ 2 * (A τ') ^ 2) := by
      field_simp
    rw [hkey, abs_div, abs_of_pos (by positivity : 0 < (A τ) ^ 2 * (A τ') ^ 2)]
    have hden : a₀ ^ 4 ≤ (A τ) ^ 2 * (A τ') ^ 2 := by
      have h1 := (hAb τ hτ).1
      have h2 := (hAb τ' hτ').1
      nlinarith [mul_le_mul h1 h2 ha₀.le hAτ.le]
    have hP0 : 0 ≤ A3 * a₁ ^ 2 * |τ - τ'| ^ α + A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α := by
      positivity
    calc |deriv A τ * (A τ') ^ 2 - deriv A τ' * (A τ) ^ 2|
            / ((A τ) ^ 2 * (A τ') ^ 2)
        ≤ (A3 * a₁ ^ 2 * |τ - τ'| ^ α + A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α)
            / ((A τ) ^ 2 * (A τ') ^ 2) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (A3 * a₁ ^ 2 * |τ - τ'| ^ α + A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α) / a₀ ^ 4 :=
          div_le_div_of_nonneg_left hP0 (by positivity) hden
      _ = ((A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4) * |τ - τ'| ^ α := by ring
      _ ≤ C * |τ - τ'| ^ α :=
          mul_le_mul_of_nonneg_right hterm2 (Real.rpow_nonneg (abs_nonneg _) α)
  · intro τ hτ τ' hτ'
    have hBτ : 0 < B τ := h.hB τ hτ
    have hBτ' : 0 < B τ' := h.hB τ' hτ'
    have hnum : |(deriv B τ - deriv B τ') * B τ' + deriv B τ' * (B τ' - B τ)|
        ≤ B3 * b₁ * |τ - τ'| ^ α + B2 * Kb * K' * |τ - τ'| ^ α := by
      have h1 : |(deriv B τ - deriv B τ') * B τ'| ≤ B3 * b₁ * |τ - τ'| ^ α := by
        rw [abs_mul, abs_of_pos hBτ']
        calc |deriv B τ - deriv B τ'| * B τ' ≤ (B3 * |τ - τ'| ^ α) * b₁ :=
              mul_le_mul (hB3 τ hτ τ' hτ') (hBb τ' hτ').2 (le_of_lt hBτ')
                (mul_nonneg hB30 (Real.rpow_nonneg (abs_nonneg _) α))
          _ = B3 * b₁ * |τ - τ'| ^ α := by ring
      have h2 : |deriv B τ' * (B τ' - B τ)| ≤ B2 * Kb * K' * |τ - τ'| ^ α := by
        rw [abs_mul]
        have hstep : |B τ' - B τ| ≤ Kb * K' * |τ - τ'| ^ α := by
          rw [abs_sub_comm]
          calc |B τ - B τ'| ≤ Kb * |τ - τ'| := hKb τ hτ τ' hτ'
            _ ≤ Kb * (K' * |τ - τ'| ^ α) :=
                mul_le_mul_of_nonneg_left (hK1 τ hτ τ' hτ') hKb0
            _ = Kb * K' * |τ - τ'| ^ α := by ring
        calc |deriv B τ'| * |B τ' - B τ| ≤ B2 * (Kb * K' * |τ - τ'| ^ α) :=
              mul_le_mul (hB2 τ' hτ') hstep (abs_nonneg _) hB20
          _ = B2 * Kb * K' * |τ - τ'| ^ α := by ring
      exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
    have hkey : deriv B τ / B τ - deriv B τ' / B τ'
        = ((deriv B τ - deriv B τ') * B τ' + deriv B τ' * (B τ' - B τ))
            / (B τ * B τ') := by
      field_simp
      ring
    rw [hkey, abs_div, abs_of_pos (mul_pos hBτ hBτ')]
    have hden : b₀ ^ 2 ≤ B τ * B τ' := by
      have h1 := (hBb τ hτ).1
      have h2 := (hBb τ' hτ').1
      nlinarith [mul_le_mul h1 h2 hb₀.le hBτ.le]
    have hP0 : 0 ≤ B3 * b₁ * |τ - τ'| ^ α + B2 * Kb * K' * |τ - τ'| ^ α := by positivity
    calc |(deriv B τ - deriv B τ') * B τ' + deriv B τ' * (B τ' - B τ)| / (B τ * B τ')
        ≤ (B3 * b₁ * |τ - τ'| ^ α + B2 * Kb * K' * |τ - τ'| ^ α) / (B τ * B τ') :=
          div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos hBτ hBτ'))
      _ ≤ (B3 * b₁ * |τ - τ'| ^ α + B2 * Kb * K' * |τ - τ'| ^ α) / b₀ ^ 2 :=
          div_le_div_of_nonneg_left hP0 (by positivity) hden
      _ = ((B3 * b₁ + B2 * Kb * K') / b₀ ^ 2) * |τ - τ'| ^ α := by ring
      _ ≤ C * |τ - τ'| ^ α :=
          mul_le_mul_of_nonneg_right hterm3 (Real.rpow_nonneg (abs_nonneg _) α)


end Work.FTS.FireFix.Prime