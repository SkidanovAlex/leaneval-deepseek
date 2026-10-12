import ChallengeDeps
import Submission.Work.BoseBogFS.ZPCleanDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.BogFSKernel` — the honest FS kernel of `integral_cleanFun_le`

The target `Work.BoseBogFS.integral_cleanFun_le` needs FS `lem:BogIntegral`'s estimate
`I₁ ≤ −lhyValue(8π) + C ε` at the *honest* datum.  The corpus's `Work.BoseB6Est.fsI1_le`
proves that estimate for **any** `FsKernel` satisfying the parameter regime `FsI1Regime`.

Here we define the kernel used to instantiate it: the *affine model kernel*
`β(r) = 8π + η r` on `[0,T]`, `0` beyond, with
`η = 16πR√(ρa)` (the `Ŵ₁`-Lipschitz scale, `chat_W1fun_lipschitz`) and
`T = 10⁶(1 + log(1/dil))/lhyEps` (FS's momentum cutoff, chosen large enough that the
kernel tail `4π(8π)³/(2T)` and the logarithmic row are inside `lhyEps`).

The honest `β(t) = a⁻¹Ŵ₁(√(ρa)t)` then satisfies
`b(t) − β(‖t‖) ∈ [−2η‖t‖, δ₁]` with `δ₁ = 16πC_R(R/ℓ)²` (the `χ⋆χ` Taylor deficit,
`ConvChiBound.wScaled_sandwich`), which is what makes the comparison possible: the
deviation is *small* where `‖t‖ ≤ T`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The affine FS kernel** `β(r) = 8π + η r` on `[0,T]`, zero beyond.  Its
`FsKernel` data are `B = 8π + ηT`, `η`, `T`: the closeness field holds with equality
(`|β r − 8π| = η r`), the bound is `β r ≤ 8π + ηT`, and `β` vanishes past the cutoff. -/
def honKernel (η T : ℝ) (hη : 0 ≤ η) (hT : 0 ≤ T) : Work.BoseB6Est.FsKernel where
  β := fun r : ℝ => if r ∈ Set.Icc (0 : ℝ) T then 8 * Real.pi + η * r else 0
  B := 8 * Real.pi + η * T
  η := η
  T := T
  Bnn := by
    have := mul_nonneg hη hT
    nlinarith [Real.pi_pos]
  ηnn := hη
  Tnn := hT
  meas := Measurable.ite measurableSet_Icc
    (measurable_const.add (measurable_const.mul measurable_id)) measurable_const
  nonneg := by
    intro r
    by_cases h : r ∈ Set.Icc (0 : ℝ) T
    · obtain ⟨h1, -⟩ := Set.mem_Icc.mp h
      rw [if_pos h]
      have := mul_nonneg hη h1
      nlinarith [Real.pi_pos]
    · rw [if_neg h]
  bound := by
    intro r
    by_cases h : r ∈ Set.Icc (0 : ℝ) T
    · obtain ⟨-, h2⟩ := Set.mem_Icc.mp h
      rw [if_pos h]
      have := mul_le_mul_of_nonneg_left h2 hη
      linarith
    · rw [if_neg h]
      have := mul_nonneg hη hT
      linarith [Real.pi_pos]
  close := by
    intro r h0 hrT
    rw [if_pos (show r ∈ Set.Icc (0 : ℝ) T from Set.mem_Icc.mpr ⟨h0, hrT⟩),
      show 8 * Real.pi + η * r - 8 * Real.pi = η * r from by ring,
      abs_of_nonneg (mul_nonneg hη h0)]
  support := by
    intro r hr
    rw [if_neg (fun h : r ∈ Set.Icc (0 : ℝ) T =>
      absurd (Set.mem_Icc.mp h).2 (not_le.mpr hr))]

lemma honKernel_beta (η T : ℝ) (hη : 0 ≤ η) (hT : 0 ≤ T) {r : ℝ} (h0 : 0 ≤ r) (hrT : r ≤ T) :
    (honKernel η T hη hT).β r = 8 * Real.pi + η * r := by
  change (if r ∈ Set.Icc (0 : ℝ) T then 8 * Real.pi + η * r else 0) = 8 * Real.pi + η * r
  rw [if_pos (Set.mem_Icc.mpr ⟨h0, hrT⟩)]

lemma honKernel_beta_of_gt (η T : ℝ) (hη : 0 ≤ η) (hT : 0 ≤ T) {r : ℝ} (hr : T < r) :
    (honKernel η T hη hT).β r = 0 := by
  change (if r ∈ Set.Icc (0 : ℝ) T then 8 * Real.pi + η * r else 0) = 0
  rw [if_neg (fun h : r ∈ Set.Icc (0 : ℝ) T => absurd (Set.mem_Icc.mp h).2 (not_le.mpr hr))]

lemma honKernel_B (η T : ℝ) (hη : 0 ≤ η) (hT : 0 ≤ T) :
    (honKernel η T hη hT).B = 8 * Real.pi + η * T := rfl

lemma honKernel_eta (η T : ℝ) (hη : 0 ≤ η) (hT : 0 ≤ T) :
    (honKernel η T hη hT).η = η := rfl

lemma honKernel_T (η T : ℝ) (hη : 0 ≤ η) (hT : 0 ≤ T) :
    (honKernel η T hη hT).T = T := rfl

/-! ## The honest constants -/

/-- The Lipschitz scale of the honest `β`: `η = 16πR√(ρa)`. -/
def bogEta (v : E3 → ℝ) (R ρ : ℝ) : ℝ := 16 * Real.pi * R * Real.sqrt (ρ * a v)

/-- FS's momentum cutoff `T = 10⁶(1 + log(1/dil))/lhyEps`. -/
def bogT (v : E3 → ℝ) (R μ : ℝ) : ℝ :=
  10 ^ 6 * (1 + Real.log (1 / dil v μ))
    / Work.BoseB6.lhyEps (a v) R ((paramsAt μ (a v)).eT) ((paramsAt μ (a v)).Kl)
        ((paramsAt μ (a v)).s) ((paramsAt μ (a v)).d) μ

/-- The honest kinetic cutoff `c₁ = ½(K_ℓs)^{-1}√(μ/ρ)`, written as
`(2 s ℓ √(ρa))⁻¹`. -/
def bogC1 (v : E3 → ℝ) (ρ μ : ℝ) : ℝ :=
  (2 * (paramsAt μ (a v)).s * ell v μ * Real.sqrt (ρ * a v))⁻¹

/-- The honest kinetic cutoff `c₂ = ½(K_ℓds)^{-1}√(μ/ρ)`, written as
`(2 d s ℓ √(ρa))⁻¹`. -/
def bogC2 (v : E3 → ℝ) (ρ μ : ℝ) : ℝ :=
  (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * ell v μ * Real.sqrt (ρ * a v))⁻¹

/-- `κ_B v μ = √(μa)` (the momentum unit at density `μ`). -/
def bogSqrtPm (v : E3 → ℝ) (μ : ℝ) : ℝ := Real.sqrt (μ * a v)

/-- **The honest affine FS kernel** at the data `(v, R, ρ, μ)`: the kernel
`honKernel` fed with `η = max 0 (bogEta v R ρ)` and `T = max 0 (bogT v R μ)`
(the `max 0` makes the definition total; on the admissible region both arguments
are nonnegative and the maxima are attained by them). -/
def bogKernel (v : E3 → ℝ) (R ρ μ : ℝ) : Work.BoseB6Est.FsKernel :=
  honKernel (max 0 (bogEta v R ρ)) (max 0 (bogT v R μ)) (le_max_left _ _) (le_max_left _ _)

lemma bogKernel_beta (v : E3 → ℝ) (R ρ μ : ℝ) {r : ℝ}
    (hη : 0 ≤ bogEta v R ρ) (hT : 0 ≤ bogT v R μ) (h0 : 0 ≤ r) (hrT : r ≤ bogT v R μ) :
    (bogKernel v R ρ μ).β r = 8 * Real.pi + bogEta v R ρ * r := by
  have h := honKernel_beta (max 0 (bogEta v R ρ)) (max 0 (bogT v R μ))
    (le_max_left _ _) (le_max_left _ _) h0 (le_trans hrT (le_max_right _ _))
  have h2 : max 0 (bogEta v R ρ) * r = bogEta v R ρ * r := by rw [max_eq_right hη]
  rw [h2] at h
  exact h

lemma bogKernel_beta_of_gt (v : E3 → ℝ) (R ρ μ : ℝ) {r : ℝ}
    (hη : 0 ≤ bogEta v R ρ) (hT : 0 ≤ bogT v R μ) (hr : bogT v R μ < r) :
    (bogKernel v R ρ μ).β r = 0 := by
  have h := honKernel_beta_of_gt (max 0 (bogEta v R ρ)) (max 0 (bogT v R μ))
    (le_max_left _ _) (le_max_left _ _) (by rw [max_eq_right hT]; exact hr)
  exact h

lemma bogKernel_eta (v : E3 → ℝ) (R ρ μ : ℝ) :
    (bogKernel v R ρ μ).η = max 0 (bogEta v R ρ) := rfl

lemma bogKernel_T (v : E3 → ℝ) (R ρ μ : ℝ) :
    (bogKernel v R ρ μ).T = max 0 (bogT v R μ) := rfl

lemma bogEta_nonneg (v : E3 → ℝ) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ) : 0 ≤ bogEta v R ρ := by
  rw [bogEta]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hR)
    (Real.sqrt_nonneg _)

end Work.BoseBogFS
