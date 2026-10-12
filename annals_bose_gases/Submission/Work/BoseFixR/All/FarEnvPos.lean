import ChallengeDeps
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.All.RB5FSFixAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/FarEnvPos.lean` — positivity of the `ε`-split environment

`Work.BoseFixR.All.FarEnvPos` is the *Bogoliubov-positivity* input of the far leg
(`Work.BoseFixR.All.FarBogPair` needs exactly `0 < 𝒜_k ∧ |ℬ_k| ≤ 𝒜_k` at
`E' = farEnv E v μ ρ`).  FS `lem:Roughbounds` obtains it from the `ε`-split: with
`ε = epsFar v μ ρ = √(𝓜/((ρ+μ)ℓ³))` and `τ̃ ≥ 0`, the diagonal is

  `𝒜_k = (1−ε)τ_k + ρε^{−1/2}a + ρŴ₁(k)`

and `|ρŴ₁(k)| ≤ ρ·16πa` (`hW1`), so `𝒜_k ≥ ρa(ε^{−1/2} − 16π) > 0` and
`|ℬ_k| ≤ ρ·16πa ≤ 𝒜_k` as soon as `ε^{−1/2} > 32π`, which holds because
`ε ≤ 10^{−8}` (`hε`) forces `ε^{−1/2} ≥ 10^4`.

The only input from the view besides the definitional unfoldings is `τ_k ≥ 0`
(`E.tau` is pinned to the smoothed symbol `tauSm`, which is a nonnegative
combination of the nonnegative profile `tauProf`, with `0 ≤ ε_T ≤ 1` from
`FSParamsView`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Consequences of the view used by the far environment -/

/-- `τ̃ ≥ 0` at the chosen profile (`exists_tauProf`'s lower bound is a square). -/
lemma farEnvPos_tauProf_nonneg (r : ℝ) : 0 ≤ Work.BoseBoxFock.tauProf r := by
  have h := Work.BoseBoxFock.tauProf_spec.2.2.1 r
  linarith [sq_nonneg (max 0 (r - 2))]

/-- The view's `ε_T`-pin gives `0 ≤ ε_T ≤ 1` (`FSParamsView`: `ε_T = X^{23/4}` with
`0 < t ≤ 1`). -/
lemma farEnvPos_eT_bounds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFSAll v h μ) : 0 ≤ D.E.eT ∧ D.E.eT ≤ 1 := by
  unfold KzDatum.viewFSAll RViewFSAll at hview
  obtain ⟨hFSP, -⟩ := hview
  have hv := Classical.choice hFSP
  refine ⟨?_, ?_⟩
  · rw [hv.eT_eq]; exact (fsXp_pos hv.t_pos).le
  · rw [hv.eT_eq]
    exact fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)

/-- `0 ≤ τ_k` at a view-satisfying datum: the `τ`-pin is the smoothed symbol, a convex
combination of the nonnegative profile. -/
lemma farEnvPos_tau_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFSAll v h μ) (k : D.Mode) : 0 ≤ D.E.tau k := by
  obtain ⟨heT0, heT1⟩ := farEnvPos_eT_bounds D hview
  unfold KzDatum.viewFSAll RViewFSAll at hview
  obtain ⟨-, -, -, -, -, -, -, -, heTpin, -, -, htau, -⟩ := hview
  rw [htau, ← heTpin]
  simp only [tauSm]
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (farEnvPos_tauProf_nonneg _))
    (mul_nonneg (mul_nonneg heT0 (sq_nonneg _)) (farEnvPos_tauProf_nonneg _))

/-! ## 2. The `ε`-arithmetic of FS `eq:ChoiceEpsilon` -/

/-- `ε > 0` at admissible parameters (`𝓜 > 0`, `ρ + μ > 0`, `ℓ > 0`). -/
lemma farEnvPos_eps_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (hρ : 0 < ρ) : 0 < epsFar v μ ρ := by
  have hM : 0 < bigMV v μ := Work.BoseBox.bigM_pos_of_params hμ hav
  have hℓ : 0 < ell v μ := by
    rw [ell]; exact Work.BoseBox.sideAt_pos hμ hav
  rw [epsFar]
  exact Real.sqrt_pos_of_pos (div_pos hM (mul_pos (by linarith) (pow_pos hℓ 3)))

/-- `ε ≤ 10^{-8}` forces `ε^{−1/2} ≥ 10^4`: `ε^{−1/2} = (√ε)^{−1}` and `√ε ≤ 10^{−4}`. -/
lemma farEnvPos_rpow_ge {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ}
    (hε0 : 0 < epsFar v μ ρ) (hε : epsFar v μ ρ ≤ 1 / 10 ^ 8) :
    (10 : ℝ) ^ 4 ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := by
  have hsqrt_le : Real.sqrt (epsFar v μ ρ) ≤ 1 / 10 ^ 4 := by
    have h1 : Real.sqrt (epsFar v μ ρ) ≤ Real.sqrt (1 / 10 ^ 8 : ℝ) := Real.sqrt_le_sqrt hε
    have h2 : Real.sqrt (1 / 10 ^ 8 : ℝ) = 1 / 10 ^ 4 := by
      rw [show (1 / 10 ^ 8 : ℝ) = (1 / 10 ^ 4) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    linarith
  have h3 : (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (epsFar v μ ρ))⁻¹ := by
    rw [Real.rpow_neg hε0.le (1 / 2), ← Real.sqrt_eq_rpow]
  rw [h3]
  have h4 := one_div_le_one_div_of_le (Real.sqrt_pos_of_pos hε0) hsqrt_le
  have h5 : (1 : ℝ) / (1 / 10 ^ 4) = 10 ^ 4 := by norm_num
  rw [h5] at h4
  rwa [one_div] at h4

/-! ## 3. The B-indices of the split pair form -/

theorem FarEnvPos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {μ ρ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (hρ : 0 < ρ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hW1 : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * BoseGases.a v)
    (hε : Work.BoseFixR.All.epsFar v μ ρ ≤ 1 / 10 ^ 8) :
    ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      0 < (Work.BoseFixR.KzEnvAt (Work.BoseFixR.All.farEnv
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k
      ∧ |(Work.BoseFixR.KzEnvAt (Work.BoseFixR.All.farEnv
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k|
          ≤ (Work.BoseFixR.KzEnvAt (Work.BoseFixR.All.farEnv
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k := by
  intro k
  have hτ : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.tau k :=
    farEnvPos_tau_nonneg (HonestBoxFam v h fc fu HM μ) hview k
  have hε0 : 0 < epsFar v μ ρ := farEnvPos_eps_pos hμ hav hρ
  have hbig : (10 : ℝ) ^ 4 ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := farEnvPos_rpow_ge hε0 hε
  have h1ε : 0 ≤ 1 - epsFar v μ ρ := by linarith
  have hAeq : (KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k
      = (1 - epsFar v μ ρ) * (HonestBoxFam v h fc fu HM μ).E.tau k
        + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
        + ρ * (HonestBoxFam v h fc fu HM μ).E.W1 k := rfl
  have hBeq : (KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k
      = ρ * (HonestBoxFam v h fc fu HM μ).E.W1 k := rfl
  constructor
  · -- positivity: `𝒜_k ≥ ρa(ε^{-1/2} − 16π)`
    rw [hAeq]
    have he : 16 * Real.pi < (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := by
      have h64 : 16 * Real.pi < 64 := by linarith [Real.pi_lt_four]
      have h10000 : (64 : ℝ) < (10 : ℝ) ^ 4 := by norm_num
      linarith
    have h2 : 16 * Real.pi * BoseGases.a v
        < (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v :=
      mul_lt_mul_of_pos_right he hav
    have hpos : ρ * (16 * Real.pi * BoseGases.a v)
        < ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := by
      simpa only [mul_assoc] using mul_lt_mul_of_pos_left h2 hρ
    have hneg : -(ρ * (16 * Real.pi * BoseGases.a v))
        ≤ ρ * (HonestBoxFam v h fc fu HM μ).E.W1 k := by
      have h3 : ρ * (-(16 * Real.pi * BoseGases.a v))
          ≤ ρ * (HonestBoxFam v h fc fu HM μ).E.W1 k :=
        mul_le_mul_of_nonneg_left (abs_le.mp (hW1 k)).1 hρ.le
      linarith
    have hnn : 0 ≤ (1 - epsFar v μ ρ) * (HonestBoxFam v h fc fu HM μ).E.tau k :=
      mul_nonneg h1ε hτ
    linarith
  · -- domination: `|ℬ_k| = ρ|Ŵ₁(k)| ≤ ρ·16πa ≤ 𝒜_k`
    rw [hAeq, hBeq, abs_mul, abs_of_pos hρ]
    have h1 : ρ * |(HonestBoxFam v h fc fu HM μ).E.W1 k|
        ≤ ρ * (16 * Real.pi * BoseGases.a v) :=
      mul_le_mul_of_nonneg_left (hW1 k) hρ.le
    have hneg : -(ρ * |(HonestBoxFam v h fc fu HM μ).E.W1 k|)
        ≤ ρ * (HonestBoxFam v h fc fu HM μ).E.W1 k := by
      have h3 : ρ * (-|(HonestBoxFam v h fc fu HM μ).E.W1 k|)
          ≤ ρ * (HonestBoxFam v h fc fu HM μ).E.W1 k :=
        mul_le_mul_of_nonneg_left (neg_abs_le _) hρ.le
      linarith
    have he32 : 32 * Real.pi < (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := by
      have h128 : 32 * Real.pi < 128 := by linarith [Real.pi_lt_four]
      have h10000 : (128 : ℝ) < (10 : ℝ) ^ 4 := by norm_num
      linarith
    have h2 : 2 * (ρ * (16 * Real.pi * BoseGases.a v))
        ≤ ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := by
      have h3 : 32 * Real.pi * BoseGases.a v
          ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v :=
        mul_le_mul_of_nonneg_right he32.le hav.le
      have h4 : ρ * (32 * Real.pi * BoseGases.a v)
          ≤ ρ * ((epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v) :=
        mul_le_mul_of_nonneg_left h3 hρ.le
      linarith
    have hnn : 0 ≤ (1 - epsFar v μ ρ) * (HonestBoxFam v h fc fu HM μ).E.tau k :=
      mul_nonneg h1ε hτ
    linarith

end Work.BoseFixR.All
