import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.All.FarKernelRowsB
import Submission.Work.BoseFixR.All.FarResidAux
import Submission.Work.BoseFixR.All.FarThreeQSlots
import Submission.Work.BoseFixR.All.farEnvSideB
import Submission.Work.BoseFixR.All.farSlotSharp
import Submission.Work.BoseFixR.farLinArith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/All/farZPWin.lean` — the sharp windowed zero-point slot

The target `Work.BoseFixR.All.farZPWin` is FS §9's (`prop:FarAway`) zero-point estimate at the
`ε`-split environment `E' = farEnv E v μ ρ`, with the *sharp* mass constant

  `C₀ = (1 + 64√ε)(1 + 100√ε)`,  `ε = epsFar v μ ρ`,

on the spectral window `T.NWindow 𝓜 f`:

  `−(½ρ²ℓ³C₀·Mcont + ErrRes/2)‖f‖² ≤ ⟨f, KzBogFS F E' ρ f⟩`,  `Mcont = (2π)^{−3}∫Ŵ₁(q)²/(2q²)dq`.

**Route.**  The scalar route through `FarBogPair` (i.e. through `zpSumOf (farEnv E v μ ρ) ρ`) is a
dead end for large `ρ`: the `κ`-half of `zpSumOf` is `≍ (ρ−μ)²ℓ³ε^{1/2} ≍ ρ^{7/4}` while
`ErrRes/2 ≍ ρ^{3/2}`, so `Σ_k½κ_k ≤ ErrRes/2` cannot hold.  We therefore use FS's *operator*
decomposition

  `pairOpFar F E' ρ k = pairQuad F E' ρ k + 𝒞_k • pairLin F k`,  `𝒞_k = cCoefFar E' ρ k`,

and bound the two halves separately:

* the *quadratic* half per pair by Bogoliubov (`All.pairQuad_ground`), summed to `−(Σ_k½𝒵_k)‖f‖²`
  (`sum_pairQuad_ground`);
* the *linear* half by Cauchy–Schwarz against the window (`All.linWord_le`), which — applied at
  the environment with the reversed `χ̂` (reversing every `𝒞_k` and preserving `Σ_k𝒞_k²`) —
  yields the *lower* bound `−8√(Σ_k𝒞_k²)√𝓜‖f‖²` (`linWord_lower`); its arithmetic is exactly
  `farLinArith` (`≤ ErrRes/4`, *uniformly* in `ρ`).

The zero-point sum `Σ_k½𝒵_k` (over *all* modes, including the label `0`) is split as
`Σ_{k≠0}½𝒵_k + ½𝒵_0`:

* `Σ_{k≠0}½𝒵_k ≤ (ρ²/4)(1+64√ε)·Σ_{k≠0}Ŵ₁(k)²/τ'_k` (`All.farSlotSharp`, the *lossless* slot) and
  the row `hτ` bounds the `τ'`-weighted sum by `(1+100√ε)·2ℓ³Mcont` (`W1row_le`), giving exactly
  the target's `½ρ²ℓ³C₀Mcont`;
* the single label `0` is charged crudely to `ErrRes/4` (`zp_zero_mode`): this is uniform in `ρ`
  because `𝒵_0 ≤ ℬ_0²/𝒜_0 ≤ 256π²ρa·ε^{1/2}` is *linear* in `ρ`.

The `ρ = 0` branch is separate (`qw_KzBogFS_rho0_nonneg'`): at vanishing density `KzBogFS` is a
nonnegative combination of the `n_k + n_{−k}`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The `τ'`-weighted row of the statement, as a named hypothesis -/

/-- The `τ'`-weighted sharp lattice row (the hypothesis `hτ` of the target), named so that it can
be passed to the helper lemmas. -/
noncomputable def FarTauRowFS (v : E3 → ℝ) (h : ScatSol v) (μ ρ : ℝ) (N : ℕ) : Prop :=
  (∑ k ∈ Work.BoseB7.excited (Lab N),
      (chat (W1fun v h (ell v μ)) (kmomLab (ell v μ) N k)) ^ 2
        / ((1 - epsFar v μ ρ) * tauSm (paramsAt μ (a v)).eT (paramsAt μ (a v)).s
              (paramsAt μ (a v)).d (ell v μ) (kmomLab (ell v μ) N k)
            + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v))
    ≤ (1 + 100 * Real.sqrt (epsFar v μ ρ))
        * (2 * (((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
          * ∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)))

/-! ## 1. The vanishing-density branch -/

lemma KzBogFS_rho0_eq' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) :
    KzBogFS F E 0 = ∑ k : Mode, (1 / 2 : ℝ) • ((E.tau k) • (F.nOp k + F.nOp (-k))) := by
  simp only [KzBogFS]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp

/-- At vanishing density `KzBogFS` is a sum of nonnegative multiples of the operators
`n_k + n_{−k}`, hence has a nonnegative quadratic form. -/
lemma qw_KzBogFS_rho0_nonneg' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (E : Q3Env Mode) (f : F.H)
    (hτ : ∀ k : Mode, 0 ≤ E.tau k) :
    0 ≤ F.qw f (KzBogFS F E 0) := by
  rw [KzBogFS_rho0_eq']
  rw [qw_sum_smul_zp]
  refine Finset.sum_nonneg (fun k _ => ?_)
  rw [FockData.qw_smul]
  exact mul_nonneg (by norm_num) (mul_nonneg (hτ k) (qw_nOp_add_neg_nonneg F k f))

/-! ## 2. The summed per-pair quadratic ground bound -/

/-- **The half-weighted sum of FS `eq:BogIneq` over the pairs** at the quadratic half `pairQuad`
of the pair form: `Σ_k½𝒵_k` is the price of the quadratic word.  (Verbatim
`Work.BoseFixR.sum_qw_quad_ge` with `quadOpFar` replaced by `pairQuad`.) -/
theorem sum_pairQuad_ground {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ)
    (hA : ∀ k : Mode, 0 < (KzEnvAt E ρ).A k)
    (hB : ∀ k : Mode, |(KzEnvAt E ρ).B k| ≤ (KzEnvAt E ρ).A k)
    (hAB : ∀ k : Mode, 0 < (KzEnvAt E ρ).A k + (KzEnvAt E ρ).B k)
    (hAe : ∀ k : Mode, (KzEnvAt E ρ).A (-k) = (KzEnvAt E ρ).A k)
    (hBe : ∀ k : Mode, (KzEnvAt E ρ).B (-k) = (KzEnvAt E ρ).B k)
    (hccr : ∀ k : Mode, F.ccrK k k + F.ccrK (-k) (-k) ≤ 2) (f : F.H) :
    -((∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
        ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k))) * F.normSq f
      ≤ ∑ k : Mode, (1 / 2 : ℝ) * F.qw f (pairQuad F E ρ k) := by
  have hper : ∀ k : Mode,
      -((1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k))
          * F.normSq f
        ≤ (1 / 2 : ℝ) * F.qw f (pairQuad F E ρ k) := by
    intro k
    have h := pairQuad_ground F E ρ k (hA k) (hB k) (hAB k) (hAe k) (hBe k) (hccr k) f
    nlinarith [h]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Mode)) => hper k)
  refine le_trans (le_of_eq ?_) hsum
  rw [← Finset.sum_mul, Finset.sum_neg_distrib]

/-! ## 3. The lower bound for the summed linear word -/

/-- **The linear word against the window, lower bound.**  `All.linWord_le` at the environment
with the reversed `χ̂` (which reverses every `𝒞_k` and leaves `Σ_k𝒞_k²` unchanged). -/
theorem linWord_lower {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (ρ Cn M : ℝ)
    (hCn0 : 0 ≤ Cn) (hCn16 : Cn ≤ 16)
    (hCn : ∀ g : F.H, F.bp ((∑ k : Mode, F.nOp k) g) g ≤ Cn * F.bp (T.N g) g)
    (hM : 0 ≤ M) (f : F.H) (hf : T.NWindow M f) :
    -(8 * Real.sqrt (∑ k : Mode, (cCoefFar E ρ k) ^ 2) * Real.sqrt M * F.normSq f)
      ≤ ∑ k : Mode, (1 / 2 : ℝ) * cCoefFar E ρ k * F.qw f (pairLin F k) := by
  set G : Q3Env Mode := { E with hatChi := fun k => -E.hatChi k } with hG
  have hcoef : ∀ k : Mode, cCoefFar G ρ k = -cCoefFar E ρ k := by
    intro k
    have h1 : G.mu = E.mu := by simp [hG]
    have h2 : G.W1 0 = E.W1 0 := by simp [hG]
    have h3 : G.hatChi k = -E.hatChi k := by simp [hG]
    have h4 : (KzEnvAt G ρ).z = (KzEnvAt E ρ).z := by simp [hG, KzEnvAt]
    rw [cCoefFar, cCoefFar, h1, h2, h3, h4]
    ring
  have hsq : (∑ k : Mode, (cCoefFar G ρ k) ^ 2) = ∑ k : Mode, (cCoefFar E ρ k) ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcoef k, neg_sq]
  have h := linWord_le F T G ρ Cn M hCn0 hCn16 hCn hM f hf
  rw [hsq] at h
  have hneg : -(∑ k : Mode, (1 / 2 : ℝ) * cCoefFar E ρ k * F.qw f (pairLin F k))
      = ∑ k : Mode, (1 / 2 : ℝ) * cCoefFar G ρ k * F.qw f (pairLin F k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcoef k]
    ring
  linarith [h, hneg]

/-! ## 4. The environment's `𝒞`-sum, bounded -/

/-- **`√(Σ_k𝒞_k²)` against the parameters.**  At `E' = farEnv E v μ ρ` the coefficient is
`𝒞_k = (ρ−μ)Ŵ₁(0)χ̂_k√(ρℓ³)`, and `Σ_kχ̂_k² ≤ 1 + Σ_{k≠0}χ̂_k² ≤ 101`, so

  `8·√(Σ_k𝒞_k²)·√𝓜 ≤ 128π√101·|ρ−μ|·a·√(ρℓ³)·√𝓜`  (the left side of `farLinArith`). -/
theorem cCoefFar_sqrt_sum_le {v : E3 → ℝ} {μ ρ : ℝ} (D : KzDatum)
    (hav : 0 < a v) (hρ : 0 ≤ ρ) (hmuE : D.E.mu = μ)
    (hellpos : 0 < D.E.ell)
    (hW1 : ∀ k : D.Mode, |D.E.W1 k| ≤ 16 * Real.pi * a v)
    (hchi : ∑ k ∈ Work.BoseB7.excited D.Mode, (D.E.hatChi k) ^ 2 ≤ 100)
    (hchi0 : |D.E.hatChi (0 : D.Mode)| ≤ 1) :
    8 * Real.sqrt (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2) * Real.sqrt D.E.bigM
      ≤ 128 * Real.pi * Real.sqrt 101 * |ρ - μ| * a v * Real.sqrt (ρ * D.E.ell ^ 3)
          * Real.sqrt D.E.bigM := by
  have hcoef : ∀ k : D.Mode,
      cCoefFar (farEnv D.E v μ ρ) ρ k
        = (ρ - μ) * D.E.W1 0 * D.E.hatChi k * Real.sqrt (ρ * D.E.ell ^ 3) := by
    intro k
    simp only [cCoefFar, farEnv, KzEnvAt]
    rw [hmuE]
  have hX : 0 ≤ ρ * D.E.ell ^ 3 := mul_nonneg hρ (pow_nonneg (le_of_lt hellpos) 3)
  have hsumsq : (∑ k : D.Mode, (D.E.hatChi k) ^ 2) ≤ 101 := by
    have hsplit : (∑ k : D.Mode, (D.E.hatChi k) ^ 2)
        = (D.E.hatChi (0 : D.Mode)) ^ 2
          + ∑ k ∈ Work.BoseB7.excited D.Mode, (D.E.hatChi k) ^ 2 := by
      have hh := (Finset.add_sum_erase (Finset.univ : Finset D.Mode)
        (fun k => (D.E.hatChi k) ^ 2) (a := (0 : D.Mode)) (Finset.mem_univ 0)).symm
      simpa only [Work.BoseB7.excited] using hh
    have h0 : (D.E.hatChi (0 : D.Mode)) ^ 2 ≤ 1 := by
      have h1 := abs_le.mp hchi0
      nlinarith [h1.1, h1.2]
    rw [hsplit]
    linarith
  have hsumC : (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2)
      = ((ρ - μ) * D.E.W1 0) ^ 2 * (ρ * D.E.ell ^ 3)
          * (∑ k : D.Mode, (D.E.hatChi k) ^ 2) := by
    have hterm : ∀ k : D.Mode,
        ((ρ - μ) * D.E.W1 0 * D.E.hatChi k * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2
          = ((ρ - μ) * D.E.W1 0) ^ 2 * (ρ * D.E.ell ^ 3) * (D.E.hatChi k) ^ 2 := by
      intro k
      simp only [mul_pow, Real.sq_sqrt hX]
      ring
    rw [Finset.sum_congr rfl (fun k _ => by rw [hcoef k, hterm k]), ← Finset.mul_sum]
    try ring
  have hSle : (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2)
      ≤ ((|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2 * 101) := by
    rw [hsumC]
    have hW : (D.E.W1 0) ^ 2 ≤ (16 * Real.pi * a v) ^ 2 := by
      have h := hW1 0
      have h2 := abs_le.mp h
      nlinarith [h2.1, h2.2, sq_abs (D.E.W1 0), Real.pi_pos]
    have hsq : ((ρ - μ) * D.E.W1 0) ^ 2 ≤ (|ρ - μ| * (16 * Real.pi * a v)) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs (ρ - μ)]
      exact mul_le_mul_of_nonneg_left hW (sq_nonneg _)
    have hkey : ((ρ - μ) * D.E.W1 0) ^ 2 * (ρ * D.E.ell ^ 3) * (∑ k, (D.E.hatChi k) ^ 2)
        ≤ (|ρ - μ| * (16 * Real.pi * a v)) ^ 2 * (ρ * D.E.ell ^ 3) * 101 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hsq hX) hsumsq
        (Finset.sum_nonneg fun k _ => sq_nonneg _) (by positivity)
    calc ((ρ - μ) * D.E.W1 0) ^ 2 * (ρ * D.E.ell ^ 3) * (∑ k, (D.E.hatChi k) ^ 2)
        ≤ (|ρ - μ| * (16 * Real.pi * a v)) ^ 2 * (ρ * D.E.ell ^ 3) * 101 := hkey
      _ = (|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2 * 101 := by
          have h2 : (|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2
              = |ρ - μ| ^ 2 * (16 * Real.pi * a v) ^ 2 * (ρ * D.E.ell ^ 3) := by
            simp only [mul_pow, Real.sq_sqrt hX]
            try ring
          rw [h2]
          ring
  have hX0 : 0 ≤ |ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3) := by positivity
  have hY0 : 0 ≤ |ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)
      * Real.sqrt 101 := mul_nonneg hX0 (Real.sqrt_nonneg _)
  have hsleq : Real.sqrt (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2)
      ≤ |ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3) * Real.sqrt 101 := by
    have heq : ((|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2 * 101)
        = (|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)
            * Real.sqrt 101) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 101)]
      try ring
    calc Real.sqrt (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2)
        ≤ Real.sqrt ((|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2
            * 101) := Real.sqrt_le_sqrt hSle
      _ = |ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3) * Real.sqrt 101 := by
          rw [heq, Real.sqrt_sq hY0]
  calc 8 * Real.sqrt (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2) * Real.sqrt D.E.bigM
      ≤ 8 * (|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3) * Real.sqrt 101)
          * Real.sqrt D.E.bigM :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsleq (by norm_num))
          (Real.sqrt_nonneg _)
    _ = 128 * Real.pi * Real.sqrt 101 * |ρ - μ| * a v * Real.sqrt (ρ * D.E.ell ^ 3)
          * Real.sqrt D.E.bigM := by ring

/-! ## 5. The single label `0` of the zero-point sum -/

/-- **The `k = 0` zero point.**  `𝒵_0 = 𝒜_0 − √(𝒜_0²−ℬ_0²) ≤ ℬ_0²/𝒜_0` with `ℬ_0 = ρŴ₁(0)`,
`|Ŵ₁(0)| ≤ 16πa` and `𝒜_0 ≥ ρε^{-1/2}a/2`, so `½𝒵_0 ≤ 256π²ρa·ε^{1/2} ≤ ErrRes/4` (the budget
carries `10^300(ρ+μ)a𝓜` with `𝓜 ≥ 1`). -/
theorem zp_zero_mode {v : E3 → ℝ} {h : ScatSol v} {μ ρ : ℝ} (D : KzDatum)
    (hav : 0 < a v) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hA : 0 < (KzEnvAt (farEnv D.E v μ ρ) ρ).A (0 : D.Mode))
    (hB : |(KzEnvAt (farEnv D.E v μ ρ) ρ).B (0 : D.Mode)|
        ≤ (KzEnvAt (farEnv D.E v μ ρ) ρ).A (0 : D.Mode))
    (hW10 : |D.E.W1 (0 : D.Mode)| ≤ 16 * Real.pi * a v)
    (hτ0 : 0 ≤ D.E.tau (0 : D.Mode))
    (hεle : epsFar v μ ρ ≤ 1 / 10 ^ 8)
    (hM1 : 1 ≤ bigMV v μ) :
    (1 / 2) * Work.BoseB6.bogZeroPoint ((KzEnvAt (farEnv D.E v μ ρ) ρ).A (0 : D.Mode))
        ((KzEnvAt (farEnv D.E v μ ρ) ρ).B (0 : D.Mode)) ≤ ErrRes v μ ρ / 4 := by
  have hεpos : 0 < epsFar v μ ρ := farEnvPos_eps_pos hμ hav hρ
  have hbig : (10 : ℝ) ^ 4 ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := farEnvPos_rpow_ge hεpos hεle
  have hεle1 : epsFar v μ ρ ≤ 1 := le_trans hεle (by norm_num)
  have h1ε : 0 ≤ 1 - epsFar v μ ρ := by linarith
  have h32 : 32 * Real.pi ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := by
    have h128 : 32 * Real.pi ≤ 128 := by nlinarith [Real.pi_lt_four]
    linarith
  have hAeq : (KzEnvAt (farEnv D.E v μ ρ) ρ).A (0 : D.Mode)
      = (1 - epsFar v μ ρ) * D.E.tau 0
        + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v + ρ * D.E.W1 0 := rfl
  have hBeq : (KzEnvAt (farEnv D.E v μ ρ) ρ).B (0 : D.Mode) = ρ * D.E.W1 0 := rfl
  have hDpos : 0 < ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v / 2 := by positivity
  -- `𝒜_0 ≥ ρε^{-1/2}a/2`
  have hAlow : ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v / 2
      ≤ (KzEnvAt (farEnv D.E v μ ρ) ρ).A (0 : D.Mode) := by
    have hWlo : -(ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v / 2) ≤ ρ * D.E.W1 0 := by
      have h3 : ρ * (-(16 * Real.pi * a v)) ≤ ρ * D.E.W1 0 :=
        mul_le_mul_of_nonneg_left (abs_le.mp hW10).1 hρ.le
      have hmono : ρ * (32 * Real.pi * a v)
          ≤ ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v := by
        have h2 : 32 * Real.pi * a v ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v := by
          nlinarith [h32, hav]
        nlinarith [h2, hρ.le]
      linarith
    have hnn : 0 ≤ (1 - epsFar v μ ρ) * D.E.tau 0 := mul_nonneg h1ε hτ0
    rw [hAeq]
    linarith
  have hB2 : ((KzEnvAt (farEnv D.E v μ ρ) ρ).B (0 : D.Mode)) ^ 2
      ≤ (ρ * (16 * Real.pi * a v)) ^ 2 := by
    rw [hBeq]
    rw [show (ρ * D.E.W1 0) ^ 2 = ρ ^ 2 * (D.E.W1 0) ^ 2 by ring]
    rw [show (ρ * (16 * Real.pi * a v)) ^ 2 = ρ ^ 2 * (16 * Real.pi * a v) ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left (Work.BoseB6.sq_le_sq_of_abs_le hW10) (sq_nonneg ρ)
  have hbog := Work.BoseB6.bogZeroPoint_le hA hB
  have hdiv : ((KzEnvAt (farEnv D.E v μ ρ) ρ).B (0 : D.Mode)) ^ 2
        / (KzEnvAt (farEnv D.E v μ ρ) ρ).A (0 : D.Mode)
      ≤ (ρ * (16 * Real.pi * a v)) ^ 2
          / (ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v / 2) :=
    div_le_div₀ (sq_nonneg _) hB2 hDpos hAlow
  -- the crude value of the `k = 0` term
  have hval : (ρ * (16 * Real.pi * a v)) ^ 2 / (ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v / 2)
      ≤ 512 * Real.pi ^ 2 * (ρ * a v) := by
    have hEq1 : (ρ * (16 * Real.pi * a v)) ^ 2
          / (ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v / 2)
        = 512 * Real.pi ^ 2 * (ρ * a v) / (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := by
      field_simp
      ring
    rw [hEq1]
    have hnum : 0 ≤ 512 * Real.pi ^ 2 * (ρ * a v) := by positivity
    calc 512 * Real.pi ^ 2 * (ρ * a v) / (epsFar v μ ρ) ^ (-(1 / 2 : ℝ))
        ≤ 512 * Real.pi ^ 2 * (ρ * a v) / (10 : ℝ) ^ 4 :=
          div_le_div_of_nonneg_left hnum (by norm_num) hbig
      _ ≤ 512 * Real.pi ^ 2 * (ρ * a v) := by
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (10 : ℝ) ^ 4)]
          calc 512 * Real.pi ^ 2 * (ρ * a v)
              = 512 * Real.pi ^ 2 * (ρ * a v) * 1 := by ring
            _ ≤ 512 * Real.pi ^ 2 * (ρ * a v) * (10 : ℝ) ^ 4 :=
                mul_le_mul_of_nonneg_left (by norm_num) hnum
  have h267 : 256 * Real.pi ^ 2 * (ρ * a v) ≤ ErrRes v μ ρ / 4 := by
    have hρa : 0 ≤ ρ * a v := mul_nonneg hρ.le hav.le
    have hErr : (10 : ℝ) ^ 300 * ((ρ + μ) * a v * bigMV v μ) ≤ ErrRes v μ ρ := by
      rw [ErrRes]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ ρ + μ by linarith) (3 / 2))
          hav.le) (Real.sqrt_nonneg _))
    have hbig' : ρ * a v ≤ (ρ + μ) * a v * bigMV v μ := by
      have h1 : ρ * a v ≤ (ρ + μ) * a v := by nlinarith [hμ, hρ.le, hav]
      have h2 : (ρ + μ) * a v ≤ (ρ + μ) * a v * bigMV v μ := by
        have h3 := mul_le_mul_of_nonneg_left hM1 (by positivity : (0 : ℝ) ≤ (ρ + μ) * a v)
        simpa using h3
      linarith
    have hnum : 256 * Real.pi ^ 2 ≤ (10 : ℝ) ^ 300 / 4 := by
      have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
      have h3 : (256 : ℝ) * 16 ≤ (10 : ℝ) ^ 10 / 4 := by norm_num
      have h4 : 256 * Real.pi ^ 2 ≤ (10 : ℝ) ^ 10 / 4 := by nlinarith [hpi2, h3]
      have h5 : (10 : ℝ) ^ 10 / 4 ≤ (10 : ℝ) ^ 300 / 4 :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by norm_num)) (by norm_num)
      exact le_trans h4 h5
    have hfac : (0 : ℝ) ≤ (ρ + μ) * a v * bigMV v μ := by
      have h1 : (0 : ℝ) ≤ (ρ + μ) * a v := mul_nonneg (by linarith) hav.le
      have h2 : (0 : ℝ) ≤ bigMV v μ := by linarith
      exact mul_nonneg h1 h2
    calc 256 * Real.pi ^ 2 * (ρ * a v)
        ≤ 256 * Real.pi ^ 2 * ((ρ + μ) * a v * bigMV v μ) :=
          mul_le_mul_of_nonneg_left hbig' (show (0 : ℝ) ≤ 256 * Real.pi ^ 2 by positivity)
      _ ≤ (10 : ℝ) ^ 300 / 4 * ((ρ + μ) * a v * bigMV v μ) :=
          mul_le_mul_of_nonneg_right hnum hfac
      _ = (10 : ℝ) ^ 300 * ((ρ + μ) * a v * bigMV v μ) / 4 := by ring
      _ ≤ ErrRes v μ ρ / 4 := div_le_div_of_nonneg_right hErr (by norm_num)
  have h256 : Work.BoseB6.bogZeroPoint ((KzEnvAt (farEnv D.E v μ ρ) ρ).A (0 : D.Mode))
        ((KzEnvAt (farEnv D.E v μ ρ) ρ).B (0 : D.Mode)) ≤ 512 * Real.pi ^ 2 * (ρ * a v) :=
    le_trans (le_trans hbog hdiv) hval
  have hhalf : (1 / 2) * Work.BoseB6.bogZeroPoint ((KzEnvAt (farEnv D.E v μ ρ) ρ).A (0 : D.Mode))
        ((KzEnvAt (farEnv D.E v μ ρ) ρ).B (0 : D.Mode))
      ≤ 256 * Real.pi ^ 2 * (ρ * a v) := by
    nlinarith [h256]
  exact le_trans hhalf h267

/-! ## 6. The `τ'`-weighted row at the honest family -/

/-- **The row comparison.**  At the honest family the pins give
`Ŵ₁(k) = ζ_Λ·chat(W1fun)(kmomLab ℓ N k)` with `|ζ_Λ| ≤ 1` and `τ_k = tauSm … (kmomLab ℓ N k)`,
so the `τ'`-weighted sum of `Ŵ₁(k)²` is dominated by the row `hτ`. -/
theorem W1row_le {v : E3 → ℝ} (h : ScatSol v) (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ)
    {μ ρ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) (hρ : 0 < ρ) (hℓpos : 0 < ell v μ)
    (hεle : epsFar v μ ρ ≤ 1 / 10 ^ 8)
    (hview : (HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hτ : FarTauRowFS v h μ ρ (HM μ).N) :
    (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.W1 k) ^ 2
          / ((1 - epsFar v μ ρ) * (HonestBoxFam v h fc fu HM μ).E.tau k
              + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v))
      ≤ (1 + 100 * Real.sqrt (epsFar v μ ρ))
          * (2 * (((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
            * ∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2))) := by
  classical
  have hvw := hview
  unfold KzDatum.viewFSAll RViewFSAll at hview
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htauE, -, -, hW1pin, -, -, -, -, -, -, -, -⟩ := hview
  obtain ⟨fu', Λ, -, hW1eq⟩ := hW1pin
  have hellH : ellH v μ = ell v μ := by
    rw [ellH, ell]
    exact if_pos hℓpos
  have hkm : ∀ k : Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).F.kmom k = kmomLab (ell v μ) (HM μ).N k := by
    intro k
    show kmomLab (ellH v μ) (HM μ).N k = kmomLab (ell v μ) (HM μ).N k
    rw [hellH]
  have hτpin : ∀ k : Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).E.tau k
        = tauSm (paramsAt μ (a v)).eT (paramsAt μ (a v)).s (paramsAt μ (a v)).d (ell v μ)
            (kmomLab (ell v μ) (HM μ).N k) := by
    intro k
    simp only [htauE]
    rw [hkm k]
  have hW1pin' : ∀ k : Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).E.W1 k
        = uvCut fu' Λ (kmomLab (ell v μ) (HM μ).N k)
          * chat (W1fun v h (ell v μ)) (kmomLab (ell v μ) (HM μ).N k) := by
    intro k
    simp only [hW1eq]
    rw [hkm k]
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) hτ
  have hεpos : 0 < epsFar v μ ρ := farEnvPos_eps_pos hμ hav hρ
  have hden : 0 < (1 - epsFar v μ ρ) * tauSm (paramsAt μ (a v)).eT (paramsAt μ (a v)).s
        (paramsAt μ (a v)).d (ell v μ) (kmomLab (ell v μ) (HM μ).N k)
      + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v := by
    have hτnn : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.tau k :=
      farEnvPos_tau_nonneg _ hvw k
    have h1ε : 0 ≤ 1 - epsFar v μ ρ := by
      linarith [le_trans hεle (by norm_num : (1 : ℝ) / 10 ^ 8 ≤ 1)]
    rw [← hτpin k]
    have h2 : 0 < ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v := by positivity
    nlinarith [mul_nonneg h1ε hτnn]
  have hsq : ((HonestBoxFam v h fc fu HM μ).E.W1 k) ^ 2
      ≤ (chat (W1fun v h (ell v μ)) (kmomLab (ell v μ) (HM μ).N k)) ^ 2 := by
    rw [hW1pin' k, mul_pow]
    refine mul_le_of_le_one_left (sq_nonneg _) ?_
    simpa using Work.BoseB6.sq_le_sq_of_abs_le (abs_uvCut_le_one fu' Λ
      (kmomLab (ell v μ) (HM μ).N k))
  rw [hW1pin' k] at hsq
  rw [hW1pin' k, hτpin k]
  exact div_le_div_of_nonneg_right hsq hden.le

/-! ## 7. The full zero-point sum -/

/-- **The zero-point slot.**  `Σ_k½𝒵_k ≤ ½ρ²ℓ³C₀Mcont + ErrRes/4` at the `ε`-split environment,
where `C₀ = (1+64√ε)(1+100√ε)`: the sum over the excited modes is `All.farSlotSharp` composed
with the row, and the label `0` is `zp_zero_mode`. -/
theorem zeroPointSum_le {v : E3 → ℝ} (h : ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < a v) (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ))) (hAdm : Adm v ε₀ μ)
    (hview : (HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    (hW1 : ∀ k : Lab (HM μ).N, |(HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * a v)
    (hchi : ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 ≤ 100)
    (ρ : ℝ) (hρ : 0 < ρ) (hfar : FarCondFS v μ ρ)
    (hτ : FarTauRowFS v h μ ρ (HM μ).N) :
    (∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
        ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k)
        ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k))
      ≤ (1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
          * ((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ))
            * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
                (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
        + ErrRes v μ ρ / 4 := by
  classical
  have hμ : 0 < μ := hAdm.1
  have hℓpos : 0 < ell v μ := ell_pos_of_le hR hRℓ
  have hεle : epsFar v μ ρ ≤ 1 / 10 ^ 8 :=
    FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav hρ.le hfar
  have hvw := hview
  obtain ⟨hA, hB, -, hAe, hBe, -, hccr⟩ :=
    FarResidBaux.farEnvSideB (v := v) (D := HonestBoxFam v h fc fu HM μ) hεle hav hμ hρ hview hW1
  unfold KzDatum.viewFSAll RViewFSAll at hvw
  obtain ⟨hFSP, -, -, -, hbigMpin, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hvw
  have hM1 : 1 ≤ (HonestBoxFam v h fc fu HM μ).E.bigM := (Classical.choice hFSP).one_le_bigM
  have hM1' : 1 ≤ bigMV v μ := by
    rw [hbigMpin] at hM1
    exact hM1
  have hk0 := zp_zero_mode (v := v) (h := h) (μ := μ) (ρ := ρ)
    (HonestBoxFam v h fc fu HM μ) hav hμ hρ (hA 0) (hB 0) (hW1 0)
    (farEnvPos_tau_nonneg _ hview 0) hεle hM1'
  have hsharp := farSlotSharp (h := h) hv hv1 hvrad hR hv_supp hav fc fu HM hε₀ hAdm hview hRℓ hW1
    ρ hρ.le hfar
  have hrow := W1row_le (h := h) fc fu HM hav hμ hρ hℓpos hεle hview hτ
  have htoMass : (ρ ^ 2 / 4) * (1 + 64 * Real.sqrt (epsFar v μ ρ))
      * (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
          ((HonestBoxFam v h fc fu HM μ).E.W1 k) ^ 2
            / ((farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ).tau k))
      ≤ (ρ ^ 2 / 4) * (1 + 64 * Real.sqrt (epsFar v μ ρ))
          * ((1 + 100 * Real.sqrt (epsFar v μ ρ))
            * (2 * (((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
              * ∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)))) :=
    mul_le_mul_of_nonneg_left hrow (by positivity)
  have hmain : (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
          ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k)
          ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k))
      ≤ (ρ ^ 2 / 4) * (1 + 64 * Real.sqrt (epsFar v μ ρ))
          * ((1 + 100 * Real.sqrt (epsFar v μ ρ))
            * (2 * (((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
              * ∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)))) :=
    le_trans hsharp htoMass
  have hsplit : (∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
        ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k)
        ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k))
      = (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
          (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
            ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k)
            ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k))
        + (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
            ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A 0)
            ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B 0) := by
    rw [Work.BoseB7.excited]
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Lab (HM μ).N))).symm
  rw [hsplit]
  have hEq : (ρ ^ 2 / 4) * (1 + 64 * Real.sqrt (epsFar v μ ρ))
        * ((1 + 100 * Real.sqrt (epsFar v μ ρ))
          * (2 * (((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
            * ∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2))))
      = (1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
          * ((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ))
            * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
                (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2))) := by ring
  linarith [hmain, hk0, hEq]

/-! ## 8. The target -/

theorem farZPWin {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ))) (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hreg : 100 * R ≤ Work.BoseFixR.ell v μ)
    (hW1 : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * BoseGases.a v)
    (hchi : ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 ≤ 100)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hfar : Work.BoseBoxFock.FarCondFS v μ ρ)
    (hτ : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
            (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k)) ^ 2
          / ((1 - Work.BoseFixR.All.epsFar v μ ρ)
                * Work.BoseBoxFock.tauSm (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                    (Work.BoseFixR.ell v μ)
                    (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k)
              + ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v))
      ≤ (1 + 100 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
          * (2 * (((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
            * ∫ q : EuclideanSpace ℝ (Fin 3),
                (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
                  / (2 * ‖q‖ ^ 2))))
    (f : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H)
    (hf : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f) :
    -((1 / 2) * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3
          * ((1 + 64 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
              * (1 + 100 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
              * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
                  (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
                    / (2 * ‖q‖ ^ 2)))
        + Work.BoseFixR.ErrRes v μ ρ / 2)
        * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
          (Work.BoseBoxFock.KzBogFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
            (Work.BoseFixR.All.farEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              v μ ρ) ρ) := by
  classical
  have hμ : 0 < μ := hAdm.1
  have hℓpos : 0 < ell v μ := ell_pos_of_le hR hRℓ
  have hεle : epsFar v μ ρ ≤ 1 / 10 ^ 8 := FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav hρ hfar
  have hns : 0 ≤ (HonestBoxFam v h fc fu HM μ).F.normSq f :=
    (HonestBoxFam v h fc fu HM μ).F.normSq_nonneg f
  rcases eq_or_lt_of_le hρ with hρ0 | hρpos
  · -- ## vanishing density
    have hρzero : ρ = 0 := hρ0.symm
    have hτ0 : ∀ k : Lab (HM μ).N, 0 ≤ (farEnv (HonestBoxFam v h fc fu HM μ).E v μ 0).tau k := by
      intro k
      have h1 : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.tau k := farEnvPos_tau_nonneg _ hview k
      have h2 : 0 ≤ 1 - epsFar v μ 0 := by
        have h3 := FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav (le_refl 0)
          (by rw [← hρzero]; exact hfar)
        linarith
      simp only [farEnv]
      nlinarith [h1, h2]
    have hq : 0 ≤ (HonestBoxFam v h fc fu HM μ).F.qw f
        (KzBogFS (HonestBoxFam v h fc fu HM μ).F
          (farEnv (HonestBoxFam v h fc fu HM μ).E v μ 0) 0) :=
      qw_KzBogFS_rho0_nonneg' (HonestBoxFam v h fc fu HM μ).F
        (farEnv (HonestBoxFam v h fc fu HM μ).E v μ 0) f hτ0
    rw [hρzero]
    rw [show (1 / 2) * (0 : ℝ) ^ 2 * (ell v μ) ^ 3
          * ((1 + 64 * Real.sqrt (epsFar v μ 0)) * (1 + 100 * Real.sqrt (epsFar v μ 0))
            * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
                (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2))) = 0 from by ring]
    rw [zero_add]
    have hErr : 0 ≤ ErrRes v μ 0 := ErrRes_nonneg hμ hav (le_refl 0) hℓpos.le
    have h1 : -(ErrRes v μ 0 / 2) * (HonestBoxFam v h fc fu HM μ).F.normSq f ≤ 0 := by
      nlinarith [hErr, hns]
    linarith [hq, h1]
  · -- ## positive density
    have hvw := hview
    unfold KzDatum.viewFSAll RViewFSAll at hview
    obtain ⟨hFSP, hmuE, haSc, hellE, hbigME, hb, hd, hs, heT, hM, hg0, htauE, hAenv, hBenv,
      hW1pin, hW1o, hW1o0, hchiE, hchiSqE, hfL, hNH, hBessel, hKK⟩ := hview
    have hbigM1 : 1 ≤ bigMV v μ := by
      have h := (Classical.choice hFSP).one_le_bigM
      rw [hbigME] at h
      exact h
    have hchi0 : |(HonestBoxFam v h fc fu HM μ).E.hatChi (0 : Lab (HM μ).N)| ≤ 1 := by
      obtain ⟨K₀, b₀, -, -, -, hker⟩ := hKK
      exact (hker μ (closeCondFS_self hμ hav)).hatChi_le 0
    have hposE : 0 < (HonestBoxFam v h fc fu HM μ).E.ell := by rw [hellE]; exact hℓpos
    obtain ⟨hA, hB, hAB, hAe, hBe, hCe, hccr⟩ :=
      FarResidBaux.farEnvSideB (v := v) (D := HonestBoxFam v h fc fu HM μ)
        hεle hav hμ hρpos hvw hW1
    -- the decomposition of `KzBogFS`
    have hdecomp : (HonestBoxFam v h fc fu HM μ).F.qw f
          (KzBogFS (HonestBoxFam v h fc fu HM μ).F
            (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ)
        = (∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
            (pairQuad (HonestBoxFam v h fc fu HM μ).F
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k))
          + (∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * (cCoefFar
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
              * (HonestBoxFam v h fc fu HM μ).F.qw f
                  (pairLin (HonestBoxFam v h fc fu HM μ).F k)) := by
      have hsum1 : (∑ k : (HonestBoxFam v h fc fu HM μ).Mode,
            (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
              (pairOpFar (HonestBoxFam v h fc fu HM μ).F
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k))
          = ∑ k : (HonestBoxFam v h fc fu HM μ).Mode,
              (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
                (pairQuad (HonestBoxFam v h fc fu HM μ).F
                    (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k
                  + (cCoefFar (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) •
                      pairLin (HonestBoxFam v h fc fu HM μ).F k) :=
        Finset.sum_congr rfl (fun k _ => by rfl)
      have hstep : ∀ k : (HonestBoxFam v h fc fu HM μ).Mode,
          (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
              (pairQuad (HonestBoxFam v h fc fu HM μ).F
                  (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k
                + (cCoefFar (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) •
                    pairLin (HonestBoxFam v h fc fu HM μ).F k)
            = (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
                (pairQuad (HonestBoxFam v h fc fu HM μ).F
                  (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
              + (1 / 2 : ℝ) * (cCoefFar
                    (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                  * (HonestBoxFam v h fc fu HM μ).F.qw f
                      (pairLin (HonestBoxFam v h fc fu HM μ).F k) := by
        intro k
        rw [FockData.qw_add, FockData.qw_smul]
        ring
      have hsumstep : (∑ k : (HonestBoxFam v h fc fu HM μ).Mode,
              (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
                (pairQuad (HonestBoxFam v h fc fu HM μ).F
                    (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k
                  + (cCoefFar (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) •
                      pairLin (HonestBoxFam v h fc fu HM μ).F k))
          = ∑ k : (HonestBoxFam v h fc fu HM μ).Mode,
              ((1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
                  (pairQuad (HonestBoxFam v h fc fu HM μ).F
                    (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                + (1 / 2 : ℝ) * (cCoefFar
                      (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                    * (HonestBoxFam v h fc fu HM μ).F.qw f
                        (pairLin (HonestBoxFam v h fc fu HM μ).F k)) :=
        Finset.sum_congr rfl (fun k _ => hstep k)
      have hcomb : (∑ k : (HonestBoxFam v h fc fu HM μ).Mode,
              ((1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
                  (pairQuad (HonestBoxFam v h fc fu HM μ).F
                    (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                + (1 / 2 : ℝ) * (cCoefFar
                      (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                    * (HonestBoxFam v h fc fu HM μ).F.qw f
                        (pairLin (HonestBoxFam v h fc fu HM μ).F k)))
          = (∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
              (pairQuad (HonestBoxFam v h fc fu HM μ).F
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k))
            + (∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * (cCoefFar
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                * (HonestBoxFam v h fc fu HM μ).F.qw f
                    (pairLin (HonestBoxFam v h fc fu HM μ).F k)) := by
        rw [Finset.sum_add_distrib]
        rfl
      have hfirst : (HonestBoxFam v h fc fu HM μ).F.qw f
            (KzBogFS (HonestBoxFam v h fc fu HM μ).F
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ)
          = ∑ k : (HonestBoxFam v h fc fu HM μ).Mode,
              (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
                (pairOpFar (HonestBoxFam v h fc fu HM μ).F
                  (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) := by
        rw [KzBogFS_eq_sum_pairOpFar, qw_sum_smul_zp]
      exact hfirst.trans (hsum1.trans (hsumstep.trans hcomb))
    -- the quadratic half
    have hzp := zeroPointSum_le (h := h) hv hv1 hvrad hR hv_supp hav fc fu HM hε₀ hAdm hvw hRℓ
      hW1 hchi ρ hρpos hfar hτ
    have hquad := sum_pairQuad_ground (HonestBoxFam v h fc fu HM μ).F
      (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ hA hB hAB hAe hBe hccr f
    have hquad' : -((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
          * ((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ))
            * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
                (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
          + ErrRes v μ ρ / 4)
        * (HonestBoxFam v h fc fu HM μ).F.normSq f
        ≤ ∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
            (pairQuad (HonestBoxFam v h fc fu HM μ).F
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) := by
      have h1 : (∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
            ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k)
            ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k))
            * (HonestBoxFam v h fc fu HM μ).F.normSq f
          ≤ ((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
              * ((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ))
                * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
                    (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
              + ErrRes v μ ρ / 4) * (HonestBoxFam v h fc fu HM μ).F.normSq f :=
        mul_le_mul_of_nonneg_right hzp hns
      have h2 : -(((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
              * ((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ))
                * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
                    (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
              + ErrRes v μ ρ / 4) * (HonestBoxFam v h fc fu HM μ).F.normSq f)
          ≤ -((∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
                ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k)
                ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k))
              * (HonestBoxFam v h fc fu HM μ).F.normSq f) := neg_le_neg h1
      have h3 : -(∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
                ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k)
                ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k))
              * (HonestBoxFam v h fc fu HM μ).F.normSq f
          = -((∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
                ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k)
                ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k))
              * (HonestBoxFam v h fc fu HM μ).F.normSq f) := by ring
      calc -((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
              * ((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ))
                * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
                    (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
              + ErrRes v μ ρ / 4)
            * (HonestBoxFam v h fc fu HM μ).F.normSq f
          = -(((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
              * ((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ))
                * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
                    (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
              + ErrRes v μ ρ / 4) * (HonestBoxFam v h fc fu HM μ).F.normSq f) := by ring
        _ ≤ -((∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
                ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).A k)
                ((KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ).B k))
              * (HonestBoxFam v h fc fu HM μ).F.normSq f) := h2
        _ ≤ ∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
              (pairQuad (HonestBoxFam v h fc fu HM μ).F
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) := by
              rw [← h3]; exact hquad
    -- the linear half
    obtain ⟨Cn, hCn0, hCn16, hCn⟩ := hBessel
    have hMnn : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.bigM := le_trans zero_le_one hbigM1
    have hlin := linWord_lower (HonestBoxFam v h fc fu HM μ).F
      (HonestBoxFam v h fc fu HM μ).T (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ Cn
      (HonestBoxFam v h fc fu HM μ).E.bigM hCn0 hCn16 hCn hMnn f hf
    have harith : 8 * Real.sqrt (∑ k : Lab (HM μ).N, (cCoefFar
          (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) ^ 2)
        * Real.sqrt (HonestBoxFam v h fc fu HM μ).E.bigM ≤ ErrRes v μ ρ / 4 := by
      have h1 := cCoefFar_sqrt_sum_le (v := v) (μ := μ) (ρ := ρ)
        (HonestBoxFam v h fc fu HM μ) hav hρ hmuE hposE hW1 hchi hchi0
      rw [hellE, hbigME] at h1
      have h2 : 128 * Real.pi * Real.sqrt 101 * |ρ - μ| * a v * Real.sqrt (ρ * (ell v μ) ^ 3)
            * Real.sqrt (bigMV v μ)
          ≤ ErrRes v μ ρ / 4 := by
        have h3 := farLinArith (ρ := ρ) (μ := μ) (ℓ := ell v μ) (M := bigMV v μ) (a := a v)
          hρ hμ hℓpos.le (le_trans zero_le_one hbigM1) hav
        have h4 : ErrRes v μ ρ / 4
            = 10 ^ 300 / 4 * ((ρ + μ) * a v * bigMV v μ
                + (ρ + μ) ^ (3 / 2 : ℝ) * a v * Real.sqrt ((ell v μ) ^ 3 * bigMV v μ)) := by
          rw [ErrRes]; ring
        rw [h4]
        exact h3
      exact le_trans h1 h2
    have hlin' : -(ErrRes v μ ρ / 4) * (HonestBoxFam v h fc fu HM μ).F.normSq f
        ≤ ∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * (cCoefFar
            (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
            * (HonestBoxFam v h fc fu HM μ).F.qw f
                (pairLin (HonestBoxFam v h fc fu HM μ).F k) := by
      have h5 := mul_le_mul_of_nonneg_right harith hns
      have h6 : -(ErrRes v μ ρ / 4 * (HonestBoxFam v h fc fu HM μ).F.normSq f)
          ≤ -(8 * Real.sqrt (∑ k : Lab (HM μ).N, (cCoefFar
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) ^ 2)
              * Real.sqrt (HonestBoxFam v h fc fu HM μ).E.bigM
              * (HonestBoxFam v h fc fu HM μ).F.normSq f) := neg_le_neg h5
      calc -(ErrRes v μ ρ / 4) * (HonestBoxFam v h fc fu HM μ).F.normSq f
          = -(ErrRes v μ ρ / 4 * (HonestBoxFam v h fc fu HM μ).F.normSq f) := by ring
        _ ≤ -(8 * Real.sqrt (∑ k : Lab (HM μ).N, (cCoefFar
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) ^ 2)
              * Real.sqrt (HonestBoxFam v h fc fu HM μ).E.bigM
              * (HonestBoxFam v h fc fu HM μ).F.normSq f) := h6
        _ ≤ ∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * (cCoefFar
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
              * (HonestBoxFam v h fc fu HM μ).F.qw f
                  (pairLin (HonestBoxFam v h fc fu HM μ).F k) := hlin
    rw [hdecomp]
    have hfin : -((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
            * ((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ))
              * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
                  (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
          + ErrRes v μ ρ / 2)
        * (HonestBoxFam v h fc fu HM μ).F.normSq f
        = -((1 / 2) * ρ ^ 2 * (ell v μ) ^ 3
              * ((1 + 64 * Real.sqrt (epsFar v μ ρ)) * (1 + 100 * Real.sqrt (epsFar v μ ρ))
                * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
                    (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
            + ErrRes v μ ρ / 4)
          * (HonestBoxFam v h fc fu HM μ).F.normSq f
          + -(ErrRes v μ ρ / 4) * (HonestBoxFam v h fc fu HM μ).F.normSq f := by ring
    rw [hfin]
    exact add_le_add hquad' hlin'
end Work.BoseFixR.All
