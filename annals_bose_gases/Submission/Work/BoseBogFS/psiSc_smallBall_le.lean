import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.BoseBogFS.honestFsCutoffRows
import Submission.Work.BoseBogFS.origin_cell_excess_le
import Submission.Work.BoseBogFS.psiSc_bulk_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.psiSc_smallBall_le` — the small-ball row of `integral_cleanFun_le`

The target is the "small ball" row of the comparison `psiSc ↔ fsI1Integrand`: on the ball
`‖t‖ ≤ 4c₁` (where `c₁ = bogC1 v ρ μ = ½(K_ℓs)⁻¹√(ρ/(a v))` is the smaller of FS's two kinetic
cutoffs) the *difference* of the two integrands is bounded by an absolute constant, so that its
integral is `≤ C·c₁³ ≤ C·lhyEps` (the last step being `c₁ ≤ (K_ℓ s)⁻¹ ≤ lhyEps`).

## The two-point structure of the difference

Writing `gFun τ b r = (τ+b) − √((τ+b)²−b²) − b²/(2r²)` (FS's Bogoliubov bracket) and
`ψ(τ,b) = (τ+b) − √((τ+b)²−b²)`, the two integrands are

  `psiSc t = gFun τ_s b r`,  `fsI1Integrand t = gFun τ̃ Kβ r`   (`r = ‖t‖`),

with `b = betaSc v h ρ μ t` the honest pairing coefficient, `Kβ = (bogKernel v R ρ μ).β r` the
model one, and `τ_s = tauScRad`, `τ̃ = fsTau` the two kinetic symbols.  Since
`gFun τ b r − gFun τ' b' r = [ψ(τ,b) − ψ(τ',b')] + (b'² − b²)/(2r²)`, and the *only* property of
`ψ` needed is

  **`|ψ(τ,b)| ≤ |b|` for `τ ≥ 0`**  (`psiSc_abs_bracket_le_abs`),

the difference is bounded by `|b| + |b'| + (|b|+|b'|)|b−b'|/(2r²)`.  On the ball

* `|b| ≤ 8π + δ + 3η r ≤ 100` (`betaSc_close`, `δ ≤ 8π`, `η r ≤ η·4c₁ ≤ 4c₁/T ≤ 4`),
* `|b'| ≤ (bogKernel v R ρ μ).B ≤ 100` (`hB` of `FsI1Regime`),

so `|b − b'| ≤ 200` and the difference is `≤ 200 + 20000/(2r²) ≤ 30000·(1 + ‖t‖⁻²)`.

## The integral

`∫_{‖t‖≤R₀} 30000(1 + ‖t‖⁻²) = 30000(4πR₀³/3 + 4πR₀)` (polar coordinates,
`Work.BoseB6.integral_radial_closedBall_r3` and `setIntegral_inv_normSq_closedBall`), and with
`R₀ = 4c₁ ≤ 4` this is `≤ 30000·(304/3)π·c₁ ≤ 10⁸·c₁ ≤ 10⁸·lhyEps`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The algebraic core: the bracket is dominated by the pairing scale -/

/-- **`|(τ+b) − √((τ+b)²−b²)| ≤ |b|` for `τ ≥ 0`.**

If `(τ+b)² ≤ b²` the square root vanishes and the claim is `|τ+b| ≤ |b|`.  Otherwise the bracket
is `b²/((τ+b)+√((τ+b)²−b²))`; here `τ+b ≥ 0` (as `τ+b ≥ b` while `|τ+b| > |b|` forbids
`τ+b < -b ≤ b`), so the denominator is `≥ |b|` and the quotient is `≤ |b|`. -/
lemma psiSc_abs_bracket_le_abs (τ b : ℝ) (hτ : 0 ≤ τ) :
    |τ + b - Real.sqrt ((τ + b) ^ 2 - b ^ 2)| ≤ |b| := by
  rcases le_or_gt ((τ + b) ^ 2) (b ^ 2) with hle | hlt
  · rw [Real.sqrt_eq_zero_of_nonpos (by linarith : (τ + b) ^ 2 - b ^ 2 ≤ 0), sub_zero]
    exact sq_le_sq.mp hle
  · have hsq : 0 < (τ + b) ^ 2 - b ^ 2 := by linarith
    have hs2 : Real.sqrt ((τ + b) ^ 2 - b ^ 2) ^ 2 = (τ + b) ^ 2 - b ^ 2 := Real.sq_sqrt hsq.le
    have hs0 : 0 ≤ Real.sqrt ((τ + b) ^ 2 - b ^ 2) := Real.sqrt_nonneg _
    have hAabs : |b| < |τ + b| := sq_lt_sq.mp hlt
    have hA0 : 0 ≤ τ + b := by
      by_contra hc
      push Not at hc
      have h1 : |τ + b| = -(τ + b) := abs_of_neg hc
      rw [h1] at hAabs
      have h4 : -b ≤ |b| := neg_le_abs b
      linarith
    have hAb : |b| < τ + b := by
      rwa [abs_of_nonneg hA0] at hAabs
    have hsum : 0 < (τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2) := by
      have := abs_nonneg b; linarith
    have hkey : (τ + b) - Real.sqrt ((τ + b) ^ 2 - b ^ 2)
        = b ^ 2 / ((τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) := by
      rw [eq_div_iff (ne_of_gt hsum)]
      nlinarith [hs2]
    rw [hkey, abs_of_nonneg (div_nonneg (sq_nonneg b) hsum.le), div_le_iff₀ hsum]
    calc b ^ 2 = |b| * |b| := by rw [← sq_abs]; ring
      _ ≤ |b| * ((τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg b)

/-- **The two-point bound** for FS's bracket: if `0 ≤ τ, τ'`, `|b| ≤ Bb`, `|b'| ≤ Bb'` and
`|b − b'| ≤ Db`, then

  `gFun τ b r − gFun τ' b' r ≤ (Bb + Bb') + (Bb + Bb')Db/(2r²)`.

The `1/r²` singularities cancel: the difference is the increment of `ψ(τ,b) = τ+b − √((τ+b)²−b²)`
plus `(b'² − b²)/(2r²)`. -/
lemma psiSc_gFun_sub_le {τ τ' b b' r Bb Bb' Db : ℝ} (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ')
    (hb : |b| ≤ Bb) (hb' : |b'| ≤ Bb') (hbb : |b - b'| ≤ Db) :
    Work.BoseB6Est.gFun τ b r - Work.BoseB6Est.gFun τ' b' r
      ≤ (Bb + Bb') + (Bb + Bb') * Db / (2 * r ^ 2) := by
  have h1 : Work.BoseB6Est.gFun τ b r - Work.BoseB6Est.gFun τ' b' r
      = (τ + b - Real.sqrt ((τ + b) ^ 2 - b ^ 2))
        - (τ' + b' - Real.sqrt ((τ' + b') ^ 2 - b' ^ 2))
        + (b' ^ 2 - b ^ 2) / (2 * r ^ 2) := by
    simp only [Work.BoseB6Est.gFun]; ring
  rw [h1]
  have h2 : (τ + b - Real.sqrt ((τ + b) ^ 2 - b ^ 2)) ≤ |b| :=
    le_trans (le_abs_self _) (psiSc_abs_bracket_le_abs τ b hτ)
  have h3 : -(τ' + b' - Real.sqrt ((τ' + b') ^ 2 - b' ^ 2)) ≤ |b'| :=
    le_trans (neg_le_abs _) (psiSc_abs_bracket_le_abs τ' b' hτ')
  have h4 : (b' ^ 2 - b ^ 2) / (2 * r ^ 2) ≤ |b' ^ 2 - b ^ 2| / (2 * r ^ 2) :=
    div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
  have hDb : 0 ≤ Db := le_trans (abs_nonneg _) hbb
  have h5 : |b' ^ 2 - b ^ 2| ≤ Db * (Bb + Bb') := by
    have e : b' ^ 2 - b ^ 2 = (b' - b) * (b' + b) := by ring
    rw [e, abs_mul]
    refine le_trans (mul_le_mul_of_nonneg_left (abs_add_le b' b) (abs_nonneg _)) ?_
    exact mul_le_mul (by rwa [abs_sub_comm]) (by linarith [hb, hb']) (by positivity) hDb
  have h6 : (b' ^ 2 - b ^ 2) / (2 * r ^ 2) ≤ (Bb + Bb') * Db / (2 * r ^ 2) := by
    refine le_trans h4 ?_
    have h7 := div_le_div_of_nonneg_right h5 (by positivity : (0:ℝ) ≤ 2 * r ^ 2)
    calc |b' ^ 2 - b ^ 2| / (2 * r ^ 2) ≤ Db * (Bb + Bb') / (2 * r ^ 2) := h7
      _ = (Bb + Bb') * Db / (2 * r ^ 2) := by ring
  linarith [h2, h3, h6]

/-! ## 2. The volume of the ball, in the two forms needed -/

/-- `∫_{‖t‖ ≤ R} 1 = 4πR³/3` (polar coordinates, `Work.BoseB6.integral_radial_closedBall_r3`). -/
lemma psiSc_setIntegral_one_closedBall_r3 {R : ℝ} (hR : 0 ≤ R) :
    (∫ t in Metric.closedBall (0 : E3) R, (1 : ℝ)) = 4 * Real.pi * R ^ 3 / 3 := by
  rw [show (∫ t in Metric.closedBall (0 : E3) R, (1 : ℝ))
      = ∫ t in Metric.closedBall (0 : E3) R, (fun _ : ℝ => (1 : ℝ)) ‖t‖ from rfl]
  rw [Work.BoseB6.integral_radial_closedBall_r3 R (fun _ : ℝ => (1 : ℝ))]
  have h2 : (∫ r in Set.Ioc (0 : ℝ) R, r ^ 2 * (fun _ : ℝ => (1 : ℝ)) r) = R ^ 3 / 3 := by
    rw [← intervalIntegral.integral_of_le hR]
    simp only [mul_one]
    rw [integral_pow]
    norm_num
  rw [h2]
  ring

/-! ## 3. The target -/

theorem psiSc_smallBall_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ : ℝ},
      0 < R → 0 < _root_.BoseGases.a v → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      Work.BoseBogFS.Core v R μ ρ →
      Work.BoseB6Est.FsI1Regime (Work.BoseBogFS.bogKernel v R ρ μ)
        (_root_.BoseGases.a v) R ρ μ
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 →
      Work.BoseBogFS.chiTC * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1 / 2 →
      R / Work.BoseFixR.ell v μ ≤ Work.BoseBogFS.chiTR1 →
      MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBogFS.psiSc v h ρ μ t) →
      MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t) →
      (∫ t in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ 4 * Work.BoseBogFS.bogC1 v ρ μ},
         (Work.BoseBogFS.psiSc v h ρ μ t -
          Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t))
        ≤ C * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro v h R ρ μ hR hav hv hvrad hv_supp hcore hreg hrl hcond hchiTR1 hint1 hint2
  have hμ : 0 < μ := hreg.hμ
  have hρ0 : 0 < ρ := hreg.hρz
  have hℓ : 0 < Work.BoseFixR.ell v μ := Work.BoseFixR.ell_pos' v hμ hav
  have hP : 0 < ρ * _root_.BoseGases.a v := mul_pos hρ0 hav
  have hc1le : Work.BoseBogFS.bogC1 v ρ μ ≤ 1 := hreg.c1_le_one
  have hc1nn : 0 ≤ Work.BoseBogFS.bogC1 v ρ μ := by
    rw [Work.BoseBogFS.bogC1]
    apply inv_nonneg.mpr
    have h1 : (0 : ℝ) < 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s := by
      have := hreg.hs; linarith
    exact mul_nonneg (mul_nonneg h1.le hℓ.le) (Real.sqrt_nonneg _)
  have hη1 : Work.BoseBogFS.bogEta v R ρ ≤ 1 := le_trans (le_max_right _ _) hreg.eta_le_one
  have hηnn : 0 ≤ Work.BoseBogFS.bogEta v R ρ := Work.BoseBogFS.bogEta_nonneg v hR.le hρ0.le
  -- `δ ≤ 8π`
  have hδle : Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
      ≤ 8 * Real.pi := by
    rw [Work.BoseBogFS.bogDelta]
    have h1 := mul_le_mul_of_nonneg_left hcond (by positivity : (0:ℝ) ≤ 16 * Real.pi)
    nlinarith [h1]
  -- the pointwise bound on the ball
  have hpoint : ∀ t : E3, ‖t‖ ≤ 4 * Work.BoseBogFS.bogC1 v ρ μ →
      Work.BoseBogFS.psiSc v h ρ μ t -
          Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t
        ≤ 30000 * (1 + (‖t‖ ^ 2)⁻¹) := by
    intro t ht
    have hηr : Work.BoseBogFS.bogEta v R ρ * ‖t‖ ≤ 4 := by
      calc Work.BoseBogFS.bogEta v R ρ * ‖t‖
          ≤ Work.BoseBogFS.bogEta v R ρ * (4 * Work.BoseBogFS.bogC1 v ρ μ) :=
            mul_le_mul_of_nonneg_left ht hηnn
        _ ≤ 1 * (4 * Work.BoseBogFS.bogC1 v ρ μ) :=
            mul_le_mul_of_nonneg_right hη1 (by linarith [hreg.hc1])
        _ ≤ 4 := by linarith [hreg.c1_le_one]
    have hclose := Work.BoseBogFS.betaSc_close (v := v) (h := h) (R := R)
      (C := Work.BoseBogFS.chiTC) (r₁ := Work.BoseBogFS.chiTR1) (ρ := ρ) (μ := μ)
      hR hv hvrad hv_supp Work.BoseBogFS.chiTC_nonneg Work.BoseBogFS.chiTR1_pos hℓ
      (fun x hx => Work.BoseBogFS.chiT_bound x hx) hchiTR1 hcond hρ0 hav hrl t
    have hb100 : |Work.BoseBogFS.betaSc v h ρ μ t| ≤ 100 := by
      have hA : 0 ≤ 8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖ := by
        nlinarith [hηnn, norm_nonneg t, Real.pi_pos]
      have h1 : Work.BoseBogFS.betaSc v h ρ μ t
          ≤ 8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖
            + (Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
              + 2 * Work.BoseBogFS.bogEta v R ρ * ‖t‖) := by
        have := (abs_le.mp hclose).2; linarith
      have h2 : -(8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖)
          - (Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
              + 2 * Work.BoseBogFS.bogEta v R ρ * ‖t‖) ≤ Work.BoseBogFS.betaSc v h ρ μ t := by
        have := (abs_le.mp hclose).1; linarith
      rw [abs_le]
      constructor <;> nlinarith [h1, h2, hηr, hδle, Real.pi_lt_four]
    have hb'100 : |(Work.BoseBogFS.bogKernel v R ρ μ).β ‖t‖| ≤ 100 := by
      rw [abs_of_nonneg ((Work.BoseBogFS.bogKernel v R ρ μ).nonneg _)]
      linarith [(Work.BoseBogFS.bogKernel v R ρ μ).bound ‖t‖, hreg.hB]
    have hdiff : |Work.BoseBogFS.betaSc v h ρ μ t
        - (Work.BoseBogFS.bogKernel v R ρ μ).β ‖t‖| ≤ 200 := by
      have h1 : |Work.BoseBogFS.betaSc v h ρ μ t
            - (Work.BoseBogFS.bogKernel v R ρ μ).β ‖t‖|
          ≤ |Work.BoseBogFS.betaSc v h ρ μ t| + |(Work.BoseBogFS.bogKernel v R ρ μ).β ‖t‖| := by
        have := abs_add_le (Work.BoseBogFS.betaSc v h ρ μ t)
          (-(Work.BoseBogFS.bogKernel v R ρ μ).β ‖t‖)
        simpa [sub_eq_add_neg, abs_neg] using this
      linarith [hb100, hb'100]
    have hτnn : 0 ≤ Work.BoseBogFS.tauScRad v ρ μ ‖t‖ :=
      Work.BoseBogFS.tauScRad_nonneg v hP hreg.hε0 (by linarith [hreg.hε1]) ‖t‖
    have hτ'nn : 0 ≤ Work.BoseB6.fsTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) ‖t‖ :=
      Work.BoseB6Est.fsTau_nonneg hreg.hε0 (by linarith [hreg.hε1]) (norm_nonneg t)
    rw [Work.BoseBogFS.psiSc_eq_gFun, Work.BoseBogFS.fsI1Integrand_eq_gFun]
    have hkey := psiSc_gFun_sub_le (τ := Work.BoseBogFS.tauScRad v ρ μ ‖t‖)
      (τ' := Work.BoseB6.fsTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) ‖t‖)
      (b := Work.BoseBogFS.betaSc v h ρ μ t)
      (b' := (Work.BoseBogFS.bogKernel v R ρ μ).β ‖t‖)
      (r := ‖t‖) (Bb := 100) (Bb' := 100) (Db := 200)
      hτnn hτ'nn hb100 hb'100 hdiff
    have hrw : (100 + 100) * 200 / (2 * ‖t‖ ^ 2)
        = ((100 + 100) * 200 / 2) * (‖t‖ ^ 2)⁻¹ := by
      rw [div_eq_mul_inv, mul_inv]; ring
    rw [hrw] at hkey
    have hinvnn : 0 ≤ (‖t‖ ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg ‖t‖)
    nlinarith [hkey, hinvnn]
  -- the integral assembly
  have hR0nn : 0 ≤ 4 * Work.BoseBogFS.bogC1 v ρ μ := by linarith
  have hset : {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ 4 * Work.BoseBogFS.bogC1 v ρ μ}
      = Metric.closedBall (0 : E3) (4 * Work.BoseBogFS.bogC1 v ρ μ) := by
    ext t
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hset]
  have hIntL : IntegrableOn (fun t : E3 => Work.BoseBogFS.psiSc v h ρ μ t -
      Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t)
      (Metric.closedBall (0 : E3) (4 * Work.BoseBogFS.bogC1 v ρ μ)) :=
    (hint1.sub hint2).integrableOn
  have hIntR : IntegrableOn (fun t : E3 => 30000 * (1 + (‖t‖ ^ 2)⁻¹))
      (Metric.closedBall (0 : E3) (4 * Work.BoseBogFS.bogC1 v ρ μ)) :=
    ((MeasureTheory.integrableOn_const
        (MeasureTheory.measure_closedBall_lt_top (x := (0 : E3))
          (r := 4 * Work.BoseBogFS.bogC1 v ρ μ)).ne enorm_ne_top).add
      Work.BoseBogFS.integrableOn_inv_normSq_closedBall).const_mul 30000
  have hstep1 : (∫ t in Metric.closedBall (0 : E3) (4 * Work.BoseBogFS.bogC1 v ρ μ),
        (Work.BoseBogFS.psiSc v h ρ μ t -
          Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t))
      ≤ ∫ t in Metric.closedBall (0 : E3) (4 * Work.BoseBogFS.bogC1 v ρ μ),
          30000 * (1 + (‖t‖ ^ 2)⁻¹) := by
    refine MeasureTheory.setIntegral_mono_on hIntL hIntR measurableSet_closedBall ?_
    intro t ht
    exact hpoint t (by simpa [Metric.mem_closedBall, dist_eq_norm] using ht)
  have hval : (∫ t in Metric.closedBall (0 : E3) (4 * Work.BoseBogFS.bogC1 v ρ μ),
        30000 * (1 + (‖t‖ ^ 2)⁻¹))
      = 30000 * (4 * Real.pi * (4 * Work.BoseBogFS.bogC1 v ρ μ) ^ 3 / 3
          + 4 * Real.pi * (4 * Work.BoseBogFS.bogC1 v ρ μ)) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hA : Integrable (fun _ : E3 => (1 : ℝ))
        ((volume : Measure E3).restrict (Metric.closedBall (0 : E3)
          (4 * Work.BoseBogFS.bogC1 v ρ μ))) :=
      MeasureTheory.integrableOn_const
        (MeasureTheory.measure_closedBall_lt_top (x := (0 : E3))
          (r := 4 * Work.BoseBogFS.bogC1 v ρ μ)).ne enorm_ne_top
    have hB : Integrable (fun t : E3 => (‖t‖ ^ 2)⁻¹)
        ((volume : Measure E3).restrict (Metric.closedBall (0 : E3)
          (4 * Work.BoseBogFS.bogC1 v ρ μ))) :=
      Work.BoseBogFS.integrableOn_inv_normSq_closedBall
    rw [MeasureTheory.integral_add hA hB]
    rw [Work.BoseBogFS.psiSc_setIntegral_one_closedBall_r3 hR0nn,
      Work.BoseBogFS.setIntegral_inv_normSq_closedBall hR0nn]
  -- the arithmetic
  have hc1eps : Work.BoseBogFS.bogC1 v ρ μ
      ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
    have h1 : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹
        ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := hreg.hEpsKl
    have h2 : Work.BoseBogFS.bogC1 v ρ μ
        ≤ ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ := by
      rw [hreg.hc1val]
      have h3 : 0 ≤ ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ :=
        inv_nonneg.mpr (mul_pos hreg.hKl hreg.hs).le
      nlinarith [hreg.sqrt_mu_div_rhoz_le_two, h3, Real.sqrt_nonneg (μ / ρ)]
    linarith
  have hfinal : 30000 * (4 * Real.pi * (4 * Work.BoseBogFS.bogC1 v ρ μ) ^ 3 / 3
        + 4 * Real.pi * (4 * Work.BoseBogFS.bogC1 v ρ μ))
      ≤ 10 ^ 8 * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
    have hR0le : 4 * Work.BoseBogFS.bogC1 v ρ μ ≤ 4 := by linarith [hreg.c1_le_one]
    have hcube : (4 * Work.BoseBogFS.bogC1 v ρ μ) ^ 3
        ≤ 16 * (4 * Work.BoseBogFS.bogC1 v ρ μ) := by
      have hsq : (4 * Work.BoseBogFS.bogC1 v ρ μ) ^ 2 ≤ 16 := by nlinarith [hR0nn, hR0le]
      nlinarith [hsq, hR0nn]
    have h1 : 4 * Real.pi * (4 * Work.BoseBogFS.bogC1 v ρ μ) ^ 3 / 3
          + 4 * Real.pi * (4 * Work.BoseBogFS.bogC1 v ρ μ)
        ≤ (304 / 3) * Real.pi * Work.BoseBogFS.bogC1 v ρ μ := by
      nlinarith [hcube, hR0nn, Real.pi_pos]
    have h2 : 30000 * ((304 / 3) * Real.pi * Work.BoseBogFS.bogC1 v ρ μ)
        ≤ 10 ^ 8 * Work.BoseBogFS.bogC1 v ρ μ := by
      have h3 : 30000 * ((304 / 3) * Real.pi) ≤ 10 ^ 8 := by nlinarith [Real.pi_lt_four]
      nlinarith [h3, hc1nn]
    have h4 : 10 ^ 8 * Work.BoseBogFS.bogC1 v ρ μ
        ≤ 10 ^ 8 * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
      have := mul_le_mul_of_nonneg_left hc1eps (by norm_num : (0 : ℝ) ≤ 10 ^ 8)
      linarith [this]
    have h5 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 30000)
    linarith [h5, h2, h4]
  calc (∫ t in Metric.closedBall (0 : E3) (4 * Work.BoseBogFS.bogC1 v ρ μ),
        (Work.BoseBogFS.psiSc v h ρ μ t -
          Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t))
      ≤ ∫ t in Metric.closedBall (0 : E3) (4 * Work.BoseBogFS.bogC1 v ρ μ),
          30000 * (1 + (‖t‖ ^ 2)⁻¹) := hstep1
    _ = 30000 * (4 * Real.pi * (4 * Work.BoseBogFS.bogC1 v ρ μ) ^ 3 / 3
          + 4 * Real.pi * (4 * Work.BoseBogFS.bogC1 v ρ μ)) := hval
    _ ≤ 10 ^ 8 * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := hfinal

end Work.BoseBogFS
