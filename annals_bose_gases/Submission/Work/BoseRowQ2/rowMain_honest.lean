import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB7AK.W1rows.W1omega_low_nonneg
import Submission.Work.BoseBoxFock.bessel_honest
import Submission.Work.BoseRowQ2.ArithRow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseRowQ2/rowMain_honest.lean` — FS l.3240–3262 at the honest model
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! ## 0. The honest `n₊^H` threshold `κ` -/

/-- The threshold of the honest `n₊^H`: `κ = (K_ℓ d²)⁻¹√(μa)`. -/
noncomputable def honKappa (v : ℝ³ → ℝ) (μ : ℝ) : ℝ :=
  ((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
    * Real.sqrt (μ * BoseGases.a v)

/-! ## 1. The two absolute thresholds the row produces -/

/-- `2^{-65892}`: the diluteness scale at which the `ε`-correction is paid. -/
noncomputable def honTA : ℝ := ((1 : ℝ) / 2) ^ (65892 : ℕ)

/-- `(2^{-27})^{323/299}(a/R)^{646/299}`: the diluteness scale at which the
low-momentum deficit `W₀ − Ŵ₁ω(k)` is dominated by the `ℓ⁻²n₊` gap. -/
noncomputable def honTB (a R : ℝ) : ℝ :=
  (((1 : ℝ) / 2) ^ (27 : ℕ)) ^ (323 / 299 : ℝ)
    * (a / R) ^ (646 / 299 : ℝ)

lemma honTA_pos : 0 < honTA := by
  rw [honTA]; positivity

lemma honTB_pos {a R : ℝ} (ha : 0 < a) (hR : 0 < R) : 0 < honTB a R := by
  rw [honTB]
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)

/-! ## 2. `ρ` of `KzEnvAt`, and `η_H` at high momentum -/

/-- `KzEnvAt` reassigns `z = √(ρℓ³)`, so it reassigns the derived density
`rho = z²/ℓ³` to `ρ`. -/
lemma KzEnvAt_rho {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) (_hρ : 0 ≤ ρ) (hℓ : 0 < E.ell) :
    (Work.BoseFixR.KzEnvAt E ρ).rho = ρ := by
  rw [Work.BoseB7.Q3Env.rho, Work.BoseFixR.KzEnvAt, Work.BoseB7.rhoZ]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ρ * E.ell ^ 3)]
  rw [mul_div_assoc, div_self (by positivity : E.ell ^ 3 ≠ 0), mul_one]

/-- `η_H(k) = 1` on `‖k‖ ≥ 4κ` (`f_u = 0` on `[2,∞)`). -/
lemma etaH_eq_one (fu : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : 4 * κ ≤ ‖p‖) : Work.BoseBoxFock.etaH fu κ p = 1 := by
  have h2 : (2 : ℝ) ≤ ‖p‖ / (2 * κ) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [Work.BoseBoxFock.etaH, fu.zero (‖p‖ / (2 * κ)) h2]
  ring

/-- `qw` of a finite weighted sum. -/
lemma qw_finset_sum {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (Ψ : F.H) (s : Finset Mode) (c : Mode → ℝ)
    (X : Mode → F.H →ₗ[ℝ] F.H) :
    F.qw Ψ (∑ k ∈ s, c k • X k) = ∑ k ∈ s, c k * F.qw Ψ (X k) := by
  simp only [Work.BoseB7.FockData.qw, LinearMap.sum_apply, map_sum, LinearMap.smul_apply,
    map_smul, smul_eq_mul]

/-! ## 3. The two `Ŵ₁ω` bounds at the corpus kernel -/

/-- At the corpus kernel `Ŵ₁ω = chat (W1omegaFun v h ℓ)`, in the dilute regime
`R ≤ ℓ·chiR0`:

* `Ŵ₁ω(k) ≥ −Ŵ₁ω(0)` for **every** `k` (no smallness of `‖k‖R`);
* `Ŵ₁ω(0) − Ŵ₁ω(k) ≤ ½‖k‖²R²Ŵ₁ω(0)` for **every** `k`. -/
lemma W1omegaFun_bounds {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ} (hR : 0 < R)
    (hℓ : 0 < ℓ) (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    (∀ p : ℝ³, -(Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) 0)
        ≤ Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) p)
    ∧ (∀ p : ℝ³, Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) 0
          - Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) p
        ≤ (1 / 2) * ‖p‖ ^ 2 * R ^ 2
            * Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) 0) := by
  have hWi : MeasureTheory.Integrable (Work.BoseFixR.W1omegaFun v h ℓ) :=
    Work.BoseB7AK.W1rows.W1omegaFun_integrable (ℓ := ℓ) hR hℓ hv_nonneg hvrad hv_supp h hRℓ
  have hWi2 : MeasureTheory.Integrable
      (fun x : ℝ³ => ‖x‖ ^ 2 * |Work.BoseFixR.W1omegaFun v h ℓ x|) :=
    Work.BoseB7AK.W1rows.W1omegaFun_moment_integrable (ℓ := ℓ) hR hℓ hv_nonneg hvrad hv_supp h hRℓ
  have hnn : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³),
      0 ≤ Work.BoseFixR.W1omegaFun v h ℓ x :=
    Work.BoseB7AK.W1rows.W1omegaFun_nonneg_ae (ℓ := ℓ) hR hv_nonneg hvrad hv_supp h
  have h0 : Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) 0
      = ∫ x, Work.BoseFixR.W1omegaFun v h ℓ x := Work.BoseB7AK.W1rows.chat_zero _
  have habsint : (∫ x, |Work.BoseFixR.W1omegaFun v h ℓ x|)
      = ∫ x, Work.BoseFixR.W1omegaFun v h ℓ x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hnn] with x hx
    exact abs_of_nonneg hx
  constructor
  · intro p
    rw [h0, Work.BoseB7AK.W1low.chat_eq_integral_cos hWi p]
    have h2 : |∫ y, Work.BoseFixR.W1omegaFun v h ℓ y * Real.cos (inner ℝ p y)|
        ≤ ∫ y, |Work.BoseFixR.W1omegaFun v h ℓ y * Real.cos (inner ℝ p y)| := by
      simpa only [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm
          (fun y : ℝ³ => Work.BoseFixR.W1omegaFun v h ℓ y * Real.cos (inner ℝ p y))
    have h3 : (∫ y, |Work.BoseFixR.W1omegaFun v h ℓ y * Real.cos (inner ℝ p y)|)
        ≤ ∫ y, |Work.BoseFixR.W1omegaFun v h ℓ y| := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun y => abs_nonneg _) hWi.abs ?_
      filter_upwards with y
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    rw [habsint] at h3
    have h4 := (abs_le.mp (le_trans h2 h3)).1
    linarith
  · intro p
    rw [h0]
    have hsub := Work.BoseB7AK.W1low.chat_sub_le_abs hWi hWi2 p
    rw [Work.BoseB7AK.W1rows.chat_zero] at hsub
    have hmom : (∫ x, ‖x‖ ^ 2 * |Work.BoseFixR.W1omegaFun v h ℓ x|)
        ≤ R ^ 2 * ∫ x, Work.BoseFixR.W1omegaFun v h ℓ x := by
      have hm := Work.BoseB7AK.W1rows.W1omegaFun_moment_le (ℓ := ℓ) hR hv_nonneg hvrad hv_supp h
      have h1 := MeasureTheory.integral_mono_ae hWi2 (hWi.const_mul (R ^ 2)) ?_
      · rwa [MeasureTheory.integral_const_mul] at h1
      · filter_upwards [hm] with x hx
        exact hx
    have h4 : |Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) p
        - ∫ x, Work.BoseFixR.W1omegaFun v h ℓ x|
        ≤ (1 / 2) * ‖p‖ ^ 2 * (R ^ 2 * ∫ x, Work.BoseFixR.W1omegaFun v h ℓ x) := by
      refine le_trans hsub ?_
      have h5 : 0 ≤ (1 / 2 : ℝ) * ‖p‖ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hmom h5
      linarith
    have h6 : (∫ x, Work.BoseFixR.W1omegaFun v h ℓ x)
        - Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) p
        ≤ |Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) p
            - ∫ x, Work.BoseFixR.W1omegaFun v h ℓ x| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith

/-! ## 4. The `Ŵ₁ω(0)` row at the honest model (from the régime alone) -/

/-- **`0 ≤ Ŵ₁ω(0) ≤ 16π a v` at the honest data**, from the régime hypothesis
`hrég` alone (no `HonSetup`, no UV-cut condition). -/
lemma honE_W1omega0_row {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R εg : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      0 ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        ∧ (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            ≤ 16 * Real.pi * _root_.BoseGases.a v := by
  intro HM μ hμ hμa
  obtain ⟨-, hRℓ⟩ := hrég μ hμ hμa
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hW0 : (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ)) 0 := by
    have hside : Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        = Work.BoseBoxFock.ellH v μ := by
      rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
    simp only [Work.BoseRowsFS.honE, Work.BoseRowsFS.honF, Work.BoseBoxFock.HonestBoxFam,
      Work.BoseBoxFock.KzEnvHon, Work.BoseFixR.KzEnvFs, hside]
  have hWnn : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³),
      0 ≤ Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) z :=
    Work.BoseB7AK.W1rows.W1omegaFun_nonneg_ae (ℓ := Work.BoseBoxFock.ellH v μ) hR hv_nonneg hvrad hv_supp h
  have hnn : 0 ≤ Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ)) 0 := by
    rw [Work.BoseB7AK.W1rows.chat_zero]
    exact MeasureTheory.integral_nonneg_of_ae hWnn
  have hIntEq : (∫ z, Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) z)
      = ∫ z, |Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) z| := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hWnn] with z hz
    exact (abs_of_nonneg hz).symm
  have habs : Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ)) 0
      ≤ 16 * Real.pi * _root_.BoseGases.a v := by
    rw [Work.BoseB7AK.W1rows.chat_zero, hIntEq]
    exact Work.BoseB7AK.W1rows.W1omega_abs_integral_le hR hℓ hv_nonneg hvrad hv_supp h hRℓ
  exact ⟨hW0 ▸ hnn, hW0 ▸ habs⟩

/-- The two `Ŵ₁ω` bounds of §3 restated at the honest environment. -/
lemma honE_W1omega_bounds {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {R : ℝ} (hR : 0 < R) (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        -(Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
    ∧ (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k
          ≤ (1 / 2) * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2 * R ^ 2
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0) := by
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  obtain ⟨hb1, hb2⟩ := W1omegaFun_bounds hR hℓ hv_nonneg hvrad hv_supp hRℓ
  have hw : (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega
      = fun k => Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ))
          ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) := by
    funext k
    have hside : Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        = Work.BoseBoxFock.ellH v μ := by
      rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
    simp only [Work.BoseRowsFS.honE, Work.BoseRowsFS.honF, Work.BoseBoxFock.HonestBoxFam,
      Work.BoseBoxFock.KzEnvHon, Work.BoseFixR.KzEnvFs, hside]
  have hw0 : (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ)) 0 := by
    have hside : Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        = Work.BoseBoxFock.ellH v μ := by
      rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
    simp only [Work.BoseRowsFS.honE, Work.BoseRowsFS.honF, Work.BoseBoxFock.HonestBoxFam,
      Work.BoseBoxFock.KzEnvHon, Work.BoseFixR.KzEnvFs, hside]
  constructor
  · intro k
    rw [hw, hw0]
    exact hb1 _
  · intro k
    rw [hw, hw0]
    exact hb2 _


/-! ## 5. The parameter identities in `t = μa³` -/

/-- `ℓ⁻² = μa·t^{3/323}`. -/
lemma honE_ell_rpow {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
      = (μ * _root_.BoseGases.a v) * (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ) := by
  have ht : 0 < μ * _root_.BoseGases.a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hμa : 0 < μ * _root_.BoseGases.a v := mul_pos hμ hav
  rw [Work.BoseRowQ2.honE_ell_eq v h fc fu HM hμ hav]
  rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hμa.le _)]
  rw [← Real.rpow_mul ht.le, ← Real.rpow_mul hμa.le]
  rw [show (-(3 / 646) : ℝ) * (-(2 : ℝ)) = 3 / 323 by norm_num,
    show (-(1 / 2) : ℝ) * (-(2 : ℝ)) = 1 by norm_num, Real.rpow_one]
  ring

/-- `ε_T(dℓ)⁻² = μa·t^{-13/1292}`. -/
lemma honE_gap2_eq {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).eT
        * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))
      = (μ * _root_.BoseGases.a v) * (μ * _root_.BoseGases.a v ^ 3) ^ (-(13 / 1292) : ℝ) := by
  have ht : 0 < μ * _root_.BoseGases.a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hμa : 0 < μ * _root_.BoseGases.a v := mul_pos hμ hav
  rw [Work.BoseRowQ2.honE_eT_eq' v h fc fu HM μ, Work.BoseRowQ2.honE_d_eq v h fc fu HM μ,
    Work.BoseRowQ2.honE_ell_eq v h fc fu HM hμ hav]
  rw [show (6 : ℝ) / 323 = (12 : ℝ) / 646 by norm_num]
  rw [show (μ * _root_.BoseGases.a v ^ 3) ^ ((12 : ℝ) / 646)
        * ((μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ)
            * (μ * _root_.BoseGases.a v) ^ (-(1 / 2) : ℝ))
      = ((μ * _root_.BoseGases.a v ^ 3) ^ ((12 : ℝ) / 646)
          * (μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ))
          * (μ * _root_.BoseGases.a v) ^ (-(1 / 2) : ℝ) by ring]
  rw [show ((μ * _root_.BoseGases.a v ^ 3) ^ ((12 : ℝ) / 646)
          * (μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ))
      = (μ * _root_.BoseGases.a v ^ 3) ^ ((9 : ℝ) / 646) by
    rw [← Real.rpow_add ht]
    rw [show (12 : ℝ) / 646 + (-(3 / 646)) = (9 : ℝ) / 646 by norm_num]]
  rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hμa.le _)]
  rw [← Real.rpow_mul ht.le, ← Real.rpow_mul hμa.le]
  rw [show ((9 : ℝ) / 646) * (-(2 : ℝ)) = -(9 / 323) by norm_num,
    show (-(1 / 2) : ℝ) * (-(2 : ℝ)) = 1 by norm_num, Real.rpow_one]
  rw [show (μ * _root_.BoseGases.a v ^ 3) ^ ((23 : ℝ) / 1292)
        * ((μ * _root_.BoseGases.a v ^ 3) ^ (-(9 / 323) : ℝ)
            * (μ * _root_.BoseGases.a v))
      = ((μ * _root_.BoseGases.a v ^ 3) ^ ((23 : ℝ) / 1292)
          * (μ * _root_.BoseGases.a v ^ 3) ^ (-(9 / 323) : ℝ))
          * (μ * _root_.BoseGases.a v) by ring]
  rw [show (μ * _root_.BoseGases.a v ^ 3) ^ ((23 : ℝ) / 1292)
        * (μ * _root_.BoseGases.a v ^ 3) ^ (-(9 / 323) : ℝ)
      = (μ * _root_.BoseGases.a v ^ 3) ^ (-(13 / 1292) : ℝ) by
    rw [← Real.rpow_add ht]
    rw [show (23 : ℝ) / 1292 + (-(9 / 323)) = -(13 / 1292) by norm_num]]
  ring

/-- `fsEps v 58982400 μ = 58982400·t^{13/1292}`. -/
lemma fsEps_eq {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseRowQ2.fsEps v 58982400 μ
      = 58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ) := by
  have ht : 0 < μ * _root_.BoseGases.a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hcomb1 : (μ * _root_.BoseGases.a v ^ 3) ^ ((12 : ℝ) / 323)
        * (μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 323) : ℝ)
      = (μ * _root_.BoseGases.a v ^ 3) ^ ((9 : ℝ) / 323) := by
    have h := Real.rpow_add ht ((12 : ℝ) / 323) (-(3 / 323) : ℝ)
    rw [show (12 : ℝ) / 323 + (-(3 / 323)) = (9 : ℝ) / 323 by norm_num] at h
    exact h.symm
  have hcomb2 : (μ * _root_.BoseGases.a v ^ 3) ^ (-(23 / 1292) : ℝ)
        * (μ * _root_.BoseGases.a v ^ 3) ^ ((9 : ℝ) / 323)
      = (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ) := by
    have h := Real.rpow_add ht (-(23 / 1292) : ℝ) ((9 : ℝ) / 323)
    rw [show (-(23 / 1292) : ℝ) + 9 / 323 = 13 / 1292 by norm_num] at h
    exact h.symm
  simp only [Work.BoseRowQ2.fsEps, Work.BoseBox.paramsAt, Work.BoseBox.fsParams,
    Work.BoseBox.fsXp]
  rw [show (23 / 4 : ℝ) / 323 = (23 : ℝ) / 1292 by norm_num,
    show (6 : ℝ) / 323 = (12 : ℝ) / 646 by norm_num,
    show (-(3 / 2) : ℝ) / 323 = -(3 / 646) by norm_num]
  rw [← Real.rpow_neg ht.le]
  rw [← Real.rpow_two]
  rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _)]
  rw [← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le]
  rw [show ((12 : ℝ) / 646) * (2 : ℝ) = (12 : ℝ) / 323 by norm_num,
    show (-(3 / 646) : ℝ) * (2 : ℝ) = -(3 / 323) by norm_num]
  rw [hcomb1, mul_assoc, hcomb2]

/-- `κ² = t^{302/323}/a²` for the honest `n₊^H` threshold `κ`. -/
lemma honKappa_sq {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    (Work.BoseRowQ2.honKappa v μ) ^ 2
      = (μ * _root_.BoseGases.a v ^ 3) ^ (302 / 323 : ℝ) / (_root_.BoseGases.a v) ^ 2 := by
  have ht : 0 < μ * _root_.BoseGases.a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hμa : 0 < μ * _root_.BoseGases.a v := mul_pos hμ hav
  have hKl : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      = (μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ) := by
    rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        = Work.BoseBox.fsXp (μ * _root_.BoseGases.a v ^ 3) (-(3 / 2)) from rfl]
    rw [Work.BoseBox.fsXp]
    rw [show (-(3 / 2) : ℝ) / 323 = -(3 / 646) by norm_num]
  have hd : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      = (μ * _root_.BoseGases.a v ^ 3) ^ ((12 : ℝ) / 646) := by
    rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        = Work.BoseBox.fsXp (μ * _root_.BoseGases.a v ^ 3) 6 from rfl]
    rw [Work.BoseBox.fsXp]
    rw [show (6 : ℝ) / 323 = 12 / 646 by norm_num]
  -- convert all the natural powers to real powers
  have h1 : (Work.BoseRowQ2.honKappa v μ) ^ (2 : ℕ) = (Work.BoseRowQ2.honKappa v μ) ^ (2 : ℝ) :=
    (Real.rpow_two _).symm
  have h2 : (_root_.BoseGases.a v) ^ (2 : ℕ) = (_root_.BoseGases.a v) ^ (2 : ℝ) :=
    (Real.rpow_two _).symm
  rw [h1, h2]
  have h3 : ((μ * _root_.BoseGases.a v ^ 3) ^ ((12 : ℝ) / 646)) ^ (2 : ℕ)
      = ((μ * _root_.BoseGases.a v ^ 3) ^ ((12 : ℝ) / 646)) ^ (2 : ℝ) :=
    (Real.rpow_two _).symm
  rw [Work.BoseRowQ2.honKappa, hKl, hd, Real.sqrt_eq_rpow, h3]
  have hKd : (μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ)
        * ((μ * _root_.BoseGases.a v ^ 3) ^ ((12 : ℝ) / 646)) ^ (2 : ℝ)
      = (μ * _root_.BoseGases.a v ^ 3) ^ ((21 : ℝ) / 646) := by
    rw [← Real.rpow_mul ht.le]
    rw [show ((12 : ℝ) / 646) * (2 : ℝ) = (24 : ℝ) / 646 by norm_num]
    rw [← Real.rpow_add ht]
    rw [show (-(3 / 646) : ℝ) + 24 / 646 = 21 / 646 by norm_num]
  have hfin : (μ * _root_.BoseGases.a v ^ 3) ^ (-(21 / 323) : ℝ) * (μ * _root_.BoseGases.a v)
      = (μ * _root_.BoseGases.a v ^ 3) ^ (302 / 323 : ℝ) / (_root_.BoseGases.a v) ^ (2 : ℝ) := by
    rw [show μ * _root_.BoseGases.a v
        = (μ * _root_.BoseGases.a v ^ 3) / (_root_.BoseGases.a v) ^ (2 : ℝ) by
      rw [mul_div_assoc]
      congr 1
      rw [show (_root_.BoseGases.a v) ^ (3 : ℕ) = (_root_.BoseGases.a v) ^ (3 : ℝ) from
        (Real.rpow_natCast _ 3).symm]
      rw [← Real.rpow_sub hav (3 : ℝ) (2 : ℝ)]
      rw [show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one]]
    rw [mul_div_assoc']
    rw [show (μ * _root_.BoseGases.a v ^ 3) ^ (302 / 323 : ℝ)
        = (μ * _root_.BoseGases.a v ^ 3) ^ (-(21 / 323) : ℝ)
            * (μ * _root_.BoseGases.a v ^ 3) ^ (1 : ℝ) by
      rw [← Real.rpow_add ht]
      rw [show (-(21 / 323) : ℝ) + 1 = 302 / 323 by norm_num]]
    rw [Real.rpow_one]
  have hX : 0 ≤ (μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ)
      * ((μ * _root_.BoseGases.a v ^ 3) ^ ((12 : ℝ) / 646)) ^ (2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (Real.rpow_nonneg ht.le _) _)
  rw [Real.mul_rpow (Real.rpow_nonneg hX _) (Real.rpow_nonneg hμa.le _)]
  rw [← Real.rpow_mul hX, ← Real.rpow_mul hμa.le]
  rw [show (-(1 : ℝ)) * (2 : ℝ) = -2 by norm_num,
    show (1 / 2 : ℝ) * (2 : ℝ) = 1 by norm_num, Real.rpow_one]
  rw [show ((μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ)
        * ((μ * _root_.BoseGases.a v ^ 3) ^ ((12 : ℝ) / 646)) ^ (2 : ℝ)) ^ (-(2 : ℝ))
      = ((μ * _root_.BoseGases.a v ^ 3) ^ ((21 : ℝ) / 646)) ^ (-(2 : ℝ)) by rw [hKd]]
  rw [← Real.rpow_mul ht.le]
  rw [show ((21 : ℝ) / 646) * (-(2 : ℝ)) = -(21 / 323) by norm_num]
  exact hfin

/-! ## 6. The absolute arithmetic of the row -/

private lemma rpow_honTA {t e : ℝ} (ht : 0 < t) (h : t ≤ honTA) (he : 0 ≤ e) :
    t ^ e ≤ ((1 : ℝ) / 2) ^ (65892 * e) := by
  rw [honTA] at h
  calc t ^ e ≤ (((1 : ℝ) / 2) ^ (65892 : ℕ)) ^ e := Real.rpow_le_rpow ht.le h he
    _ = ((1 : ℝ) / 2) ^ (((65892 : ℕ) : ℝ) * e) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ = ((1 : ℝ) / 2) ^ ((65892 : ℝ) * e) := by
        rw [show ((65892 : ℕ) : ℝ) = (65892 : ℝ) by norm_num]

private lemma rowMain_arith {t a R : ℝ} (ht : 0 < t) (ha : 0 < a) (hR : 0 < R)
    (hTA : t ≤ honTA) (hTB : t ≤ honTB a R) :
    58982400 * t ^ (13 / 1292 : ℝ) ≤ 1 / 2
    ∧ 2304 * (58982400 * t ^ (13 / 1292 : ℝ)) ≤ (1 / 12800) * t ^ (3 / 323 : ℝ)
    ∧ 9216 * (t ^ (302 / 323 : ℝ) * (R / a) ^ 2) ≤ (1 / 12800) * t ^ (3 / 323 : ℝ)
    ∧ 2304 * Real.pi ≤ (1 / 12800) * t ^ (-(13 / 1292) : ℝ) := by
  have hA13 : t ^ (13 / 1292 : ℝ) ≤ ((1 : ℝ) / 2) ^ (663 : ℕ) := by
    have h := rpow_honTA ht hTA (by norm_num : (0 : ℝ) ≤ 13 / 1292)
    have h663 : ((1 : ℝ) / 2) ^ ((65892 : ℝ) * (13 / 1292)) = ((1 : ℝ) / 2) ^ (663 : ℕ) := by
      rw [show (65892 : ℝ) * (13 / 1292) = ((663 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [h663] at h
  have hA1 : t ^ (1 / 1292 : ℝ) ≤ ((1 : ℝ) / 2) ^ (51 : ℕ) := by
    have h := rpow_honTA ht hTA (by norm_num : (0 : ℝ) ≤ 1 / 1292)
    have h51 : ((1 : ℝ) / 2) ^ ((65892 : ℝ) * (1 / 1292)) = ((1 : ℝ) / 2) ^ (51 : ℕ) := by
      rw [show (65892 : ℝ) * (1 / 1292) = ((51 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [h51] at h
  have hpos3 : 0 < t ^ (3 / 323 : ℝ) := Real.rpow_pos_of_pos ht _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h27 : ((1 : ℝ) / 2) ^ (663 : ℕ) ≤ ((1 : ℝ) / 2) ^ (27 : ℕ) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num : 27 ≤ 663)
    have h2 : (58982400 : ℝ) * ((1 : ℝ) / 2) ^ (27 : ℕ) ≤ 1 / 2 := by norm_num
    calc 58982400 * t ^ (13 / 1292 : ℝ)
        ≤ 58982400 * ((1 : ℝ) / 2) ^ (663 : ℕ) :=
          mul_le_mul_of_nonneg_left hA13 (by norm_num)
      _ ≤ 58982400 * ((1 : ℝ) / 2) ^ (27 : ℕ) :=
          mul_le_mul_of_nonneg_left h27 (by norm_num)
      _ ≤ 1 / 2 := h2
  · have hconst : (2304 : ℝ) * 58982400 * ((1 : ℝ) / 2) ^ (51 : ℕ) ≤ 1 / 12800 := by norm_num
    have hsplit : t ^ (13 / 1292 : ℝ) = t ^ (3 / 323 : ℝ) * t ^ (1 / 1292 : ℝ) := by
      rw [show (13 / 1292 : ℝ) = 3 / 323 + 1 / 1292 by norm_num, Real.rpow_add ht]
    calc 2304 * (58982400 * t ^ (13 / 1292 : ℝ))
        = (2304 * 58982400) * (t ^ (3 / 323 : ℝ) * t ^ (1 / 1292 : ℝ)) := by
          rw [hsplit]; ring
      _ ≤ (2304 * 58982400) * (t ^ (3 / 323 : ℝ) * ((1 : ℝ) / 2) ^ (51 : ℕ)) := by
          have h := mul_le_mul_of_nonneg_left hA1 hpos3.le
          exact mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (2304 * 58982400 * ((1 : ℝ) / 2) ^ (51 : ℕ)) * t ^ (3 / 323 : ℝ) := by ring
      _ ≤ (1 / 12800) * t ^ (3 / 323 : ℝ) := mul_le_mul_of_nonneg_right hconst hpos3.le
  · have hTB1 : t ^ (299 / 323 : ℝ) ≤ ((1 : ℝ) / 2) ^ (27 : ℕ) * (a / R) ^ 2 := by
      have h1 : t ^ (299 / 323 : ℝ) ≤ (honTB a R) ^ (299 / 323 : ℝ) :=
        Real.rpow_le_rpow ht.le hTB (by norm_num)
      have h2 : (honTB a R) ^ (299 / 323 : ℝ) = ((1 : ℝ) / 2) ^ (27 : ℕ) * (a / R) ^ 2 := by
        rw [honTB, Real.mul_rpow
          (Real.rpow_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 27) _)
          (Real.rpow_nonneg (div_nonneg ha.le hR.le) _)]
        rw [← Real.rpow_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 27),
          ← Real.rpow_mul (div_nonneg ha.le hR.le)]
        rw [show (323 / 299 : ℝ) * (299 / 323) = (1 : ℝ) by norm_num, Real.rpow_one]
        rw [show (646 / 299 : ℝ) * (299 / 323) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [h2] at h1
      exact h1
    have hab : (a / R) ^ 2 * (R / a) ^ 2 = 1 := by
      rw [← mul_pow]
      rw [show a / R * (R / a) = 1 by field_simp]
      norm_num
    have hmain : t ^ (302 / 323 : ℝ) * (R / a) ^ 2
        ≤ ((1 : ℝ) / 2) ^ (27 : ℕ) * t ^ (3 / 323 : ℝ) := by
      have hsplit2 : t ^ (302 / 323 : ℝ) = t ^ (299 / 323 : ℝ) * t ^ (3 / 323 : ℝ) := by
        rw [show (302 / 323 : ℝ) = 299 / 323 + 3 / 323 by norm_num, Real.rpow_add ht]
      rw [hsplit2]
      have h := mul_le_mul_of_nonneg_right hTB1 (pow_nonneg (div_nonneg hR.le ha.le) 2)
      have h' : ((1 : ℝ) / 2) ^ (27 : ℕ) * (a / R) ^ 2 * (R / a) ^ 2
          = ((1 : ℝ) / 2) ^ (27 : ℕ) := by
        rw [mul_assoc, hab, mul_one]
      rw [h'] at h
      calc t ^ (299 / 323 : ℝ) * t ^ (3 / 323 : ℝ) * (R / a) ^ 2
          = (t ^ (299 / 323 : ℝ) * (R / a) ^ 2) * t ^ (3 / 323 : ℝ) := by ring
        _ ≤ ((1 : ℝ) / 2) ^ (27 : ℕ) * t ^ (3 / 323 : ℝ) :=
            mul_le_mul_of_nonneg_right h hpos3.le
    calc 9216 * (t ^ (302 / 323 : ℝ) * (R / a) ^ 2)
        ≤ 9216 * (((1 : ℝ) / 2) ^ (27 : ℕ) * t ^ (3 / 323 : ℝ)) :=
          mul_le_mul_of_nonneg_left hmain (by norm_num)
      _ = (9216 * ((1 : ℝ) / 2) ^ (27 : ℕ)) * t ^ (3 / 323 : ℝ) := by ring
      _ ≤ (1 / 12800) * t ^ (3 / 323 : ℝ) :=
          mul_le_mul_of_nonneg_right (by norm_num) hpos3.le
  · have h2 : (2 : ℝ) ^ (663 : ℕ) ≤ t ^ (-(13 / 1292) : ℝ) := by
      have h3 : (2 : ℝ) ^ (663 : ℕ) = (1 : ℝ) / ((1 : ℝ) / 2) ^ (663 : ℕ) := by
        rw [one_div, ← inv_pow]
        norm_num
      rw [h3]
      calc (1 : ℝ) / ((1 : ℝ) / 2) ^ (663 : ℕ)
          ≤ (1 : ℝ) / t ^ (13 / 1292 : ℝ) := one_div_le_one_div_of_le (by positivity) hA13
        _ = t ^ (-(13 / 1292) : ℝ) := by rw [one_div, ← Real.rpow_neg ht.le]
    have h4 : (2304 : ℝ) * Real.pi ≤ (1 / 12800) * (2 : ℝ) ^ (663 : ℕ) := by
      have h5 : (2 : ℝ) ^ (27 : ℕ) ≤ (2 : ℝ) ^ (663 : ℕ) :=
        pow_le_pow_right₀ (by norm_num) (by norm_num : 27 ≤ 663)
      have h6 : (2304 : ℝ) * 4 * 12800 ≤ (2 : ℝ) ^ (27 : ℕ) := by norm_num
      have h7 : (2304 : ℝ) * 4 * 12800 ≤ (2 : ℝ) ^ (663 : ℕ) := le_trans h6 h5
      have h8 : (2304 : ℝ) * 4 ≤ (2 : ℝ) ^ (663 : ℕ) / 12800 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12800)]
        exact h7
      calc (2304 : ℝ) * Real.pi ≤ (2304 : ℝ) * 4 := by linarith [Real.pi_lt_four]
        _ ≤ (2 : ℝ) ^ (663 : ℕ) / 12800 := h8
        _ = (1 / 12800) * (2 : ℝ) ^ (663 : ℕ) := by
            rw [div_eq_mul_inv, one_div]
            exact mul_comm _ _
    calc 2304 * Real.pi ≤ (1 / 12800) * (2 : ℝ) ^ (663 : ℕ) := h4
      _ ≤ (1 / 12800) * t ^ (-(13 / 1292) : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)

/-! ## 7. The row -/

/-- **FS `final_v2.tex` l.3240–3262 at the honest model** (the `RowMain` half of `RowQ2AllCore`, at `ε = fsEps v 58982400`): there are a cube size `Ng` and a diluteness threshold `εg' ∈ (0, εg]` such that for every honest mode family `HM` with `∀ μ, Ng μ ≤ (HM μ).N`, every `μ > 0` with `μ(a v)³ ≤ εg'`, every admissible `ρ` (`μ/2 ≤ ρ ≤ 3μ/2`) and every model vector `Ψ`,

  `2ρ(1 + ε μ)Ŵ₁ω(0)⟨Ψ, Σ_k a_k†a_k Ψ⟩ ≤ ⟨Ψ, Q₂^{ex,all}(KzEnvAt E ρ) Ψ⟩ + (b/400)ℓ⁻²⟨Ψ, n₊ Ψ⟩ + (b/800)ε_T(dℓ)⁻²⟨Ψ, n₊^H Ψ⟩`

where `Q₂^{ex,all} = Σ_k ρ(Ŵ₁ω(k) + Ŵ₁ω(0))a_k†a_k` runs over **all** labels (the corrected row of `Defs.lean`).  This is the `Q₂^ex` cancellation step: `Q₂^{ex,all}` pays the χ-mode number, and the two gap slots pay the arithmetic `ε`-correction and the low-momentum deficit `Ŵ₁ω(0) − Ŵ₁ω(k)`. -/
theorem rowMain_honest {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (εg : ℝ) (hεg : 0 < εg) (hεg1 : εg ≤ 1)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    ∃ Ng : ℝ → ℕ, ∃ εg' : ℝ, 0 < εg' ∧ εg' ≤ εg ∧
      Work.BoseRowQ2.RowMain (v := v) (h := h) (fc := fc) (fu := fu) R εg' Ng
        (Work.BoseRowQ2.fsEps v 58982400) := by
  refine ⟨fun _ => 0, min εg (min honTA (honTB (_root_.BoseGases.a v) R)),
    lt_min hεg (lt_min honTA_pos (honTB_pos hav hR)), min_le_left _ _, ?_⟩
  intro hεg'1 HM hNg μ hμ hμa ρ hρ Ψ
  have hμa3 : μ * _root_.BoseGases.a v ^ 3 ≤ εg := le_trans hμa (min_le_left _ _)
  have htA : μ * _root_.BoseGases.a v ^ 3 ≤ honTA :=
    le_trans hμa (le_trans (min_le_right _ _) (min_le_left _ _))
  have htB : μ * _root_.BoseGases.a v ^ 3 ≤ honTB (_root_.BoseGases.a v) R :=
    le_trans hμa (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht0 : 0 < μ * _root_.BoseGases.a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  obtain ⟨har0, har1, har2, har3⟩ := rowMain_arith ht0 hav hR htA htB
  have hEℓ : (Work.BoseRowsFS.honE v h fc fu HM μ).ell = Work.BoseBoxFock.ellH v μ :=
    Work.BoseRowsFS.honE_ell v h fc fu HM μ hμ hav
  have hℓEp : 0 < (Work.BoseRowsFS.honE v h fc fu HM μ).ell := by
    rw [hEℓ]; exact Work.BoseBoxFock.ellH_pos v μ
  have hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 := (hrég μ hμ hμa3).2
  have hRℓE : R ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).ell * Submission.BoseGases.chiR0 := by
    rw [hEℓ]; exact hRℓ
  obtain ⟨hW0nn, hW0le⟩ := honE_W1omega0_row (v := v) (h := h) (fc := fc) (fu := fu)
    (R := R) (εg := εg) hR hav hv_nonneg hvrad hv_supp hrég HM μ hμ hμa3
  obtain ⟨hwkge, hwkdef⟩ := honE_W1omega_bounds (v := v) (h := h) (fc := fc) (fu := fu)
    (HM := HM) (R := R) (μ := μ) hR hv_nonneg hvrad hv_supp hμ hav hRℓ
  have hμeq : (Work.BoseRowsFS.honE v h fc fu HM μ).mu = μ := rfl
  have hκpos : 0 < honKappa v μ := by
    rw [honKappa]
    refine mul_pos (Real.rpow_pos_of_pos ?_ _) (Real.sqrt_pos.mpr (mul_pos hμ hav))
    exact mul_pos (Work.BoseBox.fsXp_pos (mul_pos hμ (pow_pos hav 3)))
      (pow_pos (Work.BoseBox.fsXp_pos (mul_pos hμ (pow_pos hav 3))) 2)
  have heps : Work.BoseRowQ2.fsEps v 58982400 μ
      = 58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ) := fsEps_eq hμ hav
  have hκR : (honKappa v μ) ^ 2 * R ^ 2
      = (μ * _root_.BoseGases.a v ^ 3) ^ (302 / 323 : ℝ) * (R / _root_.BoseGases.a v) ^ 2 := by
    rw [honKappa_sq hμ hav]; ring
  have hell2 : (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
      = (μ * _root_.BoseGases.a v) * (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ) :=
    honE_ell_rpow hμ hav
  have hgap2 : (Work.BoseRowsFS.honE v h fc fu HM μ).eT
        * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))
      = (μ * _root_.BoseGases.a v) * (μ * _root_.BoseGases.a v ^ 3) ^ (-(13 / 1292) : ℝ) :=
    honE_gap2_eq hμ hav
  have hb16 : (Work.BoseRowsFS.honE v h fc fu HM μ).b = 1 / 16 :=
    Work.BoseRowsFS.honE_b v h fc fu HM μ
  -- §3 the `Ŵ₁ω` facts at the environment
  have hAunf : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
      = ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
          (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) :=
    Work.BoseB7.FockData.qw_allNumOp _ _
  have hQunf : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
      = ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
          ρ * ((Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k
              + (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
    rw [Work.BoseB7.FockData.qw_Q2exAll]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hρ' : (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).rho = ρ :=
      KzEnvAt_rho _ ρ hρ.1 hℓEp
    have hw1 : (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).W1omega
        = (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega := rfl
    have hw0 : (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).W1omega0
        = (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := rfl
    rw [hρ', hw1, hw0]
  have hBessel : ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
      ≤ (48 / Real.pi) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          (Work.BoseRowsFS.honT v h fc fu HM μ).N := by
    have hbes := Work.BoseBoxFock.bessel_honest v h fc fu HM μ Ψ
    have hsum : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
            (Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        = ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
            (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
      have hq := Work.BoseB7.FockData.qw_sum_all (Work.BoseRowsFS.honF v h fc fu HM μ) Ψ
        (fun _ => (1 : ℝ)) (fun k => (Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
      simpa using hq
    rw [← hsum]
    exact hbes
  have hNHunf : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        (Work.BoseRowsFS.honT v h fc fu HM μ).NH
      = (1 / 32 : ℝ) * ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          Work.BoseBoxFock.etaH fu (honKappa v μ)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
    have hNHform : (Work.BoseRowsFS.honT v h fc fu HM μ).NH
        = (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
            Work.BoseBoxFock.etaH fu (honKappa v μ)
                ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
              • (Work.BoseRowsFS.honF v h fc fu HM μ).nOp k := by
      simp only [Work.BoseRowsFS.honT, Work.BoseRowsFS.honF, Work.BoseBoxFock.HonestBoxFam,
        Work.BoseBoxFock.tildeDataHon, Work.BoseRowQ2.honKappa]
      rfl
    rw [hNHform, Work.BoseB7.FockData.qw_smul, qw_finset_sum]
  have hHle : ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
          ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
        (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
      ≤ 32 * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by
    rw [hNHunf]
    have hsub : ∀ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
          ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
        k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨-, hk2⟩ := hk
      rw [Work.BoseB7.excited, Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hk0
      have hkm : (Work.BoseRowsFS.honF v h fc fu HM μ).kmom k = 0 := by
        rw [hk0, Work.BoseRowsFS.honF_kmom]
        exact Work.BoseBoxFock.kmomLab_zero (Work.BoseBoxFock.ellH v μ) (HM μ).N
      rw [hkm, norm_zero] at hk2
      have : (0 : ℝ) < 4 * honKappa v μ := by linarith [hκpos]
      linarith
    have h1 : ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          Work.BoseBoxFock.etaH fu (honKappa v μ)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≥ ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
              ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
            (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
      rw [ge_iff_le]
      calc ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
              ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
            (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
          = ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
              ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
              Work.BoseBoxFock.etaH fu (honKappa v μ)
                ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [Finset.mem_filter] at hk
            rw [etaH_eq_one fu hκpos (not_lt.mp hk.2), one_mul]
        _ ≤ _ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ =>
              mul_nonneg (Work.BoseBoxFock.etaH_nonneg fu (honKappa v μ) _)
                (Work.BoseB7.FockData.nOp_qw_nonneg' _ k Ψ))
    rw [show (32 : ℝ) * ((1 / 32) * ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          Work.BoseBoxFock.etaH fu (honKappa v μ)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k))
        = ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          Work.BoseBoxFock.etaH fu (honKappa v μ)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) from by ring]
    linarith [h1]
  -- the two arithmetic estimates
  have hNvnn : 0 ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
      (Work.BoseRowsFS.honT v h fc fu HM μ).N :=
    (Work.BoseRowsFS.honT v h fc fu HM μ).N_nonneg Ψ
  have hNHvnn : 0 ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
      (Work.BoseRowsFS.honT v h fc fu HM μ).NH :=
    (Work.BoseRowsFS.honT v h fc fu HM μ).NH_nonneg Ψ
  have hρle : ρ ≤ 3 * μ / 2 := by rw [← hμeq]; exact hρ.2.2
  have heps1 : Work.BoseRowQ2.fsEps v 58982400 μ ≤ 1 / 2 := by
    rw [heps]; exact har0
  have hμapos : 0 < μ * _root_.BoseGases.a v := mul_pos hμ hav
  have ht3nn : 0 ≤ (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ) :=
    Real.rpow_nonneg (le_of_lt ht0) _
  have hW0bound : ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
      ≤ (μ * _root_.BoseGases.a v) * 24 * Real.pi := by
    calc ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        ≤ (3 * μ / 2) * (16 * Real.pi * _root_.BoseGases.a v) :=
          mul_le_mul hρle hW0le hW0nn (by positivity)
      _ = (μ * _root_.BoseGases.a v) * 24 * Real.pi := by ring
  have har1' : 2 * (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ))
      ≤ (1 / 12800) * (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ) := by linarith [har1]
  have har2' : 8 * ((μ * _root_.BoseGases.a v ^ 3) ^ (302 / 323 : ℝ)
        * (R / _root_.BoseGases.a v) ^ 2)
      ≤ (1 / 12800) * (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ) := by linarith [har2]
  have harith1 : ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * (2 * Work.BoseRowQ2.fsEps v 58982400 μ + 8 * (honKappa v μ) ^ 2 * R ^ 2)
        * (48 / Real.pi)
      ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 400
          * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ)) := by
    rw [hb16, hell2, heps]
    rw [show (2 * (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ))
          + 8 * (honKappa v μ) ^ 2 * R ^ 2)
        = (2 * (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ))
          + 8 * ((honKappa v μ) ^ 2 * R ^ 2)) by ring]
    rw [hκR]
    have hcoef : 2 * (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ))
          + 8 * ((μ * _root_.BoseGases.a v ^ 3) ^ (302 / 323 : ℝ)
              * (R / _root_.BoseGases.a v) ^ 2)
        ≤ ((1 / 6400) * (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ)) / 1152 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1152)]
      linarith [har1', har2']
    calc ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          * (2 * (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ))
            + 8 * ((μ * _root_.BoseGases.a v ^ 3) ^ (302 / 323 : ℝ)
                * (R / _root_.BoseGases.a v) ^ 2))
          * (48 / Real.pi)
        ≤ ((μ * _root_.BoseGases.a v) * 24 * Real.pi)
            * (((1 / 6400) * (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ)) / 1152)
            * (48 / Real.pi) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hW0bound hcoef (by positivity) (by positivity))
            (by positivity)
      _ = (1 / 16 / 400) * ((μ * _root_.BoseGases.a v)
            * (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ)) := by
          field_simp
          ring
  have harith2 : 3 * 32 * (ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
      ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800
          * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
              * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                  * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))) := by
    rw [hb16, hgap2]
    calc 3 * 32 * (ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
        ≤ 3 * 32 * ((μ * _root_.BoseGases.a v) * 24 * Real.pi) := by linarith [hW0bound]
      _ = 2304 * Real.pi * (μ * _root_.BoseGases.a v) := by ring
      _ ≤ (1 / 12800) * (μ * _root_.BoseGases.a v ^ 3) ^ (-(13 / 1292) : ℝ)
            * (μ * _root_.BoseGases.a v) :=
          mul_le_mul_of_nonneg_right har3 (le_of_lt hμapos)
      _ = (1 / 16 / 800) * ((μ * _root_.BoseGases.a v)
            * (μ * _root_.BoseGases.a v ^ 3) ^ (-(13 / 1292) : ℝ)) := by ring
  -- the charge inequality
  have hcharge : ρ * (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
        ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k))
      ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 400
          * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).N
        + (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800
          * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
              * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                  * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Work.BoseBoxFock.Lab (HM μ).N))
      (fun k => ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ)
      (fun k => ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k))
    rw [← hsplit]
    have hcoefnn : 0 ≤ (2 * Work.BoseRowQ2.fsEps v 58982400 μ
        + 8 * (honKappa v μ) ^ 2 * R ^ 2) * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := by
      have he : 0 < Work.BoseRowQ2.fsEps v 58982400 μ := by rw [heps]; positivity
      refine mul_nonneg (by
        have hk2 : 0 ≤ (honKappa v μ) ^ 2 := sq_nonneg _
        have hR2 : 0 ≤ R ^ 2 := sq_nonneg _
        nlinarith [he, mul_nonneg hk2 hR2]) hW0nn
    have hLow : ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
            ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ)),
          ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≤ ((2 * Work.BoseRowQ2.fsEps v 58982400 μ + 8 * (honKappa v μ) ^ 2 * R ^ 2)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
          * ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
              ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ)),
              (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_filter] at hk
      have hklt : ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ := hk.2
      have h1 : (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k
          ≤ (1 / 2) * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2 * R ^ 2
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := hwkdef k
      have h2 : (1 / 2) * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2 * R ^ 2
          ≤ 8 * (honKappa v μ) ^ 2 * R ^ 2 := by
        have hx2 : ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2
            < 16 * (honKappa v μ) ^ 2 := by
          nlinarith [hklt, norm_nonneg ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k), hκpos.le]
        nlinarith [hx2, hR]
      have h3 : ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          ≤ (2 * Work.BoseRowQ2.fsEps v 58982400 μ + 8 * (honKappa v μ) ^ 2 * R ^ 2)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := by
        nlinarith [h1, h2, hW0nn]
      exact mul_le_mul_of_nonneg_right h3
        (Work.BoseB7.FockData.nOp_qw_nonneg' _ k Ψ)
    have hHigh : ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
            ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
          ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≤ 3 * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          * ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
              ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
              (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have h1 : -(Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k := hwkge k
      have h3 : ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          ≤ 3 * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := by
        nlinarith [h1, heps1, hW0nn]
      exact mul_le_mul_of_nonneg_right h3
        (Work.BoseB7.FockData.nOp_qw_nonneg' _ k Ψ)
    have hA_low : ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
            ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ)),
          (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≤ (48 / Real.pi) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            (Work.BoseRowsFS.honT v h fc fu HM μ).N := by
      calc _ ≤ ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
              (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun k _ _ => Work.BoseB7.FockData.nOp_qw_nonneg' _ k Ψ)
        _ ≤ _ := hBessel
    have hL : ρ * ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
            ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ)),
          ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 400
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).N := by
      have h1 := mul_le_mul_of_nonneg_left hLow hρ.1
      have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA_low hcoefnn) hρ.1
      have h3 := mul_le_mul_of_nonneg_right harith1 hNvnn
      have h4 : ρ * (((2 * Work.BoseRowQ2.fsEps v 58982400 μ
              + 8 * (honKappa v μ) ^ 2 * R ^ 2)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
            * ((48 / Real.pi) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).N))
          = (ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
              * (2 * Work.BoseRowQ2.fsEps v 58982400 μ + 8 * (honKappa v μ) ^ 2 * R ^ 2)
              * (48 / Real.pi)) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).N := by ring
      linarith [h1, h2, h3, h4]
    have hH : ρ * ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
            ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
          ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800
            * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                    * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by
      have h1 := mul_le_mul_of_nonneg_left hHigh hρ.1
      have h2 := mul_le_mul_of_nonneg_left hHle
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hρ.1) hW0nn)
      have h3 := mul_le_mul_of_nonneg_right harith2 hNHvnn
      have h4 : ρ * (3 * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            * (32 * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).NH))
          = (3 * 32 * (ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0))
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by ring
      linarith [h1, h2, h3, h4]
    linarith [hL, hH]
  -- the algebraic bridge
  have hbridge : 2 * ρ * (1 + Work.BoseRowQ2.fsEps v 58982400 μ)
        * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
      = (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
              (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
        + ρ * (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
            ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
                * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
              - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)) := by
    rw [hAunf, hQunf]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  linarith [hcharge, hbridge]

end Work.BoseRowQ2
