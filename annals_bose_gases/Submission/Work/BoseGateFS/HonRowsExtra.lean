import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.W1low.W1_low_nonneg
import Submission.Work.BoseB7AK.W1rows.W1omega0_rows
import Submission.Work.BoseGateFS.KinkFSHonest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.HonRowsExtra` — the potential rows of the honest gate

Two of the honest §11/§12 rows of `HonestRows` are *theorems* at the honest model,
once the corresponding FS §4/§11 estimates are available:

* **`honE_W1omega0`** — `0 ≤ Ŵ₁ω(0) ≤ 16π·a`: the honest environment's
  `W1omega0 = chat (W1omegaFun v h (ellH v μ)) 0`, which is
  `Work.BoseB7AK.W1rows.W1omega0_rows` (`C = 16π`), the nonnegativity of
  `g₀ω = v(1-ω)ω` a.e. and the mass bound `∫g₀ω ≤ 8πa`;
* **`honE_W1low`** — FS's low-momentum positivity of `Ŵ₁` at the honest model:
  below `1/(4K_Ha)` the UV cut `ζ_Λ` is `1` (`Λ ≥ 1/(4K_Ha)`) and
  `Ŵ₁ ≥ 0` provided `‖k‖R ≤ 1/2` (`R ≤ 2K_Ha`), which is
  `Work.BoseB7AK.W1low.W1_low_nonneg`.

Both are stated with the two *threshold* hypotheses (`R ≤ 2K_Ha`,
`1/(4K_Ha) ≤ Λ_N`) that the final assembly folds into its `εg`/`Ng`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
variable {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ}

/-! ## 1. `Ŵ₁ω(0)` at the honest model -/

/-- The honest `W1omega0` is `chat (W1omegaFun v h (ellH v μ)) 0`. -/
theorem honE_W1omega0_eq (S : HonSetup v h fc fu HM μ) :
    (honE v h fc fu HM μ).W1omega0
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ)) 0 := by
  rw [ellH_eq_sideAt S]
  rfl

/-- **FS `0 ≤ Ŵ₁ω(0) ≤ Ca` at the honest model**, `C = 16π`. -/
theorem honE_W1omega0 (S : HonSetup v h fc fu HM μ) {R : ℝ} (hR : 0 < R)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    0 ≤ (honE v h fc fu HM μ).W1omega0
      ∧ (honE v h fc fu HM μ).W1omega0 ≤ 16 * Real.pi * a v := by
  have hℓ : (0 : ℝ) < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hWnn : ∀ᵐ z ∂(volume : Measure ℝ³),
      0 ≤ Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) z := by
    filter_upwards [Work.BoseB7AK.W1rows.W1omegaNum_nonneg_ae hR hv_nonneg hvrad hv_supp h]
      with z hz
    rw [Work.BoseB7AK.W1rows.W1omegaFun_eq]
    dsimp only [Submission.BoseGases.wScaled]
    rw [div_eq_mul_inv]
    exact mul_nonneg hz (inv_nonneg.mpr (Submission.BoseGases.convScale_nonneg _ z))
  rw [honE_W1omega0_eq S, Work.BoseB7AK.W1rows.chat_zero]
  refine ⟨MeasureTheory.integral_nonneg_of_ae hWnn, ?_⟩
  calc (∫ z, Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) z)
      = ∫ z, |Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) z| := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hWnn] with z hz
        exact (abs_of_nonneg hz).symm
    _ ≤ 16 * Real.pi * a v :=
        Work.BoseB7AK.W1rows.W1omega_abs_integral_le hR hℓ hv_nonneg hvrad hv_supp h hRℓ

/-! ## 2. FS's low-momentum positivity at the honest model -/

/-- **`W1low` at the honest model.**  With `Λ_N ≥ 1/(4K_Ha)` the cut `ζ_Λ` equals
`1` below the `P_H^q` threshold, and `R ≤ 2K_Ha` makes `‖k‖R ≤ 1/2` there, so
FS's quadratic estimate `0 ≤ Ŵ₁(k)` (`‖k‖R ≤ 1/2`) applies verbatim. -/
theorem honE_W1low (S : HonSetup v h fc fu HM μ) {R : ℝ} (hR : 0 < R)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (hR0 : R ≤ 2 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
    (hΛ : 1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
      ≤ uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N) :
    ∀ k : Lab (HM μ).N,
      ‖(honF v h fc fu HM μ).kmom k‖
          ≤ 1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) →
        0 ≤ (honE v h fc fu HM μ).W1 k := by
  intro k hk
  have hKH : 0 < (honE v h fc fu HM μ).KH := lt_of_lt_of_le one_pos S.hv.one_le_KH
  have ha : 0 < (honE v h fc fu HM μ).aScat := S.hv.a_pos
  have hden : 0 < 4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat := by positivity
  have hΛpos : 0 < uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N :=
    lt_of_lt_of_le (div_pos one_pos hden) hΛ
  have hζ : uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
      ((honF v h fc fu HM μ).kmom k) = 1 := by
    refine fu.one _ ?_
    rw [div_le_one hΛpos]
    exact le_trans hk hΛ
  have hkR : ‖(honF v h fc fu HM μ).kmom k‖ * R ≤ 1 / 2 := by
    have h1 : ‖(honF v h fc fu HM μ).kmom k‖ * R
        ≤ (1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)) * R :=
      mul_le_mul_of_nonneg_right hk hR.le
    have h2 : (1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)) * R
        ≤ (1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat))
            * (2 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) :=
      mul_le_mul_of_nonneg_left hR0 (by positivity)
    have h3 : (1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat))
        * (2 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) = 1 / 2 := by
      field_simp
      norm_num
    linarith [h1, h2, h3.le, h3.ge]
  rw [honE_W1_apply S k, hζ, one_mul]
  exact Work.BoseB7AK.W1low.W1_low_nonneg hR (Work.BoseBoxFock.ellH_pos v μ) hv_nonneg hvrad
    hv_supp h hRℓ hkR

end Work.BoseGateFS
