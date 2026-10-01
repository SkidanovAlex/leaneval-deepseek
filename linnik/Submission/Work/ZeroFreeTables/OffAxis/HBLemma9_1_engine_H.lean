/-
# `ZeroFreeTables/OffAxis/HBLemma9_1_engine_H` — HB Lemma 9.1 / (9.13) at height `H`

The height-parametric form of HB Lemma 9.1: the engine `HBLemma9_1Wide`
(`HB94/Lam0GeEngine.lean`) with the working region `Is1Z`/height literals replaced by the
parameters `H`, `W` of `Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁` and with the real-character
case `χ₁ ^ 2 = 1` (HB's case `χ₁² = χ₀`, including the degenerate sub-case `ρ₀` real) added.

The analytic ingredients are the height-parametric point bounds
(`OffAxis/HBLemma9_1_engine_H_real.lean`: `k1_input_gen`, `point_bound_prim_R`,
`point_bound_q_R`, `point_bound_principal_H`) built on the height-parametric dropping rule
`OffAxis/nearP3sum_ge_kept_R` and the height-parametric `ζ`-inputs
(`OffAxis/zetaZeroFreeStripH`, `OffAxis/zetaLogDerivPoleSplitH`); the three numerical
reductions are `caseA_bridge`/`caseB_bridge`/`caseC_bridge` of `HB94/Lam0GeEngine.lean`
together with `caseC_bridge_zero` for the degenerate real-`ρ₀` sub-case.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.CaseC_D
import Submission.Work.ZeroFreeTables.P3.SideConditions
import Submission.Work.ZeroFreeTables.P9.rescale_variants
import Submission.Work.ZeroFreeTables.P9.HbCombinationL_nonneg
import Submission.Work.ZeroFreeTables.P9.InvNearSum_anti
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le
import Submission.Work.ZeroFreeTables.P9.parity_bound_re
import Submission.Work.ZeroFreeTables.P9.absorption_eventual
import Submission.Work.ZeroFreeTables.OffAxis.zetaZeroFreeStripH
import Submission.Work.ZeroFreeTables.OffAxis.zetaLogDerivPoleSplitH
import Submission.Work.ZeroFreeTables.OffAxis.nearP3sum_ge_kept_R
import Submission.Work.ZeroFreeTables.OffAxis.pointEngine_prim_gen
import Submission.Work.ZeroFreeTables.OffAxis.invNearSum_eq_tsum_gen
import Submission.Work.ZeroFreeTables.HB94.Lam0GeEngine
import Submission.Work.A7.zeroMult_conj_sq_one
import Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.LinnikAreas.area1
import Submission.Work.LinnikAreas2.D2Aux
import Submission.Work.ZeroFreeTables.Table4.zeroMult_changeLevel

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 8000000

namespace Work.ZeroFreeTables.HB91Aux

open Work.ZeroFreeTables.P9
open Work.LinnikContract
open Work.ZeroFreeTables.OffAxis

theorem k1_input_gen {L₀ δ₀ δ ε₁ a L : ℝ}
    (h31 : ∀ {M : ℕ} [NeZero M], 3 ≤ M → ∀ (χ : DirichletCharacter ℂ M), χ ≠ 1 →
      χ.IsPrimitive →
      ∀ {L : ℝ}, L₀ ≤ L → Real.log (M : ℝ) ≤ L → ∀ s : ℂ,
        1 + 1 / (L * Real.log L) ≤ s.re → s.re ≤ 1 + Real.log L / L → |s.im| ≤ 10 * L →
        (-logDeriv (DirichletCharacter.LFunction χ) s).re
          + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
              (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ₀ then ((1 / (s - u)).re) else 0))
          ≤ (1 / 6 + ε₁) * L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    (hN3 : 3 ≤ N) (hL0 : L₀ ≤ L) (hlogN : Real.log (N : ℝ) ≤ L)
    (hδδ₀ : δ ≤ δ₀) (hδ₀1 : δ₀ ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : 0 < a) (hL1 : 1 ≤ L) (h1 : 1 ≤ a * Real.log L) (h2 : a ≤ Real.log L)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 10 * L) :
    (-logDeriv (DirichletCharacter.LFunction χ) s).re + P9.nearInvSum N χ s δ
      ≤ (1 / 6 + ε₁) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hlogLpos : 0 < Real.log L := by nlinarith [h1, ha]
  have hs1 : 1 + 1 / (L * Real.log L) ≤ s.re := by
    rw [hsre]
    have hkey : 1 / (L * Real.log L) ≤ a / L := by
      field_simp
      nlinarith [h1, hLpos]
    linarith
  have hs2 : s.re ≤ 1 + Real.log L / L := by
    rw [hsre]
    have h3 : a / L ≤ Real.log L / L := div_le_div_of_nonneg_right h2 hLpos.le
    linarith
  have h31' := h31 hN3 χ hχ hprim hL0 hlogN s hs1 hs2 hsim
  have hre1 : (1 : ℝ) ≤ s.re := by
    rw [hsre]
    have h4 : 0 ≤ a / L := div_nonneg ha.le hLpos.le
    linarith
  have hmono : InvNearSum N χ s δ ≤ InvNearSum N χ s δ₀ :=
    P9.InvNearSum_anti χ hχ hprim hre1 hδδ₀ hδ₀1
  have heq : InvNearSum N χ s δ = P9.nearInvSum N χ s δ :=
    invNearSum_eq_tsum_gen χ hχ hprim hδ0 hδ1
  rw [heq] at hmono
  simp only [InvNearSum, pdiv] at hmono
  linarith [h31', hmono]

/-! ## The point bound with room `R`

`point_bound_prim` of `HBLemma9_1_proof.lean` with the height literal `3` replaced by a
parameter `R` (and the dropping radius `10` by `R + 1`): the test point has `|Im s| ≤ R`, the
kept zeros have `|Im u| ≤ R + 1`, and `λ₁` is minimal at height `≤ R + 1`. -/

theorem point_bound_prim_R {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {L a lam₁ δ c Ct Cj R : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L)
    (haδL : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ R)
    (hlog : (-logDeriv (DirichletCharacter.LFunction χ) s).re
      + P9.nearInvSum N χ s δ ≤ c * L)
    (par : ℕ) (hpar0 : χ.Even → par = 0) (hpar1 : χ.Odd → par = 1)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    (hJ : P9.invSqSum N χ s ≤ Cj)
    (hmin : ∀ u : ℂ, zeroMult χ u ≠ 0 → |u.im| ≤ R + 1 → lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, zeroMult χ u ≠ 0)
    (hTim : ∀ u ∈ T, |u.im| ≤ R + 1) :
    SigmaP3L N L χ s a lam₁
      ≤ -(∑ u ∈ T, (P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re)
        + (a + lam₁) * c + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct)
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
  have h1 := pointEngine_prim_gen χ hχ hprim ha hlam₁ hδ hδ1 hLt haδL hsre hlog
    par hpar0 hpar1 hS2 hS3
  have h2 := nearP3sum_ge_kept_R χ hχ (by linarith) ha hlam₁ hδ hδ1 haδL hsre hsim hmin T hT hTim
  have hw : (0 : ℝ) ≤ 1 + 4 / δ ^ 2 := by positivity
  have hc1 : ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * P9.invSqSum N χ s + Ct)
      ≤ ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [mul_le_mul_of_nonneg_left hJ hw]
  have hc2 : (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3)
        * ((2 / δ) * (1 + 4 / δ ^ 2) * P9.invSqSum N χ s + Ct)
      ≤ (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hw2 : (0 : ℝ) ≤ (2 / δ) * (1 + 4 / δ ^ 2) := by positivity
    linarith [mul_le_mul_of_nonneg_left hJ hw2]
  linarith [h1, h2, hc1, hc2]

/-- `changeLevel` of a non-principal character is non-principal. -/
theorem changeLevel_ne_one_R {N q : ℕ} [NeZero q] [NeZero N] (hNq : N ∣ q)
    (φ : DirichletCharacter ℂ N) (hφ : φ ≠ 1) :
    DirichletCharacter.changeLevel hNq φ ≠ 1 :=
  fun h => hφ ((DirichletCharacter.changeLevel_eq_one_iff hNq).mp h)

/-- **The point bound at an imprimitive character, with room `R`.** -/
theorem point_bound_q_R {q N : ℕ} [NeZero q] [NeZero N] (hNq : N ∣ q)
    (φ : DirichletCharacter ℂ N) (hφ : φ ≠ 1) (hprim : φ.IsPrimitive)
    {a lam₁ δ L c Ct Cj Cc R : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L)
    (haδL : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ R)
    (hlog : (-logDeriv (DirichletCharacter.LFunction φ) s).re
        + P9.nearInvSum N φ s δ ≤ c * L)
    (par : ℕ) (hpar0 : φ.Even → par = 0) (hpar1 : φ.Odd → par = 1)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    (hJ : P9.invSqSum N φ s ≤ Cj)
    (hmin : ∀ u : ℂ, zeroMult φ u ≠ 0 → |u.im| ≤ R + 1 →
      lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, zeroMult φ u ≠ 0)
    (hTim : ∀ u ∈ T, |u.im| ≤ R + 1)
    (hcorr : |SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) s a lam₁
        - SigmaP3L N L φ s a lam₁| ≤ Cc) :
    SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) s a lam₁
      ≤ -(∑ u ∈ T, (P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re) + (a + lam₁) * c
        + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct)
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) + Cc := by
  have h1 := point_bound_prim_R φ hφ hprim ha hlam₁ hδ hδ1 hLt haδL hsre hsim
    hlog par hpar0 hpar1 hS2 hS3 hJ hmin T hT hTim
  have h2 : SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) s a lam₁
      ≤ SigmaP3L N L φ s a lam₁ + Cc := by
    have h := (abs_le.mp hcorr).2
    linarith
  linarith [h1, h2]

/-- **The point bound at the principal character, with height parameter `T` and ball radius
`Rd`** (`point_bound_principal` with the literals `3, 4, 5` replaced by the parameters). -/
theorem point_bound_principal_H {q : ℕ} [NeZero q] {a lam₁ δ L Ct Cz C₀ Cc T Rd : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L)
    (haδL : 2 * a ≤ δ * L) (haL : a ≤ L)
    (hCz : ∀ s : ℂ, ‖s‖ ≤ Rd → (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ)
        * (1 / (1 + ‖s - u‖ ^ 2))) ≤ Cz)
    (hC0 : ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ T →
        (-logDeriv riemannZeta s).re ≤ (1 / (s - 1)).re + C₀)
    (hnz : ∀ t : ℝ, |t| ≤ T → ∀ u : ℂ, riemannZeta u = 0 →
        δ < ‖(1 : ℂ) + (t : ℂ) * Complex.I - u‖)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ T) (hsnorm : ‖s‖ ≤ Rd)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    (hcorr : |SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
        - SigmaP3L 1 L 1 s a lam₁| ≤ Cc) :
    SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      ≤ (P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re + ((a + lam₁) / L) * C₀
        + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) + Cc := by
  have hLpos : 0 < L := lt_trans zero_lt_one hLt
  have hsre2 : s.re ≤ 2 := by
    rw [hsre]
    have hdiv : a / L ≤ 1 := div_le_one_of_le₀ haL hLpos.le
    linarith
  have hsre1 : 1 < s.re := by rw [hsre]; have : 0 < a / L := div_pos ha hLpos; linarith
  have h1 := P9.zetaEngine_principal (a := a) (lam₁ := lam₁) (δ := δ) (L := L)
    (Ct := Ct) (Cz := Cz) (C₀ := C₀) ha hlam₁ hδ hδ1 hLt haδL hsre
    (fun u hu => hnz s.im hsim u hu)
    (hC0 s hsre1 hsre2 hsim) (hCz s hsnorm) hS2 hS3
  have h2 : SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      ≤ SigmaP3L 1 L 1 s a lam₁ + Cc := by
    have h := (abs_le.mp hcorr).2
    linarith
  linarith [h1, h2]

/-- **The `γ₀ = 0` variant of `caseC_bridge`.**  When the second zero `ρ₀` is real, the point
bound at `σ + iγ₁` provides only a *single* `λ₀`-term (of `Δ = β`); the drop-out expression
correspondingly loses the second `K Φ(α,λ₀,β)`. -/
theorem caseC_bridge_zero {a lam₁ lam₀ K ε ε₁ Δ β γ : ℝ}
    {S1 S2 S3 S4 S5 S6 S7 S8 e1 e2 e3 e4 e5 e6 e7 e8 corr : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ a + lam₁) (hβΔ : β = Δ)
    (h1 : S1 ≤ P3R ((a + lam₁) / a) + e1)
    (h2 : S2 ≤ -P3R ((a + lam₁) / (a + lam₀)) - P9.PhiG (a + lam₁) (a + lam₁) Δ
        - P9.PhiG (a + lam₁) (a + lam₁) β + (a + lam₁) * (1 / 6 + ε₁) + e2)
    (h3 : S3 ≤ P9.PhiG (a + lam₁) a Δ + e3)
    (h4 : S4 ≤ -P3R 1 - P9.PhiG (a + lam₁) (a + lam₀) Δ - P9.PhiG (a + lam₁) (a + lam₁) γ
        + (a + lam₁) * (1 / 6 + ε₁) + e4)
    (h5 : S5 ≤ P9.PhiG (a + lam₁) a β + e5)
    (h6 : S6 ≤ -P9.PhiG (a + lam₁) (a + lam₁) Δ - P9.PhiG (a + lam₁) (a + lam₀) γ
        + (a + lam₁) * (1 / 6 + ε₁) + e6)
    (h7 : S7 ≤ P9.PhiG (a + lam₁) a γ + e7)
    (h8 : S8 ≤ -P9.PhiG (a + lam₁) (a + lam₁) β - P9.PhiG (a + lam₁) (a + lam₀) γ
        + (a + lam₁) * (1 / 6 + ε₁) + e8)
    (hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
        + (1 / 4) * (S6 + 2 * S7 + S8) + corr)
    (hExpr : 0 ≤
        (K ^ 2 + 3 / 4) * P9.PhiG (a + lam₁) (a + lam₁) Δ
          + K * P9.PhiG (a + lam₁) (a + lam₀) Δ - K * P9.PhiG (a + lam₁) a Δ
        + ((K ^ 2 + 3 / 4) * P9.PhiG (a + lam₁) (a + lam₁) β
          + K * P9.PhiG (a + lam₁) (a + lam₀) β - K * P9.PhiG (a + lam₁) a β)
        + (2 * K * P9.PhiG (a + lam₁) (a + lam₁) γ
          + (1 / 2) * P9.PhiG (a + lam₁) (a + lam₀) γ - (1 / 2) * P9.PhiG (a + lam₁) a γ)
        + K * P9.PhiG (a + lam₁) (a + lam₀) Δ
        - K * P9.PhiG (a + lam₁) (a + lam₀) β)
    (habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5) + (1 / 4) * (e6 + 2 * e7 + e8)
        + corr + (a + lam₁) * ε₁ * (K ^ 2 + 2 * K + 1) ≤ (a + lam₁) * ε) :
    ineq913 lam₁ lam₀ a K ε := by
  subst hβΔ
  rw [ineq913, p913, psi13] at *
  have hK0 : 0 ≤ K ^ 2 + 1 / 2 := by positivity
  have h14 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  nlinarith [hcomb, h1, h2, h3, h4, h5, h6, h7, h8, hExpr, habs, hK0, h14, hα, hK]

/-- A two-element `Finset` sum. -/
theorem sum_pair_eq {f : ℂ → ℝ} {a b : ℂ} (hab : a ≠ b) :
    ∑ u ∈ ({a, b} : Finset ℂ), f u = f a + f b := by
  rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton]

/-- A three-element `Finset` sum (the elements being distinct). -/
theorem sum_three_eq {f : ℂ → ℝ} {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ u ∈ ({a, b, c} : Finset ℂ), f u = f a + f b + f c := by
  have h1 : a ∉ ({b, c} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, hac⟩
  have h2 : b ∉ ({c} : Finset ℂ) := by
    simpa using hbc
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  ring

/-- A four-element `Finset` sum (the elements being distinct). -/
theorem sum_four_eq {f : ℂ → ℝ} {a b c d : ℂ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∑ u ∈ ({a, b, c, d} : Finset ℂ), f u = f a + f b + f c + f d := by
  have h1 : a ∉ ({b, c, d} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, hac, had⟩
  have h2 : b ∉ ({c, d} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hbc, hbd⟩
  have h3 : c ∉ ({d} : Finset ℂ) := by
    simpa using hcd
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_singleton]
  ring

/-- A sum of five terms is bounded termwise. -/
theorem sum5_le {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : ℝ}
    (h1 : A1 ≤ B1) (h2 : A2 ≤ B2) (h3 : A3 ≤ B3) (h4 : A4 ≤ B4) (h5 : A5 ≤ B5) :
    A1 + A2 + A3 + A4 + A5 ≤ B1 + B2 + B3 + B4 + B5 := by
  linarith only [h1, h2, h3, h4, h5]

/-- The card of an explicit set of at most three complex numbers. -/
theorem card_three_le (a b c : ℂ) : ((({a, b, c} : Finset ℂ)).card : ℝ) ≤ 3 := by
  have h1 := Finset.card_insert_le a ({b, c} : Finset ℂ)
  have h2 := Finset.card_insert_le b ({c} : Finset ℂ)
  have h3 : ({c} : Finset ℂ).card = 1 := Finset.card_singleton c
  have : ({a, b, c} : Finset ℂ).card ≤ 3 := by omega
  exact_mod_cast this

/-- The card of an explicit set of at most four complex numbers. -/
theorem card_four_le (a b c d : ℂ) : ((({a, b, c, d} : Finset ℂ)).card : ℝ) ≤ 4 := by
  have h1 := Finset.card_insert_le a ({b, c, d} : Finset ℂ)
  have h2 := Finset.card_insert_le b ({c, d} : Finset ℂ)
  have h3 := Finset.card_insert_le c ({d} : Finset ℂ)
  have h4 : ({d} : Finset ℂ).card = 1 := Finset.card_singleton d
  have : ({a, b, c, d} : Finset ℂ).card ≤ 4 := by omega
  exact_mod_cast this


end Work.ZeroFreeTables.HB91Aux

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables.HB94.Lam0GeEngine
open Work.ZeroFreeTables.HB91Aux

theorem HBLemma9_1_engine_H : ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ H → ρ₁ ≠ ρ₀ →
      (χ₁ ^ 2 = 1 → ρ₀ ≠ starRingEnd ℂ ρ₁) →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K ε := by
  intro a K ε ha hK hε H W hH1 hHW
  -- ## the room `R = 3H` of the eight test points, and `R + 1 ≤ W`
  set R : ℝ := 3 * H with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; linarith
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRW : R + 1 ≤ W := by rw [hRdef]; linarith
  have hHW' : H ≤ W := by linarith
  -- ## the constants
  set ε₁ : ℝ := ε / (4 * (K ^ 2 + 3 * K + 4)) with hε₁def
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; positivity
  have hε₁bud : ε₁ * (K ^ 2 + 3 * K + 3 / 2) ≤ ε / 4 := by
    rw [hε₁def, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (K ^ 2 + 3 * K + 4))]
    nlinarith [hε.le, sq_nonneg K, hK.le]
  have hε₁budC : ε₁ * (K ^ 2 + 2 * K + 1) ≤ ε / 4 := by
    have h2 : (K : ℝ) ^ 2 + 2 * K + 1 ≤ K ^ 2 + 3 * K + 3 / 2 := by nlinarith [hK.le]
    exact le_trans (mul_le_mul_of_nonneg_left h2 hε₁pos.le) hε₁bud
  obtain ⟨L₀, δ₀, hδ₀pos, hδ₀lt1, h31⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := 1 / 3) (by norm_num) hε₁pos
      Work.LinnikAreas.LBound13_holds
  obtain ⟨Ct, hCtpos, hCtS⟩ := P9.parity_bound_re
  obtain ⟨Czk, hCzkpos, hCzk⟩ := Work.LinnikAreas.FarRepel.zetaHalfKernelBound
  set Rd : ℝ := 5 * H + 2 with hRddef
  have hRd3 : R + 2 ≤ Rd := by rw [hRdef, hRddef]; linarith
  have hRdpos : 0 < Rd := by rw [hRddef]; linarith
  set Cz : ℝ := Czk * (Real.log (2 + Rd) + 2) + 1 with hCzdef
  have hCzpos : 0 < Cz := by
    rw [hCzdef]
    have h1 : (0 : ℝ) < Real.log (2 + Rd) + 2 := by
      have h2 : Real.log (2 + Rd) ≥ 0 := Real.log_nonneg (by linarith)
      linarith
    positivity
  have hCzZeta : ∀ s : ℂ, ‖s‖ ≤ Rd →
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
        ≤ Cz := by
    intro s hs
    have h := (hCzk s).2
    have hlog : Real.log (2 + ‖s‖) ≤ Real.log (2 + Rd) :=
      Real.log_le_log (by positivity) (by linarith [norm_nonneg s])
    rw [hCzdef]
    have h2 : Czk * (Real.log (2 + ‖s‖) + 2) ≤ Czk * (Real.log (2 + Rd) + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hCzkpos.le
    linarith only [h, h2]
  obtain ⟨C₀, hC₀pos, hC₀b⟩ := zetaLogDerivPoleSplitH R hRpos.le
  obtain ⟨Cc, hCcpos, hCc⟩ := P9.SigmaP3L_changeLevel_diff
  obtain ⟨Cp1, hCp1pos, hCp1⟩ := P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨Cp2, hCp2pos, hCp2⟩ := P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨Cp3, hCp3pos, hCp3⟩ := P9.primeFactors_logPow_div_le 3 (by norm_num)
  set Cp : ℝ := max (max Cp1 Cp2) Cp3 with hCpdef
  have hCpnn : 0 ≤ Cp := by rw [hCpdef]; positivity
  have hCp1le : Cp1 ≤ Cp := by rw [hCpdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCp2le : Cp2 ≤ Cp := by rw [hCpdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCp3le : Cp3 ≤ Cp := by rw [hCpdef]; exact le_max_right _ _
  obtain ⟨Cq, hCqpos, hCq⟩ := Work.ZeroFreeTables.HB94.Lam0GeEngine.invSqSum_uniform
  set Cn : ℝ := max Cq 1 with hCndef
  have hCnpos : 0 < Cn := by rw [hCndef]; positivity
  have hCqle : Cq ≤ Cn := by rw [hCndef]; exact le_max_left _ _
  obtain ⟨εζ, hεζpos, hεζ⟩ := zetaZeroFreeStripH (4 * H + 1) (by linarith)
  set δ : ℝ := min δ₀ (min (εζ / 2) (1 / 2)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (lt_min (by linarith only [hεζpos]) (by norm_num))
  have hδleδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδleζ : δ ≤ εζ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδlehalf : δ ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hδlt1 : δ < 1 := lt_of_le_of_lt hδlehalf (by norm_num)
  set aup : ℝ := (a ^ 3 * (Kond K + 1)) ^ (1 / 3 : ℝ) with haupdef
  have hauppos : 0 < aup := by
    rw [haupdef]
    exact Real.rpow_pos_of_pos (by
      have h1 : 0 < Kond K := lt_min (by positivity) (by positivity)
      positivity) _
  obtain ⟨qabs, habs⟩ := P9.absorption_eventual a K ε aup δ C₀ Ct (3 * Cn) Cz Cc Cp
    ha hK.le hε hδpos hauppos hC₀pos.le hCtpos (by positivity) hCzpos hCcpos.le hCpnn
  set Λ : ℝ := max (max (max L₀ (2 * a / δ))
    (max (max a 10) (Real.exp (max (1 / a) (max a 1))))) H with hΛdef
  refine ⟨max qabs (max 3 (Nat.ceil (Real.exp Λ))), ?_⟩
  intro q hq hqne χ₁ ρ₁ ρ₀ hHL hmin hnc hzm0 him0 hne hconj hcond
  have hqq : 3 ≤ q := by have h := hq; simp only [max_le_iff] at h; exact h.2.1
  have hqexp : Nat.ceil (Real.exp Λ) ≤ q := by
    have h := hq; simp only [max_le_iff] at h; exact h.2.2
  have hΛL : Λ ≤ Real.log q := by
    have h1 : Real.exp Λ ≤ (q : ℝ) :=
      le_trans (Nat.le_ceil (Real.exp Λ)) (by exact_mod_cast hqexp)
    rw [← Real.log_exp Λ]
    exact Real.log_le_log (Real.exp_pos Λ) h1
  set L : ℝ := Real.log q with hLdef
  have hHL' : H ≤ L := le_trans (le_max_right _ _) hΛL
  have hΛA : max (max L₀ (2 * a / δ)) (max (max a 10) (Real.exp (max (1 / a) (max a 1)))) ≤ L :=
    le_trans (le_max_left _ _) hΛL
  have hL₀L : L₀ ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛA
  have h2aδL : 2 * a / δ ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛA
  have haL : a ≤ L := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hΛA
  have hexpL : Real.exp (max (1 / a) (max a 1)) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΛA
  have heL : Real.exp 1 ≤ L := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hexpL
    exact le_trans (le_max_right a 1) (le_max_right (1 / a) (max a 1))
  have hLt : 1 < L := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr one_pos) heL
  have hLpos : 0 < L := lt_trans zero_lt_one hLt
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hL1 : 1 ≤ L := le_of_lt hLt
  have hlogLnn : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlogLmax : max (1 / a) (max a 1) ≤ Real.log L := by
    rw [← Real.log_exp (max (1 / a) (max a 1))]
    exact Real.log_le_log (Real.exp_pos _) hexpL
  have hlogL1a : 1 / a ≤ Real.log L := le_trans (le_max_left _ _) hlogLmax
  have hlogLa : a ≤ Real.log L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlogLmax
  have h1aL : 1 ≤ a * Real.log L := by
    have h := mul_le_mul_of_nonneg_left hlogL1a ha.le
    have h2 : a * (1 / a) = 1 := by field_simp
    linarith only [h, h2]
  have haδL : 2 * a ≤ δ * L := by
    rw [div_le_iff₀ hδpos] at h2aδL
    linarith only [h2aδL]
  have hnormR : ∀ t : ℝ, |t| ≤ R → ‖sPt a L t‖ ≤ Rd := by
    intro t ht
    have h1 : (sPt a L t).re = 1 + a / L := by simp [sPt]
    have h2 : (sPt a L t).im = t := by simp [sPt]
    have h3 : 1 + a / L ≤ 2 := by
      have h : a / L ≤ 1 := div_le_one_of_le₀ haL hLpos.le
      linarith
    have h5 : ‖sPt a L t‖ ≤ |(sPt a L t).re| + |(sPt a L t).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    rw [h1, h2] at h5
    have h6 : |1 + a / L| ≤ 2 := abs_le.mpr ⟨by
      have : 0 ≤ a / L := div_nonneg ha.le hLpos.le
      linarith, h3⟩
    rw [hRdef] at ht
    rw [hRddef]
    linarith only [h5, h6, ht, hH1]
  -- ## the error constants
  set Cj : ℝ := Cn * (3 * L + 8) + Cz with hCjdef
  have hCjnn : 0 ≤ Cj := by rw [hCjdef]; positivity
  set Sp1 : ℝ := ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) with hSp1def
  set Sp2 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) with hSp2def
  set Sp3 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) with hSp3def
  set Corr : ℝ := (Cc / L) * ((a + (Work.LinnikContract.lamOf q ρ₁)) * Sp1
    + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L) * Sp2
    + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 2) * Sp3) with hCorrdef
  set E : ℝ := P9.Brack aup δ C₀ Ct (3 * Cn) Cz Cc Cp q with hEdef
  have hEbound : 2 * (K + 1) ^ 2 * E ≤ a * ε / 2 := by
    rw [hEdef]
    exact habs q (by have hh := hq; simp only [max_le_iff] at hh; omega)
  have hCj_le : Cj ≤ 3 * Cn * (L + 6) + Cz := by
    rw [hCjdef]; nlinarith only [hCnpos.le, hLpos.le]
  -- ## basic bounds
  have hχ₁ne : χ₁ ≠ 1 := hmin.1
  have hzm₁ : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin.2.1
  have hγ₁ : |ρ₁.im| ≤ H := hmin.2.2.1
  have hlam₁nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.ZeroFreeTables.HB94.Lam0GeEngine.lamOf_nonneg_of_zeroMult hzm₁
  have hlam₀nn : 0 ≤ Work.LinnikContract.lamOf q ρ₀ :=
    Work.ZeroFreeTables.HB94.Lam0GeEngine.lamOf_nonneg_of_zeroMult hzm0
  have hlam₁lam₀ : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ :=
    hmin.2.2.2 χ₁ ρ₀ hχ₁ne hzm0 (le_trans him0 hHW')
  have hα0 : 0 ≤ a + Work.LinnikContract.lamOf q ρ₁ := by linarith only [ha, hlam₁nn]
  have hαaup : a + Work.LinnikContract.lamOf q ρ₁ ≤ aup := by
    rw [haupdef]
    exact Work.ZeroFreeTables.HB94.Lam0GeEngine.alpha_le_aup ha hlam₁nn hlam₁lam₀ hcond
  have hαaup2 : (a + Work.LinnikContract.lamOf q ρ₁) ^ 2 ≤ aup ^ 2 :=
    pow_le_pow_left₀ hα0 hαaup 2
  have hαaup3 : (a + Work.LinnikContract.lamOf q ρ₁) ^ 3 ≤ aup ^ 3 :=
    pow_le_pow_left₀ hα0 hαaup 3
  have hlamOf_eq : ∀ u : ℂ, Work.LinnikContract.lamOf q u = (1 - u.re) * L := by
    intro u; rw [Work.LinnikContract.lamOf, ← hLdef]
  have hminOf : ∀ (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ u : ℂ,
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ W →
      Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L := by
    intro ψ hψ u hu him
    rw [← hlamOf_eq u]
    exact hmin.2.2.2 ψ u hψ hu him
  have hminPrim : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N), φ ≠ 1 →
      φ.IsPrimitive → ∀ u : ℂ, Work.LinnikContract.zeroMult φ u ≠ 0 → |u.im| ≤ R + 1 →
      Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L := by
    intro N _ hNq φ hφ hprim u hu him
    refine hminOf (DirichletCharacter.changeLevel hNq φ)
      (Work.ZeroFreeTables.HB94.Lam0GeEngine.changeLevel_ne_one hNq φ hφ) u ?_
      (le_trans him hRW)
    rw [Work.ZeroFreeTables.Table4.zeroMult_changeLevel hNq φ u]
    exact hu
  -- ## the families of bounds
  have hSpr : ∀ (par : ℕ), par ≤ 2 → ∀ t : ℝ,
      |∑' n : ℕ, (((1 / (sPt a L t + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct ∧
      |∑' n : ℕ, (((1 / (sPt a L t + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct := by
    intro par hpar t
    refine hCtS (sPt a L t) ?_ par hpar
    have h : (sPt a L t).re = 1 + a / L := by simp [sPt]
    rw [h]
    have : 0 ≤ a / L := div_nonneg ha.le hLpos.le
    linarith only [this]
  have hSzeta : ∀ t : ℝ,
      |∑' n : ℕ, (((1 / (sPt a L t + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2)).re| ≤ Ct ∧
      |∑' n : ℕ, (((1 / (sPt a L t + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3)).re| ≤ Ct := by
    intro t
    have h := hSpr 2 (by norm_num) t
    have hnat : ∀ n : ℕ, (2 * (n + 1) : ℕ) = 2 + 2 * n := fun n => by ring
    constructor
    · refine le_trans (le_of_eq ?_) h.1
      apply congrArg abs
      apply tsum_congr
      intro n
      rw [hnat n]
    · refine le_trans (le_of_eq ?_) h.2
      apply congrArg abs
      apply tsum_congr
      intro n
      rw [hnat n]
  have hC0b' : ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ R →
      (-logDeriv riemannZeta s).re ≤ (1 / (s - 1)).re + C₀ := hC₀b
  have hnzδ : ∀ t : ℝ, |t| ≤ R → ∀ u : ℂ, riemannZeta u = 0 →
      δ < ‖(1 : ℂ) + (t : ℂ) * Complex.I - u‖ := by
    intro t ht u hu
    by_contra hle
    push Not at hle
    have hre1 : |(1 : ℝ) - u.re| ≤ δ := by
      have h := Complex.abs_re_le_norm ((1 : ℂ) + (t : ℂ) * Complex.I - u)
      have h2 : ((1 : ℂ) + (t : ℂ) * Complex.I - u).re = 1 - u.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
      rw [h2] at h
      linarith only [h, hle]
    have him1 : |t - u.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) + (t : ℂ) * Complex.I - u)
      have h2 : ((1 : ℂ) + (t : ℂ) * Complex.I - u).im = t - u.im := by
        simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
      rw [h2] at h
      linarith only [h, hle]
    have hure : 1 - εζ ≤ u.re := by
      have h := (abs_le.mp hre1).2
      linarith only [h, hδleζ, hεζpos]
    have hure2 : u.re ≤ 2 := by
      have h := (abs_le.mp hre1).1
      linarith only [h, hδlehalf]
    have huim : |u.im| ≤ 4 * H + 1 := by
      have h1 := (abs_le.mp him1).1
      have h2 := (abs_le.mp him1).2
      have h3 := abs_le.mp ht
      have h4 : |u.im| ≤ |t| + δ := by
        calc |u.im| = |t - (t - u.im)| := by ring_nf
          _ ≤ |t| + |t - u.im| := abs_sub _ _
          _ ≤ |t| + δ := add_le_add (le_refl |t|) (abs_le.mpr ⟨h1, h2⟩)
      rw [hRdef] at h3
      have h6 : |t| ≤ 3 * H := abs_le.mpr ⟨h3.1, h3.2⟩
      have h5 := abs_le.mp h4
      rw [abs_le]
      constructor
      · linarith only [h5.1, h6, hδlehalf, hH1]
      · linarith only [h5.2, h6, hδlehalf, hH1]
    have hz : ((u.re : ℂ) + Complex.I * (u.im : ℂ)) = u := by
      rw [mul_comm]; exact Complex.re_add_im u
    exact hεζ u.im u.re huim hure hure2 (by rw [hz]; exact hu)
  have hJOf : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N), φ ≠ 1 →
      φ.IsPrimitive → ∀ s : ℂ, ‖s‖ ≤ Rd → P9.invSqSum N φ s ≤ Cj := by
    intro N _ hNq φ hφ hprim s hs
    have h1 : P9.invSqSum N φ s ≤ Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) :=
      hCq φ hφ hprim s
    have h2 : Real.log (N : ℝ) ≤ L := by
      rw [hLdef]
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      refine Real.log_le_log hNpos ?_
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hNq
    have h3 : Real.log (2 + ‖s‖) ≤ 2 * L + 6 := by
      have h7 : 2 + ‖s‖ ≤ 7 * L := by
        rw [hRddef] at hs
        linarith only [hs, hHL', heL, Real.exp_one_gt_two]
      have h8 : Real.log (2 + ‖s‖) ≤ Real.log (7 * L) :=
        Real.log_le_log (by positivity) h7
      have h9 : Real.log (7 * L) = Real.log 7 + Real.log L :=
        Real.log_mul (by norm_num) hLne
      have h10 : Real.log 7 ≤ 6 := by
        have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 by norm_num)
        linarith only [hh]
      have h11 : Real.log L ≤ L := Real.log_le_self hLpos.le
      linarith only [h8, h9, h10, h11, hLpos.le]
    have h12 : (0 : ℝ) ≤ Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2 := by
      have ha1 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
      have ha2 : (0 : ℝ) ≤ Real.log (2 + ‖s‖) :=
        Real.log_nonneg (by have h := norm_nonneg s; linarith only [h])
      linarith only [ha1, ha2]
    have h13 : Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) ≤ Cn * (3 * L + 8) := by
      have h14 : Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2 ≤ 3 * L + 8 := by linarith only [h2, h3]
      have h15 : Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) ≤ Cn * (3 * L + 8) :=
        le_trans (mul_le_mul hCqle h14 h12 hCnpos.le)
          (by nlinarith only [hCnpos.le, hLpos.le])
      exact h15
    have h16 : Cn * (3 * L + 8) ≤ Cj := by rw [hCjdef]; linarith only [hCzpos.le]
    linarith only [h1, h13, h16]
  have hCcOf : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N) (t : ℝ),
      |SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) (sPt a L t) a
          (Work.LinnikContract.lamOf q ρ₁)
        - SigmaP3L N L φ (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr := by
    intro N _ hNq φ t
    have h := hCc (hNq := hNq) (ψ := φ) (L := L) hL1 (by
      have h2 : (sPt a L t).re = 1 + a / L := by simp [sPt]
      rw [h2]
      have : 0 < a / L := div_pos ha hLpos
      linarith only [this]) (a := a) (lam₁ := Work.LinnikContract.lamOf q ρ₁) ha hlam₁nn
    rw [hCorrdef, hSp1def, hSp2def, hSp3def]
    rw [← hSp1def, ← hSp2def, ← hSp3def] at h
    exact h
  have h31' : ∀ {M : ℕ} [NeZero M], 3 ≤ M → ∀ (χ : DirichletCharacter ℂ M), χ ≠ 1 →
      χ.IsPrimitive →
      ∀ {L : ℝ}, L₀ ≤ L → Real.log (M : ℝ) ≤ L → ∀ s : ℂ,
        1 + 1 / (L * Real.log L) ≤ s.re → s.re ≤ 1 + Real.log L / L → |s.im| ≤ 10 * L →
        (-logDeriv (DirichletCharacter.LFunction χ) s).re
          + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
              (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ₀ then ((1 / (s - u)).re) else 0))
          ≤ (1 / 6 + ε₁) * L := by
    intro M _ hM χ hχ hprim L hL0 hlogN s hs1 hs2 hs3
    simpa only [show ((1 : ℝ) / 3 / 2) = 1 / 6 by norm_num] using
      h31 hM χ hχ hprim hL0 hlogN s hs1 hs2 hs3
  have hk1Of : ∀ {N : ℕ} [NeZero N] (φ : DirichletCharacter ℂ N), φ ≠ 1 → φ.IsPrimitive →
      3 ≤ N → Real.log (N : ℝ) ≤ L → ∀ t : ℝ, |t| ≤ R →
      (-logDeriv (DirichletCharacter.LFunction φ) (sPt a L t)).re
        + P9.nearInvSum N φ (sPt a L t) δ ≤ (1 / 6 + ε₁) * L := by
    intro N _ φ hφ hprim hN3 hlogN t ht
    refine HB91Aux.k1_input_gen h31' φ hφ hprim hN3 hL₀L hlogN hδleδ₀ (le_of_lt hδ₀lt1)
      hδpos (le_of_lt hδlt1) ha hL1 h1aL hlogLa (s := sPt a L t) (by simp [sPt]) ?_
    have ht' : |t| ≤ 3 * L := by rw [hRdef] at ht; linarith only [ht, hHL']
    have h10 : 3 * L ≤ 10 * L := by linarith only [hLpos.le]
    simpa [sPt] using le_trans ht' h10
  have hSp1le : Sp1 ≤ Cp * (Real.log L) ^ 2 := by
    have h := hCp1 q hqq
    rw [hSp1def]
    have h' : (Real.log (Real.log (q : ℝ))) ^ (1 + 1) = (Real.log L) ^ 2 := by rw [hLdef]
    rw [h'] at h
    simp only [pow_one] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hCp1le (by positivity))
  have hSp2le : Sp2 ≤ Cp * (Real.log L) ^ 3 := by
    have h := hCp2 q hqq
    rw [hSp2def]
    have h' : (Real.log (Real.log (q : ℝ))) ^ (2 + 1) = (Real.log L) ^ 3 := by rw [hLdef]
    rw [h'] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hCp2le (by positivity))
  have hSp3le : Sp3 ≤ Cp * (Real.log L) ^ 4 := by
    have h := hCp3 q hqq
    rw [hSp3def]
    have h' : (Real.log (Real.log (q : ℝ))) ^ (3 + 1) = (Real.log L) ^ 4 := by rw [hLdef]
    rw [h'] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hCp3le (by positivity))
  have hSpnn1 : 0 ≤ Sp1 := by rw [hSp1def]; positivity
  have hSpnn2 : 0 ≤ Sp2 := by rw [hSp2def]; positivity
  have hSpnn3 : 0 ≤ Sp3 := by rw [hSp3def]; positivity
  -- ## the E-term comparisons
  set E2 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L ^ 2)
    * ((1 + 4 / δ ^ 2) * Cj + Ct) with hE2def
  set E3 : ℝ := (2 / 3) * ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 3)
    * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) with hE3def
  set E2z : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L ^ 2)
    * ((1 + 4 / δ ^ 2) * Cz + Ct) with hE2zdef
  set E3z : ℝ := (2 / 3) * ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 3)
    * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) with hE3zdef
  set C0c : ℝ := (aup / L) * C₀ with hC0cdef
  set Corrc : ℝ := (Cc / L) * (aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
      + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4) with hCorrcdef
  set Fc : ℝ := 64 * aup / (δ * L) with hFcdef
  have hEdef' : E = (aup / L) * C₀
      + (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * (3 * Cn * (L + 6) + Cz) + Ct)
      + (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * (3 * Cn * (L + 6) + Cz) + Ct)
      + (Cc / L) * (aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
          + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4)
      + 64 * aup / (δ * L) := by
    rw [hEdef, P9.Brack, hLdef]
  have hE2E : E2 ≤ (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * (3 * Cn * (L + 6) + Cz) + Ct) := by
    rw [hE2def]
    have h0 : (0 : ℝ) ≤ 1 + 4 / δ ^ 2 := by positivity
    have h1 : (1 + 4 / δ ^ 2) * Cj + Ct ≤ (1 + 4 / δ ^ 2) * (3 * Cn * (L + 6) + Cz) + Ct := by
      have hh := mul_le_mul_of_nonneg_left hCj_le h0
      linarith only [hh]
    have hX : 0 ≤ (1 + 4 / δ ^ 2) * Cj + Ct := by
      have h2 := mul_nonneg h0 hCjnn
      linarith only [h2, hCtpos.le]
    refine le_trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hαaup2 (by positivity)) hX) ?_
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hE3E : E3 ≤ (2 / 3) * (aup ^ 3 / L ^ 3)
      * ((2 / δ) * (1 + 4 / δ ^ 2) * (3 * Cn * (L + 6) + Cz) + Ct) := by
    rw [hE3def]
    have h0 : (0 : ℝ) ≤ (2 / δ) * (1 + 4 / δ ^ 2) := by positivity
    have h1 : (2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct
        ≤ (2 / δ) * (1 + 4 / δ ^ 2) * (3 * Cn * (L + 6) + Cz) + Ct := by
      have hh := mul_le_mul_of_nonneg_left hCj_le h0
      linarith only [hh]
    have hX : 0 ≤ (2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct := by
      have h2 := mul_nonneg h0 hCjnn
      linarith only [h2, hCtpos.le]
    refine le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hαaup3 (by positivity))
        (by norm_num : (0 : ℝ) ≤ 2 / 3)) hX) ?_
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hE2zE : E2z ≤ (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * (3 * Cn * (L + 6) + Cz) + Ct) := by
    rw [hE2zdef]
    have h0 : (0 : ℝ) ≤ 1 + 4 / δ ^ 2 := by positivity
    have h1 : (1 + 4 / δ ^ 2) * Cz + Ct ≤ (1 + 4 / δ ^ 2) * (3 * Cn * (L + 6) + Cz) + Ct := by
      have h2 : Cz ≤ 3 * Cn * (L + 6) + Cz := by
        have h3 : 0 ≤ 3 * Cn * (L + 6) := by positivity
        linarith only [h3]
      have hh := mul_le_mul_of_nonneg_left h2 h0
      linarith only [hh]
    have hX : 0 ≤ (1 + 4 / δ ^ 2) * Cz + Ct := by
      have h2 := mul_nonneg h0 hCzpos.le
      linarith only [h2, hCtpos.le]
    refine le_trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hαaup2 (by positivity)) hX) ?_
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hE3zE : E3z ≤ (2 / 3) * (aup ^ 3 / L ^ 3)
      * ((2 / δ) * (1 + 4 / δ ^ 2) * (3 * Cn * (L + 6) + Cz) + Ct) := by
    rw [hE3zdef]
    have h0 : (0 : ℝ) ≤ (2 / δ) * (1 + 4 / δ ^ 2) := by positivity
    have h1 : (2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct
        ≤ (2 / δ) * (1 + 4 / δ ^ 2) * (3 * Cn * (L + 6) + Cz) + Ct := by
      have h2 : Cz ≤ 3 * Cn * (L + 6) + Cz := by
        have h3 : 0 ≤ 3 * Cn * (L + 6) := by positivity
        linarith only [h3]
      have hh := mul_le_mul_of_nonneg_left h2 h0
      linarith only [hh]
    have hX : 0 ≤ (2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct := by
      have h2 := mul_nonneg h0 hCzpos.le
      linarith only [h2, hCtpos.le]
    refine le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hαaup3 (by positivity))
        (by norm_num : (0 : ℝ) ≤ 2 / 3)) hX) ?_
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hC0cE : C0c ≤ (aup / L) * C₀ := by rw [hC0cdef]
  have hCorrcE : Corrc ≤ (Cc / L) * (aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
      + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4) := by rw [hCorrcdef]
  have hFcE : Fc ≤ 64 * aup / (δ * L) := by rw [hFcdef]
  have hcFar : ∀ k : ℕ, k ≤ 4 →
      (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) ≤ Fc := by
    intro k hk
    have h1 : (k : ℝ) ≤ 4 := by exact_mod_cast hk
    rw [hFcdef]
    have h2 : (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L))
        ≤ 4 * (8 * aup / (δ * L)) := by
      have h3 : (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L))
          ≤ (k : ℝ) * (8 * aup / (δ * L)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith only [hαaup]
      have h4 : (k : ℝ) * (8 * aup / (δ * L)) ≤ 4 * (8 * aup / (δ * L)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      linarith only [h3, h4]
    have h5 : (4 : ℝ) * (8 * aup / (δ * L)) = 32 * aup / (δ * L) := by ring_nf
    have h6 : (32 : ℝ) * aup / (δ * L) ≤ 64 * aup / (δ * L) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith only [hauppos.le]
    linarith only [h2, h5.le, h5.ge, h6]
  have hCorrnn : 0 ≤ Corr := by rw [hCorrdef]; positivity
  have hCorrCorrc : Corr ≤ Corrc := by
    rw [hCorrdef, hCorrcdef]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e1 : (a + (Work.LinnikContract.lamOf q ρ₁)) * Sp1 ≤ aup * (Cp * (Real.log L) ^ 2) :=
      le_trans (mul_le_mul_of_nonneg_right hαaup hSpnn1)
        (mul_le_mul_of_nonneg_left hSp1le hauppos.le)
    have e2 : ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L) * Sp2
        ≤ (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3) := by
      refine le_trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hαaup2 hLpos.le) hSpnn2) ?_
      exact mul_le_mul_of_nonneg_left hSp2le (by positivity)
    have e3 : ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 2) * Sp3
        ≤ (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4) := by
      refine le_trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hαaup3 (by positivity)) hSpnn3) ?_
      exact mul_le_mul_of_nonneg_left hSp3le (by positivity)
    have e4 : (a + (Work.LinnikContract.lamOf q ρ₁)) * Sp1
          + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L) * Sp2
          + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 2) * Sp3
        ≤ aup * (Cp * (Real.log L) ^ 2) + (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3)
          + (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4) := by linarith only [e1, e2, e3]
    have e5 : aup * (Cp * (Real.log L) ^ 2) + (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3)
        + (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4)
        = aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
          + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4 := by ring
    linarith only [e4, e5.le, e5.ge]
  have heE : ∀ e : ℝ, e ≤ E2 + E3 + Fc + Corr + C0c → e ≤ E := by
    intro e he
    rw [hEdef']
    have he' : e ≤ C0c + E2 + E3 + Corr + Fc := by linarith only [he]
    exact le_trans he' (HB91Aux.sum5_le hC0cE hE2E hE3E (le_trans hCorrCorrc hCorrcE) hFcE)
  have heEz : ∀ e : ℝ, e ≤ E2z + E3z + Fc + Corr + C0c → e ≤ E := by
    intro e he
    rw [hEdef']
    have he' : e ≤ C0c + E2z + E3z + Corr + Fc := by linarith only [he]
    exact le_trans he' (HB91Aux.sum5_le hC0cE hE2zE hE3zE (le_trans hCorrCorrc hCorrcE) hFcE)
  have hlogNOf : ∀ {N : ℕ} (hNq : N ∣ q), N ≠ 0 → Real.log (N : ℝ) ≤ L := by
    intro N hNq hN0
    rw [hLdef]
    refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hN0) ?_
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hNq
  have hN3 : 3 ≤ χ₁.conductor := Work.LinnikAreas2.three_le_conductor χ₁ hχ₁ne
  haveI hNc : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  -- ## the shift parameters
  set Δ : ℝ := (ρ₁.im - ρ₀.im) * L with hΔdef
  set β : ℝ := (ρ₁.im + ρ₀.im) * L with hβdef
  set γ : ℝ := 2 * ρ₁.im * L with hγdef
  -- ## the case distinction
  by_cases hcaseC : χ₁ ^ 2 = 1
  · -- ### the real case `χ₁² = 1`
    have hγ₁ne : ρ₁.im ≠ 0 := fun h => hnc ⟨hcaseC, h⟩
    have h3eq : χ₁ ^ 3 = χ₁ := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hcaseC, one_mul]
    haveI hN1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    have hφ₁ne : χ₁.primitiveCharacter ≠ 1 := by
      intro hh
      exact hχ₁ne (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, hh,
        DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level])
    have hφ₁prim : χ₁.primitiveCharacter.IsPrimitive :=
      DirichletCharacter.primitiveCharacter_isPrimitive χ₁
    have hlogN1 : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L :=
      hlogNOf χ₁.conductor_dvd_level χ₁.conductor_ne_zero
    have hzm1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u
        = Work.LinnikContract.zeroMult χ₁.primitiveCharacter u := by
      intro u
      have h := Work.ZeroFreeTables.Table4.zeroMult_changeLevel χ₁.conductor_dvd_level
        χ₁.primitiveCharacter u
      rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
      exact h
    have hconjφ : ∀ u : ℂ,
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter (starRingEnd ℂ u)
          = Work.LinnikContract.zeroMult χ₁.primitiveCharacter u := by
      intro u
      rw [← hzm1 (starRingEnd ℂ u), ← hzm1 u]
      exact Work.A7.zeroMult_conj_sq_one χ₁ hcaseC u
    obtain ⟨par₁, hpar₁2, hpar₁0, hpar₁1⟩ := exists_par χ₁.primitiveCharacter
    have hminP1 := hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim
    have hk1P1 : ∀ t : ℝ, |t| ≤ R → (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter)
        (sPt a L t)).re + P9.nearInvSum χ₁.conductor χ₁.primitiveCharacter (sPt a L t) δ
        ≤ (1 / 6 + ε₁) * L := fun t ht =>
      hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hN3 hlogN1 t ht
    have hJ1 : ∀ s : ℂ, ‖s‖ ≤ Rd → P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s ≤ Cj :=
      fun s hs => hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim s hs
    have hCc1 : ∀ t : ℝ, |SigmaP3L q L (DirichletCharacter.changeLevel χ₁.conductor_dvd_level
          χ₁.primitiveCharacter) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
        - SigmaP3L χ₁.conductor L χ₁.primitiveCharacter (sPt a L t) a
          (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr :=
      fun t => hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter t
    have hρ₁re : ρ₁.re = 1 - (Work.LinnikContract.lamOf q ρ₁) / L := by
      rw [hlamOf_eq ρ₁]; field_simp; ring
    have hρ₀re : ρ₀.re = 1 - (Work.LinnikContract.lamOf q ρ₀) / L := by
      rw [hlamOf_eq ρ₀]; field_simp; ring
    have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
      rw [← hzm1 ρ₁]; exact hzm₁
    have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
      rw [← hzm1 ρ₀]; exact hzm0
    have hzc₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter (starRingEnd ℂ ρ₁) ≠ 0 := by
      rw [hconjφ ρ₁]; exact hz₁
    have hzc₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter (starRingEnd ℂ ρ₀) ≠ 0 := by
      rw [hconjφ ρ₀]; exact hz₀
    have hcim₁ : |(starRingEnd ℂ ρ₁).im| ≤ R + 1 := by
      rw [Complex.conj_im, abs_neg, hRdef]; linarith only [hγ₁, hH1]
    have hcim₀ : |(starRingEnd ℂ ρ₀).im| ≤ R + 1 := by
      rw [Complex.conj_im, abs_neg, hRdef]; linarith only [him0, hH1]
    have hγ₁R : |ρ₁.im| ≤ R := by rw [hRdef]; linarith only [hγ₁, hH1]
    have hγ₀R : |ρ₀.im| ≤ R := by rw [hRdef]; linarith only [him0, hH1]
    have hm3a : |ρ₁.im - ρ₀.im| ≤ R := by
      have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
      rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
    have hm3b : |ρ₁.im + ρ₀.im| ≤ R := by
      have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
      rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
    have hm3c : |2 * ρ₁.im| ≤ R := by
      have h1 := abs_le.mp hγ₁
      rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, hH1]
    have hm3d : |2 * ρ₁.im - ρ₀.im| ≤ R := by
      have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
      rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
    have hm3e : |2 * ρ₁.im + ρ₀.im| ≤ R := by
      have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
      rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
    have hcc0 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) 0
    rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc0
    have hαpos : 0 < a + Work.LinnikContract.lamOf q ρ₁ := by linarith only [ha, hlam₁nn]
    have hfpos : 0 ≤ 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) := by positivity
    -- ### error budgets
    set e1 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he1def
    set e2 : ℝ := E2 + E3 + 3 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he2def
    set e3 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he3def
    set e4 : ℝ := E2 + E3 + 4 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he4def
    set e5 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he5def
    set e6 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he6def
    set e7 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he7def
    set e8 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he8def
    -- ### the eight test points
    set S1 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L 0) a
      (Work.LinnikContract.lamOf q ρ₁) with hS1'
    set S2 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₀.im) a (Work.LinnikContract.lamOf q ρ₁) with hS2'
    set S3 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (ρ₁.im - ρ₀.im)) a
      (Work.LinnikContract.lamOf q ρ₁) with hS3'
    set S4 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₁.im) a (Work.LinnikContract.lamOf q ρ₁) with hS4'
    set S5 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (ρ₁.im + ρ₀.im)) a
      (Work.LinnikContract.lamOf q ρ₁) with hS5'
    set S6 : ℝ := SigmaP3L q L χ₁ (sPt a L (2 * ρ₁.im - ρ₀.im)) a
      (Work.LinnikContract.lamOf q ρ₁) with hS6'
    set S7 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (2 * ρ₁.im)) a
      (Work.LinnikContract.lamOf q ρ₁) with hS7'
    set S8 : ℝ := SigmaP3L q L χ₁ (sPt a L (2 * ρ₁.im + ρ₀.im)) a
      (Work.LinnikContract.lamOf q ρ₁) with hS8'
    -- ### distinctness of the conjugate zeros
    have hd₁c₁ : ρ₁ ≠ starRingEnd ℂ ρ₁ := by
      intro h
      have h' : ρ₁.im = -ρ₁.im := by
        simpa [Complex.conj_im] using congrArg Complex.im h
      exact hγ₁ne (by linarith only [h'])
    have hd₁c₀ : ρ₁ ≠ starRingEnd ℂ ρ₀ := by
      intro h
      exact hconj hcaseC (by
        have h' : starRingEnd ℂ ρ₁ = ρ₀ := by rw [h]; simp
        exact h'.symm)
    have hdcc : starRingEnd ℂ ρ₀ ≠ starRingEnd ℂ ρ₁ := by
      intro h
      have h' : ρ₀ = ρ₁ := by simpa using congrArg (starRingEnd ℂ) h
      exact hne h'.symm
    -- ### point 1: the principal character at σ
    have hS1 : S1 ≤ P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) + e1 := by
      have hb := point_bound_principal_H (q := q) (T := R) (Rd := Rd) (a := a)
        (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
        (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
        hCzZeta hC0b' hnzδ (s := sPt a L 0)
        (by simp [sPt]) (by simp [sPt, hRpos.le])
        (hnormR (t := 0) (by rw [abs_zero]; exact hRpos.le))
        (hSzeta 0).1 (hSzeta 0).2 hcc0
      have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L 0 - 1) * (L : ℂ)))).re
          = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) := by
        rw [P3_arg_eq_pole_split (a := a) (L := L) (t := 0)
          (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne]
        rw [zero_mul, PhiG_zero]
      rw [hpole] at hb
      linarith only [hb, hS1', he1def, hE2zdef, hE3zdef]
    -- ### point 3: the principal character at σ + i(γ₁-γ₀)
    have hS3 : S3 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ + e3 := by
      have hcc3 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im - ρ₀.im)
      rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc3
      have hb := point_bound_principal_H (q := q) (T := R) (Rd := Rd) (a := a)
        (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
        (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
        hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im - ρ₀.im))
        (by simp [sPt]) (by simpa [sPt] using hm3a) (hnormR _ hm3a)
        (hSzeta (ρ₁.im - ρ₀.im)).1 (hSzeta (ρ₁.im - ρ₀.im)).2 hcc3
      have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L (ρ₁.im - ρ₀.im) - 1) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ := by
        rw [P3_arg_eq_pole_split (a := a) (L := L) (t := ρ₁.im - ρ₀.im)
          (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne, hΔdef]
      rw [hpole] at hb
      linarith only [hb, hS3', he3def, hE2zdef, hE3zdef]
    -- ### point 5: the principal character at σ + i(γ₁+γ₀) (as χ₁² = 1)
    have hS5 : S5 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a β + e5 := by
      have hcc5 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im + ρ₀.im)
      rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc5
      have hb := point_bound_principal_H (q := q) (T := R) (Rd := Rd) (a := a)
        (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
        (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
        hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im + ρ₀.im))
        (by simp [sPt]) (by simpa [sPt] using hm3b) (hnormR _ hm3b)
        (hSzeta (ρ₁.im + ρ₀.im)).1 (hSzeta (ρ₁.im + ρ₀.im)).2 hcc5
      have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L (ρ₁.im + ρ₀.im) - 1) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a β := by
        rw [P3_arg_eq_pole_split (a := a) (L := L) (t := ρ₁.im + ρ₀.im)
          (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne, hβdef]
      rw [hpole] at hb
      rw [hS5', hcaseC]
      linarith only [hb, hfpos, he5def, hE2zdef, hE3zdef]
    -- ### point 7: the principal character at σ + 2iγ₁ (as χ₁² = 1)
    have hS7 : S7 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ + e7 := by
      have hcc7 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (2 * ρ₁.im)
      rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc7
      have hb := point_bound_principal_H (q := q) (T := R) (Rd := Rd) (a := a)
        (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
        (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
        hCzZeta hC0b' hnzδ (s := sPt a L (2 * ρ₁.im))
        (by simp [sPt]) (by simpa [sPt] using hm3c) (hnormR _ hm3c)
        (hSzeta (2 * ρ₁.im)).1 (hSzeta (2 * ρ₁.im)).2 hcc7
      have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L (2 * ρ₁.im) - 1) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ := by
        rw [P3_arg_eq_pole_split (a := a) (L := L) (t := 2 * ρ₁.im)
          (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne, hγdef]
      rw [hpole] at hb
      rw [hS7', hcaseC]
      linarith only [hb, hfpos, he7def, hE2zdef, hE3zdef]
    -- ### point 2: χ₁ at σ + iγ₀, kept {ρ₁, ρ₀, ρ̄₁}
    have hS2 : S2 ≤ -P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀)))
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β
        + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e2 := by
      have hT : ∀ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ),
          Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h | h
        · rw [h]; exact hz₁
        · rw [h]; exact hz₀
        · rw [h]; exact hzc₁
      have hTim : ∀ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h | h
        · rw [h, hRdef]; linarith only [hγ₁, hH1]
        · rw [h, hRdef]; linarith only [him0, hH1]
        · rw [h]; exact hcim₁
      have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor)
        (hNq := χ₁.conductor_dvd_level) (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim
        ha hlam₁nn hδpos hδlt1 hLt haδL
        (s := sPt a L ρ₀.im) (by simp [sPt]) (by simpa [sPt] using hγ₀R)
        (hk1P1 ρ₀.im hγ₀R) par₁ hpar₁0 hpar₁1
        (hSpr par₁ hpar₁2 ρ₀.im).1 (hSpr par₁ hpar₁2 ρ₀.im).2
        (hJ1 (sPt a L ρ₀.im) (hnormR _ hγ₀R))
        hminP1 ({ρ₁, ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₀.im)
      have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₀.im - ρ₀) * (L : ℂ)))).re
          = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im) (t := ρ₀.im) (ρ := ρ₀)
          hLne hρ₀re rfl]
        rw [sub_self, zero_mul, PhiG_zero]
      have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₀.im - ρ₁) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im) (t := ρ₀.im) (ρ := ρ₁)
          hLne hρ₁re rfl]
        rw [show (ρ₀.im - ρ₁.im) * L = -Δ by rw [hΔdef]; ring]
        rw [PhiG_neg']
      have t3 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₀.im - (starRingEnd ℂ ρ₁)) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := (starRingEnd ℂ ρ₁).im) (t := ρ₀.im)
          (ρ := starRingEnd ℂ ρ₁) hLne (by rw [Complex.conj_re]; exact hρ₁re) rfl]
        rw [show ρ₀.im - (starRingEnd ℂ ρ₁).im = (ρ₁.im + ρ₀.im) by
          rw [Complex.conj_im]; ring, hβdef]
      have hsum : (∑ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ),
          (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₀.im - u) * (L : ℂ)))).re)
          = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀)))
            + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
            + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β := by
        rw [HB91Aux.sum_three_eq hne hd₁c₁ (hconj hcaseC), t2, t1, t3]
        ring
      have hcard : (({ρ₁, ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ).card : ℝ) ≤ 3 :=
        HB91Aux.card_three_le ρ₁ ρ₀ (starRingEnd ℂ ρ₁)
      have hcardmul := mul_le_mul_of_nonneg_right hcard hfpos
      rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS2'] at hb
      rw [hsum] at hb
      linarith only [hb, hfpos, he2def, hE2def, hE3def, hcardmul]
    -- ### point 6: χ₁ at σ + i(2γ₁-γ₀), kept {ρ₁, ρ̄₀}
    have hS6 : S6 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
        + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e6 := by
      have hT : ∀ u ∈ ({ρ₁, starRingEnd ℂ ρ₀} : Finset ℂ),
          Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h]; exact hz₁
        · rw [h]; exact hzc₀
      have hTim : ∀ u ∈ ({ρ₁, starRingEnd ℂ ρ₀} : Finset ℂ), |u.im| ≤ R + 1 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h, hRdef]; linarith only [hγ₁, hH1]
        · rw [h]; exact hcim₀
      have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor)
        (hNq := χ₁.conductor_dvd_level) (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim
        ha hlam₁nn hδpos hδlt1 hLt haδL
        (s := sPt a L (2 * ρ₁.im - ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3d)
        (hk1P1 (2 * ρ₁.im - ρ₀.im) hm3d) par₁ hpar₁0 hpar₁1
        (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).2
        (hJ1 (sPt a L (2 * ρ₁.im - ρ₀.im)) (hnormR _ hm3d))
        hminP1 ({ρ₁, starRingEnd ℂ ρ₀} : Finset ℂ) hT hTim (hCc1 (2 * ρ₁.im - ρ₀.im))
      have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L (2 * ρ₁.im - ρ₀.im) - ρ₁) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im) (t := 2 * ρ₁.im - ρ₀.im) (ρ := ρ₁)
          hLne hρ₁re rfl]
        rw [show (2 * ρ₁.im - ρ₀.im - ρ₁.im) * L = Δ by rw [hΔdef]; ring]
      have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L (2 * ρ₁.im - ρ₀.im) - (starRingEnd ℂ ρ₀)) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := (starRingEnd ℂ ρ₀).im)
          (t := 2 * ρ₁.im - ρ₀.im) (ρ := starRingEnd ℂ ρ₀) hLne
          (by rw [Complex.conj_re]; exact hρ₀re) rfl]
        rw [show 2 * ρ₁.im - ρ₀.im - (starRingEnd ℂ ρ₀).im = 2 * ρ₁.im by
          rw [Complex.conj_im]; ring, hγdef]
      have hsum : (∑ u ∈ ({ρ₁, starRingEnd ℂ ρ₀} : Finset ℂ),
          (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L (2 * ρ₁.im - ρ₀.im) - u) * (L : ℂ)))).re)
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
            + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ := by
        rw [HB91Aux.sum_pair_eq hd₁c₀, t1, t2]
      have hcard : (({ρ₁, starRingEnd ℂ ρ₀} : Finset ℂ).card : ℝ) ≤ 2 := by
        have h1 := Finset.card_insert_le ρ₁ ({starRingEnd ℂ ρ₀} : Finset ℂ)
        have h2 : ({starRingEnd ℂ ρ₀} : Finset ℂ).card = 1 := Finset.card_singleton _
        have : ({ρ₁, starRingEnd ℂ ρ₀} : Finset ℂ).card ≤ 2 := by omega
        exact_mod_cast this
      have hcardmul := mul_le_mul_of_nonneg_right hcard hfpos
      rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS6'] at hb
      rw [hsum] at hb
      linarith only [hb, hfpos, he6def, hE2def, hE3def, hcardmul]
    -- ### point 8: χ₁ at σ + i(2γ₁+γ₀), kept {ρ₁, ρ₀}
    have hS8 : S8 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
        + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e8 := by
      have hT : ∀ u ∈ ({ρ₁, ρ₀} : Finset ℂ),
          Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h]; exact hz₁
        · rw [h]; exact hz₀
      have hTim : ∀ u ∈ ({ρ₁, ρ₀} : Finset ℂ), |u.im| ≤ R + 1 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h, hRdef]; linarith only [hγ₁, hH1]
        · rw [h, hRdef]; linarith only [him0, hH1]
      have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor)
        (hNq := χ₁.conductor_dvd_level) (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim
        ha hlam₁nn hδpos hδlt1 hLt haδL
        (s := sPt a L (2 * ρ₁.im + ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3e)
        (hk1P1 (2 * ρ₁.im + ρ₀.im) hm3e) par₁ hpar₁0 hpar₁1
        (hSpr par₁ hpar₁2 (2 * ρ₁.im + ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im + ρ₀.im)).2
        (hJ1 (sPt a L (2 * ρ₁.im + ρ₀.im)) (hnormR _ hm3e))
        hminP1 ({ρ₁, ρ₀} : Finset ℂ) hT hTim (hCc1 (2 * ρ₁.im + ρ₀.im))
      have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L (2 * ρ₁.im + ρ₀.im) - ρ₁) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im) (t := 2 * ρ₁.im + ρ₀.im) (ρ := ρ₁)
          hLne hρ₁re rfl]
        rw [show (2 * ρ₁.im + ρ₀.im - ρ₁.im) * L = β by rw [hβdef]; ring]
      have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L (2 * ρ₁.im + ρ₀.im) - ρ₀) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im) (t := 2 * ρ₁.im + ρ₀.im) (ρ := ρ₀)
          hLne hρ₀re rfl]
        rw [show (2 * ρ₁.im + ρ₀.im - ρ₀.im) * L = γ by rw [hγdef]; ring]
      have hsum : (∑ u ∈ ({ρ₁, ρ₀} : Finset ℂ),
          (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L (2 * ρ₁.im + ρ₀.im) - u) * (L : ℂ)))).re)
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β
            + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ := by
        rw [HB91Aux.sum_pair_eq hne, t1, t2]
      have hcard : (({ρ₁, ρ₀} : Finset ℂ).card : ℝ) ≤ 2 := by
        have h1 := Finset.card_insert_le ρ₁ ({ρ₀} : Finset ℂ)
        have h2 : ({ρ₀} : Finset ℂ).card = 1 := Finset.card_singleton _
        have : ({ρ₁, ρ₀} : Finset ℂ).card ≤ 2 := by omega
        exact_mod_cast this
      have hcardmul := mul_le_mul_of_nonneg_right hcard hfpos
      rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS8'] at hb
      rw [hsum] at hb
      linarith only [hb, hfpos, he8def, hE2def, hE3def, hcardmul]
    -- ### the assembly
    have hFcnn : 0 ≤ Fc := by rw [hFcdef]; positivity
    have hC0cnn : 0 ≤ C0c := by rw [hC0cdef]; positivity
    have h1C0 : ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ ≤ C0c := by
      rw [hC0cdef]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup hLpos.le) hC₀pos.le
    have hE1 : e1 ≤ E := by exact heEz _ (by linarith only [he1def, h1C0, hFcnn])
    have hE2 : e2 ≤ E := by
      exact heE _ (by have h := hcFar 3 (by norm_num); linarith only [h, hC0cnn, he2def])
    have hE3 : e3 ≤ E := by exact heEz _ (by linarith only [he3def, h1C0, hFcnn])
    have hE4 : e4 ≤ E := by
      exact heE _ (by have h := hcFar 4 (by norm_num); linarith only [h, hC0cnn, he4def])
    have hE5 : e5 ≤ E := by exact heEz _ (by linarith only [he5def, h1C0, hFcnn])
    have hE6 : e6 ≤ E := by
      exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn, he6def])
    have hE7 : e7 ≤ E := by exact heEz _ (by linarith only [he7def, h1C0, hFcnn])
    have hE8 : e8 ≤ E := by
      exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn, he8def])
    have hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
        + (1 / 4) * (S6 + 2 * S7 + S8) + 0 := by
      have h0 := P9.HbCombinationL_nonneg (q := q) χ₁ K (1 + a / L) ρ₀.im ρ₁.im a
        (Work.LinnikContract.lamOf q ρ₁)
        hK.le (by have h : 0 < a / L := div_pos ha hLpos; linarith only [h]) ha hlam₁nn
      rw [Work.ZeroFreeTables.HbCombinationL, ← hLdef] at h0
      push_cast at h0
      rw [h3eq] at h0
      simp only [hS1', hS2', hS3', hS4', hS5', hS6', hS7', hS8', sPt, Complex.ofReal_zero,
        zero_mul, add_zero]
      push_cast
      exact h0
    have habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5)
        + (1 / 4) * (e6 + 2 * e7 + e8) + 0
        + (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 2 * K + 1)
        ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
      have hfin : a * ε / 2 + (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4)
          ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
        linarith only [mul_pos ha hε, mul_nonneg hlam₁nn hε.le]
      have hsum := sumErr_le hK.le hE1 hE2 hE3 hE4 hE5 hE6 hE7 hE8
      have hε := mul_le_mul_of_nonneg_left hε₁budC hα0
      have hmain : 2 * (K + 1) ^ 2 * E ≤ a * ε / 2 := hEbound
      linarith only [hsum, hmain, hε, hfin]
    -- ### the closed `Φ`-combinations of HB (9.11) and (9.12)
    have hExprA : 0 ≤ (K ^ 2 + 3 / 4) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
          (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
        + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
        - K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ :=
      (P9.rescale_variants.1) a (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀)
        K Δ ha hlam₁nn hlam₁lam₀ hK
        (side913 ha hK hαpos (by linarith only [ha, hlam₀nn]) hcond).2.2.1
    have hExprC : 0 ≤ (K ^ 2 + 3 / 4) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
          (a + (Work.LinnikContract.lamOf q ρ₁)) β
        + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β
        - K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a β :=
      (P9.rescale_variants.1) a (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀)
        K β ha hlam₁nn hlam₁lam₀ hK
        (side913 ha hK hαpos (by linarith only [ha, hlam₀nn]) hcond).2.2.1
    have hExprD : 0 ≤ 2 * K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ
        + (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
        - (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ := by
      have h := P3.CaseC_D (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam₀ := (Work.LinnikContract.lamOf q ρ₀)) (K := K) (t := γ) ha hK.le hlam₁nn hlam₁lam₀
        (side913 ha hK hαpos (by linarith only [ha, hlam₀nn]) hcond).2.2.2
      have heq : (2 * K * P3 (((a : ℂ) + (((Work.LinnikContract.lamOf q ρ₁) : ℂ)))
                / (((a : ℂ) + (((Work.LinnikContract.lamOf q ρ₁) : ℂ))) + ((γ : ℂ)) * Complex.I))
              + (1 / 2) * P3 (((a : ℂ) + (((Work.LinnikContract.lamOf q ρ₁) : ℂ)))
                / (((a : ℂ) + (((Work.LinnikContract.lamOf q ρ₀) : ℂ))) + ((γ : ℂ)) * Complex.I))
              - (1 / 2) * P3 (((a : ℂ) + (((Work.LinnikContract.lamOf q ρ₁) : ℂ)))
                / ((a : ℂ) + ((γ : ℂ)) * Complex.I))).re
          = 2 * K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ
            + (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
            - (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ := by
        simp [P9.PhiG, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im]
      rw [heq] at h
      exact h
    have hleftΔ : 0 ≤ K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
        (a + (Work.LinnikContract.lamOf q ρ₀)) Δ :=
      mul_nonneg hK.le (P9.PhiG_nonneg hαpos (by linarith only [hlam₁lam₀]))
    have hleftβ : 0 ≤ K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
        (a + (Work.LinnikContract.lamOf q ρ₀)) β :=
      mul_nonneg hK.le (P9.PhiG_nonneg hαpos (by linarith only [hlam₁lam₀]))
    by_cases hγ₀ : ρ₀.im = 0
    · -- ### the degenerate sub-case `ρ₀` real
      have hβΔ : β = Δ := by rw [hβdef, hΔdef, hγ₀]; ring
      have hS4 : S4 ≤ -P3R 1
          - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
          - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e4 := by
        have hT : ∀ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h | h
          · rw [h]; exact hz₁
          · rw [h]; exact hz₀
          · rw [h]; exact hzc₁
        have hTim : ∀ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h | h
          · rw [h, hRdef]; linarith only [hγ₁, hH1]
          · rw [h, hRdef]; linarith only [him0, hH1]
          · rw [h]; exact hcim₁
        have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor)
          (hNq := χ₁.conductor_dvd_level) (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim
          ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hγ₁R)
          (hk1P1 ρ₁.im hγ₁R) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
          (hJ1 (sPt a L ρ₁.im) (hnormR _ hγ₁R))
          hminP1 ({ρ₁, ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₁.im)
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
              / ((sPt a L ρ₁.im - ρ₁) * (L : ℂ)))).re = P3R 1 := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
            (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im) (t := ρ₁.im) (ρ := ρ₁)
            hLne hρ₁re rfl]
          rw [sub_self, zero_mul, PhiG_zero]
          rw [show (a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₁)) = 1 by
            rw [div_self (ne_of_gt hαpos)]]
        have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
              / ((sPt a L ρ₁.im - ρ₀) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
            (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im) (t := ρ₁.im) (ρ := ρ₀)
            hLne hρ₀re rfl, hΔdef]
        have t3 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
              / ((sPt a L ρ₁.im - (starRingEnd ℂ ρ₁)) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
            (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := (starRingEnd ℂ ρ₁).im) (t := ρ₁.im)
            (ρ := starRingEnd ℂ ρ₁) hLne (by rw [Complex.conj_re]; exact hρ₁re) rfl]
          rw [show ρ₁.im - (starRingEnd ℂ ρ₁).im = 2 * ρ₁.im by rw [Complex.conj_im]; ring, hγdef]
        have hsum : (∑ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
              / ((sPt a L ρ₁.im - u) * (L : ℂ)))).re)
            = P3R 1 + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
                (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
              + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
                (a + (Work.LinnikContract.lamOf q ρ₁)) γ := by
          rw [HB91Aux.sum_three_eq hne hd₁c₁ (hconj hcaseC), t1, t2, t3]
        have hcard : (({ρ₁, ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ).card : ℝ) ≤ 3 :=
          HB91Aux.card_three_le ρ₁ ρ₀ (starRingEnd ℂ ρ₁)
        have hcardmul := mul_le_mul_of_nonneg_right hcard hfpos
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS4'] at hb
        rw [hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, hfpos, he4def, hE2def, hE3def, hcardmul]
      have hExpr : 0 ≤
          (K ^ 2 + 3 / 4) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
            (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
            + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
            - K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ
          + ((K ^ 2 + 3 / 4) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
              (a + (Work.LinnikContract.lamOf q ρ₁)) β
            + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β
            - K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a β)
          + (2 * K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
              (a + (Work.LinnikContract.lamOf q ρ₁)) γ
            + (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
              (a + (Work.LinnikContract.lamOf q ρ₀)) γ
            - (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ)
          + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
          - K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β := by
        rw [hβΔ] at hExprC ⊢
        linarith only [hExprA, hExprC, hExprD]
      exact caseC_bridge_zero (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam₀ := (Work.LinnikContract.lamOf q ρ₀)) (K := K) (ε := ε) (ε₁ := ε₁)
        (Δ := Δ) (β := β) (γ := γ) (S1 := S1) (S2 := S2) (S3 := S3) (S4 := S4)
        (S5 := S5) (S6 := S6) (S7 := S7) (S8 := S8)
        (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5) (e6 := e6) (e7 := e7)
        (e8 := e8) (corr := 0)
        hK.le hα0 hβΔ hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hcomb hExpr habs
    · -- ### the generic sub-case `ρ₀` non-real
      have hd₀c₀ : ρ₀ ≠ starRingEnd ℂ ρ₀ := by
        intro h
        have h' : ρ₀.im = -ρ₀.im := by
          simpa [Complex.conj_im] using congrArg Complex.im h
        exact hγ₀ (by linarith only [h'])
      have hS4 : S4 ≤ -P3R 1
          - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
          - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β
          - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e4 := by
        have hT : ∀ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h | h | h
          · rw [h]; exact hz₁
          · rw [h]; exact hz₀
          · rw [h]; exact hzc₀
          · rw [h]; exact hzc₁
        have hTim : ∀ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ),
            |u.im| ≤ R + 1 := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h | h | h
          · rw [h, hRdef]; linarith only [hγ₁, hH1]
          · rw [h, hRdef]; linarith only [him0, hH1]
          · rw [h]; exact hcim₀
          · rw [h]; exact hcim₁
        have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor)
          (hNq := χ₁.conductor_dvd_level) (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim
          ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hγ₁R)
          (hk1P1 ρ₁.im hγ₁R) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
          (hJ1 (sPt a L ρ₁.im) (hnormR _ hγ₁R))
          hminP1 ({ρ₁, ρ₀, starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₁.im)
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
              / ((sPt a L ρ₁.im - ρ₁) * (L : ℂ)))).re = P3R 1 := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
            (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im) (t := ρ₁.im) (ρ := ρ₁)
            hLne hρ₁re rfl]
          rw [sub_self, zero_mul, PhiG_zero]
          rw [show (a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₁)) = 1 by
            rw [div_self (ne_of_gt hαpos)]]
        have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
              / ((sPt a L ρ₁.im - ρ₀) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
            (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im) (t := ρ₁.im) (ρ := ρ₀)
            hLne hρ₀re rfl, hΔdef]
        have t3 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
              / ((sPt a L ρ₁.im - (starRingEnd ℂ ρ₀)) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
            (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := (starRingEnd ℂ ρ₀).im) (t := ρ₁.im)
            (ρ := starRingEnd ℂ ρ₀) hLne (by rw [Complex.conj_re]; exact hρ₀re) rfl]
          rw [show ρ₁.im - (starRingEnd ℂ ρ₀).im = ρ₁.im + ρ₀.im by rw [Complex.conj_im]; ring, hβdef]
        have t4 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
              / ((sPt a L ρ₁.im - (starRingEnd ℂ ρ₁)) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
            (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := (starRingEnd ℂ ρ₁).im) (t := ρ₁.im)
            (ρ := starRingEnd ℂ ρ₁) hLne (by rw [Complex.conj_re]; exact hρ₁re) rfl]
          rw [show ρ₁.im - (starRingEnd ℂ ρ₁).im = 2 * ρ₁.im by rw [Complex.conj_im]; ring, hγdef]
        have hsum : (∑ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
              / ((sPt a L ρ₁.im - u) * (L : ℂ)))).re)
            = P3R 1 + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
                (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
              + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
                (a + (Work.LinnikContract.lamOf q ρ₀)) β
              + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
                (a + (Work.LinnikContract.lamOf q ρ₁)) γ := by
          rw [HB91Aux.sum_four_eq hne hd₁c₀ hd₁c₁ hd₀c₀ (hconj hcaseC) hdcc, t1, t2, t3, t4]
        have hcard : (({ρ₁, ρ₀, starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ).card : ℝ) ≤ 4 :=
          HB91Aux.card_four_le ρ₁ ρ₀ (starRingEnd ℂ ρ₀) (starRingEnd ℂ ρ₁)
        have hcardmul := mul_le_mul_of_nonneg_right hcard hfpos
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS4'] at hb
        rw [hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, hfpos, he4def, hE2def, hE3def, hcardmul]
      have hExpr : 0 ≤
          (K ^ 2 + 3 / 4) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
            (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
            + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
            - K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ
          + ((K ^ 2 + 3 / 4) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
              (a + (Work.LinnikContract.lamOf q ρ₁)) β
            + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β
            - K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a β)
          + (2 * K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
              (a + (Work.LinnikContract.lamOf q ρ₁)) γ
            + (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
              (a + (Work.LinnikContract.lamOf q ρ₀)) γ
            - (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ)
          + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
          + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β := by
        linarith only [hExprA, hExprC, hExprD, hleftΔ, hleftβ]
      exact caseC_bridge (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam₀ := (Work.LinnikContract.lamOf q ρ₀)) (K := K) (ε := ε) (ε₁ := ε₁)
        (Δ := Δ) (β := β) (γ := γ) (S1 := S1) (S2 := S2) (S3 := S3) (S4 := S4)
        (S5 := S5) (S6 := S6) (S7 := S7) (S8 := S8)
        (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5) (e6 := e6) (e7 := e7)
        (e8 := e8) (corr := 0)
        hK.le hα0 hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hcomb hExpr habs
  · by_cases hcaseB : χ₁ ^ 3 = 1
    · -- ### case B (χ₁³ = 1, χ₁² ≠ 1)
      have hχ2 : χ₁ ^ 2 ≠ 1 := hcaseC
      haveI hN1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
      have hφ₁ne : χ₁.primitiveCharacter ≠ 1 := by
        intro hh
        exact hχ₁ne (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, hh,
          DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level])
      have hφ₁prim : χ₁.primitiveCharacter.IsPrimitive :=
        DirichletCharacter.primitiveCharacter_isPrimitive χ₁
      have hlogN1 : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L :=
        hlogNOf χ₁.conductor_dvd_level χ₁.conductor_ne_zero
      have hzm1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u
          = Work.LinnikContract.zeroMult χ₁.primitiveCharacter u := by
        intro u
        have h := Work.ZeroFreeTables.Table4.zeroMult_changeLevel χ₁.conductor_dvd_level
          χ₁.primitiveCharacter u
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
        exact h
      obtain ⟨par₁, hpar₁2, hpar₁0, hpar₁1⟩ := exists_par χ₁.primitiveCharacter
      have hminP1 := hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim
      have hk1P1 : ∀ t : ℝ, |t| ≤ R → (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter)
          (sPt a L t)).re + P9.nearInvSum χ₁.conductor χ₁.primitiveCharacter (sPt a L t) δ
          ≤ (1 / 6 + ε₁) * L := fun t ht =>
        hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hN3 hlogN1 t ht
      have hJ1 : ∀ s : ℂ, ‖s‖ ≤ Rd → P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s ≤ Cj :=
        fun s hs => hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim s hs
      have hCc1 : ∀ t : ℝ, |SigmaP3L q L (DirichletCharacter.changeLevel χ₁.conductor_dvd_level
            χ₁.primitiveCharacter) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
          - SigmaP3L χ₁.conductor L χ₁.primitiveCharacter (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr :=
        fun t => hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter t
      have hρ₁re : ρ₁.re = 1 - (Work.LinnikContract.lamOf q ρ₁) / L := by
        rw [hlamOf_eq ρ₁]; field_simp; ring
      have hρ₀re : ρ₀.re = 1 - (Work.LinnikContract.lamOf q ρ₀) / L := by
        rw [hlamOf_eq ρ₀]; field_simp; ring
      have hm3₀ : |ρ₀.im| ≤ R := by rw [hRdef]; linarith only [him0, hH1]
      have hm3₁ : |ρ₁.im| ≤ R := by rw [hRdef]; linarith only [hγ₁, hH1]
      have hm3a : |ρ₁.im - ρ₀.im| ≤ R := by
        have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
        rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
      have hm3f : |-(ρ₁.im + ρ₀.im)| ≤ R := by
        have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
        rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
      have hm3d : |2 * ρ₁.im - ρ₀.im| ≤ R := by
        have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
        rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
      have hm3g : |-(2 * ρ₁.im)| ≤ R := by
        have h1 := abs_le.mp hγ₁
        rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, hH1]
      have hm3e : |2 * ρ₁.im + ρ₀.im| ≤ R := by
        have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
        rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
      -- ### error budgets
      set e1 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he1def
      set e2 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he2def
      set e3 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he3def
      set e4 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he4def
      set e5 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he5def
      set e6 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he6def
      set e7 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he7def
      set e8 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he8def
      -- ### the eight points
      set S1 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁) with hS1'
      set S2 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₀.im) a (Work.LinnikContract.lamOf q ρ₁) with hS2'
      set S3 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS3'
      set S4 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₁.im) a (Work.LinnikContract.lamOf q ρ₁) with hS4'
      set S5 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS5'
      set S6 : ℝ := SigmaP3L q L χ₁ (sPt a L (2 * ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS6'
      set S7 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS7'
      set S8 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (2 * ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS8'
      -- ### point 1
      have hS1 : S1 ≤ P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) + e1 := by
        have hcc0 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) 0
        rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc0
        have hb := point_bound_principal_H (q := q) (T := R) (Rd := Rd) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L 0)
          (by simp [sPt])
          (by simp [sPt, hRpos.le])
          (hnormR (t := 0) (by rw [abs_zero]; exact hRpos.le))
          (hSzeta 0).1 (hSzeta 0).2 hcc0
        have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L 0 - 1) * (L : ℂ)))).re
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) := by
          rw [P3_arg_eq_pole_split (a := a) (L := L) (t := 0) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne]
          rw [zero_mul, PhiG_zero]
        rw [hpole] at hb
        linarith only [hb, hS1', he1def, hE2zdef, hE3zdef]
      -- ### point 2 (χ₁ at σ+iγ₀, kept {ρ₀,ρ₁})
      have hS2 : S2 ≤ -P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e2 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hzm₁
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; rw [hRdef]; linarith only [him0, hH1]
          · rw [Finset.mem_singleton.mp h]; rw [hRdef]; linarith only [hγ₁, hH1]
        have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₀.im) (by simp [sPt]) (by simpa [sPt] using hm3₀)
          (hk1P1 ρ₀.im hm3₀) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₀.im).1 (hSpr par₁ hpar₁2 ρ₀.im).2
          (hJ1 (sPt a L ρ₀.im) ((hnormR _ hm3₀)))
          hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₀.im)
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₀) * (L : ℂ)))).re
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
            (t := ρ₀.im) (ρ := ρ₀) hLne hρ₀re rfl]
          rw [sub_self, zero_mul, PhiG_zero]
        have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₁) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [show (ρ₀.im - ρ₁.im) * L = -Δ by rw [hΔdef]; ring]
          rw [PhiG_neg']
        have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - u) * (L : ℂ)))).re)
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [HB91Aux.sum_pair_eq (Ne.symm hne), t1, t2]
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
        rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, hS2', he2def, hE2def, hE3def]
      -- ### point 3
      have hS3 : S3 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ + e3 := by
        have hcc3 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im - ρ₀.im)
        rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc3
        have hb := point_bound_principal_H (q := q) (T := R) (Rd := Rd) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im - ρ₀.im))
          (by simp [sPt]) (by simpa [sPt] using hm3a)
          (hnormR _ hm3a)
          (hSzeta (ρ₁.im - ρ₀.im)).1 (hSzeta (ρ₁.im - ρ₀.im)).2 hcc3
        have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (ρ₁.im - ρ₀.im) - 1) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ :=
          P3_arg_eq_pole_split (a := a) (L := L) (t := ρ₁.im - ρ₀.im) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne
        rw [hpole] at hb
        linarith only [hb, hS3', he3def, hE2zdef, hE3zdef]
      -- ### point 4 (χ₁ at σ+iγ₁, kept {ρ₀,ρ₁})
      have hS4 : S4 ≤ -P3R 1 - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e4 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hzm₁
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; rw [hRdef]; linarith only [him0, hH1]
          · rw [Finset.mem_singleton.mp h]; rw [hRdef]; linarith only [hγ₁, hH1]
        have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hm3₁)
          (hk1P1 ρ₁.im hm3₁) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
          (hJ1 (sPt a L ρ₁.im) ((hnormR _ hm3₁)))
          hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₁.im)
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₁) * (L : ℂ)))).re = P3R 1 := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := ρ₁.im) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [sub_self, zero_mul, PhiG_zero]
          rw [show (a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₁)) = 1 by
            rw [div_self (ne_of_gt (lt_of_lt_of_le ha (le_add_of_nonneg_right hlam₁nn)))]]
        have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₀) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
            (t := ρ₁.im) (ρ := ρ₀) hLne hρ₀re rfl]
        have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - u) * (L : ℂ)))).re)
            = P3R 1 + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
          rw [Finset.sum_pair (Ne.symm hne), t2, t1]
          ring
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
        rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, hS4', he4def, hE2def, hE3def]
      -- ### point 5 (χ₁² via conjugation, kept {ρ₁})
      have hconj5 : SigmaP3L q L (χ₁ ^ 2) (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁)
          = SigmaP3L q L χ₁ (sPt a L (-(ρ₁.im + ρ₀.im))) a (Work.LinnikContract.lamOf q ρ₁) := by
        rw [P9.SigmaP3L_conj_eq (χ₁ ^ 2) L (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁)]
        have hinv : (χ₁ ^ 2)⁻¹ = χ₁ := by
          refine inv_eq_of_mul_eq_one_right ?_
          rw [← pow_succ]
          exact hcaseB
        rw [hinv]
        congr 1
        apply Complex.ext <;> simp [sPt, Complex.conj_re, Complex.conj_im]
      have hS5 : S5 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) ((2 * ρ₁.im + ρ₀.im) * L)
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e5 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hzm₁
        have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; rw [hRdef]; linarith only [hγ₁, hH1]
        have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (-(ρ₁.im + ρ₀.im))) (by simp [sPt]) (by simpa [sPt] using hm3f)
          (hk1P1 (-(ρ₁.im + ρ₀.im)) hm3f) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (-(ρ₁.im + ρ₀.im))).1 (hSpr par₁ hpar₁2 (-(ρ₁.im + ρ₀.im))).2
          (hJ1 (sPt a L (-(ρ₁.im + ρ₀.im))) ((hnormR _ hm3f)))
          hminP1 ({ρ₁} : Finset ℂ) hT hTim (hCc1 (-(ρ₁.im + ρ₀.im)))
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(ρ₁.im + ρ₀.im)) - ρ₁) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) ((2 * ρ₁.im + ρ₀.im) * L) := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := -(ρ₁.im + ρ₀.im)) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [show (-(ρ₁.im + ρ₀.im) - ρ₁.im) * L = -((2 * ρ₁.im + ρ₀.im) * L) by ring]
          rw [PhiG_neg']
        have hsum : (∑ u ∈ ({ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(ρ₁.im + ρ₀.im)) - u) * (L : ℂ)))).re)
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) ((2 * ρ₁.im + ρ₀.im) * L) := by
          rw [Finset.sum_singleton, t1]
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
        rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
        rw [← hconj5] at hb
        linarith only [hb, hS5', he5def, hE2def, hE3def]
      -- ### point 6 (χ₁ at σ+i(2γ₁-γ₀), kept {ρ₁})
      have hS6 : S6 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e6 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hzm₁
        have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; rw [hRdef]; linarith only [hγ₁, hH1]
        have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im - ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3d)
          (hk1P1 (2 * ρ₁.im - ρ₀.im) hm3d) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).2
          (hJ1 (sPt a L (2 * ρ₁.im - ρ₀.im)) ((hnormR _ hm3d)))
          hminP1 ({ρ₁} : Finset ℂ) hT hTim (hCc1 (2 * ρ₁.im - ρ₀.im))
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - ρ₁) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := 2 * ρ₁.im - ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl,
            show (2 * ρ₁.im - ρ₀.im - ρ₁.im) * L = Δ by rw [hΔdef]; ring]
        have hsum : (∑ u ∈ ({ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - u) * (L : ℂ)))).re)
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [Finset.sum_singleton, t1]
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
        rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
        linarith only [hb, hS6', he6def, hE2def, hE3def]
      -- ### point 7 (χ₁² via conjugation, kept {ρ₀})
      have hconj7 : SigmaP3L q L (χ₁ ^ 2) (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁)
          = SigmaP3L q L χ₁ (sPt a L (-(2 * ρ₁.im))) a (Work.LinnikContract.lamOf q ρ₁) := by
        rw [P9.SigmaP3L_conj_eq (χ₁ ^ 2) L (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁)]
        have hinv : (χ₁ ^ 2)⁻¹ = χ₁ := by
          refine inv_eq_of_mul_eq_one_right ?_
          rw [← pow_succ]
          exact hcaseB
        rw [hinv]
        congr 1
        apply Complex.ext <;> simp [sPt, Complex.conj_re, Complex.conj_im]
      have hS7 : S7 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) ((2 * ρ₁.im + ρ₀.im) * L)
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e7 := by
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₀
        have hTim : ∀ u ∈ ({ρ₀} : Finset ℂ), |u.im| ≤ R + 1 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [him0, hH1]
        have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (-(2 * ρ₁.im))) (by simp [sPt]) (by simpa [sPt] using hm3g)
          (hk1P1 (-(2 * ρ₁.im)) hm3g) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (-(2 * ρ₁.im))).1 (hSpr par₁ hpar₁2 (-(2 * ρ₁.im))).2
          (hJ1 (sPt a L (-(2 * ρ₁.im))) ((hnormR _ hm3g)))
          hminP1 ({ρ₀} : Finset ℂ) hT hTim (hCc1 (-(2 * ρ₁.im)))
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(2 * ρ₁.im)) - ρ₀) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) ((2 * ρ₁.im + ρ₀.im) * L) := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
            (t := -(2 * ρ₁.im)) (ρ := ρ₀) hLne hρ₀re rfl]
          rw [show (-(2 * ρ₁.im) - ρ₀.im) * L = -((2 * ρ₁.im + ρ₀.im) * L) by ring]
          rw [PhiG_neg']
        have hsum : (∑ u ∈ ({ρ₀} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(2 * ρ₁.im)) - u) * (L : ℂ)))).re)
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) ((2 * ρ₁.im + ρ₀.im) * L) := by
          rw [Finset.sum_singleton, t1]
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
        rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
        rw [← hconj7] at hb
        linarith only [hb, hS7', he7def, hE2def, hE3def]
      -- ### point 8 (χ₁³ = 1, principal at σ+i(2γ₁+γ₀))
      have hS8 : S8 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a ((2 * ρ₁.im + ρ₀.im) * L) + e8 := by
        have hcc8 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (2 * ρ₁.im + ρ₀.im)
        rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc8
        have hb := point_bound_principal_H (q := q) (T := R) (Rd := Rd) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L (2 * ρ₁.im + ρ₀.im))
          (by simp [sPt]) (by simpa [sPt] using hm3e)
          (hnormR _ hm3e)
          (hSzeta (2 * ρ₁.im + ρ₀.im)).1 (hSzeta (2 * ρ₁.im + ρ₀.im)).2 hcc8
        have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im + ρ₀.im) - 1) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a ((2 * ρ₁.im + ρ₀.im) * L) :=
          P3_arg_eq_pole_split (a := a) (L := L) (t := 2 * ρ₁.im + ρ₀.im) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne
        rw [hpole] at hb
        rw [hS8']
        linarith only [hb, he8def, hE2zdef, hE3zdef]
      -- ### the assembly
      have hFcnn : 0 ≤ Fc := by rw [hFcdef]; positivity
      have hC0cnn : 0 ≤ C0c := by rw [hC0cdef]; positivity
      have h1C0 : ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ ≤ C0c := by
        rw [hC0cdef]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup hLpos.le) hC₀pos.le
      have hE1 : e1 ≤ E := by rw [he1def]; exact heEz _ (by linarith only [h1C0, hFcnn])
      have hE2 : e2 ≤ E := by rw [he2def]; exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn])
      have hE4 : e4 ≤ E := by rw [he4def]; exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn])
      have hE5 : e5 ≤ E := by rw [he5def]; exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, hC0cnn])
      have hE6 : e6 ≤ E := by rw [he6def]; exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, hC0cnn])
      have hE7 : e7 ≤ E := by rw [he7def]; exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, hC0cnn])
      have hE8 : e8 ≤ E := by rw [he8def]; exact heEz _ (by linarith only [h1C0, hFcnn])
      have hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
          + (1 / 4) * (S6 + 2 * S7 + S8) + 0 := by
        have h0 := P9.HbCombinationL_nonneg (q := q) χ₁ K (1 + a / L) ρ₀.im ρ₁.im a (Work.LinnikContract.lamOf q ρ₁)
          hK.le (by have h : 0 < a / L := div_pos ha hLpos; linarith only [h]) ha hlam₁nn
        rw [Work.ZeroFreeTables.HbCombinationL, ← hLdef, hcaseB] at h0
        push_cast at h0
        simp only [hS1', hS2', hS3', hS4', hS5', hS6', hS7', hS8', sPt, Complex.ofReal_zero,
          zero_mul, add_zero]
        push_cast
        exact h0
      have habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5)
          + (1 / 4) * (e6 + 2 * e7 + e8) + 0 + (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 5 / 4)
          ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
        have hfin : a * ε / 2 + (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4)
            ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
          linarith only [mul_pos ha hε, mul_nonneg hlam₁nn hε.le]
        have hsum := sumErr_le hK.le hE1 hE2 hE1 hE4 hE5 hE6 hE7 hE8
        have hε := mul_le_mul_of_nonneg_left hε₁bud hα0
        have hmain : 2 * (K + 1) ^ 2 * E ≤ a * ε / 2 := hEbound
        have h54 : (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 5 / 4)
            ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4) := by
          have h1 : (K ^ 2 + 3 * K + 5 / 4 : ℝ) ≤ K ^ 2 + 3 * K + 3 / 2 := by norm_num
          have h2 : 0 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ := by positivity
          calc (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 5 / 4)
              ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 3 / 2) :=
                mul_le_mul_of_nonneg_left h1 h2
            _ = (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε₁ * (K ^ 2 + 3 * K + 3 / 2)) := by ring
            _ ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4) :=
                mul_le_mul_of_nonneg_left hε₁bud hα0
        linarith only [hsum, hmain, hfin, h54]
      exact caseB_bridge (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam₀ := (Work.LinnikContract.lamOf q ρ₀)) (K := K) (ε := ε) (ε₁ := ε₁)
        (Δ := Δ) (tB := (2 * ρ₁.im + ρ₀.im) * L)
        (S1 := S1) (S2 := S2) (S3 := S3) (S4 := S4) (S5 := S5) (S6 := S6)
        (S7 := S7) (S8 := S8) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5)
        (e6 := e6) (e7 := e7) (e8 := e8) (corr := 0)
        hK.le hα0 hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hcomb
        (P3.P3Bounds.2 a (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) K Δ
          ha hK hlam₁nn hlam₁lam₀ (side913 ha hK (by linarith only [ha, hlam₁nn]) (by linarith only [ha, hlam₀nn]) hcond).1)
        ((P9.rescale_variants.2.1) a (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) K
          ((2 * ρ₁.im + ρ₀.im) * L) ha hlam₁nn hlam₁lam₀ hK
          (side913 ha hK (by linarith only [ha, hlam₁nn]) (by linarith only [ha, hlam₀nn]) hcond).2.1)
        habs
    · -- ### case A (χ₁ of order neither 2 nor 3)
      have hχ2 : χ₁ ^ 2 ≠ 1 := hcaseC
      have hχ3 : χ₁ ^ 3 ≠ 1 := hcaseB
      haveI hN1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
      have hφ₁ne : χ₁.primitiveCharacter ≠ 1 := by
        intro hh
        exact hχ₁ne (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, hh,
          DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level])
      have hφ₁prim : χ₁.primitiveCharacter.IsPrimitive :=
        DirichletCharacter.primitiveCharacter_isPrimitive χ₁
      have hlogN1 : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L :=
        hlogNOf χ₁.conductor_dvd_level χ₁.conductor_ne_zero
      have hzm1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u
          = Work.LinnikContract.zeroMult χ₁.primitiveCharacter u := by
        intro u
        have h := Work.ZeroFreeTables.Table4.zeroMult_changeLevel χ₁.conductor_dvd_level
          χ₁.primitiveCharacter u
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
        exact h
      obtain ⟨par₁, hpar₁2, hpar₁0, hpar₁1⟩ := exists_par χ₁.primitiveCharacter
      have hminP1 := hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim
      have hk1P1 : ∀ t : ℝ, |t| ≤ R → (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter)
          (sPt a L t)).re + P9.nearInvSum χ₁.conductor χ₁.primitiveCharacter (sPt a L t) δ
          ≤ (1 / 6 + ε₁) * L := fun t ht =>
        hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hN3 hlogN1 t ht
      have hJ1 : ∀ s : ℂ, ‖s‖ ≤ Rd → P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s ≤ Cj :=
        fun s hs => hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim s hs
      have hCc1 : ∀ t : ℝ, |SigmaP3L q L (DirichletCharacter.changeLevel χ₁.conductor_dvd_level
            χ₁.primitiveCharacter) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
          - SigmaP3L χ₁.conductor L χ₁.primitiveCharacter (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr :=
        fun t => hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter t
      have hρ₁re : ρ₁.re = 1 - (Work.LinnikContract.lamOf q ρ₁) / L := by
        rw [hlamOf_eq ρ₁]; field_simp; ring
      have hρ₀re : ρ₀.re = 1 - (Work.LinnikContract.lamOf q ρ₀) / L := by
        rw [hlamOf_eq ρ₀]; field_simp; ring
      have hm3₁ : |ρ₁.im| ≤ R := by rw [hRdef]; linarith only [hγ₁, hH1]
      have hm3₀ : |ρ₀.im| ≤ R := by rw [hRdef]; linarith only [him0, hH1]
      have hm3a : |ρ₁.im - ρ₀.im| ≤ R := by
        have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
        rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
      have hm3b : |ρ₁.im + ρ₀.im| ≤ R := by
        have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
        rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
      have hm3c : |2 * ρ₁.im| ≤ R := by
        have h1 := abs_le.mp hγ₁
        rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, hH1]
      have hm3d : |2 * ρ₁.im - ρ₀.im| ≤ R := by
        have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
        rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
      have hm3e : |2 * ρ₁.im + ρ₀.im| ≤ R := by
        have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp him0
        rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
      have hcc0 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) 0
      rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc0
      -- ### error budgets
      set e1 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he1def
      set e2 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he2def
      set e3 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he3def
      set e4 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he4def
      set e5 : ℝ := E2 + E3 + Corr with he5def
      set e6 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he6def
      set e7 : ℝ := E2 + E3 + Corr with he7def
      set e8 : ℝ := E2 + E3 + Corr with he8def
      -- ### the eight points
      set S1 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁) with hS1'
      set S2 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₀.im) a (Work.LinnikContract.lamOf q ρ₁) with hS2'
      set S3 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS3'
      set S4 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₁.im) a (Work.LinnikContract.lamOf q ρ₁) with hS4'
      set S5 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS5'
      set S6 : ℝ := SigmaP3L q L χ₁ (sPt a L (2 * ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS6'
      set S7 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS7'
      set S8 : ℝ := SigmaP3L q L (χ₁ ^ 3) (sPt a L (2 * ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS8'
      -- ### point 1: the principal character at σ
      have hS1 : S1 ≤ P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) + e1 := by
        have hb := point_bound_principal_H (q := q) (T := R) (Rd := Rd) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L 0)
          (by simp [sPt])
          (by simp [sPt, hRpos.le])
          (hnormR (t := 0) (by rw [abs_zero]; exact hRpos.le))
          (hSzeta 0).1 (hSzeta 0).2 hcc0
        have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L 0 - 1) * (L : ℂ)))).re
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) := by
          rw [P3_arg_eq_pole_split (a := a) (L := L) (t := 0) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne]
          rw [zero_mul, PhiG_zero]
        rw [hpole] at hb
        linarith only [hb, hS1', he1def, hE2zdef, hE3zdef]
      -- ### point 2: χ₁ at σ + iγ₀, kept {ρ₀, ρ₁}
      have hS2 : S2 ≤ -P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e2 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hzm₁
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; rw [hRdef]; linarith only [him0, hH1]
          · rw [Finset.mem_singleton.mp h]; rw [hRdef]; linarith only [hγ₁, hH1]
        have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₀.im) (by simp [sPt]) (by simpa [sPt] using hm3₀)
          (hk1P1 ρ₀.im hm3₀) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₀.im).1 (hSpr par₁ hpar₁2 ρ₀.im).2
          (hJ1 (sPt a L ρ₀.im) ((hnormR _ hm3₀)))
          hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₀.im)
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₀) * (L : ℂ)))).re
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
            (t := ρ₀.im) (ρ := ρ₀) hLne hρ₀re rfl]
          rw [sub_self, zero_mul, PhiG_zero]
        have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₁) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [show (ρ₀.im - ρ₁.im) * L = -Δ by rw [hΔdef]; ring]
          rw [PhiG_neg']
        have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - u) * (L : ℂ)))).re)
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [HB91Aux.sum_pair_eq (Ne.symm hne), t1, t2]
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS2'] at hb
        rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, he2def, hE2def, hE3def]
      -- ### point 3: the principal character at σ + i(γ₁-γ₀)
      have hS3 : S3 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ + e3 := by
        have hcc3 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im - ρ₀.im)
        rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc3
        have hb := point_bound_principal_H (q := q) (T := R) (Rd := Rd) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im - ρ₀.im))
          (by simp [sPt]) (by simpa [sPt] using hm3a)
          (hnormR _ hm3a)
          (hSzeta (ρ₁.im - ρ₀.im)).1 (hSzeta (ρ₁.im - ρ₀.im)).2 hcc3
        have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (ρ₁.im - ρ₀.im) - 1) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ :=
          P3_arg_eq_pole_split (a := a) (L := L) (t := ρ₁.im - ρ₀.im)
            (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne
        rw [hpole] at hb
        linarith only [hb, hS3', he3def, hE2zdef, hE3zdef]
      -- ### point 4: χ₁ at σ + iγ₁, kept {ρ₀, ρ₁}
      have hS4 : S4 ≤ -P3R 1 - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e4 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hzm₁
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; rw [hRdef]; linarith only [him0, hH1]
          · rw [Finset.mem_singleton.mp h]; rw [hRdef]; linarith only [hγ₁, hH1]
        have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hm3₁)
          (hk1P1 ρ₁.im hm3₁) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
          (hJ1 (sPt a L ρ₁.im) ((hnormR _ hm3₁)))
          hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₁.im)
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₁) * (L : ℂ)))).re = P3R 1 := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := ρ₁.im) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [sub_self, zero_mul, PhiG_zero]
          rw [show (a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₁)) = 1 by
            rw [div_self (ne_of_gt (lt_of_lt_of_le ha (le_add_of_nonneg_right hlam₁nn)))]]
        have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₀) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
            (t := ρ₁.im) (ρ := ρ₀) hLne hρ₀re rfl]
        have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - u) * (L : ℂ)))).re)
            = P3R 1 + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
          rw [Finset.sum_pair (Ne.symm hne), t2, t1]
          ring
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS4'] at hb
        rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, he4def, hE2def, hE3def]
      -- ### point 5: χ₁² at σ + i(γ₁+γ₀), nothing kept
      haveI hN2 : NeZero (χ₁ ^ 2).conductor := ⟨(χ₁ ^ 2).conductor_ne_zero⟩
      have hφ₂ne : (χ₁ ^ 2).primitiveCharacter ≠ 1 := by
        intro hh
        exact hχ2 (by rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ ^ 2), hh,
          DirichletCharacter.changeLevel_one (χ₁ ^ 2).conductor_dvd_level])
      have hφ₂prim : (χ₁ ^ 2).primitiveCharacter.IsPrimitive :=
        DirichletCharacter.primitiveCharacter_isPrimitive (χ₁ ^ 2)
      have hlogN2 : Real.log (((χ₁ ^ 2).conductor : ℕ) : ℝ) ≤ L :=
        hlogNOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).conductor_ne_zero
      have hN2_3 : 3 ≤ (χ₁ ^ 2).conductor :=
        Work.LinnikAreas2.three_le_conductor (χ₁ ^ 2) hχ2
      have hS5 : S5 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e5 := by
        obtain ⟨par₂, hpar₂2, hpar₂0, hpar₂1⟩ := exists_par (χ₁ ^ 2).primitiveCharacter
        have hb := point_bound_q_R (q := q) (R := R) (N := (χ₁ ^ 2).conductor)
          (hNq := (χ₁ ^ 2).conductor_dvd_level) (φ := (χ₁ ^ 2).primitiveCharacter) hφ₂ne
          hφ₂prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (ρ₁.im + ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3b)
          (hk1Of (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim hN2_3 hlogN2 (ρ₁.im + ρ₀.im) hm3b)
          par₂ hpar₂0 hpar₂1
          (hSpr par₂ hpar₂2 (ρ₁.im + ρ₀.im)).1 (hSpr par₂ hpar₂2 (ρ₁.im + ρ₀.im)).2
          (hJOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim
            (sPt a L (ρ₁.im + ρ₀.im)) ((hnormR _ hm3b)))
          (hminPrim (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim)
          (∅ : Finset ℂ) (by simp) (by simp)
          (hCcOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter (ρ₁.im + ρ₀.im))
        have hsum : (∑ u ∈ (∅ : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (ρ₁.im + ρ₀.im) - u) * (L : ℂ)))).re) = 0 :=
          Finset.sum_empty
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS5'] at hb
        rw [hsum, Finset.card_empty, Nat.cast_zero, zero_mul, neg_zero, zero_add, add_zero] at hb
        linarith only [hb, he5def, hE2def, hE3def]
      -- ### point 6: χ₁ at σ + i(2γ₁-γ₀), kept {ρ₁}
      have hS6 : S6 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e6 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hzm₁
        have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; rw [hRdef]; linarith only [hγ₁, hH1]
        have hb := point_bound_q_R (q := q) (R := R) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im - ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3d)
          (hk1P1 (2 * ρ₁.im - ρ₀.im) hm3d) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).2
          (hJ1 (sPt a L (2 * ρ₁.im - ρ₀.im)) ((hnormR _ hm3d)))
          hminP1 ({ρ₁} : Finset ℂ) hT hTim (hCc1 (2 * ρ₁.im - ρ₀.im))
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - ρ₁) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := 2 * ρ₁.im - ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [show (2 * ρ₁.im - ρ₀.im - ρ₁.im) * L = Δ by rw [hΔdef]; ring]
        have hsum : (∑ u ∈ ({ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - u) * (L : ℂ)))).re)
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [Finset.sum_singleton, t1]
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS6'] at hb
        rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
        linarith only [hb, he6def, hE2def, hE3def]
      -- ### point 7: χ₁² at σ + 2iγ₁, nothing kept
      have hS7 : S7 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e7 := by
        obtain ⟨par₂, hpar₂2, hpar₂0, hpar₂1⟩ := exists_par (χ₁ ^ 2).primitiveCharacter
        have hb := point_bound_q_R (q := q) (R := R) (N := (χ₁ ^ 2).conductor)
          (hNq := (χ₁ ^ 2).conductor_dvd_level) (φ := (χ₁ ^ 2).primitiveCharacter) hφ₂ne
          hφ₂prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im)) (by simp [sPt]) (by simpa [sPt] using hm3c)
          (hk1Of (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim hN2_3 hlogN2 (2 * ρ₁.im) hm3c)
          par₂ hpar₂0 hpar₂1
          (hSpr par₂ hpar₂2 (2 * ρ₁.im)).1 (hSpr par₂ hpar₂2 (2 * ρ₁.im)).2
          (hJOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim
            (sPt a L (2 * ρ₁.im)) ((hnormR _ hm3c)))
          (hminPrim (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim)
          (∅ : Finset ℂ) (by simp) (by simp)
          (hCcOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter (2 * ρ₁.im))
        have hsum : (∑ u ∈ (∅ : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im) - u) * (L : ℂ)))).re) = 0 :=
          Finset.sum_empty
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS7'] at hb
        rw [hsum, Finset.card_empty, Nat.cast_zero, zero_mul, neg_zero, zero_add, add_zero] at hb
        linarith only [hb, he7def, hE2def, hE3def]
      -- ### point 8: χ₁³ at σ + i(2γ₁+γ₀), nothing kept
      haveI hN3' : NeZero (χ₁ ^ 3).conductor := ⟨(χ₁ ^ 3).conductor_ne_zero⟩
      have hφ₃ne : (χ₁ ^ 3).primitiveCharacter ≠ 1 := by
        intro hh
        exact hχ3 (by rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ ^ 3), hh,
          DirichletCharacter.changeLevel_one (χ₁ ^ 3).conductor_dvd_level])
      have hφ₃prim : (χ₁ ^ 3).primitiveCharacter.IsPrimitive :=
        DirichletCharacter.primitiveCharacter_isPrimitive (χ₁ ^ 3)
      have hlogN3 : Real.log (((χ₁ ^ 3).conductor : ℕ) : ℝ) ≤ L :=
        hlogNOf (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).conductor_ne_zero
      have hN3_3 : 3 ≤ (χ₁ ^ 3).conductor :=
        Work.LinnikAreas2.three_le_conductor (χ₁ ^ 3) hχ3
      have hS8 : S8 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e8 := by
        obtain ⟨par₃, hpar₃2, hpar₃0, hpar₃1⟩ := exists_par (χ₁ ^ 3).primitiveCharacter
        have hb := point_bound_q_R (q := q) (R := R) (N := (χ₁ ^ 3).conductor)
          (hNq := (χ₁ ^ 3).conductor_dvd_level) (φ := (χ₁ ^ 3).primitiveCharacter) hφ₃ne
          hφ₃prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im + ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3e)
          (hk1Of (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim hN3_3 hlogN3 (2 * ρ₁.im + ρ₀.im) hm3e)
          par₃ hpar₃0 hpar₃1
          (hSpr par₃ hpar₃2 (2 * ρ₁.im + ρ₀.im)).1 (hSpr par₃ hpar₃2 (2 * ρ₁.im + ρ₀.im)).2
          (hJOf (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim
            (sPt a L (2 * ρ₁.im + ρ₀.im)) ((hnormR _ hm3e)))
          (hminPrim (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim)
          (∅ : Finset ℂ) (by simp) (by simp)
          (hCcOf (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).primitiveCharacter (2 * ρ₁.im + ρ₀.im))
        have hsum : (∑ u ∈ (∅ : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im + ρ₀.im) - u) * (L : ℂ)))).re) = 0 :=
          Finset.sum_empty
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS8'] at hb
        rw [hsum, Finset.card_empty, Nat.cast_zero, zero_mul, neg_zero, zero_add, add_zero] at hb
        linarith only [hb, he8def, hE2def, hE3def]
      -- ### the assembly
      have hFcnn : 0 ≤ Fc := by rw [hFcdef]; positivity
      have hC0cnn : 0 ≤ C0c := by rw [hC0cdef]; positivity
      have h1C0 : ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ ≤ C0c := by
        rw [hC0cdef]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup hLpos.le) hC₀pos.le
      have hE1 : e1 ≤ E := by
        exact heEz _ (by linarith only [he1def, h1C0, hFcnn])
      have hE2 : e2 ≤ E := by
        exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn, he2def])
      have hE4 : e4 ≤ E := by
        exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn, he4def])
      have hE5 : e5 ≤ E := by
        exact heE _ (by have h := hcFar 0 (by norm_num); linarith only [h, hC0cnn, hFcnn, he5def])
      have hE6 : e6 ≤ E := by
        exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, hC0cnn, he6def])
      have hE7 : e7 ≤ E := by
        exact heE _ (by have h := hcFar 0 (by norm_num); linarith only [h, hC0cnn, hFcnn, he7def])
      have hE8 : e8 ≤ E := by
        exact heE _ (by have h := hcFar 0 (by norm_num); linarith only [h, hC0cnn, hFcnn, he8def])
      have hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
          + (1 / 4) * (S6 + 2 * S7 + S8) + 0 := by
        have h0 := P9.HbCombinationL_nonneg (q := q) χ₁ K (1 + a / L) ρ₀.im ρ₁.im a (Work.LinnikContract.lamOf q ρ₁)
          hK.le (by have h : 0 < a / L := div_pos ha hLpos; linarith only [h]) ha hlam₁nn
        rw [Work.ZeroFreeTables.HbCombinationL, ← hLdef] at h0
        push_cast at h0
        simp only [hS1', hS2', hS3', hS4', hS5', hS6', hS7', hS8', sPt, Complex.ofReal_zero,
          zero_mul, add_zero]
        push_cast
        exact h0
      have habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5)
          + (1 / 4) * (e6 + 2 * e7 + e8) + 0 + (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 3 / 2)
          ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
        have hfin : a * ε / 2 + (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4) ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
          linarith only [mul_pos ha hε, mul_nonneg hlam₁nn hε.le]
        have hsum := sumErr_le hK.le hE1 hE2 hE1 hE4 hE5 hE6 hE7 hE8
        have hε := mul_le_mul_of_nonneg_left hε₁bud hα0
        have hmain : 2 * (K + 1) ^ 2 * E ≤ a * ε / 2 := hEbound
        linarith only [hsum, hmain, hε, hfin]
      exact caseA_bridge (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam₀ := (Work.LinnikContract.lamOf q ρ₀)) (K := K) (ε := ε) (ε₁ := ε₁)
        (Δ := Δ) (S1 := S1) (S2 := S2) (S3 := S3) (S4 := S4) (S5 := S5) (S6 := S6)
        (S7 := S7) (S8 := S8) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5)
        (e6 := e6) (e7 := e7) (e8 := e8) (corr := 0)
        hK.le hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hcomb
        (P3.P3Bounds.2 a (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) K Δ ha hK hlam₁nn hlam₁lam₀
          (side913 ha hK (by linarith only [ha, hlam₁nn]) (by linarith only [ha, hlam₀nn]) hcond).1) habs


end Work.ZeroFreeTables.OffAxis
