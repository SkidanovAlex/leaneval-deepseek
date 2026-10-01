import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HB94.Lam0GeEngine
import Submission.Work.ZeroFreeTables.OffAxis.pointEngine_prim_gen
import Submission.Work.ZeroFreeTables.OffAxis.nearP3sum_ge_kept_R
import Submission.Work.ZeroFreeTables.OffAxis.zetaZeroFreeStripH
import Submission.Work.ZeroFreeTables.OffAxis.zetaLogDerivPoleSplitH
import Submission.Work.ZeroFreeTables.OffAxis.HB91H.zetaZeroInvSq_wide
import Submission.Work.ZeroFreeTables.OffAxis.invNearSum_eq_tsum_gen

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 512000000

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

open Work.ZeroFreeTables.HB94.Lam0GeEngine

/-- `‖σ + i t‖ ≤ 3H + 3` for `σ = 1 + a/L`, `a ≤ L`, `L > 0`, `H ≥ 0` and `|t| ≤ 3H`. -/
theorem norm_sPt_le_Rd {a L t H : ℝ} (ha : 0 < a) (haL : a ≤ L) (hL : 0 < L) (hH : 0 ≤ H)
    (ht : |t| ≤ 3 * H) : ‖sPt a L t‖ ≤ 3 * H + 3 := by
  have h1 : (sPt a L t).re = 1 + a / L := by simp [sPt]
  have h2 : (sPt a L t).im = t := by simp [sPt]
  have h3 : 1 + a / L ≤ 2 := by
    have h : a / L ≤ 1 := (div_le_iff₀ hL).mpr (by linarith)
    linarith
  have h4 : 1 + a / L ≥ 0 := by
    have : 0 ≤ a / L := div_nonneg ha.le hL.le
    linarith
  have h6 := abs_le.mp ht
  have h5 : (1 + a / L) ^ 2 + t ^ 2 ≤ (3 * H + 3) ^ 2 := by
    nlinarith only [h3, h4, h6.1, h6.2, hH]
  calc ‖sPt a L t‖ = Real.sqrt ((sPt a L t).re ^ 2 + (sPt a L t).im ^ 2) := by
        rw [Complex.norm_def, Complex.normSq_apply]; ring_nf
    _ = Real.sqrt ((1 + a / L) ^ 2 + t ^ 2) := by rw [h1, h2]
    _ ≤ Real.sqrt ((3 * H + 3) ^ 2) := Real.sqrt_le_sqrt h5
    _ = 3 * H + 3 := Real.sqrt_sq (by linarith)

/-- **HB Lemma 9.1 (the `P₃` engine) at arbitrary height `H` and room `W`, complex case.**

`HBLemma9_1Wide_proof` (`|Im ρ₀| ≤ 2`, working region `IsMin1WideAt 10`) generalised to
`|Im ρ₁|, |Im ρ₀| ≤ H`, `H ≤ log q`, `3H + 1 ≤ W`, and the minimality hypothesis
`IsMinWideAt H W χ₁ ρ₁` (minimality over all non-principal zeros at height `≤ W`).  The test
points sit at heights `≤ 3H`, the `δ`-windows at heights `≤ 3H + 1 ≤ W`, and the `k = 1` input
`lemma3_1_free_gen` is used at `|Im s| ≤ 10 log q`, giving `3H ≤ 3 log q ≤ 10 log q`. -/
theorem k1_input_Hgen {L₀ δ₀ δ ε₁ a L : ℝ}
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


theorem changeLevel_ne_one_Hgen {N q : ℕ} [NeZero q] [NeZero N] (hNq : N ∣ q)
    (φ : DirichletCharacter ℂ N) (hφ : φ ≠ 1) :
    DirichletCharacter.changeLevel hNq φ ≠ 1 :=
  fun h => hφ ((DirichletCharacter.changeLevel_eq_one_iff hNq).mp h)


theorem point_bound_prim_Hgen {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
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


theorem point_bound_q_Hgen {q N : ℕ} [NeZero q] [NeZero N] (hNq : N ∣ q)
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
  have h1 := point_bound_prim_Hgen φ hφ hprim ha hlam₁ hδ hδ1 hLt haδL hsre hsim
    hlog par hpar0 hpar1 hS2 hS3 hJ hmin T hT hTim
  have h2 : SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) s a lam₁
      ≤ SigmaP3L N L φ s a lam₁ + Cc := by
    have h := (abs_le.mp hcorr).2
    linarith
  linarith [h1, h2]


theorem point_bound_principal_Hgen {q : ℕ} [NeZero q] {a lam₁ δ L Ct Cz C₀ Cc T Rd : ℝ}
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
  have hdiv1 : a / L ≤ 1 := div_le_one_of_le₀ haL hLpos.le
  have hsre2 : s.re ≤ 2 := by rw [hsre]; linarith
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


theorem HBLemma9_1_engine_H_cplx : ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      χ₁ ^ 2 ≠ 1 →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ H → ρ₁ ≠ ρ₀ →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K ε := by
  intro a K ε ha hK hε H W hH1 hHW
  have hH0 : 0 ≤ H := by linarith
  -- ## the constants
  set ε₁ : ℝ := ε / (4 * (K ^ 2 + 3 * K + 4)) with hε₁def
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; positivity
  have hε₁bud : ε₁ * (K ^ 2 + 3 * K + 3 / 2) ≤ ε / 4 := by
    rw [hε₁def, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (K ^ 2 + 3 * K + 4))]
    nlinarith [hε.le, sq_nonneg K, hK.le]
  obtain ⟨L₀, δ₀, hδ₀pos, hδ₀lt1, h31⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := 1 / 3) (by norm_num) hε₁pos
      Work.LinnikAreas.LBound13_holds
  obtain ⟨εζ, hεζpos, hεζ⟩ := zetaZeroFreeStripH (3 * H + 1) (by linarith only [hH0])
  obtain ⟨Ct, hCtpos, hCtS⟩ := Work.ZeroFreeTables.P9.parity_bound_re
  obtain ⟨Czζ, hCzζpos, hCzζ⟩ := HB91H.zetaZeroInvSq_wide (3 * H + 3) (by linarith only [hH0])
  obtain ⟨C₀, hC₀pos, hC₀b⟩ := zetaLogDerivPoleSplitH (3 * H) (by linarith only [hH0])
  obtain ⟨Cc, hCcpos, hCc⟩ := P9.SigmaP3L_changeLevel_diff
  obtain ⟨Cp1, hCp1pos, hCp1⟩ := P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨Cp2, hCp2pos, hCp2⟩ := P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨Cp3, hCp3pos, hCp3⟩ := P9.primeFactors_logPow_div_le 3 (by norm_num)
  set Cp : ℝ := max (max Cp1 Cp2) Cp3 with hCpdef
  have hCpnn : 0 ≤ Cp := by rw [hCpdef]; positivity
  have hCp1le : Cp1 ≤ Cp := by rw [hCpdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCp2le : Cp2 ≤ Cp := by rw [hCpdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCp3le : Cp3 ≤ Cp := by rw [hCpdef]; exact le_max_right _ _
  obtain ⟨Cq, hCqpos, hCq⟩ := invSqSum_uniform
  set M₀ : ℝ := Real.log (2 + (3 * H + 3)) with hM₀def
  have hM₀nn : 0 ≤ M₀ := by rw [hM₀def]; exact Real.log_nonneg (by linarith only [hH0])
  set Cn : ℝ := max (Cq * (M₀ + 3)) 1 with hCndef
  have hCnpos : 0 < Cn := by rw [hCndef]; positivity
  have hCqle : Cq * (M₀ + 3) ≤ Cn := by rw [hCndef]; exact le_max_left _ _
  set Cz : ℝ := max Czζ 1 with hCzdef
  have hCzpos : 0 < Cz := by rw [hCzdef]; positivity
  have hCzζle : Czζ ≤ Cz := by rw [hCzdef]; exact le_max_left _ _
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
  obtain ⟨qabs, habs⟩ := P9.absorption_eventual a K ε aup δ C₀ Ct Cn Cz Cc Cp
    ha hK.le hε hδpos hauppos (le_of_lt hC₀pos) hCtpos hCnpos hCzpos hCcpos.le hCpnn
  set Λ : ℝ := max (max L₀ (2 * a / δ))
    (max (max a 10) (Real.exp (max (1 / a) (max a 1)))) with hΛdef
  refine ⟨max qabs (max 3 (Nat.ceil (Real.exp Λ))), ?_⟩
  intro q hq hqne χ₁ ρ₁ ρ₀ hHlog hmin1 hsq hzm0 him0 hne hcond
  have hqq : 3 ≤ q := by have h := hq; simp only [max_le_iff] at h; exact h.2.1
  have hqexp : Nat.ceil (Real.exp Λ) ≤ q := by
    have h := hq; simp only [max_le_iff] at h; exact h.2.2
  have hΛL : Λ ≤ Real.log q := by
    have h1 : Real.exp Λ ≤ (q : ℝ) :=
      le_trans (Nat.le_ceil (Real.exp Λ)) (by exact_mod_cast hqexp)
    rw [← Real.log_exp Λ]
    exact Real.log_le_log (Real.exp_pos Λ) h1
  set L : ℝ := Real.log q with hLdef
  have hL₀L : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛL
  have h2aδL : 2 * a / δ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛL
  have haL : a ≤ L := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hΛL
  have hexpL : Real.exp (max (1 / a) (max a 1)) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΛL
  have heL : Real.exp 1 ≤ L := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hexpL
    exact le_trans (le_max_right a 1) (le_max_right (1 / a) (max a 1))
  have hLt : 1 < L := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr one_pos) heL
  have hLpos : 0 < L := lt_trans zero_lt_one hLt
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hL1 : 1 ≤ L := le_of_lt hLt
  have h12L : (1 : ℝ) / 2 ≤ L := by linarith only [hLt]
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
  -- ## the E-terms
  set Cj : ℝ := Cn * (L + 6) + Cz with hCjdef
  have hCjnn : 0 ≤ Cj := by rw [hCjdef]; positivity
  set Sp1 : ℝ := ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) with hSp1def
  set Sp2 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) with hSp2def
  set Sp3 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) with hSp3def
  set Corr : ℝ := (Cc / L) * ((a + Work.LinnikContract.lamOf q ρ₁) * Sp1 + ((a + Work.LinnikContract.lamOf q ρ₁) ^ 2 / L) * Sp2
    + ((a + Work.LinnikContract.lamOf q ρ₁) ^ 3 / L ^ 2) * Sp3) with hCorrdef
  set E : ℝ := (aup / L) * C₀ + (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
    + (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct)
    + (Cc / L) * (aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
        + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4)
    + 64 * aup / (δ * L) with hEdef
  have hEbound : 2 * (K + 1) ^ 2 * E ≤ a * ε / 2 := by
    have h := habs q (by have hh := hq; simp only [max_le_iff] at hh; omega)
    rw [show Real.log q = L from hLdef.symm] at h
    rw [hEdef, hCjdef]
    exact h
  -- ## basic bounds
  have hlam₁nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := lamOf_nonneg_of_zeroMult hmin1.2.1
  have hlam₀nn : 0 ≤ Work.LinnikContract.lamOf q ρ₀ := lamOf_nonneg_of_zeroMult hzm0
  have hlam₁lam₀ : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ :=
    hmin1.2.2.2 χ₁ ρ₀ hmin1.1 hzm0 (by linarith only [him0, hH0, hHW])
  have hχ₁ne : χ₁ ≠ 1 := hmin1.1
  have hα0 : 0 ≤ a + Work.LinnikContract.lamOf q ρ₁ := by linarith only [ha, hlam₁nn]
  have hαaup : a + Work.LinnikContract.lamOf q ρ₁ ≤ aup := by
    rw [haupdef]
    exact alpha_le_aup ha hlam₁nn hlam₁lam₀ hcond
  have hαaup2 : (a + Work.LinnikContract.lamOf q ρ₁) ^ 2 ≤ aup ^ 2 := pow_le_pow_left₀ hα0 hαaup 2
  have hαaup3 : (a + Work.LinnikContract.lamOf q ρ₁) ^ 3 ≤ aup ^ 3 := pow_le_pow_left₀ hα0 hαaup 3
  have hlamOf_eq : ∀ u : ℂ, Work.LinnikContract.lamOf q u = (1 - u.re) * L := by
    intro u; rw [Work.LinnikContract.lamOf, ← hLdef]
  have hsts : ∀ t : ℝ, (sPt a L t).im = t := fun t => by simp [sPt]
  have hminOf : ∀ (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ u : ℂ,
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ W →
      Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L := by
    intro ψ hψ u hu him
    rw [← hlamOf_eq u]
    exact hmin1.2.2.2 ψ u hψ hu him
  have hminPrim : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N), φ ≠ 1 →
      φ.IsPrimitive → ∀ u : ℂ, Work.LinnikContract.zeroMult φ u ≠ 0 → |u.im| ≤ W →
      Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L := by
    intro N _ hNq φ hφ hprim u hu him
    refine hminOf (DirichletCharacter.changeLevel hNq φ) (changeLevel_ne_one hNq φ hφ) u ?_ him
    rw [Work.ZeroFreeTables.Table4.zeroMult_changeLevel hNq φ u]
    exact hu
  have hminPrimP : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N), φ ≠ 1 →
      φ.IsPrimitive → ∀ u : ℂ, Work.LinnikContract.zeroMult φ u ≠ 0 → |u.im| ≤ 3 * H + 1 →
      Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L := by
    intro N _ hNq φ hφ hprim u hu him
    exact hminPrim hNq φ hφ hprim u hu (by linarith only [him, hHW])
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
  have hCzZeta : ∀ s : ℂ, ‖s‖ ≤ 3 * H + 3 →
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) ≤ Cz := by
    intro s hs
    exact le_trans (hCzζ s hs) hCzζle
  have hC0b' : ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 3 * H →
      (-logDeriv riemannZeta s).re ≤ (1 / (s - 1)).re + C₀ := hC₀b
  have hnzδ : ∀ t : ℝ, |t| ≤ 3 * H → ∀ u : ℂ, riemannZeta u = 0 →
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
    have huim : |u.im| ≤ 3 * H + 1 := by
      have h1 := (abs_le.mp him1).1
      have h2 := (abs_le.mp him1).2
      have h3 := (abs_le.mp ht)
      rw [abs_le]
      constructor <;> linarith only [h1, h2, h3.1, h3.2, hδlehalf]
    have hz : ((u.re : ℂ) + Complex.I * (u.im : ℂ)) = u := by
      rw [mul_comm]; exact Complex.re_add_im u
    exact hεζ u.im u.re huim hure hure2 (by rw [hz]; exact hu)
  have hJOf : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N), φ ≠ 1 →
      φ.IsPrimitive → ∀ s : ℂ, ‖s‖ ≤ 3 * H + 3 → P9.invSqSum N φ s ≤ Cj := by
    intro N _ hNq φ hφ hprim s hs
    have h1 : P9.invSqSum N φ s ≤ Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) :=
      hCq φ hφ hprim s
    have h2 : Real.log (N : ℝ) ≤ L := by
      rw [hLdef]
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      refine Real.log_le_log hNpos ?_
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hNq
    have h3 : Real.log (2 + ‖s‖) ≤ M₀ := by
      rw [hM₀def]
      exact Real.log_le_log (by positivity) (by linarith only [hs])
    have h7 : Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) ≤ Cj := by
      have h10 : (0 : ℝ) ≤ Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2 := by
        have ha1 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
        have ha2 : (0 : ℝ) ≤ Real.log (2 + ‖s‖) :=
          Real.log_nonneg (by have h := norm_nonneg s; linarith only [h])
        linarith only [ha1, ha2]
      have h11 : Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) ≤ Cq * ((M₀ + 3) * (L + 6)) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [h2, h3, hM₀nn, hLpos.le, h10]) hCqpos.le
      have h12 : Cq * ((M₀ + 3) * (L + 6)) = (Cq * (M₀ + 3)) * (L + 6) := by ring
      have h9 : (Cq * (M₀ + 3)) * (L + 6) ≤ Cn * (L + 6) :=
        mul_le_mul_of_nonneg_right hCqle (by linarith only [hLpos])
      rw [hCjdef]
      linarith only [h11, h12.le, h12.ge, h9, hCzpos.le]
    linarith only [h1, h7]
  have hCcOf : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N) (t : ℝ),
      |SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
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
  have h31' : ∀ {N : ℕ} [NeZero N], 3 ≤ N → ∀ (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      χ.IsPrimitive →
      ∀ {L : ℝ}, L₀ ≤ L → Real.log (N : ℝ) ≤ L → ∀ s : ℂ,
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
      3 ≤ N → Real.log (N : ℝ) ≤ L → ∀ t : ℝ, |t| ≤ 3 * H →
      (-logDeriv (DirichletCharacter.LFunction φ) (sPt a L t)).re
        + P9.nearInvSum N φ (sPt a L t) δ ≤ (1 / 6 + ε₁) * L := by
    intro N _ φ hφ hprim hN3 hlogN t ht
    refine k1_input_Hgen (L₀ := L₀) (δ₀ := δ₀) (δ := δ) (ε₁ := ε₁) (a := a) (L := L) h31'
      (N := N) φ hφ hprim hN3 hL₀L hlogN hδleδ₀ (le_of_lt hδ₀lt1) hδpos (le_of_lt hδlt1)
      ha hL1 h1aL hlogLa (s := sPt a L t) (by simp [sPt]) ?_
    rw [hsts t]
    linarith only [ht, hHlog, hLpos.le]
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
  have hN3 : 3 ≤ χ₁.conductor := Work.LinnikAreas2.three_le_conductor χ₁ hχ₁ne
  haveI hNc : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  set Δ : ℝ := (ρ₁.im - ρ₀.im) * L with hΔdef
  set β : ℝ := (ρ₁.im + ρ₀.im) * L with hβdef
  set γ : ℝ := 2 * ρ₁.im * L with hγdef
  -- ## E-term comparisons
  set E2 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) with hE2def
  set E3 : ℝ := (2 / 3) * ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) with hE3def
  set E2z : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct) with hE2zdef
  set E3z : ℝ := (2 / 3) * ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) with hE3zdef
  set E2c : ℝ := (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) with hE2cdef
  set E3c : ℝ := (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) with hE3cdef
  set Corrc : ℝ := (Cc / L) * (aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
      + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4) with hCorrcdef
  set C0c : ℝ := (aup / L) * C₀ with hC0cdef
  set Fc : ℝ := 64 * aup / (δ * L) with hFcdef
  set E : ℝ := C0c + E2c + E3c + Corrc + Fc with hEdef
  have hcE2 : E2 ≤ E2c := by
    rw [hE2def, hE2cdef]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right hαaup2 (by positivity)
  have hcE3 : E3 ≤ E3c := by
    rw [hE3def, hE3cdef]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hαaup3 (by positivity))
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hCzCj : Cz ≤ Cj := by
    rw [hCjdef]
    have h1 : 0 ≤ Cn * (L + 6) := by positivity
    linarith only [h1]
  have hcE2z : E2z ≤ E2c := by
    rw [hE2zdef, hE2cdef]
    calc ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct)
        ≤ (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_right hαaup2 (by positivity)
      _ ≤ (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 : 0 ≤ (1 + 4 / δ ^ 2 : ℝ) := by positivity
          have h2 := mul_le_mul_of_nonneg_left hCzCj h1
          linarith only [h2]
  have hcE3z : E3z ≤ E3c := by
    rw [hE3zdef, hE3cdef]
    calc (2 / 3) * ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 3)
          * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct)
        ≤ (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hαaup3 (by positivity))
            (by norm_num : (0 : ℝ) ≤ 2 / 3)
      _ ≤ (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 : 0 ≤ (2 / δ) * (1 + 4 / δ ^ 2 : ℝ) := by positivity
          have h2 := mul_le_mul_of_nonneg_left hCzCj h1
          linarith only [h2]
  have hcFar : ∀ k : ℕ, k ≤ 4 → (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) ≤ Fc := by
    intro k hk
    have h1 : (k : ℝ) ≤ 4 := by exact_mod_cast hk
    rw [hFcdef]
    have h2 : (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) ≤ 4 * (8 * aup / (δ * L)) := by
      have h3 : (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) ≤ (k : ℝ) * (8 * aup / (δ * L)) := by
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
  have hcC0 : ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ ≤ C0c := by
    rw [hC0cdef]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup hLpos.le) hC₀pos.le
  have hcCorr : Corr ≤ Corrc := by
    rw [hCorrdef, hCorrcdef]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e1 : (a + (Work.LinnikContract.lamOf q ρ₁)) * Sp1 ≤ aup * (Cp * (Real.log L) ^ 2) :=
      le_trans (mul_le_mul_of_nonneg_right hαaup hSpnn1)
        (mul_le_mul_of_nonneg_left hSp1le hauppos.le)
    have e2 : ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L) * Sp2 ≤ (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3) := by
      refine le_trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hαaup2 hLpos.le) hSpnn2) ?_
      exact mul_le_mul_of_nonneg_left hSp2le (by positivity)
    have e3 : ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 2) * Sp3 ≤ (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4) := by
      refine le_trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hαaup3 (by positivity)) hSpnn3) ?_
      exact mul_le_mul_of_nonneg_left hSp3le (by positivity)
    have e4 : (a + (Work.LinnikContract.lamOf q ρ₁)) * Sp1 + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L) * Sp2 + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 2) * Sp3
        ≤ aup * (Cp * (Real.log L) ^ 2) + (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3)
          + (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4) := by linarith only [e1, e2, e3]
    have e5 : aup * (Cp * (Real.log L) ^ 2) + (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3)
        + (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4)
        = aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
          + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4 := by ring
    linarith only [e4, e5.le, e5.ge]
  have heE : ∀ e : ℝ, e ≤ E2 + E3 + Fc + Corr + C0c → e ≤ E :=
    fun e he => le_E_of_le hEdef hcE2 hcE3 hcCorr he
  have heEz : ∀ e : ℝ, e ≤ E2z + E3z + Fc + Corr + C0c → e ≤ E :=
    fun e he => le_E_of_le_zeta hEdef hcE2z hcE3z hcCorr he
  -- ## the zeta-parity-input, common to all cases
  have hlogNOf : ∀ {N : ℕ} (hNq : N ∣ q), N ≠ 0 → Real.log (N : ℝ) ≤ L := by
    intro N hNq hN0
    rw [hLdef]
    refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hN0) ?_
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hNq
  -- ## summation of the errors
  -- ## the case distinction
  by_cases hC : χ₁ ^ 2 = 1
  · exact absurd hC hsq
  · by_cases hB : χ₁ ^ 3 = 1
    · -- ### case B (χ₁³ = 1, χ₁² ≠ 1)
      have hχ2 : χ₁ ^ 2 ≠ 1 := hC
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
      have hminP1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 →
          |u.im| ≤ 3 * H + 1 → Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L :=
        fun u hu him => hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim u hu
          (by linarith only [him, hHW])
      have hk1P1 : ∀ t : ℝ, |t| ≤ 3 * H → (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter)
          (sPt a L t)).re + P9.nearInvSum χ₁.conductor χ₁.primitiveCharacter (sPt a L t) δ
          ≤ (1 / 6 + ε₁) * L := fun t ht =>
        hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hN3 hlogN1 t ht
      have hJ1 : ∀ s : ℂ, ‖s‖ ≤ 3 * H + 3 → P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s ≤ Cj :=
        fun s hs => hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim s hs
      have hCc1 : ∀ t : ℝ, |SigmaP3L q L (DirichletCharacter.changeLevel χ₁.conductor_dvd_level
            χ₁.primitiveCharacter) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
          - SigmaP3L χ₁.conductor L χ₁.primitiveCharacter (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr :=
        fun t => hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter t
      have hρ₁re : ρ₁.re = 1 - (Work.LinnikContract.lamOf q ρ₁) / L := by
        rw [hlamOf_eq ρ₁]; field_simp; ring
      have hρ₀re : ρ₀.re = 1 - (Work.LinnikContract.lamOf q ρ₀) / L := by
        rw [hlamOf_eq ρ₀]; field_simp; ring
      have hm3₀ : |ρ₀.im| ≤ 3 * H := by linarith only [him0, hH0]
      have hm3₁ : |ρ₁.im| ≤ 3 * H := by linarith only [hmin1.2.2.1, hH0]
      have hm3a : |ρ₁.im - ρ₀.im| ≤ 3 * H := by
        have h1 := abs_le.mp hmin1.2.2.1; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH0]
      have hm3f : |-(ρ₁.im + ρ₀.im)| ≤ 3 * H := by
        have h1 := abs_le.mp hmin1.2.2.1; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH0]
      have hm3d : |2 * ρ₁.im - ρ₀.im| ≤ 3 * H := by
        have h1 := abs_le.mp hmin1.2.2.1; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH0]
      have hm3g : |-(2 * ρ₁.im)| ≤ 3 * H := by
        have h1 := abs_le.mp hmin1.2.2.1
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, hH0]
      have hm3e : |2 * ρ₁.im + ρ₀.im| ≤ 3 * H := by
        have h1 := abs_le.mp hmin1.2.2.1; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH0]
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
        have hb := point_bound_principal_Hgen (T := 3 * H) (Rd := 3 * H + 3) (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L 0) (hsre := by simp [sPt])
          (hsim := by first | (rw [hsts 0]; rw [abs_zero]; linarith only [hH0]) | (rw [abs_zero]; linarith only [hH0]))
          (hsnorm := norm_sPt_le_Rd (t := 0) ha haL hLpos hH0 (by simp only [abs_zero]; linarith only [hH0]))
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
          rw [← hzm1 ρ₁]; exact hmin1.2.1
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ 3 * H + 1 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; linarith only [him0, hH0]
          · rw [Finset.mem_singleton.mp h]; linarith only [hmin1.2.2.1, hH0]
        have hb := point_bound_q_Hgen (R := 3 * H) (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₀.im) (by simp [sPt]) (by simpa [sPt] using hm3₀)
          (hk1P1 ρ₀.im hm3₀) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₀.im).1 (hSpr par₁ hpar₁2 ρ₀.im).2
          (hJ1 (sPt a L ρ₀.im) (norm_sPt_le_Rd ha haL hLpos hH0 hm3₀))
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
          rw [Finset.sum_pair (Ne.symm hne), t1, t2]
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
        rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, hS2', he2def, hE2def, hE3def]
      -- ### point 3
      have hS3 : S3 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ + e3 := by
        have hcc3 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im - ρ₀.im)
        rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc3
        have hb := point_bound_principal_Hgen (T := 3 * H) (Rd := 3 * H + 3) (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im - ρ₀.im)) (hsre := by simp [sPt])
          (hsim := by rw [hsts (ρ₁.im - ρ₀.im)]; exact hm3a)
          (hsnorm := norm_sPt_le_Rd (t := ρ₁.im - ρ₀.im) ha haL hLpos hH0 hm3a)
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
          rw [← hzm1 ρ₁]; exact hmin1.2.1
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ 3 * H + 1 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; linarith only [him0, hH0]
          · rw [Finset.mem_singleton.mp h]; linarith only [hmin1.2.2.1, hH0]
        have hb := point_bound_q_Hgen (R := 3 * H) (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hm3₁)
          (hk1P1 ρ₁.im hm3₁) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
          (hJ1 (sPt a L ρ₁.im) (norm_sPt_le_Rd ha haL hLpos hH0 hm3₁))
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
          exact hB
        rw [hinv]
        congr 1
        apply Complex.ext <;> simp [sPt, Complex.conj_re, Complex.conj_im]
      have hS5 : S5 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) ((2 * ρ₁.im + ρ₀.im) * L)
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e5 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hmin1.2.1
        have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ 3 * H + 1 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [hmin1.2.2.1, hH0]
        have hb := point_bound_q_Hgen (R := 3 * H) (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (-(ρ₁.im + ρ₀.im))) (by simp [sPt]) (by simpa [sPt] using hm3f)
          (hk1P1 (-(ρ₁.im + ρ₀.im)) hm3f) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (-(ρ₁.im + ρ₀.im))).1 (hSpr par₁ hpar₁2 (-(ρ₁.im + ρ₀.im))).2
          (hJ1 (sPt a L (-(ρ₁.im + ρ₀.im))) (norm_sPt_le_Rd ha haL hLpos hH0 hm3f))
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
          rw [← hzm1 ρ₁]; exact hmin1.2.1
        have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ 3 * H + 1 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [hmin1.2.2.1, hH0]
        have hb := point_bound_q_Hgen (R := 3 * H) (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im - ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3d)
          (hk1P1 (2 * ρ₁.im - ρ₀.im) hm3d) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).2
          (hJ1 (sPt a L (2 * ρ₁.im - ρ₀.im)) (norm_sPt_le_Rd ha haL hLpos hH0 hm3d))
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
          exact hB
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
        have hTim : ∀ u ∈ ({ρ₀} : Finset ℂ), |u.im| ≤ 3 * H + 1 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [him0, hH0]
        have hb := point_bound_q_Hgen (R := 3 * H) (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (-(2 * ρ₁.im))) (by simp [sPt]) (by simpa [sPt] using hm3g)
          (hk1P1 (-(2 * ρ₁.im)) hm3g) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (-(2 * ρ₁.im))).1 (hSpr par₁ hpar₁2 (-(2 * ρ₁.im))).2
          (hJ1 (sPt a L (-(2 * ρ₁.im))) (norm_sPt_le_Rd ha haL hLpos hH0 hm3g))
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
        have hb := point_bound_principal_Hgen (T := 3 * H) (Rd := 3 * H + 3) (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L (2 * ρ₁.im + ρ₀.im)) (hsre := by simp [sPt])
          (hsim := by rw [hsts (2 * ρ₁.im + ρ₀.im)]; exact hm3e)
          (hsnorm := norm_sPt_le_Rd (t := 2 * ρ₁.im + ρ₀.im) ha haL hLpos hH0 hm3e)
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
        rw [Work.ZeroFreeTables.HbCombinationL, ← hLdef, hB] at h0
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
      have hχ2 : χ₁ ^ 2 ≠ 1 := hC
      have hχ3 : χ₁ ^ 3 ≠ 1 := hB
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
      have hminP1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 →
          |u.im| ≤ 3 * H + 1 → Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L :=
        fun u hu him => hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim u hu
          (by linarith only [him, hHW])
      have hk1P1 : ∀ t : ℝ, |t| ≤ 3 * H → (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter)
          (sPt a L t)).re + P9.nearInvSum χ₁.conductor χ₁.primitiveCharacter (sPt a L t) δ
          ≤ (1 / 6 + ε₁) * L := fun t ht =>
        hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hN3 hlogN1 t ht
      have hJ1 : ∀ s : ℂ, ‖s‖ ≤ 3 * H + 3 → P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s ≤ Cj :=
        fun s hs => hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim s hs
      have hCc1 : ∀ t : ℝ, |SigmaP3L q L (DirichletCharacter.changeLevel χ₁.conductor_dvd_level
            χ₁.primitiveCharacter) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
          - SigmaP3L χ₁.conductor L χ₁.primitiveCharacter (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr :=
        fun t => hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter t
      have hρ₁re : ρ₁.re = 1 - (Work.LinnikContract.lamOf q ρ₁) / L := by
        rw [hlamOf_eq ρ₁]; field_simp; ring
      have hρ₀re : ρ₀.re = 1 - (Work.LinnikContract.lamOf q ρ₀) / L := by
        rw [hlamOf_eq ρ₀]; field_simp; ring
      have hm3₁ : |ρ₁.im| ≤ 3 * H := by linarith only [hmin1.2.2.1, hH0]
      have hm3₀ : |ρ₀.im| ≤ 3 * H := by linarith only [him0, hH0]
      have hm3a : |ρ₁.im - ρ₀.im| ≤ 3 * H := by
        have h1 := abs_le.mp hmin1.2.2.1; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH0]
      have hm3b : |ρ₁.im + ρ₀.im| ≤ 3 * H := by
        have h1 := abs_le.mp hmin1.2.2.1; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH0]
      have hm3c : |2 * ρ₁.im| ≤ 3 * H := by
        have h1 := abs_le.mp hmin1.2.2.1
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, hH0]
      have hm3d : |2 * ρ₁.im - ρ₀.im| ≤ 3 * H := by
        have h1 := abs_le.mp hmin1.2.2.1; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH0]
      have hm3e : |2 * ρ₁.im + ρ₀.im| ≤ 3 * H := by
        have h1 := abs_le.mp hmin1.2.2.1; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH0]
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
        have hb := point_bound_principal_Hgen (T := 3 * H) (Rd := 3 * H + 3) (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L 0) (hsre := by simp [sPt])
          (hsim := by first | (rw [hsts 0]; rw [abs_zero]; linarith only [hH0]) | (rw [abs_zero]; linarith only [hH0]))
          (hsnorm := norm_sPt_le_Rd (t := 0) ha haL hLpos hH0 (by simp only [abs_zero]; linarith only [hH0]))
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
          rw [← hzm1 ρ₁]; exact hmin1.2.1
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ 3 * H + 1 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; linarith only [him0, hH0]
          · rw [Finset.mem_singleton.mp h]; linarith only [hmin1.2.2.1, hH0]
        have hb := point_bound_q_Hgen (R := 3 * H) (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₀.im) (by simp [sPt]) (by simpa [sPt] using hm3₀)
          (hk1P1 ρ₀.im hm3₀) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₀.im).1 (hSpr par₁ hpar₁2 ρ₀.im).2
          (hJ1 (sPt a L ρ₀.im) (norm_sPt_le_Rd ha haL hLpos hH0 hm3₀))
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
          rw [Finset.sum_pair (Ne.symm hne), t1, t2]
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS2'] at hb
        rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, he2def, hE2def, hE3def]
      -- ### point 3: the principal character at σ + i(γ₁-γ₀)
      have hS3 : S3 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ + e3 := by
        have hcc3 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im - ρ₀.im)
        rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc3
        have hb := point_bound_principal_Hgen (T := 3 * H) (Rd := 3 * H + 3) (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im - ρ₀.im)) (hsre := by simp [sPt])
          (hsim := by rw [hsts (ρ₁.im - ρ₀.im)]; exact hm3a)
          (hsnorm := norm_sPt_le_Rd (t := ρ₁.im - ρ₀.im) ha haL hLpos hH0 hm3a)
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
          rw [← hzm1 ρ₁]; exact hmin1.2.1
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ 3 * H + 1 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; linarith only [him0, hH0]
          · rw [Finset.mem_singleton.mp h]; linarith only [hmin1.2.2.1, hH0]
        have hb := point_bound_q_Hgen (R := 3 * H) (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hm3₁)
          (hk1P1 ρ₁.im hm3₁) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
          (hJ1 (sPt a L ρ₁.im) (norm_sPt_le_Rd ha haL hLpos hH0 hm3₁))
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
        have hb := point_bound_q_Hgen (R := 3 * H) (q := q) (N := (χ₁ ^ 2).conductor)
          (hNq := (χ₁ ^ 2).conductor_dvd_level) (φ := (χ₁ ^ 2).primitiveCharacter) hφ₂ne
          hφ₂prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (ρ₁.im + ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3b)
          (hk1Of (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim hN2_3 hlogN2 (ρ₁.im + ρ₀.im) hm3b)
          par₂ hpar₂0 hpar₂1
          (hSpr par₂ hpar₂2 (ρ₁.im + ρ₀.im)).1 (hSpr par₂ hpar₂2 (ρ₁.im + ρ₀.im)).2
          (hJOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim
            (sPt a L (ρ₁.im + ρ₀.im)) (norm_sPt_le_Rd ha haL hLpos hH0 hm3b))
          (hminPrimP (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim)
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
          rw [← hzm1 ρ₁]; exact hmin1.2.1
        have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ 3 * H + 1 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [hmin1.2.2.1, hH0]
        have hb := point_bound_q_Hgen (R := 3 * H) (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im - ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3d)
          (hk1P1 (2 * ρ₁.im - ρ₀.im) hm3d) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).2
          (hJ1 (sPt a L (2 * ρ₁.im - ρ₀.im)) (norm_sPt_le_Rd ha haL hLpos hH0 hm3d))
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
        have hb := point_bound_q_Hgen (R := 3 * H) (q := q) (N := (χ₁ ^ 2).conductor)
          (hNq := (χ₁ ^ 2).conductor_dvd_level) (φ := (χ₁ ^ 2).primitiveCharacter) hφ₂ne
          hφ₂prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im)) (by simp [sPt]) (by simpa [sPt] using hm3c)
          (hk1Of (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim hN2_3 hlogN2 (2 * ρ₁.im) hm3c)
          par₂ hpar₂0 hpar₂1
          (hSpr par₂ hpar₂2 (2 * ρ₁.im)).1 (hSpr par₂ hpar₂2 (2 * ρ₁.im)).2
          (hJOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim
            (sPt a L (2 * ρ₁.im)) (norm_sPt_le_Rd ha haL hLpos hH0 hm3c))
          (hminPrimP (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim)
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
        have hb := point_bound_q_Hgen (R := 3 * H) (q := q) (N := (χ₁ ^ 3).conductor)
          (hNq := (χ₁ ^ 3).conductor_dvd_level) (φ := (χ₁ ^ 3).primitiveCharacter) hφ₃ne
          hφ₃prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im + ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3e)
          (hk1Of (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim hN3_3 hlogN3 (2 * ρ₁.im + ρ₀.im) hm3e)
          par₃ hpar₃0 hpar₃1
          (hSpr par₃ hpar₃2 (2 * ρ₁.im + ρ₀.im)).1 (hSpr par₃ hpar₃2 (2 * ρ₁.im + ρ₀.im)).2
          (hJOf (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim
            (sPt a L (2 * ρ₁.im + ρ₀.im)) (norm_sPt_le_Rd ha haL hLpos hH0 hm3e))
          (hminPrimP (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim)
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
