/-
# ZeroFreeTables/OffAxis — `HBLemma8_3_engine_H`

**HB Lemma 8.3 at rectangle height `H` with room `W`**: the `P₃` engine of HB §8.2 for a
**real-real** pair `(χ₁, ρ₁)` (`χ₁² = 1`, `ρ₁` real) and a further **non-real** zero `ρ₀` of
`χ₁` of height `≤ H`, with `λ₁` minimal over the zeros of all non-principal characters of
height `≤ W`.

It is the height-parametric form of `Work.ZeroFreeTables.HBLemma8_3`: `IsMin1WideAt 10 χ₁ ρ₁`
and `IsZ χ₁ ρ₁` become `Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁`, and `IsZ χ₁ ρ₀` becomes
`zeroMult χ₁ ρ₀ ≠ 0 ∧ |ρ₀.im| ≤ H`.  The three test points `σ`, `σ+iγ⁰`, `σ+2iγ⁰` have
heights `≤ 2H`, so the windows are contained in `3H + 1 ≤ W`; the `k = 1` input (HB Lemma 3.1)
is used in the real-character `φ = 1/4` form at `|s.im| ≤ 10 log q`, whence the hypothesis
`H ≤ Real.log q` (absorbed by enlarging `q₀`, which may depend on `H`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
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
import Submission.Work.ZeroFreeTables.OffAxis.HBLemma9_1_engine_H
import Submission.Work.ZeroFreeTables.HB94.Lam0GeEngine
import Submission.Work.ZeroFreeTables.Table4.zeroMult_changeLevel
import Submission.Work.ZeroFreeTables.Table4.HB83
import Submission.Work.ZeroFreeTables.XY.L52HypEighthDelta
import Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen_real
import Submission.Work.A7.zeroMult_conj_sq_one
import Submission.Work.LinnikAreas2.D2Aux
import Submission.Work.ZeroFreeTables.OffAxis.hb83KeptSums

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 64000000

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract
open Work.ZeroFreeTables
open Work.ZeroFreeTables.HB94.Lam0GeEngine (sPt)

/-! ## The pointwise inequality HB (8.5) for a real character -/

/-- **HB (8.5)** for a real character (`χ² = 1`): the eight-term combination of HB (9.1)
collapses to six terms at the points `σ`, `σ+iγ`, `σ+2iγ`. -/
theorem hb85Real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {K σ γ a lam₁ : ℝ} (hK : 0 ≤ K) (hσ : 1 < σ) (ha : 0 < a) (hlam : 0 ≤ lam₁) :
    0 ≤ (K ^ 2 + 1 / 2) *
          (SigmaP3L q (Real.log q) 1 (σ : ℂ) a lam₁
            + SigmaP3L q (Real.log q) χ (σ : ℂ) a lam₁)
        + 2 * K *
          (SigmaP3L q (Real.log q) 1 ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam₁
            + SigmaP3L q (Real.log q) χ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam₁)
        + (1 / 2) *
          (SigmaP3L q (Real.log q) 1 ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) a lam₁
            + SigmaP3L q (Real.log q) χ ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) a lam₁) := by
  have h3 : χ ^ 3 = χ := by rw [pow_succ, hsq, one_mul]
  have h := P9.HbCombinationL_nonneg χ K σ 0 γ a lam₁ hK hσ ha hlam
  rw [HbCombinationL, hsq, h3] at h
  simp only [Complex.ofReal_zero, zero_mul, add_zero, sub_zero, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast,
    Complex.ofReal_one] at h ⊢
  linarith

/-! ## The `k = 1` input of HB Lemma 3.1 at the real-character constant `1/8` -/

/-- HB Lemma 3.1 in the form needed at the three test points. -/
theorem k1RealGen {L₀ δ₀ δ ε₁ a L : ℝ}
    (h31 : ∀ {M : ℕ} [NeZero M], 3 ≤ M → ∀ (χ : DirichletCharacter ℂ M), χ ≠ 1 →
      χ.IsPrimitive → χ ^ 2 = 1 →
      ∀ {L : ℝ}, L₀ ≤ L → Real.log (M : ℝ) ≤ L → ∀ s : ℂ,
        1 + 1 / (L * Real.log L) ≤ s.re → s.re ≤ 1 + Real.log L / L → |s.im| ≤ 10 * L →
        (-logDeriv (DirichletCharacter.LFunction χ) s).re
          + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
              (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ₀ then ((1 / (s - u)).re) else 0))
          ≤ (1 / 8 + ε₁) * L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    (hsq : χ ^ 2 = 1)
    (hN3 : 3 ≤ N) (hL0 : L₀ ≤ L) (hlogN : Real.log (N : ℝ) ≤ L)
    (hδδ₀ : δ ≤ δ₀) (hδ₀1 : δ₀ ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : 0 < a) (hL1 : 1 ≤ L) (h1 : 1 ≤ a * Real.log L) (h2 : a ≤ Real.log L)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hs3 : |s.im| ≤ 10 * L) :
    (-logDeriv (DirichletCharacter.LFunction χ) s).re
      + P9.nearInvSum N χ s δ ≤ (1 / 8 + ε₁) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hlogLpos : 0 < Real.log L := by nlinarith only [h1, ha]
  have hs1 : 1 + 1 / (L * Real.log L) ≤ s.re := by
    rw [hsre]
    have hkey : 1 / (L * Real.log L) ≤ a / L := by
      field_simp
      nlinarith only [h1, hLpos]
    linarith only [hkey]
  have hs2 : s.re ≤ 1 + Real.log L / L := by
    rw [hsre]
    have h3 : a / L ≤ Real.log L / L := div_le_div_of_nonneg_right h2 hLpos.le
    linarith only [h3]
  have h31' := h31 hN3 χ hχ hprim hsq hL0 hlogN s hs1 hs2 hs3
  have hre1 : (1 : ℝ) ≤ s.re := by
    rw [hsre]
    have h4 : 0 ≤ a / L := div_nonneg ha.le hLpos.le
    linarith only [h4]
  have hmono : InvNearSum N χ s δ ≤ InvNearSum N χ s δ₀ :=
    P9.InvNearSum_anti χ hχ hprim hre1 hδδ₀ hδ₀1
  have heq : InvNearSum N χ s δ = P9.nearInvSum N χ s δ :=
    invNearSum_eq_tsum_gen χ hχ hprim hδ0 hδ1
  rw [heq] at hmono
  simp only [InvNearSum, pdiv] at hmono
  linarith only [h31', hmono]

/-- `‖sPt a L t‖ ≤ R + 2` for `1 + a/L ≤ 2` and `|t| ≤ R`. -/
theorem norm_sPt_le (a L R t : ℝ) (ha : 0 < a) (haL : a ≤ L) (hL : 0 < L) (hR : |t| ≤ R) :
    ‖sPt a L t‖ ≤ R + 2 := by
  have h1 : (sPt a L t).re = 1 + a / L := by simp [sPt]
  have h2 : (sPt a L t).im = t := by simp [sPt]
  have hRnn : 0 ≤ R := le_trans (abs_nonneg t) hR
  have h3 : 1 + a / L ≤ 2 := by
    have h : a / L ≤ 1 := (div_le_iff₀ hL).mpr (by linarith only [haL])
    linarith only [h]
  have h4 : 0 ≤ 1 + a / L := by
    have h : 0 ≤ a / L := div_nonneg ha.le hL.le
    linarith only [h]
  have h5 : (1 + a / L) ^ 2 + t ^ 2 ≤ (R + 2) ^ 2 := by
    have h6 := abs_le.mp hR
    nlinarith only [h3, h4, h6.1, h6.2, hRnn]
  calc ‖sPt a L t‖ = Real.sqrt ((sPt a L t).re ^ 2 + (sPt a L t).im ^ 2) := by
        rw [Complex.norm_def, Complex.normSq_apply]; ring_nf
    _ = Real.sqrt ((1 + a / L) ^ 2 + t ^ 2) := by rw [h1, h2]
    _ ≤ Real.sqrt ((R + 2) ^ 2) := Real.sqrt_le_sqrt h5
    _ = R + 2 := Real.sqrt_sq (by linarith only [hRnn])


/-- `Re P₃(al/((s-u)L))` in the `P3AB` normal form of HB §8.2, at the points `s = σ + it`
with `s.re = 1 + a/L` and a zero `u` with `u.re = 1 - lam/L`. -/
theorem reP3_div_eq_p3ab {al a lam L : ℝ} {s u : ℂ} (hL : L ≠ 0)
    (hs : s.re = 1 + a / L) (hu : u.re = 1 - lam / L) :
    (Work.ZeroFreeTables.P3 (((a : ℂ) + (al : ℂ)) / ((s - u) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + al) (a + lam) ((s.im - u.im) * L) := by
  unfold Work.ZeroFreeTables.Table4.P3AB
  have h1 : (s - u) * (L : ℂ)
      = ((a + lam : ℝ) : ℂ) + (((s.im - u.im) * L : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.I_re, Complex.I_im, zero_mul, sub_zero, Complex.sub_im]
      rw [hs, hu]; field_simp; ring
    · simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, add_zero]
      ring
  rw [h1]
  congr 1
  push_cast
  ring

/-! ## The budget of the final `ε`-accounting -/

/-- With `ε₁ ≤ ε/2`, `a ≤ α` and `2(K+1)²E ≤ aε/2`, the two error terms of the §8.2 assembly
fit into the `(K+1)²αε` slot of the target inequality. -/
theorem hb83Budget {K a α ε ε₁ E : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a) (haα : a ≤ α)
    (hε : 0 < ε) (hε₁ : ε₁ ≤ ε / 2) (hE : 2 * (K + 1) ^ 2 * E ≤ a * ε / 2) :
    (K + 1) ^ 2 * (α * ε₁) + 2 * (K + 1) ^ 2 * E ≤ (K + 1) ^ 2 * (α * ε) := by
  have h1 : (0 : ℝ) ≤ (K + 1) ^ 2 := by positivity
  have hα0 : 0 ≤ α := le_trans ha haα
  have hK1 : (1 : ℝ) ≤ (K + 1) ^ 2 := by nlinarith only [hK]
  have hε4 : (0 : ℝ) < ε / 4 := by linarith only [hε]
  -- `(K+1)²E ≤ aε/4` and then `≤ αε/2`
  have hE2 : 2 * (K + 1) ^ 2 * E ≤ α * ε / 2 := by
    have h3 : a * ε ≤ α * ε := mul_le_mul_of_nonneg_right haα hε.le
    have h4 : (0 : ℝ) ≤ α * ε := mul_nonneg hα0 hε.le
    linarith only [hE, h3, h4]
  -- `(K+1)²(αε₁) ≤ (K+1)²(αε/2)`
  have h3 : (K + 1) ^ 2 * (α * ε₁) ≤ (K + 1) ^ 2 * (α * (ε / 2)) := by
    apply mul_le_mul_of_nonneg_left _ h1
    exact mul_le_mul_of_nonneg_left hε₁ hα0
  -- `αε/2 ≤ (K+1)²(αε/2)` and the final assembly
  have h5 : α * ε / 2 ≤ (K + 1) ^ 2 * (α * ε / 2) := by
    have h7 : (0 : ℝ) ≤ α * ε / 2 := by linarith only [mul_nonneg hα0 hε.le]
    nlinarith only [hK1, h7]
  have h6 : 2 * (K + 1) ^ 2 * E ≤ (K + 1) ^ 2 * (α * (ε / 2)) := by
    have hαε : (K + 1) ^ 2 * (α * (ε / 2)) = (K + 1) ^ 2 * (α * ε) / 2 := by ring
    linarith only [hE2, h5, hαε.le, hαε.ge]
  have h8 : (K + 1) ^ 2 * (α * (ε / 2)) + (K + 1) ^ 2 * (α * (ε / 2))
      = (K + 1) ^ 2 * (α * ε) := by ring
  linarith only [h3, h6, h8]

theorem HBLemma8_3_engine_H : ∀ (a K ε : ℝ), 0 < a → 1 / 4 ≤ K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ H → ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 →
      Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ →
      Work.ZeroFreeTables.cond86 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a →
      0 ≤ Work.ZeroFreeTables.p83 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K
        + (K + 1) ^ 2 * (a + Work.LinnikContract.lamOf q ρ₁) * ε := by
  intro a K ε ha hK4 hε H W hH1 hHW
  have hK : 0 < K := by linarith
  -- ## the room `R = 2H` of the three test points, and `R + 1 ≤ W`
  set R : ℝ := 2 * H with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; linarith
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRW : R + 1 ≤ W := by rw [hRdef]; linarith
  have hHW' : H ≤ W := by linarith
  -- ## the constants
  set ε₁ : ℝ := ε / 2 with hε₁def
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; linarith
  have hε₁bud : ε₁ ≤ ε / 2 := le_of_eq hε₁def
  obtain ⟨L₀, δ₀, hδ₀pos, hδ₀lt1, h31⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen_real (φ := 1 / 4) (by norm_num) hε₁pos
      Work.ZeroFreeTables.XY.hbound_quarter_real
  obtain ⟨Ct, hCtpos, hCtS⟩ := P9.parity_bound_re
  obtain ⟨Czk, hCzkpos, hCzk⟩ := Work.LinnikAreas.FarRepel.zetaHalfKernelBound
  set Rd : ℝ := R + 2 with hRddef
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
  set CnA : ℝ := 4 * Cn with hCnAdef
  have hCnApos : 0 < CnA := by rw [hCnAdef]; positivity
  obtain ⟨εζ, hεζpos, hεζ⟩ := zetaZeroFreeStripH (4 * H + 1) (by linarith)
  set δ : ℝ := min δ₀ (min (εζ / 2) (1 / 2)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (lt_min (by linarith only [hεζpos]) (by norm_num))
  have hδleδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδleζ : δ ≤ εζ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδlehalf : δ ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hδlt1 : δ < 1 := lt_of_le_of_lt hδlehalf (by norm_num)
  set aup : ℝ := 2 * a with haupdef
  have hauppos : 0 < aup := by rw [haupdef]; linarith
  obtain ⟨qabs, habs⟩ := P9.absorption_eventual a K ε aup δ C₀ Ct CnA Cz Cc Cp
    ha hK.le hε hδpos hauppos hC₀pos.le hCtpos hCnApos hCzpos hCcpos.le hCpnn
  set Λ : ℝ := max (max (max L₀ (2 * a / δ))
    (max (max a 10) (Real.exp (max (1 / a) (max a 1))))) H with hΛdef
  refine ⟨max qabs (max 3 (Nat.ceil (Real.exp Λ))), ?_⟩
  intro q hq hqne χ₁ ρ₁ ρ₀ hHL hmin hsq him1 hzm0 him0abs hne him0 hlamle hcond
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
  -- ## the primitive character of `χ₁`
  haveI hNc : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hχ₁ne : χ₁ ≠ 1 := hmin.1
  have hN3 : 3 ≤ χ₁.conductor := Work.LinnikAreas2.three_le_conductor χ₁ hχ₁ne
  have hφ₁prim : (χ₁.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ₁
  have hφ₁ne : χ₁.primitiveCharacter ≠ 1 := by
    intro h1
    exact hχ₁ne (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, h1,
      DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level])
  have hchisq : (χ₁.primitiveCharacter) ^ 2 = 1 := by
    have hcl := DirichletCharacter.changeLevel_primitiveCharacter χ₁
    refine DirichletCharacter.changeLevel_injective χ₁.conductor_dvd_level ?_
    rw [map_pow, hcl, hsq, map_one]
  have hlogN1 : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L := by
    rw [hLdef]
    refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ₁.conductor_ne_zero) ?_
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ₁.conductor_dvd_level
  have hzm1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u
      = Work.LinnikContract.zeroMult χ₁.primitiveCharacter u := by
    intro u
    have h := Work.ZeroFreeTables.Table4.zeroMult_changeLevel χ₁.conductor_dvd_level
      χ₁.primitiveCharacter u
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    exact h
  -- ## the error constants
  set Cj : ℝ := CnA * (L + 6) + Cz with hCjdef
  have hCjnn : 0 ≤ Cj := by rw [hCjdef]; positivity
  set Sp1 : ℝ := ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) with hSp1def
  set Sp2 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) with hSp2def
  set Sp3 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) with hSp3def
  set Corr : ℝ := (Cc / L) * ((a + (Work.LinnikContract.lamOf q ρ₁)) * Sp1
    + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L) * Sp2
    + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 2) * Sp3) with hCorrdef
  set E : ℝ := P9.Brack aup δ C₀ Ct CnA Cz Cc Cp q with hEdef
  have hEbound : 2 * (K + 1) ^ 2 * E ≤ a * ε / 2 := by
    rw [hEdef]
    exact habs q (by have hh := hq; simp only [max_le_iff] at hh; omega)
  -- ## basic bounds
  have hzm₁ : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin.2.1
  have hγ₁ : |ρ₁.im| ≤ H := hmin.2.2.1
  have hlam₁nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.ZeroFreeTables.HB94.Lam0GeEngine.lamOf_nonneg_of_zeroMult hzm₁
  have hlam₀nn : 0 ≤ Work.LinnikContract.lamOf q ρ₀ :=
    Work.ZeroFreeTables.HB94.Lam0GeEngine.lamOf_nonneg_of_zeroMult hzm0
  have hα0 : 0 ≤ a + Work.LinnikContract.lamOf q ρ₁ := by linarith only [ha, hlam₁nn]
  have hlam1lea : Work.LinnikContract.lamOf q ρ₁ ≤ a := by
    have hA1 : 0 < a + Work.LinnikContract.lamOf q ρ₁ := by linarith only [ha, hlam₁nn]
    have hA0 : 0 < a + Work.LinnikContract.lamOf q ρ₀ := by linarith only [ha, hlam₀nn]
    have hle1 : 1 / (a + Work.LinnikContract.lamOf q ρ₀) ^ 3
        ≤ 1 / (a + Work.LinnikContract.lamOf q ρ₁) ^ 3 := by
      apply one_div_le_one_div_of_le (pow_pos hA1 3)
      exact pow_le_pow_left₀ hA1.le (by linarith only [hlamle]) 3
    unfold Work.ZeroFreeTables.cond86 at hcond
    have h2 : 1 / a ^ 3 ≤ 2 / (a + Work.LinnikContract.lamOf q ρ₁) ^ 3 := by
      have e : (2 : ℝ) / (a + Work.LinnikContract.lamOf q ρ₁) ^ 3
          = 1 / (a + Work.LinnikContract.lamOf q ρ₁) ^ 3
            + 1 / (a + Work.LinnikContract.lamOf q ρ₁) ^ 3 := by ring
      rw [e]
      linarith only [hcond, hle1]
    have hkey : (a + Work.LinnikContract.lamOf q ρ₁) ^ 3 ≤ 2 * a ^ 3 := by
      have h3 := (div_le_div_iff₀ (by positivity : (0 : ℝ) < a ^ 3)
        (by positivity : (0 : ℝ) < (a + Work.LinnikContract.lamOf q ρ₁) ^ 3)).mp h2
      linarith only [h3]
    have hma : a + Work.LinnikContract.lamOf q ρ₁ ≤ 2 * a := by
      by_contra hcon
      rw [not_le] at hcon
      have h8 : 2 * a ^ 3 ≤ (2 * a) ^ 3 := by
        have h9 : (2 * a) ^ 3 = 8 * a ^ 3 := by ring
        have h10 : (0 : ℝ) ≤ a ^ 3 := by positivity
        linarith only [h9, h10]
      have h1 : (2 * a) ^ 3 < (a + Work.LinnikContract.lamOf q ρ₁) ^ 3 :=
        pow_lt_pow_left₀ hcon (by linarith : (0 : ℝ) ≤ 2 * a) (by norm_num : (3 : ℕ) ≠ 0)
      linarith only [h1, hkey, h8]
    linarith only [hma]
  have hαaup : a + Work.LinnikContract.lamOf q ρ₁ ≤ aup := by
    rw [haupdef]; linarith only [hlam1lea]
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
      have h6 : |t| ≤ 2 * H := abs_le.mpr ⟨h3.1, h3.2⟩
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
    have h3 : Real.log (2 + ‖s‖) ≤ L + 2 := by
      have h7 : 2 + ‖s‖ ≤ 6 * L := by
        rw [hRddef] at hs
        have h8 : R ≤ 2 * L := by rw [hRdef]; linarith only [hHL']
        nlinarith only [hs, h8, heL, Real.exp_one_gt_two, hLpos.le]
      have h8 : Real.log (2 + ‖s‖) ≤ Real.log (6 * L) :=
        Real.log_le_log (by positivity) h7
      have h9 : Real.log (6 * L) = Real.log 6 + Real.log L :=
        Real.log_mul (by norm_num) hLne
      have h10 : Real.log 6 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 6)]
        have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
        nlinarith only [Real.exp_one_gt_d9, h2]
      have h11 : Real.log L ≤ L := Real.log_le_self hLpos.le
      linarith only [h8, h9, h10, h11]
    have h4 : Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2 ≤ 2 * L + 4 := by linarith only [h2, h3]
    have h5 : (0 : ℝ) ≤ Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2 := by
      have ha1 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
      have ha2 : (0 : ℝ) ≤ Real.log (2 + ‖s‖) :=
        Real.log_nonneg (by have h := norm_nonneg s; linarith only [h])
      linarith only [ha1, ha2]
    have h6 : Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) ≤ Cn * (2 * L + 4) :=
      mul_le_mul hCqle h4 h5 hCnpos.le
    have h7 : Cn * (2 * L + 4) ≤ CnA * (L + 6) := by
      rw [hCnAdef]
      nlinarith only [hCnpos.le, hLpos.le]
    have h8 : CnA * (L + 6) ≤ Cj := by rw [hCjdef]; linarith only [hCzpos.le]
    linarith only [h1, h6, h7, h8]
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
      χ.IsPrimitive → χ ^ 2 = 1 →
      ∀ {L : ℝ}, L₀ ≤ L → Real.log (M : ℝ) ≤ L → ∀ s : ℂ,
        1 + 1 / (L * Real.log L) ≤ s.re → s.re ≤ 1 + Real.log L / L → |s.im| ≤ 10 * L →
        (-logDeriv (DirichletCharacter.LFunction χ) s).re
          + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
              (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ₀ then ((1 / (s - u)).re) else 0))
          ≤ (1 / 8 + ε₁) * L := by
    intro M _ hM χ hχ hprim hsq L hL0 hlogN s hs1 hs2 hs3
    simpa only [show ((1 : ℝ) / 4 / 2) = 1 / 8 by norm_num] using
      h31 hM χ hχ hprim hsq hL0 hlogN s hs1 hs2 hs3
  have hk1Of : ∀ {N : ℕ} [NeZero N] (φ : DirichletCharacter ℂ N), φ ≠ 1 → φ.IsPrimitive →
      φ ^ 2 = 1 → 3 ≤ N → Real.log (N : ℝ) ≤ L → ∀ t : ℝ, |t| ≤ R →
      (-logDeriv (DirichletCharacter.LFunction φ) (sPt a L t)).re
        + P9.nearInvSum N φ (sPt a L t) δ ≤ (1 / 8 + ε₁) * L := by
    intro N _ φ hφ hprim hsq hN3 hlogN t ht
    refine k1RealGen h31' φ hφ hprim hsq hN3 hL₀L hlogN hδleδ₀ (le_of_lt hδ₀lt1)
      hδpos (le_of_lt hδlt1) ha hL1 h1aL hlogLa (s := sPt a L t) (by simp [sPt]) ?_
    have ht' : |t| ≤ 2 * L := by rw [hRdef] at ht; linarith only [ht, hHL']
    have h10 : 2 * L ≤ 10 * L := by linarith only [hLpos.le]
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
      + (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
      + (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct)
      + (Cc / L) * (aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
          + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4)
      + 64 * aup / (δ * L) := by
    rw [hEdef, P9.Brack, hLdef, hCjdef]
  have hE2E : E2 ≤ (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) := by
    rw [hE2def]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup2 (by positivity))
      (by have h2 := mul_nonneg (by positivity : (0:ℝ) ≤ 1 + 4 / δ ^ 2) hCjnn
          linarith only [h2, hCtpos.le])
  have hE3E : E3 ≤ (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) := by
    rw [hE3def]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hαaup3 (by positivity)) (by norm_num : (0:ℝ) ≤ 2 / 3)) ?_
    have h2 := mul_nonneg (by positivity : (0:ℝ) ≤ (2 / δ) * (1 + 4 / δ ^ 2)) hCjnn
    linarith only [h2, hCtpos.le]
  have hCzleCj : Cz ≤ Cj := by rw [hCjdef]; nlinarith only [hCnApos.le, hLpos.le]
  have hE2zE : E2z ≤ E2 := by
    rw [hE2zdef, hE2def]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h := mul_le_mul_of_nonneg_left hCzleCj (by positivity : (0 : ℝ) ≤ 1 + 4 / δ ^ 2)
    linarith only [h]
  have hE3zE : E3z ≤ E3 := by
    rw [hE3zdef, hE3def]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h := mul_le_mul_of_nonneg_left hCzleCj
      (by positivity : (0 : ℝ) ≤ (2 / δ) * (1 + 4 / δ ^ 2))
    linarith only [h]
  have hC0cE : C0c ≤ (aup / L) * C₀ := le_of_eq (by rw [hC0cdef])
  have hCorrcE : Corrc ≤ (Cc / L) * (aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
      + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4) := le_of_eq (by rw [hCorrcdef])
  have hFcE : Fc ≤ 64 * aup / (δ * L) := le_of_eq (by rw [hFcdef])
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
    exact heE e (by linarith only [he, hE2zE, hE3zE])
  -- ## the three test points
  set γ : ℝ := ρ₀.im with hγdef
  set μ : ℝ := γ * L with hμdef
  have hγH : |γ| ≤ H := by rw [hγdef]; exact him0abs
  have hγR : |γ| ≤ R := by rw [hRdef]; linarith only [hγH, hH1]
  have h2γR : |2 * γ| ≤ R := by
    rw [hRdef, abs_mul]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]; linarith only [hγH]
  have hσ1 : 1 < 1 + a / L := by
    have h : 0 < a / L := div_pos ha hLpos
    linarith only [h]
  -- ## the pair `ρ₁, ρ₀`
  have hlam1eq : Work.LinnikContract.lamOf q ρ₁ = (1 - ρ₁.re) * L := hlamOf_eq ρ₁
  have hlam0eq : Work.LinnikContract.lamOf q ρ₀ = (1 - ρ₀.re) * L := hlamOf_eq ρ₀
  have hρ₁re : ρ₁.re = 1 - Work.LinnikContract.lamOf q ρ₁ / L := by
    rw [hlam1eq]; field_simp; ring
  have hρ₀re : ρ₀.re = 1 - Work.LinnikContract.lamOf q ρ₀ / L := by
    rw [hlam0eq]; field_simp; ring
  have hconjre : (starRingEnd ℂ ρ₀).re = 1 - Work.LinnikContract.lamOf q ρ₀ / L := by
    rw [show (starRingEnd ℂ ρ₀).re = ρ₀.re by simp]
    exact hρ₀re
  have hγeq : γ = ρ₀.im := hγdef
  have hμeq : μ = γ * L := hμdef
  have hne0c : ρ₀ ≠ starRingEnd ℂ ρ₀ := by
    intro h
    have h2 : ρ₀.im = -(ρ₀.im) := by have := congrArg Complex.im h; simpa using this
    exact him0 (by linarith only [h2])
  have hne1c : ρ₁ ≠ starRingEnd ℂ ρ₀ := by
    intro h
    have h2 : ρ₁.im = -(ρ₀.im) := by have := congrArg Complex.im h; simpa using this
    rw [him1] at h2
    exact him0 (by linarith only [h2])
  have hzr1 : Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) ρ₁ ≠ 0 := by
    rw [← hzm1 ρ₁]; exact hzm₁
  have hzr0 : Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) ρ₀ ≠ 0 := by
    rw [← hzm1 ρ₀]; exact hzm0
  have hzrc : Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) (starRingEnd ℂ ρ₀) ≠ 0 := by
    rw [← hzm1 (starRingEnd ℂ ρ₀), Work.ZeroFreeTables.Table4.zeroMult_conj χ₁ hsq ρ₀]
    exact hzm0
  have himr1 : |ρ₁.im| ≤ R + 1 := by
    rw [hRdef, him1]
    simp only [abs_zero]
    linarith only [hH1]
  have himr0 : |ρ₀.im| ≤ R + 1 := by rw [hRdef]; linarith only [him0abs, hH1]
  have himrc : |(starRingEnd ℂ ρ₀).im| ≤ R + 1 := by
    rw [Complex.conj_im, abs_neg]; exact himr0
  have hT0card : ((({ρ₁, ρ₀} : Finset ℂ)).card : ℝ) = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne.symm]), Finset.card_singleton]
    norm_num
  have hT1card : ((({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ)).card : ℝ) = 3 := by
    rw [show ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ)
        = insert ρ₁ (insert ρ₀ {starRingEnd ℂ ρ₀}) by rfl]
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hne.symm, hne1c⟩),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hne0c),
      Finset.card_singleton]
    norm_num
  -- ## the retained-sum expansions of HB §8.2 (in `P₃`-normal form)
  obtain ⟨hkT0s0, hkT1s1, hkT0s2, hkP0, hkP1, hkP2⟩ :=
    hb83KeptSums hLne ha hlam₁nn hγdef hρ₁re hρ₀re him1 hne.symm him0
  have hmu1 : ∀ {x y : ℝ}, Work.ZeroFreeTables.Table4.P3AB x y μ
      = Work.ZeroFreeTables.Table4.P3AB x y (γ * L) := by
    intro x y
    rw [hμdef]
  have hmu2 : ∀ {x y : ℝ}, Work.ZeroFreeTables.Table4.P3AB x y (2 * μ)
      = Work.ZeroFreeTables.Table4.P3AB x y (2 * γ * L) := by
    intro x y
    have h : 2 * μ = 2 * γ * L := by rw [hμdef]; ring
    rw [h]
  have hT0s0 : (∑ u ∈ ({ρ₁, ρ₀} : Finset ℂ),
        (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
          / ((sPt a L 0 - u) * (L : ℂ)))).re)
      = Work.ZeroFreeTables.P3R 1
        + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
            (a + Work.LinnikContract.lamOf q ρ₀) μ := by
    rw [hmu1]
    exact hkT0s0
  have hT1s1 : (∑ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ),
        (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
          / ((sPt a L γ - u) * (L : ℂ)))).re)
      = Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
            (a + Work.LinnikContract.lamOf q ρ₁) μ
        + Work.ZeroFreeTables.P3R ((a + Work.LinnikContract.lamOf q ρ₁)
            / (a + Work.LinnikContract.lamOf q ρ₀))
        + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
            (a + Work.LinnikContract.lamOf q ρ₀) (2 * μ) := by
    rw [hmu1, hmu2]
    exact hkT1s1
  have hT0s2 : (∑ u ∈ ({ρ₁, ρ₀} : Finset ℂ),
        (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
          / ((sPt a L (2 * γ) - u) * (L : ℂ)))).re)
      = Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
            (a + Work.LinnikContract.lamOf q ρ₁) (2 * μ)
        + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
            (a + Work.LinnikContract.lamOf q ρ₀) μ := by
    rw [hmu1, hmu2]
    exact hkT0s2
  have hP0 : (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
      / ((sPt a L 0 - 1) * (L : ℂ)))).re
      = Work.ZeroFreeTables.P3R ((a + Work.LinnikContract.lamOf q ρ₁) / a) := by
    rw [show ((a + Work.LinnikContract.lamOf q ρ₁) / a)
        = (a + Work.LinnikContract.lamOf q ρ₁) / a from rfl]
    exact hkP0
  have hP1 : (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
      / ((sPt a L γ - 1) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a μ := by
    rw [hmu1]
    exact hkP1
  have hP2 : (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
      / ((sPt a L (2 * γ) - 1) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a (2 * μ) := by
    rw [hmu2]
    exact hkP2
  -- ## the error terms of the six point bounds
  set e1 : ℝ := E2 + E3 + 2 * (8 * (a + Work.LinnikContract.lamOf q ρ₁) / (δ * L)) + Corr with he1def
  set e1' : ℝ := ((a + Work.LinnikContract.lamOf q ρ₁) / L) * C₀ + E2z + E3z + Corr with he1'def
  set e2 : ℝ := E2 + E3 + 3 * (8 * (a + Work.LinnikContract.lamOf q ρ₁) / (δ * L)) + Corr with he2def
  -- ## the six point bounds
  obtain ⟨par₁, hpar₁2, hpar₁0, hpar₁1⟩ :=
    Work.ZeroFreeTables.HB94.Lam0GeEngine.exists_par χ₁.primitiveCharacter
  have him0R : |(sPt a L 0).im| ≤ R := by
    have h : (sPt a L 0).im = 0 := by simp [sPt]
    rw [h, abs_zero]; exact hRpos.le
  have himγR : |(sPt a L γ).im| ≤ R := by
    have h : (sPt a L γ).im = γ := by simp [sPt]
    rw [h]; exact hγR
  have him2γR : |(sPt a L (2 * γ)).im| ≤ R := by
    have h : (sPt a L (2 * γ)).im = 2 * γ := by simp [sPt]
    rw [h]; exact h2γR
  have h0R : |(0 : ℝ)| ≤ R := by simp only [abs_zero]; exact hRpos.le
  have hre0 : (sPt a L 0).re = 1 + a / L := by simp [sPt]
  have hreγ : (sPt a L γ).re = 1 + a / L := by simp [sPt]
  have hre2γ : (sPt a L (2 * γ)).re = 1 + a / L := by simp [sPt]
  have hRdpt : ∀ t : ℝ, |t| ≤ R → ‖sPt a L t‖ ≤ Rd := by
    intro t ht
    rw [hRddef]
    exact norm_sPt_le a L R t ha haL hLpos ht
  -- ### `χ₁` at `σ`
  have hU0 : SigmaP3L q L χ₁ (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁)
      ≤ -(Work.ZeroFreeTables.P3R 1
            + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
                (a + Work.LinnikContract.lamOf q ρ₀) μ)
        + (a + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε₁) + e1 := by
    have hb := HB91Aux.point_bound_q_R (q := q) (R := R) (N := χ₁.conductor)
      (hNq := χ₁.conductor_dvd_level) (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim
      ha hlam₁nn hδpos hδlt1 hLt haδL (s := sPt a L 0) hre0 him0R
      (hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hchisq hN3 hlogN1 0 h0R)
      par₁ hpar₁0 hpar₁1 (hSpr par₁ hpar₁2 0).1 (hSpr par₁ hpar₁2 0).2
      (hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim (sPt a L 0)
        (hRdpt 0 h0R))
      (hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim)
      ({ρ₁, ρ₀} : Finset ℂ)
      (by intro u hu
          rw [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h
          · rw [h]; exact hzr1
          · rw [h]; exact hzr0)
      (by intro u hu
          rw [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h
          · rw [h]; exact himr1
          · rw [h]; exact himr0)
      (hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter 0)
    rw [DirichletCharacter.changeLevel_primitiveCharacter, hT0s0, hT0card] at hb
    simp only [he1def, hE2def, hE3def]
    linarith only [hb]
  -- ### `χ₀` at `σ`
  have hV0 : SigmaP3L q L 1 (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁)
      ≤ Work.ZeroFreeTables.P3R ((a + Work.LinnikContract.lamOf q ρ₁) / a) + e1' := by
    have hcc0 : |SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L 0) a
          (Work.LinnikContract.lamOf q ρ₁)
        - SigmaP3L 1 L 1 (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr := by
      have h := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) 0
      rwa [DirichletCharacter.changeLevel_one (one_dvd q)] at h
    have hb := HB91Aux.point_bound_principal_H (q := q) (T := R) (Rd := Rd)
      ha hlam₁nn hδpos hδlt1 hLt haδL haL hCzZeta hC0b' hnzδ (s := sPt a L 0) hre0 him0R
      (hRdpt 0 h0R) (hSzeta 0).1 (hSzeta 0).2 hcc0
    rw [hP0] at hb
    simp only [he1'def, hE2zdef, hE3zdef]
    linarith only [hb]
  -- ### `χ₁` at `σ + iγ⁰`
  have hU1 : SigmaP3L q L χ₁ (sPt a L γ) a (Work.LinnikContract.lamOf q ρ₁)
      ≤ -(Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
                (a + Work.LinnikContract.lamOf q ρ₁) μ
            + Work.ZeroFreeTables.P3R ((a + Work.LinnikContract.lamOf q ρ₁)
                / (a + Work.LinnikContract.lamOf q ρ₀))
            + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
                (a + Work.LinnikContract.lamOf q ρ₀) (2 * μ))
        + (a + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε₁) + e2 := by
    have hb := HB91Aux.point_bound_q_R (q := q) (R := R) (N := χ₁.conductor)
      (hNq := χ₁.conductor_dvd_level) (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim
      ha hlam₁nn hδpos hδlt1 hLt haδL (s := sPt a L γ) hreγ himγR
      (hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hchisq hN3 hlogN1 γ hγR)
      par₁ hpar₁0 hpar₁1 (hSpr par₁ hpar₁2 γ).1 (hSpr par₁ hpar₁2 γ).2
      (hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim (sPt a L γ)
        (hRdpt γ hγR))
      (hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim)
      ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ)
      (by intro u hu
          rw [show ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ)
            = insert ρ₁ (insert ρ₀ {starRingEnd ℂ ρ₀}) by rfl] at hu
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h | h
          · rw [h]; exact hzr1
          · rw [h]; exact hzr0
          · rw [h]; exact hzrc)
      (by intro u hu
          rw [show ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ)
            = insert ρ₁ (insert ρ₀ {starRingEnd ℂ ρ₀}) by rfl] at hu
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h | h
          · rw [h]; exact himr1
          · rw [h]; exact himr0
          · rw [h]; exact himrc)
      (hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter γ)
    rw [DirichletCharacter.changeLevel_primitiveCharacter, hT1s1, hT1card] at hb
    simp only [he2def, hE2def, hE3def]
    linarith only [hb]
  -- ### `χ₀` at `σ + iγ⁰`
  have hV1 : SigmaP3L q L 1 (sPt a L γ) a (Work.LinnikContract.lamOf q ρ₁)
      ≤ Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a μ + e1' := by
    have hcc1 : |SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L γ) a
          (Work.LinnikContract.lamOf q ρ₁)
        - SigmaP3L 1 L 1 (sPt a L γ) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr := by
      have h := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) γ
      rwa [DirichletCharacter.changeLevel_one (one_dvd q)] at h
    have hb := HB91Aux.point_bound_principal_H (q := q) (T := R) (Rd := Rd)
      ha hlam₁nn hδpos hδlt1 hLt haδL haL hCzZeta hC0b' hnzδ (s := sPt a L γ) hreγ himγR
      (hRdpt γ hγR) (hSzeta γ).1 (hSzeta γ).2 hcc1
    rw [hP1] at hb
    simp only [he1'def, hE2zdef, hE3zdef]
    linarith only [hb]
  -- ### `χ₁` at `σ + 2iγ⁰`
  have hU2 : SigmaP3L q L χ₁ (sPt a L (2 * γ)) a (Work.LinnikContract.lamOf q ρ₁)
      ≤ -(Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
                (a + Work.LinnikContract.lamOf q ρ₁) (2 * μ)
            + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
                (a + Work.LinnikContract.lamOf q ρ₀) μ)
        + (a + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε₁) + e1 := by
    have hb := HB91Aux.point_bound_q_R (q := q) (R := R) (N := χ₁.conductor)
      (hNq := χ₁.conductor_dvd_level) (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim
      ha hlam₁nn hδpos hδlt1 hLt haδL (s := sPt a L (2 * γ)) hre2γ him2γR
      (hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hchisq hN3 hlogN1 (2 * γ) h2γR)
      par₁ hpar₁0 hpar₁1 (hSpr par₁ hpar₁2 (2 * γ)).1 (hSpr par₁ hpar₁2 (2 * γ)).2
      (hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim (sPt a L (2 * γ))
        (hRdpt (2 * γ) h2γR))
      (hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim)
      ({ρ₁, ρ₀} : Finset ℂ)
      (by intro u hu
          rw [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h
          · rw [h]; exact hzr1
          · rw [h]; exact hzr0)
      (by intro u hu
          rw [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h
          · rw [h]; exact himr1
          · rw [h]; exact himr0)
      (hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter (2 * γ))
    rw [DirichletCharacter.changeLevel_primitiveCharacter, hT0s2, hT0card] at hb
    simp only [he1def, hE2def, hE3def]
    linarith only [hb]
  -- ### `χ₀` at `σ + 2iγ⁰`
  have hV2 : SigmaP3L q L 1 (sPt a L (2 * γ)) a (Work.LinnikContract.lamOf q ρ₁)
      ≤ Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a (2 * μ) + e1' := by
    have hcc2 : |SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (2 * γ)) a
          (Work.LinnikContract.lamOf q ρ₁)
        - SigmaP3L 1 L 1 (sPt a L (2 * γ)) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr := by
      have h := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (2 * γ)
      rwa [DirichletCharacter.changeLevel_one (one_dvd q)] at h
    have hb := HB91Aux.point_bound_principal_H (q := q) (T := R) (Rd := Rd)
      ha hlam₁nn hδpos hδlt1 hLt haδL haL hCzZeta hC0b' hnzδ (s := sPt a L (2 * γ)) hre2γ him2γR
      (hRdpt (2 * γ) h2γR) (hSzeta (2 * γ)).1 (hSzeta (2 * γ)).2 hcc2
    rw [hP2] at hb
    simp only [he1'def, hE2zdef, hE3zdef]
    linarith only [hb]
  -- ## the error terms
  have he1E : e1 ≤ E := by
    rw [he1def]
    refine heE _ ?_
    have h := hcFar 2 (by norm_num)
    have hC0cnn : 0 ≤ C0c := by rw [hC0cdef]; positivity
    linarith only [h, hC0cnn]
  have he1'E : e1' ≤ E := by
    rw [he1'def]
    refine heEz _ ?_
    have h1C0 : ((a + Work.LinnikContract.lamOf q ρ₁) / L) * C₀ ≤ C0c := by
      rw [hC0cdef]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup hLpos.le) hC₀pos.le
    have hFcnn : 0 ≤ Fc := by rw [hFcdef]; positivity
    linarith only [h1C0, hFcnn]
  have he2E : e2 ≤ E := by
    rw [he2def]
    refine heE _ ?_
    have h := hcFar 3 (by norm_num)
    have hC0cnn : 0 ≤ C0c := by rw [hC0cdef]; positivity
    linarith only [h, hC0cnn]
  have herr : (K + 1) ^ 2 * e1' + (K ^ 2 + 1 / 2) * e1 + 2 * K * e2 + (1 / 2) * e1
      ≤ 2 * (K + 1) ^ 2 * E := by
    have h1 : (K + 1) ^ 2 * e1' ≤ (K + 1) ^ 2 * E :=
      mul_le_mul_of_nonneg_left he1'E (by positivity)
    have h2 : (K ^ 2 + 1 / 2) * e1 ≤ (K ^ 2 + 1 / 2) * E :=
      mul_le_mul_of_nonneg_left he1E (by positivity)
    have h3 : 2 * K * e2 ≤ 2 * K * E := mul_le_mul_of_nonneg_left he2E (by positivity)
    have h4 : (1 / 2) * e1 ≤ (1 / 2) * E := mul_le_mul_of_nonneg_left he1E (by norm_num)
    have hid : (K + 1) ^ 2 * E + (K ^ 2 + 1 / 2) * E + 2 * K * E + (1 / 2) * E
        = 2 * (K + 1) ^ 2 * E := by ring
    linarith only [h1, h2, h3, h4, hid]
  -- ## the pointwise combination of HB (8.5)
  have hcomb : 0 ≤ (K ^ 2 + 1 / 2) *
          (SigmaP3L q L 1 (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁)
            + SigmaP3L q L χ₁ (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁))
        + 2 * K * (SigmaP3L q L 1 (sPt a L γ) a (Work.LinnikContract.lamOf q ρ₁)
            + SigmaP3L q L χ₁ (sPt a L γ) a (Work.LinnikContract.lamOf q ρ₁))
        + (1 / 2) * (SigmaP3L q L 1 (sPt a L (2 * γ)) a (Work.LinnikContract.lamOf q ρ₁)
            + SigmaP3L q L χ₁ (sPt a L (2 * γ)) a (Work.LinnikContract.lamOf q ρ₁)) := by
    have h := hb85Real (q := q) χ₁ hsq (K := K) (σ := 1 + a / L) (γ := γ) (a := a)
      (lam₁ := Work.LinnikContract.lamOf q ρ₁) hK.le hσ1 ha hlam₁nn
    rw [← hLdef] at h
    simpa [sPt] using h
  -- ## the A- and B-brackets of HB (8.3)
  have hAnn : 0 ≤ (K ^ 2 + 1) * Work.ZeroFreeTables.Table4.P3AB
        (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₀) μ
      + 2 * K * Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
        (a + Work.LinnikContract.lamOf q ρ₁) μ
      - 2 * K * Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a μ :=
    Work.ZeroFreeTables.Table4.A83_nonneg ha hlam₁nn hlamle hK hcond
  have hBnn : 0 ≤ 2 * K * Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
        (a + Work.LinnikContract.lamOf q ρ₀) (2 * μ)
      + (1 / 2) * Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁)
        (a + Work.LinnikContract.lamOf q ρ₁) (2 * μ)
      - (1 / 2) * Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a (2 * μ) :=
    Work.ZeroFreeTables.Table4.B83_nonneg ha hlam₁nn hlamle hK4 hcond
  -- ## the assembly
  have hstep : 0 ≤ (K ^ 2 + 1 / 2) * (Work.ZeroFreeTables.P3R
          ((a + Work.LinnikContract.lamOf q ρ₁) / a) - Work.ZeroFreeTables.P3R 1)
      - 2 * K * Work.ZeroFreeTables.P3R ((a + Work.LinnikContract.lamOf q ρ₁)
          / (a + Work.LinnikContract.lamOf q ρ₀))
      + (K + 1) ^ 2 * ((a + Work.LinnikContract.lamOf q ρ₁) * (1 / 8))
      + (K + 1) ^ 2 * ((a + Work.LinnikContract.lamOf q ρ₁) * ε₁) + 2 * (K + 1) ^ 2 * E := by
    have h1 := mul_le_mul_of_nonneg_left hV0 (by positivity : (0 : ℝ) ≤ K ^ 2 + 1 / 2)
    have h2 := mul_le_mul_of_nonneg_left hU0 (by positivity : (0 : ℝ) ≤ K ^ 2 + 1 / 2)
    have h3 := mul_le_mul_of_nonneg_left hV1 (by positivity : (0 : ℝ) ≤ 2 * K)
    have h4 := mul_le_mul_of_nonneg_left hU1 (by positivity : (0 : ℝ) ≤ 2 * K)
    have h5 := mul_le_mul_of_nonneg_left hV2 (by positivity : (0 : ℝ) ≤ 1 / 2)
    have h6 := mul_le_mul_of_nonneg_left hU2 (by positivity : (0 : ℝ) ≤ 1 / 2)
    ring_nf at hcomb h1 h2 h3 h4 h5 h6 hAnn hBnn herr ⊢
    linarith only [hcomb, h1, h2, h3, h4, h5, h6, hAnn, hBnn, herr]
  -- ## the target inequality
  have hgoal : Work.ZeroFreeTables.p83 (Work.LinnikContract.lamOf q ρ₁)
      (Work.LinnikContract.lamOf q ρ₀) a K
      = (K ^ 2 + 1 / 2) * (Work.ZeroFreeTables.P3R ((a + Work.LinnikContract.lamOf q ρ₁) / a)
          - Work.ZeroFreeTables.P3R 1)
        - 2 * K * Work.ZeroFreeTables.P3R ((a + Work.LinnikContract.lamOf q ρ₁)
            / (a + Work.LinnikContract.lamOf q ρ₀))
        + (K + 1) ^ 2 * ((a + Work.LinnikContract.lamOf q ρ₁) * (1 / 8)) := by
    rw [Work.ZeroFreeTables.p83]; ring
  have hbudget := hb83Budget (K := K) (a := a) (α := a + Work.LinnikContract.lamOf q ρ₁)
    (ε := ε) (ε₁ := ε₁) (E := E) hK.le ha.le (by linarith only [hlam₁nn]) hε hε₁bud hEbound
  rw [hgoal]
  have h2 : (K + 1) ^ 2 * ((a + Work.LinnikContract.lamOf q ρ₁) * ε)
      = (K + 1) ^ 2 * (a + Work.LinnikContract.lamOf q ρ₁) * ε := by ring
  rw [← h2]
  linarith only [hstep, hbudget]

end Work.ZeroFreeTables.OffAxis

