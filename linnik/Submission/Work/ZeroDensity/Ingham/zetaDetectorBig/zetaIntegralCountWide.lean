import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Work.ZeroDensity.Ingham.zetaMeanValueSeparated
import Submission.Work.ZeroDensity.Ingham.cardLeOfSeparated
import Submission.Work.ZeroDensity.Ingham.KboundOfSmallP
import Submission.Work.ZeroDensity.Ingham.loYpowBound
import Submission.Work.ZeroDensity.Ingham.windowIntegralHolder
import Submission.Work.ZeroDensity.Ingham.sumWindowIntegral_le
import Submission.Work.ZeroDensity.Ingham.perZero_rpow
import Submission.Work.ZeroDensity.Ingham.gammaStripBound
import Submission.Work.ZeroDensity.Ingham.absorbShiftArith
import Submission.Work.ZeroDensity.Ingham.zetaFourthSymm
import Submission.Work.ZeroDensity.Montgomery.holderThirds
import Submission.Work.ZeroDensity.Huxley.largeValuesMM
import Submission.Work.ZeroDensity.Zeta.dirichletPoly_meanValue_integral_corrected
import Submission.Work.ZeroDensity.Ingham.zetaDetectorBig.sumWindowShift_le
import Submission.Work.ZeroDensity.Ingham.zetaDetectorBig.mkSecondMomentSym
import Submission.Work.ZeroDensity.Ingham.zetaDetectorBig.loYpowBoundLe
import Submission.Work.ZeroDensity.Ingham.zetaDetectorBig.perZeroBound
import Submission.Work.ZeroDensity.Ingham.zetaDetectorBig.wideIntegralArith

/-!
# The count of zeros detected by the *wide* Ingham/Montgomery contour integral

This file proves `Work.ZeroDensity.Ingham.zetaDetectorBig.zetaIntegralCountWide`: if `R` is a
`1`-separated (in imaginary part) set of zeros of `ζ` with `σ ≤ Re ≤ 1`, `|Im| ≤ T`, and at each
zero `z ∈ R` the truncated critical-line integral

`Y^{1/2-Re z} ∫_{-A log(AT)}^{A log(AT)} critIntegrand K z v dv`

is at least `1/12`, then `#R ≪ T^ε T^{1/3}(T+K)^{2/3} Y^{(2-4σ)/3}` — the Montgomery–Vaughan
(28.39)-type count, in the *wide* range `A ≥ 6`, `1 ≤ K`, `1 ≤ Y ≤ (A T)²` (no upper bound on `K`
at all) and for all `1/2 ≤ σ ≤ 1`.

## Route

Write `L = A log (A T)` for the half-length of the detector integral.

* per zero `z`: three-function Hölder (`perZeroBound`) and the uniform bound
  `‖Γ(1/2-Re z + iv)‖ ≤ Cg/(σ-1/2)` (`gammaStripBound`) turn the hypothesis into
  `1/12 ≤ Y^{1/2-σ}(Cg/(σ-1/2))(2L)^{1/4}(∫‖ζ‖⁴)^{1/4}(∫‖M_K‖²)^{1/2}`; raising to the power `4/3`
  (`perZero_rpow`) then gives
  `(1/12)^{4/3} ≤ W Y^{(2-4σ)/3} (∫‖ζ‖⁴)^{1/3}(∫‖M_K‖²)^{2/3}` with
  `W = (Cg/(σ-1/2))^{4/3}(2L)^{1/3}`;
* summing over `z ∈ R` with the sum-level Hölder inequality (`holderThirds`) gives
  `#R (1/12)^{4/3} ≤ W Y^{(2-4σ)/3} (Σ_z∫‖ζ‖⁴)^{1/3}(Σ_z∫‖M_K‖²)^{2/3}`;
* the two sums are bounded by the overlap estimate `sumWindowShift_le` together with the
  *integral* fourth moment of `ζ` on the critical line (`zetaFourthSymm`) and the mean square of the
  truncated Möbius polynomial (`mkSecondMomentSym`), giving `(2L+1)·2C₄(T+L)log⁴(T+L)` and
  `(2L+1)·C_M(T+L+K)log²(K+2)`;
* the resulting explicit expression is absorbed into `C·T^ε·T^{1/3}(T+K)^{2/3}` by
  `wideIntegralArith`, whose hypothesis is `K ≤ 6 Ã² T³` for the *rescaled* truncation parameter
  `Ã = A (C_K + 1)`, where `C_K` is the (existential) constant of `KboundOfSmallP`; indeed
  `6 Ã² ≥ C_K A²`.  The detector integral is simply extended from `[-L, L]` to
  `[-Ã log(ÃT), Ã log(ÃT)]`, which costs nothing because the integrand is non-negative.
  The two exceptional cases are
  * `σ - 1/2 ≤ 1/(2 log (A T))`: the trivial count `#R ≤ 2T+1` suffices (`loYpowBoundLe`), and
  * `K > 6 Ã² T³ ≥ C_K A² T³`: again the trivial count suffices, by the contrapositive of
    `KboundOfSmallP`.
-/

namespace Work.ZeroDensity.Ingham.zetaDetectorBig

open scoped Classical BigOperators
open MeasureTheory

set_option maxHeartbeats 2000000

/-! ## Elementary helpers -/

/-- `2 ≤ log 12`. -/
private lemma two_le_log_twelve : (2 : ℝ) ≤ Real.log 12 := by
  have h := Real.log_two_gt_d9
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
  have h3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_three]
  rw [show (12 : ℝ) = 6 * 2 by norm_num,
    Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), hlog6]
  linarith

/-- Continuity of `v ↦ ‖ζ(1/2 + (γ + v)i)‖`. -/
lemma continuous_zetaLineNorm (γ : ℝ) :
    Continuous fun v : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ := by
  have hζ : ContinuousOn riemannZeta ({1}ᶜ : Set ℂ) :=
    fun s hs => (differentiableAt_riemannZeta hs).continuousAt.continuousWithinAt
  have hlin : Continuous fun v : ℝ => (1 / 2 : ℂ) + (γ : ℂ) * Complex.I + (v : ℂ) * Complex.I := by
    fun_prop
  have hmem : ∀ v : ℝ, (1 / 2 : ℂ) + (γ : ℂ) * Complex.I + (v : ℂ) * Complex.I ∈ ({1}ᶜ : Set ℂ) := by
    intro v
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h1 : ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I + (v : ℂ) * Complex.I).re = (1 : ℂ).re := by rw [h]
    simp [Complex.add_re, Complex.mul_re] at h1
  exact (hζ.comp_continuous hlin hmem).norm

/-- Continuity of `v ↦ ‖M_K(1/2 + (γ + v)i)‖`. -/
lemma continuous_mkLineNorm (K : ℕ) (γ : ℝ) :
    Continuous fun v : ℝ => ‖MK K ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ := by
  unfold MK
  refine Continuous.norm (continuous_finsetSum _ (fun n hn => ?_))
  refine Continuous.mul continuous_const ?_
  refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  exact_mod_cast (by omega : n ≠ 0)

/-- `a + vi` is not a pole of `Γ` when `-1 < a < 0`. -/
private lemma gamma_line_ne_nat_neg (a : ℝ) (ha1 : -1 < a) (ha2 : a < 0) (v : ℝ) (m : ℕ) :
    ((a : ℂ) + (v : ℂ) * Complex.I) ≠ -(m : ℂ) := by
  intro h
  have hre : ((a : ℂ) + (v : ℂ) * Complex.I).re = a := by simp
  have h2 := congrArg Complex.re h
  rw [hre] at h2
  rcases m with _ | k
  · simp at h2
    linarith
  · simp at h2
    linarith

/-- Continuity of `v ↦ ‖Γ(a + vi)‖` for `-1 < a < 0`. -/
lemma continuous_gammaLineNorm (a : ℝ) (ha1 : -1 < a) (ha2 : a < 0) :
    Continuous fun v : ℝ => ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * Complex.I)‖ := by
  have hG : ContinuousOn Complex.Gamma {x : ℂ | ∀ m : ℕ, x ≠ -(m : ℂ)} :=
    fun s hs => (Complex.continuousAt_Gamma s hs).continuousWithinAt
  have hlin : Continuous fun v : ℝ => (a : ℂ) + (v : ℂ) * Complex.I := by fun_prop
  have hmem : ∀ v : ℝ, (a : ℂ) + (v : ℂ) * Complex.I ∈ {x : ℂ | ∀ m : ℕ, x ≠ -(m : ℂ)} :=
    fun v m => gamma_line_ne_nat_neg a ha1 ha2 v m
  exact (hG.comp_continuous hlin hmem).norm

/-- A `1`-separated (in imaginary part) set of complex numbers with `|Im| ≤ T` has at most `2T+1`
elements. -/
lemma card_le_two_mul_add_one (R : Finset ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hbd : ∀ z ∈ R, |z.im| ≤ T)
    (hsep : ∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) :
    (R.card : ℝ) ≤ 2 * T + 1 := by
  have hinj : Set.InjOn Complex.im ↑R := by
    intro z hz z' hz' heq
    by_contra hne
    have h := hsep z hz z' hz' hne
    rw [heq, sub_self, abs_zero] at h
    linarith
  have hcard : R.card = (R.image Complex.im).card := (Finset.card_image_of_injOn hinj).symm
  rw [hcard]
  have h := Work.ZeroDensity.Ingham.cardLeOfSeparated (S := R.image Complex.im) (a := -T) (b := T)
    (by linarith) ?_ ?_
  · linarith
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨by linarith [neg_abs_le z.im, hbd z hz], by linarith [le_abs_self z.im, hbd z hz]⟩
  · intro x hx y hy hxy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hy
    exact hsep z hz z' hz' (fun h => hxy (by rw [h]))

/-! ## The count -/

theorem zetaIntegralCountWide :
    ∀ A : ℝ, 6 ≤ A → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ),
      1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T → ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
        ∀ R : Finset ℂ,
          (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
            σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) →
          (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) →
          (∀ z ∈ R, (1 : ℝ) / 12 ≤ Y ^ (1 / 2 - z.re) *
            ∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
              Work.ZeroDensity.Ingham.critIntegrand K z v) →
          (R.card : ℝ) ≤ C * T ^ ε *
            (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) := by
  intro A hA ε hε
  obtain ⟨Cg, hCgpos, hCgsup⟩ := Work.ZeroDensity.Ingham.gammaStripBound
  obtain ⟨C4, hC4pos, hC4⟩ := Work.ZeroDensity.Ingham.zetaFourthSymm
  obtain ⟨CM, hCMpos, hCM⟩ := mkSecondMomentSym
  obtain ⟨Clo, hClopos, hlo⟩ := loYpowBoundLe
  obtain ⟨CK, hCKpos, hKb⟩ := Work.ZeroDensity.Ingham.KboundOfSmallP
  -- the rescaled truncation parameter `Ã = A (C_K + 1) ≥ A`, so that `6 Ã² ≥ C_K A²`
  obtain ⟨Ã, hÃdef⟩ : ∃ Ã : ℝ, Ã = A * (CK + 1) := ⟨_, rfl⟩
  have hÃ6 : 6 ≤ Ã := by
    rw [hÃdef]
    nlinarith
  obtain ⟨Car, hCarpos, har⟩ :=
    wideIntegralArith Ã ε Cg C4 CM hÃ6 hε hCgpos hC4pos hCMpos
  refine ⟨max Car (max Clo 1), by positivity, ?_⟩
  intro σ T hσ1 hσ2 hT K Y hK hY hY2 R hz hsep hint
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have hTnn : 0 ≤ T := hTpos.le
  have hAT1 : 1 < A * T := by nlinarith
  have hlogpos : 0 < Real.log (A * T) := Real.log_pos hAT1
  have hÃpos : 0 < Ã := by linarith
  have hÃT1 : 1 < Ã * T := by nlinarith
  have hlogÃpos : 0 < Real.log (Ã * T) := Real.log_pos hÃT1
  have hlogle : Real.log (A * T) ≤ Real.log (Ã * T) := Real.log_le_log (by positivity) (by nlinarith)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK2nn : (0 : ℝ) ≤ (K : ℝ) + 2 := by linarith
  have hlogKnn : 0 ≤ Real.log ((K : ℝ) + 2) := Real.log_nonneg (by linarith)
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = A * Real.log (A * T) := ⟨_, rfl⟩
  obtain ⟨L', hL'def⟩ : ∃ L' : ℝ, L' = Ã * Real.log (Ã * T) := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hLdef]; exact mul_pos hApos hlogpos
  have hLnn : 0 ≤ L := hLpos.le
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h12 : Real.log 12 ≤ Real.log (A * T) := Real.log_le_log (by norm_num) (by nlinarith)
    nlinarith [two_le_log_twelve, h12, hA]
  have hL'pos : 0 < L' := by rw [hL'def]; exact mul_pos hÃpos hlogÃpos
  have hL'nn : 0 ≤ L' := hL'pos.le
  have hL'1 : 1 ≤ L' := by
    rw [hL'def]
    have h12 : Real.log 12 ≤ Real.log (Ã * T) := Real.log_le_log (by norm_num) (by nlinarith)
    nlinarith [two_le_log_twelve, h12, hÃ6]
  have hLL' : L ≤ L' := by
    rw [hLdef, hL'def]
    exact mul_le_mul (by nlinarith [hApos, hCKpos]) hlogle hlogpos.le (le_of_lt hÃpos)
  have hL'Int : -L' ≤ L' := by linarith
  have h2L1nn : (0 : ℝ) ≤ 2 * L' + 1 := by linarith
  have hTL'2 : 2 ≤ T + L' := by linarith
  have hTL'1 : 1 ≤ T + L' := by linarith
  have hTL'nn : (0 : ℝ) ≤ T + L' := by linarith
  have hlogTL'nn : 0 ≤ Real.log (T + L') := Real.log_nonneg hTL'1
  have hYnn : 0 ≤ Y := by linarith
  have hKres : CK * A ^ 2 * T ^ 3 ≤ 6 * Ã ^ 2 * T ^ 3 := by
    have h1 : CK ≤ 6 * (CK + 1) ^ 2 := by nlinarith [hCKpos, sq_nonneg (CK + 1)]
    have h2 : (0 : ℝ) ≤ A ^ 2 * T ^ 3 := by positivity
    rw [hÃdef]
    calc CK * A ^ 2 * T ^ 3 = CK * (A ^ 2 * T ^ 3) := by ring
      _ ≤ (6 * (CK + 1) ^ 2) * (A ^ 2 * T ^ 3) := mul_le_mul_of_nonneg_right h1 h2
      _ = 6 * (A * (CK + 1)) ^ 2 * T ^ 3 := by ring
  -- the two integrands as functions of a single real variable
  have hzeta_cont : Continuous fun t : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 := by
    have h := (continuous_zetaLineNorm (0 : ℝ)).pow 4
    have h' : (fun t : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I + (t : ℂ) * Complex.I)‖)
        = fun t : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      funext t
      rw [show ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I + (t : ℂ) * Complex.I)
          = ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) from by push_cast; ring]
    rw [h'] at h
    exact h
  have hzeta_nn : ∀ t : ℝ, 0 ≤ ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 :=
    fun t => by positivity
  have hmk_cont : Continuous fun t : ℝ => ‖MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    have h := (continuous_mkLineNorm K (0 : ℝ)).pow 2
    have h' : (fun t : ℝ => ‖MK K ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I + (t : ℂ) * Complex.I)‖)
        = fun t : ℝ => ‖MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      funext t
      rw [show ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I + (t : ℂ) * Complex.I)
          = ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) from by push_cast; ring]
    rw [h'] at h
    exact h
  have hmk_nn : ∀ t : ℝ, 0 ≤ ‖MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    fun t => by positivity
  by_cases hmain : 1 / (2 * Real.log (A * T)) < σ - 1 / 2 ∧ (K : ℝ) ≤ 6 * Ã ^ 2 * T ^ 3
  · -- ### main branch: run the detector count with the half-length `L'`
    obtain ⟨hδlt, hKle⟩ := hmain
    have hδpos : 0 < σ - 1 / 2 := by
      have h1 : 0 < 1 / (2 * Real.log (A * T)) := by positivity
      linarith
    have hσgt : 1 / 2 < σ := by linarith
    have hδle : σ - 1 / 2 ≤ 1 / 2 := by linarith
    have hδlt' : 1 / (2 * Real.log (Ã * T)) < σ - 1 / 2 := by
      have ha : 0 < 2 * Real.log (A * T) := by linarith
      have hb : 2 * Real.log (A * T) ≤ 2 * Real.log (Ã * T) := by linarith
      have hle : 1 / (2 * Real.log (Ã * T)) ≤ 1 / (2 * Real.log (A * T)) :=
        one_div_le_one_div_of_le ha hb
      linarith
    -- the window sums
    have hwinZ := sumWindowShift_le (fun t : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4)
      R hL'1 hTnn hzeta_cont hzeta_nn (fun z hzm => (hz z hzm).2.2.2) hsep
    have hwinM := sumWindowShift_le (fun t : ℝ => ‖MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      R hL'1 hTnn hmk_cont hmk_nn (fun z hzm => (hz z hzm).2.2.2) hsep
    have hSumZ : (∑ z ∈ R, ∫ v in (-L')..L',
          ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4)
        ≤ (2 * L' + 1) * ((2 * C4 * (T + L')) * (Real.log (T + L')) ^ 4) := by
      refine le_trans hwinZ ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine le_trans (hC4 (T + L') hTL'2) ?_
      have hle : C4 * (T + L') ≤ 2 * C4 * (T + L') := by
        have h0 : (0 : ℝ) ≤ C4 * (T + L') := by positivity
        linarith
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    have hSumM : (∑ z ∈ R, ∫ v in (-L')..L',
          ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2)
        ≤ (2 * L' + 1) * ((CM * (T + L' + (K : ℝ))) * (Real.log ((K : ℝ) + 2)) ^ 2) := by
      refine le_trans hwinM ?_
      exact mul_le_mul_of_nonneg_left (hCM K (T + L') hK hTL'1) (by positivity)
    -- per zero: the input of `perZero_rpow`
    have hper : ∀ z ∈ R, (1 / 12 : ℝ) ^ ((4 : ℝ) / 3) ≤
        (Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3) *
          Y ^ ((2 - 4 * σ) / 3) *
          (∫ v in (-L')..L', ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 3) *
          (∫ v in (-L')..L', ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2) ^ ((2 : ℝ) / 3) := by
      intro z hzmem
      obtain ⟨-, hzσ, hz1, -⟩ := hz z hzmem
      have hcontζ : Continuous fun v : ℝ =>
          ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ :=
        continuous_zetaLineNorm z.im
      have hcontMK : Continuous fun v : ℝ =>
          ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ :=
        continuous_mkLineNorm K z.im
      have hcontG : Continuous fun v : ℝ =>
          ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖ :=
        continuous_gammaLineNorm (1 / 2 - z.re) (by linarith) (by linarith)
      have hgam : ∀ v : ℝ,
          ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖ ≤ Cg / (σ - 1 / 2) := by
        intro v
        have h := hCgsup (σ - 1 / 2) (1 / 2 - z.re) v hδpos hδle (by linarith) (by linarith)
        have hxnn : (0 : ℝ) ≤ Cg * (1 / (σ - 1 / 2)) := by positivity
        have h1v : (1 : ℝ) ≤ 1 + |v| := by linarith [abs_nonneg v]
        calc ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖
            ≤ Cg * (1 / (σ - 1 / 2)) / (1 + |v|) := h
          _ ≤ Cg * (1 / (σ - 1 / 2)) / 1 := div_le_div_of_nonneg_left hxnn (by norm_num) h1v
          _ = Cg / (σ - 1 / 2) := by ring
      have hZ := perZeroBound K z L' Cg (σ - 1 / 2) hL'nn hCgpos hδpos hgam hcontζ hcontMK hcontG
      -- extend the detector integral from `[-L, L]` to `[-L', L']`
      have hcrit_cont : Continuous fun v : ℝ => Work.ZeroDensity.Ingham.critIntegrand K z v := by
        unfold Work.ZeroDensity.Ingham.critIntegrand
        exact (hcontζ.mul hcontMK).mul hcontG
      have hext : (∫ v in (-L)..L, Work.ZeroDensity.Ingham.critIntegrand K z v)
          ≤ ∫ v in (-L')..L', Work.ZeroDensity.Ingham.critIntegrand K z v :=
        intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
          (Filter.Eventually.of_forall fun v => by
            rw [Work.ZeroDensity.Ingham.critIntegrand]; positivity)
          (hcrit_cont.intervalIntegrable _ _)
      have hhint0 := hint z hzmem
      rw [← hLdef] at hhint0
      have hhint : (1 : ℝ) / 12 ≤ Y ^ (1 / 2 - z.re) *
          ∫ v in (-L')..L', Work.ZeroDensity.Ingham.critIntegrand K z v :=
        le_trans hhint0 (mul_le_mul_of_nonneg_left hext (Real.rpow_nonneg hYnn _))
      have hyexp : Y ^ (1 / 2 - z.re) ≤ Y ^ (1 / 2 - σ) :=
        Real.rpow_le_rpow_of_exponent_le hY (by linarith)
      have hIntnn : 0 ≤ ∫ v in (-L')..L', Work.ZeroDensity.Ingham.critIntegrand K z v :=
        intervalIntegral.integral_nonneg hL'Int (fun v _ => by
          rw [Work.ZeroDensity.Ingham.critIntegrand]; positivity)
      have hYexpnn : 0 ≤ Y ^ (1 / 2 - σ) := Real.rpow_nonneg hYnn _
      have hSZnn : 0 ≤ ∫ v in (-L')..L',
          ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4 :=
        intervalIntegral.integral_nonneg hL'Int (fun v _ => by positivity)
      have hSMnn : 0 ≤ ∫ v in (-L')..L',
          ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2 :=
        intervalIntegral.integral_nonneg hL'Int (fun v _ => by positivity)
      have hone : (1 / 12 : ℝ) ≤ Y ^ (1 / 2 - σ) *
          ((Cg / (σ - 1 / 2)) * (2 * L') ^ ((1 : ℝ) / 4) *
            (∫ v in (-L')..L', ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) *
            (∫ v in (-L')..L', ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2)) := by
        refine le_trans hhint (mul_le_mul hyexp hZ hIntnn hYexpnn)
      have hWpow : (((Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3)) ^ ((3 : ℝ) / 4))
          = (Cg / (σ - 1 / 2)) * (2 * L') ^ ((1 : ℝ) / 4) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Cg / (σ - 1 / 2)) ((4 : ℝ) / 3) ((3 : ℝ) / 4),
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * L') ((1 : ℝ) / 3) ((3 : ℝ) / 4)]
        norm_num
      have hpr := Work.ZeroDensity.Ingham.perZero_rpow (Y := Y) (σ := σ)
        (W := (Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3))
        (A := ∫ v in (-L')..L',
          ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4)
        (B := ∫ v in (-L')..L',
          ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2)
        (M := 1) hY (by positivity) hSZnn hSMnn (by norm_num) (by
          calc (1 / 12 : ℝ) ≤ Y ^ (1 / 2 - σ) *
                ((Cg / (σ - 1 / 2)) * (2 * L') ^ ((1 : ℝ) / 4) *
                  (∫ v in (-L')..L', ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) *
                  (∫ v in (-L')..L', ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2)) := hone
            _ = Y ^ (1 / 2 - σ) *
                (((Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3)) ^ ((3 : ℝ) / 4)) *
                (∫ v in (-L')..L', ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) *
                (∫ v in (-L')..L', ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2) *
                1 ^ ((1 : ℝ) / 4) := by
                  rw [hWpow, Real.one_rpow]; ring)
      have hconc : (1 / 12 : ℝ) ^ ((4 : ℝ) / 3) ≤
          (Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3) *
            Y ^ ((2 - 4 * σ) / 3) *
            (∫ v in (-L')..L', ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 3) *
            (∫ v in (-L')..L', ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((2 : ℝ) / 3) := by
        refine hpr.trans (le_of_eq ?_)
        rw [Real.one_rpow]
        ring
      have hζid : (∫ v in (-L')..L',
            ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4)
          = ∫ v in (-L')..L', ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4 := by
        apply intervalIntegral.integral_congr
        intro v _
        dsimp only
        rw [show ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)
            = ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I) from by push_cast; ring]
      have hMKid : (∫ v in (-L')..L',
            ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2)
          = ∫ v in (-L')..L', ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro v _
        dsimp only
        rw [show ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)
            = ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I) from by push_cast; ring]
      rw [hζid, hMKid] at hconc
      exact hconc
    -- sum over the zeros
    have hcard_sum : (R.card : ℝ) * (1 / 12 : ℝ) ^ ((4 : ℝ) / 3)
        = ∑ _z ∈ R, (1 / 12 : ℝ) ^ ((4 : ℝ) / 3) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hSumZnn : 0 ≤ ∑ z ∈ R, ∫ v in (-L')..L',
        ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4 :=
      Finset.sum_nonneg (fun z _ => intervalIntegral.integral_nonneg hL'Int (fun v _ => by positivity))
    have hSumMnn : 0 ≤ ∑ z ∈ R, ∫ v in (-L')..L',
        ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2 :=
      Finset.sum_nonneg (fun z _ => intervalIntegral.integral_nonneg hL'Int (fun v _ => by positivity))
    have hholder := Work.ZeroDensity.Montgomery.holderThirds R
      (fun z => ∫ v in (-L')..L', ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4)
      (fun z => ∫ v in (-L')..L', ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2)
      (fun z _ => intervalIntegral.integral_nonneg hL'Int (fun v _ => by positivity))
      (fun z _ => intervalIntegral.integral_nonneg hL'Int (fun v _ => by positivity))
    have hstep1 : (R.card : ℝ) ≤
        (12 : ℝ) ^ ((4 : ℝ) / 3) *
          ((Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3) *
            Y ^ ((2 - 4 * σ) / 3) *
            ((∑ z ∈ R, ∫ v in (-L')..L',
                ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 3) *
              (∑ z ∈ R, ∫ v in (-L')..L',
                ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2) ^ ((2 : ℝ) / 3))) := by
      have hc12 : ((1 : ℝ) / 12) ^ ((4 : ℝ) / 3) * (12 : ℝ) ^ ((4 : ℝ) / 3) = 1 := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 12) (by norm_num : (0 : ℝ) ≤ 12)]
        norm_num
      have hc12pos : (0 : ℝ) < (12 : ℝ) ^ ((4 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
      have hs := Finset.sum_le_sum hper
      have hfac : (∑ z ∈ R, ((Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3) *
              Y ^ ((2 - 4 * σ) / 3) *
              (∫ v in (-L')..L', ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 3) *
              (∫ v in (-L')..L', ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2) ^ ((2 : ℝ) / 3)))
          = (Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3) *
              Y ^ ((2 - 4 * σ) / 3) *
              (∑ z ∈ R,
                (∫ v in (-L')..L', ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 3) *
                (∫ v in (-L')..L', ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2) ^ ((2 : ℝ) / 3)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun z _ => by ring)
      have hsum_le : (R.card : ℝ) * (1 / 12 : ℝ) ^ ((4 : ℝ) / 3) ≤
          (Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3) *
            Y ^ ((2 - 4 * σ) / 3) *
            ((∑ z ∈ R, ∫ v in (-L')..L',
                ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 3) *
              (∑ z ∈ R, ∫ v in (-L')..L',
                ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2) ^ ((2 : ℝ) / 3)) := by
        rw [hcard_sum]
        refine le_trans hs ?_
        rw [hfac]
        exact mul_le_mul_of_nonneg_left hholder (by positivity)
      have h := mul_le_mul_of_nonneg_right hsum_le hc12pos.le
      rw [mul_assoc, hc12, mul_one] at h
      exact h.trans (le_of_eq (by ring))
    -- the two window sums, in the shape the arithmetic lemma consumes
    have hSZbound : (∑ z ∈ R, ∫ v in (-L')..L',
          ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 3)
        ≤ ((2 * L' + 1) * ((2 * C4 * (T + L')) * (Real.log (T + L')) ^ 4)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hSumZnn hSumZ (by norm_num)
    have hSMbound : (∑ z ∈ R, ∫ v in (-L')..L',
          ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2) ^ ((2 : ℝ) / 3)
        ≤ ((2 * L' + 1) * ((CM * (T + L' + (K : ℝ))) * (Real.log ((K : ℝ) + 2)) ^ 2)) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow hSumMnn hSumM (by norm_num)
    have hexpZ : ((2 * L' + 1) * ((2 * C4 * (T + L')) * (Real.log (T + L')) ^ 4)) ^ ((1 : ℝ) / 3)
        = (2 * L' + 1) ^ ((1 : ℝ) / 3) * (2 * C4 * (T + L')) ^ ((1 : ℝ) / 3) *
            (Real.log (T + L')) ^ ((4 : ℝ) / 3) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast (Real.log (T + L')) 4,
        ← Real.rpow_mul (Real.log_nonneg hTL'1) ((4 : ℕ) : ℝ) ((1 : ℝ) / 3),
        show (((4 : ℕ) : ℝ) * ((1 : ℝ) / 3)) = (4 : ℝ) / 3 by norm_num]
      ring
    have hexpM : ((2 * L' + 1) * ((CM * (T + L' + (K : ℝ))) * (Real.log ((K : ℝ) + 2)) ^ 2)) ^ ((2 : ℝ) / 3)
        = (2 * L' + 1) ^ ((2 : ℝ) / 3) * (CM * (T + L' + (K : ℝ))) ^ ((2 : ℝ) / 3) *
            (Real.log ((K : ℝ) + 2)) ^ ((4 : ℝ) / 3) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast (Real.log ((K : ℝ) + 2)) 2,
        ← Real.rpow_mul (Real.log_nonneg (by linarith : (1 : ℝ) ≤ (K : ℝ) + 2)) ((2 : ℕ) : ℝ) ((2 : ℝ) / 3),
        show (((2 : ℕ) : ℝ) * ((2 : ℝ) / 3)) = (4 : ℝ) / 3 by norm_num]
      ring
    have hSZb : (∑ z ∈ R, ∫ v in (-L')..L',
          ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 3)
        ≤ (2 * L' + 1) ^ ((1 : ℝ) / 3) * (2 * C4 * (T + L')) ^ ((1 : ℝ) / 3) *
            (Real.log (T + L')) ^ ((4 : ℝ) / 3) :=
      le_trans hSZbound (le_of_eq hexpZ)
    have hSMb : (∑ z ∈ R, ∫ v in (-L')..L',
          ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2) ^ ((2 : ℝ) / 3)
        ≤ (2 * L' + 1) ^ ((2 : ℝ) / 3) * (CM * (T + L' + (K : ℝ))) ^ ((2 : ℝ) / 3) *
            (Real.log ((K : ℝ) + 2)) ^ ((4 : ℝ) / 3) :=
      le_trans hSMbound (le_of_eq hexpM)
    have hA1nn : (0 : ℝ) ≤ (2 * L' + 1) ^ ((1 : ℝ) / 3) * (2 * C4 * (T + L')) ^ ((1 : ℝ) / 3) *
        (Real.log (T + L')) ^ ((4 : ℝ) / 3) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg h2L1nn _)
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * C4 * (T + L')) _))
        (Real.rpow_nonneg hlogTL'nn _)
    have hSM2nn : 0 ≤ (∑ z ∈ R, ∫ v in (-L')..L',
        ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2) ^ ((2 : ℝ) / 3) :=
      Real.rpow_nonneg hSumMnn _
    have hprod : (∑ z ∈ R, ∫ v in (-L')..L',
          ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 3) *
        (∑ z ∈ R, ∫ v in (-L')..L',
          ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2) ^ ((2 : ℝ) / 3)
        ≤ ((2 * L' + 1) ^ ((1 : ℝ) / 3) * (2 * C4 * (T + L')) ^ ((1 : ℝ) / 3) *
            (Real.log (T + L')) ^ ((4 : ℝ) / 3)) *
          ((2 * L' + 1) ^ ((2 : ℝ) / 3) * (CM * (T + L' + (K : ℝ))) ^ ((2 : ℝ) / 3) *
            (Real.log ((K : ℝ) + 2)) ^ ((4 : ℝ) / 3)) :=
      mul_le_mul hSZb hSMb hSM2nn hA1nn
    have hconst : (12 : ℝ) ^ ((4 : ℝ) / 3) * (Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3)
        = (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12) (by positivity : (0 : ℝ) ≤ Cg / (σ - 1 / 2))]
      ring_nf
    have hpow2 : (2 * L' + 1) ^ ((1 : ℝ) / 3) * (2 * L' + 1) ^ ((2 : ℝ) / 3) = (2 * L' + 1) := by
      rw [← Real.rpow_add (by positivity),
        show ((1 : ℝ) / 3 + 2 / 3) = 1 by norm_num, Real.rpow_one]
    have hAprod : ((2 * L' + 1) ^ ((1 : ℝ) / 3) * (2 * C4 * (T + L')) ^ ((1 : ℝ) / 3) *
            (Real.log (T + L')) ^ ((4 : ℝ) / 3)) *
          ((2 * L' + 1) ^ ((2 : ℝ) / 3) * (CM * (T + L' + (K : ℝ))) ^ ((2 : ℝ) / 3) *
            (Real.log ((K : ℝ) + 2)) ^ ((4 : ℝ) / 3))
        = ((2 * L' + 1) ^ ((1 : ℝ) / 3) * (2 * L' + 1) ^ ((2 : ℝ) / 3)) *
            (2 * C4 * (T + L')) ^ ((1 : ℝ) / 3) * (Real.log (T + L')) ^ ((4 : ℝ) / 3) *
            (CM * (T + L' + (K : ℝ))) ^ ((2 : ℝ) / 3) * (Real.log ((K : ℝ) + 2)) ^ ((4 : ℝ) / 3) := by
      ring
    have hCore : (R.card : ℝ) ≤
        (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3) * (2 * L' + 1) *
          (2 * C4 * (T + L')) ^ ((1 : ℝ) / 3) * (Real.log (T + L')) ^ ((4 : ℝ) / 3) *
          (CM * (T + L' + (K : ℝ))) ^ ((2 : ℝ) / 3) * (Real.log ((K : ℝ) + 2)) ^ ((4 : ℝ) / 3) *
          Y ^ ((2 - 4 * σ) / 3) := by
      calc (R.card : ℝ)
          ≤ (12 : ℝ) ^ ((4 : ℝ) / 3) *
              ((Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3) *
                Y ^ ((2 - 4 * σ) / 3) *
                ((∑ z ∈ R, ∫ v in (-L')..L',
                    ‖riemannZeta ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 3) *
                  (∑ z ∈ R, ∫ v in (-L')..L',
                    ‖MK K ((1 / 2 : ℂ) + ((z.im + v : ℝ) : ℂ) * Complex.I)‖ ^ 2) ^ ((2 : ℝ) / 3))) := hstep1
        _ ≤ (12 : ℝ) ^ ((4 : ℝ) / 3) *
              ((Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3) *
                Y ^ ((2 - 4 * σ) / 3) *
                (((2 * L' + 1) ^ ((1 : ℝ) / 3) * (2 * C4 * (T + L')) ^ ((1 : ℝ) / 3) *
                    (Real.log (T + L')) ^ ((4 : ℝ) / 3)) *
                  ((2 * L' + 1) ^ ((2 : ℝ) / 3) * (CM * (T + L' + (K : ℝ))) ^ ((2 : ℝ) / 3) *
                    (Real.log ((K : ℝ) + 2)) ^ ((4 : ℝ) / 3)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (by positivity)) (by positivity)
        _ = (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3) * (2 * L' + 1) *
              (2 * C4 * (T + L')) ^ ((1 : ℝ) / 3) * (Real.log (T + L')) ^ ((4 : ℝ) / 3) *
              (CM * (T + L' + (K : ℝ))) ^ ((2 : ℝ) / 3) * (Real.log ((K : ℝ) + 2)) ^ ((4 : ℝ) / 3) *
              Y ^ ((2 - 4 * σ) / 3) := by
              rw [hAprod, hpow2, ← hconst]
              ring
    have har' := har σ T (K : ℝ) L' hσgt hT hK1 hKle hL'def hδlt'
    have hYrpow : 0 ≤ Y ^ ((2 - 4 * σ) / 3) := Real.rpow_nonneg hYnn _
    calc (R.card : ℝ)
        ≤ (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L') ^ ((1 : ℝ) / 3) * (2 * L' + 1) *
            (2 * C4 * (T + L')) ^ ((1 : ℝ) / 3) * (Real.log (T + L')) ^ ((4 : ℝ) / 3) *
            (CM * (T + L' + (K : ℝ))) ^ ((2 : ℝ) / 3) * (Real.log ((K : ℝ) + 2)) ^ ((4 : ℝ) / 3) *
            Y ^ ((2 - 4 * σ) / 3) := hCore
      _ ≤ (Car * T ^ ε * (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3))) *
            Y ^ ((2 - 4 * σ) / 3) := mul_le_mul_of_nonneg_right har' hYrpow
      _ ≤ max Car (max Clo 1) * T ^ ε *
            (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) := by
          have h1 : Car ≤ max Car (max Clo 1) := le_max_left _ _
          have h2 : (0 : ℝ) ≤ T ^ ε := Real.rpow_nonneg hTnn _
          have h3 : (0 : ℝ) ≤ T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) *
              Y ^ ((2 - 4 * σ) / 3) :=
            mul_nonneg (mul_nonneg (Real.rpow_nonneg hTnn _)
              (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ T + (K : ℝ)) _))
              (Real.rpow_nonneg hYnn _)
          calc (Car * T ^ ε * (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3))) *
                Y ^ ((2 - 4 * σ) / 3)
              = Car * T ^ ε * (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) *
                  Y ^ ((2 - 4 * σ) / 3)) := by ring
            _ ≤ max Car (max Clo 1) * T ^ ε *
                  (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) h3
  · -- ### the two exceptional cases: the trivial count `#R ≤ 2T+1` suffices
    have hcard := card_le_two_mul_add_one R hTnn (fun z hzm => (hz z hzm).2.2.2) hsep
    have hTeps1 : (1 : ℝ) ≤ T ^ ε := Real.one_le_rpow (by linarith) hε.le
    have hXnn : 0 ≤ T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hTnn _)
        (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ T + (K : ℝ)) _))
        (Real.rpow_nonneg hYnn _)
    rcases not_and_or.mp hmain with hσle | hKgt
    · -- `σ - 1/2 ≤ 1/(2 log (A T))`
      have hσle' : σ ≤ 1 / 2 + 1 / (2 * Real.log (A * T)) := by linarith
      have hlo' := hlo A T (K : ℝ) σ Y hA hT hK1 hY hY2 hσle'
      have hCmax : Clo ≤ max Car (max Clo 1) := le_trans (le_max_left _ _) (le_max_right _ _)
      calc (R.card : ℝ)
          ≤ 2 * T + 1 := hcard
        _ ≤ Clo * (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) *
              Y ^ ((2 - 4 * σ) / 3)) := hlo'
        _ ≤ max Car (max Clo 1) * T ^ ε *
              (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) := by
            have h1 : Clo * (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) *
                  Y ^ ((2 - 4 * σ) / 3)) ≤ max Car (max Clo 1) *
                  (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) :=
              mul_le_mul_of_nonneg_right hCmax hXnn
            have h2 : max Car (max Clo 1) *
                  (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) ≤
                max Car (max Clo 1) * T ^ ε *
                  (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) := by
              have h3 : T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) ≤
                  T ^ ε * (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) *
                    Y ^ ((2 - 4 * σ) / 3)) := le_mul_of_one_le_left hXnn hTeps1
              calc max Car (max Clo 1) *
                    (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3))
                  ≤ max Car (max Clo 1) *
                    (T ^ ε * (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) *
                      Y ^ ((2 - 4 * σ) / 3))) :=
                    mul_le_mul_of_nonneg_left h3 (by positivity)
                _ = max Car (max Clo 1) * T ^ ε *
                    (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) := by
                    ring
            linarith [h1, h2]
    · -- `K > 6 Ã² T³ ≥ C_K A² T³`
      have hKgt6 : 6 * Ã ^ 2 * T ^ 3 < (K : ℝ) := not_le.mp hKgt
      have hKgt' : CK * A ^ 2 * T ^ 3 < (K : ℝ) := lt_of_le_of_lt hKres hKgt6
      have hmiddle : (2 * T + 1 : ℝ) ≤ T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) *
          Y ^ ((2 - 4 * σ) / 3) * T ^ ε := by
        by_contra hcon
        simp only [not_le] at hcon
        have hb := hKb A ε T (K : ℝ) σ Y hA hε hT hK1 hY hY2 hσ1 hσ2 hcon
        exact absurd hb (not_le.mpr hKgt')
      have hmax1 : (1 : ℝ) ≤ max Car (max Clo 1) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      calc (R.card : ℝ)
          ≤ 2 * T + 1 := hcard
        _ ≤ T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) * T ^ ε :=
            hmiddle
        _ ≤ max Car (max Clo 1) * T ^ ε *
              (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) := by
            have hXnnt : 0 ≤ T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) *
                Y ^ ((2 - 4 * σ) / 3) * T ^ ε :=
              mul_nonneg hXnn (Real.rpow_nonneg hTnn _)
            calc T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) * T ^ ε
                ≤ max Car (max Clo 1) *
                  (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) *
                    T ^ ε) := le_mul_of_one_le_left hXnnt hmax1
              _ = max Car (max Clo 1) * T ^ ε *
                  (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) := by
                  ring

end Work.ZeroDensity.Ingham.zetaDetectorBig
