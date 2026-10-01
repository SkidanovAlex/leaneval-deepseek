import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.ZeroDensity.LogFree.RouteDefs
import Submission.Work.ZeroDensity.LogFree.boxUpgradeOfParams
import Submission.Work.ZeroDensity.Basic
import Submission.Work.ZeroDensity.LogFree.GramProps
import Submission.Work.ZeroDensity.LogFree.halaszDualityOfProps
import Submission.Work.HB7CF2.ZeroDensity.LogFree.massBound
import Submission.Work.HB7CF.PoleResidue
import Submission.Work.ZeroDensity.LogFree.detectorGen
import Submission.Work.ZeroDensity.LogFree.gramCross
import Submission.Work.ZeroDensity.LogFree.gramSame
import Submission.Work.ZeroDensity.LogFree.poleLargeSieve
import Submission.Work.ZeroDensity.LogFree.detectorTruncation
import Submission.Work.ZeroDensity.LogFree.nearLineCount

/-!
# L7 — the assembly of the unified log-free non-principal zero-density estimate

`logFreeNPOfParams`: for every parameter packet `p : Params` there is `C > 0` with

  `Σ'_{χ ≠ 1} N(σ,T,χ) ≤ C (qT)^{2x(1-σ)}`   for all `q ≥ 2`, `σ ∈ [p.σ₀,1]`, `T ≥ 1`.

The two deep inputs are the interfaces `DualityCount` (**L5**, the Halász duality count) and
`BoxUpgrade` (**L6**, the box/parity upgrade), both stated in `RouteDefs.lean`.  The assembly
itself — the two-scale reduction `q(T+2)` vs `qT`, the absorption of the polynomial-in-`λ` losses
into the exponent, and the small-`D` case — is done here.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.LinnikContract

/-! ## 1. Elementary facts about `scale`, `Lscale` and `Dpow` -/

lemma scale_pos {q : ℕ} (hq : 2 ≤ q) {T : ℝ} (hT : 1 ≤ T) : 0 < scale q T := by
  rw [scale]
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  nlinarith

lemma scale_one_le {q : ℕ} (hq : 2 ≤ q) {T : ℝ} (hT : 1 ≤ T) : 1 ≤ scale q T := by
  rw [scale]
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  nlinarith

lemma Lscale_nonneg {q : ℕ} (hq : 2 ≤ q) {T : ℝ} (hT : 1 ≤ T) : 0 ≤ Lscale q T := by
  rw [Lscale]
  exact Real.log_nonneg (scale_one_le hq hT)

lemma Lscale_pos {q : ℕ} (hq : 2 ≤ q) {T : ℝ} (hT : 1 ≤ T) : 0 < Lscale q T := by
  rw [Lscale]
  apply Real.log_pos
  rw [scale]
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  nlinarith

lemma Dpow_nonneg {q : ℕ} (hq : 2 ≤ q) {T a : ℝ} (hT : 1 ≤ T) : 0 ≤ Dpow q T a :=
  Real.rpow_nonneg (le_of_lt (scale_pos hq hT)) a

lemma one_le_Dpow {q : ℕ} (hq : 2 ≤ q) {T a : ℝ} (hT : 1 ≤ T) (ha : 0 ≤ a) :
    1 ≤ Dpow q T a :=
  Real.one_le_rpow (scale_one_le hq hT) ha

/-! ## 2. Exponential domination of the polynomial-in-`λ` loss -/

/-- `(1+λ)(2 + log₂(1+λ)) ≤ C e^{θλ}` for `λ ≥ 0` and every fixed `θ > 0`. -/
theorem polyLog2LeExp (θ : ℝ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 ≤ lam →
      (1 + lam) * (2 + log2 (1 + lam)) ≤ C * Real.exp (θ * lam) := by
  refine ⟨max 8 (16 / θ ^ 2), lt_max_of_lt_left (by norm_num), ?_⟩
  intro lam hlam
  have hlog2le : log2 (1 + lam) ≤ 2 * lam := by
    rw [log2, div_le_iff₀ (Real.log_pos (by norm_num))]
    have h1 : Real.log (1 + lam) ≤ lam := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + lam by linarith)
      linarith
    have h2 : (1 : ℝ) ≤ 2 * Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    nlinarith
  have hstep : (1 + lam) * (2 + log2 (1 + lam)) ≤ 2 * (1 + lam) ^ 2 := by
    have h1 : 0 ≤ 1 + lam := by linarith
    have h2 : 2 + log2 (1 + lam) ≤ 2 * (1 + lam) := by linarith
    nlinarith [h1, h2]
  have hmax8 : (8 : ℝ) ≤ max 8 (16 / θ ^ 2) := le_max_left _ _
  have hmax16 : 16 / θ ^ 2 ≤ max 8 (16 / θ ^ 2) := le_max_right _ _
  by_cases h : lam ≤ 1
  · have hle : 2 * (1 + lam) ^ 2 ≤ 8 := by nlinarith
    have hexp1 : (1 : ℝ) ≤ Real.exp (θ * lam) := Real.one_le_exp (by positivity)
    have hfin : (8 : ℝ) ≤ max 8 (16 / θ ^ 2) * Real.exp (θ * lam) := by
      have hh := mul_le_mul hmax8 hexp1 (by norm_num)
        (le_trans (by norm_num : (0 : ℝ) ≤ 8) hmax8)
      simpa using hh
    linarith [hstep, hle, hfin]
  · have h1lam : 1 + lam ≤ 2 * lam := by linarith
    have hExp : (θ * lam) ^ 2 / 2 ≤ Real.exp (θ * lam) := by
      have := Real.pow_div_factorial_le_exp (θ * lam) (by positivity) 2
      simpa using this
    have h1' : θ ^ 2 * lam ^ 2 / 2 ≤ Real.exp (θ * lam) := by
      rw [show θ ^ 2 * lam ^ 2 / 2 = (θ * lam) ^ 2 / 2 by ring]
      exact hExp
    have h2'' : 8 * lam ^ 2 ≤ (16 / θ ^ 2) * Real.exp (θ * lam) := by
      have hh := mul_le_mul_of_nonneg_left h1' (show (0 : ℝ) ≤ 16 / θ ^ 2 by positivity)
      have heq : (16 / θ ^ 2) * (θ ^ 2 * lam ^ 2 / 2) = 8 * lam ^ 2 := by field_simp; ring
      linarith [heq ▸ hh]
    have hf1 : 2 * (1 + lam) ^ 2 ≤ 8 * lam ^ 2 := by nlinarith
    have hfin : 2 * (1 + lam) ^ 2 ≤ max 8 (16 / θ ^ 2) * Real.exp (θ * lam) := by
      calc 2 * (1 + lam) ^ 2 ≤ 8 * lam ^ 2 := hf1
        _ ≤ (16 / θ ^ 2) * Real.exp (θ * lam) := h2''
        _ ≤ max 8 (16 / θ ^ 2) * Real.exp (θ * lam) :=
            mul_le_mul_of_nonneg_right hmax16 (Real.exp_nonneg _)
    linarith [hstep, hfin]

/-! ## 3. Shrinking the exponent `x` while keeping `σ₀` -/

/-- Given `p : Params` there is `p' : Params` with the same `σ₀` and a strictly smaller `x`:
take `w' = w/2`, `u' = u`, `v' = v` and `x' = (1/2 + v + w/2 + 2η)/σ₀ < x` (by `P1`).
This is what lets the exponent `2x` of the target absorb the polynomial-in-`λ` losses. -/
theorem paramsShrink (p : Params) :
    ∃ p' : Params, p'.σ₀ = p.σ₀ ∧ p'.x < p.x := by
  have hσ₀pos : 0 < p.σ₀ := by linarith [p.hσ₀]
  have hv0 : 0 < p.v := by linarith [p.hw, p.hwu, p.huv]
  refine ⟨{ σ₀ := p.σ₀, η := p.η, w := p.w / 2, u := p.u, v := p.v,
            x := (1 / 2 + p.v + p.w / 2 + 2 * p.η) / p.σ₀,
            hσ₀ := p.hσ₀, hσ₀1 := p.hσ₀1, hη := p.hη,
            hw := by linarith [p.hw],
            hwu := by linarith [p.hw, p.hwu],
            huv := p.huv,
            hvx := ?_, P1 := ?_, P2 := ?_ }, ?_, ?_⟩
  · rw [lt_div_iff₀ hσ₀pos]
    nlinarith [mul_le_mul_of_nonneg_left p.hσ₀1 (le_of_lt hv0), p.hw, p.hη]
  · rw [div_mul_cancel₀ _ (ne_of_gt hσ₀pos)]
  · have := p.P2
    linarith [p.hw]
  · rfl
  · rw [div_lt_iff₀ hσ₀pos]
    nlinarith [p.P1, p.hw]

/-! ## 4. The absorption lemma -/

/-- **Absorption of the polynomial-in-`λ` loss.**  For `σ ∈ [0,1]`, `x ≥ 0`, `θ ∈ (0,1]` with
`2x + θ ≤ c` and `(1+λ)(2+log₂(1+λ)) ≤ C_θ e^{θλ}` for all `λ ≥ 0`, the box-upgrade output
`C₀((1+λ)(M+1)+1)` with `M = C_S(2+log₂(1+λ))D^{2x(1-σ)}` is at most
`C₀(C_S+2)C_θ·3^{2x+1}(qT)^{c(1-σ)}`, using `D = q(T+2) ≤ 3qT` (`T ≥ 1`). -/
theorem absorb_ineq {q : ℕ} (hq : 2 ≤ q) {T σ x c C₀ C_S Cθ θ : ℝ} (hT : 1 ≤ T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC₀ : 0 ≤ C₀) (hC_S : 0 ≤ C_S) (hCθ : 0 < Cθ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hxc : 2 * x + θ ≤ c) (hx0 : 0 ≤ x)
    (hpoly : ∀ lam : ℝ, 0 ≤ lam →
      (1 + lam) * (2 + log2 (1 + lam)) ≤ Cθ * Real.exp (θ * lam)) :
    C₀ * ((1 + (1 - σ) * Lscale q T)
            * (C_S * (2 + log2 (1 + (1 - σ) * Lscale q T))
                * Dpow q T (2 * x * (1 - σ)) + 1) + 1)
      ≤ C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ)) := by
  have hqT1 : (1 : ℝ) ≤ (q : ℝ) * T := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hqTpos : (0 : ℝ) < (q : ℝ) * T := by linarith
  have hscale1 : (1 : ℝ) ≤ scale q T := scale_one_le hq hT
  have hscalepos : (0 : ℝ) < scale q T := scale_pos hq hT
  have hL0 : 0 ≤ Lscale q T := Lscale_nonneg hq hT
  have hs0 : 0 ≤ 1 - σ := by linarith
  have hs1 : 1 - σ ≤ 1 := by linarith
  have hlam0 : 0 ≤ (1 - σ) * Lscale q T := mul_nonneg hs0 hL0
  have hlog20 : 0 ≤ log2 (1 + (1 - σ) * Lscale q T) :=
    div_nonneg (Real.log_nonneg (by linarith)) (le_of_lt (Real.log_pos (by norm_num)))
  have hDp1 : (1 : ℝ) ≤ Dpow q T (2 * x * (1 - σ)) :=
    Real.one_le_rpow hscale1 (by positivity)
  have hDp0 : (0 : ℝ) ≤ Dpow q T (2 * x * (1 - σ)) := by linarith
  have hCS2 : (0 : ℝ) ≤ C_S + 2 := by linarith
  have hprod : (2 : ℝ) ≤ (2 + log2 (1 + (1 - σ) * Lscale q T)) * Dpow q T (2 * x * (1 - σ)) := by
    simpa using mul_le_mul (by linarith : (2 : ℝ) ≤ 2 + log2 (1 + (1 - σ) * Lscale q T)) hDp1
      (by norm_num) (by linarith)
  have hstep1 : (1 + (1 - σ) * Lscale q T)
        * (C_S * (2 + log2 (1 + (1 - σ) * Lscale q T)) * Dpow q T (2 * x * (1 - σ)) + 1) + 1
      ≤ (C_S + 2) * (1 + (1 - σ) * Lscale q T)
          * (2 + log2 (1 + (1 - σ) * Lscale q T)) * Dpow q T (2 * x * (1 - σ)) := by
    have hlam1 : (1 : ℝ) ≤ 1 + (1 - σ) * Lscale q T := by linarith
    have h4 : 4 * (1 + (1 - σ) * Lscale q T)
        ≤ 2 * (1 + (1 - σ) * Lscale q T)
            * ((2 + log2 (1 + (1 - σ) * Lscale q T)) * Dpow q T (2 * x * (1 - σ))) := by
      have h := mul_le_mul_of_nonneg_left hprod
        (show (0 : ℝ) ≤ 2 * (1 + (1 - σ) * Lscale q T) by linarith)
      linarith [h]
    nlinarith [h4, hlam1, hC_S]
  have hpoly' := hpoly ((1 - σ) * Lscale q T) hlam0
  have hstep2 : (C_S + 2) * (1 + (1 - σ) * Lscale q T)
        * (2 + log2 (1 + (1 - σ) * Lscale q T)) * Dpow q T (2 * x * (1 - σ))
      ≤ (C_S + 2) * Cθ * Real.exp (θ * ((1 - σ) * Lscale q T))
          * Dpow q T (2 * x * (1 - σ)) := by
    have h1 := mul_le_mul_of_nonneg_left hpoly' hCS2
    have h2 := mul_le_mul_of_nonneg_right h1 hDp0
    nlinarith [h2]
  have hexp_eq : Real.exp (θ * ((1 - σ) * Lscale q T)) = Dpow q T (θ * (1 - σ)) := by
    rw [Dpow, Lscale, Real.rpow_def_of_pos hscalepos]
    congr 1
    ring
  have hDpow_add : Dpow q T (θ * (1 - σ)) * Dpow q T (2 * x * (1 - σ))
      = Dpow q T ((θ + 2 * x) * (1 - σ)) := by
    rw [Dpow, Dpow, ← Real.rpow_add hscalepos]
    congr 1
    ring
  have hr0 : 0 ≤ (θ + 2 * x) * (1 - σ) := by positivity
  have hr1 : (θ + 2 * x) * (1 - σ) ≤ 2 * x + 1 := by
    have h1 : θ * (1 - σ) ≤ 1 := by
      calc θ * (1 - σ) ≤ θ * 1 := mul_le_mul_of_nonneg_left hs1 hθ.le
        _ = θ := by ring
        _ ≤ 1 := hθ1
    have h2 : 2 * x * (1 - σ) ≤ 2 * x := by
      calc 2 * x * (1 - σ) ≤ 2 * x * 1 := mul_le_mul_of_nonneg_left hs1 (by linarith)
        _ = 2 * x := by ring
    have hrw : (θ + 2 * x) * (1 - σ) = θ * (1 - σ) + 2 * x * (1 - σ) := by ring
    rw [hrw]; linarith
  have hr2 : (θ + 2 * x) * (1 - σ) ≤ c * (1 - σ) := by
    have h : θ + 2 * x ≤ c := by linarith
    exact mul_le_mul_of_nonneg_right h hs0
  have hstep3 : (C_S + 2) * Cθ * Real.exp (θ * ((1 - σ) * Lscale q T))
        * Dpow q T (2 * x * (1 - σ))
      ≤ (C_S + 2) * Cθ * ((3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ))) := by
    have hCSC : (0 : ℝ) ≤ (C_S + 2) * Cθ := by positivity
    have hDle : scale q T ≤ 3 * ((q : ℝ) * T) := by rw [scale]; nlinarith
    have hb1 : Dpow q T ((θ + 2 * x) * (1 - σ))
        ≤ (3 * ((q : ℝ) * T)) ^ ((θ + 2 * x) * (1 - σ)) :=
      Real.rpow_le_rpow (le_of_lt hscalepos) hDle hr0
    have hb2 : (3 * ((q : ℝ) * T)) ^ ((θ + 2 * x) * (1 - σ))
        = (3 : ℝ) ^ ((θ + 2 * x) * (1 - σ)) * ((q : ℝ) * T) ^ ((θ + 2 * x) * (1 - σ)) :=
      Real.mul_rpow (by norm_num) (le_of_lt hqTpos)
    have hb3 : (3 : ℝ) ^ ((θ + 2 * x) * (1 - σ)) ≤ (3 : ℝ) ^ (2 * x + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hr1
    have hb4 : ((q : ℝ) * T) ^ ((θ + 2 * x) * (1 - σ)) ≤ ((q : ℝ) * T) ^ (c * (1 - σ)) :=
      Real.rpow_le_rpow_of_exponent_le hqT1 hr2
    have hmain : Dpow q T (θ * (1 - σ)) * Dpow q T (2 * x * (1 - σ))
        ≤ (3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ)) := by
      rw [hDpow_add]
      calc Dpow q T ((θ + 2 * x) * (1 - σ)) ≤ (3 * ((q : ℝ) * T)) ^ ((θ + 2 * x) * (1 - σ)) :=
            hb1
        _ = (3 : ℝ) ^ ((θ + 2 * x) * (1 - σ)) * ((q : ℝ) * T) ^ ((θ + 2 * x) * (1 - σ)) := hb2
        _ ≤ (3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ)) :=
            mul_le_mul hb3 hb4 (Real.rpow_nonneg (le_of_lt hqTpos) _)
              (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    calc (C_S + 2) * Cθ * Real.exp (θ * ((1 - σ) * Lscale q T))
          * Dpow q T (2 * x * (1 - σ))
        = (C_S + 2) * Cθ * (Real.exp (θ * ((1 - σ) * Lscale q T))
            * Dpow q T (2 * x * (1 - σ))) := by ring
      _ ≤ (C_S + 2) * Cθ * ((3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ))) :=
          mul_le_mul_of_nonneg_left (by rw [hexp_eq]; exact hmain) hCSC
  calc C₀ * ((1 + (1 - σ) * Lscale q T)
          * (C_S * (2 + log2 (1 + (1 - σ) * Lscale q T))
              * Dpow q T (2 * x * (1 - σ)) + 1) + 1)
      ≤ C₀ * ((C_S + 2) * (1 + (1 - σ) * Lscale q T)
          * (2 + log2 (1 + (1 - σ) * Lscale q T)) * Dpow q T (2 * x * (1 - σ))) :=
        mul_le_mul_of_nonneg_left hstep1 hC₀
    _ ≤ C₀ * ((C_S + 2) * Cθ * Real.exp (θ * ((1 - σ) * Lscale q T))
          * Dpow q T (2 * x * (1 - σ))) := mul_le_mul_of_nonneg_left hstep2 hC₀
    _ ≤ C₀ * ((C_S + 2) * Cθ * ((3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ)))) :=
        mul_le_mul_of_nonneg_left hstep3 hC₀
    _ = C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ)) := by ring

/-! ## 5. The two-route assembly -/

/-- **The assembly, at an exponent `c > 2x`.**  From the two interfaces `DualityCount` (L5) and
`BoxUpgrade` (L6) one gets the log-free estimate with exponent `c`. -/
theorem logFreeNP_of_route (p : Params) (c : ℝ) (hc : 2 * p.x < c)
    (h5 : DualityCount p) (h6 : BoxUpgrade p) : logFreeNP p.σ₀ c := by
  obtain ⟨C₀, hC₀pos, c₀, hc₀pos, D₀B, hD₀Bpos, hbox⟩ := h6
  obtain ⟨C_S, hC_Spos, D₀S, hD₀Spos, hdu⟩ := h5 c₀ hc₀pos
  have hθpos : 0 < min ((c - 2 * p.x) / 2) 1 := lt_min (by linarith) one_pos
  obtain ⟨Cθ, hCθpos, hpoly⟩ := polyLog2LeExp (min ((c - 2 * p.x) / 2) 1) hθpos
  obtain ⟨Ctr, hCtrpos, htriv⟩ := trivial_bound 1 (by norm_num)
  set D₀ : ℝ := max (max D₀B D₀S) 1 with hD₀def
  have hD₀1 : (1 : ℝ) ≤ D₀ := le_max_right _ _
  have hD₀GB : D₀B ≤ D₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hD₀GS : D₀S ≤ D₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hx0 : 0 ≤ p.x := by linarith [p.hw, p.hwu, p.huv, p.hvx]
  have hcpos : 0 < c := by linarith [p.hw, p.hwu, p.huv, p.hvx]
  refine ⟨max (C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * p.x + 1)) (Ctr * (D₀ * D₀)),
          lt_max_of_lt_left (by positivity), ?_⟩
  intro q hq _inst σ T hσ0 hσ1 hT
  have hC2nn : 0 ≤ Ctr * (D₀ * D₀) := by positivity
  have hqTpos : 0 < (q : ℝ) * T := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hqT1 : 1 ≤ (q : ℝ) * T := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hσ0nn : 0 ≤ σ := by linarith [p.hσ₀, hσ0]
  have hs0 : 0 ≤ 1 - σ := by linarith
  have hexpnn : 0 ≤ c * (1 - σ) := mul_nonneg (le_of_lt hcpos) hs0
  have hrpow1 : 1 ≤ ((q : ℝ) * T) ^ (c * (1 - σ)) := Real.one_le_rpow hqT1 hexpnn
  have hL0 : 0 ≤ Lscale q T := Lscale_nonneg hq hT
  by_cases hDge : D₀ ≤ scale q T
  · -- large `D`: L5 + L6 + absorption
    set M : ℝ := C_S * (2 + log2 (1 + (1 - σ) * Lscale q T))
      * Dpow q T (2 * p.x * (1 - σ)) with hMdef
    have hMnn : 0 ≤ M := by
      rw [hMdef]
      have h1 : 1 ≤ 1 + (1 - σ) * Lscale q T := by linarith [mul_nonneg hs0 hL0]
      have h2 : 0 ≤ 2 + log2 (1 + (1 - σ) * Lscale q T) := by
        have h3 : 0 ≤ log2 (1 + (1 - σ) * Lscale q T) :=
          div_nonneg (Real.log_nonneg h1) (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
        linarith
      exact mul_nonneg (mul_nonneg (le_of_lt hC_Spos) h2)
        (Dpow_nonneg (q := q) hq hT)
    have hsys : ∀ (m : ℕ) (χ : Fin m → DirichletCharacter ℂ q) (ρ : Fin m → ℂ),
        (∀ i, χ i ≠ 1) → (∀ i, zeroMult (χ i) (ρ i) ≠ 0) →
        (∀ i, σ ≤ (ρ i).re) → (∀ i, (ρ i).re < 1) → (∀ i, |(ρ i).im| ≤ T) →
        (∀ i, c₀ ≤ (1 - (ρ i).re) * Lscale q T) →
        (∀ i j, i ≠ j → χ i = χ j → 1 / Lscale q T ≤ |(ρ i).im - (ρ j).im|) →
        (m : ℝ) ≤ M := by
      intro m χ ρ h1 h2 h3 h4 h5' h6'
      rw [hMdef]
      exact hdu q hq T σ hT (le_trans hD₀GS hDge) hσ0 hσ1 m χ ρ h1 h2 h3 h4 h5' h6'
    have hb := hbox q hq T σ hT (le_trans hD₀GB hDge) hσ0 hσ1 M hMnn hsys
    have hθ1 : min ((c - 2 * p.x) / 2) 1 ≤ 1 := min_le_right _ _
    have hxc : 2 * p.x + min ((c - 2 * p.x) / 2) 1 ≤ c := by
      have := min_le_left ((c - 2 * p.x) / 2) 1
      linarith
    have habs : C₀ * ((1 + (1 - σ) * Lscale q T) * (M + 1) + 1)
        ≤ C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * p.x + 1)
            * ((q : ℝ) * T) ^ (c * (1 - σ)) := by
      rw [hMdef]
      exact absorb_ineq hq hT hσ0nn hσ1 (le_of_lt hC₀pos) (le_of_lt hC_Spos) hCθpos
        hθpos hθ1 hxc hx0 hpoly
    calc famCountNP q σ T
        ≤ C₀ * ((1 + (1 - σ) * Lscale q T) * (M + 1) + 1) := hb
      _ ≤ C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * p.x + 1)
            * ((q : ℝ) * T) ^ (c * (1 - σ)) := habs
      _ ≤ max (C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * p.x + 1)) (Ctr * (D₀ * D₀))
            * ((q : ℝ) * T) ^ (c * (1 - σ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg (le_of_lt hqTpos) _)
  · -- small `D`: the σ-blind count
    have hDlt : scale q T < D₀ := not_le.mp hDge
    have hqTle : (q : ℝ) * T ≤ D₀ := by
      have h1 : (q : ℝ) * T ≤ scale q T := by rw [scale]; nlinarith [hqTpos]
      linarith
    have hb1 : famCountNP q σ T ≤ Ctr * ((q : ℝ) * T) ^ ((1 : ℝ) + 1) :=
      le_trans (famCountNP_le_famCount q σ T) (htriv q hq σ T hσ0nn hσ1 hT)
    have hxx : ((q : ℝ) * T) ^ ((1 : ℝ) + 1) = ((q : ℝ) * T) * ((q : ℝ) * T) := by
      rw [show ((1 : ℝ) + 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    have hsq : ((q : ℝ) * T) * ((q : ℝ) * T) ≤ D₀ * D₀ :=
      mul_self_le_mul_self (le_of_lt hqTpos) hqTle
    calc famCountNP q σ T ≤ Ctr * ((q : ℝ) * T) ^ ((1 : ℝ) + 1) := hb1
      _ = Ctr * (((q : ℝ) * T) * ((q : ℝ) * T)) := by rw [hxx]
      _ ≤ Ctr * (D₀ * D₀) := mul_le_mul_of_nonneg_left hsq (le_of_lt hCtrpos)
      _ ≤ Ctr * (D₀ * D₀) * ((q : ℝ) * T) ^ (c * (1 - σ)) := by
          nlinarith [hC2nn, hrpow1]
      _ ≤ max (C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * p.x + 1)) (Ctr * (D₀ * D₀))
            * ((q : ℝ) * T) ^ (c * (1 - σ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.rpow_nonneg (le_of_lt hqTpos) _)


/-! ## 5b. The relaxed ("slack") route: absorbing a polynomial-in-`λ` loss -/

/-- `(1+λ)^k ≤ C e^{θλ}` for `λ ≥ 0` (any fixed `k`, any `θ > 0`). -/
theorem polyOneAddLeExp (k : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 ≤ lam → (1 + lam) ^ k ≤ C * Real.exp (θ * lam) := by
  refine ⟨max (2 ^ k) (2 ^ k * (k.factorial : ℝ) * (θ ^ k)⁻¹) + 1, by positivity, ?_⟩
  intro lam hlam
  set M : ℝ := max (2 ^ k) (2 ^ k * (k.factorial : ℝ) * (θ ^ k)⁻¹) with hMdef
  have hmax1 : (2 : ℝ) ^ k ≤ M + 1 := by
    have h := le_max_left ((2 : ℝ) ^ k) (2 ^ k * (k.factorial : ℝ) * (θ ^ k)⁻¹)
    rw [hMdef]; linarith
  have hmax2 : (2 : ℝ) ^ k * (k.factorial : ℝ) * (θ ^ k)⁻¹ ≤ M + 1 := by
    have h := le_max_right ((2 : ℝ) ^ k) (2 ^ k * (k.factorial : ℝ) * (θ ^ k)⁻¹)
    rw [hMdef]; linarith
  have hMpos : (0 : ℝ) < M + 1 := by positivity
  have hθk : 0 < θ ^ k := by positivity
  have hkfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  by_cases h : lam ≤ 1
  · have h1 : 1 + lam ≤ 2 := by linarith
    have h2 : (1 + lam) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) h1 k
    have h3 : (1 : ℝ) ≤ Real.exp (θ * lam) := Real.one_le_exp (by positivity)
    have h4 : (2 : ℝ) ^ k ≤ (M + 1) * Real.exp (θ * lam) := by
      have h5 : (M + 1) * 1 ≤ (M + 1) * Real.exp (θ * lam) :=
        mul_le_mul_of_nonneg_left h3 hMpos.le
      linarith [hmax1, h5]
    linarith
  · have h1 : 1 + lam ≤ 2 * lam := by linarith
    have h2 : (1 + lam) ^ k ≤ (2 * lam) ^ k := pow_le_pow_left₀ (by linarith) h1 k
    have h3 : (2 * lam) ^ k = 2 ^ k * lam ^ k := by rw [mul_pow]
    have hExp := Real.pow_div_factorial_le_exp (θ * lam) (by positivity) k
    rw [mul_pow, div_le_iff₀ hkfac] at hExp
    have hExp' : θ ^ k * lam ^ k ≤ (k.factorial : ℝ) * Real.exp (θ * lam) := by
      linarith [hExp]
    have h5 : lam ^ k ≤ (k.factorial : ℝ) * (θ ^ k)⁻¹ * Real.exp (θ * lam) := by
      have h6 : lam ^ k ≤ (k.factorial : ℝ) * Real.exp (θ * lam) / θ ^ k := by
        rw [le_div_iff₀ hθk]
        calc lam ^ k * θ ^ k = θ ^ k * lam ^ k := by ring
          _ ≤ (k.factorial : ℝ) * Real.exp (θ * lam) := hExp'
      calc lam ^ k ≤ (k.factorial : ℝ) * Real.exp (θ * lam) / θ ^ k := h6
        _ = (k.factorial : ℝ) * (θ ^ k)⁻¹ * Real.exp (θ * lam) := by ring
    have h4 : (2 : ℝ) ^ k * lam ^ k ≤ (M + 1) * Real.exp (θ * lam) := by
      have h7 : (2 : ℝ) ^ k * lam ^ k
          ≤ 2 ^ k * ((k.factorial : ℝ) * (θ ^ k)⁻¹ * Real.exp (θ * lam)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
      have h8 : (2 : ℝ) ^ k * ((k.factorial : ℝ) * (θ ^ k)⁻¹ * Real.exp (θ * lam))
          = (2 ^ k * (k.factorial : ℝ) * (θ ^ k)⁻¹) * Real.exp (θ * lam) := by ring
      have h9 : (0 : ℝ) ≤ Real.exp (θ * lam) := Real.exp_nonneg _
      nlinarith [h7, h8, hmax2, h9]
    calc (1 + lam) ^ k ≤ (2 * lam) ^ k := h2
      _ = 2 ^ k * lam ^ k := h3
      _ ≤ _ := h4

/-- `e^{θ(1-σ)L}·D^{2x(1-σ)} ≤ 3^{2x+1}(qT)^{c(1-σ)}` when `2x + θ ≤ c`. -/
lemma expDpow_le {q : ℕ} (hq : 2 ≤ q) {T σ x c θ : ℝ} (hT : 1 ≤ T) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hxc : 2 * x + θ ≤ c) (hx0 : 0 ≤ x) :
    Real.exp (θ * ((1 - σ) * Lscale q T)) * Dpow q T (2 * x * (1 - σ))
      ≤ (3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ)) := by
  have hqT1 : (1 : ℝ) ≤ (q : ℝ) * T := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hqTpos : (0 : ℝ) < (q : ℝ) * T := by linarith
  have hscalepos : (0 : ℝ) < scale q T := scale_pos hq hT
  have hs0 : 0 ≤ 1 - σ := by linarith
  have hs1 : 1 - σ ≤ 1 := by linarith
  have hexp_eq : Real.exp (θ * ((1 - σ) * Lscale q T)) = Dpow q T (θ * (1 - σ)) := by
    rw [Dpow, Lscale, Real.rpow_def_of_pos hscalepos]
    congr 1
    ring
  have hDpow_add : Dpow q T (θ * (1 - σ)) * Dpow q T (2 * x * (1 - σ))
      = Dpow q T ((θ + 2 * x) * (1 - σ)) := by
    rw [Dpow, Dpow, ← Real.rpow_add hscalepos]
    congr 1
    ring
  have hr0 : 0 ≤ (θ + 2 * x) * (1 - σ) := by positivity
  have hr1 : (θ + 2 * x) * (1 - σ) ≤ 2 * x + 1 := by
    have h1 : θ * (1 - σ) ≤ 1 := by
      calc θ * (1 - σ) ≤ θ * 1 := mul_le_mul_of_nonneg_left hs1 hθ.le
        _ = θ := by ring
        _ ≤ 1 := hθ1
    have h2 : 2 * x * (1 - σ) ≤ 2 * x := by
      calc 2 * x * (1 - σ) ≤ 2 * x * 1 := mul_le_mul_of_nonneg_left hs1 (by linarith)
        _ = 2 * x := by ring
    have hrw : (θ + 2 * x) * (1 - σ) = θ * (1 - σ) + 2 * x * (1 - σ) := by ring
    rw [hrw]; linarith
  have hr2 : (θ + 2 * x) * (1 - σ) ≤ c * (1 - σ) := by
    have h : θ + 2 * x ≤ c := by linarith
    exact mul_le_mul_of_nonneg_right h hs0
  rw [hexp_eq, hDpow_add]
  have hDle : scale q T ≤ 3 * ((q : ℝ) * T) := by rw [scale]; nlinarith
  have hb1 : Dpow q T ((θ + 2 * x) * (1 - σ))
      ≤ (3 * ((q : ℝ) * T)) ^ ((θ + 2 * x) * (1 - σ)) :=
    Real.rpow_le_rpow (le_of_lt hscalepos) hDle hr0
  have hb2 : (3 * ((q : ℝ) * T)) ^ ((θ + 2 * x) * (1 - σ))
      = (3 : ℝ) ^ ((θ + 2 * x) * (1 - σ)) * ((q : ℝ) * T) ^ ((θ + 2 * x) * (1 - σ)) :=
    Real.mul_rpow (by norm_num) (le_of_lt hqTpos)
  have hb3 : (3 : ℝ) ^ ((θ + 2 * x) * (1 - σ)) ≤ (3 : ℝ) ^ (2 * x + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hr1
  have hb4 : ((q : ℝ) * T) ^ ((θ + 2 * x) * (1 - σ)) ≤ ((q : ℝ) * T) ^ (c * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le hqT1 hr2
  calc Dpow q T ((θ + 2 * x) * (1 - σ)) ≤ (3 * ((q : ℝ) * T)) ^ ((θ + 2 * x) * (1 - σ)) := hb1
    _ = (3 : ℝ) ^ ((θ + 2 * x) * (1 - σ)) * ((q : ℝ) * T) ^ ((θ + 2 * x) * (1 - σ)) := hb2
    _ ≤ (3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ)) :=
        mul_le_mul hb3 hb4 (Real.rpow_nonneg (le_of_lt hqTpos) _)
          (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))

/-- Absorption for the relaxed interface: with `M = C_S(1+λ)^4 X^{2-2σ}` and `(1+λ)^5 ≤ C_θe^{θλ}`,
the box-upgrade output is `≤ C₀(C_S+2)C_θ3^{2x+1}(qT)^{c(1-σ)}` for `2x + θ ≤ c`. -/
theorem absorb_ineq_slack {q : ℕ} (hq : 2 ≤ q) {T σ x c C₀ C_S Cθ θ : ℝ} (hT : 1 ≤ T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC₀ : 0 ≤ C₀) (hC_S : 0 ≤ C_S) (hCθ : 0 < Cθ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hxc : 2 * x + θ ≤ c) (hx0 : 0 ≤ x)
    (hpoly : ∀ lam : ℝ, 0 ≤ lam → (1 + lam) ^ 5 ≤ Cθ * Real.exp (θ * lam)) :
    C₀ * ((1 + (1 - σ) * Lscale q T)
            * (C_S * (1 + (1 - σ) * Lscale q T) ^ 4 * Dpow q T (2 * x * (1 - σ)) + 1) + 1)
      ≤ C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ)) := by
  have hL0 : 0 ≤ Lscale q T := Lscale_nonneg hq hT
  have hs0 : 0 ≤ 1 - σ := by linarith
  have hlam0 : 0 ≤ (1 - σ) * Lscale q T := mul_nonneg hs0 hL0
  have hlam1 : (1 : ℝ) ≤ 1 + (1 - σ) * Lscale q T := by linarith
  have hDp1 : (1 : ℝ) ≤ Dpow q T (2 * x * (1 - σ)) :=
    Real.one_le_rpow (scale_one_le hq hT) (by positivity)
  have hDp0 : (0 : ℝ) ≤ Dpow q T (2 * x * (1 - σ)) := by linarith
  have hCS2 : (0 : ℝ) ≤ C_S + 2 := by linarith
  have hpoly' := hpoly ((1 - σ) * Lscale q T) hlam0
  have hkey : (1 + (1 - σ) * Lscale q T) + 1
      ≤ 2 * (1 + (1 - σ) * Lscale q T) ^ 5 * Dpow q T (2 * x * (1 - σ)) := by
    have h5ge : (1 + (1 - σ) * Lscale q T) ≤ (1 + (1 - σ) * Lscale q T) ^ 5 := by
      have h4 : (1 : ℝ) ≤ (1 + (1 - σ) * Lscale q T) ^ 4 := one_le_pow₀ hlam1
      nlinarith
    have h3 := mul_le_mul h5ge hDp1 (by linarith) (by linarith)
    linarith [h3, hlam1]
  have hstep1 : (1 + (1 - σ) * Lscale q T)
        * (C_S * (1 + (1 - σ) * Lscale q T) ^ 4 * Dpow q T (2 * x * (1 - σ)) + 1) + 1
      ≤ (C_S + 2) * (1 + (1 - σ) * Lscale q T) ^ 5 * Dpow q T (2 * x * (1 - σ)) := by
    nlinarith [hkey, hC_S]
  have hstep2 : (C_S + 2) * (1 + (1 - σ) * Lscale q T) ^ 5 * Dpow q T (2 * x * (1 - σ))
      ≤ (C_S + 2) * Cθ * Real.exp (θ * ((1 - σ) * Lscale q T))
          * Dpow q T (2 * x * (1 - σ)) := by
    have h1 := mul_le_mul_of_nonneg_left hpoly' hCS2
    have h2 := mul_le_mul_of_nonneg_right h1 hDp0
    nlinarith [h2]
  have hstep3 : (C_S + 2) * Cθ * Real.exp (θ * ((1 - σ) * Lscale q T))
        * Dpow q T (2 * x * (1 - σ))
      ≤ (C_S + 2) * Cθ * ((3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ))) := by
    have hCSC : (0 : ℝ) ≤ (C_S + 2) * Cθ := by positivity
    have hmain := expDpow_le (q := q) hq hT hσ0 hσ1 hθ hθ1 hxc hx0
    calc (C_S + 2) * Cθ * Real.exp (θ * ((1 - σ) * Lscale q T)) * Dpow q T (2 * x * (1 - σ))
        = (C_S + 2) * Cθ * (Real.exp (θ * ((1 - σ) * Lscale q T))
            * Dpow q T (2 * x * (1 - σ))) := by ring
      _ ≤ (C_S + 2) * Cθ * ((3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ))) :=
          mul_le_mul_of_nonneg_left hmain hCSC
  calc C₀ * ((1 + (1 - σ) * Lscale q T)
          * (C_S * (1 + (1 - σ) * Lscale q T) ^ 4 * Dpow q T (2 * x * (1 - σ)) + 1) + 1)
      ≤ C₀ * ((C_S + 2) * (1 + (1 - σ) * Lscale q T) ^ 5 * Dpow q T (2 * x * (1 - σ))) :=
        mul_le_mul_of_nonneg_left hstep1 hC₀
    _ ≤ C₀ * ((C_S + 2) * Cθ * Real.exp (θ * ((1 - σ) * Lscale q T))
          * Dpow q T (2 * x * (1 - σ))) := mul_le_mul_of_nonneg_left hstep2 hC₀
    _ ≤ C₀ * ((C_S + 2) * Cθ * ((3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ)))) :=
        mul_le_mul_of_nonneg_left hstep3 hC₀
    _ = C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * x + 1) * ((q : ℝ) * T) ^ (c * (1 - σ)) := by ring

/-- **The assembly, at an exponent `c > 2x`, from the relaxed interface `DualityCountSlack`.** -/
theorem logFreeNP_of_route_slack (p : Params) (c : ℝ) (hc : 2 * p.x < c)
    (h5 : DualityCountSlack p) (h6 : BoxUpgrade p) : logFreeNP p.σ₀ c := by
  obtain ⟨C₀, hC₀pos, c₀, hc₀pos, D₀B, hD₀Bpos, hbox⟩ := h6
  obtain ⟨C_S, hC_Spos, D₀S, hD₀Spos, hdu⟩ := h5 c₀ hc₀pos
  have hθpos : 0 < min ((c - 2 * p.x) / 2) 1 := lt_min (by linarith) one_pos
  obtain ⟨Cθ, hCθpos, hpoly5⟩ := polyOneAddLeExp 5 (min ((c - 2 * p.x) / 2) 1) hθpos
  obtain ⟨Ctr, hCtrpos, htriv⟩ := trivial_bound 1 (by norm_num)
  set D₀ : ℝ := max (max D₀B D₀S) 1 with hD₀def
  have hD₀1 : (1 : ℝ) ≤ D₀ := le_max_right _ _
  have hD₀GB : D₀B ≤ D₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hD₀GS : D₀S ≤ D₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hx0 : 0 ≤ p.x := by linarith [p.hw, p.hwu, p.huv, p.hvx]
  have hcpos : 0 < c := by linarith [p.hw, p.hwu, p.huv, p.hvx]
  refine ⟨max (C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * p.x + 1)) (Ctr * (D₀ * D₀)),
          lt_max_of_lt_left (by positivity), ?_⟩
  intro q hq _inst σ T hσ0 hσ1 hT
  have hC2nn : 0 ≤ Ctr * (D₀ * D₀) := by positivity
  have hqTpos : 0 < (q : ℝ) * T := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hqT1 : 1 ≤ (q : ℝ) * T := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hσ0nn : 0 ≤ σ := by linarith [p.hσ₀, hσ0]
  have hs0 : 0 ≤ 1 - σ := by linarith
  have hexpnn : 0 ≤ c * (1 - σ) := mul_nonneg (le_of_lt hcpos) hs0
  have hrpow1 : 1 ≤ ((q : ℝ) * T) ^ (c * (1 - σ)) := Real.one_le_rpow hqT1 hexpnn
  have hL0 : 0 ≤ Lscale q T := Lscale_nonneg hq hT
  by_cases hDge : D₀ ≤ scale q T
  · set M : ℝ := C_S * (1 + (1 - σ) * Lscale q T) ^ 4 * Dpow q T (2 * p.x * (1 - σ)) with hMdef
    have hMnn : 0 ≤ M := by
      rw [hMdef]
      have h1 : (0 : ℝ) ≤ 1 + (1 - σ) * Lscale q T := by linarith [mul_nonneg hs0 hL0]
      exact mul_nonneg (mul_nonneg (le_of_lt hC_Spos) (by positivity))
        (Dpow_nonneg (q := q) hq hT)
    have hsys : ∀ (m : ℕ) (χ : Fin m → DirichletCharacter ℂ q) (ρ : Fin m → ℂ),
        (∀ i, χ i ≠ 1) → (∀ i, zeroMult (χ i) (ρ i) ≠ 0) →
        (∀ i, σ ≤ (ρ i).re) → (∀ i, (ρ i).re < 1) → (∀ i, |(ρ i).im| ≤ T) →
        (∀ i, c₀ ≤ (1 - (ρ i).re) * Lscale q T) →
        (∀ i j, i ≠ j → χ i = χ j → 1 / Lscale q T ≤ |(ρ i).im - (ρ j).im|) →
        (m : ℝ) ≤ M := by
      intro m χ ρ h1 h2 h3 h4 h5' h6'
      rw [hMdef]
      exact hdu q hq T σ hT (le_trans hD₀GS hDge) hσ0 hσ1 m χ ρ h1 h2 h3 h4 h5' h6'
    have hb := hbox q hq T σ hT (le_trans hD₀GB hDge) hσ0 hσ1 M hMnn hsys
    have hθ1 : min ((c - 2 * p.x) / 2) 1 ≤ 1 := min_le_right _ _
    have hxc : 2 * p.x + min ((c - 2 * p.x) / 2) 1 ≤ c := by
      have := min_le_left ((c - 2 * p.x) / 2) 1
      linarith
    have habs : C₀ * ((1 + (1 - σ) * Lscale q T) * (M + 1) + 1)
        ≤ C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * p.x + 1)
            * ((q : ℝ) * T) ^ (c * (1 - σ)) := by
      rw [hMdef]
      exact absorb_ineq_slack hq hT hσ0nn hσ1 (le_of_lt hC₀pos) (le_of_lt hC_Spos) hCθpos
        hθpos hθ1 hxc hx0 hpoly5
    calc famCountNP q σ T
        ≤ C₀ * ((1 + (1 - σ) * Lscale q T) * (M + 1) + 1) := hb
      _ ≤ C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * p.x + 1)
            * ((q : ℝ) * T) ^ (c * (1 - σ)) := habs
      _ ≤ max (C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * p.x + 1)) (Ctr * (D₀ * D₀))
            * ((q : ℝ) * T) ^ (c * (1 - σ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg (le_of_lt hqTpos) _)
  · have hDlt : scale q T < D₀ := not_le.mp hDge
    have hqTle : (q : ℝ) * T ≤ D₀ := by
      have h1 : (q : ℝ) * T ≤ scale q T := by rw [scale]; nlinarith [hqTpos]
      linarith
    have hb1 : famCountNP q σ T ≤ Ctr * ((q : ℝ) * T) ^ ((1 : ℝ) + 1) :=
      le_trans (famCountNP_le_famCount q σ T) (htriv q hq σ T hσ0nn hσ1 hT)
    have hxx : ((q : ℝ) * T) ^ ((1 : ℝ) + 1) = ((q : ℝ) * T) * ((q : ℝ) * T) := by
      rw [show ((1 : ℝ) + 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    have hsq : ((q : ℝ) * T) * ((q : ℝ) * T) ≤ D₀ * D₀ :=
      mul_self_le_mul_self (le_of_lt hqTpos) hqTle
    calc famCountNP q σ T ≤ Ctr * ((q : ℝ) * T) ^ ((1 : ℝ) + 1) := hb1
      _ = Ctr * (((q : ℝ) * T) * ((q : ℝ) * T)) := by rw [hxx]
      _ ≤ Ctr * (D₀ * D₀) := mul_le_mul_of_nonneg_left hsq (le_of_lt hCtrpos)
      _ ≤ Ctr * (D₀ * D₀) * ((q : ℝ) * T) ^ (c * (1 - σ)) := by
          nlinarith [hC2nn, hrpow1]
      _ ≤ max (C₀ * (C_S + 2) * Cθ * (3 : ℝ) ^ (2 * p.x + 1)) (Ctr * (D₀ * D₀))
            * ((q : ℝ) * T) ^ (c * (1 - σ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.rpow_nonneg (le_of_lt hqTpos) _)


/-! ## 5c. The general Halász duality count, assembled clash-free -/

/-- **The general Halász duality count `DualityCount p`**, assembled by `dualityOfProps` from the
eight analytic inputs.  The two inputs that live on the shifted-divisor-sum (`Jutila`/Selberg) side
are taken in their clash-free copies (`massBoundCF`, `Work.HB7CF.poleResidueBoundCF`), because the
workspace's two copies of `Work.LinnikAreas.Density4.Phi` (`SsmSetup.lean`, used by the
`detector`/`gram` side, and `ShiftedDefs.lean`, used by the shifted-divisor-sum side) cannot be
imported into one environment; this is the documented pre-existing defect
`ZeroFreeTables/STATUS_HBTable7_NAME_CLASH.md`, and the copies used here are the ones the
`Density4`/HB7 tree provides for exactly this purpose. -/
theorem dualityCountOfParamsCF (p : Params) : DualityCount p :=
  dualityOfProps p (massBoundCF p) (Work.HB7CF.poleResidueBoundCF p) (detectorGen p)
    (gramCross p) (gramSame p) (poleLargeSieve p) (detectorTruncation p) (nearLineCount p)

/-! ## 6. The target -/

/-- L7 of JUTILA_UNIFIED_LEAD.md section 3: the final assembly of the unified log-free zero-density estimate, for an explicit parameter packet. Let `p : Work.ZeroDensity.LogFree.Params` (`p.sigma0 > 1/2`, `p.eta > 0`, `0 < p.w < p.u < p.v < p.x`, conditions `P1`, `P2`). Then there is `C > 0` such that for all `q >= 2`, all `sigma` with `p.sigma0 <= sigma <= 1` and all `T >= 1`,

  `sum_{chi != 1} N(sigma,T,chi) <= C * (q*T)^(2*p.x*(1-sigma))`.

The route is the one of `JUTILA_UNIFIED_LEAD.md` section 3: for `D >= D0` the Halasz duality count
`dualityCountOfParamsCF` (L5, from the detector L1, the Graham mean values L2(a), the Gram kernel
bounds L3 and the damped large sieve L4) is applied to the `1/L`-separated system of the box upgrade
`boxUpgradeOfParams` (L6), giving
`famCountNP q sigma T <= C0 * ((lambda+1) * C_S (2 + log2(1+lambda)) X^(2-2*sigma) + 1)` with
`lambda = (1-sigma)*L`; the polynomial-in-`lambda` factor is absorbed into `(qT)^(theta(1-sigma))`
by `(1+lambda)^k <= C e^(theta*lambda)` (`absorb_ineq`), and for `D < D0` the sigma-blind count
bounds the left-hand side while the right-hand side is at least `C`.  Because the target's exponent
is exactly `2x`, the estimate is used not at `p` but at the shrunken packet `p'` of `paramsShrink`
(same `sigma0`, strictly smaller `x`; such a packet always exists by `P1`), whose slack
`c - 2 x' > 0` pays for the polynomial loss; `logFreeNP_mono` then gives the exponent `2x` of `p`
itself. -/
theorem logFreeNPOfParams (p : Work.ZeroDensity.LogFree.Params) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (σ T : ℝ),
      p.σ₀ ≤ σ → σ ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.LogFree.famCountNP q σ T
        ≤ C * ((q : ℝ) * T) ^ (2 * p.x * (1 - σ)) := by
  obtain ⟨p', hp'σ, hp'x⟩ := paramsShrink p
  have hc : 2 * p'.x < (2 * p'.x + 2 * p.x) / 2 := by linarith
  have hle : (2 * p'.x + 2 * p.x) / 2 ≤ 2 * p.x := by linarith
  exact logFreeNP_mono (le_of_eq hp'σ) hle (logFreeNP_of_route p' ((2 * p'.x + 2 * p.x) / 2) hc
    (dualityCountOfParamsCF p') (boxUpgradeOfParams p'))

end Work.ZeroDensity.LogFree
