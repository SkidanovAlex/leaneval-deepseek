import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero
import Submission.Work.BoseFixB1S.corrAuxKin
import Submission.Work.BoseFixB1S.corrPlanchMarg
import Submission.Work.BoseFixB1S.kineticCruxParsed
import Submission.Work.BoseFixB1S.weightedPlancherelKinFT
import Submission.Work.BoseFixB1S.win.chiSmallB_kinFT_decay
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.LocRepoint.chiSmallB_sq_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.CubeWindow

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
# `Submission.Work.BoseFixB1S.CubeWindow.cutWordsCube`

Two cut-word bounds at the **cube** cutoff `chiSmallB` (FS's `χ_B` with the cosine bump), with
cutoff-aware constants.  The mathematics is the same as for the ball window
(`Work.BoseFixB1S.corrCutWords`) but driven by the **`N`-th order** Fourier decay of the cube
window rather than by `C^∞`:

* `chiSmallB M ℓ d u = χ(x/ℓ)·χ_M(x/(ℓd) − u)` is `C^{M−1}` and its `(ℓd)`-scale factor is
  supported in the unit ball; hence for `N + 1 ≤ M`
  (`Work.BoseFixB1S.win.chiSmallB_kinFT_decay`)

      `‖kinFT (chiSmallB) p‖ ≤ C (ℓd)³ / (1 + (ℓd)‖p‖)^N`     (`C` uniform in `0<ℓ,0<d≤1,u`),

  which unwinds to the decay `‖p‖^N‖kinFT p‖ ≤ C (ℓd)^{3−N}`;
* with the small-box cut-off `c = (dsℓ)^{-1}` the closed exterior integrals
  `∫_{‖p‖>c}‖p‖^{-n} = 4π/(n−3)·c^{3−n}` then give

      `bsW ≤ C'(ℓd)·s^{2N−5}`   and   `∫ [·]₊⁴‖kinFT‖² ≤ C'(ℓd)^{-1}·s^{2N−7}`.

All ingredients are proved here or imported from previously landed (`sorry`-free) modules.
-/

/-! ## 0. Auxiliary lemmas -/

/-- `bsPsi` is continuous for **continuous, compactly supported** data (the corpus lemma
`Work.BSKinetic.Decomp.continuous_bsPsi` assumes `C^∞`; the cube cutoff `chiSmallB M` is only
`C^{M-1}`, so the weaker hypothesis is needed). -/
private theorem continuous_bsPsi_of_continuous {h : E3 → ℝ} (hcont : Continuous h)
    (hcs : HasCompactSupport h) :
    Continuous (fun p : E3 => Work.BSKinetic.Decomp.bsPsi h p) := by
  have hint : Integrable (fun y : E3 => (h y : ℂ)) :=
    (Complex.continuous_ofReal.comp hcont).integrable_of_hasCompactSupport
      (hcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
  show Continuous (fun p : E3 =>
    ∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (h y : ℂ))
  refine MeasureTheory.continuous_of_dominated
    (F := fun (p y : E3) => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (h y : ℂ))
    (bound := fun y : E3 => ‖h y‖) ?_ ?_ ?_ ?_
  · intro p
    exact (by fun_prop : Continuous fun y : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (h y : ℂ)).aestronglyMeasurable
  · intro p
    filter_upwards with y
    rw [norm_mul, Work.BSKinetic.Decomp.norm_exp_neg_I_inner p y, one_mul]
    simp
  · simpa using hint.norm
  · filter_upwards with y
    fun_prop

/-- **From the `N`-th order Fourier decay to the `‖p‖^N` decay.**  If
`‖ψ p‖ ≤ C L³/(1+L‖p‖)^N` then `‖p‖^N ‖ψ p‖ ≤ C L³ (L^N)^{-1}`. -/
private lemma decay_extract {N : ℕ} {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L) {ψ : E3 → ℂ}
    (hdec : ∀ p : E3, ‖ψ p‖ ≤ C * L ^ 3 / (1 + L * ‖p‖) ^ N) (p : E3) :
    ‖p‖ ^ N * ‖ψ p‖ ≤ C * L ^ 3 * ((L ^ N)⁻¹) := by
  have hden : 0 < 1 + L * ‖p‖ := by positivity
  have hdenN : (0 : ℝ) < (1 + L * ‖p‖) ^ N := pow_pos hden N
  have hr : ‖p‖ / (1 + L * ‖p‖) ≤ L⁻¹ := by
    rw [div_le_iff₀ hden]
    have hid : L⁻¹ * (1 + L * ‖p‖) = L⁻¹ + ‖p‖ := by
      rw [mul_add, mul_one, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hL), one_mul]
    rw [hid]
    exact le_add_of_nonneg_left (by positivity)
  have hmul : (1 + L * ‖p‖) ^ N * ‖ψ p‖ ≤ C * L ^ 3 := by
    have h := hdec p
    rw [le_div_iff₀ hdenN] at h
    simpa [mul_comm] using h
  calc ‖p‖ ^ N * ‖ψ p‖
      = (‖p‖ / (1 + L * ‖p‖)) ^ N * ((1 + L * ‖p‖) ^ N * ‖ψ p‖) := by
        rw [div_pow, ← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hdenN)]
    _ ≤ (L⁻¹) ^ N * (C * L ^ 3) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hr N) hmul (by positivity) (by positivity)
    _ = C * L ^ 3 * ((L ^ N)⁻¹) := by rw [inv_pow]; ring

/-- The `[r−c]₊²` pointwise tail bound. -/
private lemma tail_quad {N : ℕ} (hN : 2 ≤ N) {A c : ℝ} (hc : 0 < c) {ψ : E3 → ℂ}
    (hdec : ∀ p : E3, ‖p‖ ^ N * ‖ψ p‖ ≤ A) {p : E3} (hp : c < ‖p‖) :
    Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖ψ p‖ ^ 2
      ≤ A ^ 2 * (((‖p‖ : ℝ) ^ (2 * N - 2))⁻¹) := by
  have hr : 0 < ‖p‖ := lt_trans hc hp
  have hrn : (‖p‖ : ℝ) ≠ 0 := ne_of_gt hr
  have hmax : Submission.BoseGases.fsKinCoeff c ‖p‖ ≤ ‖p‖ ^ 2 := by
    have h1 : max (‖p‖ - c) 0 ≤ ‖p‖ := max_le (by linarith) (norm_nonneg _)
    have h2 : (0 : ℝ) ≤ max (‖p‖ - c) 0 := le_max_right _ _
    show (max (‖p‖ - c) 0) ^ 2 ≤ ‖p‖ ^ 2
    exact pow_le_pow_left₀ h2 h1 2
  have hsq : (‖p‖ ^ N * ‖ψ p‖) ^ 2 = (‖p‖ : ℝ) ^ (2 * N) * ‖ψ p‖ ^ 2 := by
    have hN2 : N * 2 = 2 * N := by omega
    rw [mul_pow, ← pow_mul, hN2]
  have hsplit : (‖p‖ : ℝ) ^ (2 * N) = (‖p‖ : ℝ) ^ (2 * N - 2) * ‖p‖ ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hkey : ‖p‖ ^ 2 * ‖ψ p‖ ^ 2
      = (‖p‖ ^ N * ‖ψ p‖) ^ 2 * (((‖p‖ : ℝ) ^ (2 * N - 2))⁻¹) := by
    rw [hsq, hsplit]
    have hc0 : (‖p‖ : ℝ) ^ (2 * N - 2) * (((‖p‖ : ℝ) ^ (2 * N - 2))⁻¹) = 1 :=
      mul_inv_cancel₀ (pow_ne_zero _ hrn)
    calc ‖p‖ ^ 2 * ‖ψ p‖ ^ 2
        = ((‖p‖ : ℝ) ^ (2 * N - 2) * (((‖p‖ : ℝ) ^ (2 * N - 2))⁻¹)) *
            (‖p‖ ^ 2 * ‖ψ p‖ ^ 2) := by
          rw [hc0, one_mul]
      _ = ((‖p‖ : ℝ) ^ (2 * N - 2) * ‖p‖ ^ 2) * ‖ψ p‖ ^ 2 *
            (((‖p‖ : ℝ) ^ (2 * N - 2))⁻¹) := by ring
  calc Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖ψ p‖ ^ 2
      ≤ ‖p‖ ^ 2 * ‖ψ p‖ ^ 2 := mul_le_mul_of_nonneg_right hmax (sq_nonneg _)
    _ = (‖p‖ ^ N * ‖ψ p‖) ^ 2 * (((‖p‖ : ℝ) ^ (2 * N - 2))⁻¹) := hkey
    _ ≤ A ^ 2 * (((‖p‖ : ℝ) ^ (2 * N - 2))⁻¹) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hdec p) 2) (by positivity)

/-- The `[r−c]₊⁴` pointwise tail bound. -/
private lemma tail_quartic {N : ℕ} (hN : 2 ≤ N) {A c : ℝ} (hc : 0 < c) {ψ : E3 → ℂ}
    (hdec : ∀ p : E3, ‖p‖ ^ N * ‖ψ p‖ ≤ A) {p : E3} (hp : c < ‖p‖) :
    (Submission.BoseGases.fsKinCoeff c ‖p‖) ^ 2 * ‖ψ p‖ ^ 2
      ≤ A ^ 2 * (((‖p‖ : ℝ) ^ (2 * N - 4))⁻¹) := by
  have hr : 0 < ‖p‖ := lt_trans hc hp
  have hrn : (‖p‖ : ℝ) ≠ 0 := ne_of_gt hr
  have hmax : Submission.BoseGases.fsKinCoeff c ‖p‖ ≤ ‖p‖ ^ 2 := by
    have h1 : max (‖p‖ - c) 0 ≤ ‖p‖ := max_le (by linarith) (norm_nonneg _)
    have h2 : (0 : ℝ) ≤ max (‖p‖ - c) 0 := le_max_right _ _
    show (max (‖p‖ - c) 0) ^ 2 ≤ ‖p‖ ^ 2
    exact pow_le_pow_left₀ h2 h1 2
  have hsq : (‖p‖ ^ N * ‖ψ p‖) ^ 2 = (‖p‖ : ℝ) ^ (2 * N) * ‖ψ p‖ ^ 2 := by
    have hN2 : N * 2 = 2 * N := by omega
    rw [mul_pow, ← pow_mul, hN2]
  have hsplit : (‖p‖ : ℝ) ^ (2 * N) = (‖p‖ : ℝ) ^ (2 * N - 4) * ‖p‖ ^ 4 := by
    rw [← pow_add]
    congr 1
    omega
  have hkey : (‖p‖ ^ 2) ^ 2 * ‖ψ p‖ ^ 2
      = (‖p‖ ^ N * ‖ψ p‖) ^ 2 * (((‖p‖ : ℝ) ^ (2 * N - 4))⁻¹) := by
    rw [hsq, hsplit]
    have hc0 : (‖p‖ : ℝ) ^ (2 * N - 4) * (((‖p‖ : ℝ) ^ (2 * N - 4))⁻¹) = 1 :=
      mul_inv_cancel₀ (pow_ne_zero _ hrn)
    calc (‖p‖ ^ 2) ^ 2 * ‖ψ p‖ ^ 2
        = ((‖p‖ : ℝ) ^ (2 * N - 4) * (((‖p‖ : ℝ) ^ (2 * N - 4))⁻¹)) *
            ((‖p‖ ^ 2) ^ 2 * ‖ψ p‖ ^ 2) := by
          rw [hc0, one_mul]
      _ = ((‖p‖ : ℝ) ^ (2 * N - 4) * ‖p‖ ^ 4) * ‖ψ p‖ ^ 2 *
            (((‖p‖ : ℝ) ^ (2 * N - 4))⁻¹) := by ring
  calc (Submission.BoseGases.fsKinCoeff c ‖p‖) ^ 2 * ‖ψ p‖ ^ 2
      ≤ (‖p‖ ^ 2) ^ 2 * ‖ψ p‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) hmax 2) (sq_nonneg _)
    _ = (‖p‖ ^ N * ‖ψ p‖) ^ 2 * (((‖p‖ : ℝ) ^ (2 * N - 4))⁻¹) := hkey
    _ ≤ A ^ 2 * (((‖p‖ : ℝ) ^ (2 * N - 4))⁻¹) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hdec p) 2) (by positivity)

/-! ## 1. The two elementary arithmetic identities -/

/-- `c^{3−(2N−2)} = (ℓd)^{2N−5} s^{2N−5}` for `c = (dsℓ)^{-1}`. -/
private lemma cutWords_exp_first {N : ℕ} (hN : 5 ≤ N) {ℓ d s c : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hc : c = (d * s * ℓ)⁻¹) :
    c ^ ((3 : ℝ) - ((2 * N - 2 : ℕ) : ℝ)) = (ℓ * d) ^ (2 * N - 5) * s ^ (2 * N - 5) := by
  have hcp : 0 < c := by rw [hc]; positivity
  have hcast : (3 : ℝ) - ((2 * N - 2 : ℕ) : ℝ) = -(((2 * N - 5 : ℕ)) : ℝ) := by
    have h : ((2 * N - 2 : ℕ) : ℝ) = ((2 * N - 5 : ℕ) : ℝ) + 3 := by
      have hh : (2 * N - 2 : ℕ) = (2 * N - 5) + 3 := by omega
      rw [hh]; push_cast; ring
    rw [h]; ring
  rw [hcast, Real.rpow_neg hcp.le, Real.rpow_natCast, hc]
  have hdsl : d * s * ℓ = (ℓ * d) * s := by ring
  rw [hdsl, inv_pow, mul_pow, inv_inv]

/-- `c^{3−(2N−4)} = (ℓd)^{2N−7} s^{2N−7}` for `c = (dsℓ)^{-1}`. -/
private lemma cutWords_exp_second {N : ℕ} (hN : 6 ≤ N) {ℓ d s c : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hc : c = (d * s * ℓ)⁻¹) :
    c ^ ((3 : ℝ) - ((2 * N - 4 : ℕ) : ℝ)) = (ℓ * d) ^ (2 * N - 7) * s ^ (2 * N - 7) := by
  have hcp : 0 < c := by rw [hc]; positivity
  have hcast : (3 : ℝ) - ((2 * N - 4 : ℕ) : ℝ) = -(((2 * N - 7 : ℕ)) : ℝ) := by
    have h : ((2 * N - 4 : ℕ) : ℝ) = ((2 * N - 7 : ℕ) : ℝ) + 3 := by
      have hh : (2 * N - 4 : ℕ) = (2 * N - 7) + 3 := by omega
      rw [hh]; push_cast; ring
    rw [h]; ring
  rw [hcast, Real.rpow_neg hcp.le, Real.rpow_natCast, hc]
  have hdsl : d * s * ℓ = (ℓ * d) * s := by ring
  rw [hdsl, inv_pow, mul_pow, inv_inv]

/-- The `(ℓd)`-bookkeeping of the first bound. -/
private lemma cutWords_pow_first {N : ℕ} (hN : 5 ≤ N) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) :
    (ℓ * d) ^ 6 * (((ℓ * d) ^ (2 * N))⁻¹) * (ℓ * d) ^ (2 * N - 5) = ℓ * d := by
  have hp : (ℓ * d) ≠ 0 := ne_of_gt (mul_pos hℓ hd)
  have hsum : 6 + (2 * N - 5) = 2 * N + 1 := by omega
  calc (ℓ * d) ^ 6 * (((ℓ * d) ^ (2 * N))⁻¹) * (ℓ * d) ^ (2 * N - 5)
      = ((ℓ * d) ^ 6 * (ℓ * d) ^ (2 * N - 5)) * (((ℓ * d) ^ (2 * N))⁻¹) := by ring
    _ = (ℓ * d) ^ (6 + (2 * N - 5)) * (((ℓ * d) ^ (2 * N))⁻¹) := by rw [pow_add]
    _ = (ℓ * d) ^ (2 * N + 1) * (((ℓ * d) ^ (2 * N))⁻¹) := by rw [hsum]
    _ = ((ℓ * d) ^ (2 * N) * (ℓ * d)) * (((ℓ * d) ^ (2 * N))⁻¹) := by rw [pow_succ]
    _ = (ℓ * d) * (((ℓ * d) ^ (2 * N)) * (((ℓ * d) ^ (2 * N))⁻¹)) := by ring
    _ = ℓ * d := by rw [mul_inv_cancel₀ (pow_ne_zero _ hp), mul_one]

/-- The `(ℓd)`-bookkeeping of the second bound. -/
private lemma cutWords_pow_second {N : ℕ} (hN : 6 ≤ N) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) :
    (ℓ * d) ^ 6 * (((ℓ * d) ^ (2 * N))⁻¹) * (ℓ * d) ^ (2 * N - 7) = (ℓ * d)⁻¹ := by
  have hp : (ℓ * d) ≠ 0 := ne_of_gt (mul_pos hℓ hd)
  have hsum : 6 + (2 * N - 7) = 2 * N - 1 := by omega
  calc (ℓ * d) ^ 6 * (((ℓ * d) ^ (2 * N))⁻¹) * (ℓ * d) ^ (2 * N - 7)
      = ((ℓ * d) ^ 6 * (ℓ * d) ^ (2 * N - 7)) * (((ℓ * d) ^ (2 * N))⁻¹) := by ring
    _ = (ℓ * d) ^ (6 + (2 * N - 7)) * (((ℓ * d) ^ (2 * N))⁻¹) := by rw [pow_add]
    _ = (ℓ * d) ^ (2 * N - 1) * (((ℓ * d) ^ (2 * N))⁻¹) := by rw [hsum]
    _ = (ℓ * d) ^ (2 * N - 1) * (((ℓ * d) ^ (2 * N - 1) * (ℓ * d))⁻¹) := by
        have h : (ℓ * d) ^ (2 * N) = (ℓ * d) ^ (2 * N - 1) * (ℓ * d) := by
          conv_lhs => rw [show (2 * N) = (2 * N - 1) + 1 by omega]
          rw [pow_succ]
        rw [h]
    _ = (ℓ * d) ^ (2 * N - 1) * (((ℓ * d) ^ (2 * N - 1))⁻¹ * (ℓ * d)⁻¹) := by rw [mul_inv]
    _ = (ℓ * d)⁻¹ := by
        rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp), one_mul]

/-- The first target identity:
`A²·4π/((2N−2)−3)·c^{3−(2N−2)} = C²·4π/(2N−5)·(ℓd)·s^{2N−5}`. -/
private lemma cutWords_arith_first {N : ℕ} (hN : 8 ≤ N) {C ℓ d s c : ℝ}
    (hC : 0 ≤ C) (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hc : c = (d * s * ℓ)⁻¹) :
    (C * (ℓ * d) ^ 3 * (((ℓ * d) ^ N)⁻¹)) ^ 2 *
        (4 * Real.pi / (((2 * N - 2 : ℕ) : ℝ) - 3) * c ^ ((3 : ℝ) - ((2 * N - 2 : ℕ) : ℝ)))
      = C ^ 2 * (4 * Real.pi / ((2 * N - 5 : ℕ) : ℝ)) * (ℓ * d) * s ^ (2 * N - 5) := by
  have hden : (((2 * N - 2 : ℕ) : ℝ) - 3) = ((2 * N - 5 : ℕ) : ℝ) := by
    have h : (2 * N - 2 : ℕ) = (2 * N - 5) + 3 := by omega
    rw [h]; push_cast; ring
  have hApow : (C * (ℓ * d) ^ 3 * (((ℓ * d) ^ N)⁻¹)) ^ 2
      = C ^ 2 * (ℓ * d) ^ 6 * (((ℓ * d) ^ (2 * N))⁻¹) := by
    have h1 : ((ℓ * d) ^ 3) ^ 2 = (ℓ * d) ^ 6 := by rw [← pow_mul]
    have h2 : (((ℓ * d) ^ N)⁻¹) ^ 2 = (((ℓ * d) ^ (2 * N))⁻¹) := by
      have hN2 : N * 2 = 2 * N := by omega
      rw [inv_pow, ← pow_mul, hN2]
    rw [mul_pow, mul_pow, h1, h2]
  have hgroup : C ^ 2 * (ℓ * d) ^ 6 * (((ℓ * d) ^ (2 * N))⁻¹) *
        (4 * Real.pi / ((2 * N - 5 : ℕ) : ℝ) * ((ℓ * d) ^ (2 * N - 5) * s ^ (2 * N - 5)))
      = C ^ 2 * (4 * Real.pi / ((2 * N - 5 : ℕ) : ℝ)) *
          (((ℓ * d) ^ 6 * (((ℓ * d) ^ (2 * N))⁻¹) * (ℓ * d) ^ (2 * N - 5))
            * s ^ (2 * N - 5)) := by
    ring
  rw [hden, cutWords_exp_first (by omega) hℓ hd hs hc, hApow, hgroup,
    cutWords_pow_first (by omega) hℓ hd]
  ring

/-- The second target identity:
`A²·4π/((2N−4)−3)·c^{3−(2N−4)} = C²·4π/(2N−7)·(ℓd)^{-1}·s^{2N−7}`. -/
private lemma cutWords_arith_second {N : ℕ} (hN : 8 ≤ N) {C ℓ d s c : ℝ}
    (hC : 0 ≤ C) (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hc : c = (d * s * ℓ)⁻¹) :
    (C * (ℓ * d) ^ 3 * (((ℓ * d) ^ N)⁻¹)) ^ 2 *
        (4 * Real.pi / (((2 * N - 4 : ℕ) : ℝ) - 3) * c ^ ((3 : ℝ) - ((2 * N - 4 : ℕ) : ℝ)))
      = C ^ 2 * (4 * Real.pi / ((2 * N - 7 : ℕ) : ℝ)) * (ℓ * d)⁻¹ * s ^ (2 * N - 7) := by
  have hden : (((2 * N - 4 : ℕ) : ℝ) - 3) = ((2 * N - 7 : ℕ) : ℝ) := by
    have h : (2 * N - 4 : ℕ) = (2 * N - 7) + 3 := by omega
    rw [h]; push_cast; ring
  have hApow : (C * (ℓ * d) ^ 3 * (((ℓ * d) ^ N)⁻¹)) ^ 2
      = C ^ 2 * (ℓ * d) ^ 6 * (((ℓ * d) ^ (2 * N))⁻¹) := by
    have h1 : ((ℓ * d) ^ 3) ^ 2 = (ℓ * d) ^ 6 := by rw [← pow_mul]
    have h2 : (((ℓ * d) ^ N)⁻¹) ^ 2 = (((ℓ * d) ^ (2 * N))⁻¹) := by
      have hN2 : N * 2 = 2 * N := by omega
      rw [inv_pow, ← pow_mul, hN2]
    rw [mul_pow, mul_pow, h1, h2]
  have hgroup : C ^ 2 * (ℓ * d) ^ 6 * (((ℓ * d) ^ (2 * N))⁻¹) *
        (4 * Real.pi / ((2 * N - 7 : ℕ) : ℝ) * ((ℓ * d) ^ (2 * N - 7) * s ^ (2 * N - 7)))
      = C ^ 2 * (4 * Real.pi / ((2 * N - 7 : ℕ) : ℝ)) *
          (((ℓ * d) ^ 6 * (((ℓ * d) ^ (2 * N))⁻¹) * (ℓ * d) ^ (2 * N - 7))
            * s ^ (2 * N - 7)) := by
    ring
  rw [hden, cutWords_exp_second (by omega) hℓ hd hs hc, hApow, hgroup,
    cutWords_pow_second (by omega) hℓ hd]
  ring

/-! ## 2. The target -/

/-- Two cut-word bounds at the **cube** cutoff `chiSmallB` (FS's `χ_B` with the cosine bump), with
the cutoff-aware constants `(ℓd)·s^{2N-5}` and `(ℓd)⁻¹·s^{2N-7}` coming from the `N`-th order
Fourier decay of the window and the small-box cutoff `c = (dsℓ)⁻¹`. -/
theorem cutWordsCube (N M : ℕ) (hNM : N + 1 ≤ M) (hN : 8 ≤ N) :
    ∃ Cq Ce : ℝ, 0 ≤ Cq ∧ 0 ≤ Ce ∧
      ∀ {ℓ d s c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
        (hc : c = (d * s * ℓ)⁻¹) (u : EuclideanSpace ℝ (Fin 3)),
        MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
            (Submission.BoseGases.fsKinCoeff c ‖p‖) ^ 2 *
              ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2)
        ∧ Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
              (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiSmallB M ℓ d u z)
            ≤ Cq * (ℓ * d) * s ^ (2 * N - 5)
        ∧ (∫ p : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.fsKinCoeff c ‖p‖) ^ 2 *
              ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2)
            ≤ Ce * (ℓ * d)⁻¹ * s ^ (2 * N - 7) := by
  obtain ⟨C, hC0, hCdec⟩ := Work.BoseFixB1S.win.chiSmallB_kinFT_decay N M hNM
  have hden1 : (0 : ℝ) < ((2 * N - 5 : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * N - 5 := by omega
    exact_mod_cast this
  have hden2 : (0 : ℝ) < ((2 * N - 7 : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * N - 7 := by omega
    exact_mod_cast this
  refine ⟨C ^ 2 * (4 * Real.pi / ((2 * N - 5 : ℕ) : ℝ)),
    C ^ 2 * (4 * Real.pi / ((2 * N - 7 : ℕ) : ℝ)),
    mul_nonneg (sq_nonneg C) (div_nonneg (by positivity) hden1.le),
    mul_nonneg (sq_nonneg C) (div_nonneg (by positivity) hden2.le), ?_⟩
  intro ℓ d s c hℓ hd hd1 hs hs1 hc u
  have hM1 : 1 ≤ M := by omega
  have hLd : 0 < ℓ * d := mul_pos hℓ hd
  have hcpos : 0 < c := by rw [hc]; exact inv_pos.mpr (by positivity)
  -- the cube window: continuity and compact support
  have hcont : Continuous (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) := by
    have h1 : Continuous (fun z : E3 => Submission.BoseGases.chiScale ℓ z) :=
      Submission.BoseGases.chiScale_continuous ℓ
    have h2 : Continuous (fun z : E3 =>
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)) :=
      (Submission.BoseGases.chiSmall_continuous hM1).comp (by fun_prop)
    exact h1.mul h2
  have hcs : HasCompactSupport (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) :=
    (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)).mul_right
  have hψcont : Continuous (fun p : E3 => Work.BSKinetic.Decomp.bsPsi
      (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p) :=
    continuous_bsPsi_of_continuous hcont hcs
  -- the `N`-th order decay of the window
  have hdec : ∀ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
      (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖
      ≤ C * (ℓ * d) ^ 3 / (1 + (ℓ * d) * ‖p‖) ^ N := by
    intro p
    have h := hCdec hℓ hd hd1 u p
    simpa only [Work.BSKinetic.Decomp.bsPsi] using h
  set A : ℝ := C * (ℓ * d) ^ 3 * (((ℓ * d) ^ N)⁻¹) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (mul_nonneg hC0 (pow_nonneg hLd.le 3))
      (inv_nonneg.mpr (pow_nonneg hLd.le N))
  have hdecA : ∀ p : E3, ‖p‖ ^ N * ‖Work.BSKinetic.Decomp.bsPsi
      (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ≤ A := by
    intro p
    rw [hAdef]
    exact decay_extract hC0 hLd hdec p
  -- measurability
  have hFc : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
    show Continuous (fun p : E3 => (max (‖p‖ - c) 0) ^ 2)
    exact ((continuous_norm.sub continuous_const).max continuous_const).pow 2
  have hmeas1 : AEStronglyMeasurable (fun p : E3 =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2) volume :=
    (hFc.mul (hψcont.norm.pow 2)).aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun p : E3 =>
      (Submission.BoseGases.fsKinCoeff c ‖p‖) ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2) volume :=
    ((hFc.pow 2).mul (hψcont.norm.pow 2)).aestronglyMeasurable
  -- the pointwise tail bounds
  have hbd1 : ∀ p : E3, c < ‖p‖ →
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2
        ≤ A ^ 2 * (((‖p‖ : ℝ) ^ (2 * N - 2))⁻¹) :=
    fun p hp => tail_quad (by omega) hcpos hdecA hp
  have hbd2 : ∀ p : E3, c < ‖p‖ →
      (Submission.BoseGases.fsKinCoeff c ‖p‖) ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2
        ≤ A ^ 2 * (((‖p‖ : ℝ) ^ (2 * N - 4))⁻¹) :=
    fun p hp => tail_quartic (by omega) hcpos hdecA hp
  have hzero1 : ∀ p : E3, ¬ (c < ‖p‖) →
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2 = 0 := by
    intro p hp
    rw [Submission.BoseGases.fsKinCoeff_of_le (not_lt.mp hp), zero_mul]
  have hzero2 : ∀ p : E3, ¬ (c < ‖p‖) →
      (Submission.BoseGases.fsKinCoeff c ‖p‖) ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2 = 0 := by
    intro p hp
    rw [Submission.BoseGases.fsKinCoeff_of_le (not_lt.mp hp), zero_pow (by norm_num), zero_mul]
  have hnn1 : ∀ p : E3, 0 ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2 :=
    fun p => mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)
  have hnn2 : ∀ p : E3, 0 ≤ (Submission.BoseGases.fsKinCoeff c ‖p‖) ^ 2 *
      ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2 :=
    fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- integrability of the quartic integrand
  have hint2 : MeasureTheory.Integrable (fun p : E3 =>
      (Submission.BoseGases.fsKinCoeff c ‖p‖) ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2) :=
    Work.BoseFixB1S.integrable_of_tail_bound (g := fun p : E3 =>
        (Submission.BoseGases.fsKinCoeff c ‖p‖) ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi
          (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2)
      hcpos (sq_nonneg A) (2 * N - 4) (by omega) hbd2 hzero2 hnn2 hmeas2
  -- the two integral bounds
  have hle1 := Work.BoseFixB1S.integral_le_tail_bound (g := fun p : E3 =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2)
    hcpos (sq_nonneg A) (2 * N - 2) (by omega) hbd1 hzero1 hnn1
  have hle2 := Work.BoseFixB1S.integral_le_tail_bound (g := fun p : E3 =>
      (Submission.BoseGases.fsKinCoeff c ‖p‖) ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2)
    hcpos (sq_nonneg A) (2 * N - 4) (by omega) hbd2 hzero2 hnn2
  refine ⟨hint2, ?_, ?_⟩
  · rw [show Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z)
        = ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi
            (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) p‖ ^ 2 from rfl]
    refine hle1.trans (le_of_eq ?_)
    rw [hAdef]
    exact cutWords_arith_first hN hC0 hℓ hd hs hc
  · refine hle2.trans (le_of_eq ?_)
    rw [hAdef]
    exact cutWords_arith_second hN hC0 hℓ hd hs hc

end Work.BoseFixB1S.CubeWindow
