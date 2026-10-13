/-
# The `z`-pointwise bound on the angular moments `Qang g i z` in the open class

For a datum `g` which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen`) and honestly in `ℋ⁴` (`Work.Spaces.HkMem α 4 g`), the
angular moment

  `Qang g i z = ∫_θ Ktheta θ · (D_z^i g)(z,θ) dθ`,   `Ktheta θ = 3 sin θ cos²θ`,

satisfies, for every `i ≤ 3` and every `z > 0`,

  `(Qang g i z)² ≤ (∫_θ Ktheta θ² dθ) · HkSq α 4 g`.

This is the open-quadrant version of `Work.FTS.Nonlinear.Pieces.Qang_sq_le_const` (which
additionally assumes `SmoothQuad g` and the decay `D_z^i g z θ → 0` as `z → ∞`, and uses the
radial Hardy inequality `Work.FTS.H2.HQ.HardyZQ`).  No decay is available here, and the
pointwise-in-`z` Hardy inequality is false without it.  The replacement is a **relative-window
Agmon device**: for `z > 0` and every `θ ∈ (0,π/2)` the `tvAverageLe` estimate applied to
`U(s) = (D_z^i g s θ)²` on the window `[z,2z]` gives

  `(D_z^i g z θ)² ≤ (2/z)·w(2z)^{-2}·(∫_z^{2z}(D_z^i g s θ)²w(s)²ds
      + ∫_z^{2z}(D_z^{i+1} g s θ)²w(s)²ds)`,   `w(s) = (1+s)²/s²`

(`windowBoundDzIter_local` below — the sibling module
`Submission.Work.FTS.StrongEps.E4R3.QangSqAux.windowBoundDzIter` proves the same statement
independently — the price being the *weighted* integrals of the two adjacent slots
instead of the value at infinity.  Both of those slots are summands of `HkIntegrand α 4 g`
(`sin(2θ)^{-η} ≥ 1`), and `2·(2/z)·w(2z)^{-2} ≤ 1` (equivalently `64z³ ≤ (1+2z)⁴`).

Hence, a.e. in `θ`,

  `(D_z^i g z θ)² ≤ ∫_s HkIntegrand α 4 g s θ ds`

and integrating in `θ` (with `HkSqSwap_C4` for the identification
`∫_θ∫_s HkIntegrand = HkSq α 4 g`) gives `∫_θ (D_z^i g z θ)² dθ ≤ HkSq α 4 g`; Cauchy–Schwarz
in `θ` (`Qang_sq_leQ_open`) then yields the claim with the sharp angular constant.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.H2.Qang_sq_leQ
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.StrongEps.E4R3.NauxAux.zSliceNormLeHkSq
import Submission.Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux.tvAverageLe
import Submission.Work.FTS_RegExport.C4.HkSqSwap_C4
import Submission.Work.Spaces.Slots.lintegral_DzIter_le_HkSq_smooth
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary properties of the weight `w` -/

/-- **The weight `w` is decreasing on `(0,∞)`**: `w(s) = (1 + 1/s)²` and `s ↦ 1/s` is
antitone. -/
theorem w_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Work.Spaces.w b ≤ Work.Spaces.w a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : Work.Spaces.w b = (1 + b⁻¹) ^ 2 := by
    rw [Work.Spaces.w, ← div_pow, add_div, div_self (ne_of_gt hb)]
    ring
  have h2 : Work.Spaces.w a = (1 + a⁻¹) ^ 2 := by
    rw [Work.Spaces.w, ← div_pow, add_div, div_self (ne_of_gt ha)]
    ring
  rw [h1, h2]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  have h := inv_anti₀ ha hab
  linarith

/-- The elementary arithmetic inequality behind the constant of the window device:
`64 z³ ≤ (1 + 2z)⁴` for `z ≥ 0` (equivalently `2·(2/z)·w(2z)^{-2} ≤ 1`). -/
theorem sixtyfour_mul_cube_le {z : ℝ} (hz : 0 ≤ z) : 64 * z ^ 3 ≤ (1 + 2 * z) ^ 4 := by
  have hfac : (1 + 2 * z) ^ 4 - 64 * z ^ 3
      = 1 + 8 * z * (2 * z * (z - 1) ^ 2 + (z + 1)) := by ring
  have hpos : (0 : ℝ) ≤ 2 * z * (z - 1) ^ 2 + (z + 1) := by nlinarith [sq_nonneg (z - 1), hz]
  nlinarith [hfac, hpos, hz]

/-- **The coefficient of the window device is at most `1/2`**:
`2·(2/z)·w(2z)^{-2} ≤ 1` for `z > 0`. -/
theorem two_mul_coef_le_one {z : ℝ} (hz : 0 < z) :
    2 * ((2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹) ≤ 1 := by
  have hw : (Work.Spaces.w (2 * z)) ^ 2 = (1 + 2 * z) ^ 4 / (16 * z ^ 4) := by
    rw [Work.Spaces.w, div_pow]; field_simp; ring
  rw [hw, inv_div]
  have h64 : 64 * z ^ 3 ≤ (1 + 2 * z) ^ 4 := sixtyfour_mul_cube_le hz.le
  have hden : 0 < (1 + 2 * z) ^ 4 := by positivity
  rw [show (2 : ℝ) * (2 / z * (16 * z ^ 4 / (1 + 2 * z) ^ 4))
      = 64 * z ^ 3 / (1 + 2 * z) ^ 4 by field_simp; ring]
  rw [div_le_one hden]
  exact h64

/-! ## Pointwise domination of a pure `D_z`-slot by the `ℋ⁴`-integrand -/

/-- On the open quadrant, a pure `D_z`-slot of order `k ≤ 4` is dominated by `HkIntegrand`:
the `k`-th summand of the pure sum is `(D_z^k g · w / sin(2θ)^{η/2})²` and
`sin(2θ)^{η/2} ≤ 1`. -/
theorem dzSlot_sq_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {k : ℕ} (hk : k ≤ 4)
    {z θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.DzIter k f z θ * Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
  have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.Spaces.Slots.one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hkey := Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ k hk
  have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  have heq : (Work.Spaces.DzIter k f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter k f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
    ring
  calc (Work.Spaces.DzIter k f z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.DzIter k f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    _ ≤ (Work.Spaces.DzIter k f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hone
    _ = (Work.Spaces.DzIter k f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := heq.symm
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := hkey

/-! ## The relative-window Agmon bound -/

/-- **The window bound for the radial iterates.**  For `z > 0`, `θ ∈ (0,π/2)` and every `i`,

  `(D_z^i g z θ)² ≤ (2/z)·w(2z)^{-2}·(∫_z^{2z}(D_z^i g s θ)²w(s)²ds
      + ∫_z^{2z}(D_z^{i+1} g s θ)²w(s)²ds)`.

Route: `tvAverageLe` on `[z,2z]` for `U(s) = (D_z^i g s θ)²` gives
`U z ≤ (1/z)∫_{z}^{2z}U + ∫_{z}^{2z}|U'|`; `∂_z(D_z^i g)(s,θ) = D_z^{i+1}g s θ / s`, AM–GM
`2|XY|/s ≤ (X²+Y²)/z` (as `s ≥ z > 0`), and the monotonicity of `w` on the window. -/
private theorem windowBoundDzIter_local {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (i : ℕ) :
    (Work.Spaces.DzIter i g z θ) ^ 2
      ≤ (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ *
        ((∫ s in z..(2 * z), (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
          + (∫ s in z..(2 * z), (Work.Spaces.DzIter (i + 1) g s θ) ^ 2
              * (Work.Spaces.w s) ^ 2)) := by
  have hz2 : z < 2 * z := by linarith
  have hz2' : z ≤ 2 * z := hz2.le
  have hsub : Set.Icc z (2 * z) ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le hz hs.1
  have hcontD : ContinuousOn (fun s => Work.Spaces.DzIter i g s θ) (Set.Icc z (2 * z)) :=
    ((hO.DzIter i).curry_z hθ).continuousOn.mono hsub
  have hcontD1 : ContinuousOn (fun s => Work.Spaces.DzIter (i + 1) g s θ) (Set.Icc z (2 * z)) :=
    ((hO.DzIter (i + 1)).curry_z hθ).continuousOn.mono hsub
  have hcontW : ContinuousOn (fun s : ℝ => (Work.Spaces.w s) ^ 2) (Set.Icc z (2 * z)) := by
    have h1 : ContinuousOn (fun s : ℝ => Work.Spaces.w s) (Set.Icc z (2 * z)) := by
      simp only [Work.Spaces.w]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) (fun s hs => ?_)
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hs.1))
    exact h1.pow 2
  have hUderiv : ∀ x ∈ Set.Icc z (2 * z),
      HasDerivAt (fun s => (Work.Spaces.DzIter i g s θ) ^ 2)
        (2 * Work.Spaces.DzIter i g x θ * Work.Spaces.pz (Work.Spaces.DzIter i g) x θ) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
    have hd : HasDerivAt (fun s => Work.Spaces.DzIter i g s θ)
        (Work.Spaces.pz (Work.Spaces.DzIter i g) x θ) x :=
      Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice_DzIter hO i hθ hxpos
    have h2 := hd.pow 2
    have hval : (↑(2 : ℕ) : ℝ) * Work.Spaces.DzIter i g x θ ^ (2 - 1)
        * Work.Spaces.pz (Work.Spaces.DzIter i g) x θ
        = 2 * Work.Spaces.DzIter i g x θ * Work.Spaces.pz (Work.Spaces.DzIter i g) x θ := by
      norm_num
    rw [hval] at h2
    exact h2
  have hcontU : ContinuousOn (fun s => (Work.Spaces.DzIter i g s θ) ^ 2) (Set.Icc z (2 * z)) :=
    hcontD.pow 2
  have hcontU' : ContinuousOn
      (fun s => 2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ)
      (Set.Icc z (2 * z)) := by
    have hP : ContinuousOn (fun s => Work.Spaces.pz (Work.Spaces.DzIter i g) s θ)
        (Set.Icc z (2 * z)) :=
      (((hO.DzIter i).pz).curry_z hθ).continuousOn.mono hsub
    exact (continuousOn_const.mul hcontD).mul hP
  have hIntU : IntervalIntegrable (fun s => (Work.Spaces.DzIter i g s θ) ^ 2) volume z (2 * z) :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hz2']; exact hcontU)
  have hIntU' : IntervalIntegrable
      (fun s => 2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ)
      volume z (2 * z) :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hz2']; exact hcontU')
  have htv := Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux.tvAverageLe hz2 le_rfl hz2'
    hUderiv hIntU' hIntU
  rw [show (2 : ℝ) * z - z = z by ring] at htv
  have hW : 0 < Work.Spaces.w (2 * z) := Work.FTS.TransportS.w_pos_of_pos (by linarith)
  have hW2 : 0 < (Work.Spaces.w (2 * z)) ^ 2 := by positivity
  set A : ℝ := ∫ s in z..(2 * z), (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
    with hAdef
  set B : ℝ := ∫ s in z..(2 * z), (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
    with hBdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact intervalIntegral.integral_nonneg hz2' fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact intervalIntegral.integral_nonneg hz2' fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- the mean-value term
  have hA : (∫ s in z..(2 * z), (Work.Spaces.DzIter i g s θ) ^ 2)
      ≤ ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * A := by
    rw [hAdef, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hz2' hIntU ?_ ?_
    · exact ContinuousOn.intervalIntegrable (by
        rw [Set.uIcc_of_le hz2']; exact continuousOn_const.mul (hcontU.mul hcontW))
    · intro s hs
      have hspos : 0 < s := lt_of_lt_of_le hz hs.1
      have hle : Work.Spaces.w (2 * z) ≤ Work.Spaces.w s := w_antitone hspos (by linarith [hs.2])
      have hsq : (Work.Spaces.w (2 * z)) ^ 2 ≤ (Work.Spaces.w s) ^ 2 :=
        pow_le_pow_left₀ hW.le hle 2
      rw [inv_mul_eq_div, le_div_iff₀ hW2]
      exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  -- the total-variation term
  have hfint : IntervalIntegrable
      (fun s => (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2) volume z (2 * z) :=
    ContinuousOn.intervalIntegrable (by
      rw [Set.uIcc_of_le hz2']; exact hcontU.mul hcontW)
  have hgint : IntervalIntegrable
      (fun s => (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
      volume z (2 * z) :=
    ContinuousOn.intervalIntegrable (by
      rw [Set.uIcc_of_le hz2']; exact hcontD1.pow 2 |>.mul hcontW)
  have hB' : (∫ s in z..(2 * z),
        |2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ|)
      ≤ ∫ s in z..(2 * z), ((1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹)
          * ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            + (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2) := by
    refine intervalIntegral.integral_mono_on hz2' hIntU'.abs ?_ ?_
    · exact ContinuousOn.intervalIntegrable (by
        rw [Set.uIcc_of_le hz2']
        exact continuousOn_const.mul ((hcontU.mul hcontW).add (hcontD1.pow 2 |>.mul hcontW)))
    · intro s hs
      have hspos : 0 < s := lt_of_lt_of_le hz hs.1
      have hle : Work.Spaces.w (2 * z) ≤ Work.Spaces.w s := w_antitone hspos (by linarith [hs.2])
      have hsq : (Work.Spaces.w (2 * z)) ^ 2 ≤ (Work.Spaces.w s) ^ 2 :=
        pow_le_pow_left₀ hW.le hle 2
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter i g) s θ
          = Work.Spaces.DzIter (i + 1) g s θ / s := by
        have h1 : Work.Spaces.DzIter (i + 1) g s θ
            = s * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ := rfl
        rw [h1, mul_comm s, mul_div_cancel_right₀ _ (ne_of_gt hspos)]
      have hkey : |2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ|
          ≤ (|Work.Spaces.DzIter i g s θ| ^ 2
            + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2) / z := by
        rw [le_div_iff₀ hz, hpz]
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hspos,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have h2 : 2 * (|Work.Spaces.DzIter i g s θ| * |Work.Spaces.DzIter (i + 1) g s θ|)
            ≤ |Work.Spaces.DzIter i g s θ| ^ 2 + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2 := by
          nlinarith [sq_nonneg (|Work.Spaces.DzIter i g s θ|
            - |Work.Spaces.DzIter (i + 1) g s θ|)]
        have hzs : z / s ≤ 1 := (div_le_one hspos).mpr hs.1
        calc 2 * |Work.Spaces.DzIter i g s θ|
              * (|Work.Spaces.DzIter (i + 1) g s θ| / s) * z
            = 2 * (|Work.Spaces.DzIter i g s θ| * |Work.Spaces.DzIter (i + 1) g s θ|)
              * (z / s) := by ring
          _ ≤ (|Work.Spaces.DzIter i g s θ| ^ 2
                + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2) * 1 :=
              mul_le_mul h2 hzs (by positivity) (by positivity)
          _ = |Work.Spaces.DzIter i g s θ| ^ 2
                + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2 := by ring
      have hinv : 1 ≤ (Work.Spaces.w s) ^ 2 * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hW2, one_mul]
        exact hsq
      have hX : (Work.Spaces.DzIter i g s θ) ^ 2
          ≤ (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by
        calc (Work.Spaces.DzIter i g s θ) ^ 2 = (Work.Spaces.DzIter i g s θ) ^ 2 * 1 := by ring
          _ ≤ (Work.Spaces.DzIter i g s θ) ^ 2
              * ((Work.Spaces.w s) ^ 2 * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
          _ = (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
              * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by ring
      have hY : (Work.Spaces.DzIter (i + 1) g s θ) ^ 2
          ≤ (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by
        calc (Work.Spaces.DzIter (i + 1) g s θ) ^ 2
            = (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * 1 := by ring
          _ ≤ (Work.Spaces.DzIter (i + 1) g s θ) ^ 2
              * ((Work.Spaces.w s) ^ 2 * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
          _ = (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
              * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by ring
      have hfin : |Work.Spaces.DzIter i g s θ| ^ 2 + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2
          ≤ ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
              + (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
            * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by
        rw [sq_abs, sq_abs, add_mul]
        linarith [hX, hY]
      calc |2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ|
          ≤ (|Work.Spaces.DzIter i g s θ| ^ 2
              + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2) / z := hkey
        _ ≤ (((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
                + (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
              * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹) / z :=
            div_le_div_of_nonneg_right hfin hz.le
        _ = (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹
              * ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
                + (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2) := by
            ring
  have hB : (∫ s in z..(2 * z),
        |2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ|)
      ≤ (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (A + B) := by
    refine hB'.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hfint hgint,
      ← hAdef, ← hBdef]
  have hcnn : (0 : ℝ) ≤ (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by positivity
  have hmain : (Work.Spaces.DzIter i g z θ) ^ 2
      ≤ (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (A + B) := by
    calc (Work.Spaces.DzIter i g z θ) ^ 2
        ≤ (1 / z) * (∫ s in z..(2 * z), (Work.Spaces.DzIter i g s θ) ^ 2)
            + ∫ s in z..(2 * z),
                |2 * Work.Spaces.DzIter i g s θ
                  * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ| := htv
      _ ≤ (1 / z) * (((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * A)
            + (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (A + B) :=
          add_le_add (mul_le_mul_of_nonneg_left hA (by positivity)) hB
      _ = (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (2 * A + B) := by ring
      _ ≤ (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (2 * A + 2 * B) :=
          mul_le_mul_of_nonneg_left (by linarith) hcnn
      _ = (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (A + B) := by ring
  rw [hAdef, hBdef] at hmain
  exact hmain

/-! ## The a.e. pointwise slice bound -/

/-- **The a.e. slice bound.**  For a.e. angle (namely whenever the angular slice of
`HkIntegrand α 4 g` is integrable in `z`) the square of the pure slot `D_z^i g z θ` is
dominated by the *slice* `∫_s HkIntegrand α 4 g s θ ds`, for `i ≤ 3`. -/
private theorem ae_dzIter_sq_le_sliceIntegral {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hInt : MeasureTheory.IntegrableOn
      (fun s => Work.Spaces.HkIntegrand α 4 g s θ) Work.Spaces.Iz)
    (i : ℕ) (hi : i ≤ 3) :
    (Work.Spaces.DzIter i g z θ) ^ 2
      ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ := by
  have hz2' : z ≤ 2 * z := by linarith
  have hwin := windowBoundDzIter_local hO hz hθ i
  have hCnn : 0 ≤ (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by
    have := Work.FTS.TransportS.w_pos_of_pos (by linarith : (0 : ℝ) < 2 * z)
    positivity
  have hChalf : 2 * ((2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹) ≤ 1 := two_mul_coef_le_one hz
  have hJnn : 0 ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ :=
    integral_nonneg fun s => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
  have hinterval : ∀ k ≤ 4,
      (∫ s in z..(2 * z), (Work.Spaces.DzIter k g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ := by
    intro k hk
    rw [intervalIntegral.integral_of_le hz2']
    calc (∫ s in Set.Ioc z (2 * z), (Work.Spaces.DzIter k g s θ) ^ 2
            * (Work.Spaces.w s) ^ 2)
        ≤ ∫ s in Set.Ioc z (2 * z), Work.Spaces.HkIntegrand α 4 g s θ := by
          refine integral_mono_of_nonneg
            (Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_ ?_
          · exact hInt.mono_set (fun s hs => le_of_lt (lt_trans hz hs.1))
          · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
            have h := dzSlot_sq_le_HkIntegrand (α := α) (f := g) hk hθ.1 hθ.2 (z := s)
            rwa [mul_pow] at h
      _ ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ :=
          setIntegral_mono_set hInt
            (Eventually.of_forall fun s => Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
            (Eventually.of_forall fun s hs => le_of_lt (lt_trans hz hs.1))
  have h1 := hinterval i (by omega)
  have h2 := hinterval (i + 1) (by omega)
  calc (Work.Spaces.DzIter i g z θ) ^ 2
      ≤ (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ *
          ((∫ s in z..(2 * z), (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
            + (∫ s in z..(2 * z), (Work.Spaces.DzIter (i + 1) g s θ) ^ 2
                * (Work.Spaces.w s) ^ 2)) := hwin
    _ ≤ (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹
          * (2 * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ) := by
        refine mul_le_mul_of_nonneg_left ?_ hCnn
        linarith
    _ = (2 * ((2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹))
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ) := by ring
    _ ≤ 1 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ) :=
        mul_le_mul_of_nonneg_right hChalf hJnn
    _ = ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ := one_mul _

/-! ## The target -/

theorem Qang_sq_le_const_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {i : ℕ} (hi : i ≤ 3) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Qang g i z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
  have hCS := Work.FTS.OpenPkg.QangOpen.Qang_sq_leQ_open α g hO hmem i (by omega) hz
  obtain ⟨hswap, hIntHkθ, hAeIntHk⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 (hO.forall 4) hmem
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => ⟨h0, h1⟩)
  have hkey : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.DzIter i g z θ) ^ 2
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ := by
    filter_upwards [hAeIntHk, haeθ] with θ hInt hθ
    exact ae_dzIter_sq_le_sliceIntegral hO hz hθ hInt i hi
  have hθint : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
      ≤ Work.Spaces.HkSq α 4 g := by
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ,
            ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ :=
          integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hIntHkθ hkey
      _ = Work.Spaces.HkSq α 4 g := hswap
  calc (Work.Elliptic.Qang g i z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2) := hCS
    _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g :=
        mul_le_mul_of_nonneg_left hθint (integral_nonneg fun θ => sq_nonneg _)

end Work.FTS.StrongEps.E4R3
