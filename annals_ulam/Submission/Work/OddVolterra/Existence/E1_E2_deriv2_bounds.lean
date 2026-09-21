import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.E1_E2_diff_bounds
import Submission.Work.OddVolterra.Existence.E1_E2_model
import Submission.Work.OddVolterra.Existence.exists_bound_comp_pair_sub_param
import Submission.Work.OddVolterra.Existence.IteratedDerivSection
import Submission.Work.OddVolterra.Existence.xi_close_of_small
import Submission.Work.OddVolterra.Existence.E1_deriv_bounds

/-!
# Second `v`-derivative bounds for the odd inhomogeneities `E₁`, `E₂`

This file proves
`Work.OddVolterra.Existence.E1_E2_deriv2_bounds`: on the slope window
`[c, 1 - τ]` (`τ = 1/10`) the second derivative of the differences
`E₁ n h - E₁ n 0` and `E₂ n h - E₂ n 0` is bounded by `C δ`, whenever the
perturbation `h` is `C^∞` with all derivatives up to order `n + 3` bounded by
`δ ≤ 1/100`.

## Route

`E₁ n h v = ∫_t ∂^{n+1}_u (u ↦ mPhiF n (u, h u, t)) v` (`mE1_eq`), and on a
neighbourhood of the window the composite `u ↦ mPhiF n (u, h u, t)` agrees with
the composite of the *globally* smooth clamped model `PhiC n` of
`Existence/E1_deriv_bounds.lean` (the model radicand exceeds the clamp threshold
`radEta = 1/100` on the box, by `radEta_le_mRad`).  For the clamped family the
parametric integral can be differentiated under the integral sign at every order
(`iteratedDeriv_integral_fixed`), so the `j`-th derivative of `E₁ n h - E₁ n 0`
is the `t`-integral of the difference of the two order-`(j+n+1)` composites, which
`exists_bound_comp_pair_sub_param` bounds by `C δ`.  The `E₂` half is the same
argument for the clamped model of `mPhiB` composed with the graph, using the
Leibniz rule for the factor `t + deriv h u`.
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Commons.Geometry.Ulam
open Work.OddVolterra.DiffBounds

/-! ## Helper lemmas -/

/-- `iteratedDeriv 2 f = deriv (deriv f)`. -/
private lemma iDeriv2_eq_deriv_deriv (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- On the box the clamped `E₁` model agrees with the true graph composite near every
slope in the window; hence `E₁ n h` is the parametric integral of the clamped composite. -/
private lemma E1_eq_integral_PhiParam_of_abs (n : ℕ) {h : ℝ → ℝ}
    (hb : ∀ u : ℝ, |h u| ≤ 1 / 100) {u : ℝ} (hu : |u| < 91 / 100) :
    Work.OddVolterra.E1 n h u
      = ∫ t in (-(profileX 1))..(profileX 1), PhiParam n h (n + 1) (u, t) := by
  rw [mE1_eq n h u]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have ht' : |t| ≤ profileX 1 := by
    rw [Set.uIcc_of_le (by linarith [profileX_one_pos'])] at ht
    rw [abs_le]
    exact ⟨by linarith [ht.1], ht.2⟩
  have hrho : 0 < (91 / 100 - |u|) / 2 := by linarith
  have hev : (fun x : ℝ => mPhiF n (x, h x, t)) =ᶠ[𝓝 u]
      (fun x : ℝ => PhiC n (x, h x, t)) := by
    filter_upwards [Metric.ball_mem_nhds u hrho] with x hx
    have hxabs : |x| ≤ 91 / 100 := by
      rw [Metric.mem_ball, Real.dist_eq] at hx
      have h3 := abs_sub_abs_le_abs_sub x u
      linarith [abs_nonneg x, hx]
    exact (PhiC_eq_mPhiF (radEta_le_mRad hxabs (hb x) ht')).symm
  have h1 : iteratedDeriv (n + 1) (fun x : ℝ => mPhiF n (x, h x, t)) u
      = iteratedDeriv (n + 1) (fun x : ℝ => PhiC n (x, h x, t)) u :=
    (hev.iteratedDeriv (n + 1)).eq_of_nhds
  rw [h1]
  exact iteratedDeriv_eq_PhiParam n h (n + 1) u t

/-- **The `E₁` half**: the second derivative of `E₁ n h - E₁ n 0` is `C δ`-small on the
window `[c, 1 - τ]`. -/
lemma E1_deriv2_bound (n : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - Work.OddVolterra.tau) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ v ∈ Set.Icc c (1 - Work.OddVolterra.tau),
        |deriv (deriv (fun w : ℝ => Work.OddVolterra.E1 n h w - Work.OddVolterra.E1 n 0 w)) v|
          ≤ C * δ := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ := exists_bound_comp_pair_sub_param (i := n + 3) (Φ := PhiC n)
    (c := c) (d := 1 - tau) (R := 1 / 100) (p := profileX 1) (U := Set.univ)
    isOpen_univ (Set.subset_univ _) (contDiff_PhiC n).contDiffOn hc1 (by norm_num)
    (le_of_lt profileX_one_pos')
  have hp : (0 : ℝ) < profileX 1 := profileX_one_pos'
  refine ⟨C₁ * (2 * profileX 1) + 1, by positivity, ?_⟩
  intro h δ hh hδpos hδ100 hjet v hv
  have hv9 : v ≤ 9 / 10 := by simpa [Work.OddVolterra.DiffBounds.one_sub_tau_eq] using hv.2
  have hδnn : 0 ≤ δ := le_of_lt hδpos
  have hδ1 : δ ≤ 1 := by linarith
  have hhd : ∀ u : ℝ, |h u| ≤ 1 / 100 := fun u => le_trans (hjet 0 (by omega) u) hδ100
  have h0cd : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ → ℝ) := contDiff_const
  have hvabs : |v| < 91 / 100 := by
    rw [abs_of_pos (lt_of_lt_of_le hc hv.1)]
    linarith
  have htransfer : (fun w : ℝ => Work.OddVolterra.E1 n h w - Work.OddVolterra.E1 n 0 w)
      =ᶠ[𝓝 v] (fun u : ℝ => ∫ t in (-(profileX 1))..(profileX 1),
        (PhiParam n h (n + 1) (u, t) - PhiParam n 0 (n + 1) (u, t))) := by
    have hrho : 0 < (91 / 100 - |v|) / 2 := by linarith
    filter_upwards [Metric.ball_mem_nhds v hrho] with u hu
    have huabs : |u| < 91 / 100 := by
      rw [Metric.mem_ball, Real.dist_eq] at hu
      have h3 := abs_sub_abs_le_abs_sub u v
      linarith [abs_nonneg u, hu]
    have h1 := E1_eq_integral_PhiParam_of_abs n hhd huabs
    have h2 := E1_eq_integral_PhiParam_of_abs n (h := 0) (fun u => by simp) huabs
    rw [h1, h2, ← intervalIntegral.integral_sub (intervalIntegrable_PhiParam n hh (n + 1) u)
      (intervalIntegrable_PhiParam n h0cd (n + 1) u)]
  have hD : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      PhiParam n h (n + 1) (p.1, p.2) - PhiParam n 0 (n + 1) (p.1, p.2)) :=
    (contDiff_PhiParam n hh (n + 1)).sub (contDiff_PhiParam n h0cd (n + 1))
  have hswap := iteratedDeriv_integral_fixed (j := 2)
    (F := fun u t : ℝ => PhiParam n h (n + 1) (u, t) - PhiParam n 0 (n + 1) (u, t))
    (a := -(profileX 1)) (b := profileX 1) (x := v) hD
  have hidx : 2 + (n + 1) = n + 3 := by omega
  have hcongr : (fun t : ℝ => iteratedDeriv 2
        (fun u : ℝ => PhiParam n h (n + 1) (u, t) - PhiParam n 0 (n + 1) (u, t)) v)
      = fun t : ℝ => PhiParam n h (n + 3) (v, t) - PhiParam n 0 (n + 3) (v, t) := by
    funext t
    have hpd := iteratedDeriv_PhiParamDiff n hh (n + 1) 2 t v
    have he : (fun u : ℝ => PhiParam n h (n + 1) (u, t) - PhiParam n 0 (n + 1) (u, t))
        = fun u : ℝ => PhiParamDiff n h (n + 1) (u, t) := rfl
    rw [he, hpd, hidx]
  have hbd : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      |PhiParam n h (n + 3) (v, t) - PhiParam n 0 (n + 3) (v, t)| ≤ C₁ * δ := by
    intro t ht
    exact hC₁ h δ hδnn hδ1 hδ100 hh (fun j hj u _ => hjet j hj u) v hv t ht
  have hab : -(profileX 1) ≤ profileX 1 := by linarith
  rw [← iDeriv2_eq_deriv_deriv]
  have hmain : iteratedDeriv 2
        (fun w : ℝ => Work.OddVolterra.E1 n h w - Work.OddVolterra.E1 n 0 w) v
      = ∫ t in (-(profileX 1))..(profileX 1),
          (PhiParam n h (n + 3) (v, t) - PhiParam n 0 (n + 3) (v, t)) := by
    rw [(htransfer.iteratedDeriv 2).eq_of_nhds, hswap, hcongr]
  rw [hmain]
  have hInt : IntervalIntegrable (fun t : ℝ =>
      |PhiParam n h (n + 3) (v, t) - PhiParam n 0 (n + 3) (v, t)|) volume
      (-(profileX 1)) (profileX 1) :=
    ((intervalIntegrable_PhiParam n hh (n + 3) v).sub
      (intervalIntegrable_PhiParam n h0cd (n + 3) v)).abs
  calc |∫ t in (-(profileX 1))..(profileX 1),
          (PhiParam n h (n + 3) (v, t) - PhiParam n 0 (n + 3) (v, t))|
      ≤ ∫ t in (-(profileX 1))..(profileX 1),
          |PhiParam n h (n + 3) (v, t) - PhiParam n 0 (n + 3) (v, t)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in (-(profileX 1))..(profileX 1), C₁ * δ :=
        intervalIntegral.integral_mono_on hab hInt intervalIntegrable_const (fun t ht => hbd t ht)
    _ = C₁ * δ * (2 * profileX 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ (C₁ * (2 * profileX 1) + 1) * δ := by
        nlinarith [hC₁nn, hp, hδnn]


/-! ## The clamped `E₂` model and its parametrised families -/

/-- The clamped model of the `E₂` radicand factor (the exponent is `n - 1`). -/
def PhiBc (n : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  radClamp (mRad p.1 p.2.1 p.2.2) ^ (n - 1) * Real.sqrt (radClamp (mRad p.1 p.2.1 p.2.2))

lemma contDiff_PhiBc (n : ℕ) : ContDiff ℝ ∞ (PhiBc n) := by
  have hrad : ContDiff ℝ ∞ fun p : ℝ × ℝ × ℝ => radClamp (mRad p.1 p.2.1 p.2.2) :=
    contDiff_radClamp.comp mRad_contDiff
  exact (hrad.pow (n - 1)).mul (hrad.sqrt (fun p => ne_of_gt (radClamp_pos _)))

/-- Above the clamp threshold the clamped `E₂` model is the true model. -/
lemma PhiBc_eq_mPhiB {n : ℕ} {u y t : ℝ} (h : radEta ≤ mRad u y t) :
    PhiBc n (u, y, t) = mPhiB n (u, y, t) := by
  rw [PhiBc, mPhiB, radClamp_of_le h]

/-- The clamped `E₂` graph composite. -/
def BSlice (n : ℕ) (h : ℝ → ℝ) (t : ℝ) : ℝ → ℝ := fun u => PhiBc n (u, h u, t)

/-- The clamped `E₂` graph composite multiplied by the graph slope. -/
def BSliceLin (n : ℕ) (h : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun u => BSlice n h t u * (t + deriv h u)

/-- The parametrised `k`-th derivative of the clamped `E₂` graph composite. -/
def BParam (n : ℕ) (h : ℝ → ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun p => iteratedDeriv k (BSlice n h p.2) p.1

/-- The parametrised `k`-th derivative of the clamped `E₂` integrand. -/
def BParamLin (n : ℕ) (h : ℝ → ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun p => iteratedDeriv k (BSliceLin n h p.2) p.1

lemma BSliceLin_apply (n : ℕ) (h : ℝ → ℝ) (t u : ℝ) :
    BSliceLin n h t u = PhiBc n (u, h u, t) * (t + deriv h u) := rfl

lemma BParamLin_apply (n : ℕ) (h : ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ) :
    BParamLin n h k p = iteratedDeriv k (BSliceLin n h p.2) p.1 := rfl

/-- The uncurried clamped `E₂` integrand is smooth. -/
lemma contDiff_BSliceLin (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => BSliceLin n h p.2 p.1) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => PhiBc n (p.1, h p.1, p.2)) :=
    (contDiff_PhiBc n).comp (by fun_prop)
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2 + deriv h p.1) :=
    contDiff_snd.add ((DiffBounds.contDiff_deriv_of_contDiff hh).comp contDiff_fst)
  exact h1.mul h2

/-- The parametrised family of `k`-th derivatives of the clamped `E₂` integrand is smooth. -/
lemma contDiff_BParamLin (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (k : ℕ) :
    ContDiff ℝ ∞ (BParamLin n h k) :=
  Commons.Analysis.Calculus.contDiff_iteratedDeriv_param (E := ℝ) k (contDiff_BSliceLin n hh)

/-- Interval integrability of the clamped `E₂` integrand in the section parameter. -/
lemma intervalIntegrable_BParamLin (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (k : ℕ) (u : ℝ) :
    IntervalIntegrable (fun t : ℝ => BParamLin n h k (u, t)) volume
      (-(profileX 1)) (profileX 1) := by
  have hcont : Continuous fun t : ℝ => BParamLin n h k (u, t) :=
    (contDiff_BParamLin n hh k).continuous.comp (continuous_const.prodMk continuous_id)
  exact hcont.intervalIntegrable _ _

/-- `E₂ n h` is the parametric integral of the clamped `E₂` integrand near every slope
`u` with `|u| < 91/100`. -/
lemma E2_eq_integral_BParamLin_of_abs (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hb : ∀ u : ℝ, |h u| ≤ 1 / 100) {u : ℝ} (hu : |u| < 91 / 100) :
    Work.OddVolterra.E2 n h u
      = ∫ t in (-(profileX 1))..(profileX 1), BParamLin n h n (u, t) := by
  rw [mE2_eq n h u]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have ht' : |t| ≤ profileX 1 := by
    rw [Set.uIcc_of_le (by linarith [profileX_one_pos'])] at ht
    rw [abs_le]
    exact ⟨by linarith [ht.1], ht.2⟩
  have hrho : 0 < (91 / 100 - |u|) / 2 := by linarith
  have hev : (fun x : ℝ => mPhiB n (x, h x, t) * lineSlope h x t) =ᶠ[𝓝 u]
      (fun x : ℝ => PhiBc n (x, h x, t) * (t + deriv h x)) := by
    filter_upwards [Metric.ball_mem_nhds u hrho] with x hx
    have hxabs : |x| ≤ 91 / 100 := by
      rw [Metric.mem_ball, Real.dist_eq] at hx
      have h3 := abs_sub_abs_le_abs_sub x u
      linarith [abs_nonneg x, hx]
    rw [PhiBc_eq_mPhiB (radEta_le_mRad hxabs (hb x) ht')]
    rfl
  have h1 := (hev.iteratedDeriv n).eq_of_nhds
  rw [h1]
  rfl


/-! ## The model data: difference and ball-slice bounds for the clamped `E₂` composites -/

/-- `((j : ℕ) : ℕ∞ω) ≤ ⊤`. -/
private lemma natCast_le_top (j : ℕ) : ((j : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)

/-- For the clamped `E₂` model there are constants `C` (difference of the `k`-th composites of
`h` and `0`) and `M` (ball slices) valid on the box, uniformly in `h` and `δ`. -/
lemma E2_model_data (n : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau) :
    ∃ (C M : ℕ → ℝ), (∀ k, 0 ≤ C k) ∧ (∀ k, 0 ≤ M k) ∧
      (∀ k, ∀ (h : ℝ → ℝ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → δ ≤ 1 / 100 →
        ContDiff ℝ (⊤ : ℕ∞) h →
        (∀ j ≤ k, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv j h u| ≤ δ) →
        ∀ x ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
          |iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) x -
            iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) x| ≤ C k * δ) ∧
      (∀ k, ∀ v ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
          |iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) v| ≤ M k) := by
  have hexC : ∀ k, ∃ Ck : ℝ, 0 ≤ Ck ∧
      (∀ (h : ℝ → ℝ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → δ ≤ 1 / 100 →
        ContDiff ℝ (⊤ : ℕ∞) h →
        (∀ j ≤ k, ∀ u ∈ Set.Icc c (1 - tau), |iteratedDeriv j h u| ≤ δ) →
        ∀ x ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
          |iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) x -
            iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) x| ≤ Ck * δ) :=
    fun k => exists_bound_comp_pair_sub_param (i := k) (Φ := PhiBc n) (c := c) (d := 1 - tau)
      (R := 1 / 100) (p := profileX 1) (U := Set.univ) isOpen_univ (Set.subset_univ _)
      (contDiff_PhiBc n).contDiffOn hc1 (by norm_num) (le_of_lt profileX_one_pos')
  have hexM : ∀ k, ∃ Mk : ℝ, 0 ≤ Mk ∧
      (∀ v ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        |iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) v| ≤ Mk) := by
    intro k
    have hF : ContDiff ℝ ∞ (fun q : ℝ × ℝ => PhiBc n (q.2, 0, q.1)) :=
      (contDiff_PhiBc n).comp (by fun_prop)
    obtain ⟨M, hM⟩ := Work.OddVolterra.Smooth.parametric_iteratedDeriv_bound_smooth
      (F := fun t u : ℝ => PhiBc n (u, 0, t)) isOpen_univ hF.contDiffOn
      (isCompact_Icc.prod isCompact_Icc) (Set.subset_univ _) k
    exact ⟨max M 0, le_max_right _ _, fun v hv t ht =>
      le_trans (hM (t, v) ⟨ht, hv⟩) (le_max_left _ _)⟩
  exact ⟨fun k => Classical.choose (hexC k), fun k => Classical.choose (hexM k),
    fun k => (Classical.choose_spec (hexC k)).1, fun k => (Classical.choose_spec (hexM k)).1,
    fun k => (Classical.choose_spec (hexC k)).2, fun k => (Classical.choose_spec (hexM k)).2⟩

/-! ## The Leibniz bound at order `n + 2` -/

/-- Pointwise bound for the `(n+2)`-nd derivative of the difference of the two clamped `E₂`
integrands, obtained from the Leibniz rule for the factor `t + deriv h`. -/
lemma BSliceLin_iteratedDeriv_sub_bound (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {δ t v : ℝ} (hδnn : 0 ≤ δ) (hδ1 : δ ≤ 1) {C M : ℕ → ℝ}
    (hCnn : ∀ k ≤ n + 2, 0 ≤ C k) (hMnn : ∀ k ≤ n + 2, 0 ≤ M k)
    (hCb : ∀ k ≤ n + 2, |iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v -
        iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) v| ≤ C k * δ)
    (hMb : ∀ k ≤ n + 2, |iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) v| ≤ M k)
    (hjet : ∀ k : ℕ, k ≤ n + 3 → |iteratedDeriv k h v| ≤ δ) :
    |iteratedDeriv (n + 2) (BSliceLin n h t) v - iteratedDeriv (n + 2) (BSliceLin n 0 t) v|
      ≤ (|t| * C (n + 2)
          + ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ) * (C k + M k)) * δ := by
  have hAh : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => PhiBc n (u, h u, t)) v :=
    (contDiff_PhiBc n).contDiffAt.comp v (by fun_prop)
  have hA0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => PhiBc n (u, 0, t)) v :=
    (contDiff_PhiBc n).contDiffAt.comp v (by fun_prop)
  have hdh : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => deriv h u) v :=
    (DiffBounds.contDiff_deriv_of_contDiff hh).contDiffAt
  have hAhle : ContDiffAt ℝ (((n + 2 : ℕ) : ℕ∞ω)) (fun u : ℝ => PhiBc n (u, h u, t)) v :=
    hAh.of_le (natCast_le_top (n + 2))
  have hA0le : ContDiffAt ℝ (((n + 2 : ℕ) : ℕ∞ω)) (fun u : ℝ => PhiBc n (u, 0, t)) v :=
    hA0.of_le (natCast_le_top (n + 2))
  have hdhle : ContDiffAt ℝ (((n + 2 : ℕ) : ℕ∞ω)) (fun u : ℝ => deriv h u) v :=
    hdh.of_le (natCast_le_top (n + 2))
  have hsplith : BSliceLin n h t = fun u : ℝ => PhiBc n (u, h u, t) * (t + deriv h u) := by
    funext u; rfl
  have hsplit0 : BSliceLin n 0 t = fun u : ℝ => PhiBc n (u, 0, t) * t := by
    funext u
    have hz : deriv (0 : ℝ → ℝ) u = 0 := deriv_const u 0
    simp only [BSliceLin, BSlice, Pi.zero_apply, hz]
    ring
  have hlin : (fun u : ℝ => PhiBc n (u, h u, t) * (t + deriv h u))
      = (fun u : ℝ => PhiBc n (u, h u, t) * t)
        + (fun u : ℝ => PhiBc n (u, h u, t) * deriv h u) := by
    funext u; simp only [Pi.add_apply]; ring
  have hstep1 : iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, h u, t) * (t + deriv h u)) v
      = iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, h u, t) * t) v
        + iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, h u, t) * deriv h u) v := by
    rw [hlin]
    exact iteratedDeriv_add (hAhle.mul contDiffAt_const) (hAhle.mul hdhle)
  have hstep2 : iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, h u, t) * t) v
      = t * iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, h u, t)) v := by
    have h1 := iteratedDeriv_const_mul (𝔸 := ℝ) t hAhle
    rw [show (fun u : ℝ => PhiBc n (u, h u, t) * t)
        = fun u : ℝ => t * PhiBc n (u, h u, t) from by funext u; ring, h1]
  have hstep2' : iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, 0, t) * t) v
      = t * iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, 0, t)) v := by
    have h1 := iteratedDeriv_const_mul (𝔸 := ℝ) t hA0le
    rw [show (fun u : ℝ => PhiBc n (u, 0, t) * t)
        = fun u : ℝ => t * PhiBc n (u, 0, t) from by funext u; ring, h1]
  have hleib : iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, h u, t) * deriv h u) v
      = ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ)
          * iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v
          * iteratedDeriv (n + 2 - k) (fun u : ℝ => deriv h u) v := by
    have h1 : iteratedDeriv (n + 2)
        ((fun u : ℝ => PhiBc n (u, h u, t)) * (fun u : ℝ => deriv h u)) v
        = ∑ i ∈ Finset.range (n + 2 + 1), (((n + 2).choose i : ℕ) : ℝ)
            * iteratedDeriv i (fun u : ℝ => PhiBc n (u, h u, t)) v
            * iteratedDeriv (n + 2 - i) (fun u : ℝ => deriv h u) v :=
      iteratedDeriv_mul (𝔸 := ℝ) hAhle hdhle
    rw [show (fun u : ℝ => PhiBc n (u, h u, t) * deriv h u)
        = (fun u : ℝ => PhiBc n (u, h u, t)) * (fun u : ℝ => deriv h u) from by
          funext u; rfl,
      h1, show n + 2 + 1 = n + 3 from by omega]
  have hdiff : iteratedDeriv (n + 2) (BSliceLin n h t) v - iteratedDeriv (n + 2) (BSliceLin n 0 t) v
      = t * (iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, h u, t)) v
              - iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, 0, t)) v)
        + ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ)
            * iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v
            * iteratedDeriv (n + 2 - k) (fun u : ℝ => deriv h u) v := by
    rw [hsplith, hsplit0, hstep1, hstep2, hstep2', hleib]
    ring
  have hpiece1 : |t * (iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, h u, t)) v
        - iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, 0, t)) v)| ≤ |t| * (C (n + 2) * δ) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hCb (n + 2) le_rfl) (abs_nonneg t)
  have hpiece2 : |∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ)
        * iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v
        * iteratedDeriv (n + 2 - k) (fun u : ℝ => deriv h u) v|
      ≤ ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ) * (C k + M k) * δ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro k hk
    have hk2 : k ≤ n + 2 := by rw [Finset.mem_range] at hk; omega
    have hb1 : |iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v| ≤ C k + M k := by
      have h1 : |iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v|
          ≤ |iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v
              - iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) v|
            + |iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) v| := by
        have hadd := abs_add_le (iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v
            - iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) v)
          (iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) v)
        have h2 : (iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v
              - iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) v)
            + iteratedDeriv k (fun u : ℝ => PhiBc n (u, 0, t)) v
            = iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v := by ring
        rw [h2] at hadd
        exact hadd
      have h2 := hCb k hk2
      have h3 := hMb k hk2
      have h4 : C k * δ ≤ C k * 1 := mul_le_mul_of_nonneg_left hδ1 (hCnn k hk2)
      linarith
    have hb2 : |iteratedDeriv (n + 2 - k) (fun u : ℝ => deriv h u) v| ≤ δ := by
      have hs : iteratedDeriv (n + 2 - k + 1) h
          = iteratedDeriv (n + 2 - k) (fun u : ℝ => deriv h u) := iteratedDeriv_succ'
      rw [← hs]
      have hidx : n + 2 - k + 1 = n + 3 - k := by omega
      rw [hidx]
      exact hjet (n + 3 - k) (by omega)
    calc |(((n + 2).choose k : ℕ) : ℝ) * iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v
            * iteratedDeriv (n + 2 - k) (fun u : ℝ => deriv h u) v|
        = (((n + 2).choose k : ℕ) : ℝ)
            * |iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v|
            * |iteratedDeriv (n + 2 - k) (fun u : ℝ => deriv h u) v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      _ ≤ (((n + 2).choose k : ℕ) : ℝ) * (C k + M k) * δ := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hb1 (Nat.cast_nonneg _)) hb2
            (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hCnn k hk2) (hMnn k hk2)))
  calc |iteratedDeriv (n + 2) (BSliceLin n h t) v - iteratedDeriv (n + 2) (BSliceLin n 0 t) v|
      = |t * (iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, h u, t)) v
            - iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, 0, t)) v)
          + ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ)
              * iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v
              * iteratedDeriv (n + 2 - k) (fun u : ℝ => deriv h u) v| := by rw [hdiff]
    _ ≤ |t * (iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, h u, t)) v
            - iteratedDeriv (n + 2) (fun u : ℝ => PhiBc n (u, 0, t)) v)|
          + |∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ)
              * iteratedDeriv k (fun u : ℝ => PhiBc n (u, h u, t)) v
              * iteratedDeriv (n + 2 - k) (fun u : ℝ => deriv h u) v| := abs_add_le _ _
    _ ≤ |t| * (C (n + 2) * δ)
          + ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ) * (C k + M k) * δ :=
        add_le_add hpiece1 hpiece2
    _ = (|t| * C (n + 2)
          + ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ) * (C k + M k)) * δ := by
        rw [← Finset.sum_mul]
        ring


/-! ## The `E₂` half -/

/-- **The `E₂` half**: the second derivative of `E₂ n h - E₂ n 0` is `C δ`-small on the
window `[c, 1 - τ]`. -/
lemma E2_deriv2_bound (n : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1 - Work.OddVolterra.tau) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ v ∈ Set.Icc c (1 - Work.OddVolterra.tau),
        |deriv (deriv (fun w : ℝ => Work.OddVolterra.E2 n h w - Work.OddVolterra.E2 n 0 w)) v|
          ≤ C * δ := by
  obtain ⟨C, M, hCnn, hMnn, hCb, hMb⟩ := E2_model_data n hc hc1
  have hp : (0 : ℝ) < profileX 1 := profileX_one_pos'
  have hp2 : (0 : ℝ) ≤ 2 * profileX 1 := by linarith
  have hK0 : (0 : ℝ) ≤ profileX 1 * C (n + 2)
      + ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ) * (C k + M k) :=
    add_nonneg (mul_nonneg hp.le (hCnn (n + 2)))
      (Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (hCnn k) (hMnn k)))
  refine ⟨(profileX 1 * C (n + 2)
      + ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ) * (C k + M k)) * (2 * profileX 1)
      + 1, by positivity, ?_⟩
  intro h δ hh hδpos hδ100 hjet v hv
  have hδnn : 0 ≤ δ := le_of_lt hδpos
  have hδ1 : δ ≤ 1 := by linarith
  have hhd : ∀ u : ℝ, |h u| ≤ 1 / 100 := fun u => le_trans (hjet 0 (by omega) u) hδ100
  have h0cd : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ → ℝ) := contDiff_const
  have hv9 : v ≤ 9 / 10 := by simpa [Work.OddVolterra.DiffBounds.one_sub_tau_eq] using hv.2
  have hvabs : |v| < 91 / 100 := by
    rw [abs_of_pos (lt_of_lt_of_le hc hv.1)]
    linarith
  -- `E₂ n h - E₂ n 0` is, near `v`, the parametric integral of the difference of the clamped
  -- `E₂` integrands
  have htransfer : (fun w : ℝ => Work.OddVolterra.E2 n h w - Work.OddVolterra.E2 n 0 w)
      =ᶠ[𝓝 v] (fun u : ℝ => ∫ t in (-(profileX 1))..(profileX 1),
        (BParamLin n h n (u, t) - BParamLin n 0 n (u, t))) := by
    have hrho : 0 < (91 / 100 - |v|) / 2 := by linarith
    filter_upwards [Metric.ball_mem_nhds v hrho] with u hu
    have huabs : |u| < 91 / 100 := by
      rw [Metric.mem_ball, Real.dist_eq] at hu
      have h3 := abs_sub_abs_le_abs_sub u v
      linarith [abs_nonneg u, hu]
    have h1 := E2_eq_integral_BParamLin_of_abs n hh hhd huabs
    have h2 := E2_eq_integral_BParamLin_of_abs n (h := 0) contDiff_const (fun u => by simp) huabs
    rw [h1, h2, ← intervalIntegral.integral_sub (intervalIntegrable_BParamLin n hh n u)
      (intervalIntegrable_BParamLin n h0cd n u)]
  have hD : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      BParamLin n h n (p.1, p.2) - BParamLin n 0 n (p.1, p.2)) :=
    (contDiff_BParamLin n hh n).sub (contDiff_BParamLin n h0cd n)
  have hswap := iteratedDeriv_integral_fixed (j := 2)
    (F := fun u t : ℝ => BParamLin n h n (u, t) - BParamLin n 0 n (u, t))
    (a := -(profileX 1)) (b := profileX 1) (x := v) hD
  have hcongr : (fun t : ℝ => iteratedDeriv 2
        (fun u : ℝ => BParamLin n h n (u, t) - BParamLin n 0 n (u, t)) v)
      = fun t : ℝ => iteratedDeriv (n + 2) (BSliceLin n h t) v
          - iteratedDeriv (n + 2) (BSliceLin n 0 t) v := by
    funext t
    have hcdh : ContDiffAt ℝ (((2 : ℕ) : ℕ∞ω)) (fun u : ℝ => BParamLin n h n (u, t)) v :=
      (ContDiffAt.fun_comp v ((contDiff_BParamLin n hh n).contDiffAt)
        (by fun_prop : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => (u, t)) v)).of_le (natCast_le_top 2)
    have hcd0 : ContDiffAt ℝ (((2 : ℕ) : ℕ∞ω)) (fun u : ℝ => BParamLin n 0 n (u, t)) v :=
      (ContDiffAt.fun_comp v ((contDiff_BParamLin n h0cd n).contDiffAt)
        (by fun_prop : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => (u, t)) v)).of_le (natCast_le_top 2)
    have hsub := iteratedDeriv_sub
      (f := fun u : ℝ => BParamLin n h n (u, t)) (g := fun u : ℝ => BParamLin n 0 n (u, t))
      hcdh hcd0
    have hs1 : iteratedDeriv 2 (fun u : ℝ => BParamLin n h n (u, t)) v
        = iteratedDeriv (n + 2) (BSliceLin n h t) v := by
      have hiter := iteratedDeriv_iteratedDeriv 2 n (BSliceLin n h t)
      rw [show (fun u : ℝ => BParamLin n h n (u, t))
          = fun x : ℝ => iteratedDeriv n (BSliceLin n h t) x from rfl, hiter,
        show 2 + n = n + 2 from by omega]
    have hs0 : iteratedDeriv 2 (fun u : ℝ => BParamLin n 0 n (u, t)) v
        = iteratedDeriv (n + 2) (BSliceLin n 0 t) v := by
      have hiter := iteratedDeriv_iteratedDeriv 2 n (BSliceLin n 0 t)
      rw [show (fun u : ℝ => BParamLin n 0 n (u, t))
          = fun x : ℝ => iteratedDeriv n (BSliceLin n 0 t) x from rfl, hiter,
        show 2 + n = n + 2 from by omega]
    rw [show (fun u : ℝ => BParamLin n h n (u, t) - BParamLin n 0 n (u, t))
        = (fun u : ℝ => BParamLin n h n (u, t)) - (fun u : ℝ => BParamLin n 0 n (u, t))
        from rfl, hsub, hs1, hs0]
  have hbd : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      |iteratedDeriv (n + 2) (BSliceLin n h t) v - iteratedDeriv (n + 2) (BSliceLin n 0 t) v|
        ≤ (profileX 1 * C (n + 2)
            + ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ) * (C k + M k)) * δ := by
    intro t ht
    have htabs : |t| ≤ profileX 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have h1 := BSliceLin_iteratedDeriv_sub_bound n hh hδnn hδ1
      (fun k _ => hCnn k) (fun k _ => hMnn k)
      (fun k hk => hCb k h δ hδnn hδ1 hδ100 hh (fun j hj u _ => hjet j (by omega) u) v hv t ht)
      (fun k hk => hMb k v hv t ht)
      (fun k hk => hjet k hk v)
    refine le_trans h1 ?_
    refine mul_le_mul_of_nonneg_right ?_ hδnn
    have hle : |t| * C (n + 2) ≤ profileX 1 * C (n + 2) :=
      mul_le_mul_of_nonneg_right htabs (hCnn (n + 2))
    linarith
  have hab : -(profileX 1) ≤ profileX 1 := by linarith
  rw [← iDeriv2_eq_deriv_deriv]
  have hmain : iteratedDeriv 2
        (fun w : ℝ => Work.OddVolterra.E2 n h w - Work.OddVolterra.E2 n 0 w) v
      = ∫ t in (-(profileX 1))..(profileX 1),
          (iteratedDeriv (n + 2) (BSliceLin n h t) v
            - iteratedDeriv (n + 2) (BSliceLin n 0 t) v) := by
    rw [(htransfer.iteratedDeriv 2).eq_of_nhds, hswap, hcongr]
  rw [hmain]
  have hInt : IntervalIntegrable (fun t : ℝ =>
      |iteratedDeriv (n + 2) (BSliceLin n h t) v - iteratedDeriv (n + 2) (BSliceLin n 0 t) v|)
      volume (-(profileX 1)) (profileX 1) :=
    ((intervalIntegrable_BParamLin n hh (n + 2) v).sub
      (intervalIntegrable_BParamLin n h0cd (n + 2) v)).abs
  calc |∫ t in (-(profileX 1))..(profileX 1),
          (iteratedDeriv (n + 2) (BSliceLin n h t) v
            - iteratedDeriv (n + 2) (BSliceLin n 0 t) v)|
      ≤ ∫ t in (-(profileX 1))..(profileX 1),
          |iteratedDeriv (n + 2) (BSliceLin n h t) v - iteratedDeriv (n + 2) (BSliceLin n 0 t) v| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in (-(profileX 1))..(profileX 1),
          (profileX 1 * C (n + 2)
            + ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ) * (C k + M k)) * δ :=
        intervalIntegral.integral_mono_on hab hInt intervalIntegrable_const (fun t ht => hbd t ht)
    _ = ((profileX 1 * C (n + 2)
          + ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ) * (C k + M k)) * δ)
          * (2 * profileX 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ ((profileX 1 * C (n + 2)
          + ∑ k ∈ Finset.range (n + 3), (((n + 2).choose k : ℕ) : ℝ) * (C k + M k)) * (2 * profileX 1)
          + 1) * δ := by
        nlinarith [hK0, hp, hδnn]


theorem E1_E2_deriv2_bounds (n : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1 - Work.OddVolterra.tau) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      (∀ v ∈ Set.Icc c (1 - Work.OddVolterra.tau),
        |deriv (deriv (fun w : ℝ => Work.OddVolterra.E1 n h w - Work.OddVolterra.E1 n 0 w)) v| ≤ C * δ) ∧
      (∀ v ∈ Set.Icc c (1 - Work.OddVolterra.tau),
        |deriv (deriv (fun w : ℝ => Work.OddVolterra.E2 n h w - Work.OddVolterra.E2 n 0 w)) v| ≤ C * δ) := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ := E1_deriv2_bound n hc hc1
  obtain ⟨C₂, hC₂nn, hC₂⟩ := E2_deriv2_bound n hn hc hc1
  refine ⟨max C₁ C₂, le_trans hC₁nn (le_max_left _ _), fun h δ hh hδpos hδ100 hjet => ⟨?_, ?_⟩⟩
  · intro v hv
    exact le_trans (hC₁ h δ hh hδpos hδ100 hjet v hv)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hδpos.le)
  · intro v hv
    exact le_trans (hC₂ h δ hh hδpos hδ100 hjet v hv)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hδpos.le)

end

end Work.OddVolterra.Existence
