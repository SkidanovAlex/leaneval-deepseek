import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Honesty.lzero1_bdd_on_Ioo
import Submission.Work.FTS.PhiStar.Honesty.lzero1_pair_eFam_c2
import Submission.Work.FTS.PhiStar.Honesty.sq_integral_mul_cos_le
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_Lzero1_mul_cos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

/-- **The mode coefficient of a slice is bounded by the `L²(cos θ dθ)`-norm of its
`Lzero1`-image, divided by the eigenvalue.**

For a `C²` slice `θ ↦ F z θ` vanishing at both endpoints (so that the Dirichlet problem for the
angular operator `Lzero1` is the right one), the `e_m`-coefficient of the slice in the weight
`cos θ dθ` satisfies

  `|cmode m F z| ≤ ‖Lzero1 (F z ·)‖_{L²(cos)} / (lam m · ‖e_m‖_{L²(cos)})`.

**Proof.**  Write `v := F z ·`, `e := eFam m`, `Q := ∫_{Iθ} (Lzero1 v)² cos`,
`D := ∫_{Iθ} e² cos`, `A := ∫_{Iθ} v e cos`.  By definition `cmode m F z = A / D`, and `D > 0`
is the explicit value `FamNormValue`.  Self-adjointness of `Lzero1` in the weight `cos θ dθ`
(the pairing identity `Work.FTS.PhiStar.Honesty.lzero1_pair_eFam_c2`, proved from the Wronskian
primitive `-v' e cos θ` whose endpoint values vanish thanks to `v 0 = v (π/2) = 0` and
`eFam m 0 = 0`, `cos (π/2) = 0`) gives `∫_{Iθ} (Lzero1 v) e cos = lam m · A`, and Cauchy–Schwarz
for the weight `cos θ ≥ 0` (the lemma `Work.FTS.PhiStar.Honesty.sq_integral_mul_cos_le`) turns
that into `(lam m · A)² ≤ Q · D`.  Taking square roots and dividing by `lam m · D = lam m · √D · √D`
yields the claim.  The endpoint regularity needed to make the integrals honest is supplied by
`lzero1_bdd_on_Ioo` and `integrableOn_Lzero1_mul_cos`: `Lzero1 v` blows up at `π/2` if `v` does
not vanish there, but for our slices the two singular pieces cancel. -/
theorem abs_cmode_le_lzero {F : ℝ → ℝ → ℝ} {m : ℕ} (hm : 1 ≤ m) {z : ℝ}
    (hC2 : ContDiffOn ℝ 2 (fun θ : ℝ => F z θ) (Set.Icc 0 (Real.pi / 2)))
    (h0 : F z 0 = 0) (h1 : F z (Real.pi / 2) = 0) :
    |Work.FTS.PhiStar.Series.cmode m F z|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.Lzero1 (fun θ : ℝ => F z θ) θ) ^ 2 * Real.cos θ)
          / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                  (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  set v : ℝ → ℝ := fun θ : ℝ => F z θ with hv
  have hvC2 : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)) := hC2
  have hv0 : v 0 = 0 := h0
  have hv1 : v (Real.pi / 2) = 0 := h1
  -- the four abbreviations
  set Q : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.Lzero1 v θ) ^ 2 * Real.cos θ with hQdef
  set D : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ with hDdef
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
      v θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ with hAdef
  set P : ℝ := ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 v θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Real.cos θ with hPdef
  -- boundedness of `Lzero1 v` and integrability of the two integrands
  obtain ⟨M, hM⟩ := Work.FTS.PhiStar.Honesty.lzero1_bdd_on_Ioo hvC2 hv0 hv1
  obtain ⟨hIq, hIp⟩ :=
    Work.FTS.PhiStar.Honesty.integrableOn_Lzero1_mul_cos (m := m) hvC2 ⟨M, hM⟩
  -- the pairing identity
  have hpair : P = Work.FTS.PhiStar.Gegenbauer.lam m * A :=
    Work.FTS.PhiStar.Honesty.lzero1_pair_eFam_c2 v m hvC2 hv0 hv1 ⟨M, hM⟩
  -- positivity of the eigenvalue
  have hlam : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    simp only [Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith
  -- the denominator is the explicit `FamNormValue`, hence positive
  have heFam_eq : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ := by
    rw [intervalIntegral.integral_of_le hpi,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    simp only [Work.Spaces.Iθ]
  have hDpos : 0 < D := by
    rw [hDdef, ← heFam_eq, Work.FTS.PhiStar.Gegenbauer.FamNormValue m]
    positivity
  -- nonnegativity of `Q`
  have hQnn : 0 ≤ Q := by
    rw [hQdef]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- integrability of the mode square
  have hcont_e : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
    rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
        = fun θ : ℝ => Real.cos θ
            * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) from rfl]
    exact Real.continuous_cos.mul
      ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
        Real.continuous_sin)
  have hIe : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      Work.Spaces.Iθ :=
    (((hcont_e.pow 2).mul Real.continuous_cos).continuousOn).integrableOn_Icc
  -- Cauchy–Schwarz
  have hCS : P ^ 2 ≤ Q * D :=
    Work.FTS.PhiStar.Honesty.sq_integral_mul_cos_le
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 v θ)
      (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) hIq hIe hIp
  -- the elementary algebra
  have hmain : |A / D| ≤ Real.sqrt Q
      / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt D) := by
    have hsqrtD : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
    have h1 : |P| ≤ Real.sqrt Q * Real.sqrt D := by
      have h2 : Real.sqrt (P ^ 2) ≤ Real.sqrt (Q * D) := Real.sqrt_le_sqrt hCS
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_mul hQnn] at h2
    have h3 : Work.FTS.PhiStar.Gegenbauer.lam m * |A|
        ≤ Real.sqrt Q * Real.sqrt D := by
      rwa [hpair, abs_mul, abs_of_pos hlam] at h1
    have h4 : |A| ≤ Real.sqrt Q * Real.sqrt D
        / Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [le_div_iff₀ hlam]
      linarith [h3]
    calc |A / D| = |A| / D := by rw [abs_div, abs_of_pos hDpos]
      _ ≤ (Real.sqrt Q * Real.sqrt D / Work.FTS.PhiStar.Gegenbauer.lam m) / D :=
          div_le_div_of_nonneg_right h4 hDpos.le
      _ = Real.sqrt Q / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt D) := by
          rw [div_div, div_eq_div_iff
            (mul_ne_zero (ne_of_gt hlam) (ne_of_gt hDpos))
            (mul_ne_zero (ne_of_gt hlam) (ne_of_gt hsqrtD))]
          linear_combination (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt Q)
            * Real.sq_sqrt hDpos.le
  -- `cmode m F z = A / D`
  have hcm : Work.FTS.PhiStar.Series.cmode m F z = A / D := by
    rw [hAdef, hDdef, Work.FTS.PhiStar.Series.cmode]
    have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
          F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ,
            v θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
      rw [intervalIntegral.integral_of_le hpi,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      simp only [Work.Spaces.Iθ, hv]
    have hden : (∫ θ in (0 : ℝ)..(Real.pi / 2),
          (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ,
            (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ := by
      rw [intervalIntegral.integral_of_le hpi,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      simp only [Work.Spaces.Iθ]
    rw [hnum, hden]
  rw [hcm]
  simpa only [hQdef, hDdef, hv] using hmain

end Work.FTS.PhiStar.Honesty
