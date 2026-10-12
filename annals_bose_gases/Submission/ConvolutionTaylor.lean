import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import ChallengeDeps
import Submission.KernelIds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5, brick B4 — the convolution approximation lemma (lem:Convolution)

FS `final_v2.tex` Lemma `lem:Convolution` (line ~845): for `f ∈ L¹(ℝ³)` even
with `supp f ⊆ ball 0 R`, writing `χΛ := χ(·/ℓ)` and
`(f⋆χΛ)(x) := ∫_y f(y)·χ((x−y)/ℓ) dy`, we have for every `x`:

    |(f⋆χΛ)(x) − χΛ(x)·∫f| ≤ C·(R/ℓ)²·∫|f|

(their constant `max‖∂ᵢ∂ⱼχ‖∞`; ours is an existential `C` from the
second-order Taylor bound of the smooth compactly-supported `χ`).

## Why this module exists

The estimate is used repeatedly in the FS box analysis (e.g.
`lem:QDecompSimpler` estimating `χΛ·(W₁⋆χΛ)`-type terms against
`(∫W₁)·χΛ²` with error `C(R/ℓ)²n₊`), always *for even kernels* `f`
(`g`, `gω`, `W₁`, ... are even because `v` and `ω` are radial).  It is
purely a second-order Taylor statement about `χ`, with the linear term
killed by evenness of `f`.
-/

noncomputable section

open MeasureTheory
open intervalIntegral
open scoped ContDiff Topology Real Convolution NNReal

namespace Submission.BoseGases

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

-- ======================================================================
-- 0. helpers used in both proofs
-- ======================================================================

/-- `fderiv χ` is `C^∞`. -/
private lemma convTaylor_fderiv_contDiff : ContDiff ℝ ∞ (fun z : ℝ³ => fderiv ℝ chi z) := by
  exact (contDiff_infty_iff_fderiv.mp chi_contDiff).2

/-- `fderiv χ` has compact support. -/
private lemma convTaylor_fderiv_hasCompactSupport :
    HasCompactSupport (fun z : ℝ³ => fderiv ℝ chi z) := by
  simpa using (chi_hasCompactSupport.fderiv ℝ)

/-- `fderiv χ` is Lipschitz on all of `ℝ³`. -/
private lemma convTaylor_fderiv_lipschitz :
    ∃ C : ℝ≥0, LipschitzWith C (fun z : ℝ³ => fderiv ℝ chi z) := by
  exact ContDiff.lipschitzWith_of_hasCompactSupport convTaylor_fderiv_hasCompactSupport
    convTaylor_fderiv_contDiff (by norm_num)

/-- `χ` is `C¹` at every point of the segment `[u, u − v]`. -/
private lemma convTaylor_chi_contDiffAt (u v : ℝ³) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (↑(0 : ℕ) + 1) chi (u + t • (-v)) := by
  intro t ht
  apply ContDiffAt.of_le (n := ∞) (m := (↑(0 : ℕ) + 1 : ℕ∞ω))
  · exact chi_contDiff.contDiffAt
  · exact (WithTop.coe_le_coe.mpr le_top : ((↑(0 : ℕ) + 1 : ℕ∞ω) : ℕ∞ω) ≤ (∞ : ℕ∞ω))

/-- FTC along a segment: `χ(u−v) − χu = ∫₀¹ (fderiv ℝ χ (u + t·(−v)))(−v) dt`. -/
private lemma convTaylor_ftc (u v : ℝ³) :
    chi (u - v) - chi u = (∫ t in (0 : ℝ)..1, (fderiv ℝ chi (u + t • (-v))) (-v)) := by
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (f := chi) (x := u) (y := -v) (n := 0)
    (convTaylor_chi_contDiffAt u v)
  have hmain : chi (u - v) = chi u +
      (∫ t in (0 : ℝ)..1, (fderiv ℝ chi (u + t • (-v))) (-v)) := by
    change chi (u + -v) = chi u + (∫ t in (0 : ℝ)..1, (fderiv ℝ chi (u + t • (-v))) (-v))
    rw [hT]
    simp
  rw [sub_eq_iff_eq_add]
  rw [add_comm]
  exact hmain

/-- Continuity in `t` of the FTC integrand. -/
private lemma convTaylor_continuous_A_apply (u v : ℝ³) :
    Continuous (fun t : ℝ => (fderiv ℝ chi (u + t • (-v))) (-v)) := by
  have hcontF : Continuous (fun z : ℝ³ => fderiv ℝ chi z) := convTaylor_fderiv_contDiff.continuous
  have hcontP : Continuous (fun t : ℝ => u + t • (-v)) := by fun_prop
  have hcont : Continuous (fun t : ℝ => fderiv ℝ chi (u + t • (-v))) := hcontF.comp hcontP
  exact hcont.clm_apply (continuous_const : Continuous (fun _ : ℝ => (-v : ℝ³)))

/-- Interval-integrability of the FTC integrand. -/
private lemma convTaylor_integrable_A_apply (u v : ℝ³) :
    IntervalIntegrable (fun t : ℝ => (fderiv ℝ chi (u + t • (-v))) (-v)) volume (0 : ℝ) 1 := by
  exact (convTaylor_continuous_A_apply u v).intervalIntegrable (0 : ℝ) 1

/-- The Taylor remainder is the integral of the derivative increment:
`χ(u−v) − χu + (fderiv χ u)v = ∫₀¹ (fderiv χ(u+t(−v)) − fderiv χ u)(−v) dt`. -/
private lemma convTaylor_hsplit (u v : ℝ³) :
    chi (u - v) - chi u + (fderiv ℝ chi u) v =
      (∫ t in (0 : ℝ)..1, (fderiv ℝ chi (u + t • (-v)) - fderiv ℝ chi u) (-v)) := by
  have hpt : ∀ t : ℝ, (fderiv ℝ chi (u + t • (-v)) - fderiv ℝ chi u) (-v)
      = (fderiv ℝ chi (u + t • (-v))) (-v) - (fderiv ℝ chi u) (-v) := by
    intro t
    rfl
  have hc : (∫ t in (0 : ℝ)..1, (fderiv ℝ chi u) v) = (fderiv ℝ chi u) v := by
    rw [intervalIntegral.integral_const]
    simp
  have hBint : IntervalIntegrable (fun t : ℝ => (fderiv ℝ chi u) v) volume (0 : ℝ) 1 := by
    exact intervalIntegrable_const
  have hpair : (∫ t in (0 : ℝ)..1, (fderiv ℝ chi (u + t • (-v)) - fderiv ℝ chi u) (-v))
      = (∫ t in (0 : ℝ)..1, (fderiv ℝ chi (u + t • (-v))) (-v)) + (fderiv ℝ chi u) v := by
    calc
      (∫ t in (0 : ℝ)..1, (fderiv ℝ chi (u + t • (-v)) - fderiv ℝ chi u) (-v))
          = ∫ t in (0 : ℝ)..1, ((fderiv ℝ chi (u + t • (-v))) (-v) + (fderiv ℝ chi u) v) := by
              apply intervalIntegral.integral_congr
              intro t ht
              change (fderiv ℝ chi (u + t • (-v)) - fderiv ℝ chi u) (-v)
                  = (fderiv ℝ chi (u + t • (-v))) (-v) + (fderiv ℝ chi u) v
              rw [hpt t]
              simp [map_neg]
      _ = (∫ t in (0 : ℝ)..1, (fderiv ℝ chi (u + t • (-v))) (-v)) +
            (∫ t in (0 : ℝ)..1, (fderiv ℝ chi u) v) := by
              rw [integral_add (convTaylor_integrable_A_apply u v) hBint]
      _ = (∫ t in (0 : ℝ)..1, (fderiv ℝ chi (u + t • (-v))) (-v)) + (fderiv ℝ chi u) v := by
              rw [hc]
  rw [convTaylor_ftc u v]
  exact hpair.symm

/-- The second-order remainder estimate from the Lipschitz constant of `fderiv χ`. -/
private lemma convTaylor_remainder_bound (L : ℝ≥0)
    (hLip : LipschitzWith L (fun z : ℝ³ => fderiv ℝ chi z)) (u v : ℝ³) :
    |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ (L : ℝ) * ‖v‖ ^ 2 := by
  have hnorm : ∀ a b : ℝ³, ‖fderiv ℝ chi a - fderiv ℝ chi b‖ ≤ (L : ℝ) * ‖a - b‖ := by
    intro a b
    have hd := (lipschitzWith_iff_dist_le_mul.mp hLip) a b
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd
  rw [convTaylor_hsplit u v]
  rw [← Real.norm_eq_abs]
  have hb : ∀ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 →
      ‖(fderiv ℝ chi (u + t • (-v)) - fderiv ℝ chi u) (-v)‖ ≤ (L : ℝ) * ‖v‖ ^ 2 := by
    intro t ht
    calc
      ‖(fderiv ℝ chi (u + t • (-v)) - fderiv ℝ chi u) (-v)‖
          ≤ ‖fderiv ℝ chi (u + t • (-v)) - fderiv ℝ chi u‖ * ‖v‖ := by
              have hle := ContinuousLinearMap.le_opNorm
                (f := (fderiv ℝ chi (u + t • (-v)) - fderiv ℝ chi u)) (-v)
              simpa using hle
      _ ≤ (L : ℝ) * ‖(u + t • (-v)) - u‖ * ‖v‖ := by
              gcongr
              exact hnorm (u + t • (-v)) u
      _ ≤ (L : ℝ) * ‖v‖ ^ 2 := by
              have htsub : ‖(u + t • (-v)) - u‖ = ‖t • (-v)‖ := by simp
              rw [htsub]
              have ht01 : |t| ≤ 1 := by
                have htI : t ∈ Set.Ioc (0 : ℝ) 1 := by
                  simpa using ht
                rw [abs_of_nonneg (le_of_lt htI.1)]
                exact htI.2
              rw [norm_smul, Real.norm_eq_abs]
              calc
                (L : ℝ) * (|t| * ‖-v‖) * ‖v‖ = (L : ℝ) * (|t| * ‖v‖) * ‖v‖ := by
                        rw [norm_neg]
                _ ≤ (L : ℝ) * (1 * ‖v‖) * ‖v‖ := by
                        gcongr
                _ = (L : ℝ) * ‖v‖ ^ 2 := by
                        rw [one_mul, pow_two]
                        ring
  have hineq : ‖(∫ t in (0 : ℝ)..1, (fderiv ℝ chi (u + t • (-v)) - fderiv ℝ chi u) (-v))‖
      ≤ (L : ℝ) * ‖v‖ ^ 2 * |(1 : ℝ) - 0| := by
    exact norm_integral_le_of_norm_le_const hb
  simpa using hineq

-- ======================================================================
-- 1. helpers for the convolution estimate (even kernels)
-- ======================================================================

/-- `Cχ ≥ 0` follows from the Taylor hypothesis at a nonzero vector. -/
private lemma convTaylor_Cχ_nonneg {Cχ : ℝ}
    (hT : ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ Cχ * ‖v‖ ^ 2) :
    0 ≤ Cχ := by
  rcases exists_ne (0 : ℝ³) with ⟨v0, hv0⟩
  have hsqpos : 0 < ‖v0‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv0) 2
  have hmul : 0 ≤ Cχ * ‖v0‖ ^ 2 := le_trans (abs_nonneg _) (hT 0 v0)
  have hcq : Cχ = (Cχ * ‖v0‖ ^ 2) / ‖v0‖ ^ 2 := by
    field_simp [ne_of_gt hsqpos]
  rw [hcq]
  exact div_nonneg hmul (le_of_lt hsqpos)

/-- An even integrand times a linear functional of `c • y` integrates to zero. -/
private lemma convTaylor_even_linear {f : ℝ³ → ℝ}
    (hfeven : ∀ x : ℝ³, f (-x) = f x) (L : ℝ³ →L[ℝ] ℝ) (c : ℝ) :
    (∫ y : ℝ³, f y * (L (c • y))) = 0 := by
  let H : ℝ³ → ℝ := fun y => f y * (L (c • y))
  have h1 : (∫ y : ℝ³, H (-y)) = ∫ y : ℝ³, H y := integral_comp_neg (g := H)
  have hpt : ∀ y : ℝ³, H (-y) = -H y := by
    intro y
    dsimp [H]
    rw [hfeven y, smul_neg, map_neg]
    ring
  have h2 : (∫ y : ℝ³, H (-y)) = ∫ y : ℝ³, -H y := by
    apply MeasureTheory.integral_congr_ae
    exact ae_of_all _ (by intro y; simp [hpt])
  have hmain : (∫ y : ℝ³, H y) = -(∫ y : ℝ³, H y) := by
    calc
      (∫ y : ℝ³, H y) = ∫ y : ℝ³, H (-y) := h1.symm
      _ = ∫ y : ℝ³, -H y := h2
      _ = -(∫ y : ℝ³, H y) := MeasureTheory.integral_neg (fun y : ℝ³ => H y)
  linarith

/-- `‖(ℓ⁻¹)•y‖ ≤ R/ℓ` when `‖y‖ ≤ R`. -/
private lemma convTaylor_norm_inv_smul_le_div {y : ℝ³} {R ℓ : ℝ} (hℓ : 0 < ℓ)
    (hR : 0 ≤ R) (hy : ‖y‖ ≤ R) : ‖(ℓ⁻¹) • y‖ ≤ R / ℓ := by
  have hℓi : 0 ≤ ℓ⁻¹ := le_of_lt (inv_pos.mpr hℓ)
  have hns : ‖(ℓ⁻¹) • y‖ = (ℓ⁻¹) * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hℓi]
  calc
    ‖(ℓ⁻¹) • y‖ = (ℓ⁻¹) * ‖y‖ := hns
    _ ≤ (ℓ⁻¹) * R := mul_le_mul_of_nonneg_left hy hℓi
    _ = R / ℓ := by rw [div_eq_mul_inv]; ring

/-- squared version: `‖(ℓ⁻¹)•y‖² ≤ (R/ℓ)²` when `‖y‖ ≤ R`. -/
private lemma convTaylor_norm_inv_smul_sq_le_div {y : ℝ³} {R ℓ : ℝ} (hℓ : 0 < ℓ)
    (hR : 0 ≤ R) (hy : ‖y‖ ≤ R) : ‖(ℓ⁻¹) • y‖ ^ 2 ≤ (R / ℓ) ^ 2 := by
  have hle := convTaylor_norm_inv_smul_le_div (y := y) hℓ hR hy
  have hnn1 : 0 ≤ ‖(ℓ⁻¹) • y‖ := norm_nonneg _
  exact pow_le_pow_left₀ hnn1 hle 2

/-- Pointwise bound of the (remainder) integrand `f·(Taylor remainder)` on the
support of `f`: `|f y · R(y)| ≤ (Cχ(R/ℓ)²)·|f y|`. -/
private lemma convTaylor_pointwise_bound {f : ℝ³ → ℝ} {ℓ R Cχ : ℝ} (hℓ : 0 < ℓ)
    (hR : 0 ≤ R) (hT : ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ Cχ * ‖v‖ ^ 2)
    (hfsupp : ∀ x : ℝ³, R ≤ ‖x‖ → f x = 0) (hC : 0 ≤ Cχ) (u y : ℝ³) :
    |f y * (chi (u - (ℓ⁻¹) • y) - chi u + (fderiv ℝ chi u) ((ℓ⁻¹) • y))|
      ≤ (Cχ * (R / ℓ) ^ 2) * |f y| := by
  by_cases hfy : f y = 0
  · simp [hfy]
  · have hRy : ¬ R ≤ ‖y‖ := by
      intro hRy
      exact hfy (hfsupp y hRy)
    have hyR : ‖y‖ ≤ R := le_of_lt (lt_of_not_ge hRy)
    have hsq := convTaylor_norm_inv_smul_sq_le_div (y := y) hℓ hR hyR
    have hTay := hT u ((ℓ⁻¹) • y)
    have hc1 : Cχ * ‖(ℓ⁻¹) • y‖ ^ 2 ≤ Cχ * (R / ℓ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hC
    calc
      |f y * (chi (u - (ℓ⁻¹) • y) - chi u + (fderiv ℝ chi u) ((ℓ⁻¹) • y))|
          = |f y| * |chi (u - (ℓ⁻¹) • y) - chi u + (fderiv ℝ chi u) ((ℓ⁻¹) • y)| := by rw [abs_mul]
      _ ≤ |f y| * (Cχ * ‖(ℓ⁻¹) • y‖ ^ 2) := mul_le_mul_of_nonneg_left hTay (abs_nonneg (f y))
      _ ≤ |f y| * (Cχ * (R / ℓ) ^ 2) := mul_le_mul_of_nonneg_left hc1 (abs_nonneg (f y))
      _ = (Cχ * (R / ℓ) ^ 2) * |f y| := by ring

-- ======================================================================
-- 2. the second-order Taylor bound (hT)
-- ======================================================================

/-- Second-order Taylor remainder bound for the smooth compactly-supported
bump `χ`: `∃ C ≥ 0, ∀ u v : ℝ³, |χ(u−v) − χ(u) + (fderiv ℝ χ u) v| ≤ C‖v‖²`. -/
theorem chi_second_order_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ³,
      |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ C * ‖v‖ ^ 2 := by
  rcases convTaylor_fderiv_lipschitz with ⟨L, hLip⟩
  refine ⟨(L : ℝ), L.2, ?_⟩
  exact convTaylor_remainder_bound L hLip

-- ======================================================================
-- 3. the convolution approximation lemma
-- ======================================================================

/-- **lem:Convolution** of the FS paper: for an even integrable `f` supported
inside `ball 0 R` and `0 < ℓ`, the sliding convolution
`∫_y f(y)·χ((x−y)/ℓ) dy` differs from `χ(x/ℓ)·∫f` by at most
`Cχ·(R/ℓ)²·∫|f|`, uniformly in `x`. -/
theorem convolution_approx {f : ℝ³ → ℝ} {ℓ R Cχ : ℝ} (hℓ : 0 < ℓ)
    (hT : ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ Cχ * ‖v‖ ^ 2)
    (hfint : MeasureTheory.Integrable f)
    (hfeven : ∀ x : ℝ³, f (-x) = f x)
    (hfsupp : ∀ x : ℝ³, R ≤ ‖x‖ → f x = 0) (hR : 0 ≤ R) :
    ∀ x : ℝ³,
      |∫ y : ℝ³, f y * (chiScale ℓ (x - y) - chiScale ℓ x)| ≤
        Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |f y|) := by
  have hC : 0 ≤ Cχ := convTaylor_Cχ_nonneg hT
  have hfabs : Integrable (fun y : ℝ³ => |f y|) := by
    exact hfint.abs
  intro x
  let u : ℝ³ := (ℓ⁻¹) • x
  let L : ℝ³ →L[ℝ] ℝ := fderiv ℝ chi u
  let c : ℝ := Cχ * (R / ℓ) ^ 2
  -- rewrite chiScale in terms of chi
  have hAy : ∀ y : ℝ³, chiScale ℓ (x - y) - chiScale ℓ x = chi (u - (ℓ⁻¹) • y) - chi u := by
    intro y
    dsimp [chiScale, u]
    rw [smul_sub]
  -- linear term vanishes (evenness)
  have hlin : (∫ y : ℝ³, f y * (L ((ℓ⁻¹) • y))) = 0 := by
    exact convTaylor_even_linear hfeven L (ℓ⁻¹)
  -- integrability of the dominating function
  have hdom_int : Integrable (fun y : ℝ³ => c * |f y|) := by
    exact hfabs.const_mul c
  -- integrability of the remainder integrand and of its absolute value
  have hR0cont : Continuous (fun y : ℝ³ => chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y)) := by
    have hc1 : Continuous (fun y : ℝ³ => chi (u - (ℓ⁻¹) • y)) := by
      refine chi_contDiff.continuous.comp ?_
      fun_prop
    have hc2 : Continuous (fun y : ℝ³ => L ((ℓ⁻¹) • y)) := by
      exact L.continuous.comp ((ℓ⁻¹) • (ContinuousLinearMap.id ℝ ℝ³)).continuous
    exact hc1.sub continuous_const |>.add hc2
  have hfae : AEStronglyMeasurable f volume := hfint.aestronglyMeasurable
  have hbR : ∀ y : ℝ³,
      |f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))| ≤ c * |f y| := by
    intro y
    have hb := convTaylor_pointwise_bound (y := y) (u := u) hℓ hR hT hfsupp hC
    simpa [L, c] using hb
  have hbodyR_ae : AEStronglyMeasurable
      (fun y : ℝ³ => f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))) volume := by
    exact hfae.mul hR0cont.aestronglyMeasurable
  have hbodyR_bd : ∀ᵐ y ∂volume,
      ‖f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))‖ ≤ c * |f y| := by
    exact ae_of_all _ (by intro y; simpa [Real.norm_eq_abs] using hbR y)
  have hbodyR_int : Integrable
      (fun y : ℝ³ => f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))) := by
    exact Integrable.mono' hdom_int hbodyR_ae hbodyR_bd
  have hbodyR_abs_ae : AEStronglyMeasurable
      (fun y : ℝ³ => |f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))|) volume := by
    exact hbodyR_ae.norm
  have hbodyR_abs_bd : ∀ᵐ y ∂volume,
      ‖|f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))|‖ ≤ c * |f y| := by
    exact ae_of_all _ (by intro y; simpa [Real.norm_eq_abs] using hbR y)
  have hbodyR_abs_int : Integrable
      (fun y : ℝ³ => |f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))|) := by
    exact Integrable.mono' hdom_int hbodyR_abs_ae hbodyR_abs_bd
  have hbodyR_abs_le : (fun y : ℝ³ =>
        |f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))|) ≤ᵐ[volume]
      (fun y : ℝ³ => c * |f y|) := by
    exact ae_of_all _ hbR
  -- integrability of the linear term
  have hLcont : Continuous (fun y : ℝ³ => L ((ℓ⁻¹) • y)) := by
    exact L.continuous.comp ((ℓ⁻¹) • (ContinuousLinearMap.id ℝ ℝ³)).continuous
  have hbodyL_ae : AEStronglyMeasurable (fun y : ℝ³ => f y * (L ((ℓ⁻¹) • y))) volume := by
    exact hfae.mul hLcont.aestronglyMeasurable
  have hbodyL_bd : ∀ᵐ y ∂volume,
      ‖f y * (L ((ℓ⁻¹) • y))‖ ≤ (‖L‖ * (R / ℓ)) * |f y| := by
    apply ae_of_all
    intro y
    by_cases hfy : f y = 0
    · simp [hfy]
    · have hRy : ¬ R ≤ ‖y‖ := by
        intro hRy
        exact hfy (hfsupp y hRy)
      have hyR : ‖y‖ ≤ R := le_of_lt (lt_of_not_ge hRy)
      have hv := convTaylor_norm_inv_smul_le_div (y := y) hℓ hR hyR
      calc
        ‖f y * (L ((ℓ⁻¹) • y))‖ = |f y * (L ((ℓ⁻¹) • y))| := by rw [Real.norm_eq_abs]
        _ = |f y| * |L ((ℓ⁻¹) • y)| := by rw [abs_mul]
        _ ≤ |f y| * (‖L‖ * ‖(ℓ⁻¹) • y‖) := by
              have hl := L.le_opNorm ((ℓ⁻¹) • y)
              have hl' : |L ((ℓ⁻¹) • y)| ≤ ‖L‖ * ‖(ℓ⁻¹) • y‖ := by
                simpa [Real.norm_eq_abs] using hl
              exact mul_le_mul_of_nonneg_left hl' (abs_nonneg (f y))
        _ ≤ |f y| * (‖L‖ * (R / ℓ)) := by
              have hnnL : 0 ≤ ‖L‖ := norm_nonneg _
              have hmm : ‖L‖ * ‖(ℓ⁻¹) • y‖ ≤ ‖L‖ * (R / ℓ) :=
                mul_le_mul_of_nonneg_left hv hnnL
              exact mul_le_mul_of_nonneg_left hmm (abs_nonneg (f y))
        _ = (‖L‖ * (R / ℓ)) * |f y| := by ring
  have hdomL_int : Integrable (fun y : ℝ³ => (‖L‖ * (R / ℓ)) * |f y|) := by
    exact hfabs.const_mul (‖L‖ * (R / ℓ))
  have hbodyL_int : Integrable (fun y : ℝ³ => f y * (L ((ℓ⁻¹) • y))) := by
    exact Integrable.mono' hdomL_int hbodyL_ae hbodyL_bd
  -- pointwise A = R − Lv
  have hptA : ∀ y : ℝ³, f y * (chiScale ℓ (x - y) - chiScale ℓ x)
      = (f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))) - f y * (L ((ℓ⁻¹) • y)) := by
    intro y
    rw [hAy y]
    ring
  -- ∫(f·A) = ∫(f·R) since the linear term integrates to zero
  have hsub : (∫ y : ℝ³, f y * (chiScale ℓ (x - y) - chiScale ℓ x))
      = ∫ y : ℝ³, f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y)) := by
    calc
      (∫ y : ℝ³, f y * (chiScale ℓ (x - y) - chiScale ℓ x))
          = ∫ y : ℝ³, (f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))) - f y * (L ((ℓ⁻¹) • y)) := by
              apply MeasureTheory.integral_congr_ae
              exact ae_of_all _ (by intro y; simpa [hptA])
      _ = (∫ y : ℝ³, f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))) -
            (∫ y : ℝ³, f y * (L ((ℓ⁻¹) • y))) := by
              rw [MeasureTheory.integral_sub hbodyR_int hbodyL_int]
      _ = ∫ y : ℝ³, f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y)) := by
              rw [hlin]
              ring
  -- main estimate
  have hmain : |∫ y : ℝ³, f y * (chiScale ℓ (x - y) - chiScale ℓ x)| ≤ c * (∫ y : ℝ³, |f y|) := by
    calc
      |∫ y : ℝ³, f y * (chiScale ℓ (x - y) - chiScale ℓ x)|
          = |∫ y : ℝ³, f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))| := by rw [hsub]
      _ ≤ ∫ y : ℝ³, |f y * (chi (u - (ℓ⁻¹) • y) - chi u + L ((ℓ⁻¹) • y))| := by
              exact MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ y : ℝ³, c * |f y| := by
              exact MeasureTheory.integral_mono_ae hbodyR_abs_int hdom_int hbodyR_abs_le
      _ = c * (∫ y : ℝ³, |f y|) := by
              rw [MeasureTheory.integral_const_mul c (fun y : ℝ³ => |f y|)]
  -- conclude with c = Cχ·(R/ℓ)²
  simpa [c] using hmain

end BoseGases

end Submission
