import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.OneBodyKin.SymAPI
import Submission.Work.OneBodyKin.exists_fsKinCoeff_mul_abs_profHat_le
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_mul_abs_profHat
import Submission.Work.OneBodyKin.profHat_add_sub_linear_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.symD_second_order` — the cross symbol `symD` is flat at the origin

At scale `ℓ = 1` the second symbol term of the projected moving-box family form is

    `symD 1 F ρ = ∫_p F(‖p‖) · profHat p · profHat (ρ − p) dp`.

This file proves that for the FS cut-off `F = fsKinCoeff C = [·−C]₊²` the difference
`symD 1 F ρ − symD 1 F 0` is `O(‖ρ‖²)` **with a constant that can be made arbitrarily small by
enlarging the cut-off `C`**:

    `∀ ε > 0, ∃ C > 0, ∃ R > 0, ∀ ‖ρ‖ ≤ R, |symD 1 (fsKinCoeff C) ρ − symD 1 (fsKinCoeff C) 0|
        ≤ ε ‖ρ‖²`.

## The mechanism

Write `f = profHat`, the cosine transform of the bump `χ` (even, continuous, `|f| ≤ ∫|χ|`,
`f(p) = O(‖p‖^{-6})`), and `F_C(p) = [‖p‖−C]₊²`.  Then

    `W(ρ) := symD 1 F_C ρ − symD 1 F_C 0 = ∫_p F_C(p) f(p) (f(ρ−p) − f(p)) dp`.

Three ingredients:

1. **Two-term expansion of `f`.**  Differentiating `f = ∫_z χ z cos⟪·,z⟫ dz` under the integral
   sign,
   `f(y+d) − f(y) = −∫_z χ z ⟪d,z⟫ sin⟪y,z⟫ dz + R(y,d)`,  `|R(y,d)| ≤ M₂ ‖d‖²`,
   with the second moment `M₂ = ∫_z |χ z| ‖z‖² dz` of the bump (`profHat_add_sub_linear_le`).
2. **Parity.**  Substituting `p ↦ −p` and using that `f` is even, `W(ρ)` is also the integral of
   `F_C(p) f(p) (f(ρ+p) − f(p))`; averaging the two, the linear parts
   `±∫χ z⟪ρ,z⟫sin⟪p,z⟫ dz` cancel **pointwise** and only the two quadratic remainders survive:
   `2W(ρ) = ∫_p F_C(p) f(p) [(f(ρ−p) − f(p)) + (f(ρ+p) − f(p))] dp`, so
   `|W(ρ)| ≤ M₂ ‖ρ‖² ∫_p F_C(p) |f(p)| dp` for **every** `ρ`.
3. **The tail of the cut-off.**  `F_C(p) ≤ ‖p‖²` vanishes pointwise as `C → ∞` and is dominated
   by `‖p‖² |f(p)| ≤ const (1+‖p‖)^{-4} ∈ L¹`, so `∫_p F_C(p)|f(p)| dp → 0`
   (`exists_fsKinCoeff_mul_abs_profHat_le`).  Choosing `C` with `M₂ ∫_p F_C(p)|f(p)| dp ≤ ε`
   finishes; `R = 1` works.

Both constants are explicit and the estimate is global in `ρ`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## The two analytic inputs (proved in sibling modules)

* `profHat_add_sub_linear_le` : the two-term expansion of `profHat`;
* `exists_fsKinCoeff_mul_abs_profHat_le` : the cut-off tail `∫ ‖p‖² |profHat|` can be made
  arbitrarily small;
* `integrable_fsKinCoeff_mul_abs_profHat` : the cut-off weight `[‖p‖−C]₊² |profHat p|` is `L¹`. -/

/-! ## The linear part of the expansion of `profHat`, and the parity cancellation -/

/-- The linear part of the expansion of `profHat` at `y` in the direction `d`. -/
private noncomputable def linPart (y d : ℝ³) : ℝ :=
  ∫ z : ℝ³, chi z * (inner ℝ d z) * Real.sin (inner ℝ y z)

private lemma linPart_neg (y d : ℝ³) : linPart y (-d) = -linPart y d := by
  unfold linPart
  rw [show (∫ z : ℝ³, chi z * (inner ℝ (-d) z) * Real.sin (inner ℝ y z))
      = ∫ z : ℝ³, -(chi z * (inner ℝ d z) * Real.sin (inner ℝ y z)) from
    integral_congr_ae (Filter.Eventually.of_forall (fun z => by
      simp only [inner_neg_left]; ring))]
  rw [integral_neg]

private theorem aux_lin (y d : ℝ³) :
    |profHat (y + d) - profHat y + linPart y d| ≤ (∫ z : ℝ³, |chi z| * ‖z‖ ^ 2) * ‖d‖ ^ 2 :=
  profHat_add_sub_linear_le y d

/-- **The parity cancellation of the two linear parts.**  The sum
`(f(ρ−p) − f(p)) + (f(ρ+p) − f(p))` has no linear term left: expanding both differences around `p`
the linear parts are `linPart p ρ` and `−linPart p ρ` (the second because the expansion at `p` in
the direction `p − ρ` has `linPart p (-(ρ-p)) = -linPart p (ρ-p)`, and `ρ - p` plays the role of
the direction), leaving the two quadratic remainders, so the sum is `O(‖ρ‖²)` with constant
`2 M₂`. -/
private lemma rem_bound (p ρ : ℝ³) :
    |(profHat (ρ - p) - profHat p) + (profHat (ρ + p) - profHat p)|
      ≤ 2 * (∫ z : ℝ³, |chi z| * ‖z‖ ^ 2) * ‖ρ‖ ^ 2 := by
  set M : ℝ := ∫ z : ℝ³, |chi z| * ‖z‖ ^ 2 with hM
  have h1 : |profHat (p - ρ) - profHat p - linPart p ρ| ≤ M * ‖ρ‖ ^ 2 := by
    have h : |profHat (p + -ρ) - profHat p + -linPart p ρ| ≤ M * ‖ρ‖ ^ 2 := by
      have h := aux_lin p (-ρ)
      rw [linPart_neg, norm_neg, ← hM] at h
      exact h
    simpa only [sub_eq_add_neg] using h
  have h2 : |profHat (p + ρ) - profHat p + linPart p ρ| ≤ M * ‖ρ‖ ^ 2 := by
    have h := aux_lin p ρ
    rw [← hM] at h
    exact h
  have hev : profHat (ρ - p) = profHat (p - ρ) := by
    rw [show (ρ - p) = -(p - ρ) by abel, profHat_even]
  have hkey : (profHat (ρ - p) - profHat p) + (profHat (ρ + p) - profHat p)
      = (profHat (p - ρ) - profHat p - linPart p ρ)
        + (profHat (p + ρ) - profHat p + linPart p ρ) := by
    rw [hev, show ρ + p = p + ρ by abel]
    ring
  rw [hkey]
  calc |(profHat (p - ρ) - profHat p - linPart p ρ)
        + (profHat (p + ρ) - profHat p + linPart p ρ)|
      ≤ |profHat (p - ρ) - profHat p - linPart p ρ|
        + |profHat (p + ρ) - profHat p + linPart p ρ| := abs_add_le _ _
    _ ≤ M * ‖ρ‖ ^ 2 + M * ‖ρ‖ ^ 2 := add_le_add h1 h2
    _ = 2 * (∫ z : ℝ³, |chi z| * ‖z‖ ^ 2) * ‖ρ‖ ^ 2 := by rw [hM]; ring

/-! ## The second-order bound with explicit constants -/

private lemma integrable_abs_chi_mul_norm :
    Integrable (fun z : ℝ³ => |chi z| * ‖z‖) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact chi_continuous.abs.mul continuous_norm
  · refine HasCompactSupport.mono chi_hasCompactSupport ?_
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro h
    exact hz (by simp [h])

private lemma integrable_abs_chi_mul_norm_sq :
    Integrable (fun z : ℝ³ => |chi z| * ‖z‖ ^ 2) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact chi_continuous.abs.mul (continuous_norm.pow 2)
  · refine HasCompactSupport.mono chi_hasCompactSupport ?_
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro h
    exact hz (by simp [h])

/-- **The quantitative second-order bound for `symD`.**  The difference
`symD 1 (fsKinCoeff C) ρ − symD 1 (fsKinCoeff C) 0` is bounded by
`M₂ · ‖ρ‖² · ∫_p fsKinCoeff C ‖p‖ · |profHat p| dp`, with the bump's second moment
`M₂ = ∫_z |χ z| ‖z‖² dz`. -/
private lemma symD_diff_bound (C : ℝ) (ρ : ℝ³) :
    |symD 1 (fsKinCoeff C) ρ - symD 1 (fsKinCoeff C) 0|
      ≤ (∫ z : ℝ³, |chi z| * ‖z‖ ^ 2) * ‖ρ‖ ^ 2
          * (∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p|) := by
  set M : ℝ := ∫ z : ℝ³, |chi z| * ‖z‖ ^ 2 with hM
  set mass : ℝ := ∫ z : ℝ³, |chi z| with hmass
  have hmassb : ∀ q : ℝ³, |profHat q| ≤ mass := by
    intro q; rw [hmass]; exact profHat_abs_le_mass q
  have hI : Integrable (fun p : ℝ³ => fsKinCoeff C ‖p‖ * |profHat p|) := integrable_fsKinCoeff_mul_abs_profHat C
  have hFcont : Continuous (fun p : ℝ³ => fsKinCoeff C ‖p‖) := by
    unfold fsKinCoeff
    fun_prop
  -- the two integrands of `symD` at `ρ` and at `0`
  have hAint : Integrable (fun p : ℝ³ => fsKinCoeff C ‖p‖ * profHat p * profHat (ρ - p)) := by
    refine Integrable.mono' (hI.mul_const mass) ?_ (Filter.Eventually.of_forall (fun p => ?_))
    · exact ((hFcont.mul continuous_profHat).mul
        (continuous_profHat.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · have hX : 0 ≤ fsKinCoeff C ‖p‖ * |profHat p| :=
        mul_nonneg (fsKinCoeff_nonneg C ‖p‖) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (fsKinCoeff_nonneg C ‖p‖)]
      exact mul_le_mul le_rfl (hmassb _) (abs_nonneg _) hX
  have hBint : Integrable (fun p : ℝ³ => fsKinCoeff C ‖p‖ * (profHat p) ^ 2) := by
    refine Integrable.mono' (hI.mul_const mass) ?_ (Filter.Eventually.of_forall (fun p => ?_))
    · exact (hFcont.mul (continuous_profHat.pow 2)).aestronglyMeasurable
    · have hsq : (profHat p) ^ 2 ≤ |profHat p| * mass := by
        rw [← sq_abs, pow_two]
        exact mul_le_mul_of_nonneg_left (hmassb p) (abs_nonneg _)
      rw [Real.norm_eq_abs]
      calc |fsKinCoeff C ‖p‖ * (profHat p) ^ 2|
          = fsKinCoeff C ‖p‖ * (profHat p) ^ 2 :=
            abs_of_nonneg (mul_nonneg (fsKinCoeff_nonneg C ‖p‖) (sq_nonneg _))
        _ ≤ fsKinCoeff C ‖p‖ * (|profHat p| * mass) :=
            mul_le_mul_of_nonneg_left hsq (fsKinCoeff_nonneg C ‖p‖)
        _ = fsKinCoeff C ‖p‖ * |profHat p| * mass := by ring
  -- the two difference integrands (at `ρ` and at `−ρ`)
  set Gd : ℝ³ → ℝ := fun p => fsKinCoeff C ‖p‖ * profHat p * profHat (ρ - p)
      - fsKinCoeff C ‖p‖ * (profHat p) ^ 2 with hGd
  set Gd' : ℝ³ → ℝ := fun p => fsKinCoeff C ‖p‖ * profHat p * profHat (ρ + p)
      - fsKinCoeff C ‖p‖ * (profHat p) ^ 2 with hGd'
  have hAint' : Integrable (fun p : ℝ³ => fsKinCoeff C ‖p‖ * profHat p * profHat (ρ + p)) := by
    refine Integrable.mono' (hI.mul_const mass) ?_ (Filter.Eventually.of_forall (fun p => ?_))
    · exact ((hFcont.mul continuous_profHat).mul
        (continuous_profHat.comp (continuous_const.add continuous_id))).aestronglyMeasurable
    · have hX : 0 ≤ fsKinCoeff C ‖p‖ * |profHat p| :=
        mul_nonneg (fsKinCoeff_nonneg C ‖p‖) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (fsKinCoeff_nonneg C ‖p‖)]
      exact mul_le_mul le_rfl (hmassb _) (abs_nonneg _) hX
  have hGdint : Integrable Gd := by rw [hGd]; exact hAint.sub hBint
  have hGd'int : Integrable Gd' := by rw [hGd']; exact hAint'.sub hBint
  -- the two values of `symD`
  have hDρ : symD 1 (fsKinCoeff C) ρ
      = ∫ p : ℝ³, fsKinCoeff C ‖p‖ * profHat p * profHat (ρ - p) := by
    rw [symD]
    simp only [one_smul]
  have hD0 : symD 1 (fsKinCoeff C) 0 = ∫ p : ℝ³, fsKinCoeff C ‖p‖ * (profHat p) ^ 2 := by
    rw [symD_zero 1 (fsKinCoeff C)]
    simp only [one_smul]
  -- `W(ρ)` is the integral of `Gd`
  have hW : symD 1 (fsKinCoeff C) ρ - symD 1 (fsKinCoeff C) 0 = ∫ p : ℝ³, Gd p := by
    rw [hDρ, hD0, hGd, ← integral_sub hAint hBint]
  -- and also the integral of `Gd'`, by `p ↦ -p`
  have hsub : ∫ p : ℝ³, Gd p = ∫ p : ℝ³, Gd' p := by
    have h1 : ∫ p : ℝ³, Gd (-p) = ∫ p : ℝ³, Gd p := integral_neg_eq_self Gd volume
    have h2 : ∫ p : ℝ³, Gd (-p) = ∫ p : ℝ³, Gd' p := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      rw [hGd, hGd']
      simp only [norm_neg, profHat_even, sub_neg_eq_add]
    linarith [h1, h2]
  -- the pointwise bound on the pair
  have hpt : ∀ p : ℝ³,
      |Gd p + Gd' p| ≤ fsKinCoeff C ‖p‖ * |profHat p| * (2 * M * ‖ρ‖ ^ 2) := by
    intro p
    have hS : |(profHat (ρ - p) - profHat p) + (profHat (ρ + p) - profHat p)|
        ≤ 2 * M * ‖ρ‖ ^ 2 := by
      have h := rem_bound p ρ
      rwa [← hM] at h
    have hkey : Gd p + Gd' p = (fsKinCoeff C ‖p‖ * profHat p)
        * ((profHat (ρ - p) - profHat p) + (profHat (ρ + p) - profHat p)) := by
      rw [hGd, hGd']; ring
    rw [hkey, abs_mul, abs_mul, abs_of_nonneg (fsKinCoeff_nonneg C ‖p‖)]
    exact mul_le_mul_of_nonneg_left hS (mul_nonneg (fsKinCoeff_nonneg C ‖p‖) (abs_nonneg _))
  -- the estimate
  have h2W : 2 * (symD 1 (fsKinCoeff C) ρ - symD 1 (fsKinCoeff C) 0)
      = ∫ p : ℝ³, (Gd p + Gd' p) := by
    have h3 : (∫ p : ℝ³, Gd p) + (∫ p : ℝ³, Gd' p) = ∫ p : ℝ³, (Gd p + Gd' p) :=
      (integral_add hGdint hGd'int).symm
    linarith [hW, hsub, h3]
  have hbd : |∫ p : ℝ³, (Gd p + Gd' p)|
      ≤ 2 * M * ‖ρ‖ ^ 2 * (∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p|) := by
    calc |∫ p : ℝ³, (Gd p + Gd' p)| ≤ ∫ p : ℝ³, |Gd p + Gd' p| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p| * (2 * M * ‖ρ‖ ^ 2) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => abs_nonneg _))
            (hI.mul_const (2 * M * ‖ρ‖ ^ 2)) (Filter.Eventually.of_forall hpt)
      _ = 2 * M * ‖ρ‖ ^ 2 * (∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p|) := by
          rw [integral_mul_const]; ring
  have hfin : |symD 1 (fsKinCoeff C) ρ - symD 1 (fsKinCoeff C) 0|
      ≤ M * ‖ρ‖ ^ 2 * (∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p|) := by
    have h1 : |2 * (symD 1 (fsKinCoeff C) ρ - symD 1 (fsKinCoeff C) 0)|
        ≤ 2 * M * ‖ρ‖ ^ 2 * (∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p|) := by
      rw [h2W]
      exact hbd
    have h2 : |2 * (symD 1 (fsKinCoeff C) ρ - symD 1 (fsKinCoeff C) 0)|
        = 2 * |symD 1 (fsKinCoeff C) ρ - symD 1 (fsKinCoeff C) 0| := by
      rw [abs_mul]; norm_num
    linarith [h1, h2]
  calc |symD 1 (fsKinCoeff C) ρ - symD 1 (fsKinCoeff C) 0|
      ≤ M * ‖ρ‖ ^ 2 * (∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p|) := hfin
    _ = (∫ z : ℝ³, |chi z| * ‖z‖ ^ 2) * ‖ρ‖ ^ 2
          * (∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p|) := by rw [hM]

/-! ## The theorem -/

theorem symD_second_order (ε : ℝ) (hε : 0 < ε) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ ρ : EuclideanSpace ℝ (Fin 3), ‖ρ‖ ≤ R →
      |Work.OneBodyKin.symD 1 (Submission.BoseGases.fsKinCoeff C) ρ
          - Work.OneBodyKin.symD 1 (Submission.BoseGases.fsKinCoeff C) 0|
        ≤ ε * ‖ρ‖ ^ 2 := by
  set M : ℝ := ∫ z : ℝ³, |chi z| * ‖z‖ ^ 2 with hM
  have hMnn : 0 ≤ M := by rw [hM]; exact integral_nonneg (fun z => by positivity)
  have hM1pos : 0 < M + 1 := by linarith
  obtain ⟨C, hCpos, hCI⟩ := exists_fsKinCoeff_mul_abs_profHat_le (ε / (M + 1)) (by positivity)
  refine ⟨C, 1, hCpos, one_pos, fun ρ _hρ => ?_⟩
  have hcore := symD_diff_bound C ρ
  rw [← hM] at hcore
  have hmul : M * (ε / (M + 1)) ≤ ε := by
    have h3 : M / (M + 1) ≤ 1 := by
      rw [div_le_one hM1pos]; linarith
    have h4 : M * (ε / (M + 1)) = ε * (M / (M + 1)) := by ring_nf
    rw [h4]
    calc ε * (M / (M + 1)) ≤ ε * 1 := mul_le_mul_of_nonneg_left h3 (le_of_lt hε)
      _ = ε := by ring
  calc |symD 1 (fsKinCoeff C) ρ - symD 1 (fsKinCoeff C) 0|
      ≤ M * ‖ρ‖ ^ 2 * (∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p|) := hcore
    _ ≤ M * ‖ρ‖ ^ 2 * (ε / (M + 1)) :=
        mul_le_mul_of_nonneg_left hCI (mul_nonneg hMnn (sq_nonneg _))
    _ ≤ ε * ‖ρ‖ ^ 2 := by
        calc M * ‖ρ‖ ^ 2 * (ε / (M + 1)) = ‖ρ‖ ^ 2 * (M * (ε / (M + 1))) := by ring
          _ ≤ ‖ρ‖ ^ 2 * ε := mul_le_mul_of_nonneg_left hmul (sq_nonneg _)
          _ = ε * ‖ρ‖ ^ 2 := by ring

end Work.OneBodyKin
