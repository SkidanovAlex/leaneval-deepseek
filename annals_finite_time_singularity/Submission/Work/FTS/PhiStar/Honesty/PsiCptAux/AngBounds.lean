/-
# `PsiCptAux.AngBounds` — the angular bounds used by `psiSeries_bslOp_of_cptQ`

The auxiliary analytic facts for `Psi/psiSeries_bslOp_of_cptQ`: the angular sup bounds for the
derivatives of the Dirichlet eigenfamily `eFam m` of `Lzero` (built from the radial energy bound
`Work.FTS.PhiStar.Series.eFamSupAux.ug_bound` and the eigen-relation `eFam_Lzero`), plus the
elementary comparison `pow_inv_le_majPow` against the majorant `majPow m = (m+1)^{-3/2}` and the
assembling step `final_le`.

Nothing here uses the `Deleg.psiAngDefs` cone (which clashes with the `ClassC`/`cmode_decay`
cone because both declare `Work.FTS.PhiStar.Series.Deleg.gC_abs_bound`), so this file can be
imported together with `Work.FTS.ClassC.deriv_series_general`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.PhiStar.Series.eFamSupDefs
import Submission.Work.FTS.PhiStar.Series.eFamSupAux.ug_bound
import Submission.Work.FTS.PhiStar.Series.BslOp.Setup
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.PsiCptAux

set_option autoImplicit false

open Work.FTS.PhiStar.Gegenbauer (eFam gC lam)
open Work.FTS.PhiStar.Series

/-! ## `majPow` comparison -/

lemma pow_inv_le_majPow {m : ℕ} (hm : 1 ≤ m) {k : ℕ} (hk : 2 ≤ k) :
    (((m : ℝ) + 1) ^ k)⁻¹ ≤ majPow m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hpos : 0 < (m : ℝ) + 1 := lt_of_lt_of_le zero_lt_one hm1
  have hle : ((m : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤ ((m : ℝ) + 1) ^ k := by
    rw [← Real.rpow_natCast ((m : ℝ) + 1) k]
    refine Real.rpow_le_rpow_of_exponent_le hm1 ?_
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  rw [majPow]
  exact inv_anti₀ (Real.rpow_pos_of_pos hpos (3 / 2)) hle

lemma mul_cos_sq_le {A : ℝ} {c : ℝ} (hA : 0 ≤ A) (hc : c ^ 2 ≤ 1) : A * c ^ 2 ≤ A := by
  calc A * c ^ 2 ≤ A * 1 := mul_le_mul_of_nonneg_left hc hA
    _ = A := by ring

lemma abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h : a - b = a + (-b) := by ring
  rw [h]
  calc |a + (-b)| ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

/-! ## Angular bounds -/

lemma abs_deriv_ug_sin_le (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |deriv (ug m) (Real.sin θ)| ≤ Npsi m := by
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hs : Real.sin θ ∈ Set.Icc (0 : ℝ) 1 := ⟨hsin0, hsin1⟩
  have h := ene_le m hs
  have hgc : 0 ≤ gC (2 * m + 1) (Real.sin θ) * gC (2 * m + 1) (Real.sin θ) :=
    mul_self_nonneg _
  have h1m : 0 ≤ 1 - (Real.sin θ) ^ 2 := by nlinarith
  have h2 : 0 ≤ Npsi m * ((1 - (Real.sin θ) ^ 2) * (gC (2 * m + 1) (Real.sin θ)
      * gC (2 * m + 1) (Real.sin θ))) :=
    mul_nonneg (le_of_lt (Npsi_pos m)) (mul_nonneg h1m hgc)
  have h3 : deriv (ug m) (Real.sin θ) * deriv (ug m) (Real.sin θ) ≤ Npsi m * Npsi m := by
    have h4 : ene m (Real.sin θ) = deriv (ug m) (Real.sin θ) * deriv (ug m) (Real.sin θ)
        + Npsi m * ((1 - (Real.sin θ) ^ 2) * (gC (2 * m + 1) (Real.sin θ)
          * gC (2 * m + 1) (Real.sin θ))) := rfl
    linarith [h]
  have hN : 0 ≤ Npsi m := le_of_lt (Npsi_pos m)
  have h4 : deriv (ug m) (Real.sin θ) ^ 2 ≤ Npsi m ^ 2 := by
    have hh : deriv (ug m) (Real.sin θ) * deriv (ug m) (Real.sin θ) ≤ Npsi m * Npsi m := h3
    simpa only [sq] using hh
  exact abs_le_of_sq_le_sq h4 hN

lemma deriv_eFam_eq (m : ℕ) {y : ℝ} :
    deriv (eFam m) y = deriv (ug m) (Real.sin y)
      + Real.sin y * gC (2 * m + 1) (Real.sin y) := by
  have hgc : HasDerivAt (gC (2 * m + 1)) (deriv (gC (2 * m + 1)) (Real.sin y)) (Real.sin y) :=
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).differentiable
      (by norm_num)).differentiableAt).hasDerivAt
  have h1 : HasDerivAt (fun y' : ℝ => Real.cos y' * gC (2 * m + 1) (Real.sin y'))
      (-(Real.sin y) * gC (2 * m + 1) (Real.sin y)
        + Real.cos y * (deriv (gC (2 * m + 1)) (Real.sin y) * Real.cos y)) y :=
    (Real.hasDerivAt_cos y).mul (hgc.comp y (Real.hasDerivAt_sin y))
  rw [show eFam m = fun y' : ℝ => Real.cos y' * gC (2 * m + 1) (Real.sin y') from rfl,
    h1.deriv, deriv_ug m (Real.sin y)]
  have hsq : 1 - (Real.sin y) ^ 2 = (Real.cos y) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq y]
  rw [hsq]
  ring

lemma abs_deriv_eFam_le (m : ℕ) {y : ℝ} (hy : 0 < y) (hy2 : y < Real.pi / 2) :
    |deriv (eFam m) y| ≤ 12 * ((m : ℝ) + 1) ^ 2 / Real.cos y := by
  have hcos : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy2⟩
  have hsin0 : 0 ≤ Real.sin y :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hy, by linarith [Real.pi_pos]⟩
  have hIθ : y ∈ Work.Spaces.Iθ := ⟨le_of_lt hy, le_of_lt hy2⟩
  have hug : |ug m (Real.sin y)| ≤ Real.sqrt (Npsi m) * Real.cos y := abs_ug_sin_le m y hIθ
  have hdu : |deriv (ug m) (Real.sin y)| ≤ Npsi m := abs_deriv_ug_sin_le m hIθ
  have hgc : gC (2 * m + 1) (Real.sin y) = ug m (Real.sin y) / (Real.cos y) ^ 2 := by
    rw [show ug m (Real.sin y) = (1 - (Real.sin y) ^ 2) * gC (2 * m + 1) (Real.sin y) from rfl,
      show 1 - (Real.sin y) ^ 2 = (Real.cos y) ^ 2 from by
        linarith [Real.sin_sq_add_cos_sq y]]
    field_simp
  have hstep : |Real.sin y * gC (2 * m + 1) (Real.sin y)| ≤ Real.sqrt (Npsi m) / Real.cos y := by
    have hgcabs : |gC (2 * m + 1) (Real.sin y)| = |ug m (Real.sin y)| / (Real.cos y) ^ 2 := by
      rw [hgc, abs_div, abs_of_pos (pow_pos hcos 2)]
    rw [abs_mul, abs_of_nonneg hsin0, hgcabs]
    have h1 : Real.sin y * (|ug m (Real.sin y)| / (Real.cos y) ^ 2)
        = (Real.sin y * |ug m (Real.sin y)|) / (Real.cos y) ^ 2 := by ring
    rw [h1, div_le_iff₀ (pow_pos hcos 2)]
    have h2 : (Real.sqrt (Npsi m) / Real.cos y) * (Real.cos y) ^ 2
        = Real.sqrt (Npsi m) * Real.cos y := by field_simp
    rw [h2]
    calc Real.sin y * |ug m (Real.sin y)|
        ≤ 1 * (Real.sqrt (Npsi m) * Real.cos y) :=
          mul_le_mul (Real.sin_le_one y) hug (abs_nonneg _) (by positivity)
      _ = Real.sqrt (Npsi m) * Real.cos y := by ring
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hN9 : Npsi m ≤ 9 * ((m : ℝ) + 1) ^ 2 := by
    have h := sqrt_Npsi_le_three m
    rw [Real.sqrt_le_iff] at h
    nlinarith [h.2]
  have h2 : Npsi m ≤ 9 * ((m : ℝ) + 1) ^ 2 / Real.cos y := by
    rw [le_div_iff₀ hcos]
    nlinarith [hN9, hcos, Real.cos_le_one y]
  have h1' : Real.sqrt (Npsi m) / Real.cos y ≤ 3 * ((m : ℝ) + 1) / Real.cos y := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (sqrt_Npsi_le_three m) (by positivity)
  have h4 : 3 * ((m : ℝ) + 1) / Real.cos y ≤ 3 * ((m : ℝ) + 1) ^ 2 / Real.cos y := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hm1]) (by positivity)
  rw [deriv_eFam_eq m]
  calc |deriv (ug m) (Real.sin y) + Real.sin y * gC (2 * m + 1) (Real.sin y)|
      ≤ |deriv (ug m) (Real.sin y)| + |Real.sin y * gC (2 * m + 1) (Real.sin y)| := abs_add_le _ _
    _ ≤ Npsi m + Real.sqrt (Npsi m) / Real.cos y := add_le_add hdu hstep
    _ ≤ 9 * ((m : ℝ) + 1) ^ 2 / Real.cos y + 3 * ((m : ℝ) + 1) ^ 2 / Real.cos y := by
        linarith
    _ = 12 * ((m : ℝ) + 1) ^ 2 / Real.cos y := by ring

lemma differentiable_eFam (m : ℕ) : Differentiable ℝ (eFam m) := by
  have h1 : Differentiable ℝ (fun y : ℝ => Real.cos y * gC (2 * m + 1) (Real.sin y)) :=
    Real.differentiable_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).differentiable
        (by norm_num)).comp Real.differentiable_sin)
  exact h1

lemma tan_abs_le (y : ℝ) (hcos : 0 < Real.cos y) : |Real.tan y| ≤ 1 / Real.cos y := by
  rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcos]
  rw [div_le_div_iff_of_pos_right hcos]
  exact Real.abs_sin_le_one y

lemma abs_iteratedDeriv2_eFam_le (m : ℕ) {y : ℝ} (hy : 0 < y) (hy2 : y < Real.pi / 2) :
    |iteratedDeriv 2 (eFam m) y| ≤ 100 * ((m : ℝ) + 1) ^ 3 / (Real.cos y) ^ 2 := by
  have hcospos : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy2⟩
  have hcos : Real.cos y ≠ 0 := ne_of_gt hcospos
  have hODE := Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hcos 0
  rw [Work.Elliptic.Lzero_eq_deriv] at hODE
  have hrepr : deriv (deriv (fun θ : ℝ => eFam m θ)) y
      = deriv (fun θ : ℝ => Real.tan θ * eFam m θ) y - 6 * eFam m y - lam m * eFam m y := by
    linarith
  have hde : HasDerivAt (eFam m) (deriv (eFam m) y) y :=
    (differentiable_eFam m).differentiableAt.hasDerivAt
  have htan : deriv (fun θ : ℝ => Real.tan θ * eFam m θ) y
      = (1 / (Real.cos y) ^ 2) * eFam m y + Real.tan y * deriv (eFam m) y :=
    ((Real.hasDerivAt_tan hcos).mul hde).deriv
  have hIθ : y ∈ Work.Spaces.Iθ := ⟨le_of_lt hy, le_of_lt hy2⟩
  have he : |eFam m y| ≤ 3 * ((m : ℝ) + 1) :=
    le_trans (abs_eFam_le_sqrt_Npsi m hIθ) (sqrt_Npsi_le_three m)
  have hde' : |deriv (eFam m) y| ≤ 12 * ((m : ℝ) + 1) ^ 2 / Real.cos y := abs_deriv_eFam_le m hy hy2
  have htan' : |Real.tan y| ≤ 1 / Real.cos y := tan_abs_le y hcospos
  have hcs_le : (Real.cos y) ^ 2 ≤ 1 := by
    nlinarith [Real.cos_le_one y, hcospos, sq_nonneg (Real.cos y)]
  have hc2 : (1 : ℝ) ≤ 1 / ((Real.cos y) ^ 2) := by
    rw [le_div_iff₀ (pow_pos hcospos 2)]; simpa using hcs_le
  have hlam_nn : (0 : ℝ) ≤ lam m := by rw [lam]; positivity
  have hlam : lam m ≤ 6 * ((m : ℝ) + 1) ^ 2 := by
    rw [lam]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hX : |(1 / (Real.cos y) ^ 2) * eFam m y| ≤ 3 * ((m : ℝ) + 1) / (Real.cos y) ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (Real.cos y)^2)]
    calc 1 / (Real.cos y) ^ 2 * |eFam m y| ≤ 1 / (Real.cos y) ^ 2 * (3 * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = 3 * ((m : ℝ) + 1) / (Real.cos y) ^ 2 := by ring
  have hY : |Real.tan y * deriv (eFam m) y| ≤ 12 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 2 := by
    rw [abs_mul]
    calc |Real.tan y| * |deriv (eFam m) y|
        ≤ (1 / Real.cos y) * (12 * ((m : ℝ) + 1) ^ 2 / Real.cos y) :=
          mul_le_mul htan' hde' (abs_nonneg _) (by positivity)
      _ = 12 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 2 := by field_simp; try ring
  have hU : |6 * eFam m y| ≤ 6 * (3 * ((m : ℝ) + 1)) / (Real.cos y) ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 6)]
    refine le_trans (by linarith [he] : 6 * |eFam m y| ≤ 6 * (3 * ((m : ℝ) + 1))) ?_
    rw [le_div_iff₀ (pow_pos hcospos 2)]
    exact mul_cos_sq_le (by positivity) hcs_le
  have hV : |lam m * eFam m y| ≤ 6 * ((m : ℝ) + 1) ^ 2 * (3 * ((m : ℝ) + 1)) / (Real.cos y) ^ 2 := by
    rw [abs_mul, abs_of_nonneg hlam_nn]
    refine le_trans (mul_le_mul hlam he (abs_nonneg _) (by positivity) :
       lam m * |eFam m y| ≤ 6 * ((m : ℝ) + 1) ^ 2 * (3 * ((m : ℝ) + 1))) ?_
    rw [le_div_iff₀ (pow_pos hcospos 2)]
    exact mul_cos_sq_le (by positivity) hcs_le
  rw [iteratedDeriv_two_apply, hrepr, htan]
  have hcomb : |(1 / (Real.cos y) ^ 2) * eFam m y + Real.tan y * deriv (eFam m) y
      - 6 * eFam m y - lam m * eFam m y|
      ≤ 3 * ((m : ℝ) + 1) / (Real.cos y) ^ 2 + 12 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 2
        + 6 * (3 * ((m : ℝ) + 1)) / (Real.cos y) ^ 2
        + 6 * ((m : ℝ) + 1) ^ 2 * (3 * ((m : ℝ) + 1)) / (Real.cos y) ^ 2 := by
    have h1 : (1 / (Real.cos y) ^ 2) * eFam m y + Real.tan y * deriv (eFam m) y
        - 6 * eFam m y - lam m * eFam m y
        = ((1 / (Real.cos y) ^ 2) * eFam m y + Real.tan y * deriv (eFam m) y)
          + (-(6 * eFam m y) + -(lam m * eFam m y)) := by ring
    rw [h1]
    calc |((1 / (Real.cos y) ^ 2) * eFam m y + Real.tan y * deriv (eFam m) y)
          + (-(6 * eFam m y) + -(lam m * eFam m y))|
        ≤ |((1 / (Real.cos y) ^ 2) * eFam m y + Real.tan y * deriv (eFam m) y)|
          + |(-(6 * eFam m y) + -(lam m * eFam m y))| := abs_add_le _ _
      _ ≤ (|(1 / (Real.cos y) ^ 2) * eFam m y| + |Real.tan y * deriv (eFam m) y|)
          + (|-(6 * eFam m y)| + |-(lam m * eFam m y)|) :=
            add_le_add (abs_add_le _ _) (abs_add_le _ _)
      _ = (|(1 / (Real.cos y) ^ 2) * eFam m y| + |Real.tan y * deriv (eFam m) y|)
          + (|6 * eFam m y| + |lam m * eFam m y|) := by rw [abs_neg, abs_neg]
      _ ≤ 3 * ((m : ℝ) + 1) / (Real.cos y) ^ 2 + 12 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 2
          + (6 * (3 * ((m : ℝ) + 1)) / (Real.cos y) ^ 2
            + 6 * ((m : ℝ) + 1) ^ 2 * (3 * ((m : ℝ) + 1)) / (Real.cos y) ^ 2) := by
            linarith
      _ = 3 * ((m : ℝ) + 1) / (Real.cos y) ^ 2 + 12 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 2
          + 6 * (3 * ((m : ℝ) + 1)) / (Real.cos y) ^ 2
          + 6 * ((m : ℝ) + 1) ^ 2 * (3 * ((m : ℝ) + 1)) / (Real.cos y) ^ 2 := by ring
  refine le_trans hcomb ?_
  rw [← add_div, ← add_div, ← add_div]
  rw [div_le_div_iff_of_pos_right (pow_pos hcospos 2)]
  nlinarith [hm1]

lemma abs_deriv_tan_eFam_le (m : ℕ) {y : ℝ} (hy : 0 < y) (hy2 : y < Real.pi / 2) :
    |deriv (fun θ' => Real.tan θ' * eFam m θ') y| ≤ 20 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 2 := by
  have hcospos : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy2⟩
  have hcos : Real.cos y ≠ 0 := ne_of_gt hcospos
  have hde : HasDerivAt (eFam m) (deriv (eFam m) y) y :=
    (differentiable_eFam m).differentiableAt.hasDerivAt
  have htan : deriv (fun θ' : ℝ => Real.tan θ' * eFam m θ') y
      = (1 / (Real.cos y) ^ 2) * eFam m y + Real.tan y * deriv (eFam m) y :=
    ((Real.hasDerivAt_tan hcos).mul hde).deriv
  have hIθ : y ∈ Work.Spaces.Iθ := ⟨le_of_lt hy, le_of_lt hy2⟩
  have he : |eFam m y| ≤ 3 * ((m : ℝ) + 1) :=
    le_trans (abs_eFam_le_sqrt_Npsi m hIθ) (sqrt_Npsi_le_three m)
  have hde' : |deriv (eFam m) y| ≤ 12 * ((m : ℝ) + 1) ^ 2 / Real.cos y := abs_deriv_eFam_le m hy hy2
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hX : |(1 / (Real.cos y) ^ 2) * eFam m y| ≤ 3 * ((m : ℝ) + 1) / (Real.cos y) ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (Real.cos y)^2)]
    calc 1 / (Real.cos y) ^ 2 * |eFam m y| ≤ 1 / (Real.cos y) ^ 2 * (3 * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = 3 * ((m : ℝ) + 1) / (Real.cos y) ^ 2 := by ring
  have hY : |Real.tan y * deriv (eFam m) y| ≤ 12 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 2 := by
    rw [abs_mul]
    calc |Real.tan y| * |deriv (eFam m) y|
        ≤ (1 / Real.cos y) * (12 * ((m : ℝ) + 1) ^ 2 / Real.cos y) :=
          mul_le_mul (tan_abs_le y hcospos) hde' (abs_nonneg _) (by positivity)
      _ = 12 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 2 := by field_simp; try ring
  rw [htan]
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add hX hY) ?_
  rw [← add_div, div_le_div_iff_of_pos_right (pow_pos hcospos 2)]
  nlinarith [hm1]

lemma div_le_div_of_le_denom {N D d : ℝ} (hN : 0 ≤ N) (hd : 0 < d) (hD : d ≤ D) :
    N / D ≤ N / d := by
  rw [div_le_div_iff₀ (lt_of_lt_of_le hd hD) hd]
  nlinarith

lemma div_le_div_of_le_num {N n d : ℝ} (hNn : N ≤ n) (hd : 0 < d) : N / d ≤ n / d :=
  div_le_div_of_nonneg_right hNn (le_of_lt hd)

lemma final_le {Dc K : ℝ} {m k : ℕ} (hK0 : 0 ≤ K) (hKD : K ≤ Dc) (hk : 2 ≤ k) (hm1 : 1 ≤ m) :
    K * (((m : ℝ) + 1) ^ k)⁻¹ ≤ Dc * majPow m :=
  le_trans (mul_le_mul_of_nonneg_left (pow_inv_le_majPow hm1 hk) hK0)
    (mul_le_mul_of_nonneg_right hKD (majPow_nonneg m))


end Work.FTS.PhiStar.Honesty.PsiCptAux
