/-
# `Work.FTS.LocData.ZfarFstar.ZFBasic` — ingredients for the far-part `𝓗⁴`-majorant

The `ℋ⁴`-integrand of the *far part* `zfar L F_* = (1 - χ(z/L))·F_*` of the reference profile of
the localisation chapter, together with the elementary facts needed to dominate it.

The pointwise bound `HkIntegrand α 4 (zfar L F_*) z θ ≤ C·α²·angMaj α θ/(1+z)²` that the rest of
the chapter needs cannot carry a *universal* constant `C` — the cut-off
`χ = Real.smoothTransition (2 - ‖·‖)` has enormous fourth derivative in the middle of its
transition annulus (`D_z⁴(1 - χ(·/L)) ≈ 1.8·10⁴` at `z/L = 1.8`), so the true constant is large
but finite; see the discussion in `Submission/Work/FTS/LocData/HkIntegrand_zfar_Fstar_le.lean`.
Accordingly every statement in this file is phrased with the *free* constant supplied by
`Work.FTS.LocData.DzIter_oneSubChi_bound`.

## Contents

* `sin_two_nonneg_Iθ`, `DthIter_mul_left_z`, `DzIter_z_indep_succ`: elementary facts about the
  operators on a factor that does not depend on the differentiating variable;
* `contDiffOn_slice_oneSubChi`, `contDiffOn_slice_FM_Fstar`, `contDiffOn_slice_Fstar`,
  `contDiffOn_slice_c_FM`: the `z`-slice smoothness needed for the Leibniz rules;
* `Pf_abs_le`: a crude bound `|Pf i u α| ≤ 200` for `i ≤ 4`, `u ∈ [-1,1]`, `α ∈ [0,1]`
  (the sharp constants `4/3, 2, 9.6, 35.8` of the sibling `Pf_bounds` are *not* needed here);
* `DzIter_Fstar_w_le`, `mixed_Fstar_w_le`: the weighted derivative bounds for `F_*` and for the
  mixed derivatives, from `Phi_w_le`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothQuad_locG
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.LocData.DzIter_oneSubChi_bound
import Submission.Work.FTS.LocData.Phi_w_le
import Submission.Work.FTS.LocData.PhiZ_eq
import Submission.Work.FTS.LocData.Fstar_factor
import Submission.Work.FTS.LocData.DthIter_Gam_Pf
import Submission.Work.FTS.LocData.HkFstarDefs
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.FTS.LocData.c_ge_three_fifths
import Submission.Work.Stability.HkSqZfar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData
namespace ZF

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary angular fact -/

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-! ## 2. `D_θ` of a factor independent of `θ` -/

/-- `D_θ` is a derivation vanishing on functions of `z` alone, so a `θ`-independent factor passes
through `D_θ` (and all its iterates). -/
theorem DthIter_mul_left_z (i : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-! ## 3. `D_z` of a factor independent of `z` -/

/-- Every positive iterate of `D_z` kills a function of `θ` alone. -/
theorem DzIter_z_indep_succ (a : ℕ) (K : ℝ → ℝ) :
    Work.Spaces.DzIter (a + 1) (fun _ θ => K θ) = 0 := by
  induction a with
  | zero =>
      funext z θ
      simp [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
  | succ a ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dz, Work.Spaces.pz]

/-! ## 4. Smoothness of the `z`-slices -/

theorem contDiffOn_slice_oneSubChi (L : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 1 - Work.Stability.chi (z / L)) (Set.Ioi (-1)) :=
  (contDiff_const.sub (Work.Stability.chi_contDiff.comp (contDiff_id.div_const L))).contDiffOn

theorem contDiffOn_slice_FM_Fstar :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden
    (fun z hz => pow_ne_zero 2 (by have hz' : (-1 : ℝ) < z := hz; linarith))
  have heq : (fun z : ℝ => Work.FM.Fstar z)
      = (fun z : ℝ => 2 * z) / (fun z : ℝ => (1 + z) ^ 2) := rfl
  rw [heq]
  exact h

theorem contDiffOn_slice_Fstar (α : ℝ) (θ : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.Construction.Fstar α z θ)
      (Set.Ioi (-1)) := by
  have hc : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun _ : ℝ => α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) (Set.Ioi (-1)) :=
    contDiffOn_const
  have h := hc.mul contDiffOn_slice_FM_Fstar
  refine h.congr (fun z _ => ?_)
  rw [Work.Construction.Fstar]

theorem contDiffOn_slice_c_FM (L : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z) (Set.Ioi (-1)) :=
  (contDiffOn_slice_oneSubChi L).mul contDiffOn_slice_FM_Fstar

/-! ## 5. A crude bound on the angular polynomials `Pf` -/

/-- **Crude bound on the angular polynomials.**  For `i ≤ 4`, `u ∈ [-1,1]` and `α ∈ [0,1]`,
`|Pf i u α| ≤ 200`.  The sharp constants of `Pf_bounds`/`Pf_bounds_half` are not needed: only
finiteness of the constant matters for the majorant. -/
theorem Pf_abs_le (i : ℕ) (hi : i ≤ 4) {u α : ℝ} (hu : -1 ≤ u) (hu1 : u ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : |Pf i u α| ≤ 200 := by
  have hu' : |u| ≤ 1 := abs_le.mpr ⟨hu, hu1⟩
  have ht : |u - 1 / 3| ≤ 4 / 3 := by rw [abs_le]; constructor <;> linarith
  have h1u2 : |1 - u ^ 2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
  have h13u2 : |1 - 3 * u ^ 2| ≤ 2 := by rw [abs_le]; constructor <;> nlinarith
  have huP : |u * (1 - u ^ 2)| ≤ 1 := by
    rw [abs_mul]
    refine le_trans (mul_le_mul hu' h1u2 (abs_nonneg _) (by norm_num)) ?_
    norm_num
  have htP : |(u - 1 / 3) * (1 - u ^ 2)| ≤ 4 / 3 := by
    rw [abs_mul]
    refine le_trans (mul_le_mul ht h1u2 (abs_nonneg _) (by norm_num)) ?_
    norm_num
  have hA : |(1 - u ^ 2) * (1 - 3 * u ^ 2)| ≤ 2 := by
    rw [abs_mul]
    refine le_trans (mul_le_mul h1u2 h13u2 (abs_nonneg _) (by norm_num)) ?_
    norm_num
  have hB : |(1 - u ^ 2) ^ 2| ≤ 1 := by
    rw [abs_pow]
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) h1u2 2) ?_
    norm_num
  have hC : |u * (u - 1 / 3) * (1 - u ^ 2)| ≤ 4 / 3 := by
    rw [abs_mul, abs_mul]
    refine le_trans (mul_le_mul (mul_le_mul hu' ht (abs_nonneg _) (by norm_num)) h1u2
      (abs_nonneg _) (by norm_num)) ?_
    norm_num
  have hD : |(u - 1 / 3) ^ 2 * (1 - u ^ 2)| ≤ 16 / 9 := by
    rw [abs_mul, abs_pow]
    refine le_trans (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ht 2) h1u2
      (abs_nonneg _) (by norm_num)) ?_
    norm_num
  have hE3 : |(u - 1 / 3) ^ 3| ≤ 64 / 27 := by
    rw [abs_pow]
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) ht 3) ?_
    norm_num
  have hE4 : |(u - 1 / 3) ^ 4| ≤ 256 / 81 := by
    rw [abs_pow]
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) ht 4) ?_
    norm_num
  have h2 : |(-2) * (1 - u ^ 2) + α * (3 * u - 1) ^ 2 / 9| ≤ 2 := by
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1u2
    obtain ⟨hta, htb⟩ := abs_le.mp ht
    have hq : (3 * u - 1) ^ 2 = 9 * (u - 1 / 3) ^ 2 := by ring
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (u - 1 / 3), sq_nonneg (3 * u - 1)]
    · nlinarith [sq_nonneg (u - 1 / 3), sq_nonneg (3 * u - 1), hα0, hα1]
  have h3 : |(-8) * u * (1 - u ^ 2) - 6 * α * (u - 1 / 3) * (1 - u ^ 2)
      + α ^ 2 * (u - 1 / 3) ^ 3| ≤ 19 := by
    rw [abs_le] at huP htP hE3 ⊢
    constructor <;> nlinarith [hα0, hα1]
  have h4 : |16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * α * (1 - u ^ 2) ^ 2
      - 32 * α * u * (u - 1 / 3) * (1 - u ^ 2) - 12 * α ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2)
      + α ^ 3 * (u - 1 / 3) ^ 4| ≤ 150 := by
    obtain ⟨hAa, hAb⟩ := abs_le.mp hA
    obtain ⟨hBa, hBb⟩ := abs_le.mp hB
    obtain ⟨hCa, hCb⟩ := abs_le.mp hC
    obtain ⟨hDa, hDb⟩ := abs_le.mp hD
    obtain ⟨hEa, hEb⟩ := abs_le.mp hE4
    have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα0, hα1]
    have hα3 : 0 ≤ α ^ 3 := by positivity
    have hα3le : α ^ 3 ≤ 1 := by nlinarith [hα0, hα1]
    have hl1 : -(32 : ℝ) ≤ 16 * ((1 - u ^ 2) * (1 - 3 * u ^ 2)) := by nlinarith [hAa]
    have hl2 : -(12 : ℝ) ≤ 12 * α * (1 - u ^ 2) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hBa hα0
      nlinarith [h, hα1]
    have hl3 : 32 * α * u * (u - 1 / 3) * (1 - u ^ 2) ≤ 128 / 3 := by
      have h1 : α * (u * (u - 1 / 3) * (1 - u ^ 2)) ≤ 4 / 3 := by
        have h := mul_le_mul_of_nonneg_left hCb hα0
        nlinarith [h, hα1]
      nlinarith [h1]
    have hl4 : 12 * α ^ 2 * ((u - 1 / 3) ^ 2 * (1 - u ^ 2)) ≤ 64 / 3 := by
      have h := mul_le_mul_of_nonneg_left hDb (sq_nonneg α)
      nlinarith [h, hα2]
    have hl5 : -(256 : ℝ) / 81 ≤ α ^ 3 * (u - 1 / 3) ^ 4 := by
      have h := mul_le_mul_of_nonneg_left hEa hα3
      nlinarith [h, hα3le]
    have hu1 : 16 * ((1 - u ^ 2) * (1 - 3 * u ^ 2)) ≤ 32 := by nlinarith [hAb]
    have hu2 : 12 * α * (1 - u ^ 2) ^ 2 ≤ 12 := by
      have h := mul_le_mul_of_nonneg_left hBb hα0
      nlinarith [h, hα1]
    have hu3 : -(128 : ℝ) / 3 ≤ 32 * α * u * (u - 1 / 3) * (1 - u ^ 2) := by
      have h1 : -(4 : ℝ) / 3 ≤ α * (u * (u - 1 / 3) * (1 - u ^ 2)) := by
        have h := mul_le_mul_of_nonneg_left hCa hα0
        nlinarith [h]
      nlinarith [h1]
    have hu4 : -(64 : ℝ) / 3 ≤ 12 * α ^ 2 * ((u - 1 / 3) ^ 2 * (1 - u ^ 2)) := by
      have h := mul_le_mul_of_nonneg_left hDa (sq_nonneg α)
      nlinarith [h]
    have hu5 : α ^ 3 * (u - 1 / 3) ^ 4 ≤ 256 / 81 := by
      have h := mul_le_mul_of_nonneg_left hEb hα3
      nlinarith [h, hα3le]
    rw [abs_le]
    constructor <;> nlinarith [hl1, hl2, hl3, hl4, hl5, hu1, hu2, hu3, hu4, hu5]
  interval_cases i
  · rw [Pf_zero]; norm_num
  · rw [Pf_one, abs_mul, abs_of_nonneg hα0]
    have h : |(3 * u - 1) / 3| ≤ 4 / 3 := by
      rw [show (3 * u - 1) / 3 = u - 1 / 3 by ring]; exact ht
    nlinarith [abs_nonneg ((3 * u - 1) / 3)]
  · rw [Pf_two, abs_mul, abs_of_nonneg hα0]
    nlinarith [abs_nonneg ((-2) * (1 - u ^ 2) + α * (3 * u - 1) ^ 2 / 9)]
  · rw [Pf_three, abs_mul, abs_of_nonneg hα0]
    nlinarith [abs_nonneg ((-8) * u * (1 - u ^ 2) - 6 * α * (u - 1 / 3) * (1 - u ^ 2)
      + α ^ 2 * (u - 1 / 3) ^ 3)]
  · rw [Pf_four, abs_mul, abs_of_nonneg hα0]
    nlinarith [abs_nonneg (16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * α * (1 - u ^ 2) ^ 2
      - 32 * α * u * (u - 1 / 3) * (1 - u ^ 2) - 12 * α ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2)
      + α ^ 3 * (u - 1 / 3) ^ 4)]

/-! ## 6. Pointwise bounds for the weighted derivatives of `F_*` -/

/-- `|D_z^a F_* · w| ≤ (10/3)·α·Γ/z` for `z ≥ 1`: `D_z^a F_* = (α/c)·Γ·Φ_a` and
`|w·Φ_a| ≤ 2/z` (`Phi_w_le`), with `1/c ≤ 5/3`. -/
theorem DzIter_Fstar_w_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {a : ℕ} (ha : a ≤ 4)
    {z : ℝ} (hz1 : 1 ≤ z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DzIter a (Work.Construction.Fstar α) z θ * Work.Spaces.w z|
      ≤ 10 * α * Work.Spaces.Gam α θ / (3 * z) := by
  have hc : (3 : ℝ) / 5 ≤ Work.Spaces.c α := c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hz : 0 < z := by linarith
  have hPhi := Phi_w_le a ha hz1 θ
  have heq : Work.Spaces.DzIter a (Work.Construction.Fstar α) z θ
      = (α / Work.Spaces.c α) * Work.Spaces.Gam α θ
          * Work.Spaces.DzIter a (fun z _ => Work.FM.Fstar z) z θ :=
    congrFun (congrFun (DzIter_Fstar_eq α a) z) θ
  rw [heq, PhiZ_eq a ha z θ]
  have hsplit : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ
        * Work.FTS.LocData.Phi a z θ * Work.Spaces.w z
      = ((α / Work.Spaces.c α) * Work.Spaces.Gam α θ)
          * (Work.Spaces.w z * Work.FTS.LocData.Phi a z θ) := by ring
  rw [hsplit, abs_mul]
  have h1 : |(α / Work.Spaces.c α) * Work.Spaces.Gam α θ|
      = (α / Work.Spaces.c α) * Work.Spaces.Gam α θ :=
    abs_of_nonneg (by positivity)
  rw [h1]
  have h2 : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ
        * |Work.Spaces.w z * Work.FTS.LocData.Phi a z θ|
      ≤ (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (2 / z) :=
    mul_le_mul_of_nonneg_left hPhi (by positivity)
  refine le_trans h2 ?_
  have hcInv : (Work.Spaces.c α)⁻¹ ≤ (5 : ℝ) / 3 := by
    have h0 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 5) hc
    rw [one_div] at h0
    norm_num at h0
    exact h0
  have hA : 0 ≤ α * Work.Spaces.Gam α θ := mul_nonneg hα.le hG0
  have hstep : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (2 / z)
      = (α * Work.Spaces.Gam α θ) * (2 * ((Work.Spaces.c α)⁻¹ * z⁻¹)) := by ring
  rw [hstep]
  have h2' : (α * Work.Spaces.Gam α θ) * (2 * ((Work.Spaces.c α)⁻¹ * z⁻¹))
      ≤ (α * Work.Spaces.Gam α θ) * (2 * ((5 : ℝ) / 3 * z⁻¹)) := by
    refine mul_le_mul_of_nonneg_left ?_ hA
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_right hcInv (by positivity)
  refine le_trans h2' ?_
  have hzne : z ≠ 0 := ne_of_gt hz
  refine le_of_eq ?_
  field_simp
  ring

/-- `|mixed_a^i F_* · w| ≤ 200·(10/3)·α·Γ/z` for `z ≥ 1`, `i ≤ 4`: `mixed_a^i F_*` is
`(α/c)·D_θ^iΓ(0,θ)·Φ_a` and `|D_θ^iΓ(0,θ)| ≤ 200·Γ`, `|w·Φ_a| ≤ 2/z`. -/
theorem mixed_Fstar_w_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {a i : ℕ} (ha : a ≤ 4) (hi : i ≤ 4)
    {z : ℝ} (hz1 : 1 ≤ z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed a i (Work.Construction.Fstar α) z θ * Work.Spaces.w z|
      ≤ 200 * (10 * α * Work.Spaces.Gam α θ / (3 * z)) := by
  have hc : (3 : ℝ) / 5 ≤ Work.Spaces.c α := c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hz : 0 < z := by linarith
  have hPhi := Phi_w_le a ha hz1 θ
  have hgam : Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
      = Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α := DthIter_Gam_Pf α i hi 0 θ hθ
  have hPf : |Pf i (Real.cos (2 * θ)) α| ≤ 200 :=
    Pf_abs_le i hi (Real.neg_one_le_cos _) (Real.cos_le_one _) hα.le hα1
  have heq : Work.Spaces.mixed a i (Work.Construction.Fstar α) z θ
      = (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α)
          * Work.Spaces.DzIter a (fun z _ => Work.FM.Fstar z) z θ := by
    have h := congrFun (congrFun (mixed_Fstar_eq α i a) z) θ
    rw [h, hgam]
  rw [heq, PhiZ_eq a ha z θ]
  have hsplit : (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α)
        * Work.FTS.LocData.Phi a z θ * Work.Spaces.w z
      = ((α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α))
          * (Work.Spaces.w z * Work.FTS.LocData.Phi a z θ) := by ring
  rw [hsplit, abs_mul]
  have h1 : |(α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α)| ≤
      (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * 200) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α / Work.Spaces.c α)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_mul, abs_of_nonneg hG0]
    exact mul_le_mul_of_nonneg_left hPf hG0
  have h2 : |(α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α)|
        * |Work.Spaces.w z * Work.FTS.LocData.Phi a z θ|
      ≤ ((α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * 200)) * (2 / z) :=
    mul_le_mul h1 hPhi (abs_nonneg _) (by positivity)
  refine le_trans h2 ?_
  have hcInv : (Work.Spaces.c α)⁻¹ ≤ (5 : ℝ) / 3 := by
    have h0 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 5) hc
    rw [one_div] at h0
    norm_num at h0
    exact h0
  have hA : 0 ≤ α * Work.Spaces.Gam α θ := mul_nonneg hα.le hG0
  have hstep : (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * 200) * (2 / z)
      = ((α * Work.Spaces.Gam α θ) * 400) * ((Work.Spaces.c α)⁻¹ * z⁻¹) := by ring
  rw [hstep]
  have h2' : ((α * Work.Spaces.Gam α θ) * 400) * ((Work.Spaces.c α)⁻¹ * z⁻¹)
      ≤ ((α * Work.Spaces.Gam α θ) * 400) * ((5 : ℝ) / 3 * z⁻¹) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right hcInv (by positivity)
  refine le_trans h2' ?_
  have hzne : z ≠ 0 := ne_of_gt hz
  refine le_of_eq ?_
  field_simp
  ring

end ZF
end Work.FTS.LocData
