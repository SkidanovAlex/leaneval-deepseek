/-
# `Honesty.psiSeries_bslOp_of_cptQ` — the mode series solves `bslOp α Ψ = G`

For `G` a `C^∞` source whose support is a compact subset of the open quadrant `(0,∞) × (0,π/2)`
and whose angular moment `F_* G` vanishes identically on `z > 0`,

  `bslOp α (psiSeries α G) z θ = G z θ`  for `z > 0`, `0 < θ < π/2`, `0 < α ≤ 1/4`.

`psiSeries α G = Σ_m radGreen α m (cmode m G)(z) · e_m(θ)` is the modal solution of the
axi-symmetric Biot--Savart operator in the self-similar variables.

**Proof.**  Everything is reduced to the "crux estimates" of
`Work.FTS.ClassC.deriv_series_general` (the general termwise differentiation of the mode
series, under six pointwise majorant bounds `hB0..hB5`):

* the mode coefficients `cmode m G` are supported in the `z`-box `[z₁,z₂]` of `G` and decay
  rapidly in `m`: `|cmode m G t| ≤ Cdec/(m+1)^5` for `m ≥ 1`
  (`Honesty.cmode_decay_of_cptQ`) — this gives **strong** decay of
  `acoeff α m G = radGreen α m (cmode m G)`;
* `Honesty.radGreenI_deriv_bounds_cpt` bounds `radGreen` and its two `z`-derivatives by
  `C·(Cdec/(m+1)^5)`, uniformly in `z`, because the source is supported away from `0` and `∞`;
* the angular slots `hB3`–`hB5` combine that with the angular bounds
  `|∂_θ^k(eFam m)| ≤ C(m+1)^{k+1}/cos^k` proved in `PsiCptAux.AngBounds` from the radial energy
  bound `Series.eFamSupAux.ug_bound` and the eigen-relation `eFam_Lzero`;
* the resulting `bslOp`-series is identified modewise with `cmode m G z·e_m(θ)` by
  `radGreen_solves` + the eigen-relation, and the result is summed via `tsum_lincomb5`;
* finally `Σ_m cmode m G z·e_m(θ) = G z θ` on `(0,π/2)`, which is the pointwise eigen-expansion
  of the slice: `Honesty.tsum_bmode_eFam_eq_of_continuous` applied to `ψ := G z ·` (continuous,
  with vanishing moment by `hFs`, and rapid coefficient decay by `cmode_decay_of_cptQ`).

The `m = 0` mode is harmless: `F_* G ≡ 0` forces `cmode 0 G ≡ 0` (`acoeff_zero_of_fstar`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.FTS.PhiStar.Honesty.PsiCptAux.AngBounds
import Submission.Work.FTS.PhiStar.Honesty.tsum_bmode_eFam_eq_of_continuous
import Submission.Work.FTS.PhiStar.Honesty.radGreenI_deriv_bounds_cpt
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.FTS.PhiStar.Series.BslOp.Setup
import Submission.Work.FTS.PhiStar.Series.Deleg.rpowMajorant
import Submission.Work.FTS.PhiStar.Honesty.cmode_decay_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one
import Submission.Work.FTS.PhiStar.Honesty.smoothCptQ_hkMem
import Submission.Work.FTS.ClassC.deriv_series_general
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Work.FTS.PhiStar.Gegenbauer (eFam gC lam)
open Work.FTS.PhiStar.Honesty.PsiCptAux
open Work.FTS.PhiStar.Series

theorem psiSeries_bslOp_of_cptQ {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (Work.FTS.PhiStar.Series.psiSeries α G) z θ = G z θ := by
  obtain ⟨z₁, z₂, t₁, t₂, hz₁, hz₁z₂, ht₁, ht₁t₂, ht₂, hbox⟩ := hG.cpt
  obtain ⟨Cdec, hCdec0, hCdec⟩ := cmode_decay_of_cptQ hG 0 5
  have hcmode_zero : ∀ (m : ℕ) (t : ℝ), t ∉ Set.Icc z₁ z₂ → cmode m G t = 0 := by
    intro m t ht
    have hG0 : ∀ θ : ℝ, G t θ = 0 := fun θ => by
      by_contra hne
      exact ht (hbox t θ hne).1
    rw [Work.FTS.PhiStar.Series.cmode]
    have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        G t θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) = 0 := by
      simp only [hG0, zero_mul, intervalIntegral.integral_zero]
    rw [hnum, zero_div]
  have hMdec : ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ, |cmode m G t| ≤ Cdec / ((m : ℝ) + 1) ^ 5 := by
    intro m hm t; simpa using hCdec m hm t
  have hcm : ∀ m : ℕ, ContinuousOn (fun t => cmode m G t) (Set.Ioi 0) := fun m =>
    continuousOn_cmode_of_hkMem_one (α := α) m hG.smoothOpen (smoothCptQ_hkMem (α := α) hG 1)
  have hsuppcm : ∀ m : ℕ, ∀ t : ℝ, cmode m G t ≠ 0 → t ∈ Set.Icc z₁ z₂ := fun m t ht =>
    by_contra fun h => ht (hcmode_zero m t h)
  have hinteg : ∀ (m : ℕ) (r : ℝ) (s : Set ℝ),
      MeasureTheory.IntegrableOn (fun t : ℝ => cmode m G t * t ^ r) s := by
    intro m r s
    have heq : (Set.Icc z₁ z₂).indicator (fun t : ℝ => cmode m G t * t ^ r)
        = fun t : ℝ => cmode m G t * t ^ r := by
      funext t
      by_cases ht : t ∈ Set.Icc z₁ z₂
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, hcmode_zero m t ht, zero_mul]
    have hcont : ContinuousOn (fun t : ℝ => cmode m G t * t ^ r) (Set.Icc z₁ z₂) :=
      ((hcm m).mono (fun t ht => lt_of_lt_of_le hz₁ ht.1)).mul
        (continuousOn_id.rpow_const (fun t ht =>
          Or.inl (ne_of_gt (lt_of_lt_of_le hz₁ ht.1))))
    rw [← heq]
    exact ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (ContinuousOn.integrableOn_compact isCompact_Icc hcont)).integrableOn
  intro z hz θ hθ hθ2
  have hcosθ : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  set θu : ℝ := (θ + Real.pi / 2) / 2 with hθu
  have hθθu : θ < θu := by rw [hθu]; linarith [hθ2]
  have hθu_lt : θu < Real.pi / 2 := by rw [hθu]; linarith [hθ2]
  have hθu_pos : 0 < θu := lt_trans hθ hθθu
  have hcθu : 0 < Real.cos θu :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθu_lt⟩
  have hθu_le : θ ≤ (θ + Real.pi / 2) / 2 := le_of_lt hθθu
  set Dc : ℝ := 100 * (Cdec + 1) + 100 * (Cdec + 1) / (α * z₁)
      + 100 * (Cdec + 1) / (α ^ 2 * z₁ ^ 2) + 100 * (Cdec + 1) / (Real.cos θu) ^ 2 + 1 with hDc
  have hP1 : 0 < 100 * (Cdec + 1) := by positivity
  have hP2 : 0 < 100 * (Cdec + 1) / (α * z₁) := by positivity
  have hP3 : 0 < 100 * (Cdec + 1) / (α ^ 2 * z₁ ^ 2) := by positivity
  have hP4 : 0 < 100 * (Cdec + 1) / (Real.cos θu) ^ 2 := by positivity
  have hDc_pos : 0 < Dc := by rw [hDc]; linarith
  have hDcA : 100 * (Cdec + 1) ≤ Dc := by rw [hDc]; linarith [hP1, hP2, hP3, hP4]
  have hDcB : 100 * (Cdec + 1) / (α * z₁) ≤ Dc := by rw [hDc]; linarith [hP1, hP2, hP3, hP4]
  have hDcC : 100 * (Cdec + 1) / (α ^ 2 * z₁ ^ 2) ≤ Dc := by rw [hDc]; linarith [hP1, hP2, hP3, hP4]
  have hDcD : 100 * (Cdec + 1) / (Real.cos θu) ^ 2 ≤ Dc := by rw [hDc]; linarith [hP1, hP2, hP3, hP4]
  have hDc_ge1 : 100 * (Cdec + 1) ≤ Dc := by rw [hDc]; linarith
  have hmaj : ∀ D : ℝ, Summable fun m : ℕ => D * majPow m := by
    intro D
    simpa only [majPow] using Work.FTS.PhiStar.Series.Deleg.rpowMajorant.2.1 D
  have hac : ∀ m : ℕ, 1 ≤ m →
      (∀ y : ℝ, 0 < y → |acoeff α m G y| ≤ (Cdec / ((m : ℝ) + 1) ^ 5) / (m * (4 * (m : ℝ) + 5))) ∧
      (∀ y : ℝ, 0 < y → |deriv (acoeff α m G) y|
        ≤ 2 * (Cdec / ((m : ℝ) + 1) ^ 5) / (α * (4 * (m : ℝ) + 5) * z₁)) ∧
      (∀ y : ℝ, 0 < y → |deriv (deriv (acoeff α m G)) y|
        ≤ 10 * (Cdec / ((m : ℝ) + 1) ^ 5) / (α ^ 2 * z₁ ^ 2)) := by
    intro m hm1
    have hM0 : 0 ≤ Cdec / ((m : ℝ) + 1) ^ 5 := by positivity
    obtain ⟨b1, b2, b3⟩ := radGreenI_deriv_bounds_cpt (α := α) hα hα4 hm1 hM0 hz₁
      (hcm m) (hMdec m hm1) (hsuppcm m) (hinteg m ((2 * (m : ℝ) + 5) / α - 1) (Set.Ioo 0 1))
      (hinteg m (-(2 * (m : ℝ) / α) - 1) (Set.Ioi 1))
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      rw [show acoeff α m G y = Work.FTS.PhiStar.Radial.radGreenI α m
        (fun t => cmode m G t) y from rfl]
      exact b1 y hy
    · intro y hy
      rw [show deriv (acoeff α m G) y = rgiD1 α m (fun t => cmode m G t) y from
        (hasDerivAt_radGreenI (hcm m) (hinteg m ((2 * (m : ℝ) + 5) / α - 1) (Set.Ioo 0 1))
          (hinteg m (-(2 * (m : ℝ) / α) - 1) (Set.Ioi 1)) y hy).deriv]
      exact b2 y hy
    · intro y hy
      have hev : deriv (acoeff α m G) =ᶠ[𝓝 y] rgiD1 α m (fun t => cmode m G t) := by
        filter_upwards [isOpen_Ioi.mem_nhds hy] with w hw
        exact (hasDerivAt_radGreenI (hcm m) (hinteg m ((2 * (m : ℝ) + 5) / α - 1)
          (Set.Ioo 0 1)) (hinteg m (-(2 * (m : ℝ) / α) - 1) (Set.Ioi 1)) w hw).deriv
      rw [hev.deriv_eq]
      exact b3 y hy
  -- m = 0 facts
  have hz0 : ∀ y : ℝ, 0 < y → acoeff α 0 G y = 0 := fun y hy => acoeff_zero_of_fstar α G hFs y hy
  have hz1 : ∀ y : ℝ, 0 < y → deriv (acoeff α 0 G) y = 0 := by
    intro y hy
    have heq : acoeff α 0 G =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with w hw
      exact hz0 w hw
    rw [heq.deriv_eq, deriv_const]
  have hz2 : ∀ y : ℝ, 0 < y → deriv (deriv (acoeff α 0 G)) y = 0 := by
    intro y hy
    have heq : deriv (acoeff α 0 G) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with w hw
      exact hz1 w hw
    rw [heq.deriv_eq, deriv_const]
  have hEfam_bound : ∀ m : ℕ, |eFam m θ| ≤ 3 * ((m : ℝ) + 1) := fun m =>
    le_trans (abs_eFam_le_sqrt_Npsi m ⟨le_of_lt hθ, le_of_lt hθ2⟩) (sqrt_Npsi_le_three m)
  -- hB0
  have hB0 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |acoeff α m G y| * |eFam m θ| ≤ Dc * majPow m := by
    intro m y hy
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, hz0 y hy, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDc_pos) (majPow_nonneg 0)
    · have hm1 : 1 ≤ m := hmpos
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hden : (9 : ℝ) ≤ (m : ℝ) * (4 * (m : ℝ) + 5) := by nlinarith
      have h1 := (hac m hm1).1 y hy
      have h2 := hEfam_bound m
      have hK0 : 0 ≤ 3 * Cdec / (m * (4 * (m : ℝ) + 5)) := by positivity
      have hK0D : 3 * Cdec / (m * (4 * (m : ℝ) + 5)) ≤ Dc := by
        have hs1 := div_le_div_of_le_denom (N := 3 * Cdec)
          (D := (m : ℝ) * (4 * (m : ℝ) + 5)) (d := 9) (by positivity) (by norm_num) hden
        have hs2 : 3 * Cdec / 9 ≤ 100 * (Cdec + 1) := by
          rw [show 3 * Cdec / 9 = Cdec / 3 from by ring]
          nlinarith [hCdec0]
        linarith [hs1, hs2, hDcA]
      refine le_trans ?_ (final_le (m := m) (k := 4) hK0 hK0D (by norm_num) hm1)
      calc |acoeff α m G y| * |eFam m θ|
          ≤ ((Cdec / ((m : ℝ) + 1) ^ 5) / (m * (4 * (m : ℝ) + 5))) * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (3 * Cdec / (m * (4 * (m : ℝ) + 5))) * (((m : ℝ) + 1) ^ 4)⁻¹ := by
            have hx0 : ((m : ℝ) + 1) ≠ 0 := by positivity
            have hm0' : (m : ℝ) ≠ 0 := by linarith
            have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by linarith
            field_simp; try ring
  -- hB1
  have hB1 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |deriv (acoeff α m G) y| * |eFam m θ| ≤ Dc * majPow m := by
    intro m y hy
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, hz1 y hy, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDc_pos) (majPow_nonneg 0)
    · have hm1 : 1 ≤ m := hmpos
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hαz : 0 < α * z₁ := mul_pos hα hz₁
      have h1 := (hac m hm1).2.1 y hy
      have h2 := hEfam_bound m
      have hK1 : 0 ≤ 6 * Cdec / (α * (4 * (m : ℝ) + 5) * z₁) := by positivity
      have hK1D : 6 * Cdec / (α * (4 * (m : ℝ) + 5) * z₁) ≤ Dc := by
        have h45 : (1 : ℝ) ≤ 4 * (m : ℝ) + 5 := by linarith
        have hD1 : α * z₁ ≤ α * (4 * (m : ℝ) + 5) * z₁ := by nlinarith [h45, hαz]
        have hs1 := div_le_div_of_le_denom (N := 6 * Cdec)
          (D := α * (4 * (m : ℝ) + 5) * z₁) (d := α * z₁) (by positivity) hαz hD1
        have hs2 := div_le_div_of_le_num (N := 6 * Cdec) (n := 100 * (Cdec + 1))
          (d := α * z₁) (by nlinarith [hCdec0]) hαz
        linarith [hs1, hs2, hDcB]
      refine le_trans ?_ (final_le (m := m) (k := 4) hK1 hK1D (by norm_num) hm1)
      calc |deriv (acoeff α m G) y| * |eFam m θ|
          ≤ (2 * (Cdec / ((m : ℝ) + 1) ^ 5) / (α * (4 * (m : ℝ) + 5) * z₁))
              * (3 * ((m : ℝ) + 1)) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (6 * Cdec / (α * (4 * (m : ℝ) + 5) * z₁)) * (((m : ℝ) + 1) ^ 4)⁻¹ := by
            have hx0 : ((m : ℝ) + 1) ≠ 0 := by positivity
            have hα0 : α ≠ 0 := ne_of_gt hα
            have hz10 : z₁ ≠ 0 := ne_of_gt hz₁
            have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by linarith
            field_simp; try ring
  -- hB2
  have hB2 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |deriv (deriv (acoeff α m G)) y| * |eFam m θ| ≤ Dc * majPow m := by
    intro m y hy
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, hz2 y hy, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDc_pos) (majPow_nonneg 0)
    · have hm1 : 1 ≤ m := hmpos
      have h1 := (hac m hm1).2.2 y hy
      have h2 := hEfam_bound m
      have hK2 : 0 ≤ 30 * Cdec / (α ^ 2 * z₁ ^ 2) := by positivity
      have hK2D : 30 * Cdec / (α ^ 2 * z₁ ^ 2) ≤ Dc := by
        have hs := div_le_div_of_le_num (N := 30 * Cdec) (n := 100 * (Cdec + 1))
          (d := α ^ 2 * z₁ ^ 2) (by nlinarith [hCdec0]) (by positivity)
        linarith [hs, hDcC]
      refine le_trans ?_ (final_le (m := m) (k := 4) hK2 hK2D (by norm_num) hm1)
      calc |deriv (deriv (acoeff α m G)) y| * |eFam m θ|
          ≤ (10 * (Cdec / ((m : ℝ) + 1) ^ 5) / (α ^ 2 * z₁ ^ 2)) * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (30 * Cdec / (α ^ 2 * z₁ ^ 2)) * (((m : ℝ) + 1) ^ 4)⁻¹ := by
            have hx0 : ((m : ℝ) + 1) ≠ 0 := by positivity
            have hα0 : α ≠ 0 := ne_of_gt hα
            have hz10 : z₁ ≠ 0 := ne_of_gt hz₁
            field_simp; try ring
  -- hB3
  have hB3 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + Real.pi / 2) / 2 →
      |acoeff α m G z| * |deriv (eFam m) y| ≤ Dc * majPow m := by
    intro m y hy hyu
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, hz0 z hz, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDc_pos) (majPow_nonneg 0)
    · have hm1 : 1 ≤ m := hmpos
      have hyu' : y ≤ θu := by rw [hθu]; exact hyu
      have hy2 : y < Real.pi / 2 := lt_of_le_of_lt hyu' hθu_lt
      have hcosy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy2⟩
      have hcosle : Real.cos θu ≤ Real.cos y :=
        Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hy) (by linarith [hθu_lt, Real.pi_pos]) hyu'
      have h1 := (hac m hm1).1 z hz
      have h2 := abs_deriv_eFam_le m hy hy2
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hden : (9 : ℝ) ≤ (m : ℝ) * (4 * (m : ℝ) + 5) := by nlinarith
      have hK3 : 0 ≤ 12 * Cdec / (m * (4 * (m : ℝ) + 5) * Real.cos θu) := by positivity
      have hK3D : 12 * Cdec / (m * (4 * (m : ℝ) + 5) * Real.cos θu) ≤ Dc := by
        have hD1 : Real.cos θu ≤ (m : ℝ) * (4 * (m : ℝ) + 5) * Real.cos θu := by
          nlinarith [hden, hcθu]
        have hs1 := div_le_div_of_le_denom (N := 12 * Cdec)
          (D := (m : ℝ) * (4 * (m : ℝ) + 5) * Real.cos θu) (d := Real.cos θu)
          (by positivity) hcθu hD1
        have hD2 : (Real.cos θu) ^ 2 ≤ Real.cos θu := by
          nlinarith [hcθu, Real.cos_le_one θu]
        have hs2 := div_le_div_of_le_denom (N := 12 * Cdec) (D := Real.cos θu)
          (d := (Real.cos θu) ^ 2) (by positivity) (pow_pos hcθu 2) hD2
        have hs3 := div_le_div_of_le_num (N := 12 * Cdec) (n := 100 * (Cdec + 1))
          (d := (Real.cos θu) ^ 2) (by nlinarith [hCdec0]) (pow_pos hcθu 2)
        linarith [hs1, hs2, hs3, hDcD]
      refine le_trans ?_ (final_le (m := m) (k := 3) hK3 hK3D (by norm_num) hm1)
      calc |acoeff α m G z| * |deriv (eFam m) y|
          ≤ ((Cdec / ((m : ℝ) + 1) ^ 5) / (m * (4 * (m : ℝ) + 5)))
              * (12 * ((m : ℝ) + 1) ^ 2 / Real.cos y) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ ((Cdec / ((m : ℝ) + 1) ^ 5) / (m * (4 * (m : ℝ) + 5)))
              * (12 * ((m : ℝ) + 1) ^ 2 / Real.cos θu) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [div_le_div_iff₀ hcosy hcθu]
            nlinarith [hcosle, hcθu, hcosy]
        _ = (12 * Cdec / (m * (4 * (m : ℝ) + 5) * Real.cos θu))
              * (((m : ℝ) + 1) ^ 3)⁻¹ := by
            have hx0 : ((m : ℝ) + 1) ≠ 0 := by positivity
            have hm0' : (m : ℝ) ≠ 0 := by linarith
            have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by linarith
            have hc0 : Real.cos θu ≠ 0 := ne_of_gt hcθu
            field_simp; try ring
  -- hB4
  have hB4 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + Real.pi / 2) / 2 →
      |acoeff α m G z| * |iteratedDeriv 2 (eFam m) y| ≤ Dc * majPow m := by
    intro m y hy hyu
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, hz0 z hz, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDc_pos) (majPow_nonneg 0)
    · have hm1 : 1 ≤ m := hmpos
      have hyu' : y ≤ θu := by rw [hθu]; exact hyu
      have hy2 : y < Real.pi / 2 := lt_of_le_of_lt hyu' hθu_lt
      have hcosy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy2⟩
      have hcosle : Real.cos θu ≤ Real.cos y :=
        Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hy) (by linarith [hθu_lt, Real.pi_pos]) hyu'
      have h1 := (hac m hm1).1 z hz
      have h2 := abs_iteratedDeriv2_eFam_le m hy hy2
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hden : (9 : ℝ) ≤ (m : ℝ) * (4 * (m : ℝ) + 5) := by nlinarith
      have hK4 : 0 ≤ 100 * Cdec / (m * (4 * (m : ℝ) + 5) * (Real.cos θu) ^ 2) := by positivity
      have hK4D : 100 * Cdec / (m * (4 * (m : ℝ) + 5) * (Real.cos θu) ^ 2) ≤ Dc := by
        have hD1 : (Real.cos θu) ^ 2 ≤ (m : ℝ) * (4 * (m : ℝ) + 5) * (Real.cos θu) ^ 2 := by
          nlinarith [hden, hcθu]
        have hs1 := div_le_div_of_le_denom (N := 100 * Cdec)
          (D := (m : ℝ) * (4 * (m : ℝ) + 5) * (Real.cos θu) ^ 2) (d := (Real.cos θu) ^ 2)
          (by positivity) (pow_pos hcθu 2) hD1
        have hs2 := div_le_div_of_le_num (N := 100 * Cdec) (n := 100 * (Cdec + 1))
          (d := (Real.cos θu) ^ 2) (by nlinarith [hCdec0]) (pow_pos hcθu 2)
        linarith [hs1, hs2, hDcD]
      refine le_trans ?_ (final_le (m := m) (k := 2) hK4 hK4D (by norm_num) hm1)
      calc |acoeff α m G z| * |iteratedDeriv 2 (eFam m) y|
          ≤ ((Cdec / ((m : ℝ) + 1) ^ 5) / (m * (4 * (m : ℝ) + 5)))
              * (100 * ((m : ℝ) + 1) ^ 3 / (Real.cos y) ^ 2) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ ((Cdec / ((m : ℝ) + 1) ^ 5) / (m * (4 * (m : ℝ) + 5)))
              * (100 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hcs2 : (Real.cos θu) ^ 2 ≤ (Real.cos y) ^ 2 :=
              pow_le_pow_left₀ (le_of_lt hcθu) hcosle 2
            rw [div_le_div_iff₀ (pow_pos hcosy 2) (pow_pos hcθu 2)]
            exact mul_le_mul_of_nonneg_left hcs2 (by positivity)
        _ = (100 * Cdec / (m * (4 * (m : ℝ) + 5) * (Real.cos θu) ^ 2))
              * (((m : ℝ) + 1) ^ 2)⁻¹ := by
            have hx0 : ((m : ℝ) + 1) ≠ 0 := by positivity
            have hm0' : (m : ℝ) ≠ 0 := by linarith
            have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by linarith
            have hc0 : Real.cos θu ≠ 0 := ne_of_gt hcθu
            field_simp; try ring
  -- hB5
  have hB5 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + Real.pi / 2) / 2 →
      |acoeff α m G z| * |deriv (fun θ' => Real.tan θ' * eFam m θ') y| ≤ Dc * majPow m := by
    intro m y hy hyu
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, hz0 z hz, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDc_pos) (majPow_nonneg 0)
    · have hm1 : 1 ≤ m := hmpos
      have hyu' : y ≤ θu := by rw [hθu]; exact hyu
      have hy2 : y < Real.pi / 2 := lt_of_le_of_lt hyu' hθu_lt
      have hcosy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy2⟩
      have hcosle : Real.cos θu ≤ Real.cos y :=
        Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hy) (by linarith [hθu_lt, Real.pi_pos]) hyu'
      have h1 := (hac m hm1).1 z hz
      have h2 := abs_deriv_tan_eFam_le m hy hy2
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hden : (9 : ℝ) ≤ (m : ℝ) * (4 * (m : ℝ) + 5) := by nlinarith
      have hK5 : 0 ≤ 20 * Cdec / (m * (4 * (m : ℝ) + 5) * (Real.cos θu) ^ 2) := by positivity
      have hK5D : 20 * Cdec / (m * (4 * (m : ℝ) + 5) * (Real.cos θu) ^ 2) ≤ Dc := by
        have hD1 : (Real.cos θu) ^ 2 ≤ (m : ℝ) * (4 * (m : ℝ) + 5) * (Real.cos θu) ^ 2 := by
          nlinarith [hden, hcθu]
        have hs1 := div_le_div_of_le_denom (N := 20 * Cdec)
          (D := (m : ℝ) * (4 * (m : ℝ) + 5) * (Real.cos θu) ^ 2) (d := (Real.cos θu) ^ 2)
          (by positivity) (pow_pos hcθu 2) hD1
        have hs2 := div_le_div_of_le_num (N := 20 * Cdec) (n := 100 * (Cdec + 1))
          (d := (Real.cos θu) ^ 2) (by nlinarith [hCdec0]) (pow_pos hcθu 2)
        linarith [hs1, hs2, hDcD]
      refine le_trans ?_ (final_le (m := m) (k := 3) hK5 hK5D (by norm_num) hm1)
      calc |acoeff α m G z| * |deriv (fun θ' => Real.tan θ' * eFam m θ') y|
          ≤ ((Cdec / ((m : ℝ) + 1) ^ 5) / (m * (4 * (m : ℝ) + 5)))
              * (20 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 2) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ ((Cdec / ((m : ℝ) + 1) ^ 5) / (m * (4 * (m : ℝ) + 5)))
              * (20 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hcs2 : (Real.cos θu) ^ 2 ≤ (Real.cos y) ^ 2 :=
              pow_le_pow_left₀ (le_of_lt hcθu) hcosle 2
            rw [div_le_div_iff₀ (pow_pos hcosy 2) (pow_pos hcθu 2)]
            exact mul_le_mul_of_nonneg_left hcs2 (by positivity)
        _ = (20 * Cdec / (m * (4 * (m : ℝ) + 5) * (Real.cos θu) ^ 2))
              * (((m : ℝ) + 1) ^ 3)⁻¹ := by
            have hx0 : ((m : ℝ) + 1) ≠ 0 := by positivity
            have hm0' : (m : ℝ) ≠ 0 := by linarith
            have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by linarith
            have hc0 : Real.cos θu ≠ 0 := ne_of_gt hcθu
            field_simp; try ring
  -- the termwise differentiation
  obtain ⟨hPz, hPz2, hPt, hPt2, hPtan, hLzero⟩ :=
    Work.FTS.ClassC.deriv_series_general α G hα
      ⟨hcm, (fun m => hinteg m ((2 * (m : ℝ) + 5) / α - 1) (Set.Ioo 0 1)),
       (fun m => hinteg m (-(2 * (m : ℝ) / α) - 1) (Set.Ioi 1))⟩
      hmaj z hz θ hθ hθ2 Dc hB0 hB1 hB2 hB3 hB4 hB5
  -- the modewise identity
  have hpoint : ∀ m : ℕ,
      (-(α ^ 2 * z ^ 2)) * (deriv (deriv (acoeff α m G)) z * eFam m θ)
        + (-(α * (5 + α) * z)) * (deriv (acoeff α m G) z * eFam m θ)
        + ((-1) * (acoeff α m G z * iteratedDeriv 2 (eFam m) θ)
            + 1 * (acoeff α m G z * deriv (fun θ' => Real.tan θ' * eFam m θ') θ)
            + (-6) * (acoeff α m G z * eFam m θ))
      = cmode m G z * eFam m θ := by
    intro m
    have hODE : -α ^ 2 * z ^ 2 * deriv (deriv (acoeff α m G)) z
        - α * (5 + α) * z * deriv (acoeff α m G) z
        + Work.FTS.PhiStar.Radial.lamR m * acoeff α m G z = cmode m G z :=
      Work.FTS.PhiStar.Radial.radGreen_solves (α := α) hα m (hcm m)
        (hinteg m ((2 * (m : ℝ) + 5) / α - 1) (Set.Ioo 0 1))
        (hinteg m (-(2 * (m : ℝ) / α) - 1) (Set.Ioo 0 1))
        (hinteg m (-(2 * (m : ℝ) / α) - 1) (Set.Ioi 1)) z hz
    have hLam : -iteratedDeriv 2 (eFam m) θ
        + deriv (fun θ' => Real.tan θ' * eFam m θ') θ - 6 * eFam m θ
        = lam m * eFam m θ := by
      have h := Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hcosθ z
      rw [Work.Elliptic.Lzero_eq_deriv] at h
      rw [iteratedDeriv_two_apply]
      linarith
    have hlam : Work.FTS.PhiStar.Radial.lamR m = lam m := rfl
    rw [← hlam] at hLam
    linear_combination (eFam m θ) * hODE + (acoeff α m G z) * hLam
  -- summability of the five families
  have hsum_of : ∀ (E : ℝ) (f : ℕ → ℝ), (∀ m, |f m| ≤ E * majPow m) → Summable f := by
    intro E f hf
    refine Summable.of_norm_bounded (hmaj E) fun m => ?_
    rw [Real.norm_eq_abs]
    exact hf m
  have hsumF1 : Summable fun m : ℕ => deriv (deriv (acoeff α m G)) z * eFam m θ :=
    hsum_of Dc _ (fun m => by rw [abs_mul]; exact hB2 m z hz)
  have hsumF2 : Summable fun m : ℕ => deriv (acoeff α m G) z * eFam m θ :=
    hsum_of Dc _ (fun m => by rw [abs_mul]; exact hB1 m z hz)
  have hsumF3 : Summable fun m : ℕ => acoeff α m G z * iteratedDeriv 2 (eFam m) θ :=
    hsum_of Dc _ (fun m => by rw [abs_mul]; exact hB4 m θ hθ hθu_le)
  have hsumF4 : Summable fun m : ℕ =>
      acoeff α m G z * deriv (fun θ' => Real.tan θ' * eFam m θ') θ :=
    hsum_of Dc _ (fun m => by rw [abs_mul]; exact hB5 m θ hθ hθu_le)
  have hsumF5 : Summable fun m : ℕ => acoeff α m G z * eFam m θ :=
    hsum_of Dc _ (fun m => by rw [abs_mul]; exact hB0 m z hz)
  have hnorm : (-(α ^ 2 * z ^ 2)) * (∑' m : ℕ,
        deriv (deriv (acoeff α m G)) z * eFam m θ)
      - (α * (5 + α) * z) * (∑' m : ℕ, deriv (acoeff α m G) z * eFam m θ)
      + (-(∑' m : ℕ, acoeff α m G z * iteratedDeriv 2 (eFam m) θ)
          + (∑' m : ℕ, acoeff α m G z * deriv (fun θ' => Real.tan θ' * eFam m θ') θ)
          - 6 * (∑' m : ℕ, acoeff α m G z * eFam m θ))
    = (-(α ^ 2 * z ^ 2)) * (∑' m : ℕ, deriv (deriv (acoeff α m G)) z * eFam m θ)
      + (-(α * (5 + α) * z)) * (∑' m : ℕ, deriv (acoeff α m G) z * eFam m θ)
      + ((-1) * (∑' m : ℕ, acoeff α m G z * iteratedDeriv 2 (eFam m) θ)
          + 1 * (∑' m : ℕ, acoeff α m G z * deriv (fun θ' => Real.tan θ' * eFam m θ') θ)
          + (-6) * (∑' m : ℕ, acoeff α m G z * eFam m θ)) := by ring
  -- the expansion of the source
  have hcontψ : ContinuousOn (fun θ' : ℝ => G z θ') Work.Spaces.Iθ :=
    (hG.slice_contDiff z 0).continuous.continuousOn
  have hmomψ : (∫ θ' in Work.Spaces.Iθ, (fun θ' : ℝ => G z θ') θ'
      * Work.Elliptic.sinCos2 θ') = 0 := by
    simpa only [Work.Elliptic.Fstar] using hFs z hz
  have hsupψ : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |eFam m θ'| ≤ C * ((m : ℝ) + 1) :=
    ⟨3, by norm_num, fun m θ' hθ' =>
      le_trans (abs_eFam_le_sqrt_Npsi m hθ') (sqrt_Npsi_le_three m)⟩
  have hdecψ : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m (fun θ' => G z θ')| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
    refine ⟨Cdec + 1, by linarith, fun m hm => ?_⟩
    have hbm : bmode m (fun θ' => G z θ') = cmode m G z := rfl
    rw [hbm]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hstep : (Cdec : ℝ) / ((m : ℝ) + 1) ^ 5
        ≤ (Cdec + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
      have hpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
      have h1 : ((m : ℝ) + 1) ^ (5 / 2 : ℝ) ≤ ((m : ℝ) + 1) ^ 5 := by
        rw [← Real.rpow_natCast ((m : ℝ) + 1) 5]
        exact Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      have h2 : (((m : ℝ) + 1) ^ 5)⁻¹ ≤ (((m : ℝ) + 1) ^ (5 / 2 : ℝ))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hpos (5 / 2)) h1
      rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hpos)]
      calc Cdec * (((m : ℝ) + 1) ^ 5)⁻¹
          ≤ Cdec * (((m : ℝ) + 1) ^ (5 / 2 : ℝ))⁻¹ := mul_le_mul_of_nonneg_left h2 hCdec0
        _ ≤ (Cdec + 1) * (((m : ℝ) + 1) ^ (5 / 2 : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc |cmode m G z| ≤ Cdec / ((m : ℝ) + 1) ^ 5 := hMdec m hm z
      _ ≤ (Cdec + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := hstep
  have hexp := tsum_bmode_eFam_eq_of_continuous α (fun θ' : ℝ => G z θ') hα hcontψ hmomψ
    hsupψ hdecψ θ hθ hθ2
  rw [Work.Elliptic.bslOp_apply, hLzero, hPz2, hPz, hPt2, hPtan,
    show psiSeries α G z θ = ∑' m : ℕ, acoeff α m G z * eFam m θ from rfl,
    hnorm,
    Work.FTS.PhiStar.Series.tsum_lincomb5 (-(α ^ 2 * z ^ 2)) (-(α * (5 + α) * z)) (-1) 1 (-6)
      (fun m => deriv (deriv (acoeff α m G)) z * eFam m θ)
      (fun m => deriv (acoeff α m G) z * eFam m θ)
      (fun m => acoeff α m G z * iteratedDeriv 2 (eFam m) θ)
      (fun m => acoeff α m G z * deriv (fun θ' => Real.tan θ' * eFam m θ') θ)
      (fun m => acoeff α m G z * eFam m θ)
      hsumF1 hsumF2 hsumF3 hsumF4 hsumF5,
    tsum_congr hpoint]
  have hfuneq : (fun m : ℕ => cmode m G z * eFam m θ)
      = fun m : ℕ => bmode m (fun θ' => G z θ') * eFam m θ := rfl
  rw [hfuneq]
  exact hexp

end Work.FTS.PhiStar.Honesty
