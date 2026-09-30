import Mathlib
import Submission.Work.BMF.N7.vk_interface
import Submission.Work.BMF.VKStripDefs
import Submission.Work.BMF.V4prelim
import Submission.Work.BMF.vk_L_lower
import Submission.Work.BMF.vk_L_upper
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# V4: logarithmic derivative of `L(s, χ)` in the Vinogradov–Korobov region (exponent `6/7`)

This file proves node **V4** of the `N10` chain, stated conditionally on the growth bound
`VKGrowth A c` (node V2) and on the zero-free region `ZFVKN7` (node V3).

The argument is the Landau / Borel–Carathéodory disc argument of
`Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic`:

* let `δ = cL / D` with `D = (log(|t|+3))^{6/7} · (log(N+2) + log log(|t|+3))`, and take the disc
  centred at `cc = max σ (1+δ) + it` of radius `R = 3δ`;
* every point `w` of the disc has `Re w > 1 - 2δ` and `|Im w - t| ≤ 1`, hence `|Im w| ≥ 3` and
  `D(N, Im w) ≤ 4 D`: the disc is zero-free (by `hzf`) and lies in the growth range of `hgr`;
* `‖L(w,χ)‖ ≤ M := max 2 (A·N·(2 log(|t|+3))^{6/7})` on the disc (either by `hgr`, or — where
  `Re w > 2` — by `vk_L_upper` and `ζ(σ) ≤ 1 + 1/(σ-1)`), and `‖L(cc,χ)‖ ≥ δ/2` by the
  Euler-product lower bound `vk_L_lower` at `cc.re ≥ 1 + δ`;
* Borel–Carathéodory then bounds `‖L'/L(z₀)‖` in terms of `log(2M) - log m`, `‖z₀-cc‖`, `R`.

The only exponent-dependent inputs (`2^{6/7} ≤ 2`, `x^{6/7} ≤ x` for `x ≥ 1`, monotonicity of
`x ↦ x^{-6/7}`) hold because `0 < 6/7 < 1`.
-/

namespace Work.BMF.N7

open Complex Metric
open scoped Topology

set_option maxHeartbeats 8000000

/-- The Vinogradov–Korobov denominator of exponent `6/7`:
`D(N,t) = (log(|t|+3))^{6/7} · (log(N+2) + log log(|t|+3))`. -/
private noncomputable def VKD67 (N : ℕ) (t : ℝ) : ℝ :=
  Work.BMF.VKA t ^ (6 / 7 : ℝ) * Work.BMF.VKE N t

private lemma VKD67_eq' (N : ℕ) (t : ℝ) :
    VKD67 N t = Work.BMF.VKA t ^ (6 / 7 : ℝ) * Work.BMF.VKE N t := rfl

private lemma VKD67_eq (N : ℕ) (t : ℝ) :
    VKD67 N t = Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
      (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3))) := by
  rw [VKD67_eq', Work.BMF.VKA_eq, Work.BMF.VKE_eq]

private lemma one_le_VKD67 (N : ℕ) [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) :
    1 ≤ VKD67 N t := by
  rw [VKD67_eq']
  have h1 : (1 : ℝ) ≤ Work.BMF.VKA t ^ (6 / 7 : ℝ) :=
    Real.one_le_rpow (Work.BMF.one_le_VKA ht) (by norm_num)
  have h2 : (1 : ℝ) ≤ Work.BMF.VKE N t := Work.BMF.one_le_VKE N ht
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ Work.BMF.VKA t ^ (6 / 7 : ℝ) * Work.BMF.VKE N t :=
        mul_le_mul h1 h2 (by linarith) (Real.rpow_nonneg (Work.BMF.VKA_nonneg ht) _)

private lemma VKD67_pos (N : ℕ) [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) : 0 < VKD67 N t :=
  lt_of_lt_of_le zero_lt_one (one_le_VKD67 N ht)

private lemma VKD67_shift_le (N : ℕ) [NeZero N] {t v : ℝ} (ht : 4 ≤ |t|)
    (htv : |v - t| ≤ 1) : VKD67 N v ≤ 4 * VKD67 N t := by
  have hvt : 3 ≤ |v| := Work.BMF.three_le_abs_of_shift ht htv
  have hA : Work.BMF.VKA v ≤ 2 * Work.BMF.VKA t := Work.BMF.VKA_shift_le ht htv
  have hE : Work.BMF.VKE N v ≤ 2 * Work.BMF.VKE N t := Work.BMF.VKE_shift_le N ht htv
  have hAv : 0 ≤ Work.BMF.VKA v := (Work.BMF.VKA_pos hvt).le
  have hAt : 0 ≤ Work.BMF.VKA t := (Work.BMF.VKA_pos (by linarith)).le
  have hEv : 0 ≤ Work.BMF.VKE N v := (Work.BMF.VKE_pos N hvt).le
  have hEt : 0 ≤ Work.BMF.VKE N t := (Work.BMF.VKE_pos N (by linarith)).le
  have hpow : Work.BMF.VKA v ^ (6 / 7 : ℝ) ≤ (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ) :=
    Real.rpow_le_rpow hAv hA (by norm_num)
  have hmul : (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ) =
      (2 : ℝ) ^ (6 / 7 : ℝ) * Work.BMF.VKA t ^ (6 / 7 : ℝ) :=
    Real.mul_rpow (by norm_num) hAt
  have h2 : (2 : ℝ) ^ (6 / 7 : ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (y := (6 / 7 : ℝ)) (z := (1 : ℝ)) (by norm_num)
    simpa using h
  have hVt : 0 ≤ Work.BMF.VKA t ^ (6 / 7 : ℝ) * Work.BMF.VKE N t :=
    mul_nonneg (Real.rpow_nonneg hAt _) hEt
  rw [VKD67_eq', VKD67_eq']
  calc Work.BMF.VKA v ^ (6 / 7 : ℝ) * Work.BMF.VKE N v
      ≤ ((2 : ℝ) ^ (6 / 7 : ℝ) * Work.BMF.VKA t ^ (6 / 7 : ℝ)) *
          (2 * Work.BMF.VKE N t) := by
        refine mul_le_mul ?_ hE hEv (by positivity)
        rwa [hmul] at hpow
    _ = ((2 : ℝ) ^ (6 / 7 : ℝ) * 2) *
          (Work.BMF.VKA t ^ (6 / 7 : ℝ) * Work.BMF.VKE N t) := by ring
    _ ≤ 4 * (Work.BMF.VKA t ^ (6 / 7 : ℝ) * Work.BMF.VKE N t) := by
        refine mul_le_mul_of_nonneg_right ?_ hVt
        linarith

private lemma N_cast_one_le {N : ℕ} [NeZero N] : (1 : ℝ) ≤ (N : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)

/-- `log (|t|+3) ≥ 1` for `|t| ≥ 4`. -/
private lemma one_le_log_abs_add_three {t : ℝ} (ht : 4 ≤ |t|) :
    (1 : ℝ) ≤ Real.log (|t| + 3) := by
  have h : (3 : ℝ) ≤ |t| + 3 := by linarith [abs_nonneg t]
  exact le_trans Work.BMF.log_three_ge_one (Real.log_le_log (by norm_num) h)

/-- `L := log (N (|t|+3)) ≥ 1`. -/
private lemma one_le_log_N_mul {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    (1 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 3)) := by
  have h3 : (0 : ℝ) < |t| + 3 := by linarith [abs_nonneg t]
  have hle : |t| + 3 ≤ (N : ℝ) * (|t| + 3) := by
    nlinarith [N_cast_one_le (N := N), h3]
  exact le_trans (one_le_log_abs_add_three ht) (Real.log_le_log h3 hle)

private lemma log_N_le {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    Real.log (N : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 3)) := by
  have h3 : (0 : ℝ) < |t| + 3 := by linarith [abs_nonneg t]
  have hN : (1 : ℝ) ≤ (N : ℝ) := N_cast_one_le (N := N)
  exact Real.log_le_log (by linarith) (by nlinarith)

/-- `VKA t = log (|t|+3) ≤ L`. -/
private lemma VKA_le_L {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    Work.BMF.VKA t ≤ Real.log ((N : ℝ) * (|t| + 3)) := by
  rw [Work.BMF.VKA_eq]
  exact Real.log_le_log (by linarith [abs_nonneg t])
    (by nlinarith [N_cast_one_le (N := N), abs_nonneg t])

/-- `VKE N t ≤ 4L`. -/
private lemma VKE_le_four_L {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    Work.BMF.VKE N t ≤ 4 * Real.log ((N : ℝ) * (|t| + 3)) := by
  rw [Work.BMF.VKE_eq']
  set L : ℝ := Real.log ((N : ℝ) * (|t| + 3)) with hL
  have hL1 : 1 ≤ L := one_le_log_N_mul ht
  have hA1 : 1 ≤ Work.BMF.VKA t := Work.BMF.one_le_VKA (by linarith)
  have hlogN2 : Real.log ((N : ℝ) + 2) ≤ Real.log (3 * (N : ℝ)) :=
    Real.log_le_log (by linarith [N_cast_one_le (N := N)]) (by nlinarith [N_cast_one_le (N := N)])
  have hlog3 : Real.log (3 * (N : ℝ)) = Real.log 3 + Real.log (N : ℝ) :=
    Real.log_mul (by norm_num) (by linarith [N_cast_one_le (N := N)])
  have hlogN : Real.log (N : ℝ) ≤ L := by rw [hL]; exact log_N_le ht
  have hlogA : Real.log (Work.BMF.VKA t) ≤ Work.BMF.VKA t := Real.log_le_self (by linarith)
  have hA_L : Work.BMF.VKA t ≤ L := by rw [hL]; exact VKA_le_L ht
  have hlog3le : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  rw [hlog3] at hlogN2
  linarith

/-- `VKD67 N t ≤ 4L²`. -/
private lemma VKD67_le_four_L_sq {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    VKD67 N t ≤ 4 * (Real.log ((N : ℝ) * (|t| + 3))) ^ 2 := by
  rw [VKD67_eq']
  set L : ℝ := Real.log ((N : ℝ) * (|t| + 3)) with hL
  have hL1 : 1 ≤ L := one_le_log_N_mul ht
  have hA1 : 1 ≤ Work.BMF.VKA t := Work.BMF.one_le_VKA (by linarith)
  have hAnn : 0 ≤ Work.BMF.VKA t := by linarith
  have hpow : Work.BMF.VKA t ^ (6 / 7 : ℝ) ≤ Work.BMF.VKA t :=
    Real.rpow_le_self_of_one_le hA1 (by norm_num)
  have hE := VKE_le_four_L (N := N) ht
  have hAL : Work.BMF.VKA t ≤ L := by rw [hL]; exact VKA_le_L ht
  have hEnn : 0 ≤ Work.BMF.VKE N t := le_of_lt (Work.BMF.VKE_pos N (by linarith))
  calc Work.BMF.VKA t ^ (6 / 7 : ℝ) * Work.BMF.VKE N t
      ≤ Work.BMF.VKA t * Work.BMF.VKE N t := mul_le_mul_of_nonneg_right hpow hEnn
    _ ≤ L * (4 * L) := mul_le_mul hAL hE hEnn (by linarith)
    _ = 4 * L ^ 2 := by ring

/-- `log (VKD67 N t) ≤ 5L`. -/
private lemma log_VKD67_le {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    Real.log (VKD67 N t) ≤ 5 * Real.log ((N : ℝ) * (|t| + 3)) := by
  rw [VKD67_eq']
  set L : ℝ := Real.log ((N : ℝ) * (|t| + 3)) with hL
  have hL1 : 1 ≤ L := one_le_log_N_mul ht
  have hA1 : 1 ≤ Work.BMF.VKA t := Work.BMF.one_le_VKA (by linarith)
  have hApos : 0 < Work.BMF.VKA t := by linarith
  have hE1 : 1 ≤ Work.BMF.VKE N t := Work.BMF.one_le_VKE N (by linarith)
  have hEpos : 0 < Work.BMF.VKE N t := by linarith
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hApos _)) (ne_of_gt hEpos)]
  rw [Real.log_rpow hApos]
  have hlogA : Real.log (Work.BMF.VKA t) ≤ Work.BMF.VKA t := Real.log_le_self hApos.le
  have hlogE : Real.log (Work.BMF.VKE N t) ≤ Work.BMF.VKE N t := Real.log_le_self hEpos.le
  have hE4 := VKE_le_four_L (N := N) ht
  have hA_L : Work.BMF.VKA t ≤ L := by rw [hL]; exact VKA_le_L ht
  nlinarith

/-- **Euler-product lower bound at the centre of the disc.**  For `1 + y ≤ Re s`, `0 < y ≤ 1`,
`‖L(s,χ)‖ ≥ y/2`. -/
private lemma LFunction_lower_center {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hs : 1 + y ≤ s.re) :
    y / 2 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have hs1 : 1 < s.re := by linarith
  have hlow := Work.BMF.vk_L_lower χ (s := s) hs1
  have hZ := Work.BMF.riemannZeta_re_le_one_add_inv s.re hs1
  have hypos : 0 < s.re - 1 := by linarith
  have h1 : 1 / (s.re - 1) ≤ 1 / y := one_div_le_one_div_of_le hy (by linarith)
  have h2 : (riemannZeta ((s.re : ℝ) : ℂ)).re ≤ 1 + 1 / y := by linarith
  have hBpos : 0 < 1 + 1 / y := by positivity
  have h3 : 1 ≤ ‖DirichletCharacter.LFunction χ s‖ * (1 + 1 / y) := by
    calc (1 : ℝ) ≤ ‖DirichletCharacter.LFunction χ s‖ * (riemannZeta ((s.re : ℝ) : ℂ)).re := hlow
      _ ≤ ‖DirichletCharacter.LFunction χ s‖ * (1 + 1 / y) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have h4 : 1 / (1 + 1 / y) ≤ ‖DirichletCharacter.LFunction χ s‖ := by
    rw [div_le_iff₀ hBpos]
    simpa using h3
  have h5 : y / (1 + y) ≤ 1 / (1 + 1 / y) := by
    have h : 1 / (1 + 1 / y) = y / (1 + y) := by
      field_simp
      ring
    rw [h]
  have h6 : y / 2 ≤ y / (1 + y) :=
    div_le_div_of_nonneg_left hy.le (by linarith) (by linarith)
  linarith

/-- **V4 (conditional on V2 and V3): logarithmic derivative in the Vinogradov–Korobov
region.**  Route (DESIGN.md, part V4): Borel–Carathéodory applied to `L(·,χ)` on the disc centred
at `max σ (1+δ) + it` of radius `3δ`, `δ = cL / D`, `D = (log(|t|+3))^{6/7}·VKE N t`; `hzf` makes
the disc zero-free, `hgr` bounds `L` on it, `vk_L_lower` bounds `L` below at the centre. -/
theorem logDeriv_LFunction_VK_of_growth_zf {A c : ℝ} (hgr : Work.BMF.VKGrowth A c)
    (hzf : Work.BMF.ZFVKN7) :
    ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → ∀ σ t : ℝ, 4 ≤ |t| →
        1 - c' / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ → σ ≤ 2 →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * Real.log ((N : ℝ) * (|t| + 3)) ^ 4 := by
  obtain ⟨c₃, hc₃, h₃⟩ := hzf
  obtain ⟨hAg, hc₂, h₂⟩ := hgr
  set cL : ℝ := min 1 (min c₃ c) / 16 with hcdef
  have hcpos : 0 < cL := by rw [hcdef]; positivity
  have hc1 : cL ≤ 1 / 16 := by
    rw [hcdef]
    have h : min 1 (min c₃ c) ≤ 1 := min_le_left _ _
    linarith
  have hcc₃ : 8 * cL ≤ c₃ := by
    have hle : min 1 (min c₃ c) ≤ c₃ := le_trans (min_le_right _ _) (min_le_left _ _)
    rw [hcdef]; linarith
  have hcc₂ : 4 * cL ≤ c := by
    have hle : min 1 (min c₃ c) ≤ c := le_trans (min_le_right _ _) (min_le_right _ _)
    rw [hcdef]; linarith
  set K₁ : ℝ := Real.log (16 * (1 + A)) + 2 with hK₁def
  set K₂ : ℝ := Real.log (1 / cL) + 6 with hK₂def
  have hK₁pos : 0 < K₁ := by
    rw [hK₁def]
    have : 0 ≤ Real.log (16 * (1 + A)) := Real.log_nonneg (by linarith [hAg])
    linarith
  have hK₂pos : 0 < K₂ := by
    rw [hK₂def]
    have : 0 ≤ Real.log (1 / cL) := Real.log_nonneg (by rw [le_div_iff₀ hcpos]; linarith)
    linarith
  refine ⟨200 * (K₁ + K₂) / cL + 1, cL, ?_, hcpos, ?_⟩
  · positivity
  intro N _ χ hχprim σ t ht4 hσlo hσhi
  have ht3 : 3 ≤ |t| := by linarith
  set L : ℝ := Real.log ((N : ℝ) * (|t| + 3)) with hLdef
  set D : ℝ := VKD67 N t with hDdef
  set δ : ℝ := cL / D with hδdef
  set m : ℝ := δ / 2 with hmdef
  set R : ℝ := 3 * δ with hRdef
  set M : ℝ := max 2 (A * (N : ℝ) * (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ)) with hMdef
  set s₀ : ℝ := max σ (1 + δ) with hs₀def
  set cc : ℂ := (s₀ : ℂ) + (t : ℂ) * I with hccdef
  set z₀ : ℂ := (σ : ℂ) + (t : ℂ) * I with hz₀def
  have hL1 : 1 ≤ L := one_le_log_N_mul ht4
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hD1 : 1 ≤ D := by rw [hDdef]; exact one_le_VKD67 N ht3
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hD4 : D ≤ 4 * L ^ 2 := by
    rw [hDdef, hLdef]
    exact VKD67_le_four_L_sq ht4
  have hlogD : Real.log D ≤ 5 * L := by
    rw [hDdef, hLdef]
    exact log_VKD67_le ht4
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hcpos hDpos
  have hδnn : 0 ≤ δ := le_of_lt hδpos
  have hδone : δ ≤ 1 := by
    rw [hδdef, div_le_one hDpos]
    linarith [hc1, hD1]
  have hδsmall : 3 * δ ≤ 1 := by
    rw [hδdef, show 3 * (cL / D) = 3 * cL / D by ring, div_le_one hDpos]
    nlinarith [hc1, hD1]
  have hA1 : 1 ≤ Work.BMF.VKA t := Work.BMF.one_le_VKA ht3
  have hApos : 0 < Work.BMF.VKA t := Work.BMF.VKA_pos ht3
  have hM2 : 2 ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hMpos : 0 < M := by linarith
  have hmpos : 0 < m := by rw [hmdef]; linarith
  have hmone : m ≤ 1 := by rw [hmdef]; linarith
  have hmM : m ≤ M := by linarith
  have hRpos : 0 < R := by rw [hRdef]; linarith
  -- the target region condition, with the denominator identified as `D`
  have hσge : 1 - δ ≤ σ := by
    rw [hδdef]
    calc 1 - cL / D = 1 - cL / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
            (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) := by
          rw [hDdef, VKD67_eq]
      _ ≤ σ := hσlo
  -- ## geometry of the disc
  have hball : ∀ w : ℂ, w ∈ Metric.ball cc R →
      (1 - 2 * δ < w.re ∧ |w.im| ≤ |t| + 1 ∧ 3 ≤ |w.im|) := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hdist' : ‖w - cc‖ < 3 * δ := by rw [← hRdef]; exact hw
    have hre_le : w.re - s₀ ≤ ‖w - cc‖ := by
      have h := Complex.abs_re_le_norm (w - cc)
      have h2 : (w - cc).re = w.re - s₀ := by simp [hccdef]
      rw [h2] at h
      exact le_trans (le_abs_self _) h
    have hre_ge : s₀ - w.re ≤ ‖w - cc‖ := by
      have h := Complex.abs_re_le_norm (w - cc)
      have h2 : (w - cc).re = w.re - s₀ := by simp [hccdef]
      rw [h2] at h
      have h3 : -(w.re - s₀) ≤ ‖w - cc‖ := le_trans (neg_le_abs _) h
      linarith
    have him : |w.im - t| ≤ ‖w - cc‖ := by
      have h := Complex.abs_im_le_norm (w - cc)
      have h2 : (w - cc).im = w.im - t := by simp [hccdef]
      rwa [h2] at h
    have hs₀1 : 1 + δ ≤ s₀ := by rw [hs₀def]; exact le_max_right _ _
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · have h1 : |w.im| ≤ |w.im - t| + |t| := by
        calc |w.im| = |(w.im - t) + t| := by ring_nf
          _ ≤ |w.im - t| + |t| := abs_add_le _ _
      linarith
    · have h1 : |t| - |w.im| ≤ |t - w.im| := abs_sub_abs_le_abs_sub t w.im
      have h2 : |t - w.im| = |w.im - t| := abs_sub_comm _ _
      linarith
  have hshift : ∀ w : ℂ, w ∈ Metric.ball cc R → |w.im - t| ≤ 1 := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have him : |w.im - t| ≤ ‖w - cc‖ := by
      have h := Complex.abs_im_le_norm (w - cc)
      have h2 : (w - cc).im = w.im - t := by simp [hccdef]
      rwa [h2] at h
    linarith [hδsmall]
  -- ## zero-freeness of the disc
  have hzf : ∀ w ∈ Metric.ball cc R, DirichletCharacter.LFunction χ w ≠ 0 := by
    intro w hw
    obtain ⟨hwre, _, hwim_ge⟩ := hball w hw
    have hs := hshift w hw
    have hVKD : VKD67 N w.im ≤ 4 * D := by
      rw [hDdef]
      exact VKD67_shift_le N ht4 hs
    have hpos1 : 0 < VKD67 N w.im := VKD67_pos N hwim_ge
    have hle : c₃ / (4 * D) ≤ c₃ / VKD67 N w.im :=
      div_le_div_of_nonneg_left hc₃.le hpos1 hVKD
    have hbig : 2 * δ ≤ c₃ / (4 * D) := by
      rw [hδdef, show 2 * (cL / D) = 2 * cL / D by ring, div_le_div_iff₀ hDpos (by positivity)]
      nlinarith [hcc₃, hDpos]
    have hstep : 1 - c₃ / VKD67 N w.im ≤ w.re := by linarith
    have happ := h₃ N χ hχprim w.re w.im hwim_ge (by
      rw [← VKD67_eq]
      exact hstep)
    rwa [Complex.re_add_im w] at happ
  -- ## growth bound on the disc
  have hMbound : ∀ w ∈ Metric.ball cc R, ‖DirichletCharacter.LFunction χ w‖ ≤ M := by
    intro w hw
    obtain ⟨hwre, hwim_le, hwim_ge⟩ := hball w hw
    have hlog_le : Real.log (|w.im| + 3) ≤ 2 * Work.BMF.VKA t := by
      rw [Work.BMF.VKA_eq]
      have h2 : |w.im| + 3 ≤ (|t| + 3) ^ 2 := by nlinarith [hwim_le, abs_nonneg t]
      calc Real.log (|w.im| + 3) ≤ Real.log ((|t| + 3) ^ 2) :=
            Real.log_le_log (by linarith [abs_nonneg w.im]) h2
        _ = 2 * Real.log (|t| + 3) := by rw [Real.log_pow]; norm_num
    by_cases hcase : w.re ≤ 2
    · have hE1 : 1 ≤ Work.BMF.VKE N t := Work.BMF.one_le_VKE N ht3
      have hEpos : 0 < Work.BMF.VKE N t := lt_of_lt_of_le zero_lt_one hE1
      have hhalf : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(6 / 7 : ℝ)) := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (-1 : ℝ) ≤ -(6 / 7 : ℝ))
        have h2 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
        linarith [h, h2.le]
      have hA5pos : 0 < Work.BMF.VKA t ^ (6 / 7 : ℝ) := Real.rpow_pos_of_pos hApos _
      have hkey : 2 * δ ≤ c * Real.log (|w.im| + 3) ^ (-(6 / 7 : ℝ)) := by
        have hmono : (2 * Work.BMF.VKA t) ^ (-(6 / 7 : ℝ)) ≤
            Real.log (|w.im| + 3) ^ (-(6 / 7 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (Real.log_pos (by linarith [abs_nonneg w.im])) hlog_le
            (by norm_num)
        have hsplit : (2 * Work.BMF.VKA t) ^ (-(6 / 7 : ℝ)) =
            (2 : ℝ) ^ (-(6 / 7 : ℝ)) * (Work.BMF.VKA t) ^ (-(6 / 7 : ℝ)) := by
          rw [Real.mul_rpow (by norm_num) hApos.le]
        have hneg : (Work.BMF.VKA t) ^ (-(6 / 7 : ℝ)) =
            (Work.BMF.VKA t ^ (6 / 7 : ℝ))⁻¹ := Real.rpow_neg hApos.le _
        have hstep1 : 2 * δ ≤ 2 * cL / Work.BMF.VKA t ^ (6 / 7 : ℝ) := by
          rw [hδdef, hDdef, VKD67_eq',
            show 2 * (cL / (Work.BMF.VKA t ^ (6 / 7 : ℝ) * Work.BMF.VKE N t))
              = 2 * cL / (Work.BMF.VKA t ^ (6 / 7 : ℝ) * Work.BMF.VKE N t) by ring]
          exact div_le_div_of_nonneg_left (by positivity) hA5pos (by nlinarith [hE1, hA5pos])
        have hstep2 : 2 * cL / Work.BMF.VKA t ^ (6 / 7 : ℝ) ≤
            c * ((1 / 2) * (Work.BMF.VKA t ^ (6 / 7 : ℝ))⁻¹) := by
          rw [div_eq_mul_inv]
          have h1 : 2 * cL ≤ c * (1 / 2) := by linarith [hcc₂]
          have h2 : 0 ≤ (Work.BMF.VKA t ^ (6 / 7 : ℝ))⁻¹ := by positivity
          calc (2 * cL) * (Work.BMF.VKA t ^ (6 / 7 : ℝ))⁻¹
              ≤ (c * (1 / 2)) * (Work.BMF.VKA t ^ (6 / 7 : ℝ))⁻¹ :=
                mul_le_mul_of_nonneg_right h1 h2
            _ = c * ((1 / 2) * (Work.BMF.VKA t ^ (6 / 7 : ℝ))⁻¹) := by ring
        have hstep3 : c * ((1 / 2) * (Work.BMF.VKA t ^ (6 / 7 : ℝ))⁻¹) ≤
            c * ((2 : ℝ) ^ (-(6 / 7 : ℝ)) * (Work.BMF.VKA t) ^ (-(6 / 7 : ℝ))) := by
          have h2 : 0 ≤ (Work.BMF.VKA t ^ (6 / 7 : ℝ))⁻¹ := by positivity
          have h3 : (1 / 2) * (Work.BMF.VKA t ^ (6 / 7 : ℝ))⁻¹ ≤
              (2 : ℝ) ^ (-(6 / 7 : ℝ)) * (Work.BMF.VKA t) ^ (-(6 / 7 : ℝ)) := by
            rw [hneg]
            exact mul_le_mul_of_nonneg_right hhalf h2
          exact mul_le_mul_of_nonneg_left h3 hc₂.le
        have hstep4 : c * ((2 : ℝ) ^ (-(6 / 7 : ℝ)) * (Work.BMF.VKA t) ^ (-(6 / 7 : ℝ))) ≤
            c * Real.log (|w.im| + 3) ^ (-(6 / 7 : ℝ)) := by
          rw [← hsplit]
          exact mul_le_mul_of_nonneg_left hmono hc₂.le
        linarith
      have hgro : 1 - c * Real.log (|w.im| + 3) ^ (-(6 / 7 : ℝ)) ≤ w.re := by linarith
      have happ := h₂ N χ w.re w.im hwim_ge hgro hcase
      rw [Complex.re_add_im w] at happ
      refine le_trans happ ?_
      have hpow_mono : Real.log (|w.im| + 3) ^ (6 / 7 : ℝ) ≤
          (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith [abs_nonneg w.im])) hlog_le (by norm_num)
      have hstep : A * (N : ℝ) * Real.log (|w.im| + 3) ^ (6 / 7 : ℝ) ≤
          A * (N : ℝ) * (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ) := by
        have h1 : (0 : ℝ) ≤ A * (N : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hpow_mono h1
      exact le_trans hstep (le_max_right _ _)
    · have h1 : 1 < w.re := by
        have h2 : 2 < w.re := not_le.mp hcase
        linarith
      have hup := Work.BMF.vk_L_upper χ (s := w) h1
      have hz := Work.BMF.riemannZeta_re_le_one_add_inv w.re h1
      have h2 : (1 : ℝ) + 1 / (w.re - 1) ≤ 2 := by
        have h3 : 1 / (w.re - 1) ≤ 1 := by
          rw [div_le_one (by linarith : (0 : ℝ) < w.re - 1)]
          linarith
        linarith
      linarith [hup, hz, hM2]
  -- ## analyticity on the disc
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.ball cc R) := by
    have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.ball cc R) := by
      intro w hw
      have hwne : w ≠ 1 := by
        intro h1
        have h3 := (hball w hw).2.2
        rw [h1] at h3
        simp at h3
        linarith
      exact (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hwne)).differentiableWithinAt
    intro w hw
    exact hdiff.analyticAt (Metric.isOpen_ball.mem_nhds hw)
  -- ## the evaluation point
  have hdist : ‖z₀ - cc‖ ≤ 2 * δ := by
    have h1 : z₀ - cc = (((σ - s₀ : ℝ)) : ℂ) := by
      apply Complex.ext <;> simp [hz₀def, hccdef]
    have hσs₀ : σ - s₀ ≤ 0 := by
      have hσle : σ ≤ s₀ := by rw [hs₀def]; exact le_max_left _ _
      linarith
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hσs₀]
    rcases lt_or_ge σ (1 + δ) with h | h
    · have hs : s₀ = 1 + δ := by rw [hs₀def]; exact max_eq_right h.le
      rw [hs]; linarith
    · have hs : s₀ = σ := by rw [hs₀def]; exact max_eq_left h
      rw [hs]; linarith [hδpos]
  have hz0mem : z₀ ∈ Metric.ball cc R := by
    rw [Metric.mem_ball, dist_eq_norm, hRdef]
    linarith
  have hdist_lt : m < R - ‖z₀ - cc‖ := by
    rw [hRdef, hmdef]
    linarith
  -- ## the lower bound at the centre
  have hmlow : m ≤ ‖DirichletCharacter.LFunction χ cc‖ := by
    have hccre : cc.re = s₀ := by simp [hccdef]
    have h1 : 1 + δ ≤ cc.re := by rw [hccre]; exact le_max_right _ _
    have h := LFunction_lower_center χ (s := cc) (y := δ) hδpos hδone h1
    rw [hmdef]
    exact h
  refine ⟨?_, ?_⟩
  · -- non-vanishing at the point itself
    refine h₃ N χ hχprim σ t ht3 ?_
    have hden : 0 < Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3))) := by
      rw [← VKD67_eq]
      exact hDpos
    have hle : cL / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤
        c₃ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) := by
      rw [div_le_div_iff_of_pos_right hden]
      linarith [hcc₃]
    linarith
  · -- the logarithmic-derivative bound
    have hlog2M : Real.log (2 * M) ≤ K₁ * L := by
      have h2M : 2 * M ≤ 16 * (1 + A) * (N : ℝ) * L := by
        have hXnn : 0 ≤ A * (N : ℝ) * (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ) :=
          mul_nonneg (mul_nonneg hAg.le (by linarith [N_cast_one_le (N := N)]))
            (Real.rpow_nonneg (by positivity) _)
        have hmax : max 2 (A * (N : ℝ) * (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ)) ≤
            2 + A * (N : ℝ) * (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ) :=
          max_le (by linarith) (by linarith)
        have hpow_le : (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ) ≤ 2 * L := by
          rw [Real.mul_rpow (by norm_num) hApos.le]
          have h2 : (2 : ℝ) ^ (6 / 7 : ℝ) ≤ 2 := by
            have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
              (by norm_num : (6 / 7 : ℝ) ≤ 1)
            simpa using h
          have h3 : (Work.BMF.VKA t) ^ (6 / 7 : ℝ) ≤ Work.BMF.VKA t :=
            Real.rpow_le_self_of_one_le hA1 (by norm_num)
          have h4 : Work.BMF.VKA t ≤ L := by rw [hLdef]; exact VKA_le_L ht4
          have h5 : (0 : ℝ) ≤ (Work.BMF.VKA t) ^ (6 / 7 : ℝ) :=
            Real.rpow_nonneg hApos.le _
          nlinarith
        rw [hMdef]
        have h1 : A * (N : ℝ) * (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ) ≤
            A * (N : ℝ) * (2 * L) := by
          exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
        have h2 : A * (N : ℝ) * (2 * L) ≤ 4 * A * (N : ℝ) * L := by
          nlinarith [hAg, hL1, N_cast_one_le (N := N)]
        have hAgNL : 0 ≤ A * (N : ℝ) * L := by
          exact mul_nonneg (mul_nonneg hAg.le (by linarith [N_cast_one_le (N := N)]))
            (by linarith [hL1])
        have hNL1 : (1 : ℝ) ≤ (N : ℝ) * L := by nlinarith [N_cast_one_le (N := N), hL1]
        have h3 : (4 : ℝ) ≤ 16 * (N : ℝ) * L := by nlinarith [hNL1]
        have h4 : 4 * A * (N : ℝ) * L ≤ 16 * A * (N : ℝ) * L := by
          have := mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ) ≤ 16)
            (by positivity : (0:ℝ) ≤ A * (N : ℝ) * L)
          linarith [this]
        have h5 : 2 * (A * (N : ℝ) * (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ)) ≤
            4 * A * (N : ℝ) * L := by linarith [h1, h2]
        have h6 : 4 + 2 * (A * (N : ℝ) * (2 * Work.BMF.VKA t) ^ (6 / 7 : ℝ)) ≤
            16 * (1 + A) * (N : ℝ) * L := by
          have h7 : 16 * (1 + A) * (N : ℝ) * L =
              16 * (N : ℝ) * L + 16 * A * (N : ℝ) * L := by ring
          linarith [h3, h4, h7, h5]
        linarith [hmax, h6]
      have hpos2M : 0 < 2 * M := by linarith
      have hposR : 0 < 16 * (1 + A) * (N : ℝ) * L := by
        have h1 : 0 < 16 * (1 + A) := by linarith [hAg]
        have h2 : 0 < (N : ℝ) := by linarith [N_cast_one_le (N := N)]
        exact mul_pos (mul_pos h1 h2) hL0
      have hlogN : Real.log (N : ℝ) ≤ L := by rw [hLdef]; exact log_N_le ht4
      have hlogL : Real.log L ≤ L := Real.log_le_self (by linarith [hL1])
      have hlog16 : 0 ≤ Real.log (16 * (1 + A)) := Real.log_nonneg (by linarith [hAg])
      calc Real.log (2 * M) ≤ Real.log (16 * (1 + A) * (N : ℝ) * L) :=
            Real.log_le_log hpos2M h2M
        _ = Real.log (16 * (1 + A)) + Real.log (N : ℝ) + Real.log L := by
              have hNA : (16 * (1 + A) * (N : ℝ)) ≠ 0 :=
                mul_ne_zero (mul_ne_zero (by norm_num) (by linarith [hAg]))
                  (by linarith [N_cast_one_le (N := N)])
              have hLne : L ≠ 0 := by linarith [hL1]
              rw [Real.log_mul hNA hLne,
                Real.log_mul (mul_ne_zero (by norm_num) (by linarith [hAg]))
                  (by linarith [N_cast_one_le (N := N)])]
        _ ≤ K₁ * L := by
              rw [hK₁def]
              nlinarith
    have hlog1m : Real.log (1 / m) ≤ K₂ * L := by
      have hm2 : (1 : ℝ) / m = 2 * D / cL := by
        rw [hmdef, hδdef]; field_simp
      have hlog : Real.log (2 * D / cL) = Real.log 2 + Real.log D + Real.log (1 / cL) := by
        rw [show 2 * D / cL = 2 * D * (1 / cL) by ring]
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) (by positivity)]
      have hlogc : 0 ≤ Real.log (1 / cL) := Real.log_nonneg (by rw [le_div_iff₀ hcpos]; linarith)
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      rw [hm2, hlog, hK₂def]
      nlinarith [hlogD, hlogc, hlog2, hL1]
    have hsum_log : 2 * (Real.log (2 * M) - Real.log m) ≤ 2 * ((K₁ + K₂) * L) := by
      have hmpos' : 0 < m := hmpos
      have hinv : Real.log m = -Real.log (1 / m) := by
        rw [one_div, Real.log_inv, neg_neg]
      rw [hinv]
      linarith
    have hB : (‖z₀ - cc‖ + m) / ((R - ‖z₀ - cc‖ - m) * m) ≤ 10 / δ := by
      have hnum : ‖z₀ - cc‖ + m ≤ 2.5 * δ := by rw [hmdef]; linarith
      have hden : δ ^ 2 / 4 ≤ (R - ‖z₀ - cc‖ - m) * m := by
        rw [hRdef, hmdef] at *
        nlinarith [hdist, hδpos]
      have hc_nn : (0 : ℝ) ≤ 2.5 * δ := by linarith
      have hdpos : 0 < δ ^ 2 / 4 := by positivity
      calc (‖z₀ - cc‖ + m) / ((R - ‖z₀ - cc‖ - m) * m)
          ≤ (2.5 * δ) / (δ ^ 2 / 4) := div_le_div₀ hc_nn hnum hdpos hden
        _ = 10 / δ := by
              field_simp
              ring
    have hAnn : 0 ≤ 2 * (Real.log (2 * M) - Real.log m) := by
      have h1 : (1 : ℝ) ≤ 2 * M := by linarith [hM2]
      have h2 : (1 : ℝ) ≤ 1 / m := by
        rw [le_div_iff₀ hmpos]; linarith [hmone]
      have h3 : 0 ≤ Real.log (2 * M) := Real.log_nonneg h1
      have h4 : Real.log m = -Real.log (1 / m) := by rw [one_div, Real.log_inv, neg_neg]
      rw [h4]
      have h5 : 0 ≤ Real.log (1 / m) := Real.log_nonneg h2
      linarith
    have hBnn : 0 ≤ (‖z₀ - cc‖ + m) / ((R - ‖z₀ - cc‖ - m) * m) := by
      apply div_nonneg
      · linarith [norm_nonneg (z₀ - cc), hmpos]
      · have h1 : 0 < R - ‖z₀ - cc‖ - m := by linarith [hdist_lt]
        positivity
    have hdisk := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
        (g := DirichletCharacter.LFunction χ) (c := cc) (R := R) (m := m) (M := M)
        hRpos hmpos hmM han hzf hMbound hmlow (z₀ := z₀) hz0mem m hmpos hdist_lt
    have htarget : ‖logDeriv (DirichletCharacter.LFunction χ) z₀‖ ≤
        (200 * (K₁ + K₂) / cL + 1) * L ^ 4 := by
      calc ‖logDeriv (DirichletCharacter.LFunction χ) z₀‖
          = ‖deriv (DirichletCharacter.LFunction χ) z₀ / DirichletCharacter.LFunction χ z₀‖ := by
            rw [logDeriv_apply]
        _ ≤ 2 * (Real.log (2 * M) - Real.log m) * (‖z₀ - cc‖ + m) /
              ((R - ‖z₀ - cc‖ - m) * m) := hdisk
        _ = 2 * (Real.log (2 * M) - Real.log m) *
              ((‖z₀ - cc‖ + m) / ((R - ‖z₀ - cc‖ - m) * m)) := by rw [mul_div_assoc]
        _ ≤ 2 * ((K₁ + K₂) * L) * (10 / δ) :=
              mul_le_mul hsum_log hB hBnn (by
                have hKL : 0 ≤ K₁ + K₂ := by linarith
                exact mul_nonneg (by linarith) (by linarith))
        _ = 20 * (K₁ + K₂) * L / δ := by ring
        _ ≤ (200 * (K₁ + K₂) / cL + 1) * L ^ 4 := by
              have h1δ : (1 : ℝ) / δ = D / cL := by rw [hδdef]; field_simp
              rw [show 20 * (K₁ + K₂) * L / δ = 20 * (K₁ + K₂) * L * (1 / δ) by ring, h1δ]
              have h2 : 20 * (K₁ + K₂) * L * (D / cL) ≤ 20 * (K₁ + K₂) * L * (4 * L ^ 2 / cL) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact div_le_div_of_nonneg_right hD4 hcpos.le
              have h3 : 20 * (K₁ + K₂) * L * (4 * L ^ 2 / cL) =
                  80 * (K₁ + K₂) * L ^ 3 / cL := by ring
              rw [h3] at h2
              have hL3 : L ^ 3 ≤ L ^ 4 := by
                have h := mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ L ^ 3)
                simpa [pow_succ] using h
              have hKL : 0 ≤ K₁ + K₂ := by linarith
              have hcoef : 0 ≤ 80 * (K₁ + K₂) / cL :=
                div_nonneg (by linarith) hcpos.le
              have h5 : 80 * (K₁ + K₂) * L ^ 3 / cL = (80 * (K₁ + K₂) / cL) * L ^ 3 := by ring
              rw [h5] at h2
              have h6 : (80 * (K₁ + K₂) / cL) * L ^ 3 ≤ (80 * (K₁ + K₂) / cL) * L ^ 4 :=
                mul_le_mul_of_nonneg_left hL3 hcoef
              have h7 : (80 * (K₁ + K₂) / cL) * L ^ 4 ≤
                  (200 * (K₁ + K₂) / cL + 1) * L ^ 4 := by
                have h8 : 0 ≤ L ^ 4 := by positivity
                have h9 : 80 * (K₁ + K₂) / cL ≤ 200 * (K₁ + K₂) / cL := by
                  have hXc : 0 ≤ (K₁ + K₂) / cL := div_nonneg hKL hcpos.le
                  have ha : 80 * (K₁ + K₂) / cL = 80 * ((K₁ + K₂) / cL) := by ring
                  have hb : 200 * (K₁ + K₂) / cL = 200 * ((K₁ + K₂) / cL) := by ring
                  linarith
                have h10 : 80 * (K₁ + K₂) / cL ≤ 200 * (K₁ + K₂) / cL + 1 := by linarith
                exact mul_le_mul_of_nonneg_right h10 h8
              linarith [h2, h6, h7]
    rw [hz₀def] at htarget
    exact htarget

end Work.BMF.N7
