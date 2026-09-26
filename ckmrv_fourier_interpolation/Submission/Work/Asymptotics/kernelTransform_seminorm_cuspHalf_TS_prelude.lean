import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.CuspRegionDefs
import Submission.Work.Asymptotics.seminorm_on_cuspRegion_of_slashed
import Submission.Work.Asymptotics.FunnelSlashedDefs
import Submission.Work.Asymptotics.seminormK_cusp0_defs
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Residues.ResidueTheoremK
import Submission.Work.Asymptotics.kernelTransform_seminorm_halfFunnel
import Submission.Work.HFN.seminormK_cusp0_half
import Submission.Work.Asymptotics.BLZero.BadLineClean
import Submission.Work.Rigidity.Basic

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

/-!
# The `r`-seminorm bound for the CKMRV transform on the cusp-`1` half tile (`TS`)

The target `Work.Asymptotics.kernelTransform_seminorm_cuspHalf_TS` is the `γ = T S` half-region
statement: for `w` whose `T`-translate `u = w - 1` satisfies `S • u ∈ 𝒟` with `Im (S • u) ≥ 1/2`,
the `r`-seminorms of the naive contour transform of `K^{(d)}` at `w` grow at most polynomially in
`1/Im w` and in `‖w‖`.

## The reduction proved in this file

Writing `τ = S • u ∈ 𝒟` (equivalently `u = S • τ`, `w = (T S) • τ = 1 + S • τ`), the transport
identity `Work.Asymptotics.kernelTransform_slashKernel` plus `Work.Asymptotics.jFun_TS` give

  `kernelTransform (slashKernel ℓ d (T*S)) τ r = τ^{-d/2} · kernelTransform K ((T S) • τ) r`,

so the target is *equivalent* to the bound for the `T S`-**slashed** kernel on the half funnel
`{τ ∈ 𝒟 : 1/2 ≤ Im τ} = {τ ∈ 𝒟 : 2 ≤ Im τ} ∪ {τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2}`.  Hence

  `TSSlashedFunnelTS ∧ TSSlashedBand  ⟹  kernelTransform_seminorm_cuspHalf_TS`

(`TSSlashedHalfFunnel_of` merges the two slashed bounds, `cuspHalf_TS_of_slashedHalfFunnel`
performs the transport and the elementary conversion `‖τ‖^{d/2} (scale τ)^N ≤ α (Im w)^{-β} +
γ ‖w‖^δ`, via `conversion`).

## The two inputs, and their status

* **`TSSlashedFunnelTS`** (the funnel `2 ≤ Im τ`) — *discharged*: `TSSlashedFunnel_of_cuspOneFunnelTile`
  reduces it to the branch-neutral input `CuspOneFunnelTile ℓ d` (the bound at `1 + u` for
  `u ∈ E = KEpsilon`, i.e. the `n = 1` half of the cusp-`±1` tile estimate), which is supplied
  from outside this prelude by the separately proved tile bound (see the importing module
  `Submission/Work/Asymptotics/kernelTransform_seminorm_cuspHalf_TS.lean`).  On the funnel `u = S • τ` lies in `E`, the
  automorphy factor gives `‖τ^{-d/2}‖ ≤ 2^d` (`norm_zpow_half_le`) and `scale (S • τ) ≤ 2 scale τ`.
  (The older route `Work.Asymptotics.funnel_seminorm_slashed` +
  `TSSlashedFunnel_of_slashedFunnel` is stated in the file but not instantiated: that module's
  import closure contains the conflicting pair `ETailE_one` / `EtailE.Assembly`, which disagree on
  `Work.Asymptotics.Gcusp_eq_Gcoef`.)

* **`TSSlashedBand`** (the band `1/2 ≤ Im τ ≤ 2`) — reduced here to `CuspOneBandTile ℓ d` (the
  bound at `1 + u` for `u ∈ Tregion`) by `TSSlashedBand_of_bandTile`: on the band,
  `u = S • τ ∈ Tregion`, `‖τ^{-d/2}‖ ≤ 2^d`, `scale u ≤ 13`, `scale τ ≤ 6`.  `CuspOneBandTile`
  is in turn *reduced* (proved) to four isolated inputs, by `CuspOneBandTile_of_inputs` from its
  two halves `CuspOneBandTile_xneg_of_lowTile` (proved) and `CuspOneBandTile_xpos_of_inputs`
  (proved):

  1. `CuspOneBandLadder` — the `T`-ladder bound for `1/4 ≤ Re u` (requested as
     `Asymptotics/Kfun_cuspOneBand_ladder`);
  2. `CuspOneBandLadderSmall` — the `T`-ladder bound for `0 < Re u < 1/4`, `Im u > 1/2`;
  3. `CuspOneLowHalfTile` — the low-half cusp-`1` tile (requested as
     `Asymptotics/Kfun_cuspOneLowHalfTile`; the `n = 1` part of the fleet's
     `cuspTileLowHalfBound`);
  4. `CuspOneBadLineZero` — the junk vanishing at `1 + iy` — *discharged* by
     `CuspOneBadLineZero_holds` from the clean module
     `Submission/Work/Asymptotics/BLZero/BadLineClean.lean`, a de-clashed copy of
     `Work.Asymptotics.bad_line_kernelTransform_eq_zero` in which the name `coe_neg_vadd` (also
     declared by `Kaxis_principal_part_bound`, whence the branch collision) has been renamed to
     `bl_coe_neg_vadd`; the two cases `y ≠ 1` and `y = 1` are
     `kernelTransform_eq_zero_bad_line_of_im_ne_one` resp.
     `kernelTransform_eq_zero_bad_line_of_im_eq_one_of_slice`.

  The two remaining analytic inputs 1 and 2 are *not* fleet items: they need the ladder
  `kernelTransform K (1+u) = 2 kernelTransform K u - kernelTransform K (u-1)`
  (`Work.Asymptotics.kernelTransform_vadd_of_integrable`, proved below) together with
  (a) the transfer of the pointwise identity to the `r`-seminorms — either by differentiating the
  identity (for which one needs smoothness in `r` of `τ ↦ kernelTransform K τ ·` on the
  convergence region) or by the threshold argument of `Work.Asymptotics.tile_layer_transfer_aux`
  with the layer-like `F₂ (1+u) r := 2 * G(u) r - G(u-1) r`; and
  (b) the *uniformity* of the integrability threshold in `|r|` across the three translates
  (`u`, `u-1`, `1+u`), so that the junk value `0` and the identity agree at every `r`.

## Route to `CuspOneBandTile` (the case analysis; the geometry is formalised below)

Let `u ∈ Tregion`, `x = Re u`, `y = Im u`, `w = 1 + u`.  From `u ∈ Tregion` one has
`y ∈ [2/5, 2]`, `|x| < 1`, `y/2 ≤ x² + y² ≤ 2y` and the two arc inequalities `x² ∓ x + y² > 0`.

* `x = 0`: `w = 1 + iy` lies on the bad line `Re w = 1` (with `y ≠ 1`), where the transform is the
  junk value `0` (`Work.Asymptotics.kernelTransform_eq_zero_bad_line_of_im_ne_one`; that module
  clashes with the `Kaxis_principal_part_bound` chain, so a copy is needed).
* `x < 0`: then `w ∈ 𝒟` (`Re w ∈ (0,1)`), and
  - `y ≥ 1/2`: `w ∈ 𝒟_{1/2}` — `Work.Asymptotics.kernelTransform_seminorm_halfFunnel`;
  - `y < 1/2`: the case `2 ≤ Im (S • w)` is *impossible* — proved below as
    `ts_not_two_le_im_S_vadd_one`, whose arithmetic core `ts_not_E_aux` shows that the funnel
    condition `2((1+x)² + y²) ≤ y` clashes with `x² + y² ≤ 2y` and the arc condition
    `x² + x + y² > 0`; if `1/2 ≤ Im (S • w) ≤ 2` then `w ∈ Tregion` and
    `Work.Asymptotics.seminormK_cusp0_half` applies; if `Im (S • w) < 1/2`, then
    `ts_lt_quarter_of_im_S_vadd_one` (core `ts_low_aux`) gives `|x| < 1/4` from
    `(1+x)² + (y-1)² > 1` together with the arc condition, and the low-half tile statement applied
    at `u` (`u ∈ 𝒟`, `|Re u| < 1/4`, `Im u ≤ 1/2`, `Im (S•u) ≥ 1/2`) gives the bound at
    `1 + u = w`.
* `x ≥ 1/4`: then `u - 1 ∈ Tregion` whenever `y < 1/2` (`ts_vadd_neg_one_mem_Tregion`, proved
  below; for `y ≥ 1/2` one has `u - 1 ∈ 𝒟_{1/2}` directly) and the `T`-ladder
  (`Work.Asymptotics.kernelTransform_vadd_of_integrable`) bounds the seminorms at `1 + u` by
  those at `u` (`seminormK_cusp0_half`, constant) and at `u - 1` (again
  `seminormK_cusp0_half`, or `kernelTransform_seminorm_halfFunnel` for `y ≥ 1/2`).  This is the
  requested `Asymptotics/Kfun_cuspOneBand_ladder`.  Its only subtlety is the ladder's
  integrability hypothesis: for `u ∈ Tregion` with `x ≠ 0` no pole of `K(u,·)` or `K(u-1,·)` lies
  on the contour, the non-integrability locus is the decay threshold in `|r|`, and the threshold
  argument of `Work.Asymptotics.tile_layer_transfer_aux` handles the exceptional `r`.
* `x ∈ (0, 1/4)`: as for `x < 0`, either `w ∈ Tregion` (`seminormK_cusp0_half`) or
  `|x| < 1/4` and the low-half tile statement at `u` gives the bound at `1+u` directly; for
  `y ≥ 1/2` the ladder applies (`u - 1 ∈ 𝒟_{1/2}`).

So `CuspOneBandTile` follows from the two clean inputs

  `Asymptotics/Kfun_cuspOneLowHalfTile` (the cusp-`1` low-half tile, `n = 1`) and
  `Asymptotics/Kfun_cuspOneBand_ladder` (the `x ≥ 1/4` half),

together with `Work.Asymptotics.seminormK_cusp0_half`,
`Work.Asymptotics.kernelTransform_seminorm_halfFunnel`, `kernelTransform_vadd_of_integrable`
(proved in this file) and the geometry lemmas `ts_*` proved in this file.

## Import-branch notes

This file lives in the `MiddleRange.Main` branch; the `Tile`/`Gcusp`/`KPlusXiDefs` and the
`bad_line_kernelTransform_eq_zero` developments cannot be imported alongside it (`coe_neg_vadd`,
`Pspace`, `continuous_jInvariantFun` collisions).  Hence every input above is stated in
branch-neutral vocabulary (`Kfun`, `DomainD`, `Tregion`, `KEpsilon` only) so that a colleague can
prove it in whichever branch has the machinery.
-/

/-! ## The slashed kernel at `T * S`: local copies of five elementary identities

The module `Submission/Work/Asymptotics/funnel_seminorm_slashed.lean` (the only other place where
these live) currently fails to build in this workspace because its import closure pulls both
`ETailE_one` and `EtailE.Assembly`, which disagree on `Work.Asymptotics.Gcusp_eq_Gcoef`.  The five
identities below are re-proved here under `ts_`-names so that this file is independent of that
chain; a future session may delete them and restore the import once the collision is resolved. -/

/-- `jFun S (τ:ℂ) = τ`. -/
lemma ts_jFun_S (τ : UpperHalfPlane) : Work.Kernels.jFun ModularGroup.S (τ : ℂ) = (τ : ℂ) := by
  rw [Work.Kernels.jFun_apply]
  simp

/-- `jFun (T * S) (τ:ℂ) = τ`. -/
lemma ts_jFun_TS (τ : UpperHalfPlane) :
    Work.Kernels.jFun (ModularGroup.T * ModularGroup.S) (τ : ℂ) = (τ : ℂ) := by
  rw [Work.Kernels.jFun_apply]
  have h10 : ((ModularGroup.T * ModularGroup.S) 1 0 : ℤ) = 1 := by decide
  have h11 : ((ModularGroup.T * ModularGroup.S) 1 1 : ℤ) = 0 := by decide
  rw [h10, h11]
  simp

/-- `(T * S) • τ = 1 +ᵥ S • τ`. -/
lemma ts_TS_smul_eq' (τ : UpperHalfPlane) :
    (ModularGroup.T * ModularGroup.S) • τ = (1 : ℝ) +ᵥ (ModularGroup.S • τ) := by
  rw [mul_smul, UpperHalfPlane.modular_T_smul]

/-- `kernelTransform` is additive-negative in the kernel. -/
lemma ts_Kaxis_neg (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (t : ℝ) :
    Work.Kernels.Kaxis (fun σ z => - K σ z) τ t = - Work.Kernels.Kaxis K τ t := by
  unfold Work.Kernels.Kaxis
  by_cases h : 0 < t <;> simp [h]

lemma ts_kernelTransform_neg (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane)
    (r : ℝ) :
    Work.Kernels.kernelTransform (fun σ z => - K σ z) τ r
      = - Work.Kernels.kernelTransform K τ r := by
  have h1 : (fun t : ℝ => Work.Kernels.Kaxis (fun σ z => - K σ z) τ t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = fun t : ℝ => -(Work.Kernels.Kaxis K τ t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    funext t
    rw [ts_Kaxis_neg]
    ring
  rw [Work.Kernels.kernelTransform, Work.Kernels.kernelTransform, h1,
    MeasureTheory.integral_neg]
  ring

/-- `slashKernel ℓ d S = -Khat ℓ d`. -/
lemma ts_slashKernel_S (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    slashKernel ℓ d ModularGroup.S = - Work.Kernels.Khat ℓ d := by
  funext τ z
  have h := congr_fun (Work.Kernels.Khat_eq_neg_slash ℓ d hd z) τ
  rw [slashKernel]
  simp only [Pi.neg_apply]
  rw [h, neg_neg]

/-- `‖τ^{-(d:ℤ)/2}‖ ≤ 2 ^ d` for `Im τ ≥ 1/2` and `d ∈ {8, 24}` (the factor of automorphy of
`T S` is `j(TS,τ) = τ`). -/
private lemma norm_zpow_half_le (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane)
    (hτ : (1 : ℝ) / 2 ≤ τ.im) :
    ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖ ≤ (2 : ℝ) ^ d := by
  have hnorm : (1 : ℝ) / 2 ≤ ‖(τ : ℂ)‖ := le_trans hτ (Work.Kernels.im_le_coe_norm τ)
  rw [norm_zpow]
  rcases hd with rfl | rfl
  · rw [show -(((8 : ℕ) : ℤ) / 2) = (-4 : ℤ) by norm_num]
    have h4 : ((1 : ℝ) / 2) ^ 4 ≤ ‖(τ : ℂ)‖ ^ 4 := pow_le_pow_left₀ (by norm_num) hnorm 4
    have h4' : (((16 : ℝ)))⁻¹ ≤ ‖(τ : ℂ)‖ ^ 4 := by
      have h16 : ((1 : ℝ) / 2) ^ 4 = ((16 : ℝ))⁻¹ := by norm_num
      simpa only [h16] using h4
    calc ‖(τ : ℂ)‖ ^ (-4 : ℤ) = (‖(τ : ℂ)‖ ^ 4)⁻¹ := by rw [_root_.zpow_neg, zpow_ofNat]
      _ ≤ (((16 : ℝ))⁻¹)⁻¹ := by
            rw [inv_le_inv₀ (by positivity) (by norm_num)]
            exact h4'
      _ = 16 := by norm_num
      _ ≤ (2 : ℝ) ^ 8 := by norm_num
  · rw [show -(((24 : ℕ) : ℤ) / 2) = (-12 : ℤ) by norm_num]
    have h12 : ((1 : ℝ) / 2) ^ 12 ≤ ‖(τ : ℂ)‖ ^ 12 := pow_le_pow_left₀ (by norm_num) hnorm 12
    have h12' : (((4096 : ℝ)))⁻¹ ≤ ‖(τ : ℂ)‖ ^ 12 := by
      have h4096 : ((1 : ℝ) / 2) ^ 12 = ((4096 : ℝ))⁻¹ := by norm_num
      simpa only [h4096] using h12
    calc ‖(τ : ℂ)‖ ^ (-12 : ℤ) = (‖(τ : ℂ)‖ ^ 12)⁻¹ := by rw [_root_.zpow_neg, zpow_ofNat]
      _ ≤ (((4096 : ℝ))⁻¹)⁻¹ := by
            rw [inv_le_inv₀ (by positivity) (by norm_num)]
            exact h12'
      _ = 4096 := by norm_num
      _ ≤ (2 : ℝ) ^ 24 := by norm_num

/-- **The cusp-`1` funnel-tile input, isolated.**  The `r`-seminorm bound for the naive transform
at the cusp-`1` translate `1 + w` of a point `w` of the cusp-`0` funnel `E = KEpsilon`.  This is
the `n = 1` half of `Work.Asymptotics.cuspTile_seminorm` (the `γ = T*S` slashed funnel bound); it
is the *available* half of the target, up to the workspace's import collisions, and is requested
as `Asymptotics/Kfun_cuspOneTile`. -/
def CuspOneFunnelTile (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
    ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Work.Asymptotics.KEpsilon →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
        ≤ C * (Work.Kernels.scale w) ^ N

/-- `Im (S • u) = u.im / ‖u‖²`. -/
lemma ts_im_S_smulTS (u : ℍ) : (ModularGroup.S • u).im = u.im / ‖(u : ℂ)‖ ^ 2 := by
  rw [Work.Kernels.im_smul_eq]
  have h1 : Work.Kernels.jFun ModularGroup.S (u : ℂ) = (u : ℂ) := by
    rw [Work.Kernels.jFun_apply]; simp
  rw [h1]

/-- The two quadratic inequalities defining `Tregion`. -/
lemma ts_Tregion_ineqs {u : ℍ} (hu : u ∈ Work.Asymptotics.Tregion) :
    u.im / 2 ≤ ‖(u : ℂ)‖ ^ 2 ∧ ‖(u : ℂ)‖ ^ 2 ≤ 2 * u.im := by
  obtain ⟨huD, h1, h2⟩ := hu
  rw [ts_im_S_smulTS] at h1 h2
  have hpos : (0:ℝ) < ‖(u : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr u.ne_zero) 2
  constructor
  · rw [div_le_iff₀ hpos] at h2; linarith
  · rw [le_div_iff₀ hpos] at h1; linarith

/-- The norm-squared of a `T`-translate. -/
lemma ts_normSq_vadd_neg_one (u : ℍ) :
    ‖(((-1 : ℝ) +ᵥ u : ℍ) : ℂ)‖ ^ 2 = (u.re - 1) ^ 2 + u.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_vadd]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- The norm-squared of `u` in coordinates. -/
lemma ts_normSq_coe (u : ℍ) : ‖(u : ℂ)‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- The arc inequalities of `𝒟` in coordinates. -/
lemma ts_arc_ineqs {u : ℍ} (hu : u ∈ DomainD) :
    u.re ^ 2 - u.re + u.im ^ 2 > 0 ∧ u.re ^ 2 + u.re + u.im ^ 2 > 0 := by
  obtain ⟨-, -, h3, h4⟩ := (mem_DomainD.mp hu)
  have e1 : ‖(u : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = u.re ^ 2 - u.re + u.im ^ 2 + 1 / 4 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have e2 : ‖(u : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = u.re ^ 2 + u.re + u.im ^ 2 + 1 / 4 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  constructor
  · nlinarith [h3, e1, norm_nonneg ((u : ℂ) - (1/2 : ℂ))]
  · nlinarith [h4, e2, norm_nonneg ((u : ℂ) + (1/2 : ℂ))]

/-- **`(1 - y)² ≤ 7/16`.** -/
lemma ts_one_sub_im_sq_le {x y : ℝ} (hx : (1:ℝ)/4 ≤ x) (hx1 : x < 1)
    (hy : 0 < y) (hy2 : y < 1/2) (harc : 0 < x ^ 2 - x + y ^ 2) (hs : x ^ 2 + y ^ 2 ≤ 2 * y) :
    (1 - y) ^ 2 ≤ 7 / 16 := by
  by_cases hx34 : x ≤ 3 / 4
  · have h1 : 3 / 16 ≤ x - x ^ 2 := by nlinarith
    have h2 : 3 / 16 < y ^ 2 := by linarith
    have h3 : (43 / 100 : ℝ) < y := by
      by_contra h
      rw [not_lt] at h
      nlinarith [h2, h, hy]
    have h4 : 1 - y < 57 / 100 := by linarith
    have h5 : 0 < 1 - y := by linarith
    nlinarith [h4, h5]
  · have h1 : 9 / 16 < x ^ 2 := by nlinarith
    nlinarith [hs, h1]

/-- **`‖u - 1‖² ≤ 2 Im u`.** -/
lemma ts_normSq_vadd_le {x y : ℝ} (hx : (1:ℝ)/4 ≤ x) (hx1 : x < 1)
    (hy7 : (1 - y) ^ 2 ≤ 7 / 16) : (x - 1) ^ 2 + y ^ 2 ≤ 2 * y := by
  have h1 : 7 / 16 ≤ 2 * x - x ^ 2 := by nlinarith
  have h2 : (1 - x) ^ 2 + (1 - y) ^ 2 ≤ 1 := by
    have h3 : (1 - x) ^ 2 = 1 - (2 * x - x ^ 2) := by ring
    rw [h3]; linarith
  nlinarith [h2]

/-- **`y/2 ≤ ‖u - 1‖²`.** -/
lemma ts_le_normSq_vadd {x y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 < y) (hy2 : y < 1 / 2)
    (hx2 : x ^ 2 ≤ 2 * y - y ^ 2) : y / 2 ≤ (x - 1) ^ 2 + y ^ 2 := by
  have hnn : (0:ℝ) ≤ 2 * y - y ^ 2 := by nlinarith
  have hxw : x ≤ Real.sqrt (2 * y - y ^ 2) := by
    rw [← Real.sqrt_sq hx0]
    exact Real.sqrt_le_sqrt hx2
  have hw2 : (Real.sqrt (2 * y - y ^ 2)) ^ 2 = 2 * y - y ^ 2 := Real.sq_sqrt hnn
  have hw1 : Real.sqrt (2 * y - y ^ 2) ≤ 1 := by
    have h : Real.sqrt (2 * y - y ^ 2) ≤ Real.sqrt 1 := by
      apply Real.sqrt_le_sqrt
      rw [show (2 * y - y ^ 2) = 1 - (1 - y) ^ 2 by ring]
      nlinarith [sq_nonneg (1 - y)]
    rwa [Real.sqrt_one] at h
  have hk : 2 * Real.sqrt (2 * y - y ^ 2) ≤ 1 + 3 * y / 2 := by
    have h1 : (2 * Real.sqrt (2 * y - y ^ 2)) ^ 2 ≤ (1 + 3 * y / 2) ^ 2 := by
      rw [mul_pow, hw2]
      nlinarith [sq_nonneg (1 - 5 * y / 2)]
    have h2 : (0:ℝ) ≤ 1 + 3 * y / 2 := by linarith
    have h3 := sq_le_sq.mp h1
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg h2] at h3
  have hkey : y / 2 - y ^ 2 ≤ (1 - Real.sqrt (2 * y - y ^ 2)) ^ 2 := by
    have h3 : 1 - (1 + 3 * y / 2) ≤ 1 - 2 * Real.sqrt (2 * y - y ^ 2) := by linarith
    have h4 : (1 - Real.sqrt (2 * y - y ^ 2)) ^ 2
        = 1 - 2 * Real.sqrt (2 * y - y ^ 2) + (Real.sqrt (2 * y - y ^ 2)) ^ 2 := by ring
    rw [h4, hw2]; linarith
  have hle : 1 - Real.sqrt (2 * y - y ^ 2) ≤ 1 - x := by linarith
  have hnn2 : 0 ≤ 1 - Real.sqrt (2 * y - y ^ 2) := by linarith
  have hxlow : y / 2 - y ^ 2 ≤ (1 - x) ^ 2 :=
    le_trans hkey (pow_le_pow_left₀ hnn2 hle 2)
  rw [show (x - 1) ^ 2 + y ^ 2 = (1 - x) ^ 2 + y ^ 2 by ring]
  linarith

/-- **`(-1) +ᵥ u ∈ 𝒟` when `Re u > 0`.** -/
lemma ts_vadd_neg_one_mem_DomainD_of_pos {u : ℍ} (hu : u ∈ DomainD) (h0 : 0 < u.re) :
    ((-1 : ℝ) +ᵥ u) ∈ DomainD := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_DomainD.mp hu
  refine mem_DomainD.mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [UpperHalfPlane.vadd_re]; linarith
  · rw [UpperHalfPlane.vadd_re]; linarith
  · have hcoe : ((((-1 : ℝ) +ᵥ u : ℍ)) : ℂ) - (1 / 2 : ℂ) = (u : ℂ) - (3 / 2 : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    rw [hcoe]
    have hre : (((u : ℂ) - (3 / 2 : ℂ))).re = u.re - 3 / 2 := by simp
    have h := Complex.abs_re_le_norm ((u : ℂ) - (3 / 2 : ℂ))
    rw [hre, abs_of_neg (by linarith : u.re - 3 / 2 < 0)] at h
    linarith
  · have hcoe : ((((-1 : ℝ) +ᵥ u : ℍ)) : ℂ) + (1 / 2 : ℂ) = (u : ℂ) - (1 / 2 : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    rw [hcoe]; exact h3

/-- **`1 +ᵥ u ∈ 𝒟` when `Re u < 0`.** -/
lemma ts_vadd_one_mem_DomainD_of_neg {u : ℍ} (hu : u ∈ DomainD) (h0 : u.re < 0) :
    ((1 : ℝ) +ᵥ u) ∈ DomainD := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_DomainD.mp hu
  refine mem_DomainD.mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [UpperHalfPlane.vadd_re]; linarith
  · rw [UpperHalfPlane.vadd_re]; linarith
  · have hcoe : ((((1 : ℝ) +ᵥ u : ℍ)) : ℂ) - (1 / 2 : ℂ) = (u : ℂ) + (1 / 2 : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    rw [hcoe]; exact h4
  · have hcoe : ((((1 : ℝ) +ᵥ u : ℍ)) : ℂ) + (1 / 2 : ℂ) = (u : ℂ) + (3 / 2 : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    rw [hcoe]
    have hre : (((u : ℂ) + (3 / 2 : ℂ))).re = u.re + 3 / 2 := by simp
    have h := Complex.abs_re_le_norm ((u : ℂ) + (3 / 2 : ℂ))
    rw [hre, abs_of_pos (by linarith : (0:ℝ) < u.re + 3 / 2)] at h
    linarith


/-- **The geometric input for the `T`-ladder on the band.**  For `u ∈ Tregion` with `Re u ≥ 1/4`
and `Im u < 1/2` the translate `u - 1` towards the cusp is again in `Tregion`, so the seminorms of
the transform there are bounded by `Work.Asymptotics.seminormK_cusp0_half`.  With `x = Re u`,
`y = Im u` the two estimates `1/2 ≤ Im (S • (u-1)) ≤ 2` are `‖u - 1‖² ≤ 2y` (from
`(1-y)² ≤ 7/16 ≤ 2x - x²`: the arc condition `y² > x - x²` for `x ≤ 3/4`, the tube condition
`x² + y² ≤ 2y` for `x > 3/4`) and `‖u - 1‖² ≥ y/2` (from `x ≤ √(2y - y²)` and
`(1 + 3y/2)² - 4(2y - y²) = (1 - 5y/2)² ≥ 0`). -/
lemma ts_vadd_neg_one_mem_Tregion : ∀ (u : ℍ), u ∈ Work.Asymptotics.Tregion →
    (1 : ℝ) / 4 ≤ u.re → u.im < 1 / 2 →
    ((-1 : ℝ) +ᵥ u) ∈ (Work.Asymptotics.Tregion : Set ℍ) := by
  intro u hu hx hy
  obtain ⟨huD, hSlo, hShi⟩ := hu
  have hmem := mem_DomainD.mp huD
  have hx1 : u.re < 1 := hmem.2.1
  have hx0 : 0 < u.re := by linarith only [hx]
  have hy0 : 0 < u.im := u.im_pos
  have hposn : (0:ℝ) < ‖(u : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr u.ne_zero) 2
  have hsq : ‖(u : ℂ)‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := ts_normSq_coe u
  have hs : u.re ^ 2 + u.im ^ 2 ≤ 2 * u.im := by
    have h := hSlo
    rw [ts_im_S_smulTS] at h
    have h' := (le_div_iff₀ hposn).mp h
    linarith only [h', hsq]
  have hx2 : u.re ^ 2 ≤ 2 * u.im - u.im ^ 2 := by linarith only [hs]
  have harc : 0 < u.re ^ 2 - u.re + u.im ^ 2 := (ts_arc_ineqs huD).1
  have hy7 : (1 - u.im) ^ 2 ≤ 7 / 16 := ts_one_sub_im_sq_le hx hx1 hy0 hy harc hs
  have hup : (u.re - 1) ^ 2 + u.im ^ 2 ≤ 2 * u.im := ts_normSq_vadd_le hx hx1 hy7
  have hlow : u.im / 2 ≤ (u.re - 1) ^ 2 + u.im ^ 2 :=
    ts_le_normSq_vadd (le_of_lt hx0) hy0 hy hx2
  have hvD : ((-1 : ℝ) +ᵥ u) ∈ DomainD := ts_vadd_neg_one_mem_DomainD_of_pos huD hx0
  have hpos : (0 : ℝ) < (u.re - 1) ^ 2 + u.im ^ 2 := by linarith only [hlow, hy0]
  refine ⟨hvD, ?_, ?_⟩
  · rw [ts_im_S_smulTS, ts_normSq_vadd_neg_one, UpperHalfPlane.vadd_im]
    have h1 : (1 / 2 : ℝ) * ((u.re - 1) ^ 2 + u.im ^ 2) ≤ u.im := by linarith only [hup]
    exact (le_div_iff₀ hpos).mpr h1
  · rw [ts_im_S_smulTS, ts_normSq_vadd_neg_one, UpperHalfPlane.vadd_im]
    have h1 : u.im ≤ 2 * ((u.re - 1) ^ 2 + u.im ^ 2) := by linarith only [hlow]
    exact (div_le_iff₀ hpos).mpr h1


/-- **The `(T S)`-slashed bound on the funnel** `{τ ∈ 𝒟 : 2 ≤ Im τ}`. -/
def TSSlashedFunnelTS (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
    ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N

/-- **The `(T S)`-slashed bound on the band** `{τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2}`. -/
def TSSlashedBand (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
    ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im →
      τ.im ≤ 2 →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N

/-- The two slashed bounds combine into a single bound on the half funnel `{τ ∈ 𝒟 : 1/2 ≤ Im τ}`. -/
lemma TSSlashedHalfFunnel_of (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hF : TSSlashedFunnelTS ℓ d) (hB : TSSlashedBand ℓ d) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N := by
  intro k l
  obtain ⟨C₁, N₁, hC₁, hN₁, hb₁⟩ := hF k l
  obtain ⟨C₂, N₂, hC₂, hN₂, hb₂⟩ := hB k l
  refine ⟨max C₁ C₂, max N₁ N₂, le_trans hC₁ (le_max_left _ _),
    le_trans hN₁ (le_max_left _ _), ?_⟩
  intro τ r hτD hτhalf
  have hC0 : 0 ≤ max C₁ C₂ := le_trans hC₁ (le_max_left _ _)
  have hsc1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  rcases le_or_gt τ.im 2 with h2 | h2
  · exact le_trans (hb₂ τ r hτD hτhalf h2) (mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_right _ _))
      (Real.rpow_nonneg (by linarith) _) hC0)
  · exact le_trans (hb₁ τ r hτD (le_of_lt h2)) (mul_le_mul (le_max_left _ _)
      (Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_left _ _))
      (Real.rpow_nonneg (by linarith) _) hC0)

/-- **The elementary conversion** of the slashed bound at `τ` into the target's shape at
`w = 1 +ᵥ (S • τ)`.  Uses `Im w = Im (S • τ) = Im τ / ‖τ‖²`, `‖τ‖ ≥ 1/2`, `Im τ ≥ 1/2`
(so `scale τ ≤ 8 ‖τ‖`) and `1/τ.im ≤ 2`. -/
private lemma conversion (d : ℕ) (C N : ℝ) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (τ w : UpperHalfPlane) (hτ : (1 : ℝ) / 2 ≤ τ.im)
    (hwim : w.im = (ModularGroup.S • τ).im) :
    ‖(τ : ℂ)‖ ^ ((d : ℝ) / 2) * (C * (Work.Kernels.scale τ) ^ N)
      ≤ (C * 8 ^ N) * (w.im) ^ (-((d : ℝ) / 2 + N)) + 1 * (‖(w : ℂ)‖) ^ (1 : ℝ) := by
  set A : ℝ := ‖(τ : ℂ)‖ with hA
  have hApos : 0 < A := by rw [hA]; exact norm_pos_iff.mpr τ.ne_zero
  have hAhalf : (1 : ℝ) / 2 ≤ A := by
    rw [hA]; linarith [Work.Kernels.im_le_coe_norm τ, hτ]
  have hinv : (τ.im)⁻¹ ≤ 2 := by
    exact (inv_le_comm₀ τ.im_pos (by norm_num : (0 : ℝ) < 2)).mpr (by linarith : (2 : ℝ)⁻¹ ≤ τ.im)
  have hscale : Work.Kernels.scale τ ≤ 8 * A := by
    have h2 : (3 : ℝ) ≤ 6 * A := by linarith
    rw [Work.Kernels.scale, hA]
    linarith
  have hp : (Work.Kernels.scale τ) ^ N ≤ 8 ^ N * A ^ N := by
    have h0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one (Work.Kernels.one_le_scale τ)
    calc (Work.Kernels.scale τ) ^ N ≤ (8 * A) ^ N := Real.rpow_le_rpow h0 hscale hN
      _ = 8 ^ N * A ^ N := Real.mul_rpow (by norm_num) hApos.le
  have himS : (ModularGroup.S • τ).im = τ.im / A ^ 2 := by
    rw [Work.Kernels.im_smul_eq, ts_jFun_S, ← hA]
  have hkey2 : A ^ ((d : ℝ) / 2 + N) ≤ (w.im) ^ (-((d : ℝ) / 2 + N)) := by
    rw [hwim, himS]
    have hpos : 0 < τ.im / A ^ 2 := div_pos τ.im_pos (pow_pos hApos 2)
    have hle : τ.im / A ^ 2 ≤ 1 / A := by
      rw [div_le_div_iff₀ (pow_pos hApos 2) hApos, one_mul]
      nlinarith [Work.Kernels.im_le_coe_norm τ, hA]
    have hnp : -((d : ℝ) / 2 + N) ≤ 0 := by
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      linarith
    refine le_trans (le_of_eq ?_) (Real.rpow_le_rpow_of_nonpos hpos hle hnp)
    rw [one_div, Real.inv_rpow hApos.le, ← Real.rpow_neg hApos.le, neg_neg, hA]
  have hAc : ‖(τ : ℂ)‖ ^ ((d : ℝ) / 2) * (C * (Work.Kernels.scale τ) ^ N)
      ≤ (C * 8 ^ N) * A ^ ((d : ℝ) / 2 + N) := by
    rw [← hA]
    calc A ^ ((d : ℝ) / 2) * (C * (Work.Kernels.scale τ) ^ N)
        ≤ A ^ ((d : ℝ) / 2) * (C * (8 ^ N * A ^ N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hC)
            (Real.rpow_nonneg hApos.le _)
      _ = (C * 8 ^ N) * A ^ ((d : ℝ) / 2 + N) := by
          rw [Real.rpow_add hApos]; ring
  have hfinal : (C * 8 ^ N) * A ^ ((d : ℝ) / 2 + N)
      ≤ (C * 8 ^ N) * (w.im) ^ (-((d : ℝ) / 2 + N)) :=
    mul_le_mul_of_nonneg_left hkey2 (by positivity)
  have hRHS : (C * 8 ^ N) * (w.im) ^ (-((d : ℝ) / 2 + N))
      ≤ (C * 8 ^ N) * (w.im) ^ (-((d : ℝ) / 2 + N)) + 1 * (‖(w : ℂ)‖) ^ (1 : ℝ) := by
    have h1 : (0 : ℝ) ≤ (‖(w : ℂ)‖) ^ (1 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    linarith
  exact le_trans (le_trans hAc hfinal) hRHS

/-- **The transport of the slashed half-funnel bound to the target.** -/
lemma cuspHalf_TS_of_slashedHalfFunnel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (h : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N) :
    ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (w : UpperHalfPlane) (r : ℝ),
        ModularGroup.S • ((-1 : ℝ) +ᵥ w) ∈ Work.Asymptotics.DomainD →
        (1 : ℝ) / 2 ≤ (ModularGroup.S • ((-1 : ℝ) +ᵥ w)).im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖
          ≤ α * (w.im) ^ (-β) + γ * (‖(w : ℂ)‖) ^ δ := by
  have _hd : d = 8 ∨ d = 24 := hd
  intro k l
  obtain ⟨C, N, hC, hN, hb⟩ := h k l
  refine ⟨C * 8 ^ N, (d : ℝ) / 2 + N, 1, 1, by positivity, by positivity, zero_le_one,
    zero_le_one, ?_⟩
  intro w r hD him
  set u : UpperHalfPlane := (-1 : ℝ) +ᵥ w with hu
  set τ : UpperHalfPlane := ModularGroup.S • u with hτ
  have hτD : τ ∈ Work.Asymptotics.DomainD := hD
  have hτhalf : (1 : ℝ) / 2 ≤ τ.im := him
  have huS : ModularGroup.S • τ = u := by rw [hτ]; exact Work.Rigidity.S_smul_S_smul u
  have hwτ : (ModularGroup.T * ModularGroup.S) • τ = w := by
    rw [ts_TS_smul_eq', huS, hu, vadd_vadd,
      show ((1 : ℝ) + (-1 : ℝ)) = 0 by norm_num, zero_vadd]
  have hτne : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hG : ∀ s : ℝ, Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s
      = (τ : ℂ) ^ ((d : ℤ) / 2) *
        Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s := by
    intro s
    have hkey := kernelTransform_slashKernel ℓ d (ModularGroup.T * ModularGroup.S) τ s
    rw [hwτ, ts_jFun_TS τ] at hkey
    rw [hkey, ← mul_assoc, ← zpow_add₀ hτne, add_neg_cancel, zpow_zero, one_mul]
  have hderiv : iteratedDeriv l (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r
      = (τ : ℂ) ^ ((d : ℤ) / 2) * iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r := by
    rw [show (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s)
      = fun s : ℝ => (τ : ℂ) ^ ((d : ℤ) / 2) *
          Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s
      from funext hG]
    exact iteratedDeriv_const_mul_field _ _
  have hnorm_c : ‖(τ : ℂ) ^ ((d : ℤ) / 2)‖ = ‖(τ : ℂ)‖ ^ ((d : ℝ) / 2) := by
    rw [norm_zpow, ← Real.rpow_intCast]
    congr 1
    rcases hd with rfl | rfl <;> norm_num
  have hwim : w.im = (ModularGroup.S • τ).im := by rw [← hwτ, ts_TS_smul_eq', UpperHalfPlane.vadd_im]
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖
      = (|r| ^ k) * ‖(τ : ℂ) ^ ((d : ℤ) / 2) * iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖ := by
        rw [hderiv]
    _ = (|r| ^ k) * (‖(τ : ℂ) ^ ((d : ℤ) / 2)‖ * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖) := by
        rw [norm_mul]
    _ = ‖(τ : ℂ) ^ ((d : ℤ) / 2)‖ * ((|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖) := by
        ring
    _ ≤ ‖(τ : ℂ) ^ ((d : ℤ) / 2)‖ * (C * (Work.Kernels.scale τ) ^ N) :=
        mul_le_mul_of_nonneg_left (hb τ r hτD hτhalf) (norm_nonneg _)
    _ = ‖(τ : ℂ)‖ ^ ((d : ℝ) / 2) * (C * (Work.Kernels.scale τ) ^ N) := by rw [hnorm_c]
    _ ≤ (C * 8 ^ N) * (w.im) ^ (-((d : ℝ) / 2 + N)) + 1 * (‖(w : ℂ)‖) ^ (1 : ℝ) :=
        conversion d C N hC hN τ w hτhalf hwim

/-- **The `(T S)`-slashed funnel bound from the four-case funnel bound.** -/
lemma TSSlashedFunnel_of_slashedFunnel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (h : ∀ k l : ℕ, ∃ α β γ' δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ' ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ' * (‖(τ : ℂ)‖) ^ δ) :
    TSSlashedFunnelTS ℓ d := by
  intro k l
  obtain ⟨α, β, γ', δ, hα, hβ, hγ, hδ, hb⟩ := h k l
  refine ⟨α + γ', max β δ, by linarith, le_max_of_le_left hβ, ?_⟩
  intro τ r hτD hτ2
  have hsc1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hτim1 : (1 : ℝ) ≤ τ.im := by linarith
  have hnb : (τ.im) ^ (-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτim1 (by linarith)
  have hnd : (‖(τ : ℂ)‖) ^ δ ≤ (Work.Kernels.scale τ) ^ δ :=
    Real.rpow_le_rpow (norm_nonneg _) (Work.Kernels.coe_norm_le_scale τ) hδ
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖
      ≤ α * (τ.im) ^ (-β) + γ' * (‖(τ : ℂ)‖) ^ δ := hb τ r hτD hτ2
    _ ≤ α * (Work.Kernels.scale τ) ^ max β δ
          + γ' * (Work.Kernels.scale τ) ^ max β δ := by
        have h1 : α * (τ.im) ^ (-β) ≤ α * (Work.Kernels.scale τ) ^ max β δ :=
          mul_le_mul_of_nonneg_left
            (le_trans hnb (Real.one_le_rpow hsc1 (le_max_of_le_left hβ))) hα
        have h3 : (Work.Kernels.scale τ) ^ δ ≤ (Work.Kernels.scale τ) ^ max β δ :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_right _ _)
        have h2 : γ' * (‖(τ : ℂ)‖) ^ δ ≤ γ' * (Work.Kernels.scale τ) ^ max β δ :=
          mul_le_mul_of_nonneg_left (le_trans hnd h3) hγ
        linarith
    _ = (α + γ') * (Work.Kernels.scale τ) ^ max β δ := by ring

/-- **The `(T S)`-slashed funnel bound from the cusp-`1` funnel tile.**  For `τ` in the funnel
`{τ ∈ 𝒟 : 2 ≤ Im τ}` the slashed transform is `τ^{-d/2}` times the transform at `1 + u`,
`u = S • τ ∈ E = KEpsilon`, and on the funnel `scale (S • τ) ≤ 2 scale τ`; together with
`‖τ^{-d/2}‖ ≤ 2^d` this converts `CuspOneFunnelTile` into `TSSlashedFunnelTS`.

(The workspace's `Work.Asymptotics.funnel_seminorm_slashed` gives the same statement through
`Work.Asymptotics.cuspTile_seminorm`; that route is currently unavailable in this file because
that module's import closure contains the conflicting `ETailE_one` / `EtailE.Assembly` pair.) -/
lemma TSSlashedFunnel_of_cuspOneFunnelTile (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (h : CuspOneFunnelTile ℓ d) : TSSlashedFunnelTS ℓ d := by
  intro k l
  obtain ⟨C, N, hC, hN, hb⟩ := h k l
  refine ⟨C * 2 ^ d * 2 ^ N, N, by positivity, hN, ?_⟩
  intro τ r hτD hτ2
  set u : UpperHalfPlane := ModularGroup.S • τ with hu
  have hSS : ModularGroup.S • u = τ := by rw [hu]; exact Work.Rigidity.S_smul_S_smul τ
  have huE : u ∈ Work.Asymptotics.KEpsilon := by
    rw [Work.Asymptotics.mem_KEpsilon]
    exact ⟨by rw [hu]; exact S_smul_mem_DomainD hτD, by rw [hSS]; exact hτ2⟩
  have hTS : (ModularGroup.T * ModularGroup.S) • τ = (1 : ℝ) +ᵥ u := by
    rw [ts_TS_smul_eq', hu]
  have hderiv : iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r
      = (τ : ℂ) ^ (-((d : ℤ) / 2)) * iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r := by
    have hfun : (fun s : ℝ =>
          Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s)
        = fun s : ℝ => (τ : ℂ) ^ (-((d : ℤ) / 2)) *
            Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s := by
      funext s
      rw [kernelTransform_slashKernel ℓ d (ModularGroup.T * ModularGroup.S) τ s, ts_jFun_TS τ,
        hTS]
    rw [hfun, iteratedDeriv_const_mul_field]
  -- the scale comparison on the funnel: `scale (S • τ) ≤ 2 scale τ`
  have hscale : Work.Kernels.scale u ≤ 2 * Work.Kernels.scale τ := by
    have himu : u.im = τ.im / ‖(τ : ℂ)‖ ^ 2 := by rw [hu, Work.Kernels.im_smul_eq, ts_jFun_S]
    have hnormu : ‖(u : ℂ)‖ = (‖(τ : ℂ)‖)⁻¹ := by
      have hcoe : ((u : ℍ) : ℂ) = -((τ : ℂ))⁻¹ := by rw [hu]; exact Work.Rigidity.coe_S_smul τ
      rw [hcoe, norm_neg, norm_inv]
    have hmem := Work.Asymptotics.mem_DomainD.mp hτD
    have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := ts_normSq_coe τ
    have h1 : τ.re ^ 2 < 1 := by nlinarith [hmem.1, hmem.2.1]
    have hsq5 : ‖(τ : ℂ)‖ ^ 2 ≤ 1 + τ.im ^ 2 := by rw [hsq]; linarith
    rw [Work.Kernels.scale, Work.Kernels.scale, himu, hnormu, inv_div]
    have h2 : ‖(τ : ℂ)‖ ^ 2 / τ.im ≤ 1 / τ.im + τ.im := by
      rw [div_le_iff₀ τ.im_pos]
      have he : (1 / τ.im + τ.im) * τ.im = 1 + τ.im ^ 2 := by
        field_simp
      rw [he]
      exact hsq5
    have h3 : (‖(τ : ℂ)‖)⁻¹ ≤ 1 / τ.im := by
      rw [one_div]
      exact (inv_le_inv₀ (norm_pos_iff.mpr τ.ne_zero) τ.im_pos).mpr
        (Work.Kernels.im_le_coe_norm τ)
    have h2b : ‖(τ : ℂ)‖ ^ 2 / τ.im ≤ (τ.im)⁻¹ + τ.im := by
      rw [one_div] at h2
      exact h2
    have h3b : (‖(τ : ℂ)‖)⁻¹ ≤ (τ.im)⁻¹ := by
      rw [one_div] at h3
      exact h3
    have h4 : τ.im ≤ ‖(τ : ℂ)‖ := Work.Kernels.im_le_coe_norm τ
    have h6 : (0 : ℝ) < τ.im := τ.im_pos
    nlinarith [h2b, h3b, h4, h6]
  have hscN : (Work.Kernels.scale u) ^ N ≤ 2 ^ N * (Work.Kernels.scale τ) ^ N := by
    have h0 : (0 : ℝ) ≤ Work.Kernels.scale u :=
      le_trans (by norm_num) (Work.Kernels.one_le_scale u)
    have h1 : (Work.Kernels.scale u) ^ N ≤ (2 * Work.Kernels.scale τ) ^ N :=
      Real.rpow_le_rpow h0 hscale hN
    rwa [Real.mul_rpow (by norm_num) (le_trans (by norm_num) (Work.Kernels.one_le_scale τ))] at h1
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖
      = (|r| ^ k) * (‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖ * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖) := by
        rw [hderiv, norm_mul]
    _ = ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖ * ((|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖) := by
        ring
    _ ≤ (2 : ℝ) ^ d * (C * (Work.Kernels.scale u) ^ N) :=
        mul_le_mul (norm_zpow_half_le d hd τ (by linarith)) (hb u r huE) (by positivity)
          (by positivity)
    _ = C * 2 ^ d * (Work.Kernels.scale u) ^ N := by ring
    _ ≤ C * 2 ^ d * (2 ^ N * (Work.Kernels.scale τ) ^ N) :=
        mul_le_mul_of_nonneg_left hscN (by positivity)
    _ = (C * 2 ^ d * 2 ^ N) * (Work.Kernels.scale τ) ^ N := by ring


/-- **The band input, isolated.**  The `r`-seminorm bound for the naive transform at the
cusp-`1` translate `1 + u` of a point `u` of the cusp-`0` annulus
`Tregion = {u ∈ 𝒟 : 1/2 ≤ Im (S • u) ≤ 2}`.

This is exactly the `1/2 ≤ Im τ ≤ 2` (band) half of `TSSlashedBand`, transported by the slash
identity: for `τ` in the band, `u = S • τ` lies in `Tregion` and
`kernelTransform (slashKernel ℓ d (T*S)) τ = τ^{-d/2} · kernelTransform K (1 + u)` (see
`TSSlashedBand_of_bandTile` below).  It is the "low half" of the cusp-`±1` tile analysis of
CKMRV §5.2 (compare `Work.Asymptotics.cuspTileLowHalfBound`, which covers `Im u ≤ 1/2`,
`|Re u| < 1/4`); the region is bounded, so the `scale` factor on the right is inessential. -/
def CuspOneBandTile (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
    ∀ (u : UpperHalfPlane) (r : ℝ), u ∈ Work.Asymptotics.Tregion →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖
        ≤ C * (Work.Kernels.scale u) ^ N

/-- **The `(T S)`-slashed band bound from the cusp-`1` half-tile bound.**  The slash identity
`kernelTransform (slashKernel ℓ d (T*S)) τ = τ^{-d/2} · kernelTransform K ((T*S) • τ)` and
`(T*S) • τ = 1 + S • τ` turn `CuspOneBandTile` into `TSSlashedBand`: on the band
`1/2 ≤ Im τ ≤ 2`, `‖τ‖ ≥ 1/2` gives `‖τ^{-d/2}‖ ≤ 2^d`, and `scale (S • τ) ≤ 13`,
`scale τ ≤ 6` convert the `scale` factor of the tile bound into the `scale τ` factor. -/
lemma TSSlashedBand_of_bandTile (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (h : CuspOneBandTile ℓ d) : TSSlashedBand ℓ d := by
  intro k l
  obtain ⟨C, N, hC, hN, hb⟩ := h k l
  refine ⟨C * 2 ^ d * 13 ^ N, N, by positivity, hN, ?_⟩
  intro τ r hτD hτhalf hτ2
  set u : UpperHalfPlane := ModularGroup.S • τ with hu
  have hSS : ModularGroup.S • u = τ := by rw [hu]; exact Work.Rigidity.S_smul_S_smul τ
  have huT : u ∈ Work.Asymptotics.Tregion := by
    rw [Work.Asymptotics.mem_Tregion]
    exact ⟨by rw [hu]; exact S_smul_mem_DomainD hτD, by rw [hSS]; exact hτhalf,
      by rw [hSS]; exact hτ2⟩
  have hTS : (ModularGroup.T * ModularGroup.S) • τ = (1 : ℝ) +ᵥ u := by
    rw [ts_TS_smul_eq', hu]
  -- the transport of the slashed transform
  have hderiv : iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r
      = (τ : ℂ) ^ (-((d : ℤ) / 2)) * iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r := by
    have hfun : (fun s : ℝ =>
          Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s)
        = fun s : ℝ => (τ : ℂ) ^ (-((d : ℤ) / 2)) *
            Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s := by
      funext s
      rw [kernelTransform_slashKernel ℓ d (ModularGroup.T * ModularGroup.S) τ s, ts_jFun_TS τ, hTS]
    rw [hfun, iteratedDeriv_const_mul_field]
  -- the two scale bounds on the band
  have hτn : (1 : ℝ) / 2 ≤ ‖(τ : ℂ)‖ := le_trans hτhalf (Work.Kernels.im_le_coe_norm τ)
  have hτn5 : ‖(τ : ℂ)‖ ≤ Real.sqrt 5 := by
    have hmem := Work.Asymptotics.mem_DomainD.mp hτD
    have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have h1 : τ.re ^ 2 < 1 := by nlinarith [hmem.1, hmem.2.1]
    have h2 : τ.im ^ 2 ≤ 4 := by nlinarith [τ.im_pos, hτ2]
    have h3 : ‖(τ : ℂ)‖ ^ 2 ≤ 5 := by rw [hsq]; linarith
    rw [← Real.sqrt_sq (norm_nonneg (τ : ℂ))]
    exact Real.sqrt_le_sqrt h3
  have hscaleτ : Work.Kernels.scale τ ≤ 6 := by
    rw [Work.Kernels.scale]
    have h1 : (τ.im)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ τ.im_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    have h5 : Real.sqrt 5 ≤ 3 := by
      have h9 : Real.sqrt 5 ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
      rwa [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)] at h9
    linarith
  have hscaleu : Work.Kernels.scale u ≤ 13 := by
    have himu : u.im = τ.im / ‖(τ : ℂ)‖ ^ 2 := by
      rw [hu, Work.Kernels.im_smul_eq, ts_jFun_S]
    have hnormu : ‖(u : ℂ)‖ = (‖(τ : ℂ)‖)⁻¹ := by
      have hcoe : ((u : ℍ) : ℂ) = -((τ : ℂ))⁻¹ := by rw [hu]; exact Work.Rigidity.coe_S_smul τ
      rw [hcoe, norm_neg, norm_inv]
    rw [Work.Kernels.scale, himu, hnormu, inv_div]
    have h1 : ‖(τ : ℂ)‖ ^ 2 / τ.im ≤ 10 := by
      rw [div_le_iff₀ τ.im_pos]
      nlinarith [hτn5, hτhalf, Real.sqrt_nonneg 5, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
      
    have h2 : (‖(τ : ℂ)‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (norm_pos_iff.mpr τ.ne_zero) (by norm_num : (0:ℝ) < 2)]
      linarith
    linarith
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖
      = (|r| ^ k) * (‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖ * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖) := by
        rw [hderiv, norm_mul]
    _ = ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖ * ((|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖) := by
        ring
    _ ≤ (2 : ℝ) ^ d * (C * (Work.Kernels.scale u) ^ N) :=
        mul_le_mul (norm_zpow_half_le d hd τ hτhalf) (hb u r huT) (by positivity) (by positivity)
    _ = C * 2 ^ d * (Work.Kernels.scale u) ^ N := by ring
    _ ≤ C * 2 ^ d * (13 ^ N * (Work.Kernels.scale τ) ^ N) := by
        have h1 : (Work.Kernels.scale u) ^ N ≤ 13 ^ N * (Work.Kernels.scale τ) ^ N := by
          have hsu : (Work.Kernels.scale u) ^ N ≤ (13 : ℝ) ^ N :=
            Real.rpow_le_rpow (le_trans (by norm_num) (Work.Kernels.one_le_scale u)) hscaleu hN
          have hsτ : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
            Real.one_le_rpow (Work.Kernels.one_le_scale τ) hN
          calc (Work.Kernels.scale u) ^ N ≤ 13 ^ N := hsu
            _ = 13 ^ N * 1 := (mul_one _).symm
            _ ≤ 13 ^ N * (Work.Kernels.scale τ) ^ N :=
                mul_le_mul_of_nonneg_left hsτ (Real.rpow_nonneg (by norm_num) N)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (C * 2 ^ d * 13 ^ N) * (Work.Kernels.scale τ) ^ N := by ring

/-! ## The two structural identities used by the band analysis

* the **`T`-ladder** `kernelTransform K (u+1) r = 2 kernelTransform K u r - kernelTransform K (u-1) r`
  (valid wherever the two integrands involved are integrable), from the second-difference identity
  `(T-I)²K = 0` (`Work.Asymptotics.Kaxis_T2_Kfun`);
* the **`S`-transport** `kernelTransform K (S • τ) r = -(τ)^{d/2} · kernelTransform Khat τ r`, from
  `Khat = -K|^S` (`Work.Asymptotics.slashKernel_S`).
-/

/-- **(T-I)²K = 0 on the contour**: `K(τ+2,it) - 2K(τ+1,it) + K(τ,it) = 0`. -/
lemma Kaxis_T2_Kfun_s (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (t : ℝ) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((2 : ℝ) +ᵥ τ) t
      - 2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) t
      + Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t = 0 := by
  by_cases ht : 0 < t
  · have h := congr_fun (Work.Residues.Kfun_T2 ℓ d hd (Work.Kernels.imagAxis t ht)) τ
    simp only [Work.Kernels.T2op, Pi.zero_apply] at h
    simpa only [Work.Kernels.Kaxis, dif_pos ht] using h
  · simp only [Work.Kernels.Kaxis, dif_neg ht]
    ring

/-- **The `T`-ladder of the naive contour transform.**  If the contour integrands at `τ` and at
`τ - 1` are both integrable, then

  `kernelTransform K (τ+1) r = 2 * kernelTransform K τ r - kernelTransform K (τ-1) r`. -/
lemma kernelTransform_vadd_of_integrable (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ)
    (h0 : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0))
    (h1 : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ τ) t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) r
      = 2 * Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r
        - Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ τ) r := by
  set F : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t *
    Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hF
  set G : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ τ) t *
    Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hG
  set H : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) t *
    Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hH
  have hpt : ∀ t : ℝ, H t = 2 * F t - G t := by
    intro t
    have h := Kaxis_T2_Kfun_s ℓ d hd ((-1 : ℝ) +ᵥ τ) t
    have h2 : (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = (1 : ℝ) +ᵥ τ := by
      rw [vadd_vadd]; norm_num
    have h1' : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by
      rw [vadd_vadd]; norm_num
    rw [h2, h1'] at h
    simp only [hH, hF, hG]
    linear_combination Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) * h
  have h2G : MeasureTheory.IntegrableOn (fun t : ℝ => 2 * F t) (Set.Ioi 0) := h0.const_mul 2
  have hInt : (∫ t in Set.Ioi (0:ℝ), H t) = 2 * (∫ t in Set.Ioi (0:ℝ), F t)
      - (∫ t in Set.Ioi (0:ℝ), G t) := by
    calc (∫ t in Set.Ioi (0:ℝ), H t)
        = (∫ t in Set.Ioi (0:ℝ), (2 * F t - G t)) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t)
      _ = (∫ t in Set.Ioi (0:ℝ), 2 * F t) - (∫ t in Set.Ioi (0:ℝ), G t) :=
          MeasureTheory.integral_sub h2G h1
      _ = 2 * (∫ t in Set.Ioi (0:ℝ), F t) - (∫ t in Set.Ioi (0:ℝ), G t) := by
          rw [MeasureTheory.integral_const_mul]
  simp only [Work.Kernels.kernelTransform, hF, hG, hH]
  rw [hInt]
  ring

/-- **The `S`-transport of the naive contour transform.**
`kernelTransform K (S • τ) r = -(τ)^{d/2} · kernelTransform Khat τ r`. -/
lemma kernelTransform_S_smul_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) :
    Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • τ) r
      = - (τ : ℂ) ^ ((d : ℤ) / 2) *
        Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) τ r := by
  have h := kernelTransform_slashKernel ℓ d ModularGroup.S τ r
  have hS : Work.Kernels.kernelTransform (slashKernel ℓ d ModularGroup.S) τ r
      = - Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) τ r := by
    rw [ts_slashKernel_S ℓ d hd]
    exact ts_kernelTransform_neg (Work.Kernels.Khat ℓ d) τ r
  rw [hS, ts_jFun_S τ] at h
  have hτne : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hτ : (τ : ℂ) ^ (-((d : ℤ) / 2)) *
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • τ) r
      = - Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) τ r := h.symm
  have key : (τ : ℂ) ^ ((d : ℤ) / 2) * ((τ : ℂ) ^ (-((d : ℤ) / 2)) *
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • τ) r)
      = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • τ) r := by
    rw [← mul_assoc, ← zpow_add₀ hτne, add_neg_cancel, zpow_zero, one_mul]
  calc Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • τ) r
      = (τ : ℂ) ^ ((d : ℤ) / 2) * ((τ : ℂ) ^ (-((d : ℤ) / 2)) *
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • τ) r) :=
        key.symm
    _ = (τ : ℂ) ^ ((d : ℤ) / 2) * (- Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) τ r) := by
        rw [hτ]
    _ = - (τ : ℂ) ^ ((d : ℤ) / 2) * Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) τ r := by
        ring


/-- **The cusp-`0` disk bound for `K` from the `K̂`-funnel bound.**  If the `r`-seminorms of the
`K̂`-transform have moderate growth on the funnel (CKMRV Proposition 4.6 at the cusp `∞` of `K̂`),
then the `r`-seminorms of the `K`-transform are bounded on the cusp-`0` disk
`E = KEpsilon = S(funnel)`, by the `S`-transport `kernelTransform_S_smul_eq`. -/
lemma seminorm_KEpsilon_of_khat_funnel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (h : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (u : UpperHalfPlane) (r : ℝ), u ∈ KEpsilon →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) u s) r‖
          ≤ C * (Work.Kernels.scale u) ^ N := by
  intro k l
  obtain ⟨C, N, hC, hN, hb⟩ := h k l
  refine ⟨C * 3 ^ N, N + (d : ℝ) / 2, mul_nonneg hC (Real.rpow_nonneg (by norm_num) N),
    add_nonneg hN (by positivity), ?_⟩
  intro u r hu
  obtain ⟨huD, hu2⟩ := hu
  have hSuD : ModularGroup.S • u ∈ Work.Asymptotics.DomainD := S_smul_mem_DomainD huD
  have hSS : ModularGroup.S • (ModularGroup.S • u) = u := Work.Rigidity.S_smul_S_smul u
  have hkey : ∀ s : ℝ, Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) u s
      = - (↑(ModularGroup.S • u) : ℂ) ^ ((d : ℤ) / 2) *
        Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) (ModularGroup.S • u) s := by
    intro s
    have h := kernelTransform_S_smul_eq ℓ d hd (ModularGroup.S • u) s
    rwa [hSS] at h
  have hderiv : iteratedDeriv l (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) u s) r
      = - (↑(ModularGroup.S • u) : ℂ) ^ ((d : ℤ) / 2) *
        iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) (ModularGroup.S • u) s) r := by
    rw [show (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) u s)
      = fun s : ℝ => - (↑(ModularGroup.S • u) : ℂ) ^ ((d : ℤ) / 2) *
          Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) (ModularGroup.S • u) s
      from funext hkey]
    exact iteratedDeriv_const_mul_field _ _
  have hnorm_c : ‖(↑(ModularGroup.S • u) : ℂ) ^ ((d : ℤ) / 2)‖
      = ‖(↑(ModularGroup.S • u) : ℂ)‖ ^ ((d : ℝ) / 2) := by
    rw [norm_zpow, ← Real.rpow_intCast]
    congr 1
    rcases hd with rfl | rfl <;> norm_num
  have hnormS : ‖(↑(ModularGroup.S • u) : ℂ)‖ = (‖(u : ℂ)‖)⁻¹ := by
    have hcoe : ((ModularGroup.S • u : ℍ) : ℂ) = -((u : ℂ))⁻¹ := Work.Rigidity.coe_S_smul u
    rw [hcoe, norm_neg, norm_inv]
  have hSu_im : (ModularGroup.S • u).im = u.im / ‖(u : ℂ)‖ ^ 2 := by
    rw [Work.Kernels.im_smul_eq, ts_jFun_S]
  -- crude comparisons on the cusp-`0` disk
  have hscaleS : Work.Kernels.scale (ModularGroup.S • u) ≤ 3 * Work.Kernels.scale u := by
    have h1 : ((ModularGroup.S • u).im)⁻¹ ≤ 1 / 2 := by
      have h2 : 2 ≤ u.im / ‖(u : ℂ)‖ ^ 2 := by rw [← hSu_im]; exact hu2
      rw [le_div_iff₀ (pow_pos (norm_pos_iff.mpr u.ne_zero) 2)] at h2
      rw [hSu_im, inv_div, div_le_iff₀ u.im_pos]
      nlinarith [h2]
    have h2 : ‖(↑(ModularGroup.S • u) : ℂ)‖ ≤ Work.Kernels.scale u := by
      rw [hnormS]
      have h3 : (u.im)⁻¹ ≤ Work.Kernels.scale u := Work.Kernels.inv_im_le_scale u
      have h4 : (‖(u : ℂ)‖)⁻¹ ≤ (u.im)⁻¹ := by
        rw [inv_le_inv₀ (norm_pos_iff.mpr u.ne_zero) u.im_pos]
        exact Work.Kernels.im_le_coe_norm u
      linarith
    rw [Work.Kernels.scale]
    have h5 : (1 : ℝ) ≤ Work.Kernels.scale u := Work.Kernels.one_le_scale u
    linarith
  have hfac : ‖(↑(ModularGroup.S • u) : ℂ)‖ ^ ((d : ℝ) / 2)
      ≤ (Work.Kernels.scale u) ^ ((d : ℝ) / 2) := by
    rw [hnormS]
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    have h3 : (u.im)⁻¹ ≤ Work.Kernels.scale u := Work.Kernels.inv_im_le_scale u
    have h4 : (‖(u : ℂ)‖)⁻¹ ≤ (u.im)⁻¹ := by
      rw [inv_le_inv₀ (norm_pos_iff.mpr u.ne_zero) u.im_pos]
      exact Work.Kernels.im_le_coe_norm u
    linarith
  have hKhat := hb (ModularGroup.S • u) r hSuD hu2
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) u s) r‖
      = (|r| ^ k) * (‖(↑(ModularGroup.S • u) : ℂ) ^ ((d : ℤ) / 2)‖ *
          ‖iteratedDeriv l (fun s : ℝ =>
            Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) (ModularGroup.S • u) s) r‖) := by
        rw [hderiv, norm_mul, norm_neg]
    _ = ‖(↑(ModularGroup.S • u) : ℂ) ^ ((d : ℤ) / 2)‖ * ((|r| ^ k) *
          ‖iteratedDeriv l (fun s : ℝ =>
            Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) (ModularGroup.S • u) s) r‖) := by
        ring
    _ ≤ ‖(↑(ModularGroup.S • u) : ℂ) ^ ((d : ℤ) / 2)‖ *
          (C * (Work.Kernels.scale (ModularGroup.S • u)) ^ N) :=
        mul_le_mul_of_nonneg_left hKhat (norm_nonneg _)
    _ = ‖(↑(ModularGroup.S • u) : ℂ)‖ ^ ((d : ℝ) / 2) *
          (C * (Work.Kernels.scale (ModularGroup.S • u)) ^ N) := by rw [hnorm_c]
    _ ≤ (Work.Kernels.scale u) ^ ((d : ℝ) / 2) * (C * (3 * Work.Kernels.scale u) ^ N) := by
        have hb1 : (0 : ℝ) ≤ C * (Work.Kernels.scale (ModularGroup.S • u)) ^ N :=
          mul_nonneg hC (Real.rpow_nonneg (le_trans zero_le_one (Work.Kernels.one_le_scale _)) N)
        have hb2 : (0 : ℝ) ≤ (Work.Kernels.scale u) ^ ((d : ℝ) / 2) :=
          Real.rpow_nonneg (le_trans zero_le_one (Work.Kernels.one_le_scale u)) _
        have h2 : C * (Work.Kernels.scale (ModularGroup.S • u)) ^ N
            ≤ C * (3 * Work.Kernels.scale u) ^ N :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (le_trans zero_le_one (Work.Kernels.one_le_scale _)) hscaleS hN) hC
        calc ‖(↑(ModularGroup.S • u) : ℂ)‖ ^ ((d : ℝ) / 2)
              * (C * (Work.Kernels.scale (ModularGroup.S • u)) ^ N)
            ≤ (Work.Kernels.scale u) ^ ((d : ℝ) / 2)
              * (C * (Work.Kernels.scale (ModularGroup.S • u)) ^ N) :=
              mul_le_mul_of_nonneg_right hfac hb1
          _ ≤ (Work.Kernels.scale u) ^ ((d : ℝ) / 2) * (C * (3 * Work.Kernels.scale u) ^ N) :=
              mul_le_mul_of_nonneg_left h2 hb2
    _ = C * 3 ^ N * (Work.Kernels.scale u) ^ (N + (d : ℝ) / 2) := by
        have h3 : (3 * Work.Kernels.scale u) ^ N = 3 ^ N * (Work.Kernels.scale u) ^ N :=
          Real.mul_rpow (by norm_num) (le_trans zero_le_one (Work.Kernels.one_le_scale u))
        have h4 : (Work.Kernels.scale u) ^ ((d : ℝ) / 2) * (Work.Kernels.scale u) ^ N
            = (Work.Kernels.scale u) ^ (N + (d : ℝ) / 2) := by
          rw [← Real.rpow_add (Work.Kernels.scale_pos u)]
          ring_nf
        rw [h3]
        calc (Work.Kernels.scale u) ^ ((d : ℝ) / 2) * (C * (3 ^ N * (Work.Kernels.scale u) ^ N))
            = C * 3 ^ N * ((Work.Kernels.scale u) ^ ((d : ℝ) / 2) * (Work.Kernels.scale u) ^ N) := by
              ring
          _ = C * 3 ^ N * (Work.Kernels.scale u) ^ (N + (d : ℝ) / 2) := by
              rw [← Real.rpow_add (Work.Kernels.scale_pos u), add_comm]


/-- **The cusp-`0` half-tile bound for `K̂` from the half-funnel bound.**  Dually to
`seminorm_KEpsilon_of_khat_funnel`, the `S`-transport `kernelTransform_S_smul_eq` turns the
(axiom-clean) half-funnel bound for `K` into a bound for `K̂` on
`E_{1/2} = {x ∈ 𝒟 : 1/2 ≤ Im (S • x)}` (the cusp-`0` half tile), which is what the band analysis of
the cusp-`1` region needs. -/
lemma seminorm_khat_Ehalf_of_halfFunnel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (h : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (x : UpperHalfPlane) (r : ℝ), x ∈ Work.Asymptotics.DomainD →
        (1 : ℝ) / 2 ≤ (ModularGroup.S • x).im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) x s) r‖
          ≤ C * (Work.Kernels.scale x) ^ N := by
  intro k l
  obtain ⟨C, N, hC, hN, hb⟩ := h k l
  refine ⟨C * 4 ^ N, N + (d : ℝ) / 2,
    mul_nonneg hC (Real.rpow_nonneg (by norm_num) N), add_nonneg hN (by positivity), ?_⟩
  intro x r hxD hxhalf
  have hSxD : ModularGroup.S • x ∈ Work.Asymptotics.DomainD := S_smul_mem_DomainD hxD
  have hSS : ModularGroup.S • (ModularGroup.S • x) = x := Work.Rigidity.S_smul_S_smul x
  have hkey := kernelTransform_S_smul_eq ℓ d hd x r
  -- `G_K (S•x) r = -(x)^{d/2} * Khat x r`
  have hderiv : iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) x s) r
      = - (↑x : ℂ) ^ (-((d : ℤ) / 2)) *
        iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • x) s) r := by
    have hfun : (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) x s)
        = fun s : ℝ => - (↑x : ℂ) ^ (-((d : ℤ) / 2)) *
            Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • x) s := by
      funext s
      have h1 := kernelTransform_S_smul_eq ℓ d hd x s
      have h2 : (x : ℂ) ^ (-((d : ℤ) / 2)) * ((x : ℂ) ^ ((d : ℤ) / 2) *
            Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) x s)
          = Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) x s := by
        rw [← mul_assoc, ← zpow_add₀ (x.ne_zero), neg_add_cancel, zpow_zero, one_mul]
      rw [h1]
      rw [show - (x : ℂ) ^ (-((d : ℤ) / 2)) * (- (x : ℂ) ^ ((d : ℤ) / 2) *
            Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) x s)
          = (x : ℂ) ^ (-((d : ℤ) / 2)) * ((x : ℂ) ^ ((d : ℤ) / 2) *
            Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) x s) by ring]
      rw [h2]
    rw [hfun]
    exact iteratedDeriv_const_mul_field _ _
  have hnorm_c : ‖(↑x : ℂ) ^ (-((d : ℤ) / 2))‖ = ‖(↑x : ℂ)‖ ^ (-((d : ℝ) / 2)) := by
    rw [norm_zpow, ← Real.rpow_intCast]
    congr 1
    rcases hd with rfl | rfl <;> norm_num
  have hfac : ‖(↑x : ℂ)‖ ^ (-((d : ℝ) / 2)) ≤ (Work.Kernels.scale x) ^ ((d : ℝ) / 2) := by
    have hxpos : 0 < ‖(x : ℂ)‖ := norm_pos_iff.mpr x.ne_zero
    have h1 : (‖(x : ℂ)‖)⁻¹ ≤ Work.Kernels.scale x := by
      have h2 : (x.im)⁻¹ ≤ Work.Kernels.scale x := Work.Kernels.inv_im_le_scale x
      have h3 : (‖(x : ℂ)‖)⁻¹ ≤ (x.im)⁻¹ := by
        rw [inv_le_inv₀ hxpos x.im_pos]
        exact Work.Kernels.im_le_coe_norm x
      linarith
    have h4 : ‖(↑x : ℂ)‖ ^ (-((d : ℝ) / 2)) = ((‖(x : ℂ)‖)⁻¹) ^ ((d : ℝ) / 2) := by
      rw [Real.rpow_neg hxpos.le, Real.inv_rpow hxpos.le]
    rw [h4]
    exact Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hscaleS : Work.Kernels.scale (ModularGroup.S • x) ≤ 4 * Work.Kernels.scale x := by
    have hSu_im : (ModularGroup.S • x).im = x.im / ‖(x : ℂ)‖ ^ 2 := by
      rw [Work.Kernels.im_smul_eq, ts_jFun_S]
    have hnormS : ‖(↑(ModularGroup.S • x) : ℂ)‖ = (‖(x : ℂ)‖)⁻¹ := by
      have hcoe : ((ModularGroup.S • x : ℍ) : ℂ) = -((x : ℂ))⁻¹ := Work.Rigidity.coe_S_smul x
      rw [hcoe, norm_neg, norm_inv]
    have h1 : ((ModularGroup.S • x).im)⁻¹ ≤ 2 := by
      have h2 : (1 : ℝ) / 2 ≤ x.im / ‖(x : ℂ)‖ ^ 2 := by
        rw [← hSu_im]; exact hxhalf
      rw [le_div_iff₀ (pow_pos (norm_pos_iff.mpr x.ne_zero) 2)] at h2
      rw [hSu_im, inv_div, div_le_iff₀ x.im_pos]
      linarith
    have h2 : ‖(↑(ModularGroup.S • x) : ℂ)‖ ≤ Work.Kernels.scale x := by
      rw [hnormS]
      have h3 : (x.im)⁻¹ ≤ Work.Kernels.scale x := Work.Kernels.inv_im_le_scale x
      have h4 : (‖(x : ℂ)‖)⁻¹ ≤ (x.im)⁻¹ := by
        rw [inv_le_inv₀ (norm_pos_iff.mpr x.ne_zero) x.im_pos]
        exact Work.Kernels.im_le_coe_norm x
      linarith
    rw [Work.Kernels.scale]
    have h5 : (1 : ℝ) ≤ Work.Kernels.scale x := Work.Kernels.one_le_scale x
    linarith
  have hK := hb (ModularGroup.S • x) r hSxD hxhalf
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Khat ℓ d) x s) r‖
      = ‖(↑x : ℂ) ^ (-((d : ℤ) / 2))‖ * ((|r| ^ k) *
          ‖iteratedDeriv l (fun s : ℝ =>
            Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • x) s) r‖) := by
        rw [hderiv, norm_mul, norm_neg]
        ring
    _ ≤ ‖(↑x : ℂ) ^ (-((d : ℤ) / 2))‖ *
          (C * (Work.Kernels.scale (ModularGroup.S • x)) ^ N) :=
        mul_le_mul_of_nonneg_left hK (norm_nonneg _)
    _ = ‖(↑x : ℂ)‖ ^ (-((d : ℝ) / 2)) *
          (C * (Work.Kernels.scale (ModularGroup.S • x)) ^ N) := by rw [hnorm_c]
    _ ≤ (Work.Kernels.scale x) ^ ((d : ℝ) / 2) * (C * (4 * Work.Kernels.scale x) ^ N) := by
        have hb1 : (0 : ℝ) ≤ C * (Work.Kernels.scale (ModularGroup.S • x)) ^ N :=
          mul_nonneg hC (Real.rpow_nonneg (le_trans zero_le_one (Work.Kernels.one_le_scale _)) N)
        have hb2 : (0 : ℝ) ≤ (Work.Kernels.scale x) ^ ((d : ℝ) / 2) :=
          Real.rpow_nonneg (le_trans zero_le_one (Work.Kernels.one_le_scale x)) _
        have h2 : C * (Work.Kernels.scale (ModularGroup.S • x)) ^ N
            ≤ C * (4 * Work.Kernels.scale x) ^ N :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (le_trans zero_le_one (Work.Kernels.one_le_scale _)) hscaleS hN) hC
        calc ‖(↑x : ℂ)‖ ^ (-((d : ℝ) / 2)) * (C * (Work.Kernels.scale (ModularGroup.S • x)) ^ N)
            ≤ (Work.Kernels.scale x) ^ ((d : ℝ) / 2)
              * (C * (Work.Kernels.scale (ModularGroup.S • x)) ^ N) :=
              mul_le_mul_of_nonneg_right hfac hb1
          _ ≤ (Work.Kernels.scale x) ^ ((d : ℝ) / 2) * (C * (4 * Work.Kernels.scale x) ^ N) :=
              mul_le_mul_of_nonneg_left h2 hb2
    _ = C * 4 ^ N * (Work.Kernels.scale x) ^ (N + (d : ℝ) / 2) := by
        have h3 : (4 * Work.Kernels.scale x) ^ N = 4 ^ N * (Work.Kernels.scale x) ^ N :=
          Real.mul_rpow (by norm_num) (le_trans zero_le_one (Work.Kernels.one_le_scale x))
        rw [h3]
        calc (Work.Kernels.scale x) ^ ((d : ℝ) / 2) * (C * (4 ^ N * (Work.Kernels.scale x) ^ N))
            = C * 4 ^ N * ((Work.Kernels.scale x) ^ ((d : ℝ) / 2) * (Work.Kernels.scale x) ^ N) := by
              ring
          _ = C * 4 ^ N * (Work.Kernels.scale x) ^ (N + (d : ℝ) / 2) := by
              rw [← Real.rpow_add (Work.Kernels.scale_pos x), add_comm]


/-- Arithmetic core of the `E`-emptiness for `Re u < 0`: the translate `w = 1 + u` cannot satisfy
`2 ≤ Im (S • w)` (i.e. `2((1+x)² + y²) ≤ y`) together with the `Tregion` inequality
`x² + y² ≤ 2y` and the arc inequality `x² + x + y² > 0`. -/
lemma ts_not_E_aux {x y : ℝ} (hy0 : 0 < y)
    (hA : 2 * ((1 + x) ^ 2 + y ^ 2) ≤ y) (hB : x ^ 2 + y ^ 2 ≤ 2 * y)
    (hC : 0 < x ^ 2 + x + y ^ 2) : False := by
  nlinarith [hA, hB, hC, sq_nonneg (5 * y - 2), sq_nonneg (2 * x + 1),
    sq_nonneg (4 * x + 3 * y + 2), sq_nonneg (x + 1), sq_nonneg (y - 1)]

/-- **The `E`-case is empty for `Re u < 0`.**  For `u ∈ Tregion` with `Re u < 0` one cannot have
`2 ≤ Im (S • (1 + u))`: that would put the translate `1 + u` in the cusp-`0` funnel, contradicting
the `Tregion` inequalities together with the arc condition of `𝒟`. -/
lemma ts_not_two_le_im_S_vadd_one (u : ℍ) (hu : u ∈ Work.Asymptotics.Tregion) (hx : u.re < 0) :
    ¬ (2 ≤ (ModularGroup.S • ((1 : ℝ) +ᵥ u)).im) := by
  intro hE
  obtain ⟨huD, hSlo, -⟩ := hu
  have hmem := mem_DomainD.mp huD
  have hy0 : 0 < u.im := u.im_pos
  have hpos : (0 : ℝ) < ‖((((1 : ℝ) +ᵥ u : ℍ)) : ℂ)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr ((1 : ℝ) +ᵥ u).ne_zero) 2
  rw [ts_im_S_smulTS] at hE
  have hnorm : ‖((((1 : ℝ) +ᵥ u : ℍ)) : ℂ)‖ ^ 2 = (1 + u.re) ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_vadd]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have him : (((1 : ℝ) +ᵥ u : ℍ)).im = u.im := UpperHalfPlane.vadd_im 1 u
  have hA : 2 * ((1 + u.re) ^ 2 + u.im ^ 2) ≤ u.im := by
    have h := (le_div_iff₀ hpos).mp hE
    rw [hnorm, him] at h
    exact h
  have hB : u.re ^ 2 + u.im ^ 2 ≤ 2 * u.im := by
    have h := hSlo
    rw [ts_im_S_smulTS] at h
    have h2 := (le_div_iff₀ (pow_pos (norm_pos_iff.mpr u.ne_zero) 2)).mp h
    rw [ts_normSq_coe u] at h2
    linarith
  have hC : 0 < u.re ^ 2 + u.re + u.im ^ 2 := (ts_arc_ineqs huD).2
  exact ts_not_E_aux hy0 hA hB hC

/-- Arithmetic core of the `|Re u| < 1/4` fact (see `ts_lt_quarter_of_im_S_vadd_one`). -/
lemma ts_low_aux {x y : ℝ} (hx1 : -1 < x) (hy0 : 0 < y) (hy : y < 1 / 2) (hx : x ≤ -1 / 4)
    (hE : 1 < (1 + x) ^ 2 + (y - 1) ^ 2) (hC : 0 < x ^ 2 + x + y ^ 2)
    (hB : x ^ 2 + y ^ 2 ≤ 2 * y) : False := by
  by_cases hx2 : -(3:ℝ) / 4 ≤ x
  · have h1 : (3:ℝ) / 16 ≤ -x * (x + 1) := by nlinarith
    have h2 : (3:ℝ) / 16 < y ^ 2 := by nlinarith
    have h3 : (1 + x) ^ 2 ≤ 9 / 16 := by nlinarith
    have h4 : (7:ℝ) / 16 < (y - 1) ^ 2 := by nlinarith
    nlinarith [h2, h4, sq_nonneg (y - 1 / 2), sq_nonneg (y * (1 - y))]
  · have h1 : (9:ℝ) / 16 < x ^ 2 := by nlinarith
    have h4 : (y - 1) ^ 2 < 7 / 16 := by nlinarith [hB, h1]
    have h6 : ((3:ℝ) / 4) ^ 2 < (1 + x) ^ 2 := by nlinarith [hE, h4]
    have h7 : ((3:ℝ) / 4) < |1 + x| := by
      have h := sq_lt_sq.mp h6
      rwa [abs_of_pos (by norm_num : (0:ℝ) < 3 / 4)] at h
    rw [abs_of_pos (by linarith : (0:ℝ) < 1 + x)] at h7
    linarith

/-- **`|Re u| < 1/4` when `Im (S • (1+u)) < 1/2`.**  For `u ∈ Tregion` with `Re u < 0`,
`Im u < 1/2`, the condition `Im (S • (1+u)) < 1/2` (i.e. `(1+x)² + (y-1)² > 1`) together with the
arc condition of `𝒟` and the `Tregion` inequality `x² + y² ≤ 2y` forces `x > -1/4`. -/
lemma ts_lt_quarter_of_im_S_vadd_one (u : ℍ) (hu : u ∈ Work.Asymptotics.Tregion)
    (hx : u.re < 0) (hy : u.im < 1 / 2)
    (hE : (ModularGroup.S • ((1 : ℝ) +ᵥ u)).im < 1 / 2) : |u.re| < 1 / 4 := by
  by_cases hle : u.re ≤ -1 / 4
  · exfalso
    obtain ⟨huD, hSlo, -⟩ := hu
    have hmem := mem_DomainD.mp huD
    have hy0 : 0 < u.im := u.im_pos
    have hpos : (0 : ℝ) < ‖((((1 : ℝ) +ᵥ u : ℍ)) : ℂ)‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr ((1 : ℝ) +ᵥ u).ne_zero) 2
    rw [ts_im_S_smulTS] at hE
    have hnorm : ‖((((1 : ℝ) +ᵥ u : ℍ)) : ℂ)‖ ^ 2 = (1 + u.re) ^ 2 + u.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_vadd]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have him : (((1 : ℝ) +ᵥ u : ℍ)).im = u.im := UpperHalfPlane.vadd_im 1 u
    have hE' : 1 < (1 + u.re) ^ 2 + (u.im - 1) ^ 2 := by
      rw [hnorm, him] at hE
      have hpos' : (0 : ℝ) < (1 + u.re) ^ 2 + u.im ^ 2 := by rw [← hnorm]; exact hpos
      have h := (div_lt_iff₀ hpos').mp hE
      nlinarith [h]
    have hB : u.re ^ 2 + u.im ^ 2 ≤ 2 * u.im := by
      have h := hSlo
      rw [ts_im_S_smulTS] at h
      have h2 := (le_div_iff₀ (pow_pos (norm_pos_iff.mpr u.ne_zero) 2)).mp h
      rw [ts_normSq_coe u] at h2
      linarith
    have hC : 0 < u.re ^ 2 + u.re + u.im ^ 2 := (ts_arc_ineqs huD).2
    exact ts_low_aux hmem.1 hy0 hy hle hE' hC hB
  · rw [abs_lt]
    exact ⟨by linarith [not_le.mp hle], by linarith⟩


/-- **The low-half tile input, isolated.**  The `r`-seminorm bound for the naive transform at the
cusp-`1` translate `1 + w` of a point `w` of `𝒟` with `Im (S • w) ≥ 1/2`, `Im w ≤ 1/2`,
`|Re w| < 1/4` (the "low half" of the cusp-`±1` tile).  It is the `n = 1` specialization of
`Work.Asymptotics.cuspTileLowHalfBound` and is requested as
`Asymptotics/Kfun_cuspOneLowHalfTile`. -/
def CuspOneLowHalfTile (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
    ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Work.Asymptotics.DomainD →
      (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im → w.im ≤ 1 / 2 → |w.re| < 1 / 4 →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
        ≤ C * (Work.Kernels.scale w) ^ N

/-- **The `Re u < 0` half of the band tile.**  For `u ∈ Tregion` with `Re u < 0` the translate
`w = 1 + u` lies in `𝒟` and the bound at `w` comes from the clean pieces:

* `Work.Asymptotics.seminormK_cusp0_half`, when `w ∈ Tregion` (i.e. `1/2 ≤ Im (S • w) ≤ 2`);
* `Work.Asymptotics.kernelTransform_seminorm_halfFunnel`, when `Im u ≥ 1/2` (then `w ∈ 𝒟_{1/2}`);
* the low-half tile `CuspOneLowHalfTile` applied at `u`, when `Im (S • w) < 1/2` — in that case
  `ts_lt_quarter_of_im_S_vadd_one` gives `|Re u| < 1/4`, and the case `w ∈ E = KEpsilon` is
  impossible by `ts_not_two_le_im_S_vadd_one`. -/
lemma CuspOneBandTile_xneg_of_lowTile (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (hLow : CuspOneLowHalfTile ℓ d) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (u : UpperHalfPlane) (r : ℝ), u ∈ Work.Asymptotics.Tregion → u.re < 0 →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖
          ≤ C * (Work.Kernels.scale u) ^ N := by
  intro k l
  obtain ⟨CL, NL, hCL, hNL, hbL⟩ := hLow k l
  obtain ⟨CG, hCG, hbG⟩ := Work.HFN.seminormK_cusp0_half ℓ d hd k l
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hbH⟩ :=
    Work.Asymptotics.kernelTransform_seminorm_halfFunnel ℓ d hd k l
  refine ⟨max CL (max CG (α * 2 ^ β + γ * 3 ^ δ)), max NL 0, ?_, ?_, ?_⟩
  · positivity
  · exact le_max_right _ _
  · intro u r hu hx
    set Cbig : ℝ := max CL (max CG (α * 2 ^ β + γ * 3 ^ δ)) with hCbig
    set Nbig : ℝ := max NL 0 with hNbig
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale u := Work.Kernels.one_le_scale u
    have hNge : (1 : ℝ) ≤ (Work.Kernels.scale u) ^ Nbig :=
      Real.one_le_rpow hs1 (by rw [hNbig]; exact le_max_right _ _)
    have hpowN_nonneg : (0 : ℝ) ≤ (Work.Kernels.scale u) ^ Nbig :=
      Real.rpow_nonneg (le_trans (by norm_num) hs1) _
    have hNLle : (Work.Kernels.scale u) ^ NL ≤ (Work.Kernels.scale u) ^ Nbig :=
      Real.rpow_le_rpow_of_exponent_le hs1 (by rw [hNbig]; exact le_max_left _ _)
    have hCLle : CL ≤ Cbig := by rw [hCbig]; exact le_max_left _ _
    have hCGle : CG ≤ Cbig := by
      rw [hCbig]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hHle : α * 2 ^ β + γ * 3 ^ δ ≤ Cbig := by
      rw [hCbig]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hwD : ((1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD :=
      ts_vadd_one_mem_DomainD_of_neg hu.1 hx
    have himw : (((1 : ℝ) +ᵥ u : ℍ)).im = u.im := UpperHalfPlane.vadd_im 1 u
    have hnormu : ‖(u : ℂ)‖ ≤ 2 := by
      have h2 : ‖(u : ℂ)‖ ^ 2 ≤ 2 * u.im := (ts_Tregion_ineqs hu).2
      nlinarith [norm_nonneg (u : ℂ), u.im_pos, h2, Work.Kernels.im_le_coe_norm u]
    have hnormw : ‖(((1 : ℝ) +ᵥ u : ℍ) : ℂ)‖ ≤ 3 := by
      have hcoe : ((((1 : ℝ) +ᵥ u : ℍ)) : ℂ) = (1 : ℂ) + (u : ℂ) :=
        UpperHalfPlane.coe_vadd 1 u
      rw [hcoe]
      have h := norm_add_le (1 : ℂ) (u : ℂ)
      rw [norm_one] at h
      linarith
    by_cases hy : u.im < 1 / 2
    · by_cases hhalf : (1 : ℝ) / 2 ≤ (ModularGroup.S • ((1 : ℝ) +ᵥ u)).im
      · have hT : (ModularGroup.S • ((1 : ℝ) +ᵥ u)).im ≤ 2 :=
          le_of_lt (not_le.mp (ts_not_two_le_im_S_vadd_one u hu hx))
        have h := hbG ((1 : ℝ) +ᵥ u) r hwD hhalf hT
        refine le_trans h ?_
        calc CG = CG * 1 := (mul_one CG).symm
          _ ≤ CG * (Work.Kernels.scale u) ^ Nbig := mul_le_mul_of_nonneg_left hNge hCG
          _ ≤ Cbig * (Work.Kernels.scale u) ^ Nbig :=
              mul_le_mul_of_nonneg_right hCGle hpowN_nonneg
      · have hq : |u.re| < 1 / 4 :=
          ts_lt_quarter_of_im_S_vadd_one u hu hx hy (not_le.mp hhalf)
        have h := hbL u r hu.1 hu.2.1 (le_of_lt hy) hq
        refine le_trans h ?_
        calc CL * (Work.Kernels.scale u) ^ NL ≤ CL * (Work.Kernels.scale u) ^ Nbig :=
              mul_le_mul_of_nonneg_left hNLle hCL
          _ ≤ Cbig * (Work.Kernels.scale u) ^ Nbig :=
              mul_le_mul_of_nonneg_right hCLle hpowN_nonneg
    · have h1 : (1 : ℝ) / 2 ≤ (((1 : ℝ) +ᵥ u : ℍ)).im := by rw [himw]; linarith
      have h := hbH ((1 : ℝ) +ᵥ u) r hwD h1
      refine le_trans h ?_
      have himpos : (0 : ℝ) < (((1 : ℝ) +ᵥ u : ℍ)).im := by rw [himw]; exact u.im_pos
      have h1' : (((1 : ℝ) +ᵥ u : ℍ)).im ^ (-β) ≤ 2 ^ β := by
        have h2 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1/2) h1
          (by linarith : -β ≤ 0)
        rwa [show ((1:ℝ)/2) ^ (-β) = 2 ^ β by
          rw [show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
            Real.rpow_neg (by norm_num), inv_inv]] at h2
      have h2' : ‖(((1 : ℝ) +ᵥ u : ℍ) : ℂ)‖ ^ δ ≤ 3 ^ δ :=
        Real.rpow_le_rpow (norm_nonneg _) hnormw hδ
      have h3 : α * (((1 : ℝ) +ᵥ u : ℍ)).im ^ (-β) + γ * ‖(((1 : ℝ) +ᵥ u : ℍ) : ℂ)‖ ^ δ
          ≤ α * 2 ^ β + γ * 3 ^ δ := by
        have ha := mul_le_mul_of_nonneg_left h1' hα
        have hb := mul_le_mul_of_nonneg_left h2' hγ
        linarith
      refine le_trans h3 ?_
      calc α * 2 ^ β + γ * 3 ^ δ = (α * 2 ^ β + γ * 3 ^ δ) * 1 := (mul_one _).symm
        _ ≤ (α * 2 ^ β + γ * 3 ^ δ) * (Work.Kernels.scale u) ^ Nbig :=
            mul_le_mul_of_nonneg_left hNge (by positivity)
        _ ≤ Cbig * (Work.Kernels.scale u) ^ Nbig :=
            mul_le_mul_of_nonneg_right hHle hpowN_nonneg


/-- **The bad-line (junk) input, isolated.**  The naive transform vanishes at the translates
`1 + iy` of the imaginary axis (there the pole `z = iy` of `z ↦ K (1+iy) z` sits on the contour and
the Bochner integral takes the junk value `0`).  It is the branch-neutral form of
`Work.Asymptotics.bad_line_kernelTransform_eq_zero`, requested as
`Asymptotics/Kfun_vadd_one_imagAxis_eq_zero`. -/
def CuspOneBadLineZero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ (y : ℝ) (hy : 0 < y) (r : ℝ),
    Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d)
      ((1 : ℝ) +ᵥ Work.Kernels.imagAxis y hy) r = 0

/-- **The `T`-ladder input for `Re u ≥ 1/4`.**  On this range `u - 1 ∈ Tregion` for `Im u < 1/2`
(`ts_vadd_neg_one_mem_Tregion`) and `u - 1 ∈ 𝒟_{1/2}` for `Im u ≥ 1/2`, so the ladder
`G(1+u) = 2 G(u) - G(u-1)` together with `Work.Asymptotics.seminormK_cusp0_half` and
`Work.Asymptotics.kernelTransform_seminorm_halfFunnel` bounds the seminorms at `1 + u`.  It is
requested as `Asymptotics/Kfun_cuspOneBand_ladder`. -/
def CuspOneBandLadder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
    ∀ (u : UpperHalfPlane) (r : ℝ), u ∈ Work.Asymptotics.Tregion → (1 : ℝ) / 4 ≤ u.re →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖
        ≤ C * (Work.Kernels.scale u) ^ N

/-- **The `T`-ladder input for `0 < Re u < 1/4` and `Im u ≥ 1/2`.**  There `u - 1 ∈ 𝒟` with
`Im (u-1) = Im u ≥ 1/2`, so the ladder reduces the bound at `1 + u` to
`Work.Asymptotics.seminormK_cusp0_half` at `u` and
`Work.Asymptotics.kernelTransform_seminorm_halfFunnel` at `u - 1`. -/
def CuspOneBandLadderSmall (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
    ∀ (u : UpperHalfPlane) (r : ℝ), u ∈ Work.Asymptotics.Tregion → 0 < u.re → u.re < 1 / 4 →
      (1 : ℝ) / 2 < u.im →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖
        ≤ C * (Work.Kernels.scale u) ^ N

/-- **The `Re u ≥ 0` half of the band tile.**  The sub-cases are: `Re u = 0` (the junk value `0`
on the bad line, `CuspOneBadLineZero`); `1/4 ≤ Re u` (the ladder, `CuspOneBandLadder`);
`0 < Re u < 1/4` with `Im u > 1/2` (the ladder, `CuspOneBandLadderSmall`) and with
`Im u ≤ 1/2` (the low-half tile `CuspOneLowHalfTile` at `u`, whose hypotheses `u ∈ 𝒟`,
`Im (S•u) ≥ 1/2`, `Im u ≤ 1/2`, `|Re u| < 1/4` all hold). -/
lemma CuspOneBandTile_xpos_of_inputs (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (hLad : CuspOneBandLadder ℓ d) (hLadS : CuspOneBandLadderSmall ℓ d)
    (hLow : CuspOneLowHalfTile ℓ d) (hBL : CuspOneBadLineZero ℓ d) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (u : UpperHalfPlane) (r : ℝ), u ∈ Work.Asymptotics.Tregion → 0 ≤ u.re →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖
          ≤ C * (Work.Kernels.scale u) ^ N := by
  intro k l
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hLad k l
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hLadS k l
  obtain ⟨C3, N3, hC3, hN3, hb3⟩ := hLow k l
  refine ⟨max (max C1 C2) C3, max (max N1 N2) N3, ?_, ?_, ?_⟩
  · positivity
  · exact le_trans hN1 (le_trans (le_max_left N1 N2) (le_max_left _ _))
  · intro u r hu hx0
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale u := Work.Kernels.one_le_scale u
    have hpowN_nonneg : (0 : ℝ) ≤ (Work.Kernels.scale u) ^ (max (max N1 N2) N3) :=
      Real.rpow_nonneg (le_trans (by norm_num) hs1) _
    have hNge : (1 : ℝ) ≤ (Work.Kernels.scale u) ^ (max (max N1 N2) N3) :=
      Real.one_le_rpow hs1 (le_trans hN1 (le_trans (le_max_left N1 N2) (le_max_left _ _)))
    have hconst : ∀ c : ℝ, 0 ≤ c → c ≤ max (max C1 C2) C3 →
        c ≤ (max (max C1 C2) C3) * (Work.Kernels.scale u) ^ (max (max N1 N2) N3) := by
      intro c hc hcle
      calc c = c * 1 := (mul_one c).symm
        _ ≤ c * (Work.Kernels.scale u) ^ (max (max N1 N2) N3) :=
            mul_le_mul_of_nonneg_left hNge hc
        _ ≤ (max (max C1 C2) C3) * (Work.Kernels.scale u) ^ (max (max N1 N2) N3) :=
            mul_le_mul_of_nonneg_right hcle hpowN_nonneg
    have hscale : ∀ c N' : ℝ, 0 ≤ c → c ≤ max (max C1 C2) C3 →
        N' ≤ max (max N1 N2) N3 →
        c * (Work.Kernels.scale u) ^ N'
          ≤ (max (max C1 C2) C3) * (Work.Kernels.scale u) ^ (max (max N1 N2) N3) := by
      intro c N' hc hcle hN'
      have h1 : c * (Work.Kernels.scale u) ^ N'
          ≤ c * (Work.Kernels.scale u) ^ (max (max N1 N2) N3) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN') hc
      exact le_trans h1 (mul_le_mul_of_nonneg_right hcle hpowN_nonneg)
    by_cases hxzero : u.re = 0
    · -- the junk case: `u = iy`
      have hy0 : 0 < u.im := u.im_pos
      have hu_eq : u = Work.Kernels.imagAxis u.im hy0 := by
        have hcoe : (u : ℂ) = (u.im : ℂ) * Complex.I := by
          apply Complex.ext
          · simpa [Complex.mul_re] using hxzero
          · simp [Complex.mul_im]
        exact UpperHalfPlane.ext hcoe
      have hv : ((1 : ℝ) +ᵥ u) = ((1 : ℝ) +ᵥ Work.Kernels.imagAxis u.im hy0) :=
        congrArg (fun z : ℍ => ((1 : ℝ) +ᵥ z)) hu_eq
      have hz : ∀ s : ℝ,
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s = 0 := by
        intro s
        rw [hv]
        exact hBL u.im hy0 s
      have hfun : (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d)
          ((1 : ℝ) +ᵥ u) s) = fun _ => (0 : ℂ) := funext hz
      rw [hfun]
      have h0 : iteratedDeriv l (fun _ : ℝ => (0 : ℂ)) r = 0 := by
        rcases Nat.eq_zero_or_pos l with h | h
        · subst h; simp
        · rw [iteratedDeriv_const]; simp [h.ne']
      rw [h0, norm_zero, mul_zero]
      exact hconst 0 le_rfl (by positivity)
    · by_cases hq : (1 : ℝ) / 4 ≤ u.re
      · have h := hb1 u r hu hq
        refine le_trans h ?_
        exact hscale C1 N1 hC1 (le_trans (le_max_left _ _) (le_max_left _ _))
          (le_trans (le_max_left _ _) (le_max_left _ _))
      · have hlt : u.re < 1 / 4 := not_le.mp hq
        by_cases hy : u.im ≤ 1 / 2
        · have hpos_re : 0 < u.re := lt_of_le_of_ne hx0 (Ne.symm hxzero)
          have habs : |u.re| < 1 / 4 := by
            rw [abs_of_pos hpos_re]
            exact hlt
          have h := hb3 u r hu.1 hu.2.1 hy habs
          refine le_trans h ?_
          exact hscale C3 N3 hC3 (le_max_right _ _) (le_max_right _ _)
        · have hpos_re : 0 < u.re := lt_of_le_of_ne hx0 (Ne.symm hxzero)
          have h := hb2 u r hu hpos_re hlt (not_le.mp hy)
          refine le_trans h ?_
          exact hscale C2 N2 hC2 (le_trans (le_max_right _ _) (le_max_left _ _))
            (le_trans (le_max_right _ _) (le_max_left _ _))


/-- **The band tile from its two halves.**  `Re u ≤ 0` is `CuspOneBandTile_xneg_of_lowTile` and
`0 ≤ Re u` is `CuspOneBandTile_xpos_of_inputs`; the two constants are merged by `max`. -/
lemma CuspOneBandTile_of_inputs (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hLad : CuspOneBandLadder ℓ d) (hLadS : CuspOneBandLadderSmall ℓ d)
    (hLow : CuspOneLowHalfTile ℓ d) (hBL : CuspOneBadLineZero ℓ d) : CuspOneBandTile ℓ d := by
  intro k l
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := CuspOneBandTile_xneg_of_lowTile ℓ d hd hLow k l
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ :=
    CuspOneBandTile_xpos_of_inputs ℓ d hd hLad hLadS hLow hBL k l
  refine ⟨max C1 C2, max N1 N2, ?_, ?_, ?_⟩
  · positivity
  · exact le_trans hN1 (le_max_left N1 N2)
  · intro u r hu
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale u := Work.Kernels.one_le_scale u
    have hpowN_nonneg : (0 : ℝ) ≤ (Work.Kernels.scale u) ^ (max N1 N2) :=
      Real.rpow_nonneg (le_trans (by norm_num) hs1) _
    have key : ∀ c N' : ℝ, 0 ≤ c → c ≤ max C1 C2 → N' ≤ max N1 N2 →
        c * (Work.Kernels.scale u) ^ N'
          ≤ (max C1 C2) * (Work.Kernels.scale u) ^ (max N1 N2) := by
      intro c N' hc hcle hN'
      have h1 : c * (Work.Kernels.scale u) ^ N' ≤ c * (Work.Kernels.scale u) ^ (max N1 N2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN') hc
      exact le_trans h1 (mul_le_mul_of_nonneg_right hcle hpowN_nonneg)
    by_cases h : u.re < 0
    · exact le_trans (hb1 u r hu h) (key C1 N1 hC1 (le_max_left _ _) (le_max_left _ _))
    · exact le_trans (hb2 u r hu (not_lt.mp h))
        (key C2 N2 hC2 (le_max_right _ _) (le_max_right _ _))

/-- **The bad-line input, discharged.**  `CuspOneBadLineZero` follows from
`Work.Asymptotics.kernelTransform_eq_zero_bad_line_of_im_ne_one` (for `y ≠ 1`) and
`Work.Asymptotics.kernelTransform_eq_zero_bad_line_of_im_eq_one_of_slice` (for `y = 1`), both
re-proved in the de-clashed copy `Submission/Work/Asymptotics/BLZero/BadLineClean.lean` — a copy
of the clean module `Work.Asymptotics.bad_line_kernelTransform_eq_zero` in which the clashing name
`coe_neg_vadd` (also declared by `Kaxis_principal_part_bound`) has been renamed. -/
lemma CuspOneBadLineZero_holds (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    CuspOneBadLineZero ℓ d := by
  intro y hy r
  set w : ℍ := (1 : ℝ) +ᵥ Work.Kernels.imagAxis y hy with hw
  have hre : w.re = 1 := by
    rw [hw, UpperHalfPlane.vadd_re]
    simp [Work.Kernels.imagAxis]
  have him : w.im = y := by
    rw [hw, UpperHalfPlane.vadd_im, Work.Kernels.imagAxis]
    simp
  by_cases h1 : y = 1
  · subst h1
    exact kernelTransform_eq_zero_bad_line_of_im_eq_one_of_slice ℓ d hd r 1 (Or.inl rfl) w
      (by rw [hre]; norm_num) (by rw [him])
  · exact kernelTransform_eq_zero_bad_line_of_im_ne_one ℓ d hd r 1 (Or.inl rfl)
      (by rw [hre]; norm_num) (by rw [him]; exact h1)

end Work.Asymptotics
