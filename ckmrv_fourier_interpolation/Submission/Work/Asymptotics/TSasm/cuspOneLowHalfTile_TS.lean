import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.seminormK_cusp0_defs
import Submission.Work.Asymptotics.BLZero.BadLineClean
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.TSasm.cuspOneTileE_TS
import Submission.Work.Asymptotics.TSasm.BlLowSeminormTS3
import Submission.Work.Asymptotics.FlatTailVaddOneTS
import Submission.Work.Asymptotics.PaperLayerLadderTS
import Submission.Work.Asymptotics.LayerSemiTregionTS
import Submission.Work.Asymptotics.TSasm.LayerSemiBlLowTS
import Submission.Work.Asymptotics.Tile.tileLayerTransfer
import Submission.Work.Asymptotics.TSasm.LayerAgreementClean
import Submission.Work.HFN.kernelTransform_seminorm_on_compact
import Submission.Work.Asymptotics.kernelTransform_seminorm_of_layer
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.Asymptotics.FlatTailVaddOneTS
import Submission.Work.Asymptotics.PaperLayerLadderTS
import Submission.Work.Asymptotics.LayerSemiTregionTS
import Submission.Work.Asymptotics.TSasm.LayerSemiBlLowTS
import Submission.Work.Asymptotics.Tile.tileLayerTransfer
import Submission.Work.Asymptotics.TSasm.LayerAgreementClean

/-!
# The cusp-`1` low-half tile: geometry and reduction

Statement to prove (`Work.Asymptotics.cuspOneLowHalfTile_TS`): for `w ∈ 𝒟` with `|Re w| < 1/4`,
`Im w ≤ 1/2` and `Im (S • w) ≥ 1/2`, the `r`-seminorms of the naive contour transform of
`K^{(d)}` at the cusp-`1` translate `1 + w` grow at most like a power of `scale w`.

`Im (S • w) ≥ 1/2` is *automatic* from `w ∈ 𝒟`, `|Re w| < 1/4`, `Im w ≤ 1/2`
(`im_S_ge_half_of_mem`), so the region of the statement is
`R = {w ∈ 𝒟 : |Re w| < 1/4, Im w ≤ 1/2}`.  It contains `E = KEpsilon`, so the statement implies
the cusp-`1` funnel tile bound (the `n = 1` half of `Work.Asymptotics.cuspTile_seminorm`).

## Case analysis (reduction)

Write `τ := 1 + w`, `y := Im w`, and note `‖w‖² ≤ 2 y` (`Im (S • w) ≥ 1/2`) and
`|Re w| < ‖w‖²` (the `𝒟` arc conditions, `ts_abs_re_lt_normSq_of_mem_DomainD`).

* `Re w = 0`: `τ = 1 + i y` is on the bad line `Re τ = 1`, with `y ≤ 1/2 ≠ 1`; the contour
  carries the pole `z = i y` and the Bochner integral is the junk value `0`
  (`kernelTransform_eq_zero_bad_line_of_im_ne_one`).
* `Re w > 0`: `w` and `w - 1` both lie in `𝒟` (`sub_one_mem_DomainD_of_re_pos`); the ladder
  `G τ = 2 G (τ-1) - G (τ-2)` (input `kernelTransform_ladder`) reduces the bound at `τ` to
  `seminormK_cusp0_half` at `w` (which lies in `Tregion`, since `‖w‖² ≤ 2y`) and to the
  three-case bound at `w - 1` (which has `Im = y ≥ 2/5` by `im_two_fifths_of_mem_Tregion` and
  `|Re (w-1)| = 1 - Re w > 3/4`).
* `Re w < 0`: `τ ∈ 𝒟` (`vadd_one_mem_DomainD_of_re_neg`), and with `A := Im (S • τ)`:
  * `A ≤ 2` and `1/2 ≤ A`: `τ ∈ Tregion`, `seminormK_cusp0_half` at `τ`;
  * `2 ≤ A`: `τ ∈ E`, `SeminormK_E_clean` at `τ`;
  * `A < 1/2`: either `w ∈ E` (input `cuspOneTileE_TS`, the cusp-`1` funnel tile) or `y ≥ 2/5`
    (`im_two_fifths_of_mem_Tregion` at `w`), and then `τ` lies in the low bad-line region
    (input `blLowSeminorm_TS`).

The three inputs `kernelTransform_ladder`, `cuspOneTileE_TS`, `blLowSeminorm_TS` are the
remaining obligations; the geometry below is complete.
-/

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane Topology

namespace Work.Asymptotics

/-! ## Elementary geometry on `ℍ` -/

/-- `‖u‖² = u.re ^ 2 + u.im ^ 2` for `u : ℍ`. -/
lemma ts_normSq_eq (u : ℍ) : ‖(u : ℂ)‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- `Im (S • u) = u.im / ‖u‖²` for `u : ℍ`. -/
lemma ts_im_S_smul (u : ℍ) : (ModularGroup.S • u).im = u.im / ‖(u : ℂ)‖ ^ 2 := by
  have hcoe : ((ModularGroup.S • u : UpperHalfPlane) : ℂ) = -((u : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  rw [← UpperHalfPlane.coe_im, hcoe, Complex.neg_im, Complex.inv_im,
    Complex.normSq_eq_norm_sq, UpperHalfPlane.coe_im]
  ring

/-- `1/2 ≤ Im (S • u)` in coordinates. -/
lemma ts_half_le_im_S_iff (u : ℍ) :
    (1 / 2 : ℝ) ≤ (ModularGroup.S • u).im ↔ ‖(u : ℂ)‖ ^ 2 ≤ 2 * u.im := by
  rw [ts_im_S_smul]
  have hpos : (0 : ℝ) < ‖(u : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr u.ne_zero) 2
  rw [le_div_iff₀ hpos]
  constructor <;> intro h <;> linarith

/-- `Im (S • u) ≤ 2` in coordinates. -/
lemma ts_im_S_le_two_iff (u : ℍ) :
    (ModularGroup.S • u).im ≤ 2 ↔ u.im / 2 ≤ ‖(u : ℂ)‖ ^ 2 := by
  rw [ts_im_S_smul]
  have hpos : (0 : ℝ) < ‖(u : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr u.ne_zero) 2
  rw [div_le_iff₀ hpos]
  constructor <;> intro h <;> linarith

/-- The arc conditions of `𝒟` imply `|Re u| < ‖u‖²`. -/
lemma ts_abs_re_lt_normSq_of_mem_DomainD {u : ℍ} (hu : u ∈ DomainD) :
    |u.re| < ‖(u : ℂ)‖ ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_DomainD.mp hu
  have h3' : (1 / 2 : ℝ) ^ 2 < ‖(u : ℂ) - (1 / 2 : ℂ)‖ ^ 2 :=
    pow_lt_pow_left₀ h3 (by norm_num) (by norm_num)
  have h4' : (1 / 2 : ℝ) ^ 2 < ‖(u : ℂ) + (1 / 2 : ℂ)‖ ^ 2 :=
    pow_lt_pow_left₀ h4 (by norm_num) (by norm_num)
  have e1 : ‖(u : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = u.re ^ 2 - u.re + u.im ^ 2 + 1 / 4 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have e2 : ‖(u : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = u.re ^ 2 + u.re + u.im ^ 2 + 1 / 4 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  rw [ts_normSq_eq, abs_lt]
  constructor <;> nlinarith [e1, e2, h3', h4']

/-- **Algebraic core.**  For `0 ≤ s` and `0 < y ≤ 1/2`, the `𝒟`-arc inequality `s < s² + y²`
(with `s < 1/4`) forces `s² + y² ≤ 2y`. -/
lemma ts_sq_le_two_mul_aux {s y : ℝ} (hs : 0 ≤ s) (hy : 0 < y) (hy2 : y ≤ 1 / 2)
    (hs4 : s < 1 / 4) (harc : s < s ^ 2 + y ^ 2) : s ^ 2 + y ^ 2 ≤ 2 * y := by
  by_contra hcon
  push_neg at hcon
  have h1 : y < s ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have h4 : y ^ 2 < s ^ 4 := by nlinarith [h1, hy, sq_nonneg (s ^ 2 - y)]
  have h5 : 1 < s + s ^ 3 := by nlinarith [harc, h4, sq_nonneg (s - 1)]
  nlinarith [h5, hs4, sq_nonneg (s - 1)]

/-- **Algebraic core (second form).**  For `s ≥ 0` and `y > 0` the `𝒟`-arc inequality
`s < s² + y²`, together with `y/2 ≤ s² + y² ≤ 2y`, forces `y ≥ 2/5`. -/
lemma im_two_fifths_aux (s y : ℝ) (hy : 0 < y) (hs : 0 ≤ s) (harc : s < s ^ 2 + y ^ 2)
    (hlo : y / 2 ≤ s ^ 2 + y ^ 2) (hhi : s ^ 2 + y ^ 2 ≤ 2 * y) : (2 : ℝ) / 5 ≤ y := by
  nlinarith [sq_nonneg (s - y), sq_nonneg (s - 2 * y), sq_nonneg (s ^ 2 + y ^ 2 - s),
    sq_nonneg (2 * y - s), sq_nonneg (5 * y - 2)]

/-- **`Im (S • w) ≥ 1/2` is automatic.**  For `w ∈ 𝒟` with `|Re w| < 1/4` and `Im w ≤ 1/2`. -/
lemma im_S_ge_half_of_mem {w : ℍ} (hw : w ∈ DomainD) (hre : |w.re| < 1 / 4)
    (him : w.im ≤ 1 / 2) : (1 / 2 : ℝ) ≤ (ModularGroup.S • w).im := by
  rw [ts_half_le_im_S_iff, ts_normSq_eq]
  have harc := ts_abs_re_lt_normSq_of_mem_DomainD hw
  rw [ts_normSq_eq] at harc
  have key := ts_sq_le_two_mul_aux (abs_nonneg w.re) w.im_pos him hre
    (by rw [sq_abs]; exact harc)
  rw [sq_abs] at key
  exact key

/-- **`Im w ≥ 2/5` in the low half of `Tregion`.**  A point of `Tregion` whose `Re` satisfies the
`𝒟`-arc inequality `|Re| < ‖w‖²` (automatic in `𝒟`) has `Im ≥ 2/5`. -/
lemma im_two_fifths_of_mem_Tregion {w : ℍ} (hT : w ∈ Tregion)
    (harc : |w.re| < ‖(w : ℂ)‖ ^ 2) : (2 : ℝ) / 5 ≤ w.im := by
  obtain ⟨-, hlo, hhi⟩ := mem_Tregion.mp hT
  rw [ts_half_le_im_S_iff] at hlo
  rw [ts_im_S_le_two_iff] at hhi
  rw [ts_normSq_eq] at hlo hhi harc
  have h1 : |w.re| < |w.re| ^ 2 + w.im ^ 2 := by rw [sq_abs]; exact harc
  have h2 : w.im / 2 ≤ |w.re| ^ 2 + w.im ^ 2 := by rw [sq_abs]; exact hhi
  have h3 : |w.re| ^ 2 + w.im ^ 2 ≤ 2 * w.im := by rw [sq_abs]; exact hlo
  exact im_two_fifths_aux |w.re| w.im w.im_pos (abs_nonneg w.re) h1 h2 h3

/-! ## The target

The statement below is the requested lemma.  Its proof is the case analysis documented at the top
of this file; the pieces still missing are

* `Work.Asymptotics.cuspOneTileE_TS` — the cusp-`1` funnel tile bound at `1 + w`, `w ∈ E`
  (in flight, currently being proved from the `Tile/` development or from the `(T*S)`-slashed
  funnel bound).  This is the *only* input needed for the cases `w ∈ E`;
* the low bad-line bound: SUPPLIED, `Work.Asymptotics.blLowSeminormHFN_TS` (proved and
  importable on this branch, see the import above);
* the ladder-agreement input `kernelTransform_ladder` for the `Re w > 0` case (the threshold
  bookkeeping of `T2op_kernelTransform`: for `r ≠ 0` with the integrand at `1 + w` integrable,
  the integrands at `w` and `w - 1` are integrable and the ladder identity holds).

The two `𝒟`-membership facts used in the reduction (`Re w < 0 ⟹ 1 + w ∈ 𝒟` and
`0 < Re w ⟹ w - 1 ∈ 𝒟`) are proved (as `private` lemmas `vadd_one_mem_DomainD`,
`vadd_neg_one_mem_DomainD`) in `Submission/Work/Asymptotics/DomainD_cover_half.lean`; public
copies are still to be added here (the `rw [UpperHalfPlane.coe_vadd]; push_cast; ring` +
`Complex.abs_re_le_norm` pattern of that file works verbatim).

## Import branches

The workspace contains two mutually exclusive import families: the `MiddleRange.Main` family
(which contains `seminormK_cusp0_half`, `HalfFunnel.lowRegion_badLine` and the proved
`blLowSeminorm_TS`) and the `KPlusXiDefs` family (which contains `SeminormK_E`, the `Khat`
funnel bound and — through `Submission/Work/HFN/` copies — the `HalfFunnel` machinery).  Any
single assembly file must pick one; this file is on the `KPlusXiDefs`/`HFN` branch (so that the
`E`-bound is available), which is why the proved `blLowSeminorm_TS` cannot be imported here
directly. -/

/-! ## Elementary geometry of the translate `1 +ᵥ w`

The reduction of the target uses the translate `τ = 1 +ᵥ w` of the tile point.  Below we record
the coordinate form of that translate and the fact that it lies in `𝒟` as soon as
`w.re < 0`. -/

/-- If `Re w > 1/2` then `‖w‖ > 1/2` (for `w : ℂ`). -/
lemma ts_half_lt_norm_of_re {z : ℂ} (h : (1 : ℝ) / 2 < z.re) : (1 : ℝ) / 2 < ‖z‖ := by
  have := Complex.abs_re_le_norm z
  rw [abs_of_pos (by linarith)] at this
  linarith

/-- `Re (1 +ᵥ w) = 1 + Re w`. -/
lemma ts_vadd_one_re (w : ℍ) : ((1 : ℝ) +ᵥ w).re = 1 + w.re := UpperHalfPlane.vadd_re 1 w

/-- `Im (1 +ᵥ w) = Im w`. -/
lemma ts_vadd_one_im (w : ℍ) : ((1 : ℝ) +ᵥ w).im = w.im := UpperHalfPlane.vadd_im 1 w

/-- **`z ↦ z + 1` maps `𝒟 ∩ {-1 < Re z < 0}` into `𝒟`.** -/
lemma ts_vadd_one_mem_DomainD_of_re_neg {w : ℍ} (hw : w ∈ DomainD) (h0 : w.re < 0) :
    ((1 : ℝ) +ᵥ w) ∈ DomainD := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_DomainD.mp hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ts_vadd_one_re]; linarith
  · rw [ts_vadd_one_re]; linarith
  · have hcoe : ((((1 : ℝ) +ᵥ w : ℍ)) : ℂ) - (1 / 2 : ℂ) = (w : ℂ) + (1 / 2 : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    rw [hcoe]; exact h4
  · have hcoe : ((((1 : ℝ) +ᵥ w : ℍ)) : ℂ) + (1 / 2 : ℂ) = (w : ℂ) + (3 / 2 : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    rw [hcoe]
    apply ts_half_lt_norm_of_re
    have h32 : ((3 / 2 : ℂ)).re = (3 / 2 : ℝ) := by norm_num
    rw [Complex.add_re, h32, UpperHalfPlane.coe_re]
    linarith

/-- **Non-coincidence on `𝒟` off the imaginary axis.**

The positive imaginary axis is the only `SL(2,ℤ)`-orbit that meets `𝒟` on the imaginary axis
(`Work.Asymptotics.orbit_imagAxis_of_mem_DomainD`), and `j` separates `SL(2,ℤ)`-orbits
(`Work.Asymptotics.jInvariantFun_eq_smul_of_eq`).  Hence for `z ∈ 𝒟` with `Re z ≠ 0` the contour
`z = it` never meets a pole of `z' ↦ K^{(d)}(z, z')`. -/
lemma ts_jInvariantFun_ne_imagAxis_of_mem_DomainD {z : ℍ} (hz : z ∈ DomainD) (hre : z.re ≠ 0) :
    ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun z ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro t ht heq
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq heq
  have hzit : γ⁻¹ • z = Work.Kernels.imagAxis t ht := by
    rw [← hγ, ← mul_smul, inv_mul_cancel, one_smul]
  have h0 : ((γ⁻¹ • z : ℍ) : ℂ).re = 0 := by
    rw [hzit]
    simp [Work.Kernels.imagAxis]
  exact hre (Work.Asymptotics.orbit_imagAxis_of_mem_DomainD z hz γ⁻¹ h0)

/-! ## The assembly

The target region `R = {w ∈ 𝒟 : 1/2 ≤ Im (S • w), Im w ≤ 1/2, |Re w| < 1/4}` splits as

* `Re w = 0`: `1 +ᵥ w` lies on the bad line `Re = 1` (with `Im ≠ 1`), where the naive contour
  transform is the junk value `0`;
* `Re w > 0`: the `T`-ladder input `hP` (`Work.Asymptotics.CuspOneLowHalfTilePosRe`);
* `Re w < 0` and `2 ≤ Im (S • w)`, i.e. `w ∈ E = KEpsilon`: the cusp-`1` tile input `hE`
  (`Work.Asymptotics.TileETS`), applied at `w`;
* `Re w < 0` and `Im (S • w) < 2`: then `1 +ᵥ w ∈ 𝒟` lies in the *low bad line* region
  (`|Re| > 3/4`, `Im ∈ [2/5, 1/2]`) — indeed `w ∈ Tregion` forces `Im w ≥ 2/5`
  (`im_two_fifths_of_mem_Tregion`) — so `blLowSeminormHFN_TS` applies and gives a *constant*
  bound. -/
theorem cuspOneLowHalfTile_of_inputs (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hP : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (u : UpperHalfPlane) (r : ℝ), u ∈ DomainD →
        (1 : ℝ) / 2 ≤ (ModularGroup.S • u).im → 0 < u.re → u.im ≤ 1 / 2 → |u.re| < 1 / 4 →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖
          ≤ C * (Work.Kernels.scale u) ^ N) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ DomainD →
        (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im → w.im ≤ 1 / 2 → |w.re| < 1 / 4 →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  intro k l
  obtain ⟨CE, NE, hCE, hNE, hEb⟩ := cuspOneTileE_TS ℓ d hd k l
  obtain ⟨CP, NP, hCP, hNP, hPb⟩ := hP k l
  obtain ⟨CB, hCB, hBb⟩ := BlLowSeminormTS3 ℓ d hd k l
  set Cmax : ℝ := max CE (max CP CB) with hCmaxdef
  set Nmax : ℝ := max NE (max NP 0) with hNmaxdef
  have hCmax0 : 0 ≤ Cmax :=
    le_trans hCE (le_max_left CE (max CP CB))
  have hNmax0 : 0 ≤ Nmax := le_max_of_le_left hNE
  refine ⟨Cmax, Nmax, hCmax0, hNmax0, ?_⟩
  intro w r hw hS him hre
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hs1
  have htop : (1 : ℝ) ≤ (Work.Kernels.scale w) ^ Nmax :=
    Real.one_le_rpow hs1 hNmax0
  -- generic closing step: `c * (scale w)^n ≤ Cmax * (scale w)^Nmax`
  have hfin : ∀ c n : ℝ, 0 ≤ c → c ≤ Cmax → n ≤ Nmax →
      c * (Work.Kernels.scale w) ^ n ≤ Cmax * (Work.Kernels.scale w) ^ Nmax := by
    intro c n hc hcle hn
    have h1 : (Work.Kernels.scale w) ^ n ≤ (Work.Kernels.scale w) ^ Nmax :=
      Real.rpow_le_rpow_of_exponent_le hs1 hn
    calc c * (Work.Kernels.scale w) ^ n
        ≤ Cmax * (Work.Kernels.scale w) ^ n :=
          mul_le_mul_of_nonneg_right hcle (Real.rpow_nonneg hs0 n)
      _ ≤ Cmax * (Work.Kernels.scale w) ^ Nmax :=
          mul_le_mul_of_nonneg_left h1 hCmax0
  have hCEle : CE ≤ Cmax := by rw [hCmaxdef]; exact le_max_left _ _
  have hCPle : CP ≤ Cmax := by
    rw [hCmaxdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCBle : CB ≤ Cmax := by
    rw [hCmaxdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hNEle : NE ≤ Nmax := by rw [hNmaxdef]; exact le_max_left _ _
  have hNPle : NP ≤ Nmax := by
    rw [hNmaxdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h0le : (0 : ℝ) ≤ Nmax := hNmax0
  by_cases hre0 : w.re = 0
  · -- bad line: `1 +ᵥ w` has `Re = 1`, `Im ≠ 1`
    have hτre : (((1 : ℝ) +ᵥ w : ℍ)).re = ((1 : ℤ) : ℝ) := by
      rw [ts_vadd_one_re]; norm_num [hre0]
    have hτim_ne : (((1 : ℝ) +ᵥ w : ℍ)).im ≠ 1 := by
      rw [ts_vadd_one_im]; linarith
    have hz : ∀ s : ℝ,
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) s = 0 :=
      fun s => Work.Asymptotics.kernelTransform_eq_zero_bad_line_of_im_ne_one ℓ d hd s 1
        (Or.inl rfl) hτre hτim_ne
    have hfun : (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d)
        ((1 : ℝ) +ᵥ w) s) = fun _ => (0 : ℂ) := funext hz
    rw [hfun]
    have h0 : iteratedDeriv l (fun _ : ℝ => (0 : ℂ)) r = 0 := by
      rcases Nat.eq_zero_or_pos l with h | h
      · subst h; simp
      · rw [iteratedDeriv_const]; simp [h.ne']
    rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hCmax0 (Real.rpow_nonneg hs0 Nmax)
  · by_cases hpos : 0 < w.re
    · -- `Re w > 0`: the ladder input
      exact le_trans (hPb w r hw hS hpos him hre) (hfin CP NP hCP hCPle hNPle)
    · have hneg : w.re < 0 := by
        rcases lt_trichotomy w.re 0 with h | h | h
        · exact h
        · exact absurd h hre0
        · exact absurd h hpos
      by_cases hE2 : (2 : ℝ) ≤ (ModularGroup.S • w).im
      · -- `w ∈ E`: the cusp-`1` tile input
        have hwE : w ∈ KEpsilon := ⟨hw, hE2⟩
        exact le_trans (hEb w r hwE) (hfin CE NE hCE hCEle hNEle)
      · -- `w ∈ Tregion`: the constant low bad-line bound at `1 +ᵥ w`
        have hTw : w ∈ Tregion := ⟨hw, hS, le_of_lt (not_le.mp hE2)⟩
        have harc := ts_abs_re_lt_normSq_of_mem_DomainD hw
        have him25 : (2 : ℝ) / 5 ≤ w.im := im_two_fifths_of_mem_Tregion hTw harc
        have hτD : (((1 : ℝ) +ᵥ w : ℍ)) ∈ DomainD :=
          ts_vadd_one_mem_DomainD_of_re_neg hw hneg
        have hτre : (((1 : ℝ) +ᵥ w : ℍ)).re = 1 + w.re := ts_vadd_one_re w
        have hτim : (((1 : ℝ) +ᵥ w : ℍ)).im = w.im := ts_vadd_one_im w
        have hrel : -(1 / 4 : ℝ) < w.re := (abs_lt.mp hre).1
        have hτabs : (3 : ℝ) / 4 < |(((1 : ℝ) +ᵥ w : ℍ)).re| := by
          rw [hτre, abs_of_pos (by linarith : (0 : ℝ) < 1 + w.re)]
          linarith
        have hb := hBb ((1 : ℝ) +ᵥ w) r hτD (by rw [hτim]; exact him25)
          (by rw [hτim]; exact him) hτabs
        refine le_trans hb ?_
        simpa using hfin CB 0 hCB hCBle h0le


/-! ## The positive-`Re` half: the layer bound at `1 +ᵥ u`

For `u ∈ Tregion` with `0 < Re u < 1/4` and `Im u ≤ 1/2` we bound the `r`-seminorms of the layer
at the `T`-translate `1 +ᵥ u`, uniformly in `u`, by combining the `T`-ladder
`layer(1+u) = 2 layer(u) - layer(u-1)` (`Work.Asymptotics.lh_layer_vadd_ladder`) with the uniform
layer bounds on `Tregion` (`Work.Asymptotics.LayerSemiTregionTS`) and on the low bad-line region
`blLowSet ∋ u - 1` (`Work.Asymptotics.LayerSemiBlLowTS`). -/

/-- `paperLayer (Gcusp ℓ d) ℓ d τ ·` is smooth in `r` at any `τ ∈ 𝒟`. -/
theorem ts_paperLayer_contDiff_at (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (u : ℍ) (hu : u ∈ DomainD) :
    ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) :=
  Work.HFN.paperLayer_contDiff_of_mem ℓ d hd (Work.Asymptotics.Gcusp ℓ d)
    (K := ({u} : Set ℍ))
    (Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd (K := ({u} : Set ℍ)) isCompact_singleton
      (by rintro x rfl; exact hu))
    (Work.HFN.cusp_expansion_of_kernel ℓ d hd (K := ({u} : Set ℍ)) isCompact_singleton
      (by rintro x rfl; exact hu))
    u (by simp)

/-- `paperLayer (Gcusp ℓ d) ℓ d (1 +ᵥ u) ·` is smooth in `r` for `u ∈ 𝒟` with `0 < Re u`. -/
theorem ts_paperLayer_contDiff_vadd_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (u : ℍ) (hu : u ∈ DomainD) (hre : 0 < u.re) :
    ContDiff ℝ ⊤ (fun s : ℝ =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) s) :=
  Work.HFN.paperLayer_contDiff_of_mem ℓ d hd (Work.Asymptotics.Gcusp ℓ d)
    (K := ({((1 : ℝ) +ᵥ u)} : Set ℍ))
    (by
      intro N hN
      obtain ⟨c, hc, hb⟩ := Work.Asymptotics.lh_flat_vadd_one ℓ d hd u hu hre N hN
      exact ⟨c, hc, fun τ t hτ ht ht1 => by
        rw [Set.mem_singleton_iff] at hτ
        subst hτ
        exact hb t ht ht1⟩)
    (by
      obtain ⟨C, M, T₀, hC, hM, hT₀, hb⟩ := Work.Asymptotics.lh_tail_vadd_one ℓ d hd u hu hre
      exact ⟨C, M, T₀, hC, hM, hT₀, fun τ t hτ ht => by
        rw [Set.mem_singleton_iff] at hτ
        subst hτ
        exact hb t ht⟩)
    ((1 : ℝ) +ᵥ u) (by simp)

/-- The `iteratedDeriv` of the punctured layer equals that of the layer (positive order). -/
theorem ts_punctured_iteratedDeriv {G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ}
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) {l : ℕ} (hl : 1 ≤ l)
    (hcd : ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.paperLayer G ℓ d τ s)) :
    iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layer G ℓ d τ s)
      = iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer G ℓ d τ s) := by
  have hfun : (fun s : ℝ => Work.Asymptotics.layer G ℓ d τ s)
      = fun s : ℝ => if s = 0 then 0 else Work.Asymptotics.paperLayer G ℓ d τ s := by
    funext s; rw [Work.Asymptotics.layer]
  rw [hfun, Work.Asymptotics.punctured_iteratedDeriv
    (fun s => Work.HFN.paperLayer_neg G ℓ d τ s) (hcd.differentiable (by simp)) l hl]

theorem ts_layerSemi_vadd_one_Tregion (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : UpperHalfPlane) (r : ℝ), u ∈ Tregion → 0 < u.re → u.re < 1 / 4 → u.im ≤ 1 / 2 →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) s) r‖ ≤ C := by
  intro k l
  obtain ⟨C₀, hC₀, hb₀⟩ := Work.Asymptotics.LayerSemiTregionTS ℓ d hd k l
  obtain ⟨C₁, hC₁, hb₁⟩ := Work.Asymptotics.LayerSemiBlLowTS ℓ d hd k l
  refine ⟨2 * C₀ + C₁, by linarith, fun u r hu hre hre4 him => ?_⟩
  have huD : u ∈ DomainD := hu.1
  have harc := ts_abs_re_lt_normSq_of_mem_DomainD huD
  have him25 : (2 : ℝ) / 5 ≤ u.im := im_two_fifths_of_mem_Tregion hu harc
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ DomainD :=
    Work.Asymptotics.lh_vadd_neg_one_mem_DomainD_of_pos huD hre
  have hbl : Work.Asymptotics.BlLow.blLowSet (((-1 : ℝ) +ᵥ u) : ℍ) := by
    refine ⟨hu1D, ?_, ?_, ?_⟩
    · rw [UpperHalfPlane.vadd_im]; exact him25
    · rw [UpperHalfPlane.vadd_im]; exact him
    · rw [UpperHalfPlane.vadd_re]
      right
      linarith [hre4]
  have hcdu : ContDiff ℝ ⊤ (fun s : ℝ =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) :=
    ts_paperLayer_contDiff_at ℓ d hd u huD
  have hcdv : ContDiff ℝ ⊤ (fun s : ℝ =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) :=
    ts_paperLayer_contDiff_at ℓ d hd (((-1 : ℝ) +ᵥ u)) hu1D
  by_cases hr : r = 0
  · subst hr
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rcases Nat.eq_zero_or_pos l with hl | hl
      · subst hl
        have hz : Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) 0 = 0 := by
          rw [Work.Asymptotics.layer]; simp
        rw [iteratedDeriv_zero, hz, norm_zero, mul_zero]
        positivity
      · -- positive order at `r = 0`: the puncture is invisible, and the paperLayer ladder holds
        have hcd1 : ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) s) :=
          ts_paperLayer_contDiff_vadd_one ℓ d hd u huD hre
        have hp1 := ts_punctured_iteratedDeriv (G := Work.Asymptotics.Gcusp ℓ d) ℓ d
          ((1 : ℝ) +ᵥ u) hl hcd1
        have hpu := ts_punctured_iteratedDeriv (G := Work.Asymptotics.Gcusp ℓ d) ℓ d u hl hcdu
        have hpv := ts_punctured_iteratedDeriv (G := Work.Asymptotics.Gcusp ℓ d) ℓ d
          (((-1 : ℝ) +ᵥ u)) hl hcdv
        have hladeq : (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d)
              ℓ d ((1 : ℝ) +ᵥ u) s)
            = (fun s : ℝ => 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s
                - Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d
                    (((-1 : ℝ) +ᵥ u)) s) := by
          funext s
          exact Work.Asymptotics.lh_paperLayer_vadd_ladder ℓ d hd u huD hre s
        have h2 : iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
              (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) s) 0
            = 2 * iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
                (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) 0
              - iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
                (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) 0 := by
          rw [hladeq]
          have hsplit : (fun s : ℝ => 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d)
                ℓ d u s - Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d
                (((-1 : ℝ) +ᵥ u)) s)
              = (fun s : ℝ => 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s)
                - (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d
                    (((-1 : ℝ) +ᵥ u)) s) := rfl
          rw [hsplit, iteratedDeriv_sub (((contDiff_const.mul hcdu).contDiffAt).of_le le_top)
            ((hcdv.contDiffAt).of_le le_top), iteratedDeriv_const_mul_field]
        have hb1 : ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) 0‖ ≤ C₀ := by
          rw [← hpu]
          simpa using hb₀ u 0 hu
        have hb2 : ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) 0‖ ≤ C₁ := by
          rw [← hpv]
          simpa using hb₁ (((-1 : ℝ) +ᵥ u)) 0 hbl
        rw [hp1, h2]
        have hnorm : ‖2 * iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
              (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) 0
            - iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
              (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) 0‖
            ≤ 2 * C₀ + C₁ := by
          have hA : ‖2 * iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
              (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) 0‖
              ≤ 2 * C₀ := by
            rw [norm_mul]; norm_num
            linarith
          calc _ ≤ ‖2 * iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
                (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) 0‖
              + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
                (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) 0‖ := norm_sub_le _ _
            _ ≤ 2 * C₀ + C₁ := by linarith
        simpa only [abs_zero, pow_zero, one_mul] using hnorm
    · have h0 : |(0 : ℝ)| ^ k = 0 := by rw [abs_zero, zero_pow hk.ne']
      rw [h0, zero_mul]
      positivity
  · -- `r ≠ 0`: the layer is eventually the `paperLayer`, and the paperLayer ladder holds
    have hlu : (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s)
        =ᶠ[𝓝 r] (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with s hs
      rw [Work.Asymptotics.layer, if_neg hs]
    have hlv : (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d
          (((-1 : ℝ) +ᵥ u)) s)
        =ᶠ[𝓝 r] (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d
          (((-1 : ℝ) +ᵥ u)) s) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with s hs
      rw [Work.Asymptotics.layer, if_neg hs]
    have hlad : (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d
          ((1 : ℝ) +ᵥ u) s)
        =ᶠ[𝓝 r] (fun s : ℝ => 2 * Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s
          - Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) :=
      Filter.Eventually.of_forall (fun s => Work.Asymptotics.lh_layer_vadd_ladder ℓ d hd u huD hre s)
    have hev : (fun s : ℝ => 2 * Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s
          - Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s)
        =ᶠ[𝓝 r] (fun s : ℝ => 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s
          - Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) := by
      filter_upwards [hlu, hlv] with s h1 h2
      rw [h1, h2]
    rw [iteratedDeriv_congr_of_eventuallyEq hlad l,
      iteratedDeriv_congr_of_eventuallyEq hev l]
    have hsplit : (fun s : ℝ => 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d)
          ℓ d u s - Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d
          (((-1 : ℝ) +ᵥ u)) s)
        = (fun s : ℝ => 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s)
          - (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d
              (((-1 : ℝ) +ᵥ u)) s) := rfl
    rw [hsplit, iteratedDeriv_sub (((contDiff_const.mul hcdu).contDiffAt).of_le le_top)
      ((hcdv.contDiffAt).of_le le_top), iteratedDeriv_const_mul_field]
    have hb1 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
        (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r‖ ≤ C₀ := by
      rw [← iteratedDeriv_congr_of_eventuallyEq hlu l]
      exact hb₀ u r hu
    have hb2 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
        (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) r‖ ≤ C₁ := by
      rw [← iteratedDeriv_congr_of_eventuallyEq hlv l]
      exact hb₁ (((-1 : ℝ) +ᵥ u)) r hbl
    have hnorm : ‖2 * iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
          (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r
        - iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
          (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) r‖
        ≤ 2 * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) r‖ := by
      calc ‖2 * iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r
          - iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) r‖
          ≤ ‖2 * iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
              (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r‖
            + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
              (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) r‖ := norm_sub_le _ _
        _ = 2 * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
              (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r‖
            + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
              (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) r‖ := by
            rw [norm_mul]; norm_num
    calc (|r| ^ k) * ‖2 * iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r
          - iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) r‖
        ≤ (|r| ^ k) * (2 * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) r‖) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = 2 * ((|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r‖)
          + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer
            (Work.Asymptotics.Gcusp ℓ d) ℓ d (((-1 : ℝ) +ᵥ u)) s) r‖ := by ring
      _ ≤ 2 * C₀ + C₁ := by linarith

/-! ## The transfer to the naive contour transform at `1 +ᵥ u` -/

theorem ts_posRe_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : UpperHalfPlane) (r : ℝ), u ∈ Tregion → 0 < u.re → u.re < 1 / 4 → u.im ≤ 1 / 2 →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖ ≤ C := by
  obtain ⟨C₀, hC₀, hb₀⟩ := ts_layerSemi_vadd_one_Tregion ℓ d hd k l
  refine ⟨C₀, hC₀, fun u r hu hre hre4 him => ?_⟩
  have key := Work.Asymptotics.tile_layer_transfer_aux (Work.Kernels.Kfun ℓ d)
    (fun (_ : UpperHalfPlane) (s : ℝ) =>
      Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) s)
    (fun _ : UpperHalfPlane => C₀) k l (K := ({((1 : ℝ) +ᵥ u)} : Set UpperHalfPlane))
    (hR := fun τ _ => hC₀)
    (h0 := by
      intro τ hτ
      rw [Set.mem_singleton_iff] at hτ
      subst hτ
      show Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) 0 = _
      rw [Work.Asymptotics.layer, if_pos rfl]
      simp [Work.Kernels.kernelTransform])
    (hagr := by
      intro τ hτ r' hr' hint
      rw [Set.mem_singleton_iff] at hτ
      subst hτ
      rw [Work.Asymptotics.layer, if_neg hr']
      exact Work.Asymptotics.paperLayer_eq_kernelTransform_of_integrable ℓ d
        (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) r' hr' hint
        (Work.Asymptotics.integrableOn_Aexp_of_contour_integrable ℓ d hd ((1 : ℝ) +ᵥ u) r'
          hr' hint))
    (hsemi := fun τ s _ => hb₀ u s hu hre hre4 him)
  exact key ((1 : ℝ) +ᵥ u) r (Set.mem_singleton _)

/-! ## The input `hP` of the assembly -/

theorem ts_hP (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (u : UpperHalfPlane) (r : ℝ), u ∈ DomainD →
        (1 : ℝ) / 2 ≤ (ModularGroup.S • u).im → 0 < u.re → u.im ≤ 1 / 2 → |u.re| < 1 / 4 →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) s) r‖
          ≤ C * (Work.Kernels.scale u) ^ N := by
  intro k l
  obtain ⟨CE, NE, hCE, hNE, hEb⟩ := cuspOneTileE_TS ℓ d hd k l
  obtain ⟨CT, hCT, hbT⟩ := ts_posRe_bound ℓ d hd k l
  refine ⟨max CE CT, NE, le_trans hCE (le_max_left _ _), hNE, fun u r huD hS hre him hre4 => ?_⟩
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale u := Work.Kernels.one_le_scale u
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale u := le_trans zero_le_one hs1
  have hpow : (1 : ℝ) ≤ (Work.Kernels.scale u) ^ NE := Real.one_le_rpow hs1 hNE
  have hCmax : (0 : ℝ) ≤ max CE CT := le_trans hCE (le_max_left _ _)
  by_cases hE : (2 : ℝ) ≤ (ModularGroup.S • u).im
  · have h := hEb u r ⟨huD, hE⟩
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_right (le_max_left CE CT) (Real.rpow_nonneg hs0 NE)
  · have hT : u ∈ Tregion := ⟨huD, hS, le_of_lt (not_le.mp hE)⟩
    have hlt : u.re < 1 / 4 := (abs_lt.mp hre4).2
    have h := hbT u r hT hre hlt him
    refine le_trans h ?_
    calc CT = CT * 1 := (mul_one CT).symm
      _ ≤ CT * (Work.Kernels.scale u) ^ NE := mul_le_mul_of_nonneg_left hpow hCT
      _ ≤ max CE CT * (Work.Kernels.scale u) ^ NE :=
          mul_le_mul_of_nonneg_right (le_max_right CE CT) (Real.rpow_nonneg hs0 NE)

theorem cuspOneLowHalfTile_TS (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Work.Asymptotics.DomainD →
        (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im → w.im ≤ 1 / 2 → |w.re| < 1 / 4 →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
          ≤ C * (Work.Kernels.scale w) ^ N :=
  cuspOneLowHalfTile_of_inputs ℓ d hd (ts_hP ℓ d hd)


end Work.Asymptotics
