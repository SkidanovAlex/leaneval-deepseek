/-
# The resonant strip on the cusp-`1` tile, restricted to `Re w ≠ 0`

Target: `Work.Asymptotics.Tile.tileStripCusp1Re` — for `w ∈ E = KEpsilon` with `Re w ≠ 0`
and `Im (S • w) - 1 ≤ t ≤ Im (S • w) + 1`, the deviation of the CKMRV kernel at the tile
point `1 +ᵥ w` from its cusp model is bounded by `C (scale w)^N t^M`.

## The `Re w ≠ 0` restriction

The unrestricted statement (`Tile.tileStripCusp1`, `Tile.tileStripCuspNeg1`,
`Tile.TileBelowPoleStrip`) is **false**: for `w` on the bad line `Re w = 0` and `t = Im (S • w)`
the point `i t` is an exact coincidence `j (n +ᵥ w) = j (i t)`, and the kernel assembled in
`Submission/Work/Kernels/Kernels.lean` uses Lean's totalised inverse (`0⁻¹ = 0`), so at that
single point `Kfun` takes a *junk* value which (for `d = 24`) is not its removable
continuation; the deviation there is not polynomially bounded (cf. the counterexample recorded
for `Tile.tileWindowBound`).  For `Re w ≠ 0` no point of the strip is a coincidence
(`stripNoCoincidence` below), so the deviation is the honest one and the polynomial bound is
the genuine (hard) statement.  This is the reason for the `w.re ≠ 0` hypothesis.

## Numerics (this is a true statement)

A numeric check with the (verified) model of `.farprobe/exact.py` (dps 200) shows, at
`w = δ + i/(2k)`, `t = Im (S • w) = 2k`, `τ = 1 + ᵥ w`:

* `‖Kaxis (Kfun ℓ 24) τ t‖ ≈ e^{2πt} (scale w)^{11}` and the same for `‖Aexp (Gcusp ℓ 24) τ t‖`
  (the cancellation is genuine);
* the deviation is `≈ (scale w)^{13.7}` for `k = 12` and `≈ (scale w)^{13.3}` for `k = 5`, and it
  is *stable* (to 8 digits) as `δ = Re w → 0` — in particular the exact-coincidence value
  (`δ = 0`, where Lean's `Kfun` is the junk value) is *larger*: the residue of `Kfun` at the
  coincidence vanishes (`Tile.AfunFun_strip_zeros`), so the honest deviation is finite there and
  the `Re w ≠ 0` restriction is exactly what is needed.

## The proof (route and status)

`tileStripCusp1Re` is the `n = 1` case of the below-pole window, specialised to the strip
`|t - Im (S • w)| ≤ 1`; it is currently proved here by specialising the (still open) teammate
target `Work.Asymptotics.Tile.tileWindowRestricted_strip`.

The intended self-contained proof of the strip bound is the **`N`-function / three-zeros route**
(identical to the one recorded in the docstring of `Tile.tileWindowRestricted_strip` and to the
plan of the ball bound `Tile.tileNumBallBound`, which was created in the workspace while this file
was written):

* let `N ζ = 2 * Sh (n +ᵥ w) ζ * (Kfun ℓ d (n +ᵥ w) ζ - Gfun d ℓ (n +ᵥ w) ζ)`; off the coincidence
  locus `N` agrees with the *entire* holomorphic function
  `-2 · Δ(ζ) · AfunFun (n+ᵥw) ζ - 2 · Sh (n+ᵥw) ζ · Gfun d ℓ (n+ᵥw) ζ`
  (`Tile.tileNum_eq_hol`), and it vanishes at the three resonant points `ζ = S • w + k`,
  `k ∈ {-1,0,1}`, because `Sh` does (`Tile.Sh_strip_zeros`);
* the ball bound `Tile.tileNumBallBound` gives `N` on the ball `‖ζ - S • w‖ ≤ 29/20`
  (this is the ball of the strip: `|i t - S • w|² < 2 < (29/20)²` for `|t - Im (S•w)| ≤ 1` and
  `|Re (S • w)| < 1`);
* `Work.Analysis.ThreeZeros.three_zeros_bound_ball` turns that into
  `‖N (i t)‖ ≤ (M / δ) · ‖i t - S•w + 1‖ ‖i t - S•w‖ ‖i t - S•w - 1‖` with
  `δ = (29/20) (9/20)²` (`sphere_prod_dist_ge` below);
* `Tile.Sh_axis_lower_bound` (proved) gives the matching lower bound
  `c · exp (2π (Im (S•w) - t)) · ∏_k ‖i t - S•w - k‖ ≤ ‖Sh (n+ᵥw) (i t)‖` on the strip, which
  cancels the product and yields the result with `N ≤ …`, `M ≤ …` independent of `w`.

The remaining inputs for this route — the *off-axis* cleared half-deviation bounds
`‖Sh τ ζ‖ · ‖K± τ ζ - 𝒢± τ ζ‖ ≤ C (scale w)^N (1 + Im ζ)^M · (weight))` for `ζ : ℍ` with
`3 ≤ ζ.im` and `|(ζ:ℂ).re| ≤ 3` — are partly provided here:
`halfDevClearAxisPlus24` (proved in this file, from `K24F.KPlus24_diff`,
`Tile.sm_sum_le_atoms`, `Tile.H24.tileAtoms24_axis`, `K24F.E4_ne_zero_three`, all proved and all
off axis) and its stand-alone copy `Tile.halfDevClearOffAxis24Plus`.  For `K₊` the weight is
`exp (2π (Im (S•w) - Im ζ))`; for `K₋` it is the *sum*
`exp (π (Im (S•w) - Im ζ)) + exp (2π (Im (S•w) - Im ζ))`, because the `K₋` bracket's expansion in
`Ept ζ = exp (π i ζ)` starts at order one (so the far window carries `2π`, cf. the proved
`Tile.TBF.ktl_G24_far`, while `Tile.TBMW.ktl_G24` gives `π` above the pole height).
The `d = 8` analogues (`halfDevClearOffAxis8Plus`, `halfDevClearOffAxis8Minus`,
`halfDevClearOffAxis24Minus`) are stated in the same shape for the ball bound.

A technical warning for whoever assembles this: the ball bound is stated for the *Lean*
expression `2 Sh (Kfun - Gfun)`, which equals the honest (holomorphic) expression off the
coincidence locus and `0` on it, whereas the holomorphic representative is
`-2 Δ AfunFun - 2 Sh Gfun`; the two agree at the three resonant points (`Tile.AfunFun_strip_zeros`)
and differ at the other orbit points of `τ`, so either the ball bound must be phrased for the
cleared/bracket form (`brMinus + Sh · br0`, `K24F.KPlus24_diff`) or one needs the fact that the
orbit points of `τ = n + ᵥ w` inside `‖ζ - S • w‖ ≤ 29/20` are precisely `S • w + k`.

The exact `T`-affine law of the deviation,
`Dev (1 +ᵥ u) = 2 * Dev u - Dev ((-1) +ᵥ u)` (CKMRV Theorem 4.9(2) applied to both
`Kaxis (Kfun ·) ·` and `Aexp (Gcusp ·) ·`, cf. `Tile.tileDevAffine`), together with the proved
`Tile.cusp0DevWindow` for the cusp-`0` tile, shows that the strip bound for `n = +1` follows from
the strip bound for `n = -1`: only *one* half of the strip needs an independent proof.  That law
is not used in *this* file because its inputs (`Residues.Kfun_T2` and
`Asymptotics.Aexp_vadd_ladder`) live in the `KPlusXiDefs` branch of the library, which cannot be
imported together with the branch of `cusp0DevWindow` (both declare
`Work.Asymptotics.continuous_jInvariantFun`).

## What this file proves

* `Work.Asymptotics.Tile.halfDevClearAxisPlus24` — the off-axis cleared `K₊^{(24)}`
  half-deviation bound: the `K₊` half of the ball bound, with the weight `exp (2π (Im (S•w) - Im ζ))`.
* `Work.Asymptotics.Tile.sphere_prod_dist_ge` — the constant `δ` for the three-zeros estimate.
* `Work.Asymptotics.Tile.stripNoCoincidence` — `Re w ≠ 0` rules out coincidences on the strip.
* `Work.Asymptotics.Tile.tileStripCusp1Re` — the target.  Its proof is the `n = 1` case of the
  proved strip bound off the coincidences `Tile.tileBelowPoleStripOffCoincClean` (the fleet's
  three-zeros endgame `Tile.tileStripOffCoincEndgame` fed by the cleared ball bound
  `TileTileNumBallTS.of_pieces`), with the non-coincidence hypothesis discharged by
  `stripNoCoincidence` from `Re w ≠ 0`.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Tile.orbitClassifyGe
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.K24F_sm_sum_bound
import Submission.Work.Asymptotics.K24FZ
import Submission.Work.Asymptotics.Tile.HalfDev24TileFacts
import Submission.Work.Asymptotics.Tile.HalfDev24Aux
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Tile.tileStripOffCoincDefs
import Submission.Work.Asymptotics.Tile.tileBelowPoleStripOffCoincClean

namespace Work.Asymptotics.Tile

set_option linter.unusedVariables false

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

noncomputable section

/-! ## No coincidence in the strip when `Re w ≠ 0` -/

/-- `Re (S • w) = - Re w / ‖w‖²`, whence `Re (S • w) = 0` forces `Re w = 0`. -/
private lemma re_S_smul_eq (w : UpperHalfPlane) :
    (ModularGroup.S • w).re = -w.re / Complex.normSq (w : ℂ) := by
  have hcoe : ((ModularGroup.S • w : ℍ) : ℂ) = -((w : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  rw [← UpperHalfPlane.coe_re, hcoe, Complex.neg_re, Complex.inv_re,
    UpperHalfPlane.coe_re, neg_div]

/-- **No coincidence in the resonant strip away from the bad line.**  For `w ∈ E` with
`Re w ≠ 0`, `n = ± 1` and `t` in the strip `|t - Im (S • w)| ≤ 1` the contour point `i t` is
not an orbit point of `n +ᵥ w` (i.e. `j (n +ᵥ w) ≠ j (i t)`). -/
lemma stripNoCoincidence (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (w : UpperHalfPlane)
    (hw : w ∈ Work.Asymptotics.KEpsilon) (hre : w.re ≠ 0) (n : ℤ) (hn : n = 1 ∨ n = -1)
    (t : ℝ) (ht : 0 < t)
    (ht1 : (ModularGroup.S • w).im - 1 ≤ t) (ht2 : t ≤ (ModularGroup.S • w).im + 1) :
    Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
      ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro hcon
  -- `j (n +ᵥ w) = j w = j (S • w)`, so `S • w` and `i t` are in the same orbit
  have hj₁ : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun w := by
    rcases hn with h | h
    · subst h; push_cast
      exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one w
    · subst h; push_cast
      have h1 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ w)
      rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w by rw [← add_vadd]; norm_num] at h1
      exact h1.symm
  have hj₂ : Work.Kernels.jInvariantFun (ModularGroup.S • w) = Work.Kernels.jInvariantFun w :=
    Work.Kernels.KernelFacts.jInvariantFun_S_smul w
  have hj : Work.Kernels.jInvariantFun (ModularGroup.S • w)
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    rw [hj₂, ← hj₁]; exact hcon
  -- geometry of `S • w`
  have hσD : ModularGroup.S • w ∈ Work.Asymptotics.DomainD :=
    Work.Asymptotics.S_smul_mem_DomainD hw.1
  obtain ⟨hre₁, hre₂⟩ := Work.Asymptotics.re_bounds_of_mem_DomainD hσD
  have hσre : |(ModularGroup.S • w).re| ≤ 1 := abs_le.mpr ⟨le_of_lt hre₁, le_of_lt hre₂⟩
  have hσim : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  have htge : (1 : ℝ) ≤ t := by have := hw.2; linarith
  -- the orbit classification
  obtain ⟨m, hm, hσm⟩ := orbitClassifyGe hσre hσim t ht htge hj
  have hvadd_re : (((m : ℝ) +ᵥ Work.Kernels.imagAxis t ht : ℍ)).re = (m : ℝ) := by
    rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]
    simp [Complex.add_re, Work.Kernels.imagAxis, Complex.mul_re]
  have hre_eq : (ModularGroup.S • w).re = (m : ℝ) := by
    have h := congrArg UpperHalfPlane.re hσm
    rw [hvadd_re] at h
    exact h
  have hmab : |((m : ℤ) : ℝ)| < 1 := by
    rw [← hre_eq]; exact abs_lt.mpr ⟨hre₁, hre₂⟩
  have hm0 : m = 0 := by
    rcases hm with h | h | h
    · subst h; norm_num at hmab
    · exact h
    · subst h; norm_num at hmab
  -- hence `Re (S • w) = 0`, i.e. `Re w = 0`, contradicting the hypothesis
  have hre0 : (ModularGroup.S • w).re = 0 := by rw [hre_eq, hm0]; norm_num
  have hnorm : (0 : ℝ) < Complex.normSq (w : ℂ) := Complex.normSq_pos.mpr w.ne_zero
  have hw0 : w.re = 0 := by
    have h := re_S_smul_eq w
    rw [hre0] at h
    have : -w.re / Complex.normSq (w : ℂ) = 0 := h.symm
    rw [div_eq_zero_iff] at this
    rcases this with h' | h'
    · linarith
    · exact absurd h' (ne_of_gt hnorm)
  exact hre hw0

/-- Off-axis norm of `qParamFun`. -/
private lemma norm_qParamFun_offAxis (ζ : UpperHalfPlane) :
    ‖Work.Kernels.qParamFun ζ‖ = Real.exp (-(2 * Real.pi * ζ.im)) := by
  have h : Work.Kernels.qParamFun ζ = (Work.Residues.Ept ζ) ^ 2 := by
    rw [Work.Kernels.qParamFun, Work.Residues.Ept, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  rw [h, norm_pow, Work.Residues.norm_Ept, ← Real.exp_nat_mul]
  congr 1
  push_cast; ring

/-- **The cleared `K₊^{(24)}` deviation, off axis.**
For `w ∈ E`, `n = ±1` and `ζ ∈ ℍ` with `3 ≤ Im ζ` and `|Re ζ| ≤ 3`:
`‖Sh (n+ᵥw) ζ‖ ‖K₊24 (n+ᵥw) ζ - 𝒢₊24 (n+ᵥw) ζ‖`
`  ≤ C (scale w)^N (1 + Im ζ)^M exp (2π (Im (S•w) - Im ζ))`. -/
theorem halfDevClearAxisPlus24 :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (ζ : UpperHalfPlane), (n = 1 ∨ n = -1) →
        w ∈ Work.Asymptotics.KEpsilon → 3 ≤ ζ.im → |(ζ : ℂ).re| ≤ 3 →
        ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ‖
            * ‖Work.Kernels.KPlus 24 ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gplus 24 ((n : ℝ) +ᵥ w) ζ‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + ζ.im) ^ M
              * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im)) := by
  obtain ⟨KA, NA, hKAp, hNA, hAtoms⟩ := H24.tileAtoms24_axis
  obtain ⟨Ks, Ns, hKsp, hNsp, hSmsum⟩ := sm_sum_le_atoms
  refine ⟨‖K24F.c‖ * (64 * Ks * (KA + 1) ^ 2 * 4 ^ Ns) + 1, 2 * NA + Ns, 2,
    by positivity, by positivity, by norm_num, ?_⟩
  intro w n ζ hn hw hz3 hzre
  have hzw : (0 : ℝ) < ζ.im := by linarith
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  set E : ℝ := Real.exp (2 * Real.pi * (ModularGroup.S • w).im) with hEdef
  have hE1 : (1 : ℝ) ≤ E := by
    rw [hEdef, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have h2 := hw.2
    positivity
  set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
  -- scale τ ≤ 4 scale w
  have hscaleτ : Work.Kernels.scale τ ≤ 4 * Work.Kernels.scale w := by
    have hcoe : ((τ : ℍ) : ℂ) = ((n : ℝ) : ℂ) + (w : ℂ) := by
      rw [hτdef]; exact UpperHalfPlane.coe_vadd _ _
    have hτim : τ.im = w.im := by
      have h := congrArg Complex.im hcoe
      simpa [UpperHalfPlane.coe_im] using h
    have hn1 : ‖((n : ℝ) : ℂ)‖ = 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      rcases hn with h | h <;> rw [h] <;> norm_num
    have hnorm : ‖(τ : ℂ)‖ ≤ ‖(w : ℂ)‖ + 1 := by
      rw [hcoe]
      calc ‖((n : ℝ) : ℂ) + (w : ℂ)‖ ≤ ‖((n : ℝ) : ℂ)‖ + ‖(w : ℂ)‖ := norm_add_le _ _
        _ = ‖(w : ℂ)‖ + 1 := by rw [hn1]; ring
    have h1 : (w.im)⁻¹ ≤ Work.Kernels.scale w := by
      rw [Work.Kernels.scale]; linarith [norm_nonneg ((w : ℂ))]
    have h2 : ‖(w : ℂ)‖ ≤ Work.Kernels.scale w := by
      rw [Work.Kernels.scale]; linarith [inv_nonneg.mpr w.im_pos.le]
    rw [Work.Kernels.scale, hτim]
    nlinarith [h1, h2, hs1, hnorm]
  have hpowτ : (Work.Kernels.scale τ) ^ Ns ≤ 4 ^ Ns * (Work.Kernels.scale w) ^ Ns := by
    have h1 : (Work.Kernels.scale τ) ^ Ns ≤ (4 * Work.Kernels.scale w) ^ Ns :=
      Real.rpow_le_rpow (Work.Kernels.scale_pos τ).le hscaleτ hNsp
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hs0.le] at h1
  -- the tile atoms, upgraded to the convenient constants
  set K0 : ℝ := KA + 1 with hK0def
  have hK01 : (1 : ℝ) < K0 := by rw [hK0def]; linarith
  have hK00 : (0 : ℝ) ≤ K0 := le_trans zero_le_one hK01.le
  set D : ℝ := K0 * (Work.Kernels.scale w) ^ NA with hDdef
  set Dj : ℝ := K0 * (Work.Kernels.scale w) ^ NA * E with hDjdef
  have hD0 : (0 : ℝ) ≤ D := by
    rw [hDdef]; exact mul_nonneg hK00 (Real.rpow_nonneg hs0.le NA)
  have hDj0 : (0 : ℝ) ≤ Dj := by rw [hDjdef]; exact mul_nonneg hD0 (Real.exp_nonneg _)
  have hsNA1 : (1 : ℝ) ≤ (Work.Kernels.scale w) ^ NA := Real.one_le_rpow hs1 hNA
  have hD1 : (1 : ℝ) ≤ D := by
    rw [hDdef]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ K0 * (Work.Kernels.scale w) ^ NA :=
          mul_le_mul hK01.le hsNA1 (by norm_num) hK00
  have hDj1 : (1 : ℝ) ≤ Dj := by
    rw [hDjdef]
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ K0 * (Work.Kernels.scale w) ^ NA * E :=
          mul_le_mul (mul_le_mul hK01.le hsNA1 (by norm_num) hK00) hE1 (by norm_num) hD0
  have hAt0 : TileAtoms24 τ D Dj := by
    have h0 := hAtoms w n hn hw
    refine h0.mono ?_ ?_
    · rw [hDdef]; exact mul_le_mul_of_nonneg_right (by rw [hK0def]; linarith)
        (Real.rpow_nonneg hs0.le NA)
    · rw [hDjdef]
      have h1 : KA * (Work.Kernels.scale w) ^ NA ≤ K0 * (Work.Kernels.scale w) ^ NA :=
        mul_le_mul_of_nonneg_right (by rw [hK0def]; linarith) (Real.rpow_nonneg hs0.le NA)
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
  have hSm := hSmsum τ ζ D Dj hD0 hDj0 hAt0 hz3
  by_cases hJ : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ = 0
  · have hSh0 : Work.Asymptotics.Compact.Sh τ ζ = 0 := by
      rw [Work.Asymptotics.Compact.Sh_eq, hJ, mul_zero, neg_zero]
    rw [hSh0]
    simp only [norm_zero, zero_mul]
    positivity
  · have hdiff := K24F.KPlus24_diff τ ζ hJ (K24F.E4_ne_zero_three ζ hz3)
    have hSh : Work.Asymptotics.Compact.Sh τ ζ
        = -(Work.Kernels.DeltaFun ζ
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ)) :=
      Work.Asymptotics.Compact.Sh_eq τ ζ
    have hkey : Work.Asymptotics.Compact.Sh τ ζ
          * (Work.Kernels.KPlus 24 τ ζ - Work.Asymptotics.Compact.Gplus 24 τ ζ)
        = -(K24F.c * (ζ : ℂ) ^ 2
            * (K24F.Sm1 τ ζ + K24F.Sm2 τ ζ + K24F.Sm3 τ ζ + K24F.Sm4 τ ζ + K24F.Sm5 τ ζ)) := by
      rw [hSh, neg_mul, hdiff]
    rw [← norm_mul, hkey, norm_neg]
    -- numeric bounds
    have hznorm : ‖(ζ : ℂ)‖ ≤ 4 * (1 + ζ.im) := by
      have h1 : ‖(ζ : ℂ)‖ ≤ |(ζ : ℂ).re| + |(ζ : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
      have h2 : |(ζ : ℂ).im| = ζ.im := by rw [UpperHalfPlane.coe_im, abs_of_pos hzw]
      rw [h2] at h1
      nlinarith [h1, hzre, hz3]
    have hq : ‖Work.Kernels.qParamFun ζ‖ = Real.exp (-(2 * Real.pi * ζ.im)) :=
      norm_qParamFun_offAxis ζ
    have hprod : (1 + D) * (1 + Dj) ≤ 4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E := by
      have h1 : (1 : ℝ) + D ≤ 2 * D := by linarith
      have h2 : (1 : ℝ) + Dj ≤ 2 * Dj := by linarith
      have h3 : (1 + D) * (1 + Dj) ≤ (2 * D) * (2 * Dj) :=
        mul_le_mul h1 h2 (by linarith) (by linarith)
      have hs2 : (Work.Kernels.scale w) ^ NA * (Work.Kernels.scale w) ^ NA
          = (Work.Kernels.scale w) ^ (2 * NA) := by
        rw [← Real.rpow_add hs0]; congr 1; ring
      calc (1 + D) * (1 + Dj) ≤ (2 * D) * (2 * Dj) := h3
        _ = 4 * (K0 ^ 2 * ((Work.Kernels.scale w) ^ NA * (Work.Kernels.scale w) ^ NA) * E) := by
            rw [hDdef, hDjdef]; ring
        _ = 4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E := by rw [hs2]; ring
    have hexp : E * Real.exp (-(2 * Real.pi * ζ.im))
        = Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im)) := by
      rw [hEdef, ← Real.exp_add]
      congr 1; ring
    have hmain : ‖K24F.c * (ζ : ℂ) ^ 2
          * (K24F.Sm1 τ ζ + K24F.Sm2 τ ζ + K24F.Sm3 τ ζ + K24F.Sm4 τ ζ + K24F.Sm5 τ ζ)‖
        ≤ ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
          * (Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
              * Real.exp (-(2 * Real.pi * ζ.im))) := by
      have h1 : ‖(ζ : ℂ) ^ 2‖ = ‖(ζ : ℂ)‖ ^ 2 := norm_pow _ 2
      have h2 : ‖(ζ : ℂ)‖ ^ 2 ≤ (4 * (1 + ζ.im)) ^ 2 := by
        have h0 : (0 : ℝ) ≤ ‖(ζ : ℂ)‖ := norm_nonneg _
        nlinarith [hznorm, h0, hzw]
      calc ‖K24F.c * (ζ : ℂ) ^ 2
            * (K24F.Sm1 τ ζ + K24F.Sm2 τ ζ + K24F.Sm3 τ ζ + K24F.Sm4 τ ζ + K24F.Sm5 τ ζ)‖
          = ‖K24F.c‖ * ‖(ζ : ℂ) ^ 2‖ * ‖K24F.Sm1 τ ζ + K24F.Sm2 τ ζ + K24F.Sm3 τ ζ
              + K24F.Sm4 τ ζ + K24F.Sm5 τ ζ‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
              * (Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
                  * ‖Work.Kernels.qParamFun ζ‖) := by
            rw [h1]
            exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) hSm
              (by positivity) (by positivity)
        _ = ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
              * (Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
                  * Real.exp (-(2 * Real.pi * ζ.im))) := by rw [hq]
    refine le_trans hmain ?_
    have hKsD : Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
        ≤ Ks * (4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E)
            * (4 ^ Ns * (Work.Kernels.scale w) ^ Ns) := by
      have h1a : Ks * ((1 + D) * (1 + Dj))
          ≤ Ks * (4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E) :=
        mul_le_mul_of_nonneg_left hprod hKsp.le
      have h1b := mul_le_mul h1a hpowτ (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le Ns)
        (by positivity)
      calc Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
          = (Ks * ((1 + D) * (1 + Dj))) * (Work.Kernels.scale τ) ^ Ns := by ring
        _ ≤ (Ks * (4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E))
              * (4 ^ Ns * (Work.Kernels.scale w) ^ Ns) := h1b
    have hstep : ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
          * (Ks * (1 + D) * (1 + Dj) * (Work.Kernels.scale τ) ^ Ns
              * Real.exp (-(2 * Real.pi * ζ.im)))
        ≤ ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
          * (Ks * (4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E)
              * (4 ^ Ns * (Work.Kernels.scale w) ^ Ns) * Real.exp (-(2 * Real.pi * ζ.im))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hKsD (Real.exp_nonneg _))
        (by positivity)
    have hcoef0 : (0 : ℝ) ≤ ‖K24F.c‖ * (64 * Ks * K0 ^ 2 * 4 ^ Ns) := by positivity
    have hcomb2 : (Work.Kernels.scale w) ^ (2 * NA + Ns)
        = (Work.Kernels.scale w) ^ (2 * NA) * (Work.Kernels.scale w) ^ Ns :=
      Real.rpow_add hs0 _ _
    have hL : ‖K24F.c‖ * (4 * (1 + ζ.im)) ^ 2
          * (Ks * (4 * K0 ^ 2 * (Work.Kernels.scale w) ^ (2 * NA) * E)
              * (4 ^ Ns * (Work.Kernels.scale w) ^ Ns) * Real.exp (-(2 * Real.pi * ζ.im)))
        = (‖K24F.c‖ * (64 * Ks * K0 ^ 2 * 4 ^ Ns))
          * ((Work.Kernels.scale w) ^ (2 * NA) * (Work.Kernels.scale w) ^ Ns)
          * (1 + ζ.im) ^ 2 * (E * Real.exp (-(2 * Real.pi * ζ.im))) := by ring
    refine le_trans hstep ?_
    rw [hL, ← hcomb2, hexp]
    have hfin : (‖K24F.c‖ * (64 * Ks * K0 ^ 2 * 4 ^ Ns))
          * (Work.Kernels.scale w) ^ (2 * NA + Ns) * (1 + ζ.im) ^ 2
          * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im))
        ≤ (‖K24F.c‖ * (64 * Ks * K0 ^ 2 * 4 ^ Ns) + 1) * (Work.Kernels.scale w) ^ (2 * NA + Ns)
          * (1 + ζ.im) ^ 2 * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hs0.le _)
      linarith
    have hK0eq : K0 = KA + 1 := hK0def
    refine le_trans hfin (le_of_eq ?_)
    rw [hK0eq, Real.rpow_two]


/-- **The three-distance product on a sphere.**  For a point `z` of the sphere `‖z - c‖ = ρ` with
`1 ≤ ρ` the product of the distances to `c - 1`, `c` and `c + 1` is at least `ρ (ρ - 1) ^ 2`.
This is the constant `δ` in the three-zeros estimate `three_zeros_bound_ball` for the ball
`Metric.ball c ρ` centred at the tile point `c = S • w` with the three resonant zeros
`c - 1, c, c + 1`. -/
lemma sphere_prod_dist_ge (c : ℂ) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∀ z ∈ Metric.sphere c ρ,
      ρ * (ρ - 1) ^ 2 ≤ ‖z - (c - 1)‖ * ‖z - c‖ * ‖z - (c + 1)‖ := by
  intro z hz
  have hzc : ‖z - c‖ = ρ := by
    have h := Metric.mem_sphere.mp hz
    rwa [dist_eq_norm] at h
  have h1 : ρ - 1 ≤ ‖z - (c - 1)‖ := by
    have h := abs_norm_sub_norm_le (z - c) (-1 : ℂ)
    have h' : (z - c) - (-1 : ℂ) = z - (c - 1) := by ring
    rw [h', hzc, norm_neg, norm_one] at h
    exact (abs_le.mp h).2
  have h2 : ρ - 1 ≤ ‖z - (c + 1)‖ := by
    have h := abs_norm_sub_norm_le (z - c) (1 : ℂ)
    have h' : (z - c) - (1 : ℂ) = z - (c + 1) := by ring
    rw [h', hzc, norm_one] at h
    exact (abs_le.mp h).2
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hpm : (0 : ℝ) ≤ ρ - 1 := by linarith
  calc ρ * (ρ - 1) ^ 2 = (ρ - 1) * (ρ - 1) * ρ := by ring
    _ ≤ ‖z - (c - 1)‖ * ‖z - (c + 1)‖ * ‖z - c‖ :=
        mul_le_mul (mul_le_mul h1 h2 hpm (norm_nonneg _)) (le_of_eq hzc.symm)
          (le_of_lt hρ0) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖z - (c - 1)‖ * ‖z - c‖ * ‖z - (c + 1)‖ := by ring

/-! ## The target -/

/-- **The resonant strip on the cusp-`1` tile, restricted to `Re w ≠ 0`.**  See the module
docstring: the analytic content is `Tile.tileWindowRestricted_strip` specialised to `n = 1`. -/
theorem tileStripCusp1Re (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → w.re ≠ 0 → ∀ t : ℝ,
        (ModularGroup.S • w).im - 1 ≤ t → t ≤ (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ w) t‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := tileBelowPoleStripOffCoincClean ℓ d hd
  refine ⟨C, N, M, hC, hN, hM, ?_⟩
  intro w hw hre t ht1 ht2
  have ht : 0 < t := by have := hw.2; linarith
  have h := hb w 1 (Or.inl rfl) hw t ht ht1 ht2
    (stripNoCoincidence ℓ d w hw hre 1 (Or.inl rfl) t ht ht1 ht2)
  simpa using h

end

end Work.Asymptotics.Tile
