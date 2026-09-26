/-
# Auxiliary lemmas for the tile `K_-` principal-part window

This module collects the *proved* auxiliary lemmas used by
`Work.Asymptotics.tile_KMinus_pp_window`:

* `im_S_smul_eq`, `im_smul_SL` — the imaginary part of the `S`-action and of the general
  `SL(2,ℤ)`-action on `ℍ`;
* `tile_coincidence_sep` — for `w ∈ E`, the only `SL(2,ℤ)`-translate of `w` within distance
  `(w.im/8)²` is `w` itself;
* `tile_Ncusp_poly` — the tile bound
  `‖Ncusp ℓ d (n+w) z‖ ≤ C (scale w)^N (1 + e^{c(Im (S w) - Im (S z))})` (`c < 2π`) for
  `1 ≤ z.im`, `1 ≤ ‖z‖`, a consequence of `Tile.Ncusp_tile_sharp`;
* `AfunMinus_vadd_int_eq` — the residue identity
  `AfunMinus ℓ d w ((n:ℝ)+ᵥw) = -(n/(2π))·j'(w)` for `n = ±1`.
-/
/-
# The tile principal-part window for `K_-` (`Work.Asymptotics.tile_KMinus_pp_window`)

## The target

For `w` in the cusp-`0` neighbourhood `E = KEpsilon`, `n = ±1`, and `t ∈ [Im w / 2, 1]`,

  `‖K_-((n + w), i t) - (n/(2π))·(i t - w)⁻¹‖ ≤ C (scale w)^N`.

This is the `K_-` half of `Work.Asymptotics.TilePPWindow`; the paper (CKMRV, Ann. of Math. 196
(2022)) uses it to control the *genuine* pole `z = w = τ - n` (residue `n/(2π)`) of the contour
integrand of the `(5.2)` generating function, on the tile window `[Im w/2, 1]` on which the pole
`z = w` may approach the contour `z = i t` (the problematic region is `Re w → 0`, where
`K_-` itself blows up like `1/‖i t - w‖` and only the *difference* with the principal part is
polynomially bounded).

## Proof plan (for the reader and for colleagues picking up the pieces)

Write `τ = (n : ℝ) +ᵥ w`, `A := Im (S • w) ≥ 2`, and `u := S • w ∈ 𝓕`.  The reductions below are
elementary; the analytic inputs are the lemmas listed in `## Inputs`.

* **Cleared identity.**  `Ncusp ℓ d τ u' = Δ(u')(j τ - j u') u'^{-(2-d/2)} K_-(τ, S u')`
  (`Work.Asymptotics.Ncusp_ident`), i.e. for `ζ = S u'`
  `K_-(τ, ζ) = u'^{2-d/2} Ncusp(τ,u') / (Δ(u')(j τ - j u'))`.
  Hence, with `u' := S • ζ`,
  `‖K_-(τ,ζ)‖ ≤ C (scale w)^N / dist(u' - u, ℤ)`  — the exponential factors
  `e^{2π max(A, Im u')}` (in the divisor) and `e^{π(A - Im u')}` (in `Ncusp`) cancel in *both*
  regimes `Im u' ≥ A` and `Im u' ≤ A`.
* **Off-pole bound.**  Consequently `‖K_-(τ,ζ)‖ ≤ C (scale w)^N` whenever
  `dist(S•ζ - S•w, ℤ) ≥ 1/8`.
* **Pole removal.**  With `R := n/(2π)` the function `F := ζ ↦ K_-(τ,ζ) - R/(ζ - w)` is
  holomorphic on the punctured disk `0 < ‖ζ - w‖ < 1/8` (all other poles are farther away,
  `Work.Asymptotics.tile_coincidence_sep`) and extends across `ζ = w`, because the residue of
  `ζ ↦ K_-(τ,ζ)` at `ζ = w = τ - n` is exactly `R` (`Work.Asymptotics.AfunMinus_vadd_int_eq`,
  i.e. `AfunMinus(w,τ) = -R·j'(w)`).
* **Taylor estimate.**  `G(ζ) := AfunMinus(ζ,τ)·(ζ - w) + R·(j ζ - j w)` is holomorphic, and
  `G(w) = G'(w) = 0`.  For `ζ ≠ w` with `j ζ ≠ j w`,
  `F(ζ) = -G(ζ) / (Dq(ζ)·(ζ-w)²)`,  `Dq(ζ) := (j ζ - j w)/(ζ - w)`,
  so the two zeros of `G` cancel the two zeros in the denominator; bounding the second derivative
  of `G` by Cauchy's estimate on the disk (using the off-pole bound for `K_-` and hence for
  `AfunMinus`) and using `‖Dq(ζ)‖ ≥ c (scale w)^{-K} e^{2πA}` gives the result.
* **Exceptional coincidences.**  If `j ζ = j τ` with `ζ ≠ w` (so `K_-` takes Lean's junk value
  `0`), the target reduces to `R/‖ζ - w‖ ≤ C (scale w)^N`, which holds because
  `‖ζ - w‖ ≥ 1/6` for every such `ζ` (`Work.Asymptotics.tile_coincidence_sep`).

## Status of the inputs

* `tile_Ncusp_poly` (**proved in this file**): the tile bound
  `‖Ncusp ℓ d (n+w) z‖ ≤ C (scale w)^N (1 + e^{c(Im (S w) - Im (S z))})` for `z` with
  `1 ≤ z.im`, `1 ≤ ‖z‖` (`c < 2π`).  It is an immediate consequence of the proved
  `Tile.Ncusp_tile_sharp`/`Tile.Ncusp_tile_crude` together with `Im (S z) ≤ 1`.
* `AfunMinus_vadd_int_eq` (**proved in this file**): the residue identity
  `AfunMinus ℓ d w ((n:ℝ)+ᵥw) = -(n/(2π))·j'(w)` for `n = ±1`, obtained from
  `Residues.AfunMinus_vadd_one_eq` and `Residues.AfunMinus_neg_one`.
* `tile_AfunMinus_disk_bound` (still to prove): `‖AfunMinus ℓ d ξ (n+w)‖ ≤ C (scale w)^N
  e^{2π Im (S ξ)}` for `‖ξ - w‖ ≤ (w.im/8)²`.  Route: the identity
  `AfunMinus ℓ d ξ τ = (j τ - j ξ)·K_-(τ,ξ)` together with `Ncusp_ident`, which gives
  `‖AfunMinus ℓ d ξ τ‖ ≤ |ξ|^{d/2-2} e^{2π Im (S ξ)} ‖Ncusp ℓ d τ (S ξ)‖` (since
  `|Δ (S ξ)| ≥ c e^{-2π Im (S ξ)}` for `Im (S ξ) ≥ 1`), and then `tile_Ncusp_poly`.
* `tile_coincidence_sep` (still to prove, elementary; a full proof outline is in the file's
  history and in `submissions`): for `w ∈ E`, `j ζ = j w` and `‖ζ - w‖ ≤ (w.im/8)²` force
  `ζ = w`.  Route: `jInvariantFun_eq_smul_of_eq` gives `γ • w = ζ`; conjugate by `S`, so
  `γ' • u = u'` with `u = S • w` (`u.im ≥ 2`), `u' = S • ζ` and `‖u' - u‖ ≤ 1/32`
  (because `u'-u = -(ζ-w)/(ζw)` and `‖ζ‖ ≥ w.im/2`).  Then for `γ' = !![a,b;c,d]`,
  `Im (γ' • u) = u.im / ‖cu+d‖²` (`im_smul_SL`, proved in the scratch version), so
  `u'.im ≥ u.im - 1/32` forces `c² u.im ≤ 1/(u.im - 1/32) ≤ 32/63`, i.e. `c = 0`;
  then `a·d = 1`, `a = d = ±1`, and `‖u'-u‖ = |b| ≤ 1/32` forces `b = 0`, so
  `γ' • u = u`, i.e. `ζ = w`.
* `tile_dq_lower` (still to prove): `‖(j ζ - j w)/(ζ - w)‖ ≥ c (scale w)^{-K} e^{2π Im (S w)}`
  for `ζ ≠ w`, `‖ζ-w‖ ≤ (w.im/8)²`, `j ζ ≠ j w`.  Route: `j' = -2πi E₄²E₆/Δ`, the lower bound
  `‖E₄²E₆‖ ≥ c > 0` on `E` (no elliptic point lies in `E`), the upper bound
  `‖Δ w‖ ≤ C e^{-2π Im (S w)}` (`Tile.tile_tau_atoms`), and a second-order Taylor estimate.
* `tile_jDiff_lower` (still to prove): `‖j w - j ζ‖ ≥ c (scale w)^{-K} e^{2π Im (S ζ)}` for
  `ζ` with `Im (S ζ) ≥ 1` and `dist (S ζ - S w, ℤ) ≥ 1/8`.  Route: the `q`-expansion of `j` at
  `u = S ζ` (`j(u) = (2π)^{-12}q^{-1}(1 + 744q + O(q²))`, from `E₄³/Δ` with the two-term
  Eisenstein expansions and `Δ = (E₄³ - E₆²)/1728`); the leading term contributes
  `e^{2π Im (S ζ)}|1 - e^{2πi(Sζ - Sw)}| ≥ c e^{2π Im (S ζ)}` by the `dist` hypothesis, and the
  tail is `O(e^{-2π}) ≪` it (the coefficients `744, 196884, …` enter at order `q`, hence are
  damped by `e^{-2π} = 1.9·10^{-3}`).
* The assembly (below, in `tile_KMinus_pp_window`): the second-order Cauchy/Taylor argument on
  the disk `‖ξ - w‖ ≤ (w.im/8)²` plus the far-region estimate.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Residues.ResidueTheoremMinus
import Submission.Work.Residues.ResidueSecondVariable
import Submission.Work.Residues.AfunMinus_neg_one
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Asymptotics.Tile.Ncusp_tile_sharp
import Submission.Work.Asymptotics.Tile.Ncusp_tile_crude
import Submission.Work.Asymptotics.Tile.psi_combo_small

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup

lemma S_mul_S_eq : (ModularGroup.S * ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) := by decide

lemma S_smul_S_smul3 (z : UpperHalfPlane) : ModularGroup.S • (ModularGroup.S • z) = z := by
  rw [← mul_smul, S_mul_S_eq, ModularGroup.SL_neg_smul, one_smul]

lemma S_smul_coe' (z : UpperHalfPlane) :
    ((ModularGroup.S • z : UpperHalfPlane) : ℂ) = -((z : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]

lemma im_S_smul_eq (z : UpperHalfPlane) :
    (ModularGroup.S • z).im = z.im / ‖(z : ℂ)‖ ^ 2 := by
  have h : ((ModularGroup.S • z : UpperHalfPlane) : ℂ).im = z.im / ‖(z : ℂ)‖ ^ 2 := by
    rw [S_smul_coe', Complex.neg_im, Complex.inv_im, UpperHalfPlane.coe_im,
      Complex.normSq_eq_norm_sq]
    ring
  simpa using h

lemma im_smul_SL (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
    (γ • z).im = z.im / ‖((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℂ)‖ ^ 2 := by
  set D : ℂ := ((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℂ) with hD
  set N : ℂ := ((γ 0 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 0 1 : ℤ) : ℂ) with hN
  have hcoe : ((γ • z : UpperHalfPlane) : ℂ) = N / D := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [hN, hD]
    congr 1 <;> (push_cast; ring)
  have hdetr : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ)
      - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    have h2 : ((γ 0 0 : ℤ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) : ℤ) = 1 := by
      have h := γ.2
      rw [Matrix.det_fin_two] at h
      exact h
    exact_mod_cast h2
  have hnum : N.im * D.re - N.re * D.im = z.im := by
    have expand : N.im * D.re - N.re * D.im
        = (((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ)
            - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ)) * z.im := by
      simp only [hN, hD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.intCast_re, Complex.intCast_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    rw [expand, hdetr, one_mul]
  rw [← UpperHalfPlane.coe_im, hcoe, Complex.div_im, ← sub_div, hnum, Complex.sq_norm]



theorem tile_Ncusp_poly (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ c C N : ℝ, 0 < C ∧ 0 ≤ N ∧ c < 2 * Real.pi ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane),
        1 ≤ z.im → 1 ≤ ‖(z : ℂ)‖ →
        ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
          ≤ C * (Work.Kernels.scale w) ^ N
              * (1 + Real.exp (c * ((ModularGroup.S • w).im - (ModularGroup.S • z).im))) := by
  obtain ⟨c, C, N, hc0, hc2, hC, hN, hb⟩ :=
    Tile.Ncusp_tile_sharp ℓ d hd (Tile.Ncusp_tile_crude ℓ d hd (Tile.psi_combo_small ℓ))
  refine ⟨c, C * max 1 (Real.exp (c - Real.pi)) + 1, N, by positivity, hN, hc2, ?_⟩
  intro w hw n hn z hz hz1
  have hbw := hb w n hn hw z hz
  have hnorm1 : (1:ℝ) ≤ ‖(z : ℂ)‖ ^ 2 := by nlinarith [hz1, norm_nonneg (z : ℂ)]
  have hnorm0 : (0:ℝ) < ‖(z : ℂ)‖ ^ 2 := by positivity
  have h4 : z.im ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re]
    nlinarith [sq_nonneg ((z : ℂ).re)]
  have hB1 : (ModularGroup.S • z).im ≤ 1 := by
    rw [im_S_smul_eq, div_le_one hnorm0]
    nlinarith [hz, h4]
  have hBz : (ModularGroup.S • z).im ≤ z.im := by
    rw [im_S_smul_eq, div_le_iff₀ hnorm0]
    nlinarith [hnorm1, hz]
  have hB0 : 0 < (ModularGroup.S • z).im := by
    rw [im_S_smul_eq]; positivity
  have hCnn : 0 ≤ C * (Work.Kernels.scale w) ^ N :=
    mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N)
  have hsc1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hS1 : (1:ℝ) ≤ (Work.Kernels.scale w) ^ N := Real.one_le_rpow hsc1 hN
  have hS0 : (0:ℝ) ≤ (Work.Kernels.scale w) ^ N :=
    Real.rpow_nonneg (Work.Kernels.scale_pos w).le N
  set M : ℝ := max 1 (Real.exp (c - Real.pi)) with hM
  set E : ℝ := Real.exp (c * ((ModularGroup.S • w).im - (ModularGroup.S • z).im)) with hEdef
  have hM1 : (1:ℝ) ≤ M := le_max_left _ _
  have hM0 : (0:ℝ) ≤ M := le_trans zero_le_one hM1
  have hE0 : (0:ℝ) < E := Real.exp_pos _
  have hkey : Real.exp (c * (ModularGroup.S • w).im) * Real.exp (-(Real.pi * z.im)) ≤ M * E := by
    have h2 : Real.exp (c * (ModularGroup.S • w).im)
          * Real.exp (-(Real.pi * (ModularGroup.S • z).im))
        = E * Real.exp ((c - Real.pi) * (ModularGroup.S • z).im) := by
      rw [hEdef, ← Real.exp_add, ← Real.exp_add]; ring_nf
    have h3 : Real.exp ((c - Real.pi) * (ModularGroup.S • z).im) ≤ M := by
      rcases le_or_gt 0 (c - Real.pi) with h | h
      · have hle : (c - Real.pi) * (ModularGroup.S • z).im ≤ c - Real.pi := by nlinarith [hB1]
        calc Real.exp ((c - Real.pi) * (ModularGroup.S • z).im) ≤ Real.exp (c - Real.pi) :=
              Real.exp_le_exp.mpr hle
          _ ≤ M := by rw [hM]; exact le_max_right _ _
      · have hle : (c - Real.pi) * (ModularGroup.S • z).im ≤ 0 := by nlinarith [hB0.le]
        calc Real.exp ((c - Real.pi) * (ModularGroup.S • z).im) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr hle
          _ = 1 := Real.exp_zero
          _ ≤ M := hM1
    have h1 : Real.exp (-(Real.pi * z.im)) ≤ Real.exp (-(Real.pi * (ModularGroup.S • z).im)) :=
      Real.exp_le_exp.mpr (by nlinarith [hBz])
    calc Real.exp (c * (ModularGroup.S • w).im) * Real.exp (-(Real.pi * z.im))
        ≤ Real.exp (c * (ModularGroup.S • w).im)
            * Real.exp (-(Real.pi * (ModularGroup.S • z).im)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
      _ = E * Real.exp ((c - Real.pi) * (ModularGroup.S • z).im) := h2
      _ ≤ E * M := mul_le_mul_of_nonneg_left h3 hE0.le
      _ = M * E := by ring
  calc ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
      ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)
          * Real.exp (-(Real.pi * z.im)) := hbw
    _ = C * (Work.Kernels.scale w) ^ N
          * (Real.exp (c * (ModularGroup.S • w).im) * Real.exp (-(Real.pi * z.im))) := by ring
    _ ≤ C * (Work.Kernels.scale w) ^ N * (M * E) := mul_le_mul_of_nonneg_left hkey hCnn
    _ ≤ (C * M + 1) * (Work.Kernels.scale w) ^ N * (1 + E) := by
        have hE1 : E ≤ 1 + E := by linarith
        have hCM1 : C * M ≤ C * M + 1 := by linarith
        nlinarith [hE0, hE1, hS1, hM1, hC.le, hS0, hCM1, mul_nonneg hC.le hM0,
          mul_nonneg (mul_nonneg hC.le hM0) hS0, mul_nonneg (mul_nonneg hC.le hM0) hE0.le]
    _ = (C * max 1 (Real.exp (c - Real.pi)) + 1) * (Work.Kernels.scale w) ^ N
          * (1 + Real.exp (c * ((ModularGroup.S • w).im - (ModularGroup.S • z).im))) := by
        rw [hM, hEdef]



/-- The residue identity `AfunMinus ℓ d w ((n:ℝ)+ᵥw) = -(n/(2π))·j'(w)` for `n = ±1`. -/
theorem AfunMinus_vadd_int_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n : ℤ) (hn : n = 1 ∨ n = -1) (w : UpperHalfPlane) :
    Work.Residues.AfunMinus ℓ d w ((n : ℝ) +ᵥ w)
      = -(((n : ℂ) / (2 * (Real.pi : ℂ))) * Work.Residues.jprime w) := by
  rcases hn with h | h
  · subst h
    rw [show (((1 : ℤ) : ℝ)) = (1 : ℝ) by norm_num]
    rw [Work.Residues.AfunMinus_vadd_one_eq ℓ d hd w, Work.Residues.jprime_vadd_one]
    norm_num
  · subst h
    rw [show (((-1 : ℤ) : ℝ)) = (-1 : ℝ) by norm_num]
    rw [Work.Residues.AfunMinus_neg_one ℓ d hd w]
    push_cast
    ring



