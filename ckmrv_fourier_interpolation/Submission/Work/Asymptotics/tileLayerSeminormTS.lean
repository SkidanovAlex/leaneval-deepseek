/-
# The `r`-seminorm bound for the CKMRV layer on the cusp-`1` tile

Target: `Work.Asymptotics.TileLayerSeminorm ℓ d` — for `w ∈ E = KEpsilon` with `Re w ≠ 0` the
`r`-seminorms of the regularised CKMRV layer `layer (Gcusp ℓ d) ℓ d (1 + w) ·` at the cusp-`1`
tile points `1 + w` grow at most polynomially in `scale w`.

## The decomposition

`layer G ℓ d τ r = if r = 0 then 0 else paperLayer G ℓ d τ r` and
`paperLayer = layerLow + layerTrunc + highPart`, so the bound is assembled from the three pieces:

* `Work.Asymptotics.Tile.layerLow_tile_seminorm` (proved, from the principal-part window
  `Work.Asymptotics.Tile.tilePPWindow_bound`) — the `low` piece `sinSq r ∫_0^1 K e^{-πr²t} dt`,
  which contains the translate pole `z = w`;
* the `trunc` piece `sinSq r ∫_1^∞ (K - Aexp) e^{-πr²t} dt`, whose `r`-seminorms are bounded in
  `tileLayerTrunc_bound_restr` below from the *below-pole window* on the cusp-`±1` tiles at
  `Re w ≠ 0` (`tileWindowRestricted'`, assembled here from the far / strip / top regimes and the
  low window) and the sharp tail `Work.Asymptotics.Tile.tileSharpTail` (proved);
* the explicit closed form `highPart`, bounded directly on the tile from
  `Work.Asymptotics.Gcusp_tile_bound`.

## Why the restriction `Re w ≠ 0`

The *unrestricted* below-pole window on the tiles is **false**: at the bad line `Re w = 0` the
contour meets a coincidence `j (n +ᵥ w) = j (i t)`, where `Kfun` (built with Lean's totalised
inverse, `0⁻¹ = 0`) takes a junk value that is exponentially large in `scale w`
(`Work.Asymptotics.Tile.tileStripCusp1Re`, `tileStripOffCoincDefs`).  For `Re w ≠ 0` no point of
the below-pole window is a coincidence, and the polynomial bound is the genuine statement.
-/
import Mathlib
import Submission.Work.Asymptotics.cuspOneTileInputs
import Submission.Work.Asymptotics.Tile.layerLow_tile_seminorm
import Submission.Work.Asymptotics.Tile.tileLayerTrunc_bound
import Submission.Work.Asymptotics.Tile.tilePPWindow_bound
import Submission.Work.Asymptotics.Tile.tileSharpTail
import Submission.Work.Asymptotics.Tile.tileWinDefs
import Submission.Work.Asymptotics.Tile.tile_dev_low
import Submission.Work.Asymptotics.Tile.tileBelowPoleTop
import Submission.Work.Asymptotics.Tile.tileWindowFar
import Submission.Work.Asymptotics.Tile.tileWindowRestricted_strip
import Submission.Work.Asymptotics.highPart_seminorm
import Submission.Work.Asymptotics.paperLayer_smooth
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.Asymptotics.Kaxis_tile_flat_below_pole
import Submission.Work.Asymptotics.Kaxis_tile_aux
import Submission.Work.Asymptotics.SpikeCircle.divisorLowerDisc
import Submission.Work.Asymptotics.Tile.tileStripCusp1Re

set_option maxHeartbeats 3200000

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane Topology ContDiff

namespace Work.Asymptotics

variable {ℓ : Work.Kernels.LogLambdaData}

/-! ## The below-pole window on the tiles, restricted to `Re w ≠ 0` -/

/-- Rewrite the target's left-hand side, using `z = i t`, as the difference `Kfun - Gfun`. -/
private lemma axisAexp_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp (Gcusp ℓ d) τ t
      = Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)
        - Compact.Gfun d ℓ τ (Work.Kernels.imagAxis t ht) := by
  rw [Work.Kernels.Kaxis, dif_pos ht, Gcusp_eq_Gcoef ℓ d hd, Aexp_Gcoef' ℓ d τ t ht]

/-- Monotonicity of `C s^N t^M` in the constant and in the two exponents, for `s, t ≥ 1`. -/
private lemma absorb_bound {s t C C' N N' M M' : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hC' : C ≤ C') (hN : N ≤ N') (hM : M ≤ M') :
    C * s ^ N * t ^ M ≤ C' * s ^ N' * t ^ M' := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : s ^ N ≤ s ^ N' := Real.rpow_le_rpow_of_exponent_le hs hN
  have h2 : t ^ M ≤ t ^ M' := Real.rpow_le_rpow_of_exponent_le ht hM
  have h3 : s ^ N * t ^ M ≤ s ^ N' * t ^ M' :=
    mul_le_mul h1 h2 (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hs0.le _)
  have h3nn : (0 : ℝ) ≤ s ^ N * t ^ M :=
    mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg ht0.le _)
  calc C * s ^ N * t ^ M = C * (s ^ N * t ^ M) := by ring
    _ ≤ C' * (s ^ N' * t ^ M') := mul_le_mul hC' h3 h3nn (le_trans hC hC')
    _ = C' * s ^ N' * t ^ M' := by ring

/-- **The below-pole window on the cusp-`±1` tiles at `Re w ≠ 0`**, assembled from its four
`t`-regimes: the low window (`tile_dev_low`), the far regime (`far`, which holds for all
`w ∈ KEpsilon`), the resonant strip (`strip`) and the top regime (`tileBelowPoleTop`). -/
private theorem tileWindowRestricted_of_pieces (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (far : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane), w ∈ KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ t : ℝ,
        1 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M)
    (strip : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane), w ∈ KEpsilon → w.re ≠ 0 → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ t : ℝ, (ModularGroup.S • w).im - 1 ≤ t → t ≤ (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon → w.re ≠ 0 →
        ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  obtain ⟨Cf, Nf, Mf, hCf, hNf, hMf, hfarb⟩ := far
  obtain ⟨Cs, Ns, Ms, hCs, hNs, hMs, hstripb⟩ := strip
  obtain ⟨Ct, Nt, Mt, hCt, hNt, hMt, htopb⟩ := Tile.tileBelowPoleTop ℓ d hd
  obtain ⟨Cl, Nl, hCl, hNl, hlowb⟩ := Tile.tile_dev_low ℓ d hd
  refine ⟨max (max Cl Cf) (max Cs Ct) + 1, max (max Nl Nf) (max Ns Nt),
    max (max Mf Ms) Mt, by positivity, ?_, ?_, ?_⟩
  · exact le_trans hNl (le_trans (le_max_left Nl Nf) (le_max_left _ _))
  · exact le_trans hMf (le_trans (le_max_left Mf Ms) (le_max_left _ _))
  · intro w n hn hw hre t ht1 ht2
    have ht : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hs1 : 1 ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hsc0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hs1
    have hNl' : Nl ≤ max (max Nl Nf) (max Ns Nt) :=
      le_trans (le_max_left Nl Nf) (le_max_left _ _)
    have hNf' : Nf ≤ max (max Nl Nf) (max Ns Nt) :=
      le_trans (le_max_right Nl Nf) (le_max_left _ _)
    have hNs' : Ns ≤ max (max Nl Nf) (max Ns Nt) :=
      le_trans (le_max_left Ns Nt) (le_max_right _ _)
    have hNt' : Nt ≤ max (max Nl Nf) (max Ns Nt) :=
      le_trans (le_max_right Ns Nt) (le_max_right _ _)
    have hMf' : Mf ≤ max (max Mf Ms) Mt := le_trans (le_max_left Mf Ms) (le_max_left _ _)
    have hMs' : Ms ≤ max (max Mf Ms) Mt := le_trans (le_max_right Mf Ms) (le_max_left _ _)
    have hMt' : Mt ≤ max (max Mf Ms) Mt := le_max_right _ _
    have hM0 : (0 : ℝ) ≤ max (max Mf Ms) Mt :=
      le_trans hMf (le_trans (le_max_left Mf Ms) (le_max_left _ _))
    have hCl' : Cl ≤ max (max Cl Cf) (max Cs Ct) + 1 := by
      have h : Cl ≤ max (max Cl Cf) (max Cs Ct) := le_trans (le_max_left Cl Cf) (le_max_left _ _)
      linarith
    have hCf' : Cf ≤ max (max Cl Cf) (max Cs Ct) + 1 := by
      have h : Cf ≤ max (max Cl Cf) (max Cs Ct) := le_trans (le_max_right Cl Cf) (le_max_left _ _)
      linarith
    have hCs' : Cs ≤ max (max Cl Cf) (max Cs Ct) + 1 := by
      have h : Cs ≤ max (max Cl Cf) (max Cs Ct) := le_trans (le_max_left Cs Ct) (le_max_right _ _)
      linarith
    have hCt' : Ct ≤ max (max Cl Cf) (max Cs Ct) + 1 := by
      have h : Ct ≤ max (max Cl Cf) (max Cs Ct) := le_trans (le_max_right Cs Ct) (le_max_right _ _)
      linarith
    by_cases h3 : t ≤ 3
    · have hl := hlowb w hw n hn t ht ht1 h3
      have htM : (1 : ℝ) ≤ t ^ (max (max Mf Ms) Mt) := Real.one_le_rpow ht1 hM0
      have hstep : Cl * (Work.Kernels.scale w) ^ Nl
          ≤ Cl * (Work.Kernels.scale w) ^ Nl * t ^ (max (max Mf Ms) Mt) := by
        calc Cl * (Work.Kernels.scale w) ^ Nl
            = Cl * (Work.Kernels.scale w) ^ Nl * 1 := (mul_one _).symm
          _ ≤ Cl * (Work.Kernels.scale w) ^ Nl * t ^ (max (max Mf Ms) Mt) :=
              mul_le_mul_of_nonneg_left htM (mul_nonneg hCl.le (Real.rpow_nonneg hsc0 _))
      refine le_trans (le_trans (by
        simpa [axisAexp_eq ℓ d hd ((n : ℝ) +ᵥ w) t ht] using hl) hstep) ?_
      exact absorb_bound hs1 ht1 hCl.le hCl' hNl' (le_refl _)
    · push_neg at h3
      by_cases h4 : t ≤ (ModularGroup.S • w).im - 1
      · refine le_trans (hfarb w hw n hn t ht1 h4) ?_
        exact absorb_bound hs1 ht1 hCf.le hCf' hNf' hMf'
      · push_neg at h4
        by_cases h5 : t ≤ (ModularGroup.S • w).im + 1
        · refine le_trans (hstripb w hw hre n hn t (le_of_lt h4) h5) ?_
          exact absorb_bound hs1 ht1 hCs.le hCs' hNs' hMs'
        · push_neg at h5
          refine le_trans (htopb w hw n hn t (le_of_lt h5) ht2) ?_
          exact absorb_bound hs1 ht1 hCt.le hCt' hNt' hMt'

/-! ## The resonant strip from the ball bound on the cleared numerator

The remaining input of the strip estimate is the two-dimensional bound for the *cleared*
numerator `N(ζ) = 2·Sh(τ,ζ)·(Kfun(τ,ζ) − Gfun(τ,ζ))`, `τ = n +ᵥ w`, on the disc
`‖ζ − S•w‖ ≤ 29/20` (the requested input `tileBallBound`).  Given that bound the strip estimate
follows from the Schwarz-type three-zeros estimate
`Work.Analysis.ThreeZeros.three_zeros_bound_ball` applied to `N`, whose zeros at
`S•w − 1, S•w, S•w + 1` are `Tile.tileNum_strip_zeros`, together with the sharp divisor lower
bound `Tile.Sh_axis_lower_bound`: on the imaginary axis the three linear factors produced by the
three-zeros estimate cancel *exactly* against the two `Δ`-factors of `‖Sh‖ = ‖Δ(ζ)(j τ − j ζ)‖`.

The only point needing care is that the holomorphic representative `numFun` below agrees with
`2·Sh·(Kfun − Gfun)` *everywhere* on the disc: at the three coincidences `j τ = j ζ` inside the
disc (which lie at `S•w, S•w ± 1` by `SpikeCircle.jInvariantFun_eq_iff_disc`) both sides vanish.
-/

/-- `↑(ofComplex ζ) = ζ`. -/
private lemma ofComplex_coe (ζ : UpperHalfPlane) : UpperHalfPlane.ofComplex (ζ : ℂ) = ζ :=
  UpperHalfPlane.ext (Work.Asymptotics.Tile.ofComplex_coe_of_im_pos (ζ : ℂ) ζ.im_pos)

/-- `Re (S • w) = - Re w / ‖w‖²`, so `Re (S • w) = 0` forces `Re w = 0`. -/
private lemma re_S_smul_eq_zero (w : UpperHalfPlane) (h : (ModularGroup.S • w).re = 0) :
    w.re = 0 := by
  have hnorm : (0 : ℝ) < Complex.normSq (w : ℂ) := Complex.normSq_pos.mpr w.ne_zero
  have hcoe : ((ModularGroup.S • w : UpperHalfPlane) : ℂ) = -((w : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  have h2 : (ModularGroup.S • w).re = -w.re / Complex.normSq (w : ℂ) := by
    rw [← UpperHalfPlane.coe_re, hcoe, Complex.neg_re, Complex.inv_re,
      UpperHalfPlane.coe_re, neg_div]
  rw [h2] at h
  rcases div_eq_zero_iff.mp h with h' | h'
  · linarith
  · exact absurd h' (ne_of_gt hnorm)

/-- `Im z > 0` on the disc `‖z − σ‖ ≤ 29/20` when `Im σ ≥ 2`. -/
private lemma im_pos_of_disc {σ : UpperHalfPlane} (hσ : (2 : ℝ) ≤ σ.im) {z : ℂ}
    (hz : ‖z - (σ : ℂ)‖ ≤ 29 / 20) : 0 < z.im := by
  have h1 : |z.im - σ.im| ≤ ‖z - (σ : ℂ)‖ := by
    have h : (z - (σ : ℂ)).im = z.im - σ.im := by simp [UpperHalfPlane.coe_im]
    rw [← h]; exact Complex.abs_im_le_norm _
  have := (abs_le.mp (le_trans h1 hz)).1
  linarith

/-- The cleared numerator `N(ζ) = 2·Sh(τ,ζ)·(Kfun(τ,ζ) − Gfun(τ,ζ))`, in its manifestly
holomorphic form `−2·Δ(ζ)·AfunFun(τ,ζ) − 2·Sh(τ,ζ)·Gfun(τ,ζ)`, at the level of `ℍ`. -/
private def numH (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane)
    (ζ : UpperHalfPlane) : ℂ :=
  -2 * (Work.Kernels.DeltaFun ζ * AfunFun ℓ d τ ζ)
    - 2 * (Compact.Sh τ ζ * Compact.Gfun d ℓ τ ζ)

/-- The same function, as a function on the disc in `ℂ`. -/
private def numFun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) : ℂ → ℂ :=
  fun z => numH ℓ d τ (UpperHalfPlane.ofComplex z)

/-- `N` is holomorphic on the upper half plane. -/
private lemma numFun_differentiableOn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) :
    DifferentiableOn ℂ (numFun ℓ d τ) {z : ℂ | 0 < z.im} := by
  have hDelta : DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff (f := Work.Kernels.DeltaFun)).mp
      Work.Asymptotics.mdiff_DeltaFun
  have hE4 : DifferentiableOn ℂ
      (fun z : ℂ => Work.Kernels.E4Fun (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff (f := Work.Kernels.E4Fun)).mp
      Work.Asymptotics.mdiff_E4Fun
  have hAfun : DifferentiableOn ℂ
      (fun z : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff (f := fun z : UpperHalfPlane => AfunFun ℓ d τ z)).mp
      (Work.Asymptotics.mdifferentiable_AfunFun_snd ℓ d hd τ)
  have hSh : DifferentiableOn ℂ
      (fun z : ℂ => Compact.Sh τ (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} := by
    have h : (fun z : ℂ => Compact.Sh τ (UpperHalfPlane.ofComplex z))
        = fun z : ℂ => Work.Kernels.E4Fun (UpperHalfPlane.ofComplex z) ^ 3
            - Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex z)
                * Work.Kernels.jInvariantFun τ := by
      funext z; rw [Compact.Sh]
    rw [h]
    exact (hE4.pow 3).sub (hDelta.mul (differentiableOn_const _))
  have hG : DifferentiableOn ℂ
      (fun z : ℂ => Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
    Work.Asymptotics.Tile.differentiableOn_Gfun ℓ d τ
  have h : (fun z : ℂ => numH ℓ d τ (UpperHalfPlane.ofComplex z))
      = fun z : ℂ => (-2 : ℂ) * (Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex z)
              * AfunFun ℓ d τ (UpperHalfPlane.ofComplex z))
            + (-2 : ℂ) * (Compact.Sh τ (UpperHalfPlane.ofComplex z)
              * Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex z)) := by
    funext z; simp only [numH]; ring
  rw [show numFun ℓ d τ = fun z : ℂ => numH ℓ d τ (UpperHalfPlane.ofComplex z) from rfl, h]
  exact ((hDelta.mul hAfun).const_mul (-2)).add ((hSh.mul hG).const_mul (-2))

/-- The cleared identity `Sh τ ζ · Kfun τ ζ = −Δ(ζ)·AfunFun τ ζ` off the coincidence locus. -/
private lemma Sh_mul_Kfun_eq' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ ζ : UpperHalfPlane) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ) :
    Compact.Sh τ ζ * Work.Kernels.Kfun ℓ d τ ζ
      = -(Work.Kernels.DeltaFun ζ * AfunFun ℓ d τ ζ) := by
  have hdp : 1 ≤ Work.Residues.dpow d := by rcases hd with rfl | rfl <;> decide
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Work.Residues.dpow d = m + 1 :=
    ⟨Work.Residues.dpow d - 1, by omega⟩
  have hDτ : Work.Kernels.DeltaFun τ ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero τ
  have hDζ : Work.Kernels.DeltaFun ζ ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero ζ
  have hpe : Work.Kernels.DeltaFun ζ ^ (Work.Residues.dpow d - 1) * Work.Kernels.DeltaFun ζ
      = Work.Kernels.DeltaFun ζ ^ Work.Residues.dpow d := by
    rw [hm, Nat.add_sub_cancel, pow_succ]
  rw [Work.Asymptotics.Tile.Sh_mul_Kfun_eq ℓ d hd τ ζ h,
    Work.Asymptotics.KfunClear_eq_mul_AfunFun ℓ d τ ζ, ← hpe]
  field_simp

/-- `numH` is the `Kfun`-numerator, off the coincidence locus. -/
private lemma numH_eq_two_mul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ ζ : UpperHalfPlane) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ) :
    numH ℓ d τ ζ
      = 2 * (Compact.Sh τ ζ * (Work.Kernels.Kfun ℓ d τ ζ - Compact.Gfun d ℓ τ ζ)) := by
  have hk := Sh_mul_Kfun_eq' ℓ d hd τ ζ h
  simp only [numH, mul_sub, hk]
  ring

/-- `numFun` agrees with `2·Sh·(Kfun − Gfun)` off the coincidence locus. -/
private lemma numFun_eq_of_jne (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ ζ : UpperHalfPlane) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ) :
    numFun ℓ d τ (ζ : ℂ)
      = 2 * (Compact.Sh τ ζ * (Work.Kernels.Kfun ℓ d τ ζ - Compact.Gfun d ℓ τ ζ)) := by
  rw [show numFun ℓ d τ (ζ : ℂ)
        = numH ℓ d τ (UpperHalfPlane.ofComplex (ζ : ℂ)) from rfl, ofComplex_coe ζ]
  exact numH_eq_two_mul ℓ d hd τ ζ h

/-- `ofComplex (σ + k) = k +ᵥ σ` for an integer translate of a point of height `≥ 2`. -/
private lemma ofComplex_add_int (w : UpperHalfPlane) (k : ℤ) :
    UpperHalfPlane.ofComplex ((((ModularGroup.S • w : UpperHalfPlane) : ℂ) + (k : ℂ)))
      = (k : ℝ) +ᵥ (ModularGroup.S • w) := by
  apply UpperHalfPlane.ext
  rw [Work.Asymptotics.Tile.ofComplex_coe_of_im_pos _ (by
        have h1 : (ModularGroup.S • w).im
            ≤ (((ModularGroup.S • w : UpperHalfPlane) : ℂ) + (k : ℂ)).im := by
          rw [Complex.add_im, Complex.intCast_im, UpperHalfPlane.coe_im, add_zero]
        linarith [(ModularGroup.S • w).im_pos]),
    UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- The three resonant zeros of the cleared numerator. -/
private lemma numFun_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (w : UpperHalfPlane) (n : ℤ) (hn : n = 1 ∨ n = -1) (k : ℤ)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) :
    numFun ℓ d ((n : ℝ) +ᵥ w)
      (((ModularGroup.S • w : UpperHalfPlane) : ℂ) + (k : ℂ)) = 0 := by
  rw [show numFun ℓ d ((n : ℝ) +ᵥ w) (((ModularGroup.S • w : UpperHalfPlane) : ℂ) + (k : ℂ))
        = numH ℓ d ((n : ℝ) +ᵥ w)
            (UpperHalfPlane.ofComplex (((ModularGroup.S • w : UpperHalfPlane) : ℂ) + (k : ℂ)))
      from rfl, ofComplex_add_int w k, numH,
    Work.Asymptotics.Tile.AfunFun_strip_zeros ℓ d hd w n hn k hk,
    Work.Asymptotics.Tile.Sh_strip_zeros w n hn k hk]
  ring

/-- On the disc `‖z − S•w‖ ≤ 29/20` the cleared numerator is the `Kfun`-numerator. -/
private lemma numFun_eq_on_ball (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (w : UpperHalfPlane) (hw : w ∈ KEpsilon) (n : ℤ) (hn : n = 1 ∨ n = -1)
    {z : ℂ} (hz : ‖z - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20) :
    numFun ℓ d ((n : ℝ) +ᵥ w) z
      = 2 * (Compact.Sh ((n : ℝ) +ᵥ w) (UpperHalfPlane.ofComplex z)
          * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (UpperHalfPlane.ofComplex z)
              - Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (UpperHalfPlane.ofComplex z))) := by
  have hzim : 0 < z.im := im_pos_of_disc hw.2 hz
  by_cases hj : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
      = Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)
  · have hστ : Work.Kernels.jInvariantFun (ModularGroup.S • w)
        = Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) := by
      rw [Work.Kernels.KernelFacts.jInvariantFun_S_smul]
      rcases hn with h | h
      · subst h; push_cast
        exact (Work.Kernels.KernelFacts.jInvariantFun_vadd_one w).symm
      · subst h; push_cast
        have h1 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ w)
        rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w by rw [← add_vadd]; norm_num] at h1
        exact h1
    have hσζ : Work.Kernels.jInvariantFun (ModularGroup.S • w)
        = Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) := hστ.trans hj
    have hF : Work.Asymptotics.Funnel (ModularGroup.S • w) :=
      Work.Asymptotics.S_smul_mem_funnel hw
    have hball : ‖((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ)
        - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 := by
      rw [Work.Asymptotics.Tile.ofComplex_coe_of_im_pos z hzim]; exact hz
    have hk_ex : ∃ k : ℤ, (k = -1 ∨ k = 0 ∨ k = 1) ∧
        UpperHalfPlane.ofComplex z = (k : ℝ) +ᵥ (ModularGroup.S • w) := by
      rcases (Work.Asymptotics.SpikeCircle.jInvariantFun_eq_iff_disc hF hball).mp hσζ with
        h | h | h
      · exact ⟨0, Or.inr (Or.inl rfl), by rw [h]; simp⟩
      · exact ⟨1, Or.inr (Or.inr rfl), by simpa using h⟩
      · exact ⟨-1, Or.inl rfl, by simpa using h⟩
    obtain ⟨k, hk, hkζ⟩ := hk_ex
    have hzeq : z = (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) + (k : ℂ) := by
      have h := congrArg (fun u : UpperHalfPlane => (u : ℂ)) hkζ
      rw [Work.Asymptotics.Tile.ofComplex_coe_of_im_pos z hzim, UpperHalfPlane.coe_vadd] at h
      push_cast at h
      rw [h]; ring
    rw [hzeq, numFun_zero ℓ d hd w n hn k hk,
      show UpperHalfPlane.ofComplex ((((ModularGroup.S • w : UpperHalfPlane) : ℂ) + (k : ℂ)))
        = (k : ℝ) +ᵥ (ModularGroup.S • w) from ofComplex_add_int w k,
      Work.Asymptotics.Tile.Sh_strip_zeros w n hn k hk]
    ring
  · rw [show numFun ℓ d ((n : ℝ) +ᵥ w) z
          = numFun ℓ d ((n : ℝ) +ᵥ w) ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) from by
      rw [Work.Asymptotics.Tile.ofComplex_coe_of_im_pos z hzim]]
    exact numFun_eq_of_jne ℓ d hd ((n : ℝ) +ᵥ w) (UpperHalfPlane.ofComplex z) hj

/-- **The resonant strip bound from the ball bound on the cleared numerator.**

This is the reduction of the last open gate of the tile analysis: given the two-dimensional
bound for the cleared numerator `N(ζ) = 2·Sh(τ,ζ)·(Kfun(τ,ζ) − Gfun(τ,ζ))` on the disc
`‖ζ − S•w‖ ≤ 29/20` (the statement requested by many agents as `tileBallBound`,
`tileNumBall`, `tileBallBoundClean`, `tileBallBoundForStrip`, …), the resonant-strip estimate
`Tile.tileWindowRestricted_strip` follows. -/
theorem strip_of_ball (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hball : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ ζ : UpperHalfPlane,
          ‖(ζ : ℂ) - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 →
          ‖2 * (Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                  - Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
            ≤ C * (Work.Kernels.scale w) ^ N) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane), w ∈ KEpsilon → w.re ≠ 0 → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ t : ℝ, (ModularGroup.S • w).im - 1 ≤ t → t ≤ (ModularGroup.S • w).im + 1 →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  obtain ⟨Cb, Nb, hCb, hNb, hbb⟩ := hball
  obtain ⟨cs, hcs, hsh⟩ := Work.Asymptotics.Tile.Sh_axis_lower_bound
  have hδpos : (0 : ℝ) < (9 / 20 : ℝ) ^ 3 := by norm_num
  refine ⟨Cb * Real.exp (2 * Real.pi) / (2 * cs * (9 / 20 : ℝ) ^ 3) + 1, Nb, 0,
    by positivity, hNb, le_rfl, ?_⟩
  intro w hw hre n hn t ht1 ht2
  have ht : 0 < t := by have h2 := hw.2; linarith
  rw [axisAexp_eq ℓ d hd ((n : ℝ) +ᵥ w) t ht]
  obtain ⟨hσre1, hσre2⟩ :=
    Work.Asymptotics.re_bounds_of_mem_DomainD (Work.Asymptotics.S_smul_mem_DomainD hw.1)
  have hσim : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  have hIcr : ((t : ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  have hns : Complex.normSq ((t : ℂ) * Complex.I
      - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ))
      = (ModularGroup.S • w).re ^ 2 + (t - (ModularGroup.S • w).im) ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  have hb : (ModularGroup.S • w).re ^ 2 + (t - (ModularGroup.S • w).im) ^ 2 ≤ 2 := by
    have h3 : -1 ≤ t - (ModularGroup.S • w).im := by linarith
    have h4 : t - (ModularGroup.S • w).im ≤ 1 := by linarith
    nlinarith [hσre1, hσre2, h3, h4]
  have hzflt : ‖(t : ℂ) * Complex.I
      - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ < 29 / 20 := by
    have hsq : ‖(t : ℂ) * Complex.I - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ^ 2
        < (29 / 20 : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hns]
      nlinarith [hb, (by norm_num : (2 : ℝ) < (29 / 20) ^ 2)]
    nlinarith [hsq, norm_nonneg ((t : ℂ) * Complex.I
      - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ))]
  have hzfball : ‖(t : ℂ) * Complex.I
      - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 := le_of_lt hzflt
  have hdc : DiffContOnCl ℂ (numFun ℓ d ((n : ℝ) +ᵥ w))
      (Metric.ball (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) (29 / 20)) := by
    refine ⟨?_, ?_⟩
    · refine (numFun_differentiableOn ℓ d hd ((n : ℝ) +ᵥ w)).mono ?_
      intro z hz
      exact im_pos_of_disc hσim (le_of_lt (by rwa [Metric.mem_ball, dist_eq_norm] at hz))
    · refine ((numFun_differentiableOn ℓ d hd ((n : ℝ) +ᵥ w)).continuousOn).mono ?_
      intro z hz
      have h1 : z ∈ Metric.closedBall (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) (29 / 20) :=
        closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hz
      exact im_pos_of_disc hσim (by rwa [Metric.mem_closedBall, dist_eq_norm] at h1)
  have hbd : ∀ z ∈ Metric.ball (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) (29 / 20),
      ‖numFun ℓ d ((n : ℝ) +ᵥ w) z‖ ≤ Cb * (Work.Kernels.scale w) ^ Nb := by
    intro z hz
    have hzle : ‖z - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 :=
      le_of_lt (by rwa [Metric.mem_ball, dist_eq_norm] at hz)
    rw [numFun_eq_on_ball ℓ d hd w hw n hn hzle]
    exact hbb w hw n hn (UpperHalfPlane.ofComplex z) (by
      rw [Work.Asymptotics.Tile.ofComplex_coe_of_im_pos z (im_pos_of_disc hσim hzle)]
      exact hzle)
  have hMn : (0 : ℝ) ≤ Cb * (Work.Kernels.scale w) ^ Nb :=
    mul_nonneg hCb.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nb)
  set M : ℝ := Cb * (Work.Kernels.scale w) ^ Nb with hMdef
  set S0 : ℂ := (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) with hS0def
  set P : ℝ := ‖(t : ℂ) * Complex.I - S0‖ * ‖(t : ℂ) * Complex.I - (S0 - 1)‖
      * ‖(t : ℂ) * Complex.I - (S0 + 1)‖ with hPdef
  have hbound : ∀ z ∈ Metric.sphere S0 (29 / 20),
      (9 / 20 : ℝ) ^ 3 ≤ ‖z - S0‖ * ‖z - (S0 + 1)‖ * ‖z - (S0 - 1)‖ := by
    intro z hz
    have hz29 : ‖z - S0‖ = 29 / 20 := by rwa [Metric.mem_sphere, dist_eq_norm] at hz
    have h1 : (9 / 20 : ℝ) ≤ ‖z - (S0 + 1)‖ := by
      have h : z - (S0 + 1) = (z - S0) - 1 := by ring
      rw [h]
      have h2 : |‖z - S0‖ - ‖(1 : ℂ)‖| ≤ ‖(z - S0) - 1‖ := abs_norm_sub_norm_le _ _
      rw [norm_one, hz29] at h2
      have h3 : |(29 : ℝ) / 20 - 1| = 9 / 20 := by norm_num
      rwa [h3] at h2
    have h2 : (9 / 20 : ℝ) ≤ ‖z - (S0 - 1)‖ := by
      have h : z - (S0 - 1) = (z - S0) + 1 := by ring
      rw [h]
      have h3 : |‖z - S0‖ - ‖(-(1 : ℂ))‖| ≤ ‖(z - S0) - (-(1 : ℂ))‖ :=
        abs_norm_sub_norm_le _ _
      rw [norm_neg, norm_one, hz29] at h3
      have h4 : (z - S0) - (-(1 : ℂ)) = (z - S0) + 1 := by ring
      rw [h4] at h3
      have h5 : |(29 : ℝ) / 20 - 1| = 9 / 20 := by norm_num
      rwa [h5] at h3
    have h0 : (9 / 20 : ℝ) ≤ ‖z - S0‖ := by rw [hz29]; norm_num
    calc (9 / 20 : ℝ) ^ 3 = (9 / 20) * (9 / 20) * (9 / 20) := by ring
      _ ≤ ‖z - S0‖ * ‖z - (S0 + 1)‖ * ‖z - (S0 - 1)‖ := by
          gcongr
  have hne1 : S0 ≠ S0 + 1 := by
    intro h
    have h2 : (1 : ℂ) = 0 := by
      have h3 : (S0 + 1) - S0 = 0 := by rw [← h]; exact sub_self S0
      rw [show (S0 + 1) - S0 = (1 : ℂ) by ring] at h3
      exact h3
    exact one_ne_zero h2
  have hne2 : S0 ≠ S0 - 1 := by
    intro h
    have h2 : (1 : ℂ) = 0 := by
      have h3 : S0 - (S0 - 1) = 0 := by rw [← h]; exact sub_self S0
      rw [show S0 - (S0 - 1) = (1 : ℂ) by ring] at h3
      exact h3
    exact one_ne_zero h2
  have hne3 : S0 + 1 ≠ S0 - 1 := by
    intro h
    have h2 : (2 : ℂ) = 0 := by
      have h3 : (S0 + 1) - (S0 - 1) = 0 := by rw [h]; exact sub_self (S0 - 1)
      rw [show (S0 + 1) - (S0 - 1) = (2 : ℂ) by ring] at h3
      exact h3
    exact two_ne_zero h2
  have hzball : (t : ℂ) * Complex.I ∈ Metric.ball S0 (29 / 20) := by
    rw [Metric.mem_ball, dist_eq_norm, hS0def]
    exact hzflt
  have hz1 : numFun ℓ d ((n : ℝ) +ᵥ w) S0 = 0 := by
    rw [hS0def]
    have h := numFun_zero ℓ d hd w n hn 0 (Or.inr (Or.inl rfl))
    rw [show ((0 : ℤ) : ℂ) = 0 from by norm_num, add_zero] at h
    exact h
  have hz2 : numFun ℓ d ((n : ℝ) +ᵥ w) (S0 + 1) = 0 := by
    rw [hS0def]
    have h := numFun_zero ℓ d hd w n hn 1 (Or.inr (Or.inr rfl))
    rw [show ((1 : ℤ) : ℂ) = 1 from by norm_num] at h
    exact h
  have hz3 : numFun ℓ d ((n : ℝ) +ᵥ w) (S0 - 1) = 0 := by
    rw [hS0def]
    have h := numFun_zero ℓ d hd w n hn (-1) (Or.inl rfl)
    rw [show ((-1 : ℤ) : ℂ) = -1 from by norm_num, ← sub_eq_add_neg] at h
    exact h
  have hthree := Work.Analysis.ThreeZeros.three_zeros_bound_ball
    (f := numFun ℓ d ((n : ℝ) +ᵥ w))
    (c := S0) (ρ := 29 / 20) (M := M)
    (δ := (9 / 20 : ℝ) ^ 3) (z₁ := S0) (z₂ := S0 + 1) (z₃ := S0 - 1)
    (by norm_num) hMn hδpos hdc hbd hne1 hne2 hne3 hz1 hz2 hz3
    hbound ((t : ℂ) * Complex.I) hzball
  have hthree' : ‖numFun ℓ d ((n : ℝ) +ᵥ w) ((t : ℂ) * Complex.I)‖
      ≤ ((M / (9 / 20 : ℝ) ^ 3) * ‖(t : ℂ) * Complex.I - S0‖)
        * ‖(t : ℂ) * Complex.I - (S0 + 1)‖
        * ‖(t : ℂ) * Complex.I - (S0 - 1)‖ := hthree
  set Q : ℝ := ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
      - Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖ with hQdef
  set Sh : ℝ := ‖Compact.Sh ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖ with hShdef
  set E : ℝ := Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t)) with hEdef
  have hzf : UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) = Work.Kernels.imagAxis t ht := by
    have hzim2 : 0 < ((t : ℂ) * Complex.I).im := by
      rw [show (t : ℂ) * Complex.I = ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) from rfl]
      exact (Work.Kernels.imagAxis t ht).im_pos
    exact UpperHalfPlane.ext (Work.Asymptotics.Tile.ofComplex_coe_of_im_pos _ hzim2)
  have hzfball' : ‖(t : ℂ) * Complex.I
      - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 := by
    rw [← hS0def]; exact hzfball
  have hnf : numFun ℓ d ((n : ℝ) +ᵥ w) ((t : ℂ) * Complex.I)
      = 2 * (Compact.Sh ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
          * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
              - Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht))) := by
    rw [numFun_eq_on_ball ℓ d hd w hw n hn hzfball', hzf]
  have hPpos : 0 < P := by
    rw [hPdef]
    refine mul_pos (mul_pos (norm_pos_iff.mpr ?_) (norm_pos_iff.mpr ?_)) (norm_pos_iff.mpr ?_)
    · intro h
      have hh : (t : ℂ) * Complex.I = S0 := sub_eq_zero.mp h
      have h4 : ((t : ℂ) * Complex.I).re = (S0).re := by rw [hh]
      rw [hIcr] at h4
      rw [hS0def] at h4
      rw [UpperHalfPlane.coe_re] at h4
      exact hre (re_S_smul_eq_zero w h4.symm)
    · intro h
      have hh : (t : ℂ) * Complex.I = S0 - 1 := sub_eq_zero.mp h
      have h4 : ((t : ℂ) * Complex.I).re = (S0 - 1).re := by rw [hh]
      rw [hS0def] at h4
      rw [Complex.sub_re] at h4
      rw [Complex.one_re] at h4
      rw [UpperHalfPlane.coe_re] at h4
      rw [hIcr] at h4
      linarith [hσre2]
    · intro h
      have hh : (t : ℂ) * Complex.I = S0 + 1 := sub_eq_zero.mp h
      have h4 : ((t : ℂ) * Complex.I).re = (S0 + 1).re := by rw [hh]
      rw [hS0def] at h4
      rw [Complex.add_re] at h4
      rw [Complex.one_re] at h4
      rw [UpperHalfPlane.coe_re] at h4
      rw [hIcr] at h4
      linarith [hσre1]
  have hshb := hsh w hw n hn t ht ht1 ht2
  rw [norm_mul, norm_mul, ← hS0def] at hshb
  have hhsh : cs * (E * P) ≤ Sh := by
    rw [hShdef, hEdef, hPdef]
    exact hshb
  have hhthree : ‖numFun ℓ d ((n : ℝ) +ᵥ w) ((t : ℂ) * Complex.I)‖ ≤ (M / (9 / 20 : ℝ) ^ 3) * P := by
    calc ‖numFun ℓ d ((n : ℝ) +ᵥ w) ((t : ℂ) * Complex.I)‖
        ≤ ((M / (9 / 20 : ℝ) ^ 3) * ‖(t : ℂ) * Complex.I - S0‖)
          * ‖(t : ℂ) * Complex.I - (S0 + 1)‖
          * ‖(t : ℂ) * Complex.I - (S0 - 1)‖ := hthree'
      _ = (M / (9 / 20 : ℝ) ^ 3) * P := by rw [hPdef]; ring
  have hQSh : Q * (2 * Sh) = ‖numFun ℓ d ((n : ℝ) +ᵥ w) ((t : ℂ) * Complex.I)‖ := by
    rw [hQdef, hShdef, hnf, norm_mul, norm_mul, Complex.norm_ofNat]
    ring
  have hstep : Q * (2 * (cs * E)) ≤ M / (9 / 20 : ℝ) ^ 3 := by
    have h2sh : 2 * (cs * (E * P)) ≤ 2 * Sh := by linarith [hhsh]
    have hA : Q * (2 * (cs * (E * P))) ≤ ‖numFun ℓ d ((n : ℝ) +ᵥ w) ((t : ℂ) * Complex.I)‖ := by
      calc Q * (2 * (cs * (E * P))) ≤ Q * (2 * Sh) :=
            mul_le_mul_of_nonneg_left h2sh (by rw [hQdef]; exact norm_nonneg _)
        _ = _ := hQSh
    have hB : Q * (2 * (cs * (E * P))) ≤ (M / (9 / 20 : ℝ) ^ 3) * P := le_trans hA hhthree
    have hC : (Q * (2 * (cs * E))) * P ≤ (M / (9 / 20 : ℝ) ^ 3) * P := by
      calc (Q * (2 * (cs * E))) * P = Q * (2 * (cs * (E * P))) := by ring
        _ ≤ (M / (9 / 20 : ℝ) ^ 3) * P := hB
    exact le_of_mul_le_mul_right hC hPpos
  have hE1 : Real.exp (-(2 * Real.pi)) ≤ E := by
    rw [hEdef, Real.exp_le_exp]
    nlinarith [Real.pi_pos, ht2]
  have h4 : (Q * (2 * cs * (9 / 20 : ℝ) ^ 3)) * E ≤ M := by
    have h5 : (M / (9 / 20 : ℝ) ^ 3) * (9 / 20 : ℝ) ^ 3 = M := by field_simp
    calc (Q * (2 * cs * (9 / 20 : ℝ) ^ 3)) * E
        = Q * (2 * (cs * E)) * (9 / 20 : ℝ) ^ 3 := by ring
      _ ≤ (M / (9 / 20 : ℝ) ^ 3) * (9 / 20 : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hstep (by norm_num)
      _ = M := h5
  have h6 : Q * (2 * cs * (9 / 20 : ℝ) ^ 3) ≤ M * Real.exp (2 * Real.pi) := by
    have hX : (0 : ℝ) ≤ Q * (2 * cs * (9 / 20 : ℝ) ^ 3) :=
      mul_nonneg (by rw [hQdef]; exact norm_nonneg _) (by positivity)
    have h7 : (Q * (2 * cs * (9 / 20 : ℝ) ^ 3)) * Real.exp (-(2 * Real.pi)) ≤ M :=
      le_trans (mul_le_mul_of_nonneg_left hE1 hX) h4
    have h8 := mul_le_mul_of_nonneg_right h7 (Real.exp_pos (2 * Real.pi)).le
    rwa [mul_assoc, ← Real.exp_add, show -(2 * Real.pi) + 2 * Real.pi = 0 by ring,
      Real.exp_zero, mul_one] at h8
  have hcsδ : 0 < 2 * cs * (9 / 20 : ℝ) ^ 3 := by positivity
  have hQfinal : Q ≤ M * Real.exp (2 * Real.pi) / (2 * cs * (9 / 20 : ℝ) ^ 3) :=
    (le_div_iff₀ hcsδ).mpr h6
  rw [hQdef] at hQfinal ⊢
  rw [Real.rpow_zero, mul_one]
  refine le_trans hQfinal ?_
  rw [hMdef]
  have hs0 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ Nb :=
    Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nb
  calc (Cb * (Work.Kernels.scale w) ^ Nb) * Real.exp (2 * Real.pi)
        / (2 * cs * (9 / 20 : ℝ) ^ 3)
      = (Cb * Real.exp (2 * Real.pi) / (2 * cs * (9 / 20 : ℝ) ^ 3))
          * (Work.Kernels.scale w) ^ Nb := by ring
    _ ≤ (Cb * Real.exp (2 * Real.pi) / (2 * cs * (9 / 20 : ℝ) ^ 3) + 1)
          * (Work.Kernels.scale w) ^ Nb := by
        refine mul_le_mul_of_nonneg_right (by linarith) hs0

/-- **The below-pole window on the cusp-`±1` tiles at `Re w ≠ 0`** (the final form). -/
private theorem tileWindowRestricted' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon → w.re ≠ 0 →
        ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M :=
  tileWindowRestricted_of_pieces ℓ d hd (Tile.tileWindowFar ℓ d hd)
    (Tile.tileWindowRestricted_strip ℓ d hd)

/-! ## The `trunc` piece with the below-pole window restricted to `Re w ≠ 0`

This is `Work.Asymptotics.Tile.tile_amplitude_bound` and
`Work.Asymptotics.Tile.tileLayerTrunc_bound` with the unrestricted window hypothesis (which is
false on the bad line) replaced by the restricted one. -/

private lemma tile_amplitude_bound_restr (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hwin : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon → w.re ≠ 0 →
        ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M)
    (hsharp : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
        ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M
              * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))))
    (w : UpperHalfPlane) (n : ℤ) (hw : w ∈ KEpsilon) (hre : w.re ≠ 0)
    (hn : n = 1 ∨ n = -1) :
    ∃ Cg Mg : ℝ, 0 ≤ Cg ∧ 0 ≤ Mg ∧
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t)
        (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))) ∧
      (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))),
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ Cg * t ^ Mg * Real.exp (-(Real.pi * t))) := by
  obtain ⟨Cw, Nw, Mw, hCwpos, hNw, hMw, hwinb⟩ := hwin
  obtain ⟨Cs, Ns, Ms, hCspos, hNs, hMs, hsharpb⟩ := hsharp
  set h : ℝ → ℂ := fun t =>
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
      - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t with hhdef
  have hmeas : MeasureTheory.AEStronglyMeasurable h
      (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))) := by
    rw [hhdef]
    have h1 : Measurable (fun t : ℝ =>
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t) :=
      measurable_Kaxis_Kfun ℓ d hd _
    have h2 : Measurable (fun t : ℝ =>
        Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t) := by
      unfold Aexp; fun_prop
    exact (h1.sub h2).aestronglyMeasurable
  have hB1 : (1 : ℝ) ≤ 2 * (ModularGroup.S • w).im + 1 := by linarith [hw.2]
  have hD1 : 0 ≤ Cw * (Work.Kernels.scale w) ^ Nw :=
    mul_nonneg hCwpos.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nw)
  have hD2 : 0 ≤ Cs * (Work.Kernels.scale w) ^ Ns * Real.exp (Real.pi * (ModularGroup.S • w).im) :=
    mul_nonneg (mul_nonneg hCspos.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Ns))
      (Real.exp_pos _).le
  have hb1 : ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
      ‖h t‖ ≤ (Cw * (Work.Kernels.scale w) ^ Nw) * (1 + t) ^ Mw := by
    intro t ht1 ht2
    have h1 : ‖h t‖ ≤ Cw * (Work.Kernels.scale w) ^ Nw * t ^ Mw := by
      rw [hhdef]; exact hwinb w n hn hw hre t ht1 ht2
    have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
    have h2 : t ^ Mw ≤ (1 + t) ^ Mw := Real.rpow_le_rpow ht0 (by linarith) hMw
    calc ‖h t‖ ≤ Cw * (Work.Kernels.scale w) ^ Nw * t ^ Mw := h1
      _ ≤ Cw * (Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCwpos.le
            (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nw))
  have hb2 : ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
      ‖h t‖ ≤ (Cs * (Work.Kernels.scale w) ^ Ns * Real.exp (Real.pi * (ModularGroup.S • w).im))
          * t ^ Ms * Real.exp (-(Real.pi * t)) := by
    intro t ht
    have h1 : ‖h t‖ ≤ Cs * (Work.Kernels.scale w) ^ Ns * t ^ Ms
        * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := by
      rw [hhdef]; exact hsharpb w n hn hw t ht
    have hexp : Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
        = Real.exp (Real.pi * (ModularGroup.S • w).im) * Real.exp (-(Real.pi * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖h t‖ ≤ Cs * (Work.Kernels.scale w) ^ Ns * t ^ Ms
          * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := h1
      _ = (Cs * (Work.Kernels.scale w) ^ Ns * Real.exp (Real.pi * (ModularGroup.S • w).im))
            * t ^ Ms * Real.exp (-(Real.pi * t)) := by
          rw [hexp]; ring
  obtain ⟨Cg, Mg, hCg, hMg, hglob⟩ :=
    ae_bound_of_two_regime h hB1 hD1 hD2 hMw hMs hb1 hb2
  refine ⟨Cg, Mg, hCg, hMg, hmeas, ?_⟩
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
  exact hglob t (Set.mem_Ici.mp ht)

private theorem tileLayerTrunc_bound_restr (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hwin : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon → w.re ≠ 0 →
        ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M)
    (hsharp : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
        ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M
              * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      (∀ (w : UpperHalfPlane) (n : ℤ), w ∈ KEpsilon → w.re ≠ 0 → (n = 1 ∨ n = -1) →
        ContDiff ℝ ⊤ (fun s : ℝ =>
          layerTrunc (Gcusp ℓ d) ℓ d ((n : ℝ) +ᵥ w) s)) ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), w ∈ KEpsilon → w.re ≠ 0 → (n = 1 ∨ n = -1) →
        ∀ r : ℝ, (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          layerTrunc (Gcusp ℓ d) ℓ d ((n : ℝ) +ᵥ w) s) r‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  intro k l
  have hwin_c := hwin
  have hsharp_c := hsharp
  obtain ⟨Cw, Nw, Mw, hCwpos, hNw, hMw, hwinb⟩ := hwin_c
  obtain ⟨Cs, Ns, Ms, hCspos, hNs, hMs, hsharpb⟩ := hsharp_c
  obtain ⟨ct, Nt, hct, hNt, htail⟩ :=
    Tile.exists_bound_iteratedDeriv_tailIntegral_shift l Cw Nw Mw Cs Ns Ms
      hCwpos.le hNw hMw hCspos.le hNs hMs
  obtain ⟨cc, hcc, hcomp⟩ := exists_seminorm_bound_of_iteratedDeriv_bound k l
  refine ⟨cc * ct, Nt, mul_nonneg hcc hct, hNt, ?_, ?_⟩
  · intro w n hw hre hn
    obtain ⟨Cg, Mg, hCg, hMg, hmeas, hbglob⟩ :=
      tile_amplitude_bound_restr ℓ d hd hwin hsharp w n hw hre hn
    set g : ℝ → ℂ := fun t =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
        - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t with hgdef
    have hcont : ContDiffOn ℝ ⊤ (tailIntegral g) (Set.Ioi (-1)) :=
      contDiffOn_real_tailIntegral g hmeas hCg hMg hbglob
    have hsq : ContDiff ℝ ⊤ (fun r : ℝ => r ^ 2) := contDiff_id.pow 2
    have hcomp2 : ContDiffOn ℝ ⊤ (fun r : ℝ => tailIntegral g (r ^ 2)) Set.univ :=
      hcont.comp hsq.contDiffOn (fun r _ => by
        simp only [Set.mem_Ioi]; linarith [sq_nonneg r])
    have htr : ContDiff ℝ ⊤ (fun r : ℝ => tailIntegral g (r ^ 2)) :=
      contDiffOn_univ.mp hcomp2
    have hcos : ContDiff ℝ ⊤ (fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ)) := by
      have h1 : ContDiff ℝ ⊤ (fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℝ)) := by
        fun_prop
      have h2 : ContDiff ℝ ⊤ (fun r : ℝ => ((2 - 2 * Real.cos (Real.pi * r ^ 2) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp h1
      simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat] using h2
    have hfun : (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((n : ℝ) +ᵥ w) s)
        = fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ)
            * tailIntegral g (r ^ 2) := by
      funext r
      rw [layerTrunc_eq_tailIntegral, hgdef]
    rw [hfun]
    exact hcos.mul htr
  · intro w n hw hre hn r
    obtain ⟨Cg, Mg, hCg, hMg, hmeas, hbglob⟩ :=
      tile_amplitude_bound_restr ℓ d hd hwin hsharp w n hw hre hn
    set g : ℝ → ℂ := fun t =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
        - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t with hgdef
    have hA1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hT0 : (0 : ℝ) ≤ (ModularGroup.S • w).im := by linarith [hw.2]
    have hTA : (ModularGroup.S • w).im ≤ Work.Kernels.scale w := Tile.im_S_smul_le_scale w
    have hwinG : ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖g t‖ ≤ Cw * (Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw := by
      intro t ht1 ht2
      have h1 : ‖g t‖ ≤ Cw * (Work.Kernels.scale w) ^ Nw * t ^ Mw := by
        rw [hgdef]; exact hwinb w n hn hw hre t ht1 ht2
      have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
      have h2 : t ^ Mw ≤ (1 + t) ^ Mw := Real.rpow_le_rpow ht0 (by linarith) hMw
      calc ‖g t‖ ≤ Cw * (Work.Kernels.scale w) ^ Nw * t ^ Mw := h1
        _ ≤ Cw * (Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hCwpos.le
              (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nw))
    have hsharpG : ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
        ‖g t‖ ≤ Cs * (Work.Kernels.scale w) ^ Ns * t ^ Ms
            * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := by
      intro t ht
      rw [hgdef]; exact hsharpb w n hn hw t ht
    have hFdiff : ContDiffOn ℝ (l : WithTop ℕ∞) (tailIntegral g) (Set.Ioi (-1)) :=
      tailIntegral_contDiffOn l g hmeas hCg hMg hbglob
    have hbound : ∀ m : ℕ, m ≤ l → ∀ x : ℝ, 0 ≤ x →
        ‖iteratedDeriv m (tailIntegral g) x‖
          ≤ (ct * (Work.Kernels.scale w) ^ Nt) * Real.exp (-(Real.pi * x)) :=
      fun m hm x hx => htail g (Work.Kernels.scale w) ((ModularGroup.S • w).im) Cg Mg
        hA1 hT0 hTA hCg hMg hmeas hbglob hwinG hsharpG m hm x hx
    have hmain := hcomp (tailIntegral g) (ct * (Work.Kernels.scale w) ^ Nt)
      (by positivity) hFdiff hbound r
    have hfun : (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((n : ℝ) +ᵥ w) s)
        = fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
            * tailIntegral g (s ^ 2) := by
      funext s
      rw [layerTrunc_eq_tailIntegral, hgdef]
    rw [hfun]
    calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
          * tailIntegral g (s ^ 2)) r‖
        ≤ cc * (ct * (Work.Kernels.scale w) ^ Nt) := hmain
      _ = (cc * ct) * (Work.Kernels.scale w) ^ Nt := by ring

/-! ## Evenness of the three pieces of the layer -/

private lemma sinSq_neg_loc (r : ℝ) : sinSq (-r) = sinSq r := by
  have hsq : (((-r : ℝ)) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [sinSq, hsq]

private lemma layerLow_neg_loc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane)
    (s : ℝ) : layerLow ℓ d τ (-s) = layerLow ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [layerLow, sinSq, hsq]

private lemma layerTrunc_neg_loc (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    layerTrunc G ℓ d τ (-s) = layerTrunc G ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [layerTrunc, sinSq, hsq]

private lemma highPart_neg_loc (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane)
    (s : ℝ) : highPart G τ (-s) = highPart G τ s := by
  simp only [highPart, neg_sq]

private lemma paperLayer_neg_loc (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    paperLayer G ℓ d τ (-s) = paperLayer G ℓ d τ s := by
  simp only [paperLayer]
  rw [layerLow_neg_loc, layerTrunc_neg_loc, highPart_neg_loc]

/-! ## The `high` piece of the layer on the tile

The `high` part is an explicit linear combination of the four cusp coefficients
`Gcusp ℓ d i j`, so its seminorms are bounded on the tile by `Work.Asymptotics.Gcusp_tile_bound`.
This is the tile version of `Work.Asymptotics.highPart_seminorm`, with the moderate growth on `𝒟`
replaced by the tile bound (the tile point `1 +ᵥ w` is not in `𝒟`). -/

lemma highPart_tile_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ KEpsilon → ∀ r : ℝ,
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) r‖ ≤ c * (Work.Kernels.scale w) ^ N := by
  intro k l
  obtain ⟨C, N, hC, hN, hb⟩ := Gcusp_tile_bound ℓ d hd
  obtain ⟨A0, hA0, hbA0⟩ := highAmp0_grow (l + 1)
  obtain ⟨A1, hA1, hbA1⟩ := highAmp1_grow (l + 1)
  obtain ⟨B0, hB0, hbB0⟩ := seminorm_highFac highAmp0 0 k l A0 1 hA0 highAmp0_contDiff hbA0
  obtain ⟨B1, hB1, hbB1⟩ := seminorm_highFac highAmp1 0 k l A1 1 hA1 highAmp1_contDiff hbA1
  obtain ⟨B2, hB2, hbB2⟩ :=
    seminorm_highFac highAmp0 (2 * Real.pi) k l A0 1 hA0 highAmp0_contDiff hbA0
  obtain ⟨B3, hB3, hbB3⟩ :=
    seminorm_highFac highAmp1 (2 * Real.pi) k l A1 1 hA1 highAmp1_contDiff hbA1
  set E : ℝ := Real.exp (2 * Real.pi) with hE
  have hE0 : 0 ≤ E := Real.exp_nonneg _
  have hc0 : (0 : ℝ) ≤ C * B0 + C * B1 + E * C * B2 + E * C * B3 := by positivity
  refine ⟨C * B0 + C * B1 + E * C * B2 + E * C * B3, N, hc0, hN, ?_⟩
  intro w hw r
  have hS1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hc : ∀ i j : Fin 2, ‖Gcusp ℓ d i j ((1 : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N :=
    fun i j => by
      have h := hb w 1 (Or.inl rfl) hw i j
      simpa using h
  have hcI0 : ‖Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N := by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact hc 0 1
  have hcE1 : ‖Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w)‖
      ≤ (E * C) * (Work.Kernels.scale w) ^ N := by
    rw [norm_mul, Complex.norm_exp_ofReal]
    calc Real.exp (2 * Real.pi) * ‖Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w)‖
        = E * ‖Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w)‖ := by rw [hE]
      _ ≤ E * (C * (Work.Kernels.scale w) ^ N) := mul_le_mul_of_nonneg_left (hc 1 0) hE0
      _ = (E * C) * (Work.Kernels.scale w) ^ N := by ring
  have hcE2 : ‖Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w))‖
      ≤ (E * C) * (Work.Kernels.scale w) ^ N := by
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal, Complex.norm_I, one_mul]
    calc Real.exp (2 * Real.pi) * ‖Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w)‖
        = E * ‖Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w)‖ := by rw [hE]
      _ ≤ E * (C * (Work.Kernels.scale w) ^ N) := mul_le_mul_of_nonneg_left (hc 1 1) hE0
      _ = (E * C) * (Work.Kernels.scale w) ^ N := by ring
  have hfun : (fun s : ℝ => highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s)
      = fun s : ℝ => Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w) * highFac highAmp0 0 s
          + (Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w)) * highFac highAmp1 0 s
          + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w))
              * highFac highAmp0 (2 * Real.pi) s
          + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w)))
              * highFac highAmp1 (2 * Real.pi) s :=
    funext fun s => highPart_decomp (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s
  have hcd0 : ContDiffAt ℝ (↑l) (highFac highAmp0 0) r :=
    (highFac_contDiff highAmp0 0 highAmp0_contDiff).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hcd1 : ContDiffAt ℝ (↑l) (highFac highAmp1 0) r :=
    (highFac_contDiff highAmp1 0 highAmp1_contDiff).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hcd2 : ContDiffAt ℝ (↑l) (highFac highAmp0 (2 * Real.pi)) r :=
    (highFac_contDiff highAmp0 (2 * Real.pi) highAmp0_contDiff).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hcd3 : ContDiffAt ℝ (↑l) (highFac highAmp1 (2 * Real.pi)) r :=
    (highFac_contDiff highAmp1 (2 * Real.pi) highAmp1_contDiff).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  rw [hfun, iteratedDeriv_four (Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w))
    (Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w))
    (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w))
    (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w)))
    (highFac highAmp0 0) (highFac highAmp1 0) (highFac highAmp0 (2 * Real.pi))
    (highFac highAmp1 (2 * Real.pi)) l r hcd0 hcd1 hcd2 hcd3]
  have e0 := hbB0 r
  have e1 := hbB1 r
  have e2 := hbB2 r
  have e3 := hbB3 r
  have hbnd0 : |r| ^ k * ‖(Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w))
        * iteratedDeriv l (highFac highAmp0 0) r‖ ≤ C * B0 * (Work.Kernels.scale w) ^ N := by
    rw [norm_mul]
    calc |r| ^ k * (‖Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w)‖ * ‖iteratedDeriv l (highFac highAmp0 0) r‖)
        = ‖Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w)‖ * (|r| ^ k * ‖iteratedDeriv l (highFac highAmp0 0) r‖) :=
          by ring
      _ ≤ (C * (Work.Kernels.scale w) ^ N) * B0 :=
          mul_le_mul (hc 0 0) e0 (by positivity) (by positivity)
      _ = C * B0 * (Work.Kernels.scale w) ^ N := by ring
  have hbnd1 : |r| ^ k * ‖(Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w))
        * iteratedDeriv l (highFac highAmp1 0) r‖ ≤ C * B1 * (Work.Kernels.scale w) ^ N := by
    rw [norm_mul]
    calc |r| ^ k * (‖Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w)‖
          * ‖iteratedDeriv l (highFac highAmp1 0) r‖)
        = ‖Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w)‖
          * (|r| ^ k * ‖iteratedDeriv l (highFac highAmp1 0) r‖) := by ring
      _ ≤ (C * (Work.Kernels.scale w) ^ N) * B1 :=
          mul_le_mul hcI0 e1 (by positivity) (by positivity)
      _ = C * B1 * (Work.Kernels.scale w) ^ N := by ring
  have hbnd2 : |r| ^ k * ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w))
        * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r‖
      ≤ E * C * B2 * (Work.Kernels.scale w) ^ N := by
    rw [norm_mul]
    calc |r| ^ k * (‖Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w)‖
          * ‖iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r‖)
        = ‖Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w)‖
          * (|r| ^ k * ‖iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r‖) := by ring
      _ ≤ (E * C * (Work.Kernels.scale w) ^ N) * B2 :=
          mul_le_mul hcE1 e2 (by positivity) (by positivity)
      _ = E * C * B2 * (Work.Kernels.scale w) ^ N := by ring
  have hbnd3 : |r| ^ k * ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ)
        * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w)))
        * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖
      ≤ E * C * B3 * (Work.Kernels.scale w) ^ N := by
    rw [norm_mul]
    calc |r| ^ k * (‖Complex.exp ((2 * Real.pi : ℝ) : ℂ)
            * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w))‖
          * ‖iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖)
        = ‖Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w))‖
          * (|r| ^ k * ‖iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖) := by ring
      _ ≤ (E * C * (Work.Kernels.scale w) ^ N) * B3 :=
          mul_le_mul hcE2 e3 (by positivity) (by positivity)
      _ = E * C * B3 * (Work.Kernels.scale w) ^ N := by ring
  have htri : ‖Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w) * iteratedDeriv l (highFac highAmp0 0) r
        + (Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w)) * iteratedDeriv l (highFac highAmp1 0) r
        + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w))
            * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r
        + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w)))
            * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖
      ≤ ‖Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w) * iteratedDeriv l (highFac highAmp0 0) r‖
        + ‖(Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w)) * iteratedDeriv l (highFac highAmp1 0) r‖
        + ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w))
            * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r‖
        + ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w)))
            * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖ := by
    have h1 := norm_add_le (Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w) * iteratedDeriv l (highFac highAmp0 0) r
        + (Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w)) * iteratedDeriv l (highFac highAmp1 0) r
        + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w))
            * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r)
      ((Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w)))
            * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r)
    have h2 := norm_add_le (Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w) * iteratedDeriv l (highFac highAmp0 0) r
        + (Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w)) * iteratedDeriv l (highFac highAmp1 0) r)
      ((Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w))
            * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r)
    have h3 := norm_add_le (Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w) * iteratedDeriv l (highFac highAmp0 0) r)
      ((Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w)) * iteratedDeriv l (highFac highAmp1 0) r)
    linarith
  calc |r| ^ k * ‖Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w) * iteratedDeriv l (highFac highAmp0 0) r
          + (Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w)) * iteratedDeriv l (highFac highAmp1 0) r
          + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w))
              * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r
          + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w)))
              * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖
      ≤ |r| ^ k * (‖Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w) * iteratedDeriv l (highFac highAmp0 0) r‖
          + ‖(Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w))
              * iteratedDeriv l (highFac highAmp1 0) r‖
          + ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w))
              * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r‖
          + ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w)))
              * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ = |r| ^ k * ‖Gcusp ℓ d 0 0 ((1 : ℝ) +ᵥ w) * iteratedDeriv l (highFac highAmp0 0) r‖
          + |r| ^ k * ‖(Complex.I * Gcusp ℓ d 0 1 ((1 : ℝ) +ᵥ w))
              * iteratedDeriv l (highFac highAmp1 0) r‖
          + |r| ^ k * ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * Gcusp ℓ d 1 0 ((1 : ℝ) +ᵥ w))
              * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r‖
          + |r| ^ k * ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ)
              * (Complex.I * Gcusp ℓ d 1 1 ((1 : ℝ) +ᵥ w)))
              * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖ := by ring
    _ ≤ C * B0 * (Work.Kernels.scale w) ^ N
          + C * B1 * (Work.Kernels.scale w) ^ N
          + E * C * B2 * (Work.Kernels.scale w) ^ N
          + E * C * B3 * (Work.Kernels.scale w) ^ N :=
        add_le_add (add_le_add (add_le_add hbnd0 hbnd1) hbnd2) hbnd3
    _ = (C * B0 + C * B1 + E * C * B2 + E * C * B3) * (Work.Kernels.scale w) ^ N := by ring

/-! ## Smoothness of the `low` piece at the tile point `1 +ᵥ w` -/

lemma tileLayerLow_contDiff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (w : UpperHalfPlane) (hw : w ∈ KEpsilon) (hre : w.re ≠ 0) :
    ContDiff ℝ ω (fun r : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) r) := by
  obtain ⟨Cw, Nw, hCw, hNw, hwin⟩ := Tile.tilePPWindow_bound ℓ d hd
  obtain ⟨cF, NF, hcF, hNF, hflatF⟩ := Kaxis_tile_flat_below_pole ℓ d hd 0 le_rfl
  have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hscale0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hyhalf : w.im ≤ 1 / 2 := tile_im_le_half hw
  have hy21 : w.im / 2 ≤ 1 := by linarith [w.im_pos]
  have hre_abs : (0 : ℝ) < |w.re| := abs_pos.mpr hre
  set B : ℝ := cF * (Work.Kernels.scale w) ^ NF + Cw * (Work.Kernels.scale w) ^ Nw
    + (1 / (2 * Real.pi)) * (1 / |w.re|) with hBdef
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hBdef]
    have h1 : (0 : ℝ) ≤ cF * (Work.Kernels.scale w) ^ NF :=
      mul_nonneg hcF (Real.rpow_nonneg hscale0.le _)
    have h2 : (0 : ℝ) ≤ Cw * (Work.Kernels.scale w) ^ Nw :=
      mul_nonneg hCw (Real.rpow_nonneg hscale0.le _)
    have h3 : (0 : ℝ) ≤ (1 / (2 * Real.pi)) * (1 / |w.re|) :=
      mul_nonneg (by positivity) (by positivity)
    linarith
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Work.Kernels.Kaxis
      (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) t) (MeasureTheory.volume.restrict (Set.Ioc 0 1)) :=
    (measurable_Kaxis_Kfun ℓ d hd _).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc 0 1)),
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) t‖ ≤ B := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    rcases le_or_gt t (w.im / 2) with hc | hc
    · have hmin : min 1 (w.im / 2) = w.im / 2 := min_eq_right hy21
      have h := hflatF w 1 (Or.inl rfl) hw t ht0 (by rw [hmin]; exact hc)
      simp only [Real.rpow_zero, mul_one, Int.cast_one] at h
      have h1 : (0 : ℝ) ≤ cF * (Work.Kernels.scale w) ^ NF :=
        mul_nonneg hcF (Real.rpow_nonneg hscale0.le _)
      have h2 : (0 : ℝ) ≤ Cw * (Work.Kernels.scale w) ^ Nw :=
        mul_nonneg hCw (Real.rpow_nonneg hscale0.le _)
      have h3 : (0 : ℝ) ≤ (1 / (2 * Real.pi)) * (1 / |w.re|) :=
        mul_nonneg (by positivity) (by positivity)
      rw [hBdef]
      linarith
    · have hw1 := hwin w hw 1 (Or.inl rfl) t (le_of_lt hc) ht1
      have hw1' : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) t
          - ((1 : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
          ≤ Cw * (Work.Kernels.scale w) ^ Nw := by
        simpa using hw1
      have hPP : ‖((1 : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
          ≤ (1 / (2 * Real.pi)) * (1 / |w.re|) := by
        have hden : |w.re| ≤ ‖(t : ℂ) * Complex.I - (w : ℂ)‖ := by
          have h := Complex.abs_re_le_norm ((t : ℂ) * Complex.I - (w : ℂ))
          have h2 : ((t : ℂ) * Complex.I - (w : ℂ)).re = -w.re := by
            simp [Complex.sub_re, Complex.mul_re]
          rw [h2, abs_neg] at h
          exact h
        rw [norm_mul]
        have hcn : ‖((1 : ℂ) / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
          have h2pi : ‖((2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
            rw [Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          rw [norm_div, norm_one,
            show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, h2pi]
        rw [hcn]
        have hle : ‖(((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖ ≤ 1 / |w.re| := by
          rw [norm_inv, one_div]
          exact (inv_le_inv₀ (lt_of_lt_of_le hre_abs hden) hre_abs).mpr hden
        exact mul_le_mul_of_nonneg_left hle (by positivity)
      have hsub : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) t‖
          ≤ Cw * (Work.Kernels.scale w) ^ Nw
            + (1 / (2 * Real.pi)) * (1 / |w.re|) := by
        have heq : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) t
            = (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) t
                - ((1 : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹))
              + ((1 : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹) := by ring
        rw [heq]
        exact le_trans (norm_add_le _ _) (add_le_add hw1' hPP)
      have h1 : (0 : ℝ) ≤ cF * (Work.Kernels.scale w) ^ NF :=
        mul_nonneg hcF (Real.rpow_nonneg hscale0.le _)
      rw [hBdef]
      linarith
  have hmain := contDiff_omega_intervalIntegral_exp (κ := fun t : ℝ =>
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) t) hB0 hmeas hbound
  simpa only [layerLow] using contDiff_omega_sinSq.mul hmain

/-! ## The assembly -/

theorem tileLayerSeminormTS (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    Work.Asymptotics.TileLayerSeminorm ℓ d := by
  intro k l
  obtain ⟨C1, N1, hC1, hN1, h1⟩ :=
    Tile.layerLow_tile_seminorm ℓ d hd (Tile.tilePPWindow_bound ℓ d hd) k l
  obtain ⟨C2, N2, hC2, hN2, h2cont, h2⟩ :=
    tileLayerTrunc_bound_restr ℓ d hd (tileWindowRestricted' ℓ d hd)
      (Tile.tileSharpTail ℓ d hd) k l
  obtain ⟨C3, N3, hC3, hN3, h3⟩ := highPart_tile_seminorm ℓ d hd k l
  refine ⟨C1 + C2 + C3, max N1 (max N2 N3), by linarith, le_trans hN1 (le_max_left _ _), ?_⟩
  intro w hw hre r
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale w := (Work.Kernels.scale_pos w).le
  have hN1' : N1 ≤ max N1 (max N2 N3) := le_max_left _ _
  have hN2' : N2 ≤ max N1 (max N2 N3) := le_trans (le_max_left N2 N3) (le_max_right N1 _)
  have hN3' : N3 ≤ max N1 (max N2 N3) := le_trans (le_max_right N2 N3) (le_max_right N1 _)
  have b1 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) r‖
      ≤ C1 * (Work.Kernels.scale w) ^ (max N1 (max N2 N3)) := by
    have h := h1 w hw hre 1 (Or.inl rfl) r
    simp only [Int.cast_one] at h
    exact le_trans h (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hs1 hN1') hC1)
  have b2 : (|r| ^ k) * ‖iteratedDeriv l
      (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r‖
      ≤ C2 * (Work.Kernels.scale w) ^ (max N1 (max N2 N3)) := by
    have h := h2 w 1 hw hre (Or.inl rfl) r
    simp only [Int.cast_one] at h
    exact le_trans h (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hs1 hN2') hC2)
  have b3 : (|r| ^ k) * ‖iteratedDeriv l
      (fun s : ℝ => highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
      ≤ C3 * (Work.Kernels.scale w) ^ (max N1 (max N2 N3)) := by
    exact le_trans (h3 w hw r) (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hs1 hN3') hC3)
  have hsm_low : ContDiff ℝ ω (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) :=
    tileLayerLow_contDiff ℓ d hd w hw hre
  have hsm_tr : ContDiff ℝ ω (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) := by
    have h := h2cont w 1 hw hre (Or.inl rfl)
    simpa only [Int.cast_one] using h
  have hsm_hi : ContDiff ℝ ω (fun s : ℝ => highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) :=
    contDiff_omega_highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w)
  have hsm_pl : ContDiff ℝ ω (fun s : ℝ =>
      paperLayer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) := by
    have hfun : (fun s : ℝ => paperLayer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s)
        = (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s)
          + (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s)
          + (fun s : ℝ => highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) := by
      funext s; simp only [paperLayer, Pi.add_apply]
    rw [hfun]
    exact (hsm_low.add hsm_tr).add hsm_hi
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    simp only [iteratedDeriv_zero] at b1 b2 b3
    simp only [iteratedDeriv_zero]
    rcases eq_or_ne r 0 with hr | hr
    · subst hr
      have hz : layer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) 0 = 0 := by rw [layer]; simp
      rw [hz, norm_zero, mul_zero]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)
    · have hL : layer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) r
          = paperLayer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) r := by rw [layer, if_neg hr]
      rw [hL, paperLayer]
      have htri : ‖layerLow ℓ d ((1 : ℝ) +ᵥ w) r
            + layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) r
            + highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) r‖
          ≤ ‖layerLow ℓ d ((1 : ℝ) +ᵥ w) r‖
            + ‖layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) r‖
            + ‖highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) r‖ := by
        have h2' := norm_add_le (layerLow ℓ d ((1 : ℝ) +ᵥ w) r
            + layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) r)
          (highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) r)
        have h1' := norm_add_le (layerLow ℓ d ((1 : ℝ) +ᵥ w) r)
          (layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) r)
        linarith
      calc (|r| ^ k) * ‖layerLow ℓ d ((1 : ℝ) +ᵥ w) r
            + layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) r
            + highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) r‖
          ≤ (|r| ^ k) * (‖layerLow ℓ d ((1 : ℝ) +ᵥ w) r‖
              + ‖layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) r‖
              + ‖highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) r‖) :=
            mul_le_mul_of_nonneg_left htri (by positivity)
        _ = (|r| ^ k) * ‖layerLow ℓ d ((1 : ℝ) +ᵥ w) r‖
              + (|r| ^ k) * ‖layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) r‖
              + (|r| ^ k) * ‖highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) r‖ := by ring
        _ ≤ C1 * (Work.Kernels.scale w) ^ (max N1 (max N2 N3))
              + C2 * (Work.Kernels.scale w) ^ (max N1 (max N2 N3))
              + C3 * (Work.Kernels.scale w) ^ (max N1 (max N2 N3)) := by
            linarith [b1, b2, b3]
        _ = (C1 + C2 + C3) * (Work.Kernels.scale w) ^ (max N1 (max N2 N3)) := by ring
  · have hl1 : 1 ≤ l := hl
    have hpunct : iteratedDeriv l (fun s : ℝ => layer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s)
        = iteratedDeriv l (fun s : ℝ => paperLayer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) := by
      have heven : ∀ s : ℝ, paperLayer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) (-s)
          = paperLayer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s :=
        fun s => paperLayer_neg_loc (Gcusp ℓ d) ℓ d _ s
      have hdiff : Differentiable ℝ (fun s : ℝ =>
          paperLayer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) :=
        (hsm_pl.differentiable (by simp))
      have h := punctured_iteratedDeriv heven hdiff l hl1
      have hfun : (fun s : ℝ => layer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s)
          = fun s : ℝ => if s = 0 then 0 else paperLayer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s := by
        funext s; rw [layer]
      rw [hfun, h]
    have hlow_at : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) r :=
      (hsm_low.contDiffAt (x := r)).of_le le_top
    have htr_at : ContDiffAt ℝ (l : ℕ∞)
        (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r :=
      (hsm_tr.contDiffAt (x := r)).of_le le_top
    have hhi_at : ContDiffAt ℝ (l : ℕ∞)
        (fun s : ℝ => highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) r :=
      (hsm_hi.contDiffAt (x := r)).of_le le_top
    have hsplit : iteratedDeriv l (fun s : ℝ =>
          paperLayer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r
        = iteratedDeriv l (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) r
          + iteratedDeriv l (fun s : ℝ =>
              layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r
          + iteratedDeriv l (fun s : ℝ =>
              highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) r := by
      have hE : (fun s : ℝ => paperLayer (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s)
          = (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s)
            + (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s)
            + (fun s : ℝ => highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) := by
        funext s; simp only [paperLayer, Pi.add_apply]
      have outer : iteratedDeriv l (((fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s)
              + (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s))
            + (fun s : ℝ => highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s)) r
          = iteratedDeriv l ((fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s)
              + (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s)) r
            + iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) r :=
        iteratedDeriv_add (hlow_at.add htr_at) hhi_at
      have inner : iteratedDeriv l ((fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s)
              + (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s)) r
          = iteratedDeriv l (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) r
            + iteratedDeriv l (fun s : ℝ =>
                layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r :=
        iteratedDeriv_add hlow_at htr_at
      rw [hE, outer, inner]
    rw [hpunct, hsplit]
    have htri : ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) r
          + iteratedDeriv l (fun s : ℝ =>
              layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r
          + iteratedDeriv l (fun s : ℝ =>
              highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
        ≤ ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) r‖
          + ‖iteratedDeriv l (fun s : ℝ =>
              layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r‖
          + ‖iteratedDeriv l (fun s : ℝ =>
              highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) r‖ := by
      have h2' := norm_add_le (iteratedDeriv l (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) r
          + iteratedDeriv l (fun s : ℝ =>
              layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r)
        (iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) r)
      have h1' := norm_add_le (iteratedDeriv l (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) r)
        (iteratedDeriv l (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r)
      linarith
    calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) r
          + iteratedDeriv l (fun s : ℝ => layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r
          + iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
        ≤ (|r| ^ k) * (‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) r‖
            + ‖iteratedDeriv l (fun s : ℝ =>
                layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r‖
            + ‖iteratedDeriv l (fun s : ℝ =>
                highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) r‖) :=
          mul_le_mul_of_nonneg_left htri (by positivity)
      _ = (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d ((1 : ℝ) +ᵥ w) s) r‖
            + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
                layerTrunc (Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r‖
            + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
                highPart (Gcusp ℓ d) ((1 : ℝ) +ᵥ w) s) r‖ := by ring
      _ ≤ C1 * (Work.Kernels.scale w) ^ (max N1 (max N2 N3))
            + C2 * (Work.Kernels.scale w) ^ (max N1 (max N2 N3))
            + C3 * (Work.Kernels.scale w) ^ (max N1 (max N2 N3)) := by
          linarith [b1, b2, b3]
      _ = (C1 + C2 + C3) * (Work.Kernels.scale w) ^ (max N1 (max N2 N3)) := by ring

end Work.Asymptotics
