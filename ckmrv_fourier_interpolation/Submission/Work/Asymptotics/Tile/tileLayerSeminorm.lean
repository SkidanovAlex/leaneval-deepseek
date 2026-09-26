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
* `Work.Asymptotics.Tile.tileLayerTrunc_bound` (proved, from the below-pole window
  `Work.Asymptotics.Tile.tileWindowBound` and the sharp tail `Work.Asymptotics.Tile.tileSharpTail`)
  — the `trunc` piece `sinSq r ∫_1^∞ (K - Aexp) e^{-πr²t} dt`;
* the explicit closed form `highPart`, bounded here directly on the tile from
  `Work.Asymptotics.Gcusp_tile_bound`.

The combination uses the evenness of `paperLayer` and the puncture identity
`Work.Asymptotics.punctured_iteratedDeriv`, exactly as in the cusp-`0` analysis.
-/
import Mathlib
import Submission.Work.Asymptotics.cuspOneTileInputs
import Submission.Work.Asymptotics.Tile.layerLow_tile_seminorm
import Submission.Work.Asymptotics.Tile.tileLayerTrunc_bound
import Submission.Work.Asymptotics.Tile.tilePPWindow_bound
import Submission.Work.Asymptotics.Tile.tileSharpTail
import Submission.Work.Asymptotics.highPart_seminorm
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.layerPieces_smooth
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.Asymptotics.Kaxis_tile_flat_below_pole
import Submission.Work.Asymptotics.Tile.tileBelowPoleStripOffCoincClean
import Submission.Work.Asymptotics.Tile.tileStripCusp1Re
import Submission.Work.Asymptotics.Tile.tileWindowRestricted_far
import Submission.Work.Asymptotics.Tile.tileWindowRestricted
import Submission.Work.Asymptotics.Gcusp_tile_bound
import Submission.Work.Asymptotics.paperLayer_smooth
import Submission.Work.Asymptotics.Kaxis_tile_aux

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open Work.Kernels Work.Asymptotics
open scoped MatrixGroups UpperHalfPlane Topology ContDiff

namespace Work.Asymptotics.Tile

/-! ## The below-pole window away from the bad line `Re w = 0`

The window bound is only needed for `w` with `Re w ≠ 0` (the target `TileLayerSeminorm` carries
that hypothesis).  On the bad line `Re w = 0` the height-`Im (S • w)` orbit point `S • w` lies
*on* the contour, where the formula defining `Kfun` uses Lean's junk value `0⁻¹ = 0`; the
restricted statement below is exactly the coincidence-free case. -/
/-- **The resonant strip of the tile deviation, restricted to `Re w ≠ 0`.**

This is `Work.Asymptotics.Tile.TileBelowPoleStripOffCoinc` (proved in
`Tile/tileBelowPoleStripOffCoincClean.lean` by the three-zeros / maximum-modulus endgame) with
the non-coincidence hypothesis discharged by `Re w ≠ 0` (`stripNoCoincidence`). -/
private theorem tileStripRestricted_own (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane), w ∈ KEpsilon → w.re ≠ 0 → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ t : ℝ, (ModularGroup.S • w).im - 1 ≤ t → t ≤ (ModularGroup.S • w).im + 1 →
          ‖Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := tileBelowPoleStripOffCoincClean ℓ d hd
  refine ⟨C, N, M, hC, hN, hM, ?_⟩
  intro w hw hre n hn t ht1 ht2
  have ht : 0 < t := by have := hw.2; linarith
  exact hb w n hn hw t ht ht1 ht2
    (stripNoCoincidence ℓ d w hw hre n hn t ht ht1 ht2)

/-- **The below-pole window on the cusp-`±1` tiles away from the bad line `Re w = 0`**,
assembled from the far regime (`tileWindowRestricted_far`), the restricted strip
(`tileStripRestricted_own`), the top regime (`tileBelowPoleTop`) and the low window
(`tile_dev_low`) by `tileWindowRestricted_of_pieces`. -/
private theorem tileWindowRestricted_own (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon → w.re ≠ 0 →
        ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
          ‖Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M :=
  tileWindowRestricted_of_pieces ℓ d hd (tileWindowRestricted_far ℓ d hd)
    (tileStripRestricted_own ℓ d hd)

/-! ## Evenness of the three pieces of the layer in the radial variable -/

private lemma sinSq_neg_tile (r : ℝ) : sinSq (-r) = sinSq r := by
  have hsq : (((-r : ℝ)) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [sinSq, hsq]

private lemma layerLow_neg_tile (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane)
    (s : ℝ) : layerLow ℓ d τ (-s) = layerLow ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [layerLow, sinSq, hsq]

private lemma layerTrunc_neg_tile (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    layerTrunc G ℓ d τ (-s) = layerTrunc G ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [layerTrunc, sinSq, hsq]

private lemma highPart_neg_tile (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane)
    (s : ℝ) : highPart G τ (-s) = highPart G τ s := by
  simp only [highPart, neg_sq]

private lemma paperLayer_neg_tile (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    paperLayer G ℓ d τ (-s) = paperLayer G ℓ d τ s := by
  simp only [paperLayer]
  rw [layerLow_neg_tile, layerTrunc_neg_tile, highPart_neg_tile]

/-! ## The `high` piece of the layer on the tile

The `high` part is an explicit linear combination of the four cusp coefficients `Gcusp ℓ d i j`,
so its seminorms are bounded on the tile by `Work.Asymptotics.Gcusp_tile_bound`.  This is the tile
version of `Work.Asymptotics.highPart_seminorm`, with the moderate growth on `𝒟` replaced by the
tile bound (the tile point `1 +ᵥ w` is not in `𝒟`). -/

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
  obtain ⟨Cw, Nw, hCw, hNw, hwin⟩ := tilePPWindow_bound ℓ d hd
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
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Kaxis (Kfun ℓ d) ((1 : ℝ) +ᵥ w) t)
      (volume.restrict (Set.Ioc 0 1)) :=
    (measurable_Kaxis_Kfun ℓ d hd _).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 1)),
      ‖Kaxis (Kfun ℓ d) ((1 : ℝ) +ᵥ w) t‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
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
      have hw1' : ‖Kaxis (Kfun ℓ d) ((1 : ℝ) +ᵥ w) t
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
      have hsub : ‖Kaxis (Kfun ℓ d) ((1 : ℝ) +ᵥ w) t‖
          ≤ Cw * (Work.Kernels.scale w) ^ Nw
            + (1 / (2 * Real.pi)) * (1 / |w.re|) := by
        have heq : Kaxis (Kfun ℓ d) ((1 : ℝ) +ᵥ w) t
            = (Kaxis (Kfun ℓ d) ((1 : ℝ) +ᵥ w) t
                - ((1 : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹))
              + ((1 : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹) := by ring
        rw [heq]
        exact le_trans (norm_add_le _ _) (add_le_add hw1' hPP)
      have h1 : (0 : ℝ) ≤ cF * (Work.Kernels.scale w) ^ NF :=
        mul_nonneg hcF (Real.rpow_nonneg hscale0.le _)
      rw [hBdef]
      linarith
  have hmain := contDiff_omega_intervalIntegral_exp (κ := fun t : ℝ =>
    Kaxis (Kfun ℓ d) ((1 : ℝ) +ᵥ w) t) hB0 hmeas hbound
  simpa only [layerLow] using contDiff_omega_sinSq.mul hmain

/-! ## The `trunc` piece with the below-pole window restricted to `Re w ≠ 0`

This is `Work.Asymptotics.Tile.tile_amplitude_bound` and
`Work.Asymptotics.Tile.tileLayerTrunc_bound` with the (false on the bad line) unrestricted
window hypothesis replaced by the restricted one: the amplitude is controlled polynomially on
`[1, 2 Im (S•w) + 1]` for `Re w ≠ 0` and by `e^{-π(t - Im(S•w))}` beyond (which is
`Work.Asymptotics.Tile.tileSharpTail`, proved and unrestricted).  The rest of the argument is
copied verbatim. -/

private lemma tile_amplitude_bound_restr (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hwin : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon → w.re ≠ 0 →
        ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M)
    (hsharp : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
        ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
        ‖Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M
              * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))))
    (w : UpperHalfPlane) (n : ℤ) (hw : w ∈ KEpsilon) (hre : w.re ≠ 0)
    (hn : n = 1 ∨ n = -1) :
    ∃ Cg Mg : ℝ, 0 ≤ Cg ∧ 0 ≤ Mg ∧
      AEStronglyMeasurable (fun t : ℝ =>
        Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t)
        (volume.restrict (Set.Ici (1 : ℝ))) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
        ‖Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ Cg * t ^ Mg * Real.exp (-(Real.pi * t))) := by
  obtain ⟨Cw, Nw, Mw, hCwpos, hNw, hMw, hwinb⟩ := hwin
  obtain ⟨Cs, Ns, Ms, hCspos, hNs, hMs, hsharpb⟩ := hsharp
  set h : ℝ → ℂ := fun t =>
    Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t with hhdef
  have hmeas : AEStronglyMeasurable h (volume.restrict (Set.Ici (1 : ℝ))) := by
    rw [hhdef]
    have h1 : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t) :=
      measurable_Kaxis_Kfun ℓ d hd _
    have h2 : Measurable (fun t : ℝ => Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t) := by
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
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact hglob t (Set.mem_Ici.mp ht)

private theorem tileLayerTrunc_bound_restr (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hwin : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon → w.re ≠ 0 →
        ∀ t : ℝ, 1 ≤ t → t ≤ 2 * (ModularGroup.S • w).im + 1 →
        ‖Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M)
    (hsharp : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
        ∀ t : ℝ, 2 * (ModularGroup.S • w).im + 1 ≤ t →
        ‖Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
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
    exists_bound_iteratedDeriv_tailIntegral_shift l Cw Nw Mw Cs Ns Ms
      hCwpos.le hNw hMw hCspos.le hNs hMs
  obtain ⟨cc, hcc, hcomp⟩ := exists_seminorm_bound_of_iteratedDeriv_bound k l
  refine ⟨cc * ct, Nt, mul_nonneg hcc hct, hNt, ?_, ?_⟩
  · intro w n hw hre hn
    obtain ⟨Cg, Mg, hCg, hMg, hmeas, hbglob⟩ :=
      tile_amplitude_bound_restr ℓ d hd hwin hsharp w n hw hre hn
    set g : ℝ → ℂ := fun t =>
      Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t with hgdef
    have hcont : ContDiffOn ℝ ⊤ (tailIntegral g) (Set.Ioi (-1)) :=
      contDiffOn_real_tailIntegral g hmeas hCg hMg hbglob
    have hsq : ContDiff ℝ ⊤ (fun r : ℝ => r ^ 2) := contDiff_id.pow 2
    have hcomp2 : ContDiffOn ℝ ⊤ (fun r : ℝ => tailIntegral g (r ^ 2)) Set.univ :=
      hcont.comp hsq.contDiffOn (fun r _ => by
        simp only [Set.mem_Ioi]; linarith [sq_nonneg r])
    have htr : ContDiff ℝ ⊤ (fun r : ℝ => tailIntegral g (r ^ 2)) :=
      contDiffOn_univ.mp hcomp2
    have hcos : ContDiff ℝ ⊤ (fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ)) := by
      have h1 : ContDiff ℝ ⊤ (fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℝ)) := by fun_prop
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
      Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t with hgdef
    have hA1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hT0 : (0 : ℝ) ≤ (ModularGroup.S • w).im := by linarith [hw.2]
    have hTA : (ModularGroup.S • w).im ≤ Work.Kernels.scale w := im_S_smul_le_scale w
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

/-! ## The assembly -/

theorem tileLayerSeminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    Work.Asymptotics.TileLayerSeminorm ℓ d := by
  intro k l
  obtain ⟨C1, N1, hC1, hN1, h1⟩ :=
    layerLow_tile_seminorm ℓ d hd (tilePPWindow_bound ℓ d hd) k l
  obtain ⟨C2, N2, hC2, hN2, h2cont, h2⟩ :=
    tileLayerTrunc_bound_restr ℓ d hd (tileWindowRestricted_own ℓ d hd)
      (tileSharpTail ℓ d hd) k l
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
        fun s => paperLayer_neg_tile (Gcusp ℓ d) ℓ d _ s
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

end Work.Asymptotics.Tile
