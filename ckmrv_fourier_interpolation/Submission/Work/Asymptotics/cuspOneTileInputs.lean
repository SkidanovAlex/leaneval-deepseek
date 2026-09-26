/-
# The cusp-`1` tile bound for `w ∈ E = KEpsilon`

This file assembles the cusp-`1` tile bound (the `n = 1` half of the workspace's
`Work.Asymptotics.cuspTile_seminorm`) from two analytic inputs, both of which are the
CKMRV §5.2 cusp-`1` analysis:

* `Work.Asymptotics.TileLayerSeminorm` — the `r`-seminorm bound for the regularised CKMRV layer
  `layer (Gcusp ℓ d) ℓ d (1 + w) ·` at the tile points `1 + w`, `w ∈ E`, `Re w ≠ 0`.  On the
  window `t ∈ [Re w/2, 1]` this needs the principal-part window `TilePPWindow`; on `[1,∞)` it
  needs the deviation window and the sharp cusp-`i∞` tail; the `r = 0` value is handled by the
  definition of `layer` (which is `0` there).
* `Work.Asymptotics.TileLayerAgreement` — the agreement of that layer with the naive contour
  transform `kernelTransform (Kfun ℓ d)` wherever the latter converges.

The remaining content of the proof is purely formal:

* the layer/contour transfer `Work.Asymptotics.tile_layer_transfer` (the threshold argument: the
  contour integral is `0` wherever the integrand is not integrable, and the integrability set is a
  threshold in `|r|`), applied to the set `tileReSet` of tile points with `Re w ≠ 0`;
* the bad-line vanishing `Work.Asymptotics.kernelTransform_eq_zero_bad_line_of_im_ne_one`, which
  settles all tile points with `Re w = 0` (`w = i y`): there the translate pole `z = w` meets the
  contour and the naive integral is the junk value `0`;
* the two elementary scale comparisons `scale (1 + w) ≤ 2 scale w` and `scale w ≤ 2 scale (1 + w)`.

Everything in this module is `sorry`-free: the two reductions and their supporting lemmas.  The
target `Work.Asymptotics.cuspOneTileE_TS` lives in the file of the same name, which imports this
module together with the (separately proved) inputs.  Keeping the definitions here rather than in
the target's file breaks the import cycle that would otherwise arise when an input is proved in a
module that needs these definitions.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Tile.tileLayerDefs
import Submission.Work.Asymptotics.Tile.tileLayerTransfer
import Submission.Work.Asymptotics.BLZero.BadLineClean
import Submission.Work.Asymptotics.FunnelSlashedDefs
import Submission.Work.Asymptotics.seminorm_on_cuspRegion_of_slashed

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

/-! ## The two analytic inputs -/

/-- **The layer seminorm bound on the cusp-`1` tile (away from the bad line `Re w = 0`).**

For `w ∈ E = KEpsilon` with `Re w ≠ 0`, the `r`-seminorms of the regularised layer
`layer (Gcusp ℓ d) ℓ d (1 + w) ·` are bounded by `C (scale w)^N`. -/
def TileLayerSeminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
    ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → w.re ≠ 0 → ∀ r : ℝ,
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r‖
        ≤ C * (Work.Kernels.scale w) ^ N

/-- **Agreement of the layer with the contour transform on the cusp-`±1` tiles.**

For every tile point `σ ∈ cuspTileSet` and every `r ≠ 0` at which the contour integrand is
integrable, the regularised layer coincides with the naive contour transform. -/
def TileLayerAgreement (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ (σ : UpperHalfPlane), σ ∈ Work.Asymptotics.cuspTileSet → ∀ r : ℝ, r ≠ 0 →
    MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
    Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r
      = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) σ r

/-! ## Elementary geometry of `E` and of the translate `1 + w` -/

/-- For `w ∈ E` one has `Im w ≤ 1/2`: indeed `2 ≤ Im (S w) = Im w / ‖w‖²`. -/
lemma im_le_half_of_mem_KEpsilon {w : UpperHalfPlane} (hw : w ∈ Work.Asymptotics.KEpsilon) :
    w.im ≤ 1 / 2 := by
  have h2 : 2 ≤ (ModularGroup.S • w).im := hw.2
  have hpos : 0 < ‖(w : ℂ)‖ ^ 2 := by
    have hne : (w : ℂ) ≠ 0 := w.ne_zero
    positivity
  have hj : Work.Kernels.jFun ModularGroup.S (w : ℂ) = (w : ℂ) := by
    rw [Work.Kernels.jFun_apply]; simp
  rw [Work.Kernels.im_smul_eq, hj] at h2
  rw [le_div_iff₀ hpos] at h2
  have him : w.im ^ 2 ≤ ‖(w : ℂ)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg ((w : ℂ).re), UpperHalfPlane.coe_im w, UpperHalfPlane.coe_re w]
  nlinarith [w.im_pos, him, h2]

/-- `scale (1 +ᵥ w) ≤ 2 * scale w`. -/
lemma scale_vadd_one_le (w : UpperHalfPlane) :
    Work.Kernels.scale ((1 : ℝ) +ᵥ w) ≤ 2 * Work.Kernels.scale w := by
  have hcoe : (((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ) = (1 : ℂ) + (w : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; norm_num
  have him : ((1 : ℝ) +ᵥ w).im = w.im := by
    rw [← UpperHalfPlane.coe_im, hcoe]; simp
  have hn : ‖(((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ)‖ ≤ 1 + ‖(w : ℂ)‖ := by
    rw [hcoe]; simpa using norm_add_le (1 : ℂ) (w : ℂ)
  have hw0 : 0 ≤ ‖(w : ℂ)‖ := norm_nonneg _
  have hi0 : 0 < w.im := w.im_pos
  rw [Work.Kernels.scale, Work.Kernels.scale, him]
  have hinv : 0 ≤ (w.im)⁻¹ := inv_nonneg.mpr hi0.le
  linarith

/-- `scale w ≤ 2 * scale (1 +ᵥ w)`. -/
lemma scale_le_scale_vadd_one (w : UpperHalfPlane) :
    Work.Kernels.scale w ≤ 2 * Work.Kernels.scale ((1 : ℝ) +ᵥ w) := by
  have hcoe : (((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ) = (1 : ℂ) + (w : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; norm_num
  have him : ((1 : ℝ) +ᵥ w).im = w.im := by
    rw [← UpperHalfPlane.coe_im, hcoe]; simp
  have hw : (w : ℂ) = ((1 : ℂ) + (w : ℂ)) - 1 := by ring
  have hn : ‖(w : ℂ)‖ ≤ 1 + ‖(((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ)‖ := by
    have h1 : ‖(((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ)‖ = ‖(1 : ℂ) + (w : ℂ)‖ := by rw [hcoe]
    rw [hw, h1]
    have h2 := norm_sub_le ((1 : ℂ) + (w : ℂ)) (1 : ℂ)
    rw [show ‖(1 : ℂ)‖ = 1 by simp] at h2
    linarith
  have hw0 : 0 ≤ ‖(((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ)‖ := norm_nonneg _
  have hi0 : 0 < w.im := w.im_pos
  rw [Work.Kernels.scale, Work.Kernels.scale, him]
  have hinv : 0 ≤ (w.im)⁻¹ := inv_nonneg.mpr hi0.le
  linarith

/-- The set of cusp-`1` tile points `1 + w` with `w ∈ E` and `Re w ≠ 0`. -/
def tileReSet : Set UpperHalfPlane :=
  {σ : UpperHalfPlane | ∃ w : UpperHalfPlane,
    w ∈ Work.Asymptotics.KEpsilon ∧ w.re ≠ 0 ∧ σ = (1 : ℝ) +ᵥ w}

/-! ## The assembly -/

/-- **The cusp-`1` tile bound from the layer seminorm bound and the layer agreement.** -/
theorem cuspOneTileE_TS_of_inputs (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (hL : TileLayerSeminorm ℓ d) (hagr : TileLayerAgreement ℓ d) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  intro k l
  -- the layer seminorm bound on the tile, in the form consumed by the transfer
  have hsemi : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ tileReSet →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N := by
    intro k l
    obtain ⟨C, N, hC, hN, hb⟩ := hL k l
    refine ⟨C * 2 ^ N, N, mul_nonneg hC (Real.rpow_nonneg (by norm_num) N), hN, ?_⟩
    intro τ r hτ
    obtain ⟨w, hw, hre, rfl⟩ := hτ
    have hbw := hb w hw hre r
    have hsc : Work.Kernels.scale w ≤ 2 * Work.Kernels.scale ((1 : ℝ) +ᵥ w) :=
      scale_le_scale_vadd_one w
    have h2 : (Work.Kernels.scale w) ^ N
        ≤ 2 ^ N * (Work.Kernels.scale ((1 : ℝ) +ᵥ w)) ^ N := by
      calc (Work.Kernels.scale w) ^ N
          ≤ (2 * Work.Kernels.scale ((1 : ℝ) +ᵥ w)) ^ N :=
            Real.rpow_le_rpow (Work.Kernels.scale_pos w).le hsc hN
        _ = 2 ^ N * (Work.Kernels.scale ((1 : ℝ) +ᵥ w)) ^ N :=
            Real.mul_rpow (by norm_num) (Work.Kernels.scale_pos _).le
    calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ w) s) r‖
        ≤ C * (Work.Kernels.scale w) ^ N := hbw
      _ ≤ C * (2 ^ N * (Work.Kernels.scale ((1 : ℝ) +ᵥ w)) ^ N) :=
          mul_le_mul_of_nonneg_left h2 hC
      _ = C * 2 ^ N * (Work.Kernels.scale ((1 : ℝ) +ᵥ w)) ^ N := by ring
  obtain ⟨C₂, N₂, hC₂, hN₂, hb₂⟩ :=
    tile_layer_transfer ℓ d hd (Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d)
      (K := tileReSet) (B := fun τ : UpperHalfPlane => Work.Kernels.scale τ)
      (fun τ _ => Work.Kernels.one_le_scale τ)
      (fun τ _ => by
        show Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ 0 = _
        rw [show Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ 0 = 0 by
              simp [Work.Asymptotics.layer]]
        exact (by simp [Work.Kernels.kernelTransform] : Work.Kernels.kernelTransform
          (Work.Kernels.Kfun ℓ d) τ 0 = 0).symm)
      (fun τ hτ r hr hint => by
        obtain ⟨w, hw, hre, rfl⟩ := hτ
        exact hagr ((1 : ℝ) +ᵥ w) ⟨w, hw, 1, Or.inl rfl, by norm_num⟩ r hr hint)
      hsemi k l
  refine ⟨max (C₂ * 2 ^ N₂) 1, N₂, le_trans zero_le_one (le_max_right _ _), hN₂, ?_⟩
  intro w r hw
  have hCpos : (0 : ℝ) ≤ max (C₂ * 2 ^ N₂) 1 := le_trans zero_le_one (le_max_right _ _)
  by_cases hre : w.re = 0
  · -- bad line: the contour integrand is never integrable and the transform is `0`
    have hre1 : ((1 : ℝ) +ᵥ w).re = ((1 : ℤ) : ℝ) := by
      rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]
      simp [hre]
    have him : ((1 : ℝ) +ᵥ w).im ≠ 1 := by
      have h := im_le_half_of_mem_KEpsilon hw
      have h2 : ((1 : ℝ) +ᵥ w).im = w.im := by
        rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_vadd]; simp
      rw [h2]
      linarith
    have hfun : (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d)
          ((1 : ℝ) +ᵥ w) s) = fun _ => (0 : ℂ) := by
      funext s
      exact kernelTransform_eq_zero_bad_line_of_im_ne_one ℓ d hd s 1 (Or.inl rfl) hre1 him
    rw [hfun, iteratedDeriv_const]
    split_ifs
    · simp only [norm_zero, mul_zero]
      exact mul_nonneg hCpos (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N₂)
    · simp only [norm_zero, mul_zero]
      exact mul_nonneg hCpos (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N₂)
  · have hmem : ((1 : ℝ) +ᵥ w) ∈ tileReSet := ⟨w, hw, hre, rfl⟩
    have hb := hb₂ ((1 : ℝ) +ᵥ w) r hmem
    have hsc : Work.Kernels.scale ((1 : ℝ) +ᵥ w) ≤ 2 * Work.Kernels.scale w :=
      scale_vadd_one_le w
    have h2 : (Work.Kernels.scale ((1 : ℝ) +ᵥ w)) ^ N₂
        ≤ 2 ^ N₂ * (Work.Kernels.scale w) ^ N₂ := by
      calc (Work.Kernels.scale ((1 : ℝ) +ᵥ w)) ^ N₂
          ≤ (2 * Work.Kernels.scale w) ^ N₂ :=
            Real.rpow_le_rpow (Work.Kernels.scale_pos _).le hsc hN₂
        _ = 2 ^ N₂ * (Work.Kernels.scale w) ^ N₂ :=
            Real.mul_rpow (by norm_num) (Work.Kernels.scale_pos w).le
    calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
        ≤ C₂ * (Work.Kernels.scale ((1 : ℝ) +ᵥ w)) ^ N₂ := hb
      _ ≤ C₂ * (2 ^ N₂ * (Work.Kernels.scale w) ^ N₂) :=
          mul_le_mul_of_nonneg_left h2 hC₂
      _ = C₂ * 2 ^ N₂ * (Work.Kernels.scale w) ^ N₂ := by ring
      _ ≤ max (C₂ * 2 ^ N₂) 1 * (Work.Kernels.scale w) ^ N₂ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N₂)

/-! ## The `(T*S)`-slash transport route

The cusp-`1` tile bound is *equivalent* to the `(T*S)`-slashed funnel bound, because
`(T*S) • τ = 1 + S • τ` and the slash law reads
`kernelTransform (slashKernel ℓ d (T*S)) τ = j(T*S,τ)^{-d/2} kernelTransform K ((T*S)•τ)`.
Below, `Work.Asymptotics.seminorm_on_cuspRegion_of_slashed` carries the slashed funnel bound to
the cusp region `cuspRegion (T*S) = 1 + E`, and the elementary conversion
`α (Im w)^{-β} + γ ‖1 + w‖^δ ≤ (α + γ 2^δ) (scale w)^{max β δ}` finishes the job. -/

/-- **The `(T*S)`-slashed funnel bound** (CKMRV §5.2's cusp-`1` analysis, in the funnel
coordinates `τ ∈ 𝓕 = {τ ∈ 𝒟 : 2 ≤ Im τ}`). -/
def TSSlashedFunnel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
    ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform
          (Work.Asymptotics.slashKernel ℓ d (ModularGroup.T * ModularGroup.S)) τ s) r‖
        ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ

/-- The translate `1 + w` is the `(T*S)`-image of `S • w`. -/
lemma TS_smul_S_smul (w : UpperHalfPlane) :
    (ModularGroup.T * ModularGroup.S) • (ModularGroup.S • w) = (1 : ℝ) +ᵥ w := by
  rw [mul_smul, S_smul_S_smul, UpperHalfPlane.modular_T_smul]

/-- `(T*S)⁻¹ • (1 + w) = S • w`. -/
lemma inv_TS_smul_vadd_one (w : UpperHalfPlane) :
    (ModularGroup.T * ModularGroup.S)⁻¹ • ((1 : ℝ) +ᵥ w) = ModularGroup.S • w := by
  rw [← TS_smul_S_smul w, ← mul_smul, inv_mul_cancel, one_smul]

/-- **The cusp-`1` tile bound from the `(T*S)`-slashed funnel bound.** -/
theorem cuspOneTileE_TS_of_slashed (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (h : TSSlashedFunnel ℓ d) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  intro k l
  obtain ⟨α, β, γ', δ, hα, hβ, hγ, hδ, hbound⟩ :=
    Work.Asymptotics.seminorm_on_cuspRegion_of_slashed ℓ d hd
      (ModularGroup.T * ModularGroup.S) h k l
  refine ⟨α + γ' * 2 ^ δ, max β δ, add_nonneg hα (mul_nonneg hγ (Real.rpow_nonneg (by norm_num) δ)),
    le_max_of_le_left hβ, ?_⟩
  intro w r hw
  have hmem : ((1 : ℝ) +ᵥ w) ∈ Work.Asymptotics.cuspRegion (ModularGroup.T * ModularGroup.S) := by
    rw [Work.Asymptotics.mem_cuspRegion, inv_TS_smul_vadd_one w]
    exact ⟨Work.Asymptotics.S_smul_mem_DomainD hw.1, hw.2⟩
  have hb := hbound ((1 : ℝ) +ᵥ w) r hmem
  have him : ((1 : ℝ) +ᵥ w).im = w.im := by
    rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_vadd]; simp
  have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hnorm : ‖(((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ)‖ ≤ 2 * Work.Kernels.scale w := by
    have h1 : (((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ) = (1 : ℂ) + (w : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; norm_num
    rw [h1]
    have h2 : ‖(1 : ℂ) + (w : ℂ)‖ ≤ 1 + ‖(w : ℂ)‖ := by
      simpa using norm_add_le (1 : ℂ) (w : ℂ)
    have h3 : ‖(w : ℂ)‖ ≤ Work.Kernels.scale w := Work.Kernels.coe_norm_le_scale w
    linarith
  have hinv : ((1 : ℝ) +ᵥ w).im ^ (-β) = (w.im) ^ (-β) := by rw [him]
  have hterm1 : α * ((1 : ℝ) +ᵥ w).im ^ (-β) ≤ α * (Work.Kernels.scale w) ^ (max β δ) := by
    rw [hinv]
    refine mul_le_mul_of_nonneg_left ?_ hα
    have h := Work.Kernels.inv_im_le_scale w
    calc (w.im) ^ (-β) = ((w.im)⁻¹) ^ β := by
          rw [Real.inv_rpow w.im_pos.le, Real.rpow_neg w.im_pos.le]
      _ ≤ (Work.Kernels.scale w) ^ β := Real.rpow_le_rpow (inv_nonneg.mpr w.im_pos.le) h hβ
      _ ≤ (Work.Kernels.scale w) ^ (max β δ) :=
          Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_left _ _)
  have hterm2 : γ' * (‖(((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ)‖) ^ δ
      ≤ γ' * 2 ^ δ * (Work.Kernels.scale w) ^ (max β δ) := by
    have hpow : (‖(((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ)‖) ^ δ
        ≤ (2 * Work.Kernels.scale w) ^ δ :=
      Real.rpow_le_rpow (norm_nonneg _) hnorm hδ
    rw [Real.mul_rpow (by norm_num) (Work.Kernels.scale_pos w).le] at hpow
    have hle : (Work.Kernels.scale w) ^ δ ≤ (Work.Kernels.scale w) ^ (max β δ) :=
      Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_right _ _)
    calc γ' * (‖(((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ)‖) ^ δ
        ≤ γ' * (2 ^ δ * (Work.Kernels.scale w) ^ δ) :=
          mul_le_mul_of_nonneg_left hpow hγ
      _ ≤ γ' * (2 ^ δ * (Work.Kernels.scale w) ^ (max β δ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hγ
          exact mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (by norm_num) δ)
      _ = γ' * 2 ^ δ * (Work.Kernels.scale w) ^ (max β δ) := by ring
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
      ≤ α * ((1 : ℝ) +ᵥ w).im ^ (-β) + γ' * (‖(((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ)‖) ^ δ := hb
    _ ≤ α * (Work.Kernels.scale w) ^ (max β δ)
          + γ' * 2 ^ δ * (Work.Kernels.scale w) ^ (max β δ) := add_le_add hterm1 hterm2
    _ = (α + γ' * 2 ^ δ) * (Work.Kernels.scale w) ^ (max β δ) := by ring

