import Mathlib
import Submission.Work.Asymptotics.TSasm.layerSemi_Tregion
import Submission.Work.Asymptotics.TSasm.layerSemi_lowHalfFunnelNegRe
import Submission.Work.Asymptotics.tileLayerSeminormTS
import Submission.Work.Asymptotics.TSasm.cuspOneLowHalfTile_TS
import Submission.Work.Asymptotics.PaperLayerLadderTS
import Submission.Work.Asymptotics.layer_cuspHalf_Rminus_lowstrip
import Submission.Work.Asymptotics.layerShiftBandAllD
import Submission.Work.Asymptotics.layer_semi_KEpsilon_TS
import Submission.Work.Asymptotics.im_le_two_of_Tregion_TS
import Submission.Work.CKFinal.cuspHalf_Rminus_split
import Submission.Work.CKFinal.ladder_iteratedDeriv

set_option maxHeartbeats 1600000

namespace Work.CKFinal

open UpperHalfPlane ModularGroup MeasureTheory
open scoped MatrixGroups UpperHalfPlane

/-! # The layer seminorm on the cusp-`±1` half tiles

First conjunct: `R₋ = {τ ∈ 𝒟 : S •((-1)+ᵥτ) ∈ 𝒟, 1/2 ≤ Im (S •((-1)+ᵥτ))}`.  Writing
`w = τ - 1` (so `1 +ᵥ w = τ`), the hypotheses say `w ∈ 𝒟 = S • 𝒟` and `Im (S • w) ≥ 1/2`, i.e.
`w ∈ Tregion ∪ KEpsilon`:

* `w ∈ KEpsilon` (i.e. `2 ≤ Im (S • w)`) is the cusp-`0` case: the bound is
  `Work.Asymptotics.TileLayerSeminorm`, whose conclusion is about the layer at `1 +ᵥ w = τ`, plus
  the scale comparison `scale w ≤ 2 scale τ`;
* `w ∈ Tregion`: `cuspHalf_Rminus_split` puts `τ` in `Tregion`, in the low bad-line region
  `BlLow.blLowSet`, or in the low strip `{1/2 ≤ Im ≤ 2, Im (S • τ) < 1/2}` (where the pole
  `z = τ - 1` grazes the contour), handled by `layerSemi_Tregion`, `LayerSemiBlLowTS` and
  `layer_cuspHalf_Rminus_lowstrip`.

Second conjunct: `R₊` with `u = τ + 1`.  The `T`-ladder `lh_layer_vadd_ladder` gives
`layer τ = 2 layer u - layer (1 +ᵥ u)`, so it suffices to bound the layer at `u` and at `1 +ᵥ u`:

* `u ∈ KEpsilon`: `layer u` by the cusp-`0` bound `layer_semi_KEpsilon_TS` and `layer (1 +ᵥ u)` by
  `TileLayerSeminorm`;
* `u ∈ Tregion`, `1/2 ≤ Im u`: then `τ ∈ {𝒟 : 1/2 ≤ Im ≤ 2, Re < 0}` and
  `layerSemi_lowHalfFunnelNegRe` bounds the layer at `τ` directly;
* `u ∈ Tregion`, `Im u < 1/2`: `layer u` by `layerSemi_Tregion` and `layer (1 +ᵥ u)` by
  `layerShiftBandAllD` (if `1/4 ≤ Re u`) or `ts_layerSemi_vadd_one_Tregion` (if `0 < Re u < 1/4`).
-/

/-! ## Absorption helpers -/

/-- Absorbing a constant into `c' * (s')^N'` (`s' ≥ 1`, `N' ≥ 0`). -/
lemma const_le_mul_rpow {c c' s N : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c')
    (hs : 1 ≤ s) (hN : 0 ≤ N) : c ≤ c' * s ^ N := by
  have h1 : (1 : ℝ) ≤ s ^ N := Real.one_le_rpow hs hN
  calc c ≤ c' := hcc
    _ = c' * 1 := (mul_one c').symm
    _ ≤ c' * s ^ N := mul_le_mul_of_nonneg_left h1 (le_trans hc hcc)

/-- Monotone absorption in both the constant and the exponent (`s ≥ 1`, `s ≤ s'`, `N ≤ N'`). -/
lemma mul_rpow_absorb {c c' s s' N N' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c')
    (hs : 1 ≤ s) (hss : s ≤ s') (hN : N ≤ N') (hN' : 0 ≤ N') :
    c * s ^ N ≤ c' * s' ^ N' := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have h1 : s ^ N ≤ s ^ N' := Real.rpow_le_rpow_of_exponent_le hs hN
  have h2 : s ^ N' ≤ s' ^ N' := Real.rpow_le_rpow hs0.le hss hN'
  have h3 : c * s ^ N ≤ c' * s ^ N' :=
    mul_le_mul hcc h1 (Real.rpow_nonneg hs0.le N) (le_trans hc hcc)
  exact le_trans h3 (mul_le_mul_of_nonneg_left h2 (le_trans hc hcc))

/-- Absorption with a factor `2` in the scale: if `1 ≤ s ≤ 2 s'`, `s' ≥ 1` and `N ≤ N'` then
`c * s^N ≤ (c * 2^{N'}) * (s')^{N'}`. -/
lemma mul_rpow_absorb_two {c s s' N N' : ℝ} (hc : 0 ≤ c) (hs : 1 ≤ s) (hss : s ≤ 2 * s')
    (hs' : 1 ≤ s') (hN : N ≤ N') (hN' : 0 ≤ N') :
    c * s ^ N ≤ (c * 2 ^ N') * s' ^ N' := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hs'0 : 0 < s' := lt_of_lt_of_le zero_lt_one hs'
  have h1 : s ^ N ≤ s ^ N' := Real.rpow_le_rpow_of_exponent_le hs hN
  have h2 : s ^ N' ≤ (2 * s') ^ N' := Real.rpow_le_rpow hs0.le hss hN'
  have h3 : (2 * s') ^ N' = 2 ^ N' * s' ^ N' := Real.mul_rpow (by norm_num) hs'0.le
  have h4 : (0 : ℝ) ≤ 2 ^ N' * s' ^ N' :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) N') (Real.rpow_nonneg hs'0.le N')
  calc c * s ^ N ≤ c * s ^ N' := mul_le_mul_of_nonneg_left h1 hc
    _ ≤ c * (2 * s') ^ N' := mul_le_mul_of_nonneg_left h2 hc
    _ = c * (2 ^ N' * s' ^ N') := by rw [h3]
    _ = (c * 2 ^ N') * s' ^ N' := by ring

/-- Two terms with exponents `M₁, M₂ ≤ N` are dominated by their sum with exponent `N`. -/
lemma two_term_le_rpow {a b s N M1 M2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 1 ≤ s)
    (h1 : M1 ≤ N) (h2 : M2 ≤ N) : a * s ^ M1 + b * s ^ M2 ≤ (a + b) * s ^ N := by
  have e1 : a * s ^ M1 ≤ a * s ^ N :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs h1) ha
  have e2 : b * s ^ M2 ≤ b * s ^ N :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs h2) hb
  calc a * s ^ M1 + b * s ^ M2 ≤ a * s ^ N + b * s ^ N := add_le_add e1 e2
    _ = (a + b) * s ^ N := by ring

/-- Weighted norms: `|r|^k ‖2 g - h‖ ≤ 2 A + B` from `|r|^k ‖g‖ ≤ A`, `|r|^k ‖h‖ ≤ B`. -/
lemma absmul_norm_two_sub_le {k : ℕ} {r : ℝ} {g h : ℂ} {A B : ℝ}
    (hg : |r| ^ k * ‖g‖ ≤ A) (hh : |r| ^ k * ‖h‖ ≤ B) :
    |r| ^ k * ‖2 * g - h‖ ≤ 2 * A + B := by
  have hk : (0 : ℝ) ≤ |r| ^ k := pow_nonneg (abs_nonneg r) k
  have h1 : ‖(2 : ℂ) * g - h‖ ≤ 2 * ‖g‖ + ‖h‖ := by
    have h := norm_sub_le ((2 : ℂ) * g) h
    rw [norm_mul, Complex.norm_ofNat] at h
    linarith
  calc |r| ^ k * ‖2 * g - h‖ ≤ |r| ^ k * (2 * ‖g‖ + ‖h‖) :=
        mul_le_mul_of_nonneg_left h1 hk
    _ = 2 * (|r| ^ k * ‖g‖) + |r| ^ k * ‖h‖ := by ring
    _ ≤ 2 * A + B := by linarith

/-! ## The ladder identity for the iterated derivatives -/

/-- **The `T`-ladder, differentiated.**  For `u ∈ 𝒟` with `0 < Re u` (and `u - 1 ∈ 𝒟`), the
identity `layer (u-1) = 2 layer u - layer (u+1)` of `lh_layer_vadd_ladder`, differentiated `l`
times.  For `l = 0` it is the pointwise ladder; for `l ≥ 1` it is `ladder_iteratedDeriv`. -/
lemma ladder_deriv_at (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : UpperHalfPlane) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re)
    (hm : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD) (l : ℕ) (r : ℝ) :
    iteratedDeriv l (fun s : ℝ =>
        Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) s) r
      = 2 * iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r
        - iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) s) r := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    simp only [iteratedDeriv_zero]
    have h := Work.Asymptotics.lh_layer_vadd_ladder ℓ d hd u hu hre r
    rw [h]; ring
  · exact Work.CKFinal.ladder_iteratedDeriv ℓ d hd u hu hre hm hl r

/-! ## The target -/

theorem layer_semi_cuspHalf (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ((∀ (τ : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD →
          ModularGroup.S • ((-1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD →
          (1 : ℝ) / 2 ≤ (ModularGroup.S • ((-1 : ℝ) +ᵥ τ)).im → ∀ r : ℝ,
          |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
            ≤ C * (Work.Kernels.scale τ) ^ N) ∧
        (∀ (τ : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD →
          ModularGroup.S • ((1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD →
          (1 : ℝ) / 2 ≤ (ModularGroup.S • ((1 : ℝ) +ᵥ τ)).im → ∀ r : ℝ,
          |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
            ≤ C * (Work.Kernels.scale τ) ^ N)) := by
  intro k l
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := Work.Asymptotics.tileLayerSeminormTS ℓ d hd k l
  obtain ⟨C2, hC2, hb2⟩ := Work.Asymptotics.layerSemi_Tregion ℓ d hd k l
  obtain ⟨C3, hC3, hb3⟩ := Work.Asymptotics.LayerSemiBlLowTS ℓ d hd k l
  obtain ⟨C4, hC4, hb4⟩ := Work.Asymptotics.ts_layerSemi_vadd_one_Tregion ℓ d hd k l
  obtain ⟨C5, hC5, hb5⟩ := Work.Asymptotics.layerSemi_lowHalfFunnelNegRe ℓ d hd k l
  obtain ⟨C6, hC6, hb6⟩ := Work.Asymptotics.layerShiftBandAllD ℓ d hd k l
  obtain ⟨C7, N7, hC7, hN7, hb7⟩ := Work.Asymptotics.layer_semi_KEpsilon_TS ℓ d hd k l
  obtain ⟨C8, N8, hC8, hN8, hb8⟩ := Work.Asymptotics.layer_cuspHalf_Rminus_lowstrip ℓ d hd k l
  -- the constants
  set NN : ℝ := max N1 (max N7 N8) with hNN
  set CC : ℝ := (2 * C7 + C1) * 2 ^ NN + (2 * C2 + C3 + C4 + C5 + C6 + C8) with hCC
  have hN0 : 0 ≤ NN := by rw [hNN]; exact le_trans hN1 (le_max_left _ _)
  have hN1N : N1 ≤ NN := by rw [hNN]; exact le_max_left _ _
  have hN7N : N7 ≤ NN := by
    rw [hNN]; exact le_trans (le_max_left N7 N8) (le_max_right N1 _)
  have hN8N : N8 ≤ NN := by
    rw [hNN]; exact le_trans (le_max_right N7 N8) (le_max_right N1 _)
  have h2N : (0 : ℝ) ≤ 2 ^ NN := Real.rpow_nonneg (by norm_num) NN
  have hrest : (0 : ℝ) ≤ 2 * C2 + C3 + C4 + C5 + C6 + C8 := by linarith
  have hC0 : 0 ≤ CC := by rw [hCC]; nlinarith [h2N, hC7, hC1, hrest]
  have hC1le : C1 * 2 ^ NN ≤ CC := by rw [hCC]; nlinarith [h2N, hC7, hC1, hrest]
  have hCable : (2 * C7 + C1) * 2 ^ NN ≤ CC := by rw [hCC]; linarith
  have hC2le : C2 ≤ CC := by rw [hCC]; nlinarith [h2N, hC7, hC1, hrest]
  have hC3le : C3 ≤ CC := by rw [hCC]; nlinarith [h2N, hC7, hC1, hrest]
  have hC5le : C5 ≤ CC := by rw [hCC]; nlinarith [h2N, hC7, hC1, hrest]
  have hC8le : C8 ≤ CC := by rw [hCC]; nlinarith [h2N, hC7, hC1, hrest]
  have hCble : 2 * C2 + (C4 + C6) ≤ CC := by rw [hCC]; nlinarith [h2N, hC7, hC1, hrest]
  refine ⟨CC, NN, hC0, hN0, ⟨?_, ?_⟩⟩
  · -- the `-1` half
    intro τ hτD hS him r
    have hτ1 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by rw [← add_vadd]; norm_num
    have hwD : ((-1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD := by
      have h := Work.Asymptotics.S_smul_mem_DomainD hS
      rwa [Work.Asymptotics.S_smul_S_smul] at h
    have hwr : (((-1 : ℝ) +ᵥ τ : UpperHalfPlane)).re ≠ 0 := by
      have h := (Work.Asymptotics.mem_DomainD.mp hτD).2.1
      rw [UpperHalfPlane.vadd_re]; linarith
    have hsw : Work.Kernels.scale ((-1 : ℝ) +ᵥ τ) ≤ 2 * Work.Kernels.scale τ := by
      have h := Work.Asymptotics.scale_le_scale_vadd_one ((-1 : ℝ) +ᵥ τ)
      rwa [hτ1] at h
    have hsτ1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    rcases le_or_gt 2 ((ModularGroup.S • ((-1 : ℝ) +ᵥ τ)).im) with hK | hT
    · -- `τ - 1 ∈ KEpsilon`: the cusp-`0` bound at `1 +ᵥ (τ - 1) = τ`
      have h := hb1 ((-1 : ℝ) +ᵥ τ) ⟨hwD, hK⟩ hwr r
      rw [hτ1] at h
      have h1 : C1 * Work.Kernels.scale ((-1 : ℝ) +ᵥ τ) ^ N1
          ≤ (C1 * 2 ^ NN) * (Work.Kernels.scale τ) ^ NN :=
        mul_rpow_absorb_two hC1 (Work.Kernels.one_le_scale _) hsw hsτ1 hN1N hN0
      have h2 : (C1 * 2 ^ NN) * (Work.Kernels.scale τ) ^ NN
          ≤ CC * (Work.Kernels.scale τ) ^ NN :=
        mul_le_mul_of_nonneg_right hC1le (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le NN)
      exact le_trans h (le_trans h1 h2)
    · -- `τ - 1 ∈ Tregion`
      have hwT : ((-1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.Tregion :=
        ⟨hwD, him, le_of_lt hT⟩
      rcases Work.CKFinal.cuspHalf_Rminus_split hτD hwT with hc | hc | hc
      · exact le_trans (hb2 τ r hc) (const_le_mul_rpow hC2 hC2le hsτ1 hN0)
      · exact le_trans (hb3 τ r hc) (const_le_mul_rpow hC3 hC3le hsτ1 hN0)
      · obtain ⟨hy1, hy2, hSτ⟩ := hc
        exact le_trans (hb8 τ hτD hy1 hy2 hwT hSτ r)
          (mul_rpow_absorb hC8 hC8le hsτ1 le_rfl hN8N hN0)
  · -- the `+1` half
    intro τ hτD hS him r
    have hτu : (-1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) = τ := by rw [← add_vadd]; norm_num
    have huD : ((1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD := by
      have h := Work.Asymptotics.S_smul_mem_DomainD hS
      rwa [Work.Asymptotics.S_smul_S_smul] at h
    have hure : 0 < (((1 : ℝ) +ᵥ τ : UpperHalfPlane)).re := by
      have h := (Work.Asymptotics.mem_DomainD.mp hτD).1
      rw [UpperHalfPlane.vadd_re]; linarith
    have hsτ1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hsu : Work.Kernels.scale ((1 : ℝ) +ᵥ τ) ≤ 2 * Work.Kernels.scale τ :=
      Work.Asymptotics.scale_vadd_one_le τ
    have hs1u : (1 : ℝ) ≤ Work.Kernels.scale ((1 : ℝ) +ᵥ τ) :=
      Work.Kernels.one_le_scale _
    -- the ladder identity at `τ = -1 +ᵥ u`
    have hder : iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r
        = 2 * iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ τ) s) r
          - iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d
                ((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ)) s) r := by
      have hm : ((-1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ)) ∈ Work.Asymptotics.DomainD := by
        rw [hτu]; exact hτD
      have h := ladder_deriv_at ℓ d hd ((1 : ℝ) +ᵥ τ) huD hure hm l r
      rw [hτu] at h
      exact h
    rcases le_or_gt 2 ((ModularGroup.S • ((1 : ℝ) +ᵥ τ)).im) with hK | hT
    · -- `τ + 1 ∈ KEpsilon`: `layer u` (cusp-`0`) and `layer (1 +ᵥ u)` (cusp-`0` tile)
      rw [hder]
      refine le_trans (absmul_norm_two_sub_le (hb7 ((1 : ℝ) +ᵥ τ) ⟨huD, hK⟩ r)
        (hb1 ((1 : ℝ) +ᵥ τ) ⟨huD, hK⟩ (ne_of_gt hure) r)) ?_
      have h3 : (2 * C7) * (Work.Kernels.scale ((1 : ℝ) +ᵥ τ)) ^ N7
            + C1 * (Work.Kernels.scale ((1 : ℝ) +ᵥ τ)) ^ N1
          ≤ (2 * C7 + C1) * (Work.Kernels.scale ((1 : ℝ) +ᵥ τ)) ^ NN :=
        two_term_le_rpow (by linarith) hC1 hs1u hN7N hN1N
      have h4 : (2 * C7 + C1) * (Work.Kernels.scale ((1 : ℝ) +ᵥ τ)) ^ NN
          ≤ ((2 * C7 + C1) * 2 ^ NN) * (Work.Kernels.scale τ) ^ NN :=
        mul_rpow_absorb_two (by linarith) hs1u hsu hsτ1 le_rfl hN0
      have h5 : ((2 * C7 + C1) * 2 ^ NN) * (Work.Kernels.scale τ) ^ NN
          ≤ CC * (Work.Kernels.scale τ) ^ NN :=
        mul_le_mul_of_nonneg_right hCable (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le NN)
      calc 2 * (C7 * (Work.Kernels.scale ((1 : ℝ) +ᵥ τ)) ^ N7)
            + C1 * (Work.Kernels.scale ((1 : ℝ) +ᵥ τ)) ^ N1
          = (2 * C7) * (Work.Kernels.scale ((1 : ℝ) +ᵥ τ)) ^ N7
            + C1 * (Work.Kernels.scale ((1 : ℝ) +ᵥ τ)) ^ N1 := by ring
        _ ≤ (2 * C7 + C1) * (Work.Kernels.scale ((1 : ℝ) +ᵥ τ)) ^ NN := h3
        _ ≤ ((2 * C7 + C1) * 2 ^ NN) * (Work.Kernels.scale τ) ^ NN := h4
        _ ≤ CC * (Work.Kernels.scale τ) ^ NN := h5
    · -- `τ + 1 ∈ Tregion`
      have huT : ((1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.Tregion := ⟨huD, him, le_of_lt hT⟩
      have himu : (((1 : ℝ) +ᵥ τ : UpperHalfPlane)).im = τ.im := UpperHalfPlane.vadd_im 1 τ
      have himu2 : (((1 : ℝ) +ᵥ τ : UpperHalfPlane)).im ≤ 2 :=
        Work.Asymptotics.im_le_two_of_Tregion_TS huT
      rcases le_or_gt ((1 : ℝ) / 2) (((1 : ℝ) +ᵥ τ : UpperHalfPlane)).im with hy | hy
      · -- `1/2 ≤ Im u = Im τ` and `Re τ < 0`: the low half funnel at `τ`
        have hτim1 : (1 : ℝ) / 2 ≤ τ.im := by rw [← himu]; exact hy
        have hτim2 : τ.im ≤ 2 := by rw [← himu]; exact himu2
        have hτre : τ.re < 0 := by
          have h := (Work.Asymptotics.mem_DomainD.mp huD).2.1
          rw [UpperHalfPlane.vadd_re] at h
          linarith
        exact le_trans (hb5 τ r hτD hτim1 hτim2 hτre) (const_le_mul_rpow hC5 hC5le hsτ1 hN0)
      · -- the ladder, with the `T`-shift bounds for `layer (1 +ᵥ u)`
        have hum : (((1 : ℝ) +ᵥ τ : UpperHalfPlane)).im < 1 / 2 := hy
        rw [hder]
        have hh : |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d
                ((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ)) s) r‖ ≤ C4 + C6 := by
          rcases le_or_gt ((1 : ℝ) / 4) (((1 : ℝ) +ᵥ τ : UpperHalfPlane)).re with h4 | h4
          · exact le_trans (hb6 ((1 : ℝ) +ᵥ τ) r huT h4) (by linarith)
          · exact le_trans (hb4 ((1 : ℝ) +ᵥ τ) r huT hure h4 (le_of_lt hum)) (by linarith)
        exact le_trans (absmul_norm_two_sub_le (hb2 ((1 : ℝ) +ᵥ τ) r huT) hh)
          (const_le_mul_rpow (by linarith) hCble hsτ1 hN0)

end Work.CKFinal
