import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.aesm_wSmallPair_pair
import Submission.Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre
import Submission.Work.BoseFixB1.integrableOn_slot_wSmallPair
import Submission.Work.BoseFixB1.wSmall1Pair_fibre_abs_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Localised small-box kernel facts (the interface of `q1_q3_q4_mass_localised`)

Standing hypotheses of the chapter (`v ≥ 0` radial, compactly supported, `MemLp v 1`,
`ScatSol v`, `1 ≤ M`, `0 < ℓ`, `0 < d`, `R0 ≤ ℓd/16`, `R0 ≤ ℓ·chiR0`) are abbreviated
below by the individual arguments; every lemma carries exactly what it uses.

The localised kernels are

* `W  := wSmallPair M ℓ d u v`              (numerator `v`),
* `W₁ := wSmallPair M ℓ d u (g0 v h)`       (= `wSmall1Pair h M ℓ d u`),
* `W₂ := wSmallPair M ℓ d u (g2 v h)`,
* `W₁ω := wSmallPair M ℓ d u (g0·w₀)`.

This module records the pointwise relations among them (`W₁ = W(1−ω)`,
`W₂ = W₁ + W₁ω`, `W₁ω = W₁·ω`), their (a.e.) non-negativity and dominance
`0 ≤ W₁ ≤ W` a.e., symmetry, and the fibre bounds/a.e.-strong measurability
used by the peel and mass estimates.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators

namespace Work.BoseFixB1

open Submission.BoseGases

set_option autoImplicit false

/-! ## Pointwise kernel relations -/

/-- `W₁ = W·(1−ω)` pointwise (the localised form of `w1_eq_w_mul_one_sub`). -/
lemma wSmall_rel_g0 {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u x y : ℝ³) :
    wSmallPair M ℓ d u (g0 v h) x y
      = wSmallPair M ℓ d u v x y * (1 - omC (Classical.choose h) x y) := by
  simp only [wSmallPair, wSmallScaled, omC, g0]
  ring

/-- `W₂ = W·(1−ω²)` pointwise (the localised form of `w2_eq_w_mul_one_sub_sq`). -/
lemma wSmall_rel_g2 {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u x y : ℝ³) :
    wSmallPair M ℓ d u (g2 v h) x y
      = wSmallPair M ℓ d u v x y * (1 - (omC (Classical.choose h) x y) ^ 2) := by
  simp only [wSmallPair, wSmallScaled, omC, g2, g0]
  ring

/-- `W₂ = W₁ + W₁ω` pointwise (`g₂ = g₀ + g₀·w₀` and linearity in the numerator). -/
lemma wSmall_g2_split {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u x y : ℝ³) :
    wSmallPair M ℓ d u (g2 v h) x y
      = wSmallPair M ℓ d u (g0 v h) x y
        + wSmallPair M ℓ d u (fun z : ℝ³ => g0 v h z * Classical.choose h z) x y := by
  simp only [wSmallPair, wSmallScaled, g2, g0]
  ring

/-- `W₁ω = W₁·ω` pointwise. -/
lemma wSmall_g0w0_eq_mul {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u x y : ℝ³) :
    wSmallPair M ℓ d u (fun z : ℝ³ => g0 v h z * Classical.choose h z) x y
      = wSmallPair M ℓ d u (g0 v h) x y * omC (Classical.choose h) x y := by
  simp only [wSmallPair, wSmallScaled, omC, g0]
  ring

/-- `wSmallPair` is symmetric for an even numerator. -/
lemma wSmall_symm {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : ℝ³) {f : ℝ³ → ℝ}
    (hf : ∀ z : ℝ³, f (-z) = f z) (x y : ℝ³) :
    wSmallPair M ℓ d u f x y = wSmallPair M ℓ d u f y x :=
  Submission.BoseGases.wSmallPair_symm hM u hf x y

/-- `wSmallPair M ℓ d u v ≥ 0` pointwise for `0 ≤ v`. -/
lemma wSmall_v_nonneg {v : ℝ³ → ℝ} (hv : 0 ≤ v) (M : ℕ) (ℓ d : ℝ) (u x y : ℝ³) :
    0 ≤ wSmallPair M ℓ d u v x y := by
  rw [wSmallPair, wSmallScaled, convScaleSmall]
  refine mul_nonneg
    (mul_nonneg (chiSmallB_nonneg M ℓ d u x) ?_)
    (chiSmallB_nonneg M ℓ d u y)
  refine div_nonneg (div_nonneg (hv _) ?_) (convScale_nonneg ℓ _)
  rw [conv3Small]
  exact integral_nonneg fun w =>
    mul_nonneg (chiSmall_nonneg M w) (chiSmall_nonneg M (_ - w))

/-- `0 ≤ W₁` a.e. on the box (from `W₁ = W(1−ω)` and `ω ≤ 1` a.e.). -/
lemma wSmall1_nonneg_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ} {R : ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (d : ℝ) (u : ℝ³) {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      0 ≤ wSmallPair M ℓ d u (g0 v h) (x i) (x j) := by
  have hspec := w0_spec h
  have hb := scattering_bounds_ae hR hv_nonneg hvrad hv_supp hspec.1 hspec.2
  have hle : ∀ᵐ z : ℝ³, Classical.choose h z ≤ 1 := hb.2
  have hpb := ae_pair_pullback (N := N) hℓ hij hle
  filter_upwards [hpb] with x hx
  have hv0 := wSmall_v_nonneg hv_nonneg M ℓ d u (x i) (x j)
  rw [wSmall_rel_g0 h M ℓ d u (x i) (x j)]
  have hx' : omC (Classical.choose h) (x i) (x j) ≤ 1 := by simpa [omC] using hx
  exact mul_nonneg hv0 (by linarith)

/-- `W₁ ≤ W` a.e. on the box (same source). -/
lemma wSmall1_le_w_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ} {R : ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (d : ℝ) (u : ℝ³) {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      wSmallPair M ℓ d u (g0 v h) (x i) (x j) ≤ wSmallPair M ℓ d u v (x i) (x j) := by
  have hspec := w0_spec h
  have hb := scattering_bounds_ae hR hv_nonneg hvrad hv_supp hspec.1 hspec.2
  have hle : ∀ᵐ z : ℝ³, 0 ≤ Classical.choose h z ∧ Classical.choose h z ≤ 1 :=
    hb.1.and hb.2
  have hpb := ae_pair_pullback (N := N) hℓ hij hle
  filter_upwards [hpb] with x hx
  have hv0 := wSmall_v_nonneg hv_nonneg M ℓ d u (x i) (x j)
  rw [wSmall_rel_g0 h M ℓ d u (x i) (x j)]
  have hx' : 0 ≤ omC (Classical.choose h) (x i) (x j)
      ∧ omC (Classical.choose h) (x i) (x j) ≤ 1 := by simpa [omC] using hx
  nlinarith [hv0, hx'.1, hx'.2]

/-- `|W₁ω| ≤ W₁` a.e. (from `W₁ω = W₁·ω`, `0 ≤ W₁`, `|ω| ≤ 1` a.e.). -/
lemma wSmall1w_abs_le_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ} {R : ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (d : ℝ) (u : ℝ³) {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      |wSmallPair M ℓ d u (fun z : ℝ³ => g0 v h z * Classical.choose h z) (x i) (x j)|
        ≤ wSmallPair M ℓ d u (g0 v h) (x i) (x j) := by
  have hspec := w0_spec h
  have hb := scattering_bounds_ae hR hv_nonneg hvrad hv_supp hspec.1 hspec.2
  have hle : ∀ᵐ z : ℝ³, |Classical.choose h z| ≤ 1 := by
    filter_upwards [hb.1, hb.2] with z hz0 hz1
    rw [abs_of_nonneg hz0]; exact hz1
  have hpb := ae_pair_pullback (N := N) hℓ hij hle
  have hnn := wSmall1_nonneg_ae hℓ hR hv_nonneg hvrad hv_supp h M d u hij
  filter_upwards [hpb, hnn] with x hx hxnn
  rw [wSmall_g0w0_eq_mul h M ℓ d u (x i) (x j), abs_mul, abs_of_nonneg hxnn]
  have hx' : |omC (Classical.choose h) (x i) (x j)| ≤ 1 := by simpa [omC] using hx
  calc wSmallPair M ℓ d u (g0 v h) (x i) (x j) * |omC (Classical.choose h) (x i) (x j)|
      ≤ wSmallPair M ℓ d u (g0 v h) (x i) (x j) * 1 :=
        mul_le_mul_of_nonneg_left hx' hxnn
    _ = wSmallPair M ℓ d u (g0 v h) (x i) (x j) := by ring

/-! ## Generic fibre bound -/

/-- **Generic uniform fibre bound of the localised kernel.** For an integrable numerator `f`
supported in `ball 0 R`, the cube fibre of `wSmallPair M ℓ d u f` is bounded uniformly in the
base point `z` (and in `u`) by `(χ·D_M)·(2(χ·D_M)/smallConvLower M)·∫|f|`. -/
theorem wSmallPair_fibre_abs_le_gen {M : ℕ} (hM : 1 ≤ M) {ℓ d R : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {f : ℝ³ → ℝ} (hf : MeasureTheory.Integrable f)
    (hfsupp : ∀ z : ℝ³, R ≤ ‖z‖ → f z = 0) (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * chiR0)
    (u : ℝ³) :
    ∀ z : ℝ³,
      |∫ y in acube ℓ, wSmallPair M ℓ d u f z y| ≤
        (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
              * (∫ w : ℝ³, |f w|)) := by
  intro z
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hD0 : 0 ≤ chiSupAbs * chiSmallDecay M :=
    mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)
  have hK0 : 0 ≤ 2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M :=
    div_nonneg (mul_nonneg (by norm_num) hD0) (le_of_lt hSpos)
  have hchi : chiSmall M ((ℓ * d)⁻¹ • z - u) ≤ chiSmallDecay M :=
    le_trans (le_abs_self _) (chiSmall_decay_coord_le_decay hM _)
  have hA : chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - u) ≤ chiSupAbs * chiSmallDecay M :=
    mul_le_mul_of_nonneg_left hchi chiSupAbs_nonneg
  have hpt : ∀ y : ℝ³, |wSmallPair M ℓ d u f z y| ≤
      (chiSupAbs * chiSmallDecay M)
        * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * |f (z - y)|) := by
    intro y
    have h1 : |wSmallPair M ℓ d u f z y| ≤
        (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - u))
          * ((2 / Work.SmallBoxSliding.smallConvLower M)
              * (chiSupAbs * chiSmallDecay M) * |f (z - y)|) :=
      abs_wSmallPair_le (M := M) hM hℓ hd hfsupp hR hRχ u z y
    have h2 : (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - u))
          * ((2 / Work.SmallBoxSliding.smallConvLower M)
              * (chiSupAbs * chiSmallDecay M) * |f (z - y)|) ≤
        (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
              * |f (z - y)|) := by
      rw [show (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - u))
            * ((2 / Work.SmallBoxSliding.smallConvLower M)
                * (chiSupAbs * chiSmallDecay M) * |f (z - y)|)
          = (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - u))
            * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
                * |f (z - y)|) by ring]
      exact mul_le_mul_of_nonneg_right hA
        (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hD0) (le_of_lt hSpos)) (abs_nonneg _))
    exact le_trans h1 h2
  have hfint : Integrable (fun y : ℝ³ => |f (z - y)|) := by
    simpa only [Real.norm_eq_abs] using hf.abs.comp_sub_left z
  have hGint_vol : Integrable (fun y : ℝ³ =>
      (chiSupAbs * chiSmallDecay M)
        * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * |f (z - y)|)) :=
    (hfint.const_mul
        (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)).const_mul
      (chiSupAbs * chiSmallDecay M)
  have hGint : Integrable (fun y : ℝ³ =>
      (chiSupAbs * chiSmallDecay M)
        * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * |f (z - y)|))
      ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    hGint_vol.mono_measure Measure.restrict_le_self
  have hstep1 : |∫ y in acube ℓ, wSmallPair M ℓ d u f z y| ≤
      ∫ y, ‖wSmallPair M ℓ d u f z y‖ ∂((volume : Measure ℝ³).restrict (acube ℓ)) := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (μ := (volume : Measure ℝ³).restrict (acube ℓ))
        (fun y : ℝ³ => wSmallPair M ℓ d u f z y)
  have hstep2 : (∫ y, ‖wSmallPair M ℓ d u f z y‖ ∂((volume : Measure ℝ³).restrict (acube ℓ))) ≤
      ∫ y, (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * |f (z - y)|) ∂((volume : Measure ℝ³).restrict (acube ℓ)) := by
    refine integral_mono_of_nonneg (ae_of_all _ (fun y => norm_nonneg _)) hGint
      (ae_of_all _ (fun y => ?_))
    simpa only [Real.norm_eq_abs] using hpt y
  have hval : (∫ y, (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * |f (z - y)|) ∂((volume : Measure ℝ³).restrict (acube ℓ)))
      = (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * (∫ y in acube ℓ, |f (z - y)|)) := by
    rw [integral_const_mul, integral_const_mul]
  have hY : (∫ y in acube ℓ, |f (z - y)|) ≤ ∫ w : ℝ³, |f w| := by
    calc (∫ y in acube ℓ, |f (z - y)|) ≤ ∫ y : ℝ³, |f (z - y)| :=
          setIntegral_le_integral hfint (ae_of_all _ (fun y => abs_nonneg _))
      _ = ∫ w : ℝ³, |f w| :=
          integral_sub_left_eq_self (fun w : ℝ³ => |f w|) volume z
  calc |∫ y in acube ℓ, wSmallPair M ℓ d u f z y|
      ≤ ∫ y, ‖wSmallPair M ℓ d u f z y‖ ∂((volume : Measure ℝ³).restrict (acube ℓ)) := hstep1
    _ ≤ ∫ y, (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * |f (z - y)|) ∂((volume : Measure ℝ³).restrict (acube ℓ)) := hstep2
    _ = (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * (∫ y in acube ℓ, |f (z - y)|)) := hval
    _ ≤ (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * (∫ w : ℝ³, |f w|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hK0) hD0

/-! ## The `χ`-weighted fibre constant and its instantiations -/

/-- The `u`-independent fibre constant. -/
noncomputable def wFibC (M : ℕ) (A : ℝ) : ℝ :=
  (chiSupAbs * chiSmallDecay M)
    * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) * A)

/-- `W₁`-fibre bound: `|∫_y W₁(z,y)dy| ≤ wFibC M (8π _root_.BoseGases.a v)`. -/
theorem wSmall1_fibre_abs_le_gen {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRd : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * chiR0) (u : ℝ³) :
    ∀ z : ℝ³, |∫ y in acube ℓ, wSmallPair M ℓ d u (g0 v h) z y| ≤ wFibC M (8 * π * _root_.BoseGases.a v) := by
  intro z
  have hmain := wSmallPair_fibre_abs_le_gen (M := M) hM hℓ hd
    (g0_integrable hR hv_supp h)
    (fun z hz => g0_zero_of_norm_ge hv_supp hz h) hRd hRχ u z
  have hgi : (∫ w : ℝ³, |g0 v h w|) = 8 * π * _root_.BoseGases.a v :=
    Submission.BoseGases.g0_abs_integral hR hv hvrad hv_supp h
  simpa [wFibC, hgi] using hmain

/-- `W₂`-fibre bound: `|∫_y W₂(z,y)dy| ≤ wFibC M (16π _root_.BoseGases.a v)`. -/
theorem wSmall2_fibre_abs_le_gen {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRd : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * chiR0) (u : ℝ³) :
    ∀ z : ℝ³, |∫ y in acube ℓ, wSmallPair M ℓ d u (g2 v h) z y| ≤ wFibC M (16 * π * _root_.BoseGases.a v) := by
  intro z
  have hmain := wSmallPair_fibre_abs_le_gen (M := M) hM hℓ hd
    (g2_integrable hR hv hvrad hv_supp h)
    (fun z hz => g2_zero_of_norm_ge hv_supp hz h) hRd hRχ u z
  have hle : (∫ w : ℝ³, |g2 v h w|) ≤ 16 * π * _root_.BoseGases.a v := by
    have h1 : (∫ w : ℝ³, |g2 v h w|) = ∫ w : ℝ³, g2 v h w := by
      apply integral_congr_ae
      filter_upwards [g2_nonneg_ae hR hv hvrad hv_supp h] with w hw
      exact abs_of_nonneg hw
    rw [h1]
    exact (g2_integral_bounds hR hv hvrad hv_supp h).2
  have hK : 0 ≤ (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) :=
    div_nonneg (mul_nonneg (by norm_num) (mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)))
      (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos M))
  have hD0 : 0 ≤ chiSupAbs * chiSmallDecay M :=
    mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)
  calc |∫ y in acube ℓ, wSmallPair M ℓ d u (g2 v h) z y|
      ≤ wFibC M (∫ w : ℝ³, |g2 v h w|) := by
        simpa [wFibC] using hmain
    _ ≤ wFibC M (16 * π * _root_.BoseGases.a v) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hK) hD0

/-- `W₁ω`-fibre bound: `|∫_y W₁ω(z,y)dy| ≤ wFibC M (8π _root_.BoseGases.a v)`. -/
theorem wSmall1w_fibre_abs_le_gen {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRd : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * chiR0) (u : ℝ³) :
    ∀ z : ℝ³, |∫ y in acube ℓ,
        wSmallPair M ℓ d u (fun z : ℝ³ => g0 v h z * Classical.choose h z) z y|
      ≤ wFibC M (8 * π * _root_.BoseGases.a v) := by
  intro z
  have hfg : MeasureTheory.Integrable (fun z : ℝ³ => g0 v h z * Classical.choose h z) :=
    g0w0_integrable hR hv hvrad hv_supp h
  have hmain := wSmallPair_fibre_abs_le_gen (M := M) hM hℓ hd hfg
    (fun z hz => by simp [g0_zero_of_norm_ge hv_supp hz h]) hRd hRχ u z
  have hb := scattering_bounds_ae hR hv hvrad hv_supp (w0_spec h).1 (w0_spec h).2
  have hle : (∫ w : ℝ³, |(g0 v h * Classical.choose h) w|) ≤ 8 * π * _root_.BoseGases.a v := by
    have hpt : ∀ᵐ w : ℝ³, |g0 v h w * Classical.choose h w| ≤ |g0 v h w| := by
      filter_upwards [hb.1, hb.2] with w hw0 hw1
      rw [abs_mul]
      have h1 : |Classical.choose h w| ≤ 1 := by
        rw [abs_of_nonneg hw0]; exact hw1
      calc |g0 v h w| * |Classical.choose h w| ≤ |g0 v h w| * 1 :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |g0 v h w| := by ring
    calc (∫ w : ℝ³, |(g0 v h * Classical.choose h) w|)
        ≤ ∫ w : ℝ³, |g0 v h w| := by
          refine integral_mono_ae hfg.abs (g0_integrable hR hv_supp h).abs ?_
          filter_upwards [hpt] with w hw
          simpa using hw
      _ = 8 * π * _root_.BoseGases.a v := Submission.BoseGases.g0_abs_integral hR hv hvrad hv_supp h
  have hK : 0 ≤ (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) :=
    div_nonneg (mul_nonneg (by norm_num) (mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)))
      (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos M))
  have hD0 : 0 ≤ chiSupAbs * chiSmallDecay M :=
    mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)
  calc |∫ y in acube ℓ, wSmallPair M ℓ d u (fun z : ℝ³ => g0 v h z * Classical.choose h z) z y|
      ≤ wFibC M (∫ w : ℝ³, |(g0 v h * Classical.choose h) w|) := by
        simpa [wFibC] using hmain
    _ ≤ wFibC M (8 * π * _root_.BoseGases.a v) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hK) hD0

/-! ## Slot integrability for continuous slot factors -/

/-- The localised slot integrand `S x · wSmallPair M ℓ d u f (x i) (x j)` is `IntegrableOn` the
box for a continuous `S` and an integrable, supported numerator `f`. -/
lemma integrableOn_slot_wSmallPair_cont {N : ℕ} {ℓ d R : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {f : ℝ³ → ℝ} (hf : MeasureTheory.Integrable f)
    (hfsupp : ∀ z : ℝ³, R ≤ ‖z‖ → f z = 0)
    {M : ℕ} (hM : 1 ≤ M) (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * chiR0)
    (u : ℝ³) {i j : Fin N} (hij : i ≠ j)
    {S : X N → ℝ} (hSc : Continuous S) :
    MeasureTheory.IntegrableOn (fun x : X N => S x * wSmallPair M ℓ d u f (x i) (x j))
      (abox N ℓ) MeasureTheory.volume := by
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := S) hSc.continuousOn
  have hB0 : 0 ≤ B := by
    have hb := hB (0 : X N) (zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg (S (0 : X N))) hb
  refine integrableOn_slot_wSmallPair hℓ hd hf hfsupp hM hR hRχ u hij
    hSc.aestronglyMeasurable hB0 ?_
  rw [ae_restrict_iff' (abox_measurable N ℓ)]
  exact ae_of_all volume (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx)

end Work.BoseFixB1
