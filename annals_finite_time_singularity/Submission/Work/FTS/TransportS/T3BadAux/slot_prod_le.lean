import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.T3BadAux.slot_slice_le
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T3BadAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `T3BadAux/slot_prod_le`: the per-slot bound on the product measure

`Work.FTS.TransportS.gK α f g k` is the `k`-th order-five summand of the `D_z`-transport
pairing.  The one-dimensional content of its bound is `slot_slice_le`
(`T3BadAux/slot_slice_le.lean`): for every interior angle `θ`,

`|∫_z gK α f g k z θ| ≤ 2 Mf ∫_z (Xz α g k z θ)²`

whenever `|f| ≤ Mf`, `|D_z f| ≤ Mf`, `z (Thard g k z θ w(z))² → 0` at `0⁺` and at `+∞`, and
the three slice integrands are integrable.  This file removes those slice hypotheses: they
hold for a.e. `θ` as soon as `f` is `C^∞` on the open quadrant, `g` is `C^∞` there
(`SmoothQuad`) and `g ∈ ℋ⁴ ∩ ℋ⁵`, because every slice integrand is either continuous in `z`
or dominated (through `T3BadAux/`Basic`.`Thard_sq_le_hk`/`DzThard_sq_le_hk`) by the `z`-slice
of the product-integrable `HkIntegrand`'s.

The final step is Fubini: with `μ = volume.restrict Iz`, `ν = volume.restrict Iθ`, the
product integral is the iterated integral in either order, so the a.e. slice bound integrates
up to

`|∫∫ gK α f g k| ≤ 2 Mf ∫∫ (Xz α g k)²`.
-/

/-! ## The two restricted radial measures agree -/

/-- `volume.restrict Iz = volume.restrict (0,∞)`: the two differ only at the null point `0`. -/
theorem restrict_Iz_eq_Ioi :
    (MeasureTheory.volume.restrict Work.Spaces.Iz : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm

/-- `IntegrableOn` over `Iz = [0,∞)` and over `(0,∞)` are the same, the two sets differing
by a null set. -/
theorem integrableOn_Ioi_iff_Iz {h : ℝ → ℝ} :
    MeasureTheory.IntegrableOn h (Set.Ioi (0 : ℝ)) ↔
      MeasureTheory.IntegrableOn h Work.Spaces.Iz := by
  simp only [MeasureTheory.IntegrableOn, restrict_Iz_eq_Ioi]

/-! ## Measurability of the radial slices -/

/-- The `z`-slice at a fixed interior angle is a.e. strongly measurable as soon as the
uncurried function is continuous on the open quadrant `(0,∞) × (0,π/2)`. -/
theorem aesm_zslice_of_continuousOn_Qd (G : ℝ × ℝ → ℝ)
    (hG : ContinuousOn G Work.FTS.LocData.Qd) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    MeasureTheory.AEStronglyMeasurable (fun z => G (z, θ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  (hG.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hz => ⟨hz, hθ⟩)).aestronglyMeasurable measurableSet_Ioi

/-! ## Positivity of the angular slot weight -/

/-- The angular weight of the `k`-th hard slot is positive at every interior angle (it is
`sin(2θ)^{-η}` for `k = 0` and `sin(2θ)^{-γ}` otherwise, and `sin(2θ) > 0` on `(0,π/2)`). -/
theorem sghard_pos' {α : ℝ} (k : Fin 5) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Work.FTS.H2.sghard α k θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk0 : k = 0 := Fin.ext hk
    rw [hk0, Work.FTS.H2.sghard_apply_zero α θ]
    exact Real.rpow_pos_of_pos hsin _
  · rw [Work.FTS.H2.sghard_apply_ne α k hk θ]
    exact Real.rpow_pos_of_pos hsin _

/-! ## The two weighted-square slot bounds -/

/-- `(Thard g k)² w² ≤ HkIntegrand α 4 g / sghard α k` at an interior angle. -/
theorem thard_sq_mul_w_sq_le (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.FTS.H2.Thard g k z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ / Work.FTS.H2.sghard α k θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs := sghard_pos' (α := α) k hθ
  rw [le_div_iff₀ hs]
  rw [show (Work.FTS.H2.Thard g k z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.H2.sghard α k θ
      = (Work.FTS.H2.Thard g k z θ) ^ 2 * Work.FTS.H2.sghard α k θ * (Work.Spaces.w z) ^ 2
      from by ring]
  exact Thard_sq_le_hk α g k hθI

/-- `(D_z (Thard g k))² w² ≤ HkIntegrand α 5 g / sghard α k` at an interior angle. -/
theorem dzthard_sq_mul_w_sq_le (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 5 g z θ / Work.FTS.H2.sghard α k θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs := sghard_pos' (α := α) k hθ
  rw [le_div_iff₀ hs]
  rw [show (Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.H2.sghard α k θ
      = (Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2 * Work.FTS.H2.sghard α k θ
        * (Work.Spaces.w z) ^ 2 from by ring]
  exact DzThard_sq_le_hk α g k hθI

/-! ## The AM–GM estimate -/

/-- `|a b| ≤ (a² + b²)/2`. -/
theorem abs_mul_le_half_sq_add (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  have h := two_mul_le_add_sq |a| |b|
  rw [sq_abs a, sq_abs b] at h
  linarith

/-- **The pointwise domination of the `H1` slice integrand.**  With `S = sghard α k θ` and
`m = mixed (5 - k) k g` one has `z ∂_z(Thard g k) = D_z(Thard g k) = m`, so the integrand of
the radial integration by parts is `|f · m · w² · Thard|`, which AM–GM turns into the sum of
the two weighted squares of the order-four and order-five slots. -/
theorem slot_H1_le {α Mf : ℝ} (hMf : 0 ≤ Mf) {f g : ℝ → ℝ → ℝ} (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hf : |f z θ| ≤ Mf) :
    |f z θ * Work.Spaces.mixed (5 - k.val) k.val g z θ * (Work.Spaces.w z) ^ 2
        * Work.FTS.H2.Thard g k z θ|
      ≤ (Mf / 2) * ((Work.Spaces.HkIntegrand α 4 g z θ + Work.Spaces.HkIntegrand α 5 g z θ)
          / Work.FTS.H2.sghard α k θ) := by
  have hT := thard_sq_mul_w_sq_le α g k (z := z) hθ
  have hD := dzthard_sq_mul_w_sq_le α g k (z := z) hθ
  have hT' : (Work.Spaces.w z * Work.FTS.H2.Thard g k z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ / Work.FTS.H2.sghard α k θ := by
    rw [show (Work.Spaces.w z * Work.FTS.H2.Thard g k z θ) ^ 2
        = (Work.FTS.H2.Thard g k z θ) ^ 2 * (Work.Spaces.w z) ^ 2 from by ring]
    exact hT
  have hD' : (Work.Spaces.w z * (Work.Spaces.mixed (5 - k.val) k.val g z θ)) ^ 2
      ≤ Work.Spaces.HkIntegrand α 5 g z θ / Work.FTS.H2.sghard α k θ := by
    rw [show (Work.Spaces.w z * Work.Spaces.mixed (5 - k.val) k.val g z θ) ^ 2
        = (Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 from by
      rw [Work.FTS.TransportS.Dz_Thard_apply]
      ring]
    exact hD
  have hstep : |(Work.Spaces.w z * Work.FTS.H2.Thard g k z θ)
        * (Work.Spaces.w z * Work.Spaces.mixed (5 - k.val) k.val g z θ)|
      ≤ ((Work.Spaces.HkIntegrand α 4 g z θ + Work.Spaces.HkIntegrand α 5 g z θ)
          / Work.FTS.H2.sghard α k θ) / 2 := by
    refine le_trans (abs_mul_le_half_sq_add _ _) ?_
    refine div_le_div_of_nonneg_right ?_ (by norm_num : (0 : ℝ) ≤ 2)
    rw [add_div]
    exact add_le_add hT' hD'
  rw [show f z θ * Work.Spaces.mixed (5 - k.val) k.val g z θ * (Work.Spaces.w z) ^ 2
        * Work.FTS.H2.Thard g k z θ
      = f z θ * ((Work.Spaces.w z * Work.FTS.H2.Thard g k z θ)
          * (Work.Spaces.w z * Work.Spaces.mixed (5 - k.val) k.val g z θ)) from by ring,
    abs_mul]
  calc |f z θ| * |(Work.Spaces.w z * Work.FTS.H2.Thard g k z θ)
          * (Work.Spaces.w z * Work.Spaces.mixed (5 - k.val) k.val g z θ)|
      ≤ Mf * (((Work.Spaces.HkIntegrand α 4 g z θ + Work.Spaces.HkIntegrand α 5 g z θ)
          / Work.FTS.H2.sghard α k θ) / 2) := mul_le_mul hf hstep (abs_nonneg _) hMf
    _ = (Mf / 2) * ((Work.Spaces.HkIntegrand α 4 g z θ + Work.Spaces.HkIntegrand α 5 g z θ)
          / Work.FTS.H2.sghard α k θ) := by ring

/-- **The pointwise domination of the `gK'` slice integrand**: the same estimate as in
`slot_slice_le`, but with the majorant `HkIntegrand α 4 g / sghard α k` (a.e. integrable in
`z`) instead of the slice quantity `(Xz α g k)²/sghard`. -/
theorem slot_gKprime_le {α Mf : ℝ} (hMf : 0 ≤ Mf) {f g : ℝ → ℝ → ℝ} (k : Fin 5) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hf : |f z θ| ≤ Mf) (hDzf : |Work.Spaces.Dz f z θ| ≤ Mf) :
    |Work.FTS.TransportS.gK' α f g k z θ|
      ≤ 4 * Mf * (Work.Spaces.HkIntegrand α 4 g z θ / Work.FTS.H2.sghard α k θ) := by
  have hT := thard_sq_mul_w_sq_le α g k (z := z) hθ
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hratio : |(z - 3) / (1 + z)| ≤ 3 := Work.FTS.H2.abs_ratio_le_three z hz
  have h2 : |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2|
      ≤ Mf * (Work.Spaces.w z) ^ 2 := by
    rw [show Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
          = (Work.Spaces.pz f z θ * z) * (Work.Spaces.w z) ^ 2 from by ring,
      abs_mul, abs_of_nonneg hw2,
      show |Work.Spaces.pz f z θ * z| = |Work.Spaces.Dz f z θ| from by
        rw [Work.Spaces.Dz, mul_comm]]
    exact mul_le_mul_of_nonneg_right hDzf hw2
  have h3 : |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
      ≤ 3 * Mf * (Work.Spaces.w z) ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw2]
    calc |f z θ| * ((Work.Spaces.w z) ^ 2 * |(z - 3) / (1 + z)|)
        ≤ Mf * ((Work.Spaces.w z) ^ 2 * 3) :=
          mul_le_mul hf (mul_le_mul_of_nonneg_left hratio hw2)
            (mul_nonneg hw2 (abs_nonneg _)) hMf
      _ = 3 * Mf * (Work.Spaces.w z) ^ 2 := by ring
  have h1 : |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
        + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
      ≤ 4 * Mf * (Work.Spaces.w z) ^ 2 := by
    calc |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
          + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
        ≤ |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2|
          + |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))| := abs_add_le _ _
      _ ≤ Mf * (Work.Spaces.w z) ^ 2 + 3 * Mf * (Work.Spaces.w z) ^ 2 := add_le_add h2 h3
      _ = 4 * Mf * (Work.Spaces.w z) ^ 2 := by ring
  rw [show Work.FTS.TransportS.gK' α f g k z θ
      = (Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
          + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
        * (Work.FTS.H2.Thard g k z θ) ^ 2 from rfl,
    abs_mul, abs_of_nonneg (sq_nonneg (Work.FTS.H2.Thard g k z θ))]
  calc |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
        + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
        * (Work.FTS.H2.Thard g k z θ) ^ 2
      ≤ (4 * Mf * (Work.Spaces.w z) ^ 2) * (Work.FTS.H2.Thard g k z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = 4 * Mf * ((Work.FTS.H2.Thard g k z θ) ^ 2 * (Work.Spaces.w z) ^ 2) := by ring
    _ ≤ 4 * Mf * (Work.Spaces.HkIntegrand α 4 g z θ / Work.FTS.H2.sghard α k θ) :=
        mul_le_mul_of_nonneg_left hT (by linarith)

/-! ## Joint continuity of the slice integrands -/


/-! ## The a.e. radial slice bound -/


/-! ## The product-measure bound -/


end Work.FTS.TransportS.T3BadAux
