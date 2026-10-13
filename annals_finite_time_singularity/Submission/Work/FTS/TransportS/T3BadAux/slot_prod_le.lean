import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.FTS.TransportS.T3BadAux.slot_slice_le
import Submission.Work.FTS.TransportS.T3BadAux.Basic
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs

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

/-- The rewritten `H1` integrand `f · mixed (5-k) k g · w² · Thard g k` of the radial
integration by parts is continuous on the open quadrant. -/
theorem continuousOn_slotH1_Qd {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.LocData.SmoothQuad g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * Work.Spaces.mixed (5 - k.val) k.val g p.1 p.2
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.Thard g k p.1 p.2) Work.FTS.LocData.Qd :=
  ((((hsf.continuousOn).mono fun p hp => hp).mul
      (Work.FTS.TransportS.continuousOn_mixed_Qd hsg (5 - k.val) k.val)).mul
    (Work.FTS.TransportS.continuousOn_w_sq_Qd.mul
      (Work.FTS.TransportS.continuousOn_Thard_Qd hsg k))).congr fun p _ => by
    simp only [Pi.mul_apply]
    rw [show Function.uncurry f p = f p.1 p.2 from rfl]
    ring

/-! ## The a.e. radial slice bound -/

/-- **The radial slice bound for a.e. angle.**  All the slice hypotheses of `slot_slice_le`
hold for a.e. `θ ∈ Iθ`:  the two smoothness conditions come from `SmoothOpen`/`SmoothQuad`,
the boundary conditions are the hypothesis `htr`, and the three integrability conditions
follow from the product-integrability of `HkIntegrand α 4 g`, `HkIntegrand α 5 g` and
`(Xz α g k)²` together with the pointwise dominations `slot_H1_le`, `slot_gKprime_le`. -/
theorem slot_slice_le_ae {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.LocData.SmoothQuad g)
    (hm4 : Work.Spaces.HkMem α 4 g) (hm5 : Work.Spaces.HkMem α 5 g)
    (hfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ Mf)
    (hDfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Dz f z θ| ≤ Mf)
    (htr : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)|
        ≤ 2 * Mf * ∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  -- a.e. integrability of the radial slices of the `ℋ⁴`/`ℋ⁵` integrands
  have h4 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 4 g z θ)
        (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.TransportS.ae_integrableOn_slice
      (H := fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      (Work.FTS.TransportS.integrable_HkIntegrand_prod hsg hm4).1
    filter_upwards [h] with θ hθ
    exact (integrableOn_Ioi_iff_Iz).mpr hθ
  have h5 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 5 g z θ)
        (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.TransportS.ae_integrableOn_slice
      (H := fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 5 g p.1 p.2)
      (Work.FTS.TransportS.integrable_HkIntegrand_prod hsg hm5).1
    filter_upwards [h] with θ hθ
    exact (integrableOn_Ioi_iff_Iz).mpr hθ
  have hX2 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => (Work.FTS.TransportS.Xz α g k z θ) ^ 2)
        (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.TransportS.ae_integrableOn_slice
      (H := fun p : ℝ × ℝ => (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2)
      (Work.FTS.TransportS.integrable_Xz_sq hsg hm4 k)
    filter_upwards [h] with θ hθ
    exact (integrableOn_Ioi_iff_Iz).mpr hθ
  filter_upwards [Work.FTS.TransportS.ae_mem_Ioo_Iθ, h4, h5, hX2] with θ hθ hI4 hI5 hIX2
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hmem : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) → z ∈ Work.Spaces.Iz :=
    fun z hz => by simp only [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
  have hfbI : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) → |f z θ| ≤ Mf :=
    fun z hz => hfb z (hmem z hz) θ hθI
  have hDfbI : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) → |Work.Spaces.Dz f z θ| ≤ Mf :=
    fun z hz => hDfb z (hmem z hz) θ hθI
  -- the two smoothness conditions
  have hφcd : ContDiffOn ℝ 1 (fun z => f z θ) (Set.Ioi (0 : ℝ)) :=
    (hsf.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hucd : ContDiffOn ℝ 1 (fun z => Work.FTS.H2.Thard g k z θ) (Set.Ioi (0 : ℝ)) := by
    rw [Work.FTS.H2.Thard_eq_mixed g k]
    exact ((hsg.mixed (4 - k.val) k.val).curry_z hθ).mono
      (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) |>.of_le
        (by simp [Work.Stability.smoothOrder])
  -- the first integrability condition: rewrite `z ∂_z(Thard g k)` as `mixed (5-k) k g`
  have hint1 : MeasureTheory.IntegrableOn (fun z => f z θ * z * (Work.Spaces.w z) ^ 2
      * Work.FTS.H2.Thard g k z θ * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
      (Set.Ioi (0 : ℝ)) := by
    have hEq : (fun z => f z θ * z * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ
        * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
        = fun z => f z θ * Work.Spaces.mixed (5 - k.val) k.val g z θ
          * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ := by
      funext z
      have h : z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
          = Work.Spaces.mixed (5 - k.val) k.val g z θ := by
        rw [← Work.FTS.TransportS.Dz_Thard_apply g k z θ]
        rfl
      calc f z θ * z * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ
            * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
          = f z θ * (z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
            * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ := by ring
        _ = f z θ * Work.Spaces.mixed (5 - k.val) k.val g z θ
            * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ := by rw [h]
    rw [hEq]
    refine MeasureTheory.Integrable.mono'
      (((hI4.add hI5).div_const (Work.FTS.H2.sghard α k θ)).const_mul (Mf / 2))
      (aesm_zslice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => f p.1 p.2 * Work.Spaces.mixed (5 - k.val) k.val g p.1 p.2
          * (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.Thard g k p.1 p.2)
        (continuousOn_slotH1_Qd hsf hsg k) hθ) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs]
    exact slot_H1_le (α := α) (Mf := Mf) hMf k hθ (hfbI z hz)
  -- the second integrability condition
  have hint2 : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.TransportS.gK' α f g k z θ) (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.mono'
      ((hI4.div_const (Work.FTS.H2.sghard α k θ)).const_mul (4 * Mf))
      (aesm_zslice_of_continuousOn_Qd _
        (Work.FTS.TransportS.continuousOn_gK'_Qd hsf hsg k) hθ) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs]
    exact slot_gKprime_le (α := α) (Mf := Mf) hMf k hz hθ (hfbI z hz) (hDfbI z hz)
  have hkey : |∫ z in Set.Ioi (0 : ℝ), Work.FTS.TransportS.gK α f g k z θ|
      ≤ 2 * Mf * ∫ z in Set.Ioi (0 : ℝ), (Work.FTS.TransportS.Xz α g k z θ) ^ 2 :=
    slot_slice_le (α := α) (Mf := Mf) (f := f) (g := g) k hMf hθ hφcd hucd
      (fun z hz => hfb z hz θ hθI) (fun z hz => hDfb z hz θ hθI)
      (htr θ hθ).1 (htr θ hθ).2 hint1 hint2 hIX2
  rw [restrict_Iz_eq_Ioi]
  exact hkey

/-! ## The product-measure bound -/

theorem slot_prod_le {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.LocData.SmoothQuad g)
    (hm4 : Work.Spaces.HkMem α 4 g) (hm5 : Work.Spaces.HkMem α 5 g)
    (hfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ Mf)
    (hDfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Dz f z θ| ≤ Mf)
    (htr : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)) :
    |∫ p, Work.FTS.TransportS.gK α f g k p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ 2 * Mf * ∫ p, (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hfb' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |f z θ| ≤ Mf :=
    fun z θ hz hθ hθ' => hfb z (le_of_lt hz) θ ⟨le_of_lt hθ, le_of_lt hθ'⟩
  have hΦ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.TransportS.gK α f g k p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.TransportS.integrable_gK hsf hsg hm5 hMf hfb' k
  have hΨ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.TransportS.integrable_Xz_sq hsg hm4 k
  have hΦc : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.FTS.TransportS.gK α f g k z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hΦ
  have hΨc : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.FTS.TransportS.Xz α g k z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hΨ
  have hslice := slot_slice_le_ae (α := α) (Mf := Mf) (f := f) (g := g) k hMf
    hsf hsg hm4 hm5 hfb hDfb htr
  have hmΦ : MeasureTheory.Integrable
      (fun θ => ∫ z, Work.FTS.TransportS.gK α f g k z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hΦ.integral_prod_right
  have hmΨ : MeasureTheory.Integrable
      (fun θ => ∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hΨ.integral_prod_right
  have hL : (∫ p, Work.FTS.TransportS.gK α f g k p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ θ, ∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integral_integral hΦc).symm.trans
      (MeasureTheory.integral_integral_swap hΦc)
  have hR : (∫ p, (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ θ, ∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integral_integral hΨc).symm.trans
      (MeasureTheory.integral_integral_swap hΨc)
  rw [hL, ← Real.norm_eq_abs]
  calc ‖∫ θ, ∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖
      ≤ ∫ θ, ‖∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ θ, 2 * Mf * (∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integral_mono_ae hmΦ.norm (hmΨ.const_mul (2 * Mf)) hslice
    _ = 2 * Mf * ∫ θ, (∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integral_const_mul (2 * Mf) _
    _ = 2 * Mf * ∫ p, (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [hR]

end Work.FTS.TransportS.T3BadAux
