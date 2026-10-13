/-
Copyright: work module for the Elgindi finite-time singularity project.

# `sliceSourceMassBound_of_external`

`Work.FTS.EllipticEst.H2W.SliceSourceMassBound Ψ` (the locally uniform `L¹`-bound on the
source `Lzero1 (∂_z^mΨ(z,·))` together with the `π/4`-data of the four slices `m ≤ 3`)
follows from the *external* input `Work.FTS.EllipticEst.H2W.SliceMassExternal α F Ψ` for a
datum of the weak class `WeakPos2 α F Ψ` (`0 < α ≤ 1/4`).

The route: for a.e. `z₀` the external input gives a neighbourhood on which the
`sinθcos²θ`-weighted `L¹` masses of the slices `∂_z^kΨ` (`k ≤ 5`) and of the `D_z`-slices of
the source (`j ≤ 3`) are bounded by a single constant `C₀`, and the `θ`-slices of `Ψ` are
`C^∞` on `(0,π/2)`, so the `π/4`-data is bounded on the compact interval by continuity.  The
identity `Lzero (∂_z^mΨ) = ∂_z^mF + α²z²∂_z^{m+2}Ψ + … ` (`lzeroPzIterExpansion`) then bounds
the source's slice mass by `C₀` times a constant depending only on the neighbourhood, and the
`D_z`-mass of the source is converted to the `∂_z`-slices by `pzIterEqInvPowDzIter`.

-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.pzIterSliceGrowth3LocReduction
import Submission.Work.FTS.EllipticEst.H2W.SliceMassExternal
import Submission.Work.FTS.EllipticEst.H2W.pzIterEqInvPowDzIter
import Submission.Work.FTS.H2.Q.Base
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-! ### STUBS for the two delegated lemmas (will become imports) -/

/-! ### 1. Small helpers -/

theorem SSMB_volume_Iθ_toReal : (volume Work.Spaces.Iθ).toReal = Real.pi / 2 := by
  rw [Work.Spaces.Iθ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

theorem SSMB_integral_const_Iθ (c : ℝ) : (∫ θ in Work.Spaces.Iθ, c) = Real.pi / 2 * c := by
  rw [MeasureTheory.integral_const]
  show ((volume.restrict Work.Spaces.Iθ) Set.univ).toReal • c = Real.pi / 2 * c
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, SSMB_volume_Iθ_toReal]
  ring

theorem SSMB_sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have h2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  simp only [Work.Elliptic.sinCos2]
  positivity

theorem SSMB_ae_sinCos2_nonneg :
    ∀ᵐ θ ∂(Measure.restrict volume Work.Spaces.Iθ), 0 ≤ Work.Elliptic.sinCos2 θ :=
  MeasureTheory.ae_restrict_of_forall_mem
    (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) (fun θ hθ => SSMB_sinCos2_nonneg_Iθ hθ)

theorem SSMB_continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  show Continuous fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

theorem SSMB_restrict_Ioo_eq_restrict_Iθ :
    Measure.restrict volume (Set.Ioo 0 (Real.pi / 2)) = Measure.restrict volume Work.Spaces.Iθ := by
  refine Measure.restrict_congr_set ?_
  show Set.Ioo 0 (Real.pi / 2) =ᵐ[volume] Set.Icc 0 (Real.pi / 2)
  exact MeasureTheory.Ioo_ae_eq_Icc

theorem SSMB_continuousOn_pzIter_slice {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z : ℝ} (hz : 0 < z) (k : ℕ) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.pzIter k G z θ) (Set.Ioo 0 (Real.pi / 2)) :=
  ((hG.pzIter k).curry_θ hz).continuousOn

theorem SSMB_aesm_pzIter_slice {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z : ℝ} (hz : 0 < z) (k : ℕ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.pzIter k G z θ)
      (Measure.restrict volume Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.pzIter k G z θ)
      (Measure.restrict volume (Set.Ioo 0 (Real.pi / 2))) :=
    (SSMB_continuousOn_pzIter_slice hG hz k).aestronglyMeasurable measurableSet_Ioo
  rwa [SSMB_restrict_Ioo_eq_restrict_Iθ] at h1

theorem SSMB_aesm_abs_pzIter_slice_Iθ {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z : ℝ} (hz : 0 < z) (k : ℕ) :
    AEStronglyMeasurable (fun θ : ℝ => |Work.Spaces.pzIter k G z θ|)
      (Measure.restrict volume Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable (fun θ : ℝ => |Work.Spaces.pzIter k G z θ|)
      (Measure.restrict volume (Set.Ioo 0 (Real.pi / 2))) :=
    ((SSMB_continuousOn_pzIter_slice hG hz k).abs).aestronglyMeasurable measurableSet_Ioo
  rwa [SSMB_restrict_Ioo_eq_restrict_Iθ] at h1

theorem SSMB_abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor <;> linarith [neg_abs_le a, le_abs_self a, neg_abs_le b, le_abs_self b]

/-! ### 2. The `∂_z`-slices of the source, bounded by the `D_z`-slices -/

theorem SSMB_pzIterF_abs_le {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z δ θ : ℝ} (hz : 0 < z) (hδ0 : 0 < δ) (hδz : δ ≤ z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (m : ℕ) (hm : m ≤ 3) :
    |Work.Spaces.pzIter m F z θ|
      ≤ 6 * (1 + δ⁻¹ + (δ⁻¹) ^ 2 + (δ⁻¹) ^ 3) *
        (|Work.Spaces.DzIter 0 F z θ| + |Work.Spaces.DzIter 1 F z θ|
          + |Work.Spaces.DzIter 2 F z θ| + |Work.Spaces.DzIter 3 F z θ|) := by
  obtain ⟨h0, h1, h2, h3⟩ := pzIterEqInvPowDzIter hF hz hθ
  have hzs : 0 ≤ z⁻¹ := (inv_pos.mpr hz).le
  have hds : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ0).le
  set x : ℝ := δ⁻¹ with hx
  have hx0 : 0 ≤ x := by rw [hx]; exact hds
  have e1 : z⁻¹ ≤ x := by rw [hx]; rw [inv_le_inv₀ hz hδ0]; exact hδz
  have e2 : z⁻¹ ^ 2 ≤ x ^ 2 := by nlinarith [e1, hzs, hx0]
  have e3 : z⁻¹ ^ 3 ≤ x ^ 3 := by nlinarith [e1, hzs, hx0]
  set K : ℝ := 6 * (1 + x + x ^ 2 + x ^ 3) with hK
  have hK1 : 1 ≤ K := by rw [hK]; nlinarith [hx0]
  have hKnn : 0 ≤ K := by rw [hK]; nlinarith [hx0]
  have hKd1 : x ≤ K := by rw [hK]; nlinarith [hx0]
  have hKd2 : x ^ 2 ≤ K := by rw [hK]; nlinarith [hx0]
  have hKd3 : x ^ 3 ≤ K := by rw [hK]; nlinarith [hx0]
  set Dsum : ℝ := |Work.Spaces.DzIter 0 F z θ| + |Work.Spaces.DzIter 1 F z θ|
    + |Work.Spaces.DzIter 2 F z θ| + |Work.Spaces.DzIter 3 F z θ| with hDs
  have hDsnn : 0 ≤ Dsum := by
    rw [hDs]; linarith [abs_nonneg (Work.Spaces.DzIter 0 F z θ),
      abs_nonneg (Work.Spaces.DzIter 1 F z θ), abs_nonneg (Work.Spaces.DzIter 2 F z θ),
      abs_nonneg (Work.Spaces.DzIter 3 F z θ)]
  have hDs0 : |Work.Spaces.DzIter 0 F z θ| ≤ Dsum := by
    rw [hDs]; linarith [abs_nonneg (Work.Spaces.DzIter 1 F z θ),
      abs_nonneg (Work.Spaces.DzIter 2 F z θ), abs_nonneg (Work.Spaces.DzIter 3 F z θ)]
  have hDs1 : |Work.Spaces.DzIter 1 F z θ| ≤ Dsum := by
    rw [hDs]; linarith [abs_nonneg (Work.Spaces.DzIter 0 F z θ),
      abs_nonneg (Work.Spaces.DzIter 2 F z θ), abs_nonneg (Work.Spaces.DzIter 3 F z θ)]
  have hDs2 : |Work.Spaces.DzIter 2 F z θ| ≤ Dsum := by
    rw [hDs]; linarith [abs_nonneg (Work.Spaces.DzIter 0 F z θ),
      abs_nonneg (Work.Spaces.DzIter 1 F z θ), abs_nonneg (Work.Spaces.DzIter 3 F z θ)]
  have hDs3 : |Work.Spaces.DzIter 3 F z θ| ≤ Dsum := by
    rw [hDs]; linarith [abs_nonneg (Work.Spaces.DzIter 0 F z θ),
      abs_nonneg (Work.Spaces.DzIter 1 F z θ), abs_nonneg (Work.Spaces.DzIter 2 F z θ)]
  have hgoal : K * Dsum = K * (|Work.Spaces.DzIter 0 F z θ| + |Work.Spaces.DzIter 1 F z θ|
      + |Work.Spaces.DzIter 2 F z θ| + |Work.Spaces.DzIter 3 F z θ|) := by
    rw [hDs]
  interval_cases m
  · rw [h0, ← hgoal]
    calc |Work.Spaces.DzIter 0 F z θ| ≤ Dsum := hDs0
      _ = 1 * Dsum := by ring
      _ ≤ K * Dsum := mul_le_mul_of_nonneg_right hK1 hDsnn
  · rw [h1, ← hgoal]
    have hstep : |z⁻¹ * Work.Spaces.DzIter 1 F z θ|
        = z⁻¹ * |Work.Spaces.DzIter 1 F z θ| := by
      rw [abs_mul, abs_of_nonneg hzs]
    rw [hstep]
    calc z⁻¹ * |Work.Spaces.DzIter 1 F z θ| ≤ x * Dsum :=
          mul_le_mul e1 hDs1 (abs_nonneg _) hx0
      _ ≤ K * Dsum := mul_le_mul_of_nonneg_right hKd1 hDsnn
  · rw [h2, ← hgoal]
    have hstep : |z⁻¹ ^ 2 * (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)|
        = z⁻¹ ^ 2 * |Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (z⁻¹))]
    rw [hstep]
    have htri : |Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ| ≤ Dsum := by
      refine le_trans (SSMB_abs_sub_le_abs_add _ _) ?_
      rw [hDs]
      linarith [abs_nonneg (Work.Spaces.DzIter 0 F z θ), abs_nonneg (Work.Spaces.DzIter 3 F z θ)]
    calc z⁻¹ ^ 2 * |Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ|
        ≤ x ^ 2 * Dsum := mul_le_mul e2 htri (abs_nonneg _) (sq_nonneg _)
      _ ≤ K * Dsum := mul_le_mul_of_nonneg_right hKd2 hDsnn
  · rw [h3, ← hgoal]
    have hstep : |z⁻¹ ^ 3 * (Work.Spaces.DzIter 3 F z θ - 3 * Work.Spaces.DzIter 2 F z θ
          + 2 * Work.Spaces.DzIter 1 F z θ)|
        = z⁻¹ ^ 3 * |Work.Spaces.DzIter 3 F z θ - 3 * Work.Spaces.DzIter 2 F z θ
            + 2 * Work.Spaces.DzIter 1 F z θ| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z⁻¹ ^ 3)]
    rw [hstep]
    have htri : |Work.Spaces.DzIter 3 F z θ - 3 * Work.Spaces.DzIter 2 F z θ
        + 2 * Work.Spaces.DzIter 1 F z θ| ≤ 6 * Dsum := by
      have h4 : |Work.Spaces.DzIter 3 F z θ - 3 * Work.Spaces.DzIter 2 F z θ
          + 2 * Work.Spaces.DzIter 1 F z θ|
          ≤ |Work.Spaces.DzIter 3 F z θ| + 3 * |Work.Spaces.DzIter 2 F z θ|
            + 2 * |Work.Spaces.DzIter 1 F z θ| := by
        have h5 : |Work.Spaces.DzIter 3 F z θ - 3 * Work.Spaces.DzIter 2 F z θ|
            ≤ |Work.Spaces.DzIter 3 F z θ| + 3 * |Work.Spaces.DzIter 2 F z θ| := by
          refine le_trans (SSMB_abs_sub_le_abs_add _ _) ?_
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
        calc |Work.Spaces.DzIter 3 F z θ - 3 * Work.Spaces.DzIter 2 F z θ
              + 2 * Work.Spaces.DzIter 1 F z θ|
            ≤ |Work.Spaces.DzIter 3 F z θ - 3 * Work.Spaces.DzIter 2 F z θ|
              + |2 * Work.Spaces.DzIter 1 F z θ| := abs_add_le _ _
          _ ≤ (|Work.Spaces.DzIter 3 F z θ| + 3 * |Work.Spaces.DzIter 2 F z θ|)
              + 2 * |Work.Spaces.DzIter 1 F z θ| := by
              refine add_le_add h5 ?_
              rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
          _ = |Work.Spaces.DzIter 3 F z θ| + 3 * |Work.Spaces.DzIter 2 F z θ|
              + 2 * |Work.Spaces.DzIter 1 F z θ| := by ring
      linarith [h4, hDs1, hDs2, hDs3]
    calc z⁻¹ ^ 3 * |Work.Spaces.DzIter 3 F z θ - 3 * Work.Spaces.DzIter 2 F z θ
          + 2 * Work.Spaces.DzIter 1 F z θ|
        ≤ x ^ 3 * (6 * Dsum) := mul_le_mul e3 htri (abs_nonneg _) (by positivity)
      _ = (6 * x ^ 3) * Dsum := by ring
      _ ≤ K * Dsum := mul_le_mul_of_nonneg_right (by rw [hK]; nlinarith [hx0]) hDsnn

theorem SSMB_sum_range_four_eq (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range 4, f j) = f 0 + f 1 + f 2 + f 3 := by
  simp [Finset.sum_range_succ]

/-! ### 3. Mass bound for the `∂_z`-slices of the source -/

theorem SSMB_pzIterF_mass_le {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z δ C₀ : ℝ} (hz : 0 < z) (hδ0 : 0 < δ) (hδz : δ ≤ z) (hC₀ : 0 ≤ C₀)
    (hDz : ∀ j : ℕ, j ≤ 3 →
      IntegrableOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|) ≤ C₀)
    (m : ℕ) (hm : m ≤ 3) :
    IntegrableOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
        ≤ 24 * (1 + δ⁻¹ + (δ⁻¹) ^ 2 + (δ⁻¹) ^ 3) * C₀ := by
  have hD : ∀ j : ℕ, j ≤ 3 → Integrable
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|)
      (Measure.restrict volume Work.Spaces.Iθ) := fun j hj => (hDz j hj).1
  have hDi : ∀ j : ℕ, j ≤ 3 →
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|) ≤ C₀ :=
    fun j hj => (hDz j hj).2
  have hlt : ∀ j ∈ Finset.range 4, j ≤ 3 := by
    intro j hj
    have := Finset.mem_range.mp hj
    omega
  set K : ℝ := 6 * (1 + δ⁻¹ + (δ⁻¹) ^ 2 + (δ⁻¹) ^ 3) with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hSint : Integrable (fun θ : ℝ => ∑ j ∈ Finset.range 4,
      Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|)
      (Measure.restrict volume Work.Spaces.Iθ) :=
    MeasureTheory.integrable_finsetSum (Finset.range 4)
      (f := fun j θ => Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|)
      (fun j hj => hD j (hlt j hj))
  have hIntDom : Integrable (fun θ : ℝ => K * ∑ j ∈ Finset.range 4,
      Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|)
      (Measure.restrict volume Work.Spaces.Iθ) := hSint.const_mul K
  have hbound : ∀ᵐ θ ∂(Measure.restrict volume Work.Spaces.Iθ),
      ‖Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|‖
        ≤ K * ∑ j ∈ Finset.range 4, Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ| := by
    filter_upwards [Work.FTS.EllipticEst.H2W.lzsf_ae_mem_Ioo_Iθ] with θ hθ
    have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsc : 0 ≤ Work.Elliptic.sinCos2 θ := SSMB_sinCos2_nonneg_Iθ hIθ
    have habs : |Work.Spaces.pzIter m F z θ| ≤
        6 * (1 + δ⁻¹ + (δ⁻¹) ^ 2 + (δ⁻¹) ^ 3) *
          (|Work.Spaces.DzIter 0 F z θ| + |Work.Spaces.DzIter 1 F z θ|
            + |Work.Spaces.DzIter 2 F z θ| + |Work.Spaces.DzIter 3 F z θ|) :=
      SSMB_pzIterF_abs_le hF hz hδ0 hδz hθ m hm
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsc (abs_nonneg _))]
    have hcons : Work.Elliptic.sinCos2 θ * (6 * (1 + δ⁻¹ + (δ⁻¹) ^ 2 + (δ⁻¹) ^ 3) *
          (|Work.Spaces.DzIter 0 F z θ| + |Work.Spaces.DzIter 1 F z θ|
            + |Work.Spaces.DzIter 2 F z θ| + |Work.Spaces.DzIter 3 F z θ|))
        = K * ∑ j ∈ Finset.range 4,
            Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ| := by
      rw [hK, SSMB_sum_range_four_eq]
      ring
    calc Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|
        ≤ Work.Elliptic.sinCos2 θ * (6 * (1 + δ⁻¹ + (δ⁻¹) ^ 2 + (δ⁻¹) ^ 3) *
            (|Work.Spaces.DzIter 0 F z θ| + |Work.Spaces.DzIter 1 F z θ|
              + |Work.Spaces.DzIter 2 F z θ| + |Work.Spaces.DzIter 3 F z θ|)) :=
          mul_le_mul_of_nonneg_left habs hsc
      _ = K * ∑ j ∈ Finset.range 4,
            Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ| := hcons
  have hIntf : Integrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
      (Measure.restrict volume Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hIntDom ?_ hbound
    have hcont : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
        (Set.Ioo 0 (Real.pi / 2)) :=
      SSMB_continuous_sinCos2.continuousOn.mul (SSMB_continuousOn_pzIter_slice hF hz m).abs
    have h1 : AEStronglyMeasurable
        (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
        (Measure.restrict volume (Set.Ioo 0 (Real.pi / 2))) :=
      hcont.aestronglyMeasurable measurableSet_Ioo
    rwa [SSMB_restrict_Ioo_eq_restrict_Iθ] at h1
  refine ⟨hIntf, ?_⟩
  have hbound' : ∀ᵐ θ ∂(Measure.restrict volume Work.Spaces.Iθ),
      Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|
        ≤ K * ∑ j ∈ Finset.range 4, Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ| := by
    filter_upwards [hbound, SSMB_ae_sinCos2_nonneg] with θ hb hsc
    rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsc (abs_nonneg _))] at hb
  have hmono : (∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, K * ∑ j ∈ Finset.range 4,
          Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ| :=
    MeasureTheory.integral_mono_ae hIntf hIntDom hbound'
  have e1 : (∫ θ in Work.Spaces.Iθ, K * ∑ j ∈ Finset.range 4,
        Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|)
      = K * (∑ j ∈ Finset.range 4,
        ∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact MeasureTheory.integral_finsetSum (Finset.range 4)
      (f := fun j θ => Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|)
      (fun j hj => hD j (hlt j hj))
  have e2 : (∑ j ∈ Finset.range 4,
        ∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|)
      ≤ ∑ j ∈ Finset.range 4, C₀ :=
    Finset.sum_le_sum (fun j hj => hDi j (hlt j hj))
  have e3 : (∑ j ∈ Finset.range 4, C₀) = 4 * C₀ := by
    rw [Finset.sum_const, Finset.card_range]
    norm_num
  calc (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, K * ∑ j ∈ Finset.range 4,
          Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ| := hmono
    _ = K * (∑ j ∈ Finset.range 4,
          ∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|) := e1
    _ ≤ K * (4 * C₀) := by
        refine mul_le_mul_of_nonneg_left ?_ hKnn
        rw [← e3]
        exact e2
    _ = 24 * (1 + δ⁻¹ + (δ⁻¹) ^ 2 + (δ⁻¹) ^ 3) * C₀ := by rw [hK]; ring


/-! ### 4. Definitions used by the per-slice estimate -/

/-- The right-hand side of the expansion of `Lzero1 (∂_z^m Ψ (z,·))`, flattened. -/
def SSMB_RHSfun (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z : ℝ) (m : ℕ) : ℝ → ℝ :=
  fun θ => Work.Spaces.pzIter m F z θ
      + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter (m + 2) Ψ z θ
      + (α ^ 2 * (2 * (m : ℝ) * z) + α * (5 + α) * z) * Work.Spaces.pzIter (m + 1) Ψ z θ
      + (α ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) + α * (5 + α) * (m : ℝ))
          * Work.Spaces.pzIter m Ψ z θ

/-- The dominating function of the per-slice estimate. -/
def SSMB_Gfun (F Ψ : ℝ → ℝ → ℝ) (z Z : ℝ) (m : ℕ) : ℝ → ℝ :=
  fun θ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|
      + Z ^ 2 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 2) Ψ z θ|)
      + (12 * Z) * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 1) Ψ z θ|)
      + 11 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m Ψ z θ|)

theorem SSMB_integral_add4 {f0 f1 f2 f3 : ℝ → ℝ} {μ : Measure ℝ}
    (h0 : Integrable f0 μ) (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) :
    (∫ x, f0 x + f1 x + f2 x + f3 x ∂μ)
      = (∫ x, f0 x ∂μ) + (∫ x, f1 x ∂μ) + (∫ x, f2 x ∂μ) + (∫ x, f3 x ∂μ) := by
  rw [MeasureTheory.integral_add (f := fun x => f0 x + f1 x + f2 x) (g := f3)
        ((h0.add h1).add h2) h3,
      MeasureTheory.integral_add (f := fun x => f0 x + f1 x) (g := f2) (h0.add h1) h2,
      MeasureTheory.integral_add (f := f0) (g := f1) h0 h1]

theorem SSMB_abs_sum4_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

theorem SSMB_rhs_abs_le {α z Z : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {F Ψ : ℝ → ℝ → ℝ} {m : ℕ}
    (hm : m ≤ 3) {θ : ℝ} (hz : 0 < z) (hzZ : z ≤ Z) :
    |SSMB_RHSfun α F Ψ z m θ| ≤ |Work.Spaces.pzIter m F z θ|
      + Z ^ 2 * |Work.Spaces.pzIter (m + 2) Ψ z θ|
      + (12 * Z) * |Work.Spaces.pzIter (m + 1) Ψ z θ|
      + 11 * |Work.Spaces.pzIter m Ψ z θ| := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm3 : (m : ℝ) ≤ 3 := by exact_mod_cast hm
  have hcz2nn : 0 ≤ α ^ 2 * z ^ 2 := by positivity
  have hcz3nn : 0 ≤ α ^ 2 * (2 * (m : ℝ) * z) + α * (5 + α) * z := by positivity
  have hfac : α ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) + α * (5 + α) * (m : ℝ)
      = α * (m : ℝ) * (5 + α * (m : ℝ)) := by ring
  have hcz4nn : 0 ≤ α ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) + α * (5 + α) * (m : ℝ) := by
    rw [hfac]; positivity
  have hZ0 : 0 ≤ Z := le_trans (le_of_lt hz) hzZ
  have hcz2 : α ^ 2 * z ^ 2 ≤ Z ^ 2 := by
    have ha1 : α ^ 2 ≤ 1 := by nlinarith [hα, hα4]
    have hz2 : z ^ 2 ≤ Z ^ 2 := by nlinarith [hz, hzZ]
    nlinarith [ha1, hz2, sq_nonneg z, sq_nonneg α]
  have hda : 2 * α ^ 2 * (m : ℝ) ≤ 3 / 8 := by nlinarith [hα, hα4, hm0, hm3]
  have hdb : α * (5 + α) ≤ 21 / 16 := by nlinarith [hα, hα4]
  have hc3 : 2 * α ^ 2 * (m : ℝ) + α * (5 + α) ≤ 12 := by linarith
  have hcz3 : α ^ 2 * (2 * (m : ℝ) * z) + α * (5 + α) * z ≤ 12 * Z := by
    nlinarith [hc3, hcz3nn, hz, hzZ, hZ0]
  have hm6 : (m : ℝ) * ((m : ℝ) - 1) ≤ 6 := by nlinarith [hm0, hm3]
  have ha16 : α ^ 2 ≤ (1 / 4) ^ 2 := by nlinarith [hα, hα4]
  have hdc : α ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) ≤ 3 / 8 := by
    have h1 : α ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) ≤ α ^ 2 * 6 :=
      mul_le_mul_of_nonneg_left hm6 (sq_nonneg α)
    have h2 : α ^ 2 * 6 ≤ (1 / 4) ^ 2 * 6 := by nlinarith [ha16]
    linarith
  have hdd : α * (5 + α) * (m : ℝ) ≤ 63 / 16 := by
    have hp : 0 ≤ α * (5 + α) := by positivity
    nlinarith [hdb, hm3, hm0, hp]
  have hcz4 : α ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) + α * (5 + α) * (m : ℝ) ≤ 11 := by linarith
  have ht2 : |(α ^ 2 * z ^ 2) * Work.Spaces.pzIter (m + 2) Ψ z θ|
      = (α ^ 2 * z ^ 2) * |Work.Spaces.pzIter (m + 2) Ψ z θ| := by
    rw [abs_mul, abs_of_nonneg hcz2nn]
  have ht3 : |(α ^ 2 * (2 * (m : ℝ) * z) + α * (5 + α) * z) * Work.Spaces.pzIter (m + 1) Ψ z θ|
      = (α ^ 2 * (2 * (m : ℝ) * z) + α * (5 + α) * z)
          * |Work.Spaces.pzIter (m + 1) Ψ z θ| := by
    rw [abs_mul, abs_of_nonneg hcz3nn]
  have ht4 : |(α ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) + α * (5 + α) * (m : ℝ))
        * Work.Spaces.pzIter m Ψ z θ|
      = (α ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) + α * (5 + α) * (m : ℝ))
          * |Work.Spaces.pzIter m Ψ z θ| := by
    rw [abs_mul, abs_of_nonneg hcz4nn]
  simp only [SSMB_RHSfun]
  refine le_trans (SSMB_abs_sum4_le _ _ _ _) ?_
  rw [ht2, ht3, ht4]
  nlinarith [hcz2, hcz3, hcz4, abs_nonneg (Work.Spaces.pzIter m F z θ),
    abs_nonneg (Work.Spaces.pzIter (m + 2) Ψ z θ),
    abs_nonneg (Work.Spaces.pzIter (m + 1) Ψ z θ),
    abs_nonneg (Work.Spaces.pzIter m Ψ z θ)]

/-! ### 5. The per-slice estimate -/


/-! ### 5b. The expansion of `Lzero (∂_z^m Ψ)` for `m ≤ 3`

The identity that turns the `WeakPos2` equation `bslOp α Ψ = F` into a bound on the source
`Lzero1 (∂_z^m Ψ(z,·))` in terms of the slices of `Ψ` and `F`.  Levels `0`, `1`, `2` are the
lemmas `lzero_level0_pt`, `lzero_level1_pt`, `lzero_level2_pt` of
`Submission/Work/FTS/EllipticEst/H2W/lzeroSliceL1Ae.lean`; level `3` is proved here from the
same template. -/

/-- `∂_z^m (z · g) = m ∂_z^{m-1} g + z ∂_z^m g` for `C^∞` `g` (verbatim from
`Work.FTS.EllipticEst.H2W.pzIter_mul_id`). -/
theorem SSMB_lzs_pz_pthIter_two_eqOn {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter 2 g)))
      (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.pz g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h2 : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      ContDiffAt ℝ 2 (Function.uncurry g) p := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.FTS.EllipticEst.DzAmgm.contDiffAt_two_of_mem hg hz ⟨hθ0, hθ1⟩
  have h2' : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth g)) p := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.FTS.EllipticEst.DzAmgm.contDiffAt_two_of_mem (hg.pth) hz ⟨hθ0, hθ1⟩
  have hEqOn : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth g)))
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz g))) Work.FTS.EllipticEst.Q0 :=
    fun p hp => Work.Spaces.pz_pth_comm (h2 p hp)
  intro p hp
  have e2 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth g)) p.1 p.2
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) p.1 p.2 :=
    Work.Spaces.pz_pth_comm (h2' p hp)
  have e1 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) p.1 p.2
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz g)) p.1 p.2 :=
    Work.Spaces.pth_congr_of_isOpen (f := Work.Spaces.pz (Work.Spaces.pth g))
      (f' := Work.Spaces.pth (Work.Spaces.pz g)) Work.FTS.EllipticEst.isOpen_Q0 hEqOn hp
  show Work.Spaces.pz (Work.Spaces.pthIter 2 g) p.1 p.2
      = Work.Spaces.pthIter 2 (Work.Spaces.pz g) p.1 p.2
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact e2.trans e1

/-! ## Differentiability of the `z`-slices on the open quadrant -/

theorem SSMB_differentiableAt_zslice {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun z' => g z' θ) z :=
  (Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice hg hθ hz).differentiableAt

/-! ## The level-`0` form of the equation -/

/-- **The level-`0` equation on the open quadrant**: `Lzero Ψ = F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ`
wherever `bslOp α Ψ = F` (the first clause of `WeakPos2`). -/

theorem SSMB_lzero_level0 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Elliptic.Lzero Ψ z θ
      = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ := by
  have h := heq z hz θ hθ.1 hθ.2
  rw [Work.Elliptic.bslOp_apply] at h
  nlinarith [h]

/-! ## `∂_z` commutes with `Lzero` on the open quadrant -/

/-- **The commutation `Lzero ∘ ∂_z = ∂_z ∘ Lzero`** on the open quadrant, for a `C^∞` function
there.  Both sides involve only `θ`-derivatives and the `θ`-only factor `tan θ`, so Clairaut
(`H2W.pz_pthIter_two_eqOn` for the `∂_θ²` term, `Spaces.pz_pth_comm` for the mixed term with
`tan θ · u`) applies. -/

theorem SSMB_Lzero_pz_eqOn {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u) :
    Set.EqOn (Function.uncurry (Work.Elliptic.Lzero (Work.Spaces.pz u)))
      (Function.uncurry (Work.Spaces.pz (Work.Elliptic.Lzero u)))
      Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hθ : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hso_tan : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hu
  have hso_pth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 u) := hu.pth.pth
  have hC : Work.Spaces.pthIter 2 (Work.Spaces.pz u) p.1 p.2
      = Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2 :=
    (SSMB_lzs_pz_pthIter_two_eqOn hu hp).symm
  have htan : (fun z θ => Real.tan θ * Work.Spaces.pz u z θ)
      = Work.Spaces.pz (fun z θ => Real.tan θ * u z θ) := by
    funext z θ
    exact (deriv_const_mul_field (u := Real.tan θ) (v := fun z' => u z' θ) (x := z)).symm
  have hmixed : Work.Spaces.pth (fun z θ => Real.tan θ * Work.Spaces.pz u z θ) p.1 p.2
      = Work.Spaces.pz (Work.Spaces.pth (fun z θ => Real.tan θ * u z θ)) p.1 p.2 := by
    rw [htan]
    exact (Work.Spaces.pz_pth_comm ((hso_tan.contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).of_le (by norm_num))).symm
  have hdA : DifferentiableAt ℝ (fun z' => Work.Spaces.pthIter 2 u z' p.2) p.1 :=
    SSMB_differentiableAt_zslice hso_pth2 hz hθ
  have hdB : DifferentiableAt ℝ
      (fun z' => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z' p.2) p.1 :=
    SSMB_differentiableAt_zslice hso_tan.pth hz hθ
  have hdC : DifferentiableAt ℝ (fun z' => u z' p.2) p.1 := SSMB_differentiableAt_zslice hu hz hθ
  have hlin : Work.Spaces.pz (fun z θ => -(Work.Spaces.pthIter 2 u z θ)
        + Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ - 6 * u z θ) p.1 p.2
      = -(Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2)
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ => Real.tan θ * u z θ)) p.1 p.2
        - 6 * Work.Spaces.pz u p.1 p.2 := by
    show deriv (fun z' => -(Work.Spaces.pthIter 2 u z' p.2)
        + Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z' p.2 - 6 * u z' p.2) p.1 = _
    rw [(Filter.EventuallyEq.deriv_eq (f₁ := fun z' => (Work.Spaces.pth
            (fun z θ => Real.tan θ * u z θ) z' p.2 - 6 * u z' p.2)
          - (Work.Spaces.pthIter 2 u z' p.2)) (Filter.Eventually.of_forall
        (fun y => by ring))).symm]
    rw [show (fun z' : ℝ => (Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z' p.2
            - 6 * u z' p.2) - (Work.Spaces.pthIter 2 u z' p.2))
        = ((fun z' : ℝ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z' p.2)
            - (fun z' : ℝ => 6 * u z' p.2))
          - (fun z' : ℝ => Work.Spaces.pthIter 2 u z' p.2) from rfl]
    rw [deriv_sub (hdB.sub (hdC.const_mul 6)) hdA]
    rw [deriv_sub hdB (hdC.const_mul 6), deriv_const_mul_field]
    simp only [Work.Spaces.pz]
    ring
  show -(Work.Spaces.pthIter 2 (Work.Spaces.pz u) p.1 p.2)
      + Work.Spaces.pth (fun z θ => Real.tan θ * Work.Spaces.pz u z θ) p.1 p.2
      - 6 * Work.Spaces.pz u p.1 p.2
    = Work.Spaces.pz (fun z θ => -(Work.Spaces.pthIter 2 u z θ)
        + Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ - 6 * u z θ) p.1 p.2
  rw [hlin, hC, hmixed]

/-- **The commutation for the iterated derivative**: `Lzero (∂_z^j u) = ∂_z^j (Lzero u)` on the
open quadrant, by induction on `j` from `SSMB_Lzero_pz_eqOn` and the congruence of `∂_z` on open
sets (`Spaces.pz_congr_of_isOpen`). -/

theorem SSMB_Lzero_pzIter_eqOn {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Elliptic.Lzero (Work.Spaces.pzIter j u)))
      (Function.uncurry (Work.Spaces.pzIter j (Work.Elliptic.Lzero u)))
      Work.FTS.EllipticEst.Q0 := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      intro p hp
      have h1 : Work.Elliptic.Lzero (Work.Spaces.pzIter (j + 1) u) p.1 p.2
          = Work.Spaces.pz (Work.Elliptic.Lzero (Work.Spaces.pzIter j u)) p.1 p.2 := by
        show Work.Elliptic.Lzero (Work.Spaces.pz (Work.Spaces.pzIter j u)) p.1 p.2 = _
        exact SSMB_Lzero_pz_eqOn (hu.pzIter j) hp
      have h2 : Work.Spaces.pz (Work.Elliptic.Lzero (Work.Spaces.pzIter j u)) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.pzIter j (Work.Elliptic.Lzero u)) p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hp
      show Work.Elliptic.Lzero (Work.Spaces.pzIter (j + 1) u) p.1 p.2
          = Work.Spaces.pzIter (j + 1) (Work.Elliptic.Lzero u) p.1 p.2
      rw [h1, h2]
      rfl

/-! ## Product rules (used by the Leibniz expansion of `Lzero (∂_z^jΨ)`) -/

/-- `∂_z(z·u) = u + z·∂_zu` on the open quadrant. -/

theorem SSMB_pzIter_congr_of_isOpen {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pzIter k f))
      (Function.uncurry (Work.Spaces.pzIter k g)) V := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro p hp
      show deriv (fun z' => Work.Spaces.pzIter k f z' p.2) p.1
        = deriv (fun z' => Work.Spaces.pzIter k g z' p.2) p.1
      exact Work.Spaces.pz_congr_of_isOpen hV ih hp

/-- `∂_z^j` commutes with multiplication by a constant. -/

theorem SSMB_pzIter_const_mul (c : ℝ) (g : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.pzIter k g z θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]
      funext z θ
      exact deriv_const_mul_field c

/-- Additivity of `∂_z^k` on the open quadrant, for `SmoothOpen` data. -/

theorem SSMB_pzIter_const_mul_pt (c : ℝ) (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z θ => c * g z θ) z θ = c * Work.Spaces.pzIter k g z θ :=
  congrFun (congrFun (SSMB_pzIter_const_mul c g k) z) θ

theorem SSMB_pzIter_add_of_smooth {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.pzIter k f z θ + Work.Spaces.pzIter k g z θ := by
  induction k generalizing z θ with
  | zero => rfl
  | succ k ih =>
      have hev : (fun z' => Work.Spaces.pzIter k (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter k f z' θ + Work.Spaces.pzIter k g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih hz' hθ
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k f z' θ) z :=
        ((hf.pzIter k).hasDerivAt_slice hθ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k g z' θ) z :=
        ((hg.pzIter k).hasDerivAt_slice hθ hz).differentiableAt
      show deriv (fun z' => Work.Spaces.pzIter k (fun z θ => f z θ + g z θ) z' θ) z = _
      rw [hev.deriv_eq]
      rw [show (fun z' : ℝ => Work.Spaces.pzIter k f z' θ + Work.Spaces.pzIter k g z' θ)
          = (fun z' : ℝ => Work.Spaces.pzIter k f z' θ)
            + (fun z' : ℝ => Work.Spaces.pzIter k g z' θ) from rfl]
      rw [deriv_add hd1 hd2]
      rfl

/-- `∂_z²(zu) = 2∂_zu + z∂_z²u`. -/

theorem SSMB_lzero_level0_pt {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Elliptic.Lzero Ψ z θ = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ :=
  SSMB_lzero_level0 heq hz hθ

/-- **`SmoothOpen F` for the source of the equation** (the congruence of `bslOp α Ψ` with `F`
on the open quadrant). -/
theorem SSMB_smoothOpen_source {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.FTS.EllipticEst.SmoothOpen F := by
  have hL : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Ψ) := by
    have h1 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-1 : ℝ) * Work.Spaces.pthIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-1) (hsm.pth.pth)
    have h2 : Work.FTS.EllipticEst.SmoothOpen
        (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) :=
      (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
        Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hsm).pth
    have h3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (-6 : ℝ) * Ψ z θ) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-6) hsm
    have h4 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        (-1 : ℝ) * Work.Spaces.pthIter 2 Ψ z θ
          + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
          + (-6 : ℝ) * Ψ z θ) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl h1 h2) h3
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl h4 ?_
    intro z θ hz hθ0 hθ1
    show (-1 : ℝ) * Work.Spaces.pthIter 2 Ψ z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ + (-6 : ℝ) * Ψ z θ
      = -(Work.Spaces.pthIter 2 Ψ z θ)
        + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ
    ring
  have hB : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) := by
    have h1 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(α ^ 2)) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-(α ^ 2))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
          Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hsm.pzIter 2))
    have h2 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(α * (5 + α))) * (z * Work.Spaces.pz Ψ z θ)) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-(α * (5 + α)))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
          Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl hsm.pz)
    have h3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        (-(α ^ 2)) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + (-(α * (5 + α))) * (z * Work.Spaces.pz Ψ z θ)
          + Work.Elliptic.Lzero Ψ z θ) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl h1 h2) hL
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl h3 ?_
    intro z θ hz hθ0 hθ1
    show (-(α ^ 2)) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + (-(α * (5 + α))) * (z * Work.Spaces.pz Ψ z θ) + Work.Elliptic.Lzero Ψ z θ
      = Work.Elliptic.bslOp α Ψ z θ
    rw [Work.Elliptic.bslOp_apply]
    ring
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl hB (fun z θ hz hθ0 hθ1 =>
    heq z hz θ hθ0 hθ1)


/-- `∂_z(z · g) = g + z ∂_z g`. -/
theorem SSMB_pz_mul_one {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pz (fun z θ => z * g z θ) z θ = 1 * g z θ + z * Work.Spaces.pz g z θ :=
  ((hasDerivAt_id z).mul (hg.hasDerivAt_slice hθ hz)).deriv

/-- `∂_z^{m+1}(z·g) = ((m:ℝ)+1) ∂_z^m g + z ∂_z^{m+1} g`. -/
theorem SSMB_pzIter_mul_id {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) (m : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pzIter (m + 1) (fun z θ => z * g z θ) z θ
      = ((m : ℝ) + 1) * Work.Spaces.pzIter m g z θ
        + z * Work.Spaces.pzIter (m + 1) g z θ := by
  induction m generalizing z θ with
  | zero =>
      simpa [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using SSMB_pz_mul_one hg hz hθ
  | succ n ih =>
      have hdiff : ∀ k : ℕ, HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter k g z' θ)
          (Work.Spaces.pzIter (k + 1) g z θ) z :=
        fun k => hg.hasDerivAt_slice_pzIter k hθ hz
      have hev : (fun z' : ℝ => Work.Spaces.pzIter (n + 1) (fun z θ => z * g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' : ℝ => ((n : ℝ) + 1) * Work.Spaces.pzIter n g z' θ
            + z' * Work.Spaces.pzIter (n + 1) g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih hz' hθ
      have hderiv : HasDerivAt
          (fun z' : ℝ => ((n : ℝ) + 1) * Work.Spaces.pzIter n g z' θ
            + z' * Work.Spaces.pzIter (n + 1) g z' θ)
          (((n : ℝ) + 1) * Work.Spaces.pzIter (n + 1) g z θ
            + (1 * Work.Spaces.pzIter (n + 1) g z θ
              + z * Work.Spaces.pzIter (n + 1 + 1) g z θ)) z :=
        ((hdiff n).const_mul ((n : ℝ) + 1)).add
          ((hasDerivAt_id z).mul (hdiff (n + 1)))
      rw [show Work.Spaces.pzIter (n + 1 + 1) (fun z θ => z * g z θ)
            = Work.Spaces.pz (Work.Spaces.pzIter (n + 1) (fun z θ => z * g z θ)) from rfl]
      rw [show Work.Spaces.pz (Work.Spaces.pzIter (n + 1) (fun z θ => z * g z θ)) z θ
            = deriv (fun z' : ℝ =>
                Work.Spaces.pzIter (n + 1) (fun z θ => z * g z θ) z' θ) z from rfl]
      rw [hev.deriv_eq, hderiv.deriv]
      push_cast
      ring


/-- **The level-`1` identity** on the open quadrant. -/
theorem SSMB_lzero_level1_pt {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Elliptic.Lzero (Work.Spaces.pzIter 1 Ψ) z θ
      = Work.Spaces.pzIter 1 F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ
            + 2 * (1 : ℝ) * z * Work.Spaces.pzIter 2 Ψ z θ
            + (1 : ℝ) * ((1 : ℝ) - 1) * Work.Spaces.pzIter 1 Ψ z θ)
        + (α * (5 + α)) * (z * Work.Spaces.pzIter 2 Ψ z θ
            + (1 : ℝ) * Work.Spaces.pzIter 1 Ψ z θ) := by
  set c : ℝ := α * (5 + α) with hc
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ.1, hθ.2⟩
  have hso2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hsm.pzIter 2)
  have hso1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl hsm.pz
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hso2)
  have hB : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl c hso1
  have hlev : Set.EqOn (Function.uncurry (Work.Elliptic.Lzero Ψ))
      (Function.uncurry (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + c * (z * Work.Spaces.pz Ψ z θ))) Work.FTS.EllipticEst.Q0 := by
    intro q hq
    obtain ⟨hzq, hq0, hq1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
    have h := SSMB_lzero_level0 heq hzq ⟨hq0, hq1⟩
    show Work.Elliptic.Lzero Ψ q.1 q.2
      = F q.1 q.2 + α ^ 2 * (q.1 ^ 2 * Work.Spaces.pzIter 2 Ψ q.1 q.2)
        + c * (q.1 * Work.Spaces.pz Ψ q.1 q.2)
    rw [h, hc]
    ring
  have e1 : Work.Elliptic.Lzero (Work.Spaces.pzIter 1 Ψ) z θ
      = Work.Spaces.pzIter 1 (Work.Elliptic.Lzero Ψ) z θ :=
    SSMB_Lzero_pzIter_eqOn hsm 1 hp
  have e3 : Work.Spaces.pzIter 1 (fun z θ => F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) + c * (z * Work.Spaces.pz Ψ z θ)) z θ
      = Work.Spaces.pzIter 1 (fun z θ => F z θ
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.pzIter 1 (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) z θ := by
    rw [show (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + c * (z * Work.Spaces.pz Ψ z θ))
        = (fun z θ => (fun z θ => F z θ
              + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
            + (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) z θ) from rfl]
    exact SSMB_pzIter_add_of_smooth hA hB hz hθ 1
  have e2 : Work.Spaces.pzIter 1 (Work.Elliptic.Lzero Ψ) z θ
      = Work.Spaces.pzIter 1 (fun z θ => F z θ
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) + c * (z * Work.Spaces.pz Ψ z θ)) z θ :=
    SSMB_pzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hlev 1 hp
  have e4 : Work.Spaces.pzIter 1 (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) z θ
      = c * Work.Spaces.pzIter 1 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ :=
    SSMB_pzIter_const_mul_pt c (fun z θ => z * Work.Spaces.pz Ψ z θ) 1 z θ
  have e5 : Work.Spaces.pzIter 1 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ
      = (1 : ℝ) * Work.Spaces.pzIter 1 Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ := by
    have h := SSMB_pzIter_mul_id hsm.pz 0 hz hθ
    norm_num at h
    simpa using h
  have e6 : Work.Spaces.pzIter 1 (fun z θ => F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
      = Work.Spaces.pzIter 1 (fun z θ => F z θ) z θ
        + Work.Spaces.pzIter 1 (fun z θ =>
            α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ := by
    rw [show (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        = (fun z θ => (fun z θ => F z θ) z θ
            + (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) from rfl]
    exact SSMB_pzIter_add_of_smooth hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hso2) hz hθ 1
  have e7 : Work.Spaces.pzIter 1 (fun z θ =>
        α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
      = α ^ 2 * Work.Spaces.pzIter 1 (fun z θ =>
          z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    SSMB_pzIter_const_mul_pt (α ^ 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 1 z θ
  have e8 : Work.Spaces.pzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ
        + 2 * z * Work.Spaces.pzIter 2 Ψ z θ
        + 0 * Work.Spaces.pzIter 1 Ψ z θ := by
    have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
        (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ) z :=
      ((hsm.pzIter 2).curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)
    have h := Work.FTS.H2.Q.pzIter_sq_mul_sm 1 (by norm_num) hκ
    norm_num at h
    simpa using h
  have e9 : Work.Spaces.pzIter 1 (fun z θ => F z θ) z θ = Work.Spaces.pzIter 1 F z θ := rfl
  rw [e1, e2, e3, e6, e7, e8, e9, e4, e5, hc]
  ring


/-- **The level-`2` identity** on the open quadrant. -/
theorem SSMB_lzero_level2_pt {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Elliptic.Lzero (Work.Spaces.pzIter 2 Ψ) z θ
      = Work.Spaces.pzIter 2 F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ
            + 2 * (2 : ℝ) * z * Work.Spaces.pzIter 3 Ψ z θ
            + (2 : ℝ) * ((2 : ℝ) - 1) * Work.Spaces.pzIter 2 Ψ z θ)
        + (α * (5 + α)) * (z * Work.Spaces.pzIter 3 Ψ z θ
            + (2 : ℝ) * Work.Spaces.pzIter 2 Ψ z θ) := by
  set c : ℝ := α * (5 + α) with hc
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ.1, hθ.2⟩
  have hso2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hsm.pzIter 2)
  have hso1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl hsm.pz
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hso2)
  have hB : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl c hso1
  have hlev : Set.EqOn (Function.uncurry (Work.Elliptic.Lzero Ψ))
      (Function.uncurry (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + c * (z * Work.Spaces.pz Ψ z θ))) Work.FTS.EllipticEst.Q0 := by
    intro q hq
    obtain ⟨hzq, hq0, hq1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
    have h := SSMB_lzero_level0 heq hzq ⟨hq0, hq1⟩
    show Work.Elliptic.Lzero Ψ q.1 q.2
      = F q.1 q.2 + α ^ 2 * (q.1 ^ 2 * Work.Spaces.pzIter 2 Ψ q.1 q.2)
        + c * (q.1 * Work.Spaces.pz Ψ q.1 q.2)
    rw [h, hc]
    ring
  have e1 : Work.Elliptic.Lzero (Work.Spaces.pzIter 2 Ψ) z θ
      = Work.Spaces.pzIter 2 (Work.Elliptic.Lzero Ψ) z θ :=
    SSMB_Lzero_pzIter_eqOn hsm 2 hp
  have e3 : Work.Spaces.pzIter 2 (fun z θ => F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) + c * (z * Work.Spaces.pz Ψ z θ)) z θ
      = Work.Spaces.pzIter 2 (fun z θ => F z θ
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.pzIter 2 (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) z θ := by
    rw [show (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + c * (z * Work.Spaces.pz Ψ z θ))
        = (fun z θ => (fun z θ => F z θ
              + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
            + (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) z θ) from rfl]
    exact SSMB_pzIter_add_of_smooth hA hB hz hθ 2
  have e2 : Work.Spaces.pzIter 2 (Work.Elliptic.Lzero Ψ) z θ
      = Work.Spaces.pzIter 2 (fun z θ => F z θ
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) + c * (z * Work.Spaces.pz Ψ z θ)) z θ :=
    SSMB_pzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hlev 2 hp
  have e4 : Work.Spaces.pzIter 2 (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) z θ
      = c * Work.Spaces.pzIter 2 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ :=
    SSMB_pzIter_const_mul_pt c (fun z θ => z * Work.Spaces.pz Ψ z θ) 2 z θ
  have e5 : Work.Spaces.pzIter 2 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ
      = (2 : ℝ) * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pzIter 3 Ψ z θ := by
    have h := SSMB_pzIter_mul_id hsm.pz 1 hz hθ
    norm_num at h
    simpa using h
  have e6 : Work.Spaces.pzIter 2 (fun z θ => F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
      = Work.Spaces.pzIter 2 (fun z θ => F z θ) z θ
        + Work.Spaces.pzIter 2 (fun z θ =>
            α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ := by
    rw [show (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        = (fun z θ => (fun z θ => F z θ) z θ
            + (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) from rfl]
    exact SSMB_pzIter_add_of_smooth hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hso2) hz hθ 2
  have e7 : Work.Spaces.pzIter 2 (fun z θ =>
        α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
      = α ^ 2 * Work.Spaces.pzIter 2 (fun z θ =>
          z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    SSMB_pzIter_const_mul_pt (α ^ 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 2 z θ
  have e8 : Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ
        + 4 * z * Work.Spaces.pzIter 3 Ψ z θ
        + 2 * Work.Spaces.pzIter 2 Ψ z θ := by
    have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
        (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ) z :=
      ((hsm.pzIter 2).curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)
    have h := Work.FTS.H2.Q.pzIter_sq_mul_sm 2 (by norm_num) hκ
    norm_num at h
    simpa using h
  have e9 : Work.Spaces.pzIter 2 (fun z θ => F z θ) z θ = Work.Spaces.pzIter 2 F z θ := rfl
  rw [e1, e2, e3, e6, e7, e8, e9, e4, e5, hc]
  ring

/-- **The level-`3` identity** on the open quadrant. -/
theorem SSMB_lzero_level3_pt {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Elliptic.Lzero (Work.Spaces.pzIter 3 Ψ) z θ
      = Work.Spaces.pzIter 3 F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 5 Ψ z θ
            + 6 * z * Work.Spaces.pzIter 4 Ψ z θ + 6 * Work.Spaces.pzIter 3 Ψ z θ)
        + (α * (5 + α)) * (z * Work.Spaces.pzIter 4 Ψ z θ
            + 3 * Work.Spaces.pzIter 3 Ψ z θ) := by
  set c : ℝ := α * (5 + α) with hc
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ.1, hθ.2⟩
  have hso2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hsm.pzIter 2)
  have hso1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl hsm.pz
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hso2)
  have hB : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl c hso1
  have hlev : Set.EqOn (Function.uncurry (Work.Elliptic.Lzero Ψ))
      (Function.uncurry (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + c * (z * Work.Spaces.pz Ψ z θ))) Work.FTS.EllipticEst.Q0 := by
    intro q hq
    obtain ⟨hzq, hq0, hq1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
    have h := SSMB_lzero_level0 heq hzq ⟨hq0, hq1⟩
    show Work.Elliptic.Lzero Ψ q.1 q.2
      = F q.1 q.2 + α ^ 2 * (q.1 ^ 2 * Work.Spaces.pzIter 2 Ψ q.1 q.2)
        + c * (q.1 * Work.Spaces.pz Ψ q.1 q.2)
    rw [h, hc]
    ring
  have e1 : Work.Elliptic.Lzero (Work.Spaces.pzIter 3 Ψ) z θ
      = Work.Spaces.pzIter 3 (Work.Elliptic.Lzero Ψ) z θ :=
    SSMB_Lzero_pzIter_eqOn hsm 3 hp
  have e3 : Work.Spaces.pzIter 3 (fun z θ => F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) + c * (z * Work.Spaces.pz Ψ z θ)) z θ
      = Work.Spaces.pzIter 3 (fun z θ => F z θ
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.pzIter 3 (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) z θ := by
    rw [show (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + c * (z * Work.Spaces.pz Ψ z θ))
        = (fun z θ => (fun z θ => F z θ
              + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
            + (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) z θ) from rfl]
    exact SSMB_pzIter_add_of_smooth hA hB hz hθ 3
  have e2 : Work.Spaces.pzIter 3 (Work.Elliptic.Lzero Ψ) z θ
      = Work.Spaces.pzIter 3 (fun z θ => F z θ
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) + c * (z * Work.Spaces.pz Ψ z θ)) z θ :=
    SSMB_pzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hlev 3 hp
  have e4 : Work.Spaces.pzIter 3 (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) z θ
      = c * Work.Spaces.pzIter 3 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ :=
    SSMB_pzIter_const_mul_pt c
      (fun z θ => z * Work.Spaces.pz Ψ z θ) 3 z θ
  have e5 : Work.Spaces.pzIter 3 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ
      = 3 * Work.Spaces.pzIter 3 Ψ z θ + z * Work.Spaces.pzIter 4 Ψ z θ := by
    have h := SSMB_pzIter_mul_id hsm.pz 2 hz hθ
    norm_num at h
    simpa using h
  have e6 : Work.Spaces.pzIter 3 (fun z θ => F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
      = Work.Spaces.pzIter 3 (fun z θ => F z θ) z θ
        + Work.Spaces.pzIter 3 (fun z θ =>
            α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ := by
    rw [show (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        = (fun z θ => (fun z θ => F z θ) z θ
            + (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) from rfl]
    exact SSMB_pzIter_add_of_smooth hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hso2) hz hθ 3
  have e7 : Work.Spaces.pzIter 3 (fun z θ =>
        α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
      = α ^ 2 * Work.Spaces.pzIter 3 (fun z θ =>
          z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    SSMB_pzIter_const_mul_pt (α ^ 2)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 3 z θ
  have e8 : Work.Spaces.pzIter 3 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 5 Ψ z θ + 6 * z * Work.Spaces.pzIter 4 Ψ z θ
        + 6 * Work.Spaces.pzIter 3 Ψ z θ := by
    have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
        (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ) z :=
      ((hsm.pzIter 2).curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)
    have h := Work.FTS.H2.Q.pzIter_sq_mul_sm 3 (by norm_num) hκ
    norm_num at h
    simpa using h
  have e9 : Work.Spaces.pzIter 3 (fun z θ => F z θ) z θ = Work.Spaces.pzIter 3 F z θ := rfl
  rw [e1, e2, e3, e6, e7, e8, e9, e4, e5, hc]
  ring

/-- **The expansion of `Lzero1 (∂_z^m Ψ(z,·))` for `m ≤ 3`.** -/
theorem SSMB_lzeroPzIterExpansion (α : ℝ) {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (m : ℕ) (hm : m ≤ 3) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ
      = Work.Spaces.pzIter m F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter (m + 2) Ψ z θ
            + 2 * (m : ℝ) * z * Work.Spaces.pzIter (m + 1) Ψ z θ
            + (m : ℝ) * ((m : ℝ) - 1) * Work.Spaces.pzIter m Ψ z θ)
        + α * (5 + α) * (z * Work.Spaces.pzIter (m + 1) Ψ z θ
            + (m : ℝ) * Work.Spaces.pzIter m Ψ z θ) := by
  have hbridge : Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ
      = Work.Elliptic.Lzero (Work.Spaces.pzIter m Ψ) z θ := by
    simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ,
      Work.Spaces.pthIter_zero, Work.Spaces.pth]
  rw [hbridge]
  interval_cases m
  · rw [show Work.Elliptic.Lzero (Work.Spaces.pzIter 0 Ψ) z θ
        = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
          + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ from SSMB_lzero_level0_pt heq hz hθ]
    simp only [Work.Spaces.pzIter_zero, Work.Spaces.pzIter_succ] <;> ring
  · rw [SSMB_lzero_level1_pt hFsm hsm heq hz hθ]
    ring
  · rw [SSMB_lzero_level2_pt hFsm hsm heq hz hθ]
    ring
  · rw [SSMB_lzero_level3_pt hFsm hsm heq hz hθ]
    ring

theorem SSMB_sliceLzeroMass_le {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z δ Z C₀ : ℝ} (hz : 0 < z) (hδ0 : 0 < δ) (hδz : δ ≤ z) (hzZ : z ≤ Z) (hC₀ : 0 ≤ C₀)
    (hΨ : ∀ k : ℕ, k ≤ 5 →
      IntegrableOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter k Ψ z θ|)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter k Ψ z θ|) ≤ C₀)
    (hF : ∀ j : ℕ, j ≤ 3 →
      IntegrableOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|) ≤ C₀)
    (m : ℕ) (hm : m ≤ 3) :
    IntegrableOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ *
        |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ *
        |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
        ≤ (24 * (1 + δ⁻¹ + (δ⁻¹) ^ 2 + (δ⁻¹) ^ 3) + Z ^ 2 + 12 * Z + 11) * C₀ := by
  have hFm := SSMB_pzIterF_mass_le hFsm hz hδ0 hδz hC₀ hF m hm
  have hk2 : m + 2 ≤ 5 := by omega
  have hk1 : m + 1 ≤ 5 := by omega
  have hk0 : m ≤ 5 := by omega
  have hΨ2 := hΨ (m + 2) hk2
  have hΨ1 := hΨ (m + 1) hk1
  have hΨ0 := hΨ m hk0
  have hA : Integrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
      (Measure.restrict volume Work.Spaces.Iθ) := hFm.1
  have hB : Integrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 2) Ψ z θ|)
      (Measure.restrict volume Work.Spaces.Iθ) := hΨ2.1
  have hC : Integrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 1) Ψ z θ|)
      (Measure.restrict volume Work.Spaces.Iθ) := hΨ1.1
  have hD : Integrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m Ψ z θ|)
      (Measure.restrict volume Work.Spaces.Iθ) := hΨ0.1
  have hGint : Integrable (SSMB_Gfun F Ψ z Z m) (Measure.restrict volume Work.Spaces.Iθ) := by
    change Integrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|
          + Z ^ 2 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 2) Ψ z θ|)
          + (12 * Z) * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 1) Ψ z θ|)
          + 11 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m Ψ z θ|))
        (Measure.restrict volume Work.Spaces.Iθ)
    exact ((hA.add (hB.const_mul (Z ^ 2))).add (hC.const_mul (12 * Z))).add (hD.const_mul 11)
  have hRfun_eq : SSMB_RHSfun α F Ψ z m = fun θ : ℝ => Work.Spaces.pzIter m F z θ
      + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter (m + 2) Ψ z θ
      + (α ^ 2 * (2 * (m : ℝ) * z) + α * (5 + α) * z) * Work.Spaces.pzIter (m + 1) Ψ z θ
      + (α ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) + α * (5 + α) * (m : ℝ))
          * Work.Spaces.pzIter m Ψ z θ := rfl
  have hcontR : ContinuousOn (SSMB_RHSfun α F Ψ z m) (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 := SSMB_continuousOn_pzIter_slice hFsm hz m
    have h2 := SSMB_continuousOn_pzIter_slice hsm hz (m + 2)
    have h3 := SSMB_continuousOn_pzIter_slice hsm hz (m + 1)
    have h4 := SSMB_continuousOn_pzIter_slice hsm hz m
    rw [hRfun_eq]
    exact ((h1.add (continuousOn_const.mul h2)).add (continuousOn_const.mul h3)).add
      (continuousOn_const.mul h4)
  have hmeasR : AEStronglyMeasurable (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |SSMB_RHSfun α F Ψ z m θ|)
      (Measure.restrict volume Work.Spaces.Iθ) := by
    have hcont : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |SSMB_RHSfun α F Ψ z m θ|)
        (Set.Ioo 0 (Real.pi / 2)) := SSMB_continuous_sinCos2.continuousOn.mul hcontR.abs
    have h1 : AEStronglyMeasurable (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |SSMB_RHSfun α F Ψ z m θ|)
        (Measure.restrict volume (Set.Ioo 0 (Real.pi / 2))) :=
      hcont.aestronglyMeasurable measurableSet_Ioo
    rwa [SSMB_restrict_Ioo_eq_restrict_Iθ] at h1
  have hid : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ
        = SSMB_RHSfun α F Ψ z m θ := by
    intro θ hθ
    rw [SSMB_lzeroPzIterExpansion α hFsm hsm heq m hm hz hθ, hRfun_eq]
    ring
  have hmeasL : AEStronglyMeasurable (fun θ : ℝ => Work.Elliptic.sinCos2 θ *
      |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
      (Measure.restrict volume Work.Spaces.Iθ) := by
    refine hmeasR.congr ?_
    filter_upwards [Work.FTS.EllipticEst.H2W.lzsf_ae_mem_Ioo_Iθ] with θ hθ
    rw [hid θ hθ]
  have hdom : ∀ᵐ θ ∂(Measure.restrict volume Work.Spaces.Iθ),
      ‖Work.Elliptic.sinCos2 θ *
        |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|‖
        ≤ SSMB_Gfun F Ψ z Z m θ := by
    filter_upwards [Work.FTS.EllipticEst.H2W.lzsf_ae_mem_Ioo_Iθ] with θ hθ
    have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsc := SSMB_sinCos2_nonneg_Iθ hIθ
    have habs := SSMB_rhs_abs_le hα hα4 hm hz hzZ (F := F) (Ψ := Ψ) (θ := θ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsc (abs_nonneg _)), hid θ hθ]
    change Work.Elliptic.sinCos2 θ * |SSMB_RHSfun α F Ψ z m θ|
      ≤ Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|
          + Z ^ 2 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 2) Ψ z θ|)
          + (12 * Z) * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 1) Ψ z θ|)
          + 11 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m Ψ z θ|)
    calc Work.Elliptic.sinCos2 θ * |SSMB_RHSfun α F Ψ z m θ|
        ≤ Work.Elliptic.sinCos2 θ * (|Work.Spaces.pzIter m F z θ|
            + Z ^ 2 * |Work.Spaces.pzIter (m + 2) Ψ z θ|
            + (12 * Z) * |Work.Spaces.pzIter (m + 1) Ψ z θ|
            + 11 * |Work.Spaces.pzIter m Ψ z θ|) := mul_le_mul_of_nonneg_left habs hsc
      _ = Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|
            + Z ^ 2 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 2) Ψ z θ|)
            + (12 * Z) * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 1) Ψ z θ|)
            + 11 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m Ψ z θ|) := by ring
  have hIntL : Integrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ *
      |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
      (Measure.restrict volume Work.Spaces.Iθ) :=
    MeasureTheory.Integrable.mono' hGint hmeasL hdom
  refine ⟨hIntL, ?_⟩
  have hmono : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ *
        |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, SSMB_Gfun F Ψ z Z m θ := by
    refine MeasureTheory.integral_mono_ae hIntL hGint ?_
    filter_upwards [hdom, SSMB_ae_sinCos2_nonneg] with θ hb hsc
    rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsc (abs_nonneg _))] at hb
  have hGval : (∫ θ in Work.Spaces.Iθ, SSMB_Gfun F Ψ z Z m θ)
      = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
        + Z ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 2) Ψ z θ|)
        + (12 * Z) * (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 1) Ψ z θ|)
        + 11 * (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m Ψ z θ|) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, SSMB_Gfun F Ψ z Z m θ)
        = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
          + (∫ θ in Work.Spaces.Iθ, Z ^ 2 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 2) Ψ z θ|))
          + (∫ θ in Work.Spaces.Iθ, (12 * Z) * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 1) Ψ z θ|))
          + (∫ θ in Work.Spaces.Iθ, 11 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m Ψ z θ|)) := by
      change (∫ x, (fun θ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|
            + Z ^ 2 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 2) Ψ z θ|)
            + (12 * Z) * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 1) Ψ z θ|)
            + 11 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m Ψ z θ|)) x
          ∂(Measure.restrict volume Work.Spaces.Iθ)) = _
      exact SSMB_integral_add4 hA (hB.const_mul (Z ^ 2)) (hC.const_mul (12 * Z)) (hD.const_mul 11)
    rw [h1, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  have hKb : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
      ≤ 24 * (1 + δ⁻¹ + (δ⁻¹) ^ 2 + (δ⁻¹) ^ 3) * C₀ := hFm.2
  calc (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ *
        |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, SSMB_Gfun F Ψ z Z m θ := hmono
    _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m F z θ|)
        + Z ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 2) Ψ z θ|)
        + (12 * Z) * (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter (m + 1) Ψ z θ|)
        + 11 * (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter m Ψ z θ|) := hGval
    _ ≤ 24 * (1 + δ⁻¹ + (δ⁻¹) ^ 2 + (δ⁻¹) ^ 3) * C₀ + Z ^ 2 * C₀ + (12 * Z) * C₀ + 11 * C₀ := by
        have hZ2 : 0 ≤ Z ^ 2 := sq_nonneg Z
        have h12Z : 0 ≤ 12 * Z := by linarith [le_trans (le_of_lt hz) hzZ]
        nlinarith [hKb, hΨ2.2, hΨ1.2, hΨ0.2, hZ2, h12Z, hC₀]
    _ ≤ (24 * (1 + δ⁻¹ + (δ⁻¹) ^ 2 + (δ⁻¹) ^ 3) + Z ^ 2 + 12 * Z + 11) * C₀ := by ring_nf; nlinarith


/-! ### 6. Constant integrability on `Iθ` -/

theorem SSMB_integrableOn_const_Iθ (c : ℝ) :
    IntegrableOn (fun _ : ℝ => c) Work.Spaces.Iθ := by
  have hvol : (volume Work.Spaces.Iθ) ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  exact integrableOn_const hvol (by simp)

/-! ### 7. The main theorem -/

theorem sliceSourceMassBound_of_external : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.WeakPos2 α F Ψ →
    Work.FTS.EllipticEst.H2W.SliceMassExternal α F Ψ →
    Work.FTS.EllipticEst.H2W.SliceSourceMassBound Ψ := by
  intro α F Ψ hα hα4 hW hM
  obtain ⟨hEq, h0, hpi, hdec, hOF, hOP, hsmAll, hmF⟩ := hW
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsmAll
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := SSMB_smoothOpen_source hΨso hEq
  rw [Work.FTS.EllipticEst.H2W.SliceSourceMassBound, Work.FTS.EllipticEst.H2W.SliceMassExternal] at *
  filter_upwards [hM] with z₀ hz₀
  obtain ⟨ε₀, hε₀pos, hε₀lt, C₀, hC₀nn, hmass⟩ := hz₀
  set ε : ℝ := min ε₀ (z₀ / 2) with hεdef
  have hεpos : 0 < ε := lt_min hε₀pos (by linarith)
  have hεlt : ε < z₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hεle : ε ≤ ε₀ := min_le_left _ _
  have hδpos : 0 < z₀ - ε := by linarith
  have hδZ : z₀ - ε ≤ z₀ + ε := by linarith
  have hZnn : 0 ≤ z₀ + ε := by linarith [le_of_lt hεpos]
  -- the data bound at the reference angle
  obtain ⟨M0, hM0nn, hM0⟩ := Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single
    hΨso (a := z₀ - ε) (b := z₀ + ε) hδpos hδZ 0
  obtain ⟨M1, hM1nn, hM1⟩ := Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single
    hΨso (a := z₀ - ε) (b := z₀ + ε) hδpos hδZ 1
  obtain ⟨M2, hM2nn, hM2⟩ := Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single
    hΨso (a := z₀ - ε) (b := z₀ + ε) hδpos hδZ 2
  obtain ⟨M3, hM3nn, hM3⟩ := Work.FTS.EllipticEst.H2W.exists_sliceData_bound_single
    hΨso (a := z₀ - ε) (b := z₀ + ε) hδpos hδZ 3
  set Md : ℝ := max (max M0 M1) (max M2 M3) with hMddef
  have hMdnn : 0 ≤ Md := by rw [hMddef]; positivity
  have hMdb : ∀ z ∈ Set.Icc (z₀ - ε) (z₀ + ε), ∀ m : ℕ, m ≤ 3 →
      |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
        + |Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z (Real.pi / 4)| ≤ Md := by
    intro z hz m hm
    interval_cases m
    · exact le_trans (hM0 z hz) (le_trans (le_max_left M0 M1) (le_max_left _ _))
    · exact le_trans (hM1 z hz) (le_trans (le_max_right M0 M1) (le_max_left _ _))
    · exact le_trans (hM2 z hz) (le_trans (le_max_left M2 M3) (le_max_right _ _))
    · exact le_trans (hM3 z hz) (le_trans (le_max_right M2 M3) (le_max_right _ _))
  have hKBnn : 0 ≤ 24 * (1 + (z₀ - ε)⁻¹ + ((z₀ - ε)⁻¹) ^ 2 + ((z₀ - ε)⁻¹) ^ 3)
      + (z₀ + ε) ^ 2 + 12 * (z₀ + ε) + 11 := by
    have h1 : 0 ≤ (z₀ - ε)⁻¹ := (inv_pos.mpr hδpos).le
    nlinarith [h1, sq_nonneg ((z₀ - ε)⁻¹), hZnn, sq_nonneg (z₀ + ε)]
  refine ⟨ε, hεpos, hεlt,
    (24 * (1 + (z₀ - ε)⁻¹ + ((z₀ - ε)⁻¹) ^ 2 + ((z₀ - ε)⁻¹) ^ 3)
      + (z₀ + ε) ^ 2 + 12 * (z₀ + ε) + 11) * C₀ + 8 * Md, ?_, ?_⟩
  · have h1 : 0 ≤ (24 * (1 + (z₀ - ε)⁻¹ + ((z₀ - ε)⁻¹) ^ 2 + ((z₀ - ε)⁻¹) ^ 3)
        + (z₀ + ε) ^ 2 + 12 * (z₀ + ε) + 11) * C₀ := mul_nonneg hKBnn hC₀nn
    linarith [h1, hMdnn]
  · intro z hz m hm
    have hzδ : z₀ - ε ≤ z := le_of_lt hz.1
    have hzZ : z ≤ z₀ + ε := le_of_lt hz.2
    have hzpos : 0 < z := lt_of_lt_of_le hδpos hzδ
    have hzmem : z ∈ Set.Ioo (z₀ - ε₀) (z₀ + ε₀) :=
      ⟨by linarith [hz.1, hεle], by linarith [hz.2, hεle]⟩
    obtain ⟨hΨa, hFa⟩ := hmass z hzmem
    have hstep := SSMB_sliceLzeroMass_le hα hα4 hFso hΨso hEq hzpos hδpos hzδ hzZ hC₀nn
      (fun k hk => hΨa k hk) (fun j hj => hFa j hj) m hm
    refine ⟨hstep.1, ?_⟩
    have hMd : |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
        + |Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z (Real.pi / 4)| ≤ Md :=
      hMdb z ⟨hzδ, hzZ⟩ m hm
    have hIntA : IntegrableOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ *
        |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
        Work.Spaces.Iθ := hstep.1
    have hIntv : IntegrableOn (fun _ : ℝ => |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|)
        Work.Spaces.Iθ := SSMB_integrableOn_const_Iθ _
    have hIntd : IntegrableOn (fun _ : ℝ =>
        |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)|)
        Work.Spaces.Iθ := SSMB_integrableOn_const_Iθ _
    have hsplit : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ *
          |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|
          + |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
          + |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)|)
        = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ *
            |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
          + Real.pi / 2 * |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
          + Real.pi / 2 * |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)| := by
      rw [MeasureTheory.integral_add (f := fun θ : ℝ => Work.Elliptic.sinCos2 θ *
              |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|
              + |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|)
            (g := fun _ : ℝ => |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)|)
            (hIntA.add hIntv) hIntd]
      rw [MeasureTheory.integral_add (f := fun θ : ℝ => Work.Elliptic.sinCos2 θ *
              |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
            (g := fun _ : ℝ => |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|) hIntA hIntv]
      rw [SSMB_integral_const_Iθ, SSMB_integral_const_Iθ]
    change (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ *
          |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|
          + |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
          + |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)|) ≤
        (24 * (1 + (z₀ - ε)⁻¹ + ((z₀ - ε)⁻¹) ^ 2 + ((z₀ - ε)⁻¹) ^ 3)
          + (z₀ + ε) ^ 2 + 12 * (z₀ + ε) + 11) * C₀ + 8 * Md
    rw [hsplit]
    have hπ4 : Real.pi / 2 ≤ 4 := by linarith [Real.pi_lt_four]
    have hv : |Work.Spaces.pzIter m Ψ z (Real.pi / 4)| ≤ Md := by
      have h2 : 0 ≤ |Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z (Real.pi / 4)| := abs_nonneg _
      linarith [hMd]
    have hMd' : |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
        + |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)| ≤ Md := hMd
    have hd : |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)| ≤ Md := by
      have h2 : 0 ≤ |Work.Spaces.pzIter m Ψ z (Real.pi / 4)| := abs_nonneg _
      linarith [hMd']
    have hπv : Real.pi / 2 * |Work.Spaces.pzIter m Ψ z (Real.pi / 4)| ≤ 4 * Md := by
      have h0 : 0 ≤ |Work.Spaces.pzIter m Ψ z (Real.pi / 4)| := abs_nonneg _
      nlinarith [hπ4, hv, hMdnn, h0, Real.pi_pos]
    have hπd : Real.pi / 2 * |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)|
        ≤ 4 * Md := by
      have h0 : 0 ≤ |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)| :=
        abs_nonneg _
      nlinarith [hπ4, hd, hMdnn, h0, Real.pi_pos]
    have hKBC : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ *
        |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
        ≤ (24 * (1 + (z₀ - ε)⁻¹ + ((z₀ - ε)⁻¹) ^ 2 + ((z₀ - ε)⁻¹) ^ 3)
            + (z₀ + ε) ^ 2 + 12 * (z₀ + ε) + 11) * C₀ := hstep.2
    linarith [hKBC, hπv, hπd]

end

end Work.FTS.EllipticEst.H2W


