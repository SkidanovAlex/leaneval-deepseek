import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.ae_eq_cauchyTransform_of_isDbarDeriv
import Submission.Work.MRMT.Found.cauchyTransform_memLp_ball
import Submission.Work.MRMT.Found.isDzDeriv_cauchyTransform_eq_beurlingL2
import Submission.Work.MRMT.Found.fw_integral_normSq_cauchyTransform_le
import Submission.Work.MRMT.Found.fw_dz_sub_one_eq_beurlingL2
import Submission.Work.MRMT.Sobolev.mollification_pairing_tendsto
import Submission.Work.MRMT.QC.principal_unique
import Submission.Work.MRMT.Found.memLp_two_mul_of_memL2Loc
import Submission.Work.MRMT.Found.hsolA_spec
import Submission.Work.MRMT.Found.fw_ae_eq_hsolA_of_ae_eq_mul_one_add

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-! ## Auxiliary lemmas

The goal is a uniform `L²` bound on a ball for the deviation `φ - id` of a principal solution
of the Beltrami equation, in terms of the essential supremum of the coefficient.

The proof has three analytic inputs:

* the Cauchy-transform representation `φ - id = C(μ ∂φ)` (`ae_eq_cauchyTransform_of_isDbarDeriv`);
* the explicit `L²` Schur bound for the Cauchy transform of a field supported in `ball 0 M`
  (`lintegral_normSq_cauchyTransform_le` of `fw_integral_normSq_cauchyTransform_le`);
* the uniform `L²` bound `eLpNorm (μ ∂φ) 2 ≤ C ‖μ‖_∞` obtained from the Ahlfors–Bers equation
  `∂φ - 1 = S(μ ∂φ)` by the energy/Neumann-series argument.
-/

/-- The support of a product is contained in the support of the first factor. -/
theorem support_mul_subset {μ D : ℂ → ℂ} :
    Function.support (fun z => μ z * D z) ⊆ Function.support μ := by
  intro z hz
  exact Function.mem_support.mpr fun h => hz (by simp [h])

/-- **`L²` bound for the Cauchy transform on a ball, with explicit constant.**

For `ω ∈ L²(ℂ)` supported in `ball 0 M` and `M, ρ > 0`,
`eLpNorm (C ω) 2 (volume.restrict (ball 0 ρ)) ≤ ofReal (8 √(M ρ)) · eLpNorm ω 2 volume`. -/
theorem eLpNorm_cauchyTransform_ball_le {ω : ℂ → ℂ} {M ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ)
    (hω : MemLp ω 2 (volume : Measure ℂ))
    (hs : Function.support ω ⊆ Metric.ball 0 M) :
    eLpNorm (cauchyTransform ω) 2 (volume.restrict (Metric.ball 0 ρ)) ≤
      ENNReal.ofReal (8 * Real.sqrt (M * ρ)) * eLpNorm ω 2 (volume : Measure ℂ) := by
  have hcsm : AEStronglyMeasurable (cauchyTransform ω)
      (volume.restrict (Metric.ball 0 ρ)) :=
    (cauchyTransform_memLp_ball hM hρ hω hs).1.aestronglyMeasurable
  have hωsm : AEStronglyMeasurable ω (volume : Measure ℂ) := hω.aestronglyMeasurable
  have hlin := lintegral_normSq_cauchyTransform_le hM.le hρ.le hω hs
  have hL : eLpNorm (cauchyTransform ω) 2 (volume.restrict (Metric.ball 0 ρ))
      = (∫⁻ z in Metric.ball 0 ρ, ‖cauchyTransform ω z‖ₑ ^ 2) ^ ((1 : ℝ) / 2) :=
    eLpNorm_two _ _ hcsm
  have hR : eLpNorm ω 2 (volume : Measure ℂ)
      = (∫⁻ z, ‖ω z‖ₑ ^ 2) ^ ((1 : ℝ) / 2) := eLpNorm_two ω volume hωsm
  rw [hL, hR]
  have hconst : (64 : ℝ) * M * ρ = (8 * Real.sqrt (M * ρ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  calc (∫⁻ z in Metric.ball 0 ρ, ‖cauchyTransform ω z‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (64 * M * ρ) * ∫⁻ z, ‖ω z‖ₑ ^ 2) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hlin (by norm_num)
    _ = (ENNReal.ofReal (64 * M * ρ)) ^ ((1 : ℝ) / 2)
          * (∫⁻ z, ‖ω z‖ₑ ^ 2) ^ ((1 : ℝ) / 2) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = ENNReal.ofReal ((64 * M * ρ) ^ ((1 : ℝ) / 2))
          * (∫⁻ z, ‖ω z‖ₑ ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    _ = ENNReal.ofReal (8 * Real.sqrt (M * ρ)) * (∫⁻ z, ‖ω z‖ₑ ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [hconst, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]

/-- The Cauchy-transform representation `φ - id = C(μ ∂φ)` for a function with `1/‖z‖` decay
whose weak `∂̄`-derivative is `μ ∂φ`. -/
theorem sub_id_ae_eq_cauchyTransform_of_weakDeriv {φ D μ : ℂ → ℂ} {R : ℝ}
    (hdec : ∃ C R' : ℝ, ∀ z : ℂ, R' ≤ ‖z‖ → ‖φ z - z‖ ≤ C / ‖z‖)
    (hsupp : Function.support μ ⊆ Metric.closedBall 0 R)
    (hint : Integrable (fun z => μ z * D z) (volume : Measure ℂ))
    (hgzb : IsDbarDeriv φ (fun z => μ z * D z)) :
    (fun z => φ z - z) =ᵐ[(volume : Measure ℂ)]
      cauchyTransform (fun z => μ z * D z) := by
  have hsubdb : IsDbarDeriv (fun z => φ z - z) (fun z => μ z * D z) := by
    have h := Work.MRMT.QC.IsDbarDeriv.sub hgzb Work.MRMT.Sobolev.isDbarDeriv_id_zero_aux
    exact Work.MRMT.Weyl.isDbarDeriv_congr h (fun z => sub_zero _)
  exact ae_eq_cauchyTransform_of_isDbarDeriv hsubdb.1 hsubdb hint
    (support_mul_subset.trans hsupp) hdec

/-- **The Ahlfors–Bers equation `∂φ - 1 = S(μ ∂φ)` in `L²` form.**

If `φ` has `1/‖z‖` decay, its weak `∂`- and `∂̄`-derivatives are `D` and `μ D`, and the latter
is integrable with compact support and square integrable, then `D - 1` agrees almost everywhere
with the Beurling transform of `μ D`. -/
theorem sub_one_ae_eq_beurlingL2_of_weakDeriv {φ D μ : ℂ → ℂ} {R : ℝ}
    (hdec : ∃ C R' : ℝ, ∀ z : ℂ, R' ≤ ‖z‖ → ‖φ z - z‖ ≤ C / ‖z‖)
    (hsupp : Function.support μ ⊆ Metric.closedBall 0 R)
    (hint : Integrable (fun z => μ z * D z) (volume : Measure ℂ))
    (hgz : IsDzDeriv φ D)
    (hgzb : IsDbarDeriv φ (fun z => μ z * D z))
    (hLp : MemLp (fun z => μ z * D z) 2 (volume : Measure ℂ)) :
    (fun z => D z - 1) =ᵐ[(volume : Measure ℂ)]
      (((beurlingL2 (hLp.toLp (fun z => μ z * D z))) :
        Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) := by
  have hcs : HasCompactSupport (fun z => μ z * D z) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) R)
      (support_mul_subset.trans hsupp)
  -- `∂(φ - id) = D - 1`
  have hsubz : IsDzDeriv (fun z => φ z - z) (fun z => D z - 1) := by
    have h := Work.MRMT.QC.IsDzDeriv.sub hgz Work.MRMT.Sobolev.isDzDeriv_id
    exact h
  -- `φ - id = C(μD)`
  have hct := sub_id_ae_eq_cauchyTransform_of_weakDeriv hdec hsupp hint hgzb
  -- `∂(C(μD)) = S(μD)`
  have hcts : IsDzDeriv (cauchyTransform (fun z => μ z * D z))
      (((beurlingL2 (hLp.toLp (fun z => μ z * D z))) :
        Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) :=
    isDzDeriv_cauchyTransform_eq_beurlingL2 hLp hcs
  have hcts' : IsDzDeriv (fun z => φ z - z)
      (((beurlingL2 (hLp.toLp (fun z => μ z * D z))) :
        Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) :=
    isDzDeriv_congr_ae_lhs hcts hct.symm
  exact Work.MRMT.QC.is_dz_deriv_unique hsubz hcts'


/-- `MemLp` for an a.e. bounded function whose support is contained in a closed ball. -/
private theorem memLp_two_of_ae_bound_of_support {f : ℂ → ℂ} {C S : ℝ}
    (hmeas : AEStronglyMeasurable f (volume : Measure ℂ))
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖f z‖ ≤ C)
    (hs : Function.support f ⊆ Metric.closedBall 0 S) : MemLp f 2 (volume : Measure ℂ) := by
  set B : Set ℂ := Metric.ball 0 (S + 1) with hB
  have hzero : ∀ z ∉ B, f z = 0 := by
    intro z hz
    by_contra hne
    have h1 : z ∈ Metric.closedBall 0 S := hs (Function.mem_support.mpr hne)
    have h2 : ‖z‖ ≤ S := by simpa [Metric.mem_closedBall, dist_zero_right] using h1
    refine hz ?_
    simp only [hB, Metric.mem_ball, dist_zero_right]
    linarith
  have heq : f = B.indicator f := by
    funext z
    by_cases hz : z ∈ B
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz, hzero z hz]
  rw [heq, memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet]
  have hfin : IsFiniteMeasure ((volume : Measure ℂ).restrict B) := by
    rw [isFiniteMeasure_restrict]
    exact MeasureTheory.measure_ball_ne_top
  refine MemLp.of_bound hmeas.restrict (max C 0) ?_
  filter_upwards [MeasureTheory.ae_restrict_of_ae hb] with z hzb
  exact le_trans hzb (le_max_left _ _)

/-- **Uniform `L²` bound on `μ ∂φ` via the Ahlfors–Bers `L²` solution.**

If `∂̄φ = μ ∂φ` with `‖μ‖ ≤ k < 1` a.e. and bounded support, and the Ahlfors–Bers equation
`∂φ - 1 = S(μ ∂φ)` holds a.e., then

`eLpNorm (μ ∂φ) 2 volume ≤ ofReal (√(vol B)/(1 - k)) · eLpNorm μ ⊤ volume`, `B = ball 0 (max R 0 + 1)`.

The proof identifies `μ ∂φ` with the Neumann-series solution `hsolA μ` of `h = μ (1 + S h)` and
uses `‖hsolA μ‖ ≤ (1-k)⁻¹ ‖μ‖₂`, together with `eLpNorm μ 2 ≤ eLpNorm μ ⊤ · √(vol B)`
(Hölder against the indicator of `B`, which contains the support of `μ`). -/
private theorem energy_bound_of_beurling_eq {μ D : ℂ → ℂ} {R k : ℝ} (hk : k < 1)
    (hsupp : Function.support μ ⊆ Metric.closedBall 0 R)
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ))
    (hμLp : MemLp μ 2 (volume : Measure ℂ))
    (hωLp : MemLp (fun z => μ z * D z) 2 (volume : Measure ℂ))
    (hbeur : (fun z => D z - 1) =ᵐ[(volume : Measure ℂ)]
      (((beurlingL2 (hωLp.toLp (fun z => μ z * D z))) :
        Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)) :
    eLpNorm (fun z => μ z * D z) 2 (volume : Measure ℂ) ≤
      ENNReal.ofReal (Real.sqrt (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal)
        / (1 - k)) * eLpNorm μ ⊤ (volume : Measure ℂ) := by
  classical
  have hAdm : Admissible μ :=
    ⟨hμmeas, ⟨k, hk, hb⟩, Metric.isBounded_closedBall.subset hsupp⟩
  -- the Ahlfors--Bers equation solved by `μ ∂φ`
  have hω_eq : (fun z => μ z * D z) =ᵐ[(volume : Measure ℂ)]
      fun z => μ z * (1 + ((beurlingL2 (hωLp.toLp (fun z => μ z * D z))) :
        Lp ℂ 2 (volume : Measure ℂ)) z) := by
    filter_upwards [hbeur] with z hz
    rw [← hz]
    ring
  have hsol_eq : (fun z => μ z * D z) =ᵐ[(volume : Measure ℂ)]
      (((hsolA μ hAdm hμLp) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) :=
    fw_ae_eq_hsolA_of_ae_eq_mul_one_add hk hAdm hμLp hωLp hb hω_eq
  -- the `L²` bound for `hsolA`
  have hnorm : ‖hsolA μ hAdm hμLp‖ ≤ (1 - k)⁻¹ * ‖hμLp.toLp μ‖ :=
    (hsolA_spec hAdm hμLp hk hb).2.1
  have hstep1 : eLpNorm (fun z => μ z * D z) 2 (volume : Measure ℂ) ≤
      ENNReal.ofReal ((1 - k)⁻¹) * eLpNorm μ 2 (volume : Measure ℂ) := by
    have hm1 : eLpNorm (((hsolA μ hAdm hμLp) : Lp ℂ 2 (volume : Measure ℂ)) :
          ℂ → ℂ) 2 (volume : Measure ℂ) = ENNReal.ofReal ‖hsolA μ hAdm hμLp‖ := by
      have hne : eLpNorm (((hsolA μ hAdm hμLp) : Lp ℂ 2 (volume : Measure ℂ)) :
            ℂ → ℂ) 2 (volume : Measure ℂ) ≠ ⊤ :=
        (Lp.memLp (hsolA μ hAdm hμLp)).eLpNorm_lt_top.ne
      rw [Lp.norm_def, ENNReal.ofReal_toReal hne]
    have hm2 : eLpNorm μ 2 (volume : Measure ℂ) = ENNReal.ofReal ‖hμLp.toLp μ‖ := by
      have hne : eLpNorm μ 2 (volume : Measure ℂ) ≠ ⊤ := hμLp.eLpNorm_lt_top.ne
      rw [Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp hμLp), ENNReal.ofReal_toReal hne]
    rw [eLpNorm_congr_ae hsol_eq, hm1, hm2, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hnorm
  -- `eLpNorm μ 2 ≤ eLpNorm μ ⊤ * √(vol B)` by Hölder against the indicator of `B`
  set B : Set ℂ := Metric.ball 0 (max R 0 + 1) with hB
  have hVtop : (volume : Measure ℂ) B ≠ ⊤ := by
    rw [hB]
    exact ne_top_of_le_ne_top (isCompact_closedBall (0 : ℂ) (max R 0 + 1)).measure_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  have hstep2 : eLpNorm μ 2 (volume : Measure ℂ) ≤
      eLpNorm μ ⊤ (volume : Measure ℂ) *
        ENNReal.ofReal (Real.sqrt (((volume : Measure ℂ) B).toReal)) := by
    have hmul : (fun z => μ z * (B.indicator (fun _ => (1 : ℂ))) z)
        =ᵐ[(volume : Measure ℂ)] μ := by
      filter_upwards with z
      by_cases hz : z ∈ B
      · simp [Set.indicator_of_mem hz]
      · have hz0 : μ z = 0 := by
          by_contra hne
          refine hz ?_
          have h1 : z ∈ Metric.closedBall 0 R := hsupp (Function.mem_support.mpr hne)
          have h2 : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using h1
          simp only [hB, Metric.mem_ball, dist_zero_right]
          have h3 : R ≤ max R 0 := le_max_left R 0
          have h4 : (0 : ℝ) ≤ max R 0 := le_max_right R 0
          linarith
        simp [Set.indicator_of_notMem hz, hz0]
    have hholder := eLpNorm_le_eLpNorm_top_mul_eLpNorm (μ := (volume : Measure ℂ)) (p := 2)
      (b := fun a b : ℂ => a * b) (c := 1) (f := μ)
      (g := B.indicator (fun _ => (1 : ℂ)))
      (by fun_prop) hμmeas
      (by filter_upwards with z; rw [one_mul]; exact le_of_eq (nnnorm_mul (μ z) _))
    calc eLpNorm μ 2 (volume : Measure ℂ)
        = eLpNorm (fun z => μ z * (B.indicator (fun _ => (1 : ℂ))) z) 2
            (volume : Measure ℂ) := (eLpNorm_congr_ae hmul).symm
      _ ≤ (1 : ℝ≥0∞) * eLpNorm μ ⊤ (volume : Measure ℂ) *
            eLpNorm (B.indicator (fun _ => (1 : ℂ))) 2 (volume : Measure ℂ) := hholder
      _ = eLpNorm μ ⊤ (volume : Measure ℂ) * (((volume : Measure ℂ) B) ^ ((1 : ℝ) / 2)) := by
          have hind : eLpNorm (B.indicator (fun _ => (1 : ℂ))) 2 (volume : Measure ℂ)
              = ((volume : Measure ℂ) B) ^ ((1 : ℝ) / 2) := by
            rw [show eLpNorm (B.indicator (fun _ => (1 : ℂ))) 2 (volume : Measure ℂ)
                = ‖(1 : ℂ)‖ₑ * ((volume : Measure ℂ) B) ^ (1 / (2 : ℝ)) from
              eLpNorm_indicator_const measurableSet_ball.nullMeasurableSet (by norm_num)
                (by norm_num)]
            norm_num
          rw [hind, one_mul]
      _ = eLpNorm μ ⊤ (volume : Measure ℂ) *
            ENNReal.ofReal (Real.sqrt (((volume : Measure ℂ) B).toReal)) := by
          congr 1
          conv_lhs => rw [← ENNReal.ofReal_toReal hVtop]
          rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0:ℝ) ≤ 1/2),
            Real.sqrt_eq_rpow]
  calc eLpNorm (fun z => μ z * D z) 2 (volume : Measure ℂ)
      ≤ ENNReal.ofReal ((1 - k)⁻¹) * eLpNorm μ 2 (volume : Measure ℂ) := hstep1
    _ ≤ ENNReal.ofReal ((1 - k)⁻¹) * (eLpNorm μ ⊤ (volume : Measure ℂ) *
          ENNReal.ofReal (Real.sqrt (((volume : Measure ℂ) B).toReal))) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = ENNReal.ofReal ((1 - k)⁻¹ * Real.sqrt (((volume : Measure ℂ) B).toReal)) *
          eLpNorm μ ⊤ (volume : Measure ℂ) := by
        rw [mul_left_comm, mul_comm, ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (Real.sqrt (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal)
          / (1 - k)) * eLpNorm μ ⊤ (volume : Measure ℂ) := by
        have harg : (1 - k)⁻¹ * Real.sqrt (((volume : Measure ℂ) B).toReal)
            = Real.sqrt (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal)
              / (1 - k) := by
          rw [hB, inv_mul_eq_div]
        rw [harg]

/-! ## The main theorem -/

/-- **Uniform `L²` bound for the deviation `φ - id` of a family of principal solutions.**

This is the `L²` smallness input for the locally uniform convergence of the principal solutions
to the identity: the deviation on `ball 0 ρ` is controlled by the essential supremum of the
coefficient, uniformly in the family. -/
theorem eLpNorm_dev_le_family_of_weakDeriv {μs : ℕ → ℂ → ℂ} (d : ∀ j, PrincipalData (μs j)) {R k : ℝ}
    (hk : k < 1)
    (hsupp : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 R)
    (hb : ∀ j, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μs j z‖ ≤ k)
    (hwk : ∀ j, ∃ D : ℂ → ℂ, Work.MRMT.MemL2Loc D ∧
      Work.MRMT.IsDzDeriv ((d j).φ : ℂ → ℂ) D ∧
      Work.MRMT.IsDbarDeriv ((d j).φ : ℂ → ℂ) (fun z => μs j z * D z))
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
      MeasureTheory.eLpNorm (fun z => ((d j).φ : ℂ → ℂ) z - z) 2
          (MeasureTheory.volume.restrict (Metric.ball 0 ρ))
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (μs j) ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  have hR₀pos : (0 : ℝ) < max R 0 + 1 := by positivity
  have hsupp' : ∀ j, Function.support (μs j) ⊆ Metric.ball 0 (max R 0 + 1) := by
    intro j z hz
    have h1 : ‖z‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hsupp j hz
    rw [Metric.mem_ball, dist_zero_right]
    have h2 : (0 : ℝ) ≤ max R 0 := le_max_right R 0
    have h3 : R ≤ max R 0 := le_max_left R 0
    linarith
  refine ⟨8 * Real.sqrt ((max R 0 + 1) * ρ) *
      Real.sqrt (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal) / (1 - k) + 1,
    by positivity, fun j => ?_⟩
  by_cases hmeas : AEStronglyMeasurable (μs j) (volume : Measure ℂ)
  · obtain ⟨D, hDloc, hgz, hgzb⟩ := hwk j
    have hωmeas : AEStronglyMeasurable (fun z => μs j z * D z) (volume : Measure ℂ) :=
      hgzb.2.1.aestronglyMeasurable
    have hωLp : MemLp (fun z => μs j z * D z) 2 (volume : Measure ℂ) :=
      memLp_two_mul_of_memL2Loc hωmeas hDloc (hb j) (hsupp j)
    have hωcs : HasCompactSupport (fun z => μs j z * D z) :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) R)
        (support_mul_subset.trans (hsupp j))
    have hωint : Integrable (fun z => μs j z * D z) (volume : Measure ℂ) :=
      Work.MRMT.Sobolev.integrable_of_memLp_two_hasCompactSupport hωLp hωcs
    -- the Ahlfors--Bers equation `∂φ - 1 = S(μ ∂φ)`
    have hkeyae : (fun z => D z - 1) =ᵐ[(volume : Measure ℂ)]
        (((beurlingL2 (hωLp.toLp (fun z => μs j z * D z))) :
          Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) :=
      sub_one_ae_eq_beurlingL2_of_weakDeriv ⟨(d j).C, (d j).R, (d j).decay⟩
        (hsupp j) hωint hgz hgzb hωLp
    -- the Beurling transform is an isometry of `L²`
    have hiso : eLpNorm (((beurlingL2 (hωLp.toLp (fun z => μs j z * D z))) :
          Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) 2 (volume : Measure ℂ)
        = eLpNorm (fun z => μs j z * D z) 2 (volume : Measure ℂ) := by
      have hne1 : eLpNorm (((beurlingL2 (hωLp.toLp (fun z => μs j z * D z))) :
            Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) 2 (volume : Measure ℂ) ≠ ⊤ :=
        (Lp.memLp (beurlingL2 (hωLp.toLp (fun z => μs j z * D z)))).eLpNorm_lt_top.ne
      have hne2 : eLpNorm (fun z => μs j z * D z) 2 (volume : Measure ℂ) ≠ ⊤ :=
        hωLp.eLpNorm_lt_top.ne
      have h1 : eLpNorm (((beurlingL2 (hωLp.toLp (fun z => μs j z * D z))) :
            Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) 2 (volume : Measure ℂ)
          = ENNReal.ofReal ‖beurlingL2 (hωLp.toLp (fun z => μs j z * D z))‖ := by
        rw [Lp.norm_def, ENNReal.ofReal_toReal hne1]
      have h2 : eLpNorm (fun z => μs j z * D z) 2 (volume : Measure ℂ)
          = ENNReal.ofReal ‖hωLp.toLp (fun z => μs j z * D z)‖ := by
        rw [Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp hωLp),
          ENNReal.ofReal_toReal hne2]
      rw [h1, h2, norm_beurlingL2]
    -- the comparison needed by the energy bound
    have hkeyE : eLpNorm (fun z => D z - 1) 2
        (volume.restrict (Metric.ball 0 (max R 0 + 1)))
        ≤ eLpNorm (fun z => μs j z * D z) 2 (volume : Measure ℂ) := by
      calc eLpNorm (fun z => D z - 1) 2 (volume.restrict (Metric.ball 0 (max R 0 + 1)))
          = eLpNorm (((beurlingL2 (hωLp.toLp (fun z => μs j z * D z))) :
              Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) 2
              (volume.restrict (Metric.ball 0 (max R 0 + 1))) :=
            eLpNorm_congr_ae
              (hkeyae.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self))
        _ ≤ eLpNorm (((beurlingL2 (hωLp.toLp (fun z => μs j z * D z))) :
              Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) 2 (volume : Measure ℂ) :=
            eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm (fun z => μs j z * D z) 2 (volume : Measure ℂ) := hiso
    -- the uniform `L²` bound on `μ ∂φ`
    have hμLp : MemLp (μs j) 2 (volume : Measure ℂ) :=
      memLp_two_of_ae_bound_of_support hmeas (hb j) (hsupp j)
    have henergy : eLpNorm (fun z => μs j z * D z) 2 (volume : Measure ℂ)
        ≤ ENNReal.ofReal (Real.sqrt
              (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal) / (1 - k)) *
          eLpNorm (μs j) ⊤ (volume : Measure ℂ) :=
      energy_bound_of_beurling_eq hk (hsupp j) (hb j) hmeas hμLp hωLp hkeyae
    -- the representation `φ - id = C(μ ∂φ)`
    have hct : (fun z => ((d j).φ : ℂ → ℂ) z - z) =ᵐ[(volume : Measure ℂ)]
        cauchyTransform (fun z => μs j z * D z) :=
      sub_id_ae_eq_cauchyTransform_of_weakDeriv ⟨(d j).C, (d j).R, (d j).decay⟩
        (hsupp j) hωint hgzb
    have hcauchy := eLpNorm_cauchyTransform_ball_le (ω := fun z => μs j z * D z)
      (M := max R 0 + 1) (ρ := ρ) hR₀pos hρ hωLp (support_mul_subset.trans (hsupp' j))
    calc eLpNorm (fun z => ((d j).φ : ℂ → ℂ) z - z) 2
            (volume.restrict (Metric.ball 0 ρ))
        = eLpNorm (cauchyTransform (fun z => μs j z * D z)) 2
            (volume.restrict (Metric.ball 0 ρ)) :=
          eLpNorm_congr_ae (hct.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self))
      _ ≤ ENNReal.ofReal (8 * Real.sqrt ((max R 0 + 1) * ρ)) *
            eLpNorm (fun z => μs j z * D z) 2 (volume : Measure ℂ) := hcauchy
      _ ≤ ENNReal.ofReal (8 * Real.sqrt ((max R 0 + 1) * ρ)) *
            (ENNReal.ofReal (Real.sqrt
                (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal) / (1 - k)) *
              eLpNorm (μs j) ⊤ (volume : Measure ℂ)) := by
          exact mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = ENNReal.ofReal (8 * Real.sqrt ((max R 0 + 1) * ρ) *
            (Real.sqrt (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal)
              / (1 - k))) *
            eLpNorm (μs j) ⊤ (volume : Measure ℂ) := by
          conv_lhs => rw [← mul_assoc]
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (8 * Real.sqrt ((max R 0 + 1) * ρ) *
            Real.sqrt (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal)
              / (1 - k) + 1) *
            eLpNorm (μs j) ⊤ (volume : Measure ℂ) := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by positivity)
          have hEq : 8 * Real.sqrt ((max R 0 + 1) * ρ) *
              (Real.sqrt (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal)
                / (1 - k))
              = 8 * Real.sqrt ((max R 0 + 1) * ρ) *
                Real.sqrt (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal)
                  / (1 - k) := by ring
          linarith
  · rw [MeasureTheory.eLpNorm_of_not_aestronglyMeasurable hmeas, ENNReal.mul_top]
    · exact le_top
    · refine ne_of_gt (ENNReal.ofReal_pos.mpr ?_)
      have h1 : (0 : ℝ) ≤ Real.sqrt ((max R 0 + 1) * ρ) := Real.sqrt_nonneg _
      have h2 : (0 : ℝ) ≤ Real.sqrt
          (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal) := Real.sqrt_nonneg _
      have h3 : (0 : ℝ) < 1 - k := by linarith
      have h4 : (0 : ℝ) ≤ 8 * Real.sqrt ((max R 0 + 1) * ρ) * Real.sqrt
          (((volume : Measure ℂ) (Metric.ball 0 (max R 0 + 1))).toReal) / (1 - k) := by
        positivity
      linarith

end Work.MRMT.Found
