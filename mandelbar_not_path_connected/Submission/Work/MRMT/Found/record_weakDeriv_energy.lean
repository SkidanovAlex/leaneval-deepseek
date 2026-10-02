import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.records_agree
import Submission.Work.MRMT.Found.memLp_two_mul_of_memL2Loc
import Submission.Work.MRMT.Found.eLpNorm_two_le_ofReal_sqrt_mul_eLpNorm_top
import Submission.Work.MRMT.Found.eLpNorm_dev_le_family_of_weakDeriv
import Submission.Work.MRMT.Found.hsolA_spec
import Submission.Work.MRMT.Found.fw_ae_eq_hsolA_of_ae_eq_mul_one_add
import Submission.Work.MRMT.Found.memLp_two_of_ae_bound_of_support
import Submission.Work.MRMT.Found.sqrt_volume_closedBall
import Submission.Work.MRMT.Sobolev.mollification_pairing_tendsto

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

/-!
# The energy bound for the weak `∂`-derivative of the principal solution

`record_weakDeriv_energy`: for an admissible coefficient `μ` with `‖μ‖ ≤ k < 1` a.e. and
`support μ ⊆ closedBall 0 R`, the `L²_loc` limit `recD d` of `∂(F n)` for a record
`d : PrincipalData μ` is a weak `∂`-derivative of `φ = d.φ` whose `μ`-multiple is the weak
`∂̄`-derivative, and its deviation from `1` satisfies the global `L²` bound

`eLpNorm (recD d - 1) 2 volume ≤ ofReal (√(π R²)/(1-k)) · eLpNorm μ ⊤ volume`.

The proof composes three facts:

* the Beurling identity `recD d - 1 = S(μ · recD d)` (`sub_one_ae_eq_beurlingL2_of_weakDeriv`),
  so that `eLpNorm (recD d - 1) 2 = ‖S(μ · recD d)‖₂ = ‖μ · recD d‖₂` (isometry of `S`);
* the Ahlfors–Bers equation `ω = μ (1 + S ω)` solved by `ω = μ · recD d`, so that
  `ω =ᵐ hsolA μ` and `‖ω‖₂ ≤ (1-k)⁻¹ ‖μ‖₂` (`hsolA_spec`);
* `‖μ‖₂ ≤ √(vol (closedBall 0 R)) · eLpNorm μ ⊤` (`eLpNorm_two_le_ofReal_sqrt_mul_eLpNorm_top`
  applied after restricting to the (finite measure) closed ball containing `support μ`).

The two degenerate cases `k < 0` and `R < 0` are treated separately: they force `μ` to vanish
(identically, resp. almost everywhere), hence `eLpNorm μ ⊤ volume = 0` and the bound is trivial.
-/

private theorem core_eLpNorm_dev_le {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ)
    {R k : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) (hR : 0 ≤ R)
    (hsupp : Function.support μ ⊆ Metric.closedBall (0 : ℂ) R)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) :
    MeasureTheory.eLpNorm (fun z => recD d z - 1) 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) ≤
      ENNReal.ofReal (Real.sqrt ((MeasureTheory.volume (Metric.closedBall (0 : ℂ) R)).toReal)
          / (1 - k)) *
        MeasureTheory.eLpNorm μ ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  have h1k : 0 < 1 - k := by linarith
  have hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ) := hμ.meas
  have hμLp : MemLp μ 2 (volume : Measure ℂ) :=
    memLp_two_of_ae_bound_of_support hμmeas hb hsupp
  obtain ⟨hdz, hdzbar⟩ := recD_weakDeriv d
  -- `ω = μ · recD d` is in `L²` with compact support, hence integrable
  have hωLp : MemLp (fun z => μ z * recD d z) 2 (volume : Measure ℂ) :=
    memLp_two_mul_of_memL2Loc hdzbar.2.1.aestronglyMeasurable (memL2Loc_recD d) hb hsupp
  have hωsupp : Function.support (fun z => μ z * recD d z) ⊆ Metric.closedBall (0 : ℂ) R :=
    support_mul_subset.trans hsupp
  have hωcs : HasCompactSupport (fun z => μ z * recD d z) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) R) hωsupp
  have hωint : Integrable (fun z => μ z * recD d z) (volume : Measure ℂ) :=
    Work.MRMT.Sobolev.integrable_of_memLp_two_hasCompactSupport hωLp hωcs
  set g : Lp ℂ 2 (volume : Measure ℂ) := beurlingL2 (hωLp.toLp (fun z => μ z * recD d z))
    with hgdef
  -- the Beurling identity `recD d - 1 = S ω`
  have hbeur : (fun z => recD d z - 1) =ᵐ[(volume : Measure ℂ)]
      ((g : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) :=
    sub_one_ae_eq_beurlingL2_of_weakDeriv ⟨d.C, d.R, d.decay⟩ hsupp hωint hdz hdzbar hωLp
  -- the Ahlfors--Bers equation for `ω` and the identification with `hsolA μ`
  have hω_eq : (fun z => μ z * recD d z) =ᵐ[(volume : Measure ℂ)]
      fun z => μ z * (1 + ((g : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z) := by
    filter_upwards [hbeur] with z hz
    rw [← hz]
    ring
  have hsol : (fun z => μ z * recD d z) =ᵐ[(volume : Measure ℂ)]
      (((hsolA μ hμ hμLp) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) :=
    fw_ae_eq_hsolA_of_ae_eq_mul_one_add hk hμ hμLp hωLp hb hω_eq
  have hLpeq : hωLp.toLp (fun z => μ z * recD d z) = hsolA μ hμ hμLp := by
    rw [Lp.ext_iff]
    filter_upwards [MemLp.coeFn_toLp hωLp, hsol] with z h1 h2
    rw [h1, h2]
  have hnormω : ‖hωLp.toLp (fun z => μ z * recD d z)‖ ≤ (1 - k)⁻¹ * ‖hμLp.toLp μ‖ := by
    rw [hLpeq]
    exact (hsolA_spec hμ hμLp hk hb).2.1
  -- the left-hand side is the norm of `S ω`, and `S` is an isometry
  have hLHS : MeasureTheory.eLpNorm (fun z => recD d z - 1) 2 (volume : Measure ℂ)
      = ENNReal.ofReal ‖g‖ := by
    have hne : MeasureTheory.eLpNorm ((g : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) 2
        (volume : Measure ℂ) ≠ ⊤ := (Lp.memLp g).eLpNorm_lt_top.ne
    rw [eLpNorm_congr_ae hbeur, Lp.norm_def, ENNReal.ofReal_toReal hne]
  have hstep1 : MeasureTheory.eLpNorm (fun z => recD d z - 1) 2 (volume : Measure ℂ) ≤
      ENNReal.ofReal ((1 - k)⁻¹) * MeasureTheory.eLpNorm μ 2 (volume : Measure ℂ) := by
    have hm2 : MeasureTheory.eLpNorm μ 2 (volume : Measure ℂ) = ENNReal.ofReal ‖hμLp.toLp μ‖ := by
      have hne : MeasureTheory.eLpNorm μ 2 (volume : Measure ℂ) ≠ ⊤ := hμLp.eLpNorm_lt_top.ne
      rw [Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp hμLp), ENNReal.ofReal_toReal hne]
    rw [hLHS, hgdef, norm_beurlingL2, hm2, ← ENNReal.ofReal_mul (inv_nonneg.mpr h1k.le)]
    exact ENNReal.ofReal_le_ofReal hnormω
  -- `eLpNorm μ 2 ≤ √(vol (closedBall 0 R)) · eLpNorm μ ⊤`
  have hstep2 : MeasureTheory.eLpNorm μ 2 (volume : Measure ℂ) ≤
      ENNReal.ofReal (Real.sqrt ((MeasureTheory.volume (Metric.closedBall (0 : ℂ) R)).toReal)) *
        MeasureTheory.eLpNorm μ ⊤ (volume : Measure ℂ) := by
    set ν : Measure ℂ := (volume : Measure ℂ).restrict (Metric.closedBall (0 : ℂ) R) with hνdef
    have hνtop : ν Set.univ < ⊤ := by
      rw [hνdef, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact (isCompact_closedBall (0 : ℂ) R).measure_lt_top
    have hνuniv : ν Set.univ = (MeasureTheory.volume : MeasureTheory.Measure ℂ)
        (Metric.closedBall (0 : ℂ) R) := by
      rw [hνdef, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    have hmain := eLpNorm_two_le_ofReal_sqrt_mul_eLpNorm_top (ν := ν) hνtop
      (hμmeas.mono_measure Measure.restrict_le_self)
    rw [hνuniv] at hmain
    have h1 : MeasureTheory.eLpNorm μ 2 (volume : Measure ℂ) = MeasureTheory.eLpNorm μ 2 ν :=
      (eLpNorm_restrict_eq_of_support_subset hμmeas hsupp).symm
    rw [h1]
    exact hmain.trans (mul_le_mul_right
      (eLpNorm_mono_measure μ Measure.restrict_le_self) _)
  calc MeasureTheory.eLpNorm (fun z => recD d z - 1) 2 (volume : Measure ℂ)
      ≤ ENNReal.ofReal ((1 - k)⁻¹) * MeasureTheory.eLpNorm μ 2 (volume : Measure ℂ) := hstep1
    _ ≤ ENNReal.ofReal ((1 - k)⁻¹) *
          (ENNReal.ofReal (Real.sqrt ((MeasureTheory.volume (Metric.closedBall (0 : ℂ) R)).toReal)) *
            MeasureTheory.eLpNorm μ ⊤ (volume : Measure ℂ)) := mul_le_mul_right hstep2 _
    _ = ENNReal.ofReal (Real.sqrt ((MeasureTheory.volume (Metric.closedBall (0 : ℂ) R)).toReal)
          / (1 - k)) * MeasureTheory.eLpNorm μ ⊤ (volume : Measure ℂ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr h1k.le), inv_mul_eq_div]

theorem record_weakDeriv_energy {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ) {R k : ℝ}
    (hk : k < 1)
    (hsupp : Function.support μ ⊆ Metric.closedBall 0 R)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) :
    ∃ D : ℂ → ℂ, Work.MRMT.MemL2Loc D ∧
      Work.MRMT.IsDzDeriv (d.φ : ℂ → ℂ) D ∧
      Work.MRMT.IsDbarDeriv (d.φ : ℂ → ℂ) (fun z => μ z * D z) ∧
      MeasureTheory.eLpNorm (fun z => D z - 1) 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)
        ≤ ENNReal.ofReal (Real.sqrt (Real.pi * R ^ 2) / (1 - k)) *
          MeasureTheory.eLpNorm μ ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  have hk' : max k 0 < 1 := max_lt hk zero_lt_one
  have hk0' : 0 ≤ max k 0 := le_max_right k 0
  have hR' : 0 ≤ max R 0 := le_max_right R 0
  have hsupp' : Function.support μ ⊆ Metric.closedBall (0 : ℂ) (max R 0) :=
    hsupp.trans (Metric.closedBall_subset_closedBall (le_max_left R 0))
  have hb' : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ max k 0 :=
    hb.mono fun z hz => hz.trans (le_max_left k 0)
  have hcore := core_eLpNorm_dev_le hμ d hk0' hk' hR' hsupp' hb'
  refine ⟨recD d, memL2Loc_recD d, (recD_weakDeriv d).1, (recD_weakDeriv d).2, ?_⟩
  by_cases hk0 : 0 ≤ k
  · by_cases hR0 : 0 ≤ R
    · -- main case: `0 ≤ k`, `0 ≤ R`
      have hmk : max k 0 = k := max_eq_left hk0
      have hmR : max R 0 = R := max_eq_left hR0
      rw [hmk, hmR] at hcore
      rw [← sqrt_volume_closedBall R hR0]
      exact hcore
    · -- `0 ≤ k` but `R < 0`: then `μ` vanishes identically
      have hRlt : R < 0 := lt_of_not_ge hR0
      have hmk : max k 0 = k := max_eq_left hk0
      have hmR : max R 0 = 0 := max_eq_right hRlt.le
      rw [hmk, hmR] at hcore
      have hμ0 : μ = 0 := by
        funext z
        by_contra hz
        have h1 : z ∈ Metric.closedBall (0 : ℂ) R := hsupp (Function.mem_support.mpr hz)
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        linarith [norm_nonneg z]
      have hz0 : MeasureTheory.eLpNorm μ ⊤ (volume : Measure ℂ) = 0 := by
        rw [hμ0, eLpNorm_zero]
      simp only [hz0, mul_zero] at hcore ⊢
      exact hcore
  · -- `k < 0`: then `μ` vanishes a.e.
    have hkneg : k < 0 := lt_of_not_ge hk0
    have hμae : μ =ᵐ[(volume : Measure ℂ)] 0 := by
      filter_upwards [hb] with z hz
      have hz' : ‖μ z‖ = 0 := le_antisymm (hz.trans hkneg.le) (norm_nonneg _)
      simpa using norm_eq_zero.mp hz'
    have hz0 : MeasureTheory.eLpNorm μ ⊤ (volume : Measure ℂ) = 0 := by
      rw [eLpNorm_congr_ae hμae, eLpNorm_zero]
    simp only [hz0, mul_zero] at hcore ⊢
    exact hcore

end Work.MRMT.Found
