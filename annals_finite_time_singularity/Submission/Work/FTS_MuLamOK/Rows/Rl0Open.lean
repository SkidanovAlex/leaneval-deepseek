import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.h6pair_N0_zero
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.contN0_open
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Rl0Defs
import Submission.Work.FTS_MuLamOK.Rows.rl0_final

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLamOK.Rows

open Work.FTS.StrongPersist.H6Pair6Aux (A₀ B₀ B₀_nonneg)

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem Rl0Open : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {f : ℝ → ℝ → ℝ},
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2) := by
  refine ⟨10 ^ 5, by norm_num, ?_⟩
  intro α f hα hα1 hso hmem
  -- ## the three delivered analytic inputs
  have hsup : ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 f z| ≤ 3 * Work.FTS.Nonlin.Xn α f :=
    Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open hα hα1 hso hmem
  have hpt : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2 * Work.Spaces.w r
        ≤ 7 * (A₀ α (Work.FTS.Nonlin.Xn α f) * Work.Spaces.HkIntegrand α 4 f r θ
              + B₀ α (Work.FTS.Nonlin.Xn α f) * (1 / (1 + r)) ^ 2) :=
    Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open hα hα1 hso hsup
  have hcont : ContinuousOn
      (Function.uncurry (Work.Construction.N0 α (Work.Construction.Ftot α f) f))
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.contN0_open hα hα1 hso hmem
  -- ## notation
  set X : ℝ := Work.FTS.Nonlin.Xn α f with hX
  have hX0 : 0 ≤ X := by rw [hX]; exact Work.Spaces.HkNorm_nonneg α 4 f
  set Ψ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ with hΨ
  have hΨint : MeasureTheory.IntegrableOn Ψ (Set.Ioi (0 : ℝ)) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  set Φ : ℝ → ℝ := fun r =>
    7 * (A₀ α X * Ψ r
      + ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) with hΦ
  -- ## the weighted angular energy of `N₀` is dominated by `Φ`
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2)
          * ((1 + r) / r) ^ 2 ≤ Φ r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hzr : r ∈ Work.Spaces.Iz := by
      simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
    have hW1 : 1 ≤ Work.Spaces.w r := by
      rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
      nlinarith
    have hweq : ((1 + r) / r) ^ 2 = Work.Spaces.w r := by rw [Work.Spaces.w, div_pow]
    have hΦr : Φ r = 7 * (A₀ α X * Ψ r
        + ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) := by rw [hΦ]
    rw [hweq, ← MeasureTheory.integral_mul_const, hΦr]
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    have hstep : (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
            * Work.Spaces.w r)
        ≤ ∫ θ in Work.Spaces.Iθ,
          7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
            + B₀ α X * (1 / (1 + r)) ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · exact Filter.Eventually.of_forall (fun θ =>
          mul_nonneg (sq_nonneg _) (le_trans zero_le_one hW1))
      · refine (((hmem.1 r hzr).const_mul (A₀ α X)).add ?_).const_mul 7
        refine MeasureTheory.integrableOn_const ?_
        rw [Work.Spaces.Iθ, Real.volume_Icc]
        exact ENNReal.ofReal_ne_top
      · rw [hIoo2]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => by simpa only [hX] using hpt r hr θ hθ)
    refine hstep.trans ?_
    have hintA : MeasureTheory.IntegrableOn
        (fun θ => A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ) Work.Spaces.Iθ :=
      (hmem.1 r hzr).const_mul (A₀ α X)
    have hintB : MeasureTheory.IntegrableOn
        (fun θ => B₀ α X * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hvalPsi : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) = Ψ r := rfl
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hintA hintB,
      MeasureTheory.integral_const_mul, Work.FTS.Nonlinear.Pieces.integral_const_Iθ_ra, hvalPsi]
    exact le_of_eq (by ring)
  -- ## slice integrability of the squared `N₀`
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2)
        Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hzr : r ∈ Work.Spaces.Iz := by
      simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
    have hW1 : 1 ≤ Work.Spaces.w r := by
      rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
      nlinarith
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    have hslice : MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hr0
    have hmaj : MeasureTheory.Integrable
        (fun θ => 7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
          + B₀ α X * (1 / (1 + r)) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (((hmem.1 r hzr).const_mul (A₀ α X)).add ?_).const_mul 7
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    refine MeasureTheory.Integrable.mono' hmaj (hslice.pow 2) ?_
    rw [hIoo2]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
        ≤ (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
          * Work.Spaces.w r := by
          nlinarith [hW1,
            sq_nonneg (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ)]
      _ ≤ 7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
          + B₀ α X * (1 / (1 + r)) ^ 2) := by
          simpa only [hX] using hpt r hr θ hθ
  -- ## a.e. strong measurability of the weighted angular energy
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.Nonlinear.Pieces.aesm_weighted_energy_of_continuousOn hcont
  -- ## integrability of the majorant `Φ`
  have hΦint : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn (fun r => A₀ α X * Ψ r) (Set.Ioi (0 : ℝ)) :=
      hΨint.const_mul (A₀ α X)
    have h2 : MeasureTheory.IntegrableOn
        (fun r => ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul ((Real.pi / 2) * B₀ α X)
    exact (h1.add h2).const_mul 7
  -- ## the zero-mode bound from the pointwise domination
  have hmain := Work.FTS.OpenPkg.l12zero_of_weight_bound
    (f := Work.Construction.N0 α (Work.Construction.Ftot α f) f)
    hsl hmeas hΦint hbd
  -- ## evaluation of `∫Φ`
  have hΨval : (∫ r in Set.Ioi (0 : ℝ), Ψ r) = X ^ 2 := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), Ψ r) = Work.Spaces.HkSq α 4 f := by
      rw [hΨ, Work.Spaces.HkSq, Work.Spaces.Iz]
      exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
    have h2 : X ^ 2 = Work.Spaces.HkSq α 4 f := by
      rw [hX, Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    rw [h1, h2]
  have hΦval : (∫ r in Set.Ioi (0 : ℝ), Φ r)
      = 7 * (A₀ α X * X ^ 2 + ((Real.pi / 2) * B₀ α X)
          * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)) := by
    have h1 : MeasureTheory.IntegrableOn (fun r => A₀ α X * Ψ r) (Set.Ioi (0 : ℝ)) :=
      hΨint.const_mul (A₀ α X)
    have h2 : MeasureTheory.IntegrableOn
        (fun r => ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul ((Real.pi / 2) * B₀ α X)
    rw [hΦ, MeasureTheory.integral_const_mul, MeasureTheory.integral_add h1 h2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hΨval]
  have hInt_le : (∫ r in Set.Ioi (0 : ℝ), Φ r)
      ≤ 7 * (A₀ α X * X ^ 2 + Real.pi * B₀ α X) := by
    rw [hΦval]
    have hc2 : (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) ≤ 2 := Work.FTS.H2.InvOneAddSq.2
    have hB2 : ((Real.pi / 2) * B₀ α X) * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
        ≤ ((Real.pi / 2) * B₀ α X) * 2 :=
      mul_le_mul_of_nonneg_left hc2 (mul_nonneg (by positivity) (B₀_nonneg α X))
    have he : ((Real.pi / 2) * B₀ α X) * 2 = Real.pi * B₀ α X := by ring
    nlinarith [hB2]
  -- ## the final numeric comparison
  calc |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Φ r) := hmain
    _ ≤ 3 * Real.sqrt (7 * (A₀ α X * X ^ 2 + Real.pi * B₀ α X)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hInt_le) (by norm_num)
    _ ≤ 10 ^ 5 * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2) := by
        have h := rl0_final (α := α) (X := X) hα hα1 hX0
        rw [hX] at h
        exact h

end Work.FTS_MuLamOK.Rows

end
