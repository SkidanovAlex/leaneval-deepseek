/-
# `MubarRows` — copies of the class-`C` difference rows without the (unused) smallness hypothesis

`Work.FTS_MuLipC.diffRow0` and `Work.FTS_MuLipC.diffRow1` are stated with a smallness hypothesis
`C₀ * α ^ 2 ≤ 1` that is **not used anywhere in their proofs**; the statements themselves (the
`Prop`s `DiffRow0`/`DiffRow1`) carry no smallness.  The consumers in this directory need the rows
at an arbitrary (fixed) size constant `C₀` — the smallness is not available from the hypotheses of
the `RXR5L` leaf statements — so the proofs are re-run here with the hypothesis dropped (the
bodies are the delivered ones, verbatim).  `DiffRow2` (`Work.FTS.MuLipC.RowT.diffRow2`) has no
smallness hypothesis and is used directly.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS_MuLipC.Defs
import Submission.Work.FTS_MuLipC.RowN0.DiffEnergy
import Submission.Work.FTS_MuLipC.RowN0.integrableOn_L12dens_of_energy
import Submission.Work.FTS_MuLipC.RowN0.L12_sub_of_integrable
import Submission.Work.FTS_MuLipC.RowN0.N0_slice_sq_integrable
import Submission.Work.FTS_MuLipC.RowN0.N0_weighted_energy_le
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.contN0_open
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS_MuLipC.RowN.Defs
import Submission.Work.FTS_MuLipC.RowN.L12Ae
import Submission.Work.FTS_MuLipC.RowN.NHonest
import Submission.Work.FTS_MuLipC.RowN.SnPol
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS_EllLimOK.Glue
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_MuLipC.RowN0.diffRow0
import Submission.Work.FTS_MuLipC.RowN.diffRow1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn)
open Work.FTS_MuLipC
open Work.FTS_MuLipC.RowN0
open Work.FTS_MuLipC.RowN

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "L12" => Work.Construction.L12
local notation "Sn0" => Work.FTS_MuLipC.Sn0
local notation "Xn" => Work.FTS.Nonlin.Xn
local notation "Hk" => Work.Spaces.HkIntegrand

theorem diffRow0_noSmall {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS_MuLipC.DiffRow0 α C₀ := by
  refine ⟨3 * Real.sqrt (Mconst C₀ α) + 1, by positivity, ?_⟩
  intro f f' hf hf' hXf hXf'
  have hC₀ : 0 ≤ C₀ := by
    have h0 : 0 ≤ Xn α f' := Work.Spaces.HkNorm_nonneg α 4 f'
    have h1 : 0 < α ^ 2 := pow_pos hα 2
    nlinarith [hXf', h0, h1]
  have hmemf : Work.Spaces.HkMem α 4 f := Work.FTS.ClassC.classC_hkMem_four hf
  have hmemf' : Work.Spaces.HkMem α 4 f' := Work.FTS.ClassC.classC_hkMem_four hf'
  have hCsub : Work.FTS.ClassC.ClassC α (f - f') := classC_sub hf hf'
  have hmemD : Work.Spaces.HkMem α 4 (f - f') := Work.FTS.ClassC.classC_hkMem_four hCsub
  have hddefD : ∀ z θ, (f - f') z θ = f z θ - f' z θ := fun z θ => rfl
  set Xd : ℝ := Xn α (f - f') with hXddef
  have hXd : Xn α (f - f') = Xd := rfl
  have hXdnn : 0 ≤ Xd := by
    rw [← hXd]; exact Work.Spaces.HkNorm_nonneg α 4 (f - f')
  -- continuity of the difference field on the open quadrant
  have hcontf : ContinuousOn (Function.uncurry (Sn0 α f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.contN0_open hα hα1 hf.reg hmemf
  have hcontf' : ContinuousOn (Function.uncurry (Sn0 α f'))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.contN0_open hα hα1 hf'.reg hmemf'
  have hcontD : ContinuousOn (Function.uncurry (fun z θ => Sn0 α f z θ - Sn0 α f' z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hcontf.sub hcontf'
  -- a.e. strong measurability of the weighted angular energy
  have hmeasD : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.OpenPkg.l12zero_energy_aesm hcontD
  -- slice integrability of the squared difference
  have hslD : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (Sn0 α f r θ - Sn0 α f' r θ) ^ 2)
        Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hzr : r ∈ Work.Spaces.Iz := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr.le
    have hw1 : 1 ≤ Work.Spaces.w r := one_le_w hr
    have hDM : DiffMaj α C₀ Xd (f - f') f' r
        = fun θ => 3 * (A1const C₀ α * Hk α 4 (f - f') r θ
            + A2const Xd α * Hk α 4 f' r θ
            + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) := by
      funext θ
      rw [DiffMaj, A1const, A2const]
    have h3c : MeasureTheory.IntegrableOn
        (fun _ : ℝ => 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const (by
        rw [Work.Spaces.Iθ, Real.volume_Icc]
        exact ENNReal.ofReal_ne_top)
    have hmaj : MeasureTheory.IntegrableOn (fun θ => DiffMaj α C₀ Xd (f - f') f' r θ)
        Work.Spaces.Iθ := by
      rw [hDM]
      exact (((hmemD.1 r hzr).const_mul (A1const C₀ α)).add
        ((hmemf'.1 r hzr).const_mul (A2const Xd α))).add h3c |>.const_mul 3
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun θ => (Sn0 α f r θ - Sn0 α f' r θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Sn0 α f p.1 p.2 - Sn0 α f' p.1 p.2) ^ 2) (hcontD.pow 2) hr
    refine MeasureTheory.Integrable.mono' hmaj haesm ?_
    have hIoo : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    rw [hIoo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hpt := diff_pointwise_le hα hα1 hC₀ hXd hf.reg hf'.reg hCsub.reg hmemf hmemf' hmemD
      hddefD hXf hr hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (Sn0 α f r θ - Sn0 α f' r θ) ^ 2
        ≤ (Sn0 α f r θ - Sn0 α f' r θ) ^ 2 * Work.Spaces.w r := by nlinarith [hw1]
      _ ≤ DiffMaj α C₀ Xd (f - f') f' r θ := hpt
  -- the energy bound with the explicit majorant
  have hbdE : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * ((1 + r) / r) ^ 2
        ≤ PhiC α C₀ Xd (f - f') f' r := by
    filter_upwards [diff_energy_le hα hα1 hC₀ hXdnn hXf hXd hf.reg hf'.reg hCsub.reg hmemf
      hmemf' hmemD hddefD] with r hr
    have hw : Work.Spaces.w r = ((1 + r) / r) ^ 2 := by rw [Work.Spaces.w, div_pow]
    rw [hw] at hr
    exact hr
  have hΦint : MeasureTheory.IntegrableOn (PhiC α C₀ Xd (f - f') f') (Set.Ioi (0 : ℝ)) :=
    integrableOn_PhiC hmemD hmemf'
  have hL12bound := Work.FTS.OpenPkg.l12zero_of_weight_bound
    (f := fun z θ => Sn0 α f z θ - Sn0 α f' z θ) hslD hmeasD hΦint hbdE
  have hint : (∫ r in Set.Ioi (0 : ℝ), PhiC α C₀ Xd (f - f') f' r) ≤ Mconst C₀ α * Xd ^ 2 :=
    int_PhiC_le hXdnn hmemD hmemf' hXd hXf' hC₀ hα
  -- the density integrability of the two single fields
  have hslf : ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn (fun θ => (Sn0 α f r θ) ^ 2)
      Work.Spaces.Iθ :=
    N0_slice_sq_integrable hα hα1 hf.reg hmemf
  have hslf' : ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn (fun θ => (Sn0 α f' r θ) ^ 2)
      Work.Spaces.Iθ :=
    N0_slice_sq_integrable hα hα1 hf'.reg hmemf'
  have hEf : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Phi1 α f r := by
    filter_upwards [N0_weighted_energy_le hα hα1 hf.reg hmemf] with r hr
    have hL : (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ,
            (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2) := rfl
    have hR : Phi1 α f r = 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α f)
          * (∫ θ in Work.Spaces.Iθ, Hk α 4 f r θ)
        + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α f)
          * (1 / (1 + r)) ^ 2) := rfl
    have hw : Work.Spaces.w r = ((1 + r) / r) ^ 2 := by rw [Work.Spaces.w, div_pow]
    rw [hL, hR] at *
    exact hr
  have hEf' : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Sn0 α f' r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Phi1 α f' r := by
    filter_upwards [N0_weighted_energy_le hα hα1 hf'.reg hmemf'] with r hr
    have hL : (∫ θ in Work.Spaces.Iθ, (Sn0 α f' r θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ,
            (Work.Construction.N0 α (Work.Construction.Ftot α f') f' r θ) ^ 2) := rfl
    have hR : Phi1 α f' r = 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α f')
          * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
        + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α f')
          * (1 / (1 + r)) ^ 2) := rfl
    have hw : Work.Spaces.w r = ((1 + r) / r) ^ 2 := by rw [Work.Spaces.w, div_pow]
    rw [hL, hR] at *
    exact hr
  have hslf_ae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (Sn0 α f r θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => hslf r hr)
  have hslf'_ae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (Sn0 α f' r θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => hslf' r hr)
  have hdensf : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Sn0 α f))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_L12dens_of_energy hslf_ae
      (aesm_L12dens_of_continuousOn (F := Sn0 α f) hcontf)
      (integrableOn_Phi1 hmemf) (Phi1_nonneg f) hEf
  have hdensf' : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Sn0 α f'))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_L12dens_of_energy hslf'_ae
      (aesm_L12dens_of_continuousOn (F := Sn0 α f') hcontf')
      (integrableOn_Phi1 hmemf') (Phi1_nonneg f') hEf'
  have hSaf : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Sn0 α f r θ / r) Work.Spaces.Iθ :=
    fun r hr => integrableOn_K_mul_div hr
      (Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => Sn0 α f p.1 p.2) hcontf hr)
      (hslf r hr)
  have hSaf' : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Sn0 α f' r θ / r) Work.Spaces.Iθ :=
    fun r hr => integrableOn_K_mul_div hr
      (Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => Sn0 α f' p.1 p.2) hcontf' hr)
      (hslf' r hr)
  have hsub := L12_sub_of_integrable (a := Sn0 α f) (b := Sn0 α f') hdensf hdensf' hSaf hSaf'
  have hM0 : 0 ≤ Mconst C₀ α := Mconst_nonneg C₀ α
  rw [hsub]
  calc |L12 (fun z θ => Sn0 α f z θ - Sn0 α f' z θ) 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), PhiC α C₀ Xd (f - f') f' r) := hL12bound
    _ ≤ 3 * Real.sqrt (Mconst C₀ α * Xd ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hint) (by norm_num)
    _ = 3 * Real.sqrt (Mconst C₀ α) * Xd := by
        rw [Real.sqrt_mul hM0, Real.sqrt_sq hXdnn]
        ring
    _ ≤ (3 * Real.sqrt (Mconst C₀ α) + 1) * Xd := by
        have hs : 0 ≤ Real.sqrt (Mconst C₀ α) := Real.sqrt_nonneg _
        nlinarith [hs, hXdnn]


theorem diffRow1_noSmall {α C₀ Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hEadd : ∀ a b : Work.FTS.Galerkin.Fn, E (a - b) = E a - E b)
    (hEsmul : ∀ (c : ℝ) (a : Work.FTS.Galerkin.Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.VocabO.EllPkgGo α Ce f (E f)) :
    Work.FTS_MuLipC.DiffRow1 α C₀ Φs E := by
  classical
  -- ### the constants
  set K₁ : ℝ := Work.FTS_MuLamOK.KMu1 Ce Cs with hK₁
  have hK₁pos : 0 < K₁ := Work.FTS_MuLamOK.KMu1_pos Ce Cs
  have hK₁0 : 0 ≤ K₁ := hK₁pos.le
  set c : ℝ := max C₀ 0 with hc
  have hc0 : 0 ≤ c := le_max_right _ _
  have hcC : C₀ ≤ c := le_max_left _ _
  set B₁ : ℝ := Real.sqrt 2 * (2 * Real.sqrt 2 * c + 1) with hB₁
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
  set B₂ : ℝ := 1 + B₁ + B₁ ^ 2 with hB₂
  have hB₂0 : 0 ≤ B₂ := by rw [hB₂]; positivity
  refine ⟨K₁ * B₂ + 1, by positivity, ?_⟩
  intro f f' hf hf' hXf hXf'
  have hXc : Work.FTS.Nonlin.Xn α f ≤ c * α ^ 2 :=
    le_trans hXf (mul_le_mul_of_nonneg_right hcC (sq_nonneg α))
  have hXc' : Work.FTS.Nonlin.Xn α f' ≤ c * α ^ 2 :=
    le_trans hXf' (mul_le_mul_of_nonneg_right hcC (sq_nonneg α))
  set X : ℝ := Work.FTS.Nonlin.Xn α (f - f') with hX
  have hX0 : 0 ≤ X := by rw [hX]; exact Work.Spaces.HkNorm_nonneg α 4 _
  rcases lt_or_eq_of_le hX0 with hXpos | hXzero
  · -- ### the main case `|f - f'|_{ℋ⁴} > 0`
    set t : ℝ := α ^ 2 / X with ht
    have htpos : 0 < t := by rw [ht]; positivity
    have htX : t * X = α ^ 2 := by
      rw [ht]
      field_simp
    have hle := l12_diff_le hα hα1 hc0 hEadd hEsmul hstar hell hf hf' hXc hXc' htpos
    rw [← hX, htX] at hle
    have hV : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2 + α ^ 2) = B₁ * α ^ 2 := by
      rw [hB₁]
      ring
    rw [hV] at hle
    have hEnv : Work.FTS_MuLipC.Env α (B₁ * α ^ 2) ≤ B₂ * α ^ 2 := by
      rw [hB₂]
      exact Env_scaled hα hα1 hB₁0
    have hEnv0 : 0 ≤ Work.FTS_MuLipC.Env α (B₁ * α ^ 2) :=
      Work.FTS_MuLipC.Env_nonneg hα.le (by positivity)
    have htinv : K₁ / t = K₁ * X / α ^ 2 := by
      rw [ht]
      field_simp
    calc |Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0|
        ≤ (K₁ / t) * Work.FTS_MuLipC.Env α (B₁ * α ^ 2) := hle
      _ = (K₁ * X / α ^ 2) * Work.FTS_MuLipC.Env α (B₁ * α ^ 2) := by rw [htinv]
      _ ≤ (K₁ * X / α ^ 2) * (B₂ * α ^ 2) := by
          refine mul_le_mul_of_nonneg_left hEnv ?_
          positivity
      _ = K₁ * B₂ * X := by
          field_simp
      _ ≤ (K₁ * B₂ + 1) * X := by nlinarith [hX0, hB₂0, hK₁0]
  · -- ### the degenerate case `|f - f'|_{ℋ⁴} = 0`
    have hzero : |Work.Construction.L12 (Sn α Φs E f) 0
        - Work.Construction.L12 (Sn α Φs E f') 0| = 0 := by
      refine le_antisymm ?_ (abs_nonneg _)
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      set t : ℝ := K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 / ε + 1 with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have hle := l12_diff_le hα hα1 hc0 hEadd hEsmul hstar hell hf hf' hXc hXc' htpos
      rw [← hX, hXzero.symm] at hle
      have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        rw [← pow_two]
        exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hV : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2 + t * 0) = (4 * c) * α ^ 2 := by
        have hmid : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2) = (4 * c) * α ^ 2 := by
          calc Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2)
              = (Real.sqrt 2 * Real.sqrt 2) * (2 * c * α ^ 2) := by ring
            _ = 2 * (2 * c * α ^ 2) := by rw [hsq2]
            _ = (4 * c) * α ^ 2 := by ring
        rw [mul_zero, add_zero, hmid]
      rw [hV] at hle
      have hEnv : Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) ≤ (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 :=
        Env_scaled hα hα1 (by positivity)
      have hEnv0 : 0 ≤ Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) :=
        Work.FTS_MuLipC.Env_nonneg hα.le (by positivity)
      have hnum0 : 0 ≤ K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 := by positivity
      have hfin : (K₁ / t) * Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) ≤ ε := by
        calc (K₁ / t) * Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2)
            ≤ (K₁ / t) * ((1 + (4 * c) + (4 * c) ^ 2) * α ^ 2) := by
              refine mul_le_mul_of_nonneg_left hEnv ?_
              positivity
          _ = (K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2) / t := by
              field_simp
          _ ≤ ε := by
              rw [ht]
              rw [div_le_iff₀ (by positivity : 0 < K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 / ε + 1)]
              field_simp
              nlinarith [hε.le, hnum0]
      linarith [hle, hfin]
    rw [hzero]
    exact mul_nonneg (by positivity) hX0


end Work.FTS_RegExport.RXR5L
