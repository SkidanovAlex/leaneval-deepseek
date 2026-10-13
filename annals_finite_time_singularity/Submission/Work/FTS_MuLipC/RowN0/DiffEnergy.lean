/-
# `Submission/Work/FTS_MuLipC/RowN0/DiffEnergy.lean` — the energy bound for the difference

The Hardy-weighted angular energy of the difference field `Sn0 α f - Sn0 α f'` is dominated by
the explicit integrable function `PhiC`, whose integral is bounded by `Mconst C₀ α · |d|²_{ℋ⁴}`.
See `diffRow0.lean` for the route.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS_MuLipC.RowN0.DiffPointwise
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.GalFields.RHS.SharpMod.transport_L12_diff
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.l12densMeasAux
import Submission.Work.FTS.H2.InvOneAddSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN0

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "L12" => Work.Construction.L12
local notation "Sn0" => Work.FTS_MuLipC.Sn0
local notation "Xn" => Work.FTS.Nonlin.Xn
local notation "Hk" => Work.Spaces.HkIntegrand

/-- The `d`-slot coefficient of the majorant. -/
def A1const (C₀ α : ℝ) : ℝ :=
  (351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4 + 32 * α ^ 2

/-- The `f'`-slot coefficient of the majorant. -/
def A2const (Xd α : ℝ) : ℝ := (351 : ℝ) / 4 * (Xd ^ 2 / α ^ 2) + 108 * Xd ^ 2

/-- The integrable majorant of the Hardy-weighted angular energy of the difference field. -/
def PhiC (α C₀ Xd : ℝ) (d f' : Fn) : ℝ → ℝ :=
  fun r => 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
    + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
    + 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2)

/-- The unfolding of `PhiC` as an explicit three-term sum. -/
theorem PhiC_unfold (α C₀ Xd : ℝ) (d f' : Fn) :
    PhiC α C₀ Xd d f' = fun r => 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
      + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
      + 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) := rfl

/-- A.e. strong measurability of the `L₁₂`-density on `(0,∞)` from continuity of the datum on
the open quadrant. -/
theorem aesm_L12dens_of_continuousOn {F : Fn}
    (hc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable (Work.Construction.L12dens F)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hcontK : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hcontK.comp continuous_snd).continuousOn
  have hdiv : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hK.mul hc).div continuousOn_fst (fun p hp => ne_of_gt (Set.mem_prod.mp hp).1)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1) hdiv
  have h := hjoint.integral_prod_right' (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
  have h3 : MeasureTheory.AEStronglyMeasurable (Work.Construction.L12dens F)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    convert h using 1
    funext z
    rfl
  have hset : Set.Ioi (0 : ℝ) =ᵐ[MeasureTheory.volume] Work.Spaces.Iz :=
    MeasureTheory.Ioi_ae_eq_Ici
  rw [MeasureTheory.Measure.restrict_congr_set hset]
  exact h3

/-- **The energy bound for the difference field**: for a.e. `r > 0` the Hardy-weighted angular
energy of `Sn0 α f - Sn0 α f'` is dominated by `PhiC`. -/
theorem diff_energy_le {α C₀ Xd : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 ≤ C₀)
    (hXdnn : 0 ≤ Xd) {f f' d : Fn} (hXf : Xn α f ≤ C₀ * α ^ 2) (hXd : Xn α d = Xd)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hd : Work.FTS.EllipticEst.SmoothOpen d)
    (hmf : Work.Spaces.HkMem α 4 f) (hmf' : Work.Spaces.HkMem α 4 f')
    (hmd : Work.Spaces.HkMem α 4 d)
    (hddef : ∀ z θ, d z θ = f z θ - f' z θ) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * Work.Spaces.w r
        ≤ PhiC α C₀ Xd d f' r := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
  have hw1 : 1 ≤ Work.Spaces.w r := one_le_w hr
  have hw0 : 0 ≤ Work.Spaces.w r := le_trans zero_le_one hw1
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Sn0 α f r θ - Sn0 α f' r θ) ^ 2 * Work.Spaces.w r ≤ DiffMaj α C₀ Xd d f' r θ :=
    fun θ hθ => diff_pointwise_le hα hα1 hC₀ hXd hf hf' hd hmf hmf' hmd hddef hXf hr hθ
  have hzr : r ∈ Work.Spaces.Iz := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr.le
  have hzr : r ∈ Work.Spaces.Iz := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr.le
  have hHkd : MeasureTheory.IntegrableOn (fun θ => Hk α 4 d r θ) Work.Spaces.Iθ := hmd.1 r hzr
  have hHkf : MeasureTheory.IntegrableOn (fun θ => Hk α 4 f' r θ) Work.Spaces.Iθ := hmf'.1 r hzr
  have hconstI : ∀ c : ℝ, MeasureTheory.IntegrableOn (fun _ : ℝ => c) Work.Spaces.Iθ := fun c =>
    MeasureTheory.integrableOn_const (by
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  have hDM : DiffMaj α C₀ Xd d f' r = fun θ => 3 * (A1const C₀ α * Hk α 4 d r θ
      + A2const Xd α * Hk α 4 f' r θ + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) := by
    funext θ
    rw [DiffMaj, A1const, A2const]
  have h3c : MeasureTheory.IntegrableOn
      (fun _ : ℝ => 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ :=
    hconstI _
  have hInt : MeasureTheory.IntegrableOn (fun θ => DiffMaj α C₀ Xd d f' r θ) Work.Spaces.Iθ := by
    rw [hDM]
    exact (((hHkd.const_mul (A1const C₀ α)).add
      (hHkf.const_mul (A2const Xd α))).add h3c).const_mul 3
  have hIoo : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  have hbd : (fun θ => (Sn0 α f r θ - Sn0 α f' r θ) ^ 2 * Work.Spaces.w r)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => DiffMaj α C₀ Xd d f' r θ) := by
    rw [hIoo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => by simpa only [Work.Spaces.Iθ] using hpt θ hθ)
  have hstep : (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2
        * Work.Spaces.w r) ≤ ∫ θ in Work.Spaces.Iθ, DiffMaj α C₀ Xd d f' r θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) hw0) hInt hbd
  have hleft : (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2
        * Work.Spaces.w r)
      = (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * Work.Spaces.w r :=
    MeasureTheory.integral_mul_const _ _
  -- the `θ`-integral of the majorant
  have h1 : MeasureTheory.IntegrableOn (fun θ => A1const C₀ α * Hk α 4 d r θ) Work.Spaces.Iθ :=
    hHkd.const_mul (A1const C₀ α)
  have h2 : MeasureTheory.IntegrableOn (fun θ => A2const Xd α * Hk α 4 f' r θ) Work.Spaces.Iθ :=
    hHkf.const_mul (A2const Xd α)
  have f1 : (∫ θ in Work.Spaces.Iθ, (A1const C₀ α * Hk α 4 d r θ
        + A2const Xd α * Hk α 4 f' r θ))
      = (∫ θ in Work.Spaces.Iθ, A1const C₀ α * Hk α 4 d r θ)
        + (∫ θ in Work.Spaces.Iθ, A2const Xd α * Hk α 4 f' r θ) :=
    MeasureTheory.integral_add h1 h2
  have f2 : (∫ θ in Work.Spaces.Iθ, (A1const C₀ α * Hk α 4 d r θ
        + A2const Xd α * Hk α 4 f' r θ + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2))
      = (∫ θ in Work.Spaces.Iθ, (A1const C₀ α * Hk α 4 d r θ
          + A2const Xd α * Hk α 4 f' r θ))
        + (∫ θ in Work.Spaces.Iθ, 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) :=
    MeasureTheory.integral_add (h1.add h2) h3c
  have f3 : (∫ θ in Work.Spaces.Iθ, A1const C₀ α * Hk α 4 d r θ)
      = A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ) :=
    MeasureTheory.integral_const_mul _ _
  have f4 : (∫ θ in Work.Spaces.Iθ, A2const Xd α * Hk α 4 f' r θ)
      = A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ) :=
    MeasureTheory.integral_const_mul _ _
  have f5 : (∫ θ in Work.Spaces.Iθ, 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2)
      = 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 * (Real.pi / 2) :=
    Work.FTS.Nonlinear.Pieces.integral_const_Iθ_ra _
  have hTheta : (∫ θ in Work.Spaces.Iθ, (A1const C₀ α * Hk α 4 d r θ
        + A2const Xd α * Hk α 4 f' r θ + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2))
      = A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
        + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
        + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 * (Real.pi / 2) := by
    rw [f2, f1, f3, f4, f5]
  have hTheta' : (∫ θ in Work.Spaces.Iθ, DiffMaj α C₀ Xd d f' r θ)
      = 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
          + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
          + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 * (Real.pi / 2)) := by
    rw [hDM, MeasureTheory.integral_const_mul, hTheta]
  have hfin : 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
        + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
        + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 * (Real.pi / 2))
      ≤ 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
        + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
        + 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 3)
    have hpi : Real.pi / 2 ≤ 2 := by
      have := Real.pi_lt_four; linarith
    have hc : 0 ≤ α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 := by positivity
    nlinarith [hpi, hc]
  calc (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * Work.Spaces.w r
      = ∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2 * Work.Spaces.w r :=
        hleft.symm
    _ ≤ ∫ θ in Work.Spaces.Iθ, DiffMaj α C₀ Xd d f' r θ := hstep
    _ = 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
          + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
          + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 * (Real.pi / 2)) := hTheta'
    _ ≤ PhiC α C₀ Xd d f' r := hfin

/-- The majorant `PhiC` is integrable on `(0,∞)`. -/
theorem integrableOn_PhiC {α C₀ Xd : ℝ} {d f' : Fn}
    (hmd : Work.Spaces.HkMem α 4 d) (hmf' : Work.Spaces.HkMem α 4 f') :
    MeasureTheory.IntegrableOn (PhiC α C₀ Xd d f') (Set.Ioi (0 : ℝ)) := by
  have h1 : MeasureTheory.IntegrableOn
      (fun r => A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ))
      (Set.Ioi (0 : ℝ)) :=
    (hmd.2.mono_set Set.Ioi_subset_Ici_self).const_mul _
  have h2 : MeasureTheory.IntegrableOn
      (fun r => A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
      (Set.Ioi (0 : ℝ)) :=
    (hmf'.2.mono_set Set.Ioi_subset_Ici_self).const_mul _
  have h3 : MeasureTheory.IntegrableOn
      (fun r : ℝ => 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.H2.InvOneAddSq.1.const_mul _
  rw [PhiC_unfold α C₀ Xd d f']
  exact ((h1.add h2).add h3).const_mul 3

/-- The explicit constant `M` with `∫ Φ ≤ M·|d|²_{ℋ⁴}`. -/
def Mconst (C₀ α : ℝ) : ℝ :=
  3 * (180 * C₀ ^ 2 * α ^ 2 + 220 * C₀ ^ 2 * α ^ 4 + 1412000 * α ^ 2) + 1

theorem Mconst_nonneg (C₀ α : ℝ) : 0 ≤ Mconst C₀ α := by
  rw [Mconst]
  have h1 : (0 : ℝ) ≤ 180 * C₀ ^ 2 * α ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ 220 * C₀ ^ 2 * α ^ 4 := by positivity
  have h3 : (0 : ℝ) ≤ 1412000 * α ^ 2 := by positivity
  linarith

/-- **The integral of the majorant** is bounded by `Mconst C₀ α · |d|²_{ℋ⁴}`. -/
theorem int_PhiC_le {α C₀ Xd : ℝ} (hXd : 0 ≤ Xd) {f' d : Fn}
    (hmd : Work.Spaces.HkMem α 4 d) (hmf' : Work.Spaces.HkMem α 4 f')
    (hXdd : Xn α d = Xd) (hXf' : Xn α f' ≤ C₀ * α ^ 2) (hC₀ : 0 ≤ C₀) (hα : 0 < α) :
    (∫ r in Set.Ioi (0 : ℝ), PhiC α C₀ Xd d f' r) ≤ Mconst C₀ α * Xd ^ 2 := by
  have hPsid : (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)) = Xd ^ 2 := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ))
        = Work.Spaces.HkSq α 4 d := by
      rw [Work.Spaces.HkSq, Work.Spaces.Iz]
      exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
    have h2 : Xd ^ 2 = Work.Spaces.HkSq α 4 d := by
      rw [← hXdd, Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 d)]
    rw [h1, h2]
  have hPsif : (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
      ≤ C₀ ^ 2 * α ^ 4 := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
        = Work.Spaces.HkSq α 4 f' := by
      rw [Work.Spaces.HkSq, Work.Spaces.Iz]
      exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
    have h2 : Work.Spaces.HkSq α 4 f' = (Xn α f') ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f')]
    have h3 : (Xn α f') ^ 2 ≤ (C₀ * α ^ 2) ^ 2 := by
      have h0 : 0 ≤ Xn α f' := Work.Spaces.HkNorm_nonneg α 4 f'
      nlinarith [hXf', h0]
    rw [h1, h2]
    calc (Xn α f') ^ 2 ≤ (C₀ * α ^ 2) ^ 2 := h3
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hInv : (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) ≤ 2 := Work.FTS.H2.InvOneAddSq.2
  have hInt1 : MeasureTheory.IntegrableOn (fun r => A1const C₀ α
      * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)) (Set.Ioi (0 : ℝ)) :=
    (hmd.2.mono_set Set.Ioi_subset_Ici_self).const_mul _
  have hInt2 : MeasureTheory.IntegrableOn (fun r => A2const Xd α
      * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)) (Set.Ioi (0 : ℝ)) :=
    (hmf'.2.mono_set Set.Ioi_subset_Ici_self).const_mul _
  have hInt3 : MeasureTheory.IntegrableOn
      (fun r : ℝ => 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.H2.InvOneAddSq.1.const_mul _
  have e1 : (∫ r in Set.Ioi (0 : ℝ), (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
        + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)))
      = (∫ r in Set.Ioi (0 : ℝ), A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ))
        + (∫ r in Set.Ioi (0 : ℝ), A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)) :=
    MeasureTheory.integral_add hInt1 hInt2
  have e2 : (∫ r in Set.Ioi (0 : ℝ), (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
        + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
        + 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2))
      = (∫ r in Set.Ioi (0 : ℝ), (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
          + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)))
        + (∫ r in Set.Ioi (0 : ℝ), 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) :=
    MeasureTheory.integral_add (hInt1.add hInt2) hInt3
  have hval : (∫ r in Set.Ioi (0 : ℝ), PhiC α C₀ Xd d f' r)
      = 3 * (A1const C₀ α
            * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ))
          + A2const Xd α
            * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
          + 705600 * α ^ 2 * Xd ^ 2
            * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)) := by
    rw [PhiC_unfold α C₀ Xd d f', MeasureTheory.integral_const_mul, e2, e1,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hval]
  have hbInv : 705600 * α ^ 2 * Xd ^ 2 * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
      ≤ 705600 * α ^ 2 * Xd ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hInv (by positivity)
  have hb2 : A2const Xd α * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
      ≤ ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Xd ^ 2 := by
    rw [A2const]
    have h0 : 0 ≤ (351 : ℝ) / 4 * (Xd ^ 2 / α ^ 2) + 108 * Xd ^ 2 := by positivity
    calc ((351 : ℝ) / 4 * (Xd ^ 2 / α ^ 2) + 108 * Xd ^ 2)
          * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
        ≤ ((351 : ℝ) / 4 * (Xd ^ 2 / α ^ 2) + 108 * Xd ^ 2) * (C₀ ^ 2 * α ^ 4) :=
          mul_le_mul_of_nonneg_left hPsif h0
      _ = ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Xd ^ 2 := by
          first | (field_simp; ring) | field_simp
  have hfin : 3 * (A1const C₀ α * Xd ^ 2
        + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Xd ^ 2
        + 705600 * α ^ 2 * Xd ^ 2 * 2) ≤ Mconst C₀ α * Xd ^ 2 := by
    rw [Mconst]
    have hfact : 3 * (A1const C₀ α * Xd ^ 2
          + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Xd ^ 2
          + 705600 * α ^ 2 * Xd ^ 2 * 2)
        = 3 * Xd ^ 2 * (A1const C₀ α + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2
            + 108 * C₀ ^ 2 * α ^ 4) + 1411200 * α ^ 2) := by ring
    rw [hfact]
    have hb : A1const C₀ α + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4)
          + 1411200 * α ^ 2 ≤ 180 * C₀ ^ 2 * α ^ 2 + 220 * C₀ ^ 2 * α ^ 4
          + 1412000 * α ^ 2 := by
      rw [A1const]
      have h1 : (0 : ℝ) ≤ C₀ ^ 2 * α ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ C₀ ^ 2 * α ^ 4 := by positivity
      have h3 : (0 : ℝ) ≤ α ^ 2 := by positivity
      linarith
    calc 3 * Xd ^ 2 * (A1const C₀ α + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2
            + 108 * C₀ ^ 2 * α ^ 4) + 1411200 * α ^ 2)
        ≤ 3 * Xd ^ 2 * (180 * C₀ ^ 2 * α ^ 2 + 220 * C₀ ^ 2 * α ^ 4 + 1412000 * α ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ (3 * (180 * C₀ ^ 2 * α ^ 2 + 220 * C₀ ^ 2 * α ^ 4 + 1412000 * α ^ 2) + 1)
            * Xd ^ 2 := by nlinarith [sq_nonneg Xd]
  calc 3 * (A1const C₀ α * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ))
        + A2const Xd α * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
        + 705600 * α ^ 2 * Xd ^ 2 * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2))
      ≤ 3 * (A1const C₀ α * Xd ^ 2
        + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Xd ^ 2
        + 705600 * α ^ 2 * Xd ^ 2 * 2) := by
        rw [hPsid]
        linarith [hb2, hbInv]
    _ ≤ Mconst C₀ α * Xd ^ 2 := hfin

end Work.FTS_MuLipC.RowN0
