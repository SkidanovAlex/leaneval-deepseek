/-
# `Submission/Work/FTS_MuLipC/RowN0/diffRow0.lean` — the difference row of `N₀`

`Work.FTS_MuLipC.diffRow0`: for `ClassC α` profiles `f`, `f'` of `ℋ⁴`-size `≤ C₀α²` (and
`C₀α² ≤ 1`), the `L₁₂`-zero-mode of the quadratic field `Sn0 α g = N₀ α (F_*+g) g` is Lipschitz
in the profile, with a constant depending on `α` and `C₀` only.

## The route

Write `d := f - f'`.  The difference of the two fields is *linear in the data and in `d`*:
expanding `N₀ α (F_*+g) g` and telescoping each product `a·b - a'·b' = a·(b-b') + (a-a')·b'`
along `d = f - f'` gives the pointwise identity `Sn0_sub_expand` (`DiffExpand.lean`)

`Sn0 α f - Sn0 α f' = D₁ + D₂ + D₃`  on the open quadrant, with

* `D₁ = L₁₂(f)(z)·(d/α + (3/(2α))·D_θ d - (cos 2θ - sin²θ)·D_z d)`,
* `D₂ = L₁₂(d)(z)·(f'/α + (3/(2α))·D_θ f' - (cos 2θ - sin²θ)·D_z f')`,
* `D₃ = L₁₂(d)(z)·((3/(2α))·D_θ F_* - (cos 2θ - sin²θ)·D_z F_*)
        − (cos 2θ - sin²θ)·L₁₂(F_*)(z)·D_z d`,

using only `L₁₂ f = L₁₂ d + L₁₂ f'` (`Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0`, valid because
the class is honest in `ℋ⁴`), the additivity of `∂_θ`, `∂_z` on the open quadrant, and the
difference rules `pth_sub`, `pz_sub` (`Work.FTS.StrongEps.EComparison.EllPkgClsSliceAux`).

Each of the three groups is dominated slot by slot (`DiffPointwise.lean`): `|L₁₂ f| ≤ 3C₀α²`,
`|L₁₂ d| ≤ 3|d|_{ℋ⁴}` (`l12_supAbs_open`), `|D_θ F_*| ≤ 40α²z/(1+z)²`,
`|D_z F_*| ≤ 40αz/(1+z)²` (`Fstar_shape`), `L₁₂(F_*)(z) = 2α/(1+z) ≤ 2α`, `|cos 2θ - sin²θ| ≤ 2`,
and the slot dominations `(·)²w ≤ HkIntegrand α 4 ·`, with the exact cancellation
`(z/(1+z)²)²·w(z) = (1/(1+z))²`.  Hence the Hardy-weighted angular energy of the difference is
bounded by the explicit integrable majorant `PhiC` (`DiffEnergy.lean`), whose integral is
`≤ Mconst C₀ α · |d|²_{ℋ⁴}`.

The zero mode follows from `Work.FTS.OpenPkg.l12zero_of_weight_bound`
(`|L₁₂ X 0| ≤ 3√(∫ Φ)`) applied to the difference field — no use of the single-profile row is
needed, the estimate is genuinely linear in `d` — and from the subtraction identity
`L12_sub_of_integrable` (the densities of the two fields are integrable, by
`integrableOn_L12dens_of_energy` applied to their own energy bounds
`N0_weighted_energy_le`/`N0_slice_sq_integrable`).
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

/-- `ClassC` is closed under subtraction. -/
theorem classC_sub {α : ℝ} {f f' : Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hf' : Work.FTS.ClassC.ClassC α f') : Work.FTS.ClassC.ClassC α (f - f') := by
  have h := Work.FTS.ClassC.classC_add hf (Work.FTS.ClassC.classC_smul (-1) hf')
  have heq : f + (-1 : ℝ) • f' = f - f' := by
    funext z θ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [← heq]
  exact h

/-- The majorant of the Hardy-weighted angular energy of the single field `Sn0 α g`. -/
def Phi1 (α : ℝ) (g : Fn) : ℝ → ℝ :=
  fun r => 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α g)
      * (∫ θ in Work.Spaces.Iθ, Hk α 4 g r θ)
    + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α g) * (1 / (1 + r)) ^ 2)

theorem Phi1_nonneg {α : ℝ} (g : Fn) : ∀ r, 0 ≤ Phi1 α g r := by
  intro r
  have hA := Work.FTS.StrongPersist.H6Pair6Aux.A₀_nonneg α (Xn α g)
  have hB := Work.FTS.StrongPersist.H6Pair6Aux.B₀_nonneg α (Xn α g)
  have hΨ : 0 ≤ ∫ θ in Work.Spaces.Iθ, Hk α 4 g r θ := by
    apply MeasureTheory.integral_nonneg
    intro θ
    exact Work.Spaces.HkIntegrand_nonneg α 4 g r θ
  have hc : 0 ≤ (1 / (1 + r)) ^ 2 := by positivity
  exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hA hΨ)
    (mul_nonneg (mul_nonneg (by positivity) hB) hc))

theorem integrableOn_Phi1 {α : ℝ} {g : Fn} (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn (Phi1 α g) (Set.Ioi (0 : ℝ)) := by
  have h1 : MeasureTheory.IntegrableOn
      (fun r => Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α g)
        * (∫ θ in Work.Spaces.Iθ, Hk α 4 g r θ)) (Set.Ioi (0 : ℝ)) :=
    (hmem.2.mono_set Set.Ioi_subset_Ici_self).const_mul _
  have h2 : MeasureTheory.IntegrableOn
      (fun r : ℝ => (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α g)
        * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.H2.InvOneAddSq.1.const_mul _
  have hunf : Phi1 α g = fun r => 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α g)
        * (∫ θ in Work.Spaces.Iθ, Hk α 4 g r θ)
      + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α g)
        * (1 / (1 + r)) ^ 2) := rfl
  rw [hunf]
  exact (h1.add h2).const_mul 7

/-- **The difference row of `N₀`** (`DiffRow0 α C₀`, `Submission/Work/FTS_MuLipC/Defs.lean`):
for `ClassC α` profiles `f`, `f'` of `ℋ⁴`-size `≤ C₀α²` (with `C₀α² ≤ 1`), the `L₁₂`-zero-mode
of the quadratic field `Sn0 α g = N₀ α (F_*+g) g` is Lipschitz in the profile, with a constant
depending on `α` and `C₀` only.  Read `Submission/Work/FTS_MuLipC/NOTES.md` for the route
(polarization of the quadratic part against the proved single-profile row `KMu0_row`). -/
theorem diffRow0 {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hsmall : C₀ * α ^ 2 ≤ 1) :
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

end Work.FTS_MuLipC.RowN0
