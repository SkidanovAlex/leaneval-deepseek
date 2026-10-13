import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.H5.DataW
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnLGammaT
-- the order-`5` separation of an angular profile from a `z`-only profile
import Submission.Work.FTS.StrongEps.H5.AngRad5.HkIntegrand_ang_rad_le5
-- the level-`5` angular factor of `Corr`, integrable with an `α`-uniform bound
import Submission.Work.FTS.StrongEps.H5.AngFac5.ang_fac5_integrable_bound
-- `radA α w` is `C⁵` (needed for the measurability of the level-`5` slot sum)
import Submission.Work.FTS.GalFields.Norm.radA_contDiffOn_five_of_smoothOpen
-- the order-`5` angular jet bound `|D_θ^i Γ| ≤ 10⁵ α Γ`
import Submission.Work.FTS.LocDataExt.DthIter_Gam_abs_le5
-- the level-`n` radial density `RintN`
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.gam_rad_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The `ℋ⁵`-bound of `𝓛_Γ^T w` for `ClassC` data

`𝓛_Γ^T = 𝓛̂ + Corr` (`CoercivityFix.LGammaT_eq_Lhat_add_Corr`).  The clean part `𝓛̂` is
level-general (`StrongPersist.H6Aux.Lhat_mem` / `HkSq_Lhat_le`).  The correction
`Corr α w = Γ(θ)·radA α w (z)` is a *separated* product, and the level-`5` treatment needs the
three order-`5` companions of the level-`4` ingredients:

* `AngRad5.HkIntegrand_ang_rad_le5` — the pointwise separation
  `HkIntegrand α 5 (Γ·ρ) ≤ RintN 5 ρ · afac5` (`n ≤ 5` version of
  `E2norm.HkIntegrand_ang_rad_le_n`);
* `AngFac5.ang_fac5_integrable_bound` — `∫_θ afac5 ≤ K`, `K` uniform in `α` (the coefficient
  `5(10⁵α)²` on the singular factor `sin(2θ)^{2α/5-γ}` absorbs the `1/α` of its integral);
* the level-`5` radial slot bound `∫_z RintN 5 (radA α w) ≤ C·HkSq α 6 w`, which follows from
  `SlotSumRadAOpen` (the level-`6` slot sum dominates `RintN 5` pointwise) — provided
  `radA α w` is `C⁵` (`GalFields.Norm.radA_contDiffOn_five_of_smoothOpen`), which is what makes
  the slot sum a.e. strongly measurable.

The angular jet bound `|D_θ^i Γ| ≤ 10⁵ α Γ` for `i ≤ 5` (the `α`-carrying form, refined from
`LocDataExt.DthIter_Gam_abs_le5`) is what keeps `afac5` `α`-uniformly bounded; it is proved here
(`DthIter_Gam_abs_le5_alpha`) from `Spaces.dthU_iter_Gam_abs_bound` and the coefficient bound
`LocDataExt.Tfun_abs_le4`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

/-! ## The radial slot bound at level `5` -/

/-- `RintN 5 B z ≤ SlotSum B z` pointwise: the level-`5` radial density is the sum over
`range 6`, the level-`6` slot sum over `range 7`, and all summands are nonnegative squares. -/
theorem RintN_five_le_SlotSum (B : ℝ → ℝ) (z : ℝ) :
    Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5 B z ≤
      Work.FTS.StrongPersist.SlotSum B z := by
  rw [Work.FTS.StrongPersist.H6Aux.Alt_SlotSum_eq]
  rw [Work.FTS.CoercivityFix.Transfer.E2norm.RintN]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by norm_num))
    (fun q _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- **Integrability and bound of the level-`5` radial slot sum of `radA α f`**, from the
level-`6` slot sum `SlotSumRadAOpen`: `RintN 5 ≤ SlotSum` pointwise, and `SlotSum` is integrable
with `∫ SlotSum ≤ C·HkSq α 6 f`.  The `C⁵`-smoothness of `radA α f` on `(0,∞)` supplies the
a.e. strong measurability of `RintN 5 (radA α f)`. -/
theorem RintN5_radA_le_self :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Construction.L12 f 0 = 0 →
      ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) →
      MeasureTheory.IntegrableOn (fun z : ℝ =>
          Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
            (Work.FTS.CoercivityFix.Transfer.radA α f) z) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
            (Work.FTS.CoercivityFix.Transfer.radA α f) z) ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C, hC, hb⟩ := Work.FTS.StrongEps.EpsZero.ClassCHk.SlotSumRadAOpen
  refine ⟨C, hC, ?_⟩
  intro α hαIoc f hsm hmem7 hl12 hrad5
  obtain ⟨hSint, hSbd⟩ := hb α hαIoc f hsm hmem7 hl12
  have hpt : ∀ z, Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
      (Work.FTS.CoercivityFix.Transfer.radA α f) z
      ≤ Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z :=
    fun z => RintN_five_le_SlotSum _ z
  have hcont : ContinuousOn
      (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
        (Work.FTS.CoercivityFix.Transfer.radA α f) z) (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.StrongPersist.H6Aux.Alt_continuousOn_slotSum (n := 5) hrad5
    refine h.congr (fun z _ => ?_)
    rw [Work.FTS.CoercivityFix.Transfer.E2norm.RintN]
  refine ⟨?_, ?_⟩
  · have hmeas : AEStronglyMeasurable
        (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
          (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        (volume.restrict Work.Spaces.Iz) := by
      have heq : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
          = MeasureTheory.volume.restrict Work.Spaces.Iz := by
        rw [Work.Spaces.Iz,
          ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
      rw [← heq]
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    refine Integrable.mono' hSint hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
    rw [Real.norm_of_nonneg]
    · exact hpt z
    · exact Work.FTS.CoercivityFix.Transfer.E2norm.RintN_nonneg 5 _ z
  · refine (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        Work.FTS.CoercivityFix.Transfer.E2norm.RintN_nonneg 5 _ z) hSint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z _ => hpt z))).trans hSbd

/-! ## The angular factor at level `5`, and the jet bound of `Γ` -/

/-- The angular factor of the level-`5` separated product `Γ(θ)·r(z)`: the light weight
`smE θ = sin(2θ)^{-η}` plus the heavy slot with the sharp `α²`-coefficient and the combined
exponent `2α/5 - γ = 3α/10 - 1 ∈ (-1,0)`.  (`afac4` with the coefficient `4` replaced by `5`.) -/
noncomputable def afac5 (α : ℝ) (θ : ℝ) : ℝ :=
  Work.FTS.Nonlinear.RadialProd.smE θ
    + 5 * (100000 * α) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)

/-- **`|D_θ^i Γ| ≤ 10⁵·α·Γ` for `1 ≤ i ≤ 5`**: the order-`5` refinement of
`E2norm.DthIter_Gam_abs_le_alpha` (which stops at `i = 4`).  The `α`-factor comes from
`Spaces.dthU_iter_Gam_abs_bound` (`D_θ^i Γ = α·dthU^{i-1}(Tfun)·Γ`), and the coefficient bound
`|Tfun 4| ≤ 10⁵` from `LocDataExt.Tfun_abs_le4`. -/
theorem DthIter_Gam_abs_le5_alpha (i : ℕ) (hi : 1 ≤ i) (hi5 : i ≤ 5) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ|
      ≤ 100000 * α * Work.Spaces.Gam α θ := by
  have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (i - 1) α θ'| ≤ 100000 :=
    fun θ' _ => Work.FTS.LocDataExt.Tfun_abs_le4 (i - 1) (by omega) α hα hα1 θ'
  have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i hi α hα 100000 hT θ hθ
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
  calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * 100000 * Work.Spaces.Gam α θ := hkey
    _ = 100000 * α * Work.Spaces.Gam α θ := by ring

/-! ## The pointwise `ℋ⁵`-integrand bound for the transfer correction -/

/-- **Pointwise separation of `Corr α g = Γ(θ)·radA α g (z)` at level `5`.**  For `θ ∈ Iθ` the
`ℋ⁵`-integrand of the transfer correction is dominated by the product of the level-`5` radial
density of `radA α g` and the angular factor `afac5`: apply `AngRad5.HkIntegrand_ang_rad_le5`
at `n = 5` with angular profile `Γ` (`B0 = 1`), `B1 = 10⁵α` and `G θ = sin(2θ)^{α/5}`
(`DthIter_Gam_abs_le5_alpha` for the derivative bound, `LocData.Gam_le_sin_two_rpow` for
`Γ ≤ G`), and fold `(sin(2θ)^{α/5})²·smG = sin(2θ)^{2α/5-γ}`. -/
theorem HkIntegrand_Corr_le5 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (g : Fn) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 5 (Work.FTS.CoercivityFix.Corr α g) z θ
      ≤ Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
          (Work.FTS.CoercivityFix.Transfer.radA α g) z * afac5 α θ := by
  have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Gam α θ| ≤ (1 : ℝ) := fun θ hθ => by
    obtain ⟨h1, h2⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    rwa [abs_of_nonneg h1]
  have hB1pos : (0 : ℝ) < 100000 * α := by positivity
  have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ|
        ≤ (100000 * α) * (fun θ' => (Real.sin (2 * θ')) ^ (α / 5)) θ := by
    intro i hi hi5 θ hθ
    refine (DthIter_Gam_abs_le5_alpha i hi hi5 α hα hα1 hθ).trans ?_
    exact mul_le_mul_of_nonneg_left (Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ) hB1pos.le
  have hfun : Work.FTS.CoercivityFix.Corr α g
      = fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α g z := by
    funext z θ
    exact Work.FTS.CoercivityFix.Transfer.Corr_eq_radA α g z θ
  rw [hfun]
  have hsep := Work.FTS.StrongEps.H5.AngRad5.HkIntegrand_ang_rad_le5 (n := 5) (le_refl 5)
    (α := α) (a := fun θ => Work.Spaces.Gam α θ)
    (r := fun z => Work.FTS.CoercivityFix.Transfer.radA α g z)
    (G := fun θ => (Real.sin (2 * θ)) ^ (α / 5)) (B0 := 1) (B1 := 100000 * α)
    (z := z) (θ := θ) ha0 ha1 hθ
  refine hsep.trans (le_of_eq ?_)
  have hang : (1 : ℝ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
      + 5 * (100000 * α) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ = afac5 α θ := by
    rw [one_pow, one_mul]
    rw [show (5 : ℝ) * (100000 * α) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ
        = 5 * (100000 * α) ^ 2
          * (((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
        from by ring]
    rw [Work.FTS.CoercivityFix.Transfer.E2norm.rpow_sq_smG_eq α hα hα1 hθ]
    rfl
  rw [hang]
  rfl

/-! ## The `ℋ⁵`-bound and membership of the transfer correction -/

/-- **The `ℋ⁵`-energy of the transfer correction** (the level-`5` companion of
`ClassCRHS.HkSq_Corr_le_classC`): `HkSq α 5 (Corr α w) ≤ Kang·∫_z RintN 5 (radA α w)`, from
the pointwise separation, the integrable angular factor `afac5` and the integrable radial
density `RintN 5 (radA α w)`. -/
theorem HkSq_Corr_le5 {α Kang : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hKang : 0 < Kang)
    (hang : MeasureTheory.IntegrableOn (afac5 α) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, afac5 α θ) ≤ Kang)
    {w : Fn}
    (hslot : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
          (Work.FTS.CoercivityFix.Transfer.radA α w) z) Work.Spaces.Iz) :
    Work.Spaces.HkSq α 5 (Work.FTS.CoercivityFix.Corr α w)
      ≤ Kang * (∫ z in Work.Spaces.Iz,
          Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
            (Work.FTS.CoercivityFix.Transfer.radA α w) z) := by
  obtain ⟨hafInt, hafBd⟩ := hang
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 5 (Work.FTS.CoercivityFix.Corr α w) z θ
        ≤ Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
            (Work.FTS.CoercivityFix.Transfer.radA α w) z * afac5 α θ :=
    fun _ _ θ hθ => HkIntegrand_Corr_le5 hα hα1 w hθ
  have hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
          (Work.FTS.CoercivityFix.Transfer.radA α w) z * afac5 α θ) Work.Spaces.Iθ :=
    fun z _ => hafInt.const_mul _
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 5 (Work.FTS.CoercivityFix.Corr α w) z θ)
        ≤ Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
            (Work.FTS.CoercivityFix.Transfer.radA α w) z * Kang := by
    intro z hz
    have h1 := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 5 (Work.FTS.CoercivityFix.Corr α w) z θ)
      (hMslice z hz)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hafBd
      (Work.FTS.CoercivityFix.Transfer.E2norm.RintN_nonneg 5 _ z))
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 5 (Work.FTS.CoercivityFix.Corr α w) z θ)
      ≤ Kang * (∫ z in Work.Spaces.Iz,
          Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
            (Work.FTS.CoercivityFix.Transfer.radA α w) z) := by
    have hInt : MeasureTheory.IntegrableOn
        (fun z => Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
          (Work.FTS.CoercivityFix.Transfer.radA α w) z * Kang) Work.Spaces.Iz :=
      hslot.mul_const Kang
    have h1 := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 5 (Work.FTS.CoercivityFix.Corr α w) z θ)
      hInt
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hinner z hz))
    rw [MeasureTheory.integral_mul_const] at h1
    exact h1.trans_eq (by ring)
  exact houter

/-- **`ℋ⁵`-membership of the transfer correction**, by domination with the separated majorant
`RintN 5 (radA α w) z · afac5 α θ` (`LocData.HkMem_of_majorant`). -/
theorem HkMem_Corr5 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {w : Fn}
    (hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 5 (Work.FTS.CoercivityFix.Corr α w) p.1 p.2)
      Work.FTS.EllipticEst.Q0)
    (hang : MeasureTheory.IntegrableOn (afac5 α) Work.Spaces.Iθ)
    (hslot : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
          (Work.FTS.CoercivityFix.Transfer.radA α w) z) Work.Spaces.Iz) :
    Work.Spaces.HkMem α 5 (Work.FTS.CoercivityFix.Corr α w) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 5
    (f := Work.FTS.CoercivityFix.Corr α w)
    (M := fun z θ => Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
      (Work.FTS.CoercivityFix.Transfer.radA α w) z * afac5 α θ) hcont ?_ ?_ ?_
  · intro z _
    exact hang.const_mul _
  · have heq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
            (Work.FTS.CoercivityFix.Transfer.radA α w) z * afac5 α θ)
        = fun z : ℝ => Work.FTS.CoercivityFix.Transfer.E2norm.RintN 5
            (Work.FTS.CoercivityFix.Transfer.radA α w) z
          * (∫ θ in Work.Spaces.Iθ, afac5 α θ) := by
      funext z
      exact MeasureTheory.integral_const_mul _ _
    rw [heq]
    exact hslot.mul_const _
  · intro z _ θ hθ
    exact HkIntegrand_Corr_le5 hα hα1 w hθ

/-! ## `ℋ⁵`-additivity on the open class -/

/-- **`ℋ⁵`-additivity on the open class** (the level-`5` companion of
`OpenPkg.HkMem_add_of_contDiffOn_four`): from the pointwise subadditivity
`GalFields.RHS.HkIntegrand_add_le_open` and the level-general continuity
`OpenPkg.continuousOn_HkIntegrand_of_contDiffOn`. -/
theorem HkMem_add_of_smoothOpen_five {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α 5 f) (hmg : Work.Spaces.HkMem α 5 g) :
    Work.Spaces.HkMem α 5 (fun z θ => f z θ + g z θ) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 5
    (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * (Work.Spaces.HkIntegrand α 5 f z θ
      + Work.Spaces.HkIntegrand α 5 g z θ)) ?_ ?_ ?_ ?_
  · exact Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn (α := α) (n := 5) (k := 5) le_rfl
      (((hf.forall 5).add (hg.forall 5)).congr (fun p _ => by simp only [Function.uncurry]))
  · intro z hz
    exact ((hmf.1 z hz).add (hmg.1 z hz)).const_mul 2
  · refine IntegrableOn.congr_fun ((hmf.2.add hmg.2).const_mul 2) ?_ measurableSet_Ici
    intro z hz
    show 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 f z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 g z θ))
      = ∫ θ in Work.Spaces.Iθ, 2 * (Work.Spaces.HkIntegrand α 5 f z θ
          + Work.Spaces.HkIntegrand α 5 g z θ)
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hmf.1 z hz) (hmg.1 z hz)]
  · intro z hz θ hθ
    exact Work.FTS.GalFields.RHS.HkIntegrand_add_le_open α 5 hα hf hg z hz θ hθ

/-! ## The target -/

/-- **The linear part `𝓛_Γ^T w` at level 5** (the level-`5` analogue of `HkMemXnLGammaT`).

`LGammaT α w = Lhat w + Corr α w` (`CoercivityFix.LGammaT_eq_Lhat_add_Corr`).  The clean part is
already level-general: `StrongPersist.H6Aux.Lhat_mem α hα 5 hs hmem6` gives `HkMem α 5 (Lhat w)`
and `H6Aux.HkSq_Lhat_le α hα 5 hs hmem6` bounds `HkSq α 5 (Lhat w) ≤ C·HkSq α 6 w` from the
hypothesis `HkNorm α 6 w ≤ B` alone (no `α`-uniformity is needed: the constant may depend on
`α, C₀, B`).  For the correction `Corr α w = Gam α θ · radA α w z` (the product of an angular
profile with a `z`-only profile) the level-4 proof used the pointwise separation
`E2norm.HkIntegrand_ang_rad_le_n` together with the radial slot sums (`SlotSumRadAOpen`,
`radA_slotSum4_le`); one needs the order-`5` versions (either of the two separation lemmas), and
the level shift `H5.HkSq_succ_le` / `H5.H5.HkMem_succ_of` can also be applied directly to `Corr`,
whose `Dz`/`Dθ` derivatives stay separated (`Dz(Γ·ρ) = Γ·(Dz ρ)`, `Dθ(Γ·ρ) = (DθΓ)·ρ`). -/
theorem HkMemXnLGammaT5 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
    ∃ K : ℝ, 0 < K ∧ ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.Spaces.HkMem α 5 (Work.Coercivity.LGammaT α w) ∧
      Work.Spaces.HkNorm α 5 (Work.Coercivity.LGammaT α w) ≤ K := by
  intro α hαI C₀ B
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  -- ## the three constants
  obtain ⟨Cl, hClpos, hLhatbd⟩ := Work.FTS.StrongPersist.H6Aux.HkSq_Lhat_le α hα 5
  obtain ⟨Kang, hKangpos, hang⟩ := Work.FTS.StrongEps.H5.AngFac5.ang_fac5_integrable_bound
  obtain ⟨Crad, hCradpos, hrad⟩ := RintN5_radA_le_self
  refine ⟨Real.sqrt (2 * (Cl * (max B 0) ^ 2 + Kang * (Crad * (max B 0) ^ 2))) + 1,
    by positivity, ?_⟩
  intro w hw _hsmall hB
  -- ## the datum
  have hmem6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  have hmem5w : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hw.mem
  have hN6 : Work.Spaces.HkNorm α 6 w ≤ max B 0 := le_trans hB (le_max_left _ _)
  have hSq6 : Work.Spaces.HkSq α 6 w ≤ (max B 0) ^ 2 := by
    have hs : Work.Spaces.HkSq α 6 w = (Work.Spaces.HkNorm α 6 w) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 w)]
    rw [hs]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 w) hN6 2
  -- ## the two summands of `𝓛_Γ^T = 𝓛̂ + Corr`
  have hLhatmem : Work.Spaces.HkMem α 5 (Work.FTS.CoercivityFix.Lhat w) :=
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 5 hw.reg hmem6
  have hLhatsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.Lhat w) :=
    Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hw.reg
  have hLGTsm : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α w) :=
    Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw) hw.reg
  have hCorrsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.Corr α w) :=
    Work.FTS.NonlinRows.smoothOpen_sub hLGTsm hLhatsm
  have hCorr5 : ContDiffOn ℝ 5 (Function.uncurry (Work.FTS.CoercivityFix.Corr α w))
      Work.FTS.EllipticEst.Q0 := (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hCorrsm 5
  -- ## the radial slot bound
  have hradA5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.radA α w) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.GalFields.Norm.radA_contDiffOn_five_of_smoothOpen hα hα1 hw.reg hmem5w
  have hradb := hrad α hαI w hw.reg hw.mem hw.l12 hradA5
  -- ## the transfer correction
  have hCorrmem : Work.Spaces.HkMem α 5 (Work.FTS.CoercivityFix.Corr α w) :=
    HkMem_Corr5 hα hα1
      (Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn (α := α) (n := 5) (k := 5)
        le_rfl hCorr5)
      (hang α hα hα1).1 hradb.1
  have hLGmem : Work.Spaces.HkMem α 5 (Work.Coercivity.LGammaT α w) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α w]
    exact HkMem_add_of_smoothOpen_five hα hLhatsm hCorrsm hLhatmem hCorrmem
  -- ## the norm bound
  have hLhatSq : Work.Spaces.HkSq α 5 (Work.FTS.CoercivityFix.Lhat w) ≤ Cl * (max B 0) ^ 2 :=
    le_trans (hLhatbd w hw.reg hmem6) (mul_le_mul_of_nonneg_left hSq6 hClpos.le)
  have hCorrSq : Work.Spaces.HkSq α 5 (Work.FTS.CoercivityFix.Corr α w)
      ≤ Kang * (Crad * (max B 0) ^ 2) := by
    have h1 := HkSq_Corr_le5 hα hα1 hKangpos (hang α hα hα1) hradb.1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hKangpos.le)
    exact hradb.2.trans (mul_le_mul_of_nonneg_left hSq6 hCradpos.le)
  have hSqLG : Work.Spaces.HkSq α 5 (Work.Coercivity.LGammaT α w)
      ≤ 2 * (Work.Spaces.HkSq α 5 (Work.FTS.CoercivityFix.Lhat w)
        + Work.Spaces.HkSq α 5 (Work.FTS.CoercivityFix.Corr α w)) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α w]
    exact Work.FTS.GalFields.RHS.HkSq_add_le_open α 5 hα hLhatsm hCorrsm hLhatmem hCorrmem
  have hfinal : Work.Spaces.HkSq α 5 (Work.Coercivity.LGammaT α w)
      ≤ 2 * (Cl * (max B 0) ^ 2 + Kang * (Crad * (max B 0) ^ 2)) := by
    linarith [hSqLG, hLhatSq, hCorrSq]
  refine ⟨hLGmem, ?_⟩
  calc Work.Spaces.HkNorm α 5 (Work.Coercivity.LGammaT α w)
      = Real.sqrt (Work.Spaces.HkSq α 5 (Work.Coercivity.LGammaT α w)) := rfl
    _ ≤ Real.sqrt (2 * (Cl * (max B 0) ^ 2 + Kang * (Crad * (max B 0) ^ 2))) :=
        Real.sqrt_le_sqrt hfinal
    _ ≤ Real.sqrt (2 * (Cl * (max B 0) ^ 2 + Kang * (Crad * (max B 0) ^ 2))) + 1 :=
        le_add_of_nonneg_right zero_le_one

end Work.FTS.StrongEps.H5
