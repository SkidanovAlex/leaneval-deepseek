import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.I1_defs
import Submission.Work.AngSecond.I1_honesty
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngClean

set_option autoImplicit false

/-! ## The measurability of the source pairing

`F` is known only through `IsBslSol α F Ψ` (`bslOp α Ψ = F` on the *open* quadrant), so it is
not a priori measurable; but off the null boundary `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}` it agrees
with the smooth `bslOp α Ψ`, which is enough for both the slicewise and the joint statement
needed below.  Both facts are stated here in the general form (an arbitrary profile `g`
continuous on the open quadrant), so that they apply verbatim to `g = ∂_θθΨ`. -/

/-- The (jointly measurable) radial weight `z ↦ w z²`. -/
private theorem measurable_w2 : Measurable Work.FTS.EllipticEst.AngSecond.w2 := by
  change Measurable (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2)
  exact (((measurable_const.add measurable_id).pow_const 2).div
    (measurable_id.pow_const 2)).pow_const 2

/-- For `z > 0` the `θ`-slice of the source `F` agrees with that of `bslOp α Ψ` off the two
null endpoints of `Iθ`. -/
private theorem ae_slice_F_eq_bslOp {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.Elliptic.IsBslSol α F Ψ) {z : ℝ} (hz : 0 < z) :
    (fun θ => F z θ) =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Elliptic.bslOp α Ψ z θ) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff']
  · rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
    · intro θ hθ
      simp only [Set.mem_ofPred_eq, not_imp] at hθ
      obtain ⟨hθI, hne⟩ := hθ
      by_contra hmem
      have hθ0 : θ ≠ 0 := by rintro rfl; exact hmem (by simp)
      have hθπ : θ ≠ π / 2 := by rintro rfl; exact hmem (by simp)
      have h0 : 0 < θ := lt_of_le_of_ne hθI.1 (Ne.symm hθ0)
      have h1 : θ < π / 2 := lt_of_le_of_ne hθI.2 hθπ
      exact hne (hsol.1 z hz θ h0 h1).symm
    · rw [show ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} from by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
      exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))
  · exact measurableSet_Icc

/-- **Slicewise measurability of the source pairing `F · g`.**  For `z ∈ Iz` the angular
slice `θ ↦ F z θ · g z θ · w z² · σ θ` is a.e. strongly measurable: at `z = 0` it vanishes
identically (`w 0 = 0`), and for `z > 0` it agrees, off the two endpoints of `Iθ`, with the
product of the continuous function `θ ↦ bslOp α Ψ z θ` (`SmoothOpen.curry_θ`), the
`g`-slice and the measurable weight. -/
private theorem aesm_slice_F_mul' (α : ℝ) (F Ψ g : ℝ → ℝ → ℝ)
    (hsol : Work.Elliptic.IsBslSol α F Ψ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hgc : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ => F z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ) (volume.restrict Work.Spaces.Iθ) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · have hw : Work.FTS.EllipticEst.AngSecond.w2 z = 0 := by
      rw [← hz0]
      simp [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]
    have hfun : (fun θ => F z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ) = fun _ => (0 : ℝ) := by
      funext θ
      rw [hw]
      ring
    rw [hfun]
    exact aestronglyMeasurable_const
  · have hbsl : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
      Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp α Ψ hsm
    have hb : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Elliptic.bslOp α Ψ z θ)
        (volume.restrict Work.Spaces.Iθ) := by
      have hcont : ContinuousOn (fun θ => Work.Elliptic.bslOp α Ψ z θ)
          (Set.Ioo 0 (π / 2)) := (hbsl.curry_θ hzpos).continuousOn
      rw [show volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) from
        (MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))).symm]
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    have hgs : MeasureTheory.AEStronglyMeasurable (fun θ => g z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => g p.1 p.2) hgc hzpos
    have hsig : MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.FTS.EllipticEst.AngSecond.sig θ) (volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.EllipticEst.AngSecond.measurable_sig.aestronglyMeasurable
    have hres : MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.Elliptic.bslOp α Ψ z θ * g z θ
          * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) (volume.restrict Work.Spaces.Iθ) :=
      ((hb.mul hgs).mul_const (Work.FTS.EllipticEst.AngSecond.w2 z)).mul hsig
    refine hres.congr ?_
    filter_upwards [(ae_slice_F_eq_bslOp hsol hzpos).symm] with θ hθ
    rw [hθ]

/-- On the product measure, `F` agrees with the smooth `bslOp α Ψ` off the null boundary of
the quadrant. -/
private theorem ae_F_eq_bslOp_prod {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    (fun p : ℝ × ℝ => F p.1 p.2)
      =ᵐ[((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))]
      (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Ψ p.1 p.2) := by
  have hIz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hIθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprodae : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume.prod volume] (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hIz hIθ
  have hμeq : (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = (volume.prod volume).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_congr_set hprodae
  have haeQ : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod
      (volume.restrict Work.Spaces.Iθ)), p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    rw [hμeq]
    exact MeasureTheory.ae_restrict_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  filter_upwards [haeQ] with p hp
  rw [Set.mem_prod] at hp
  obtain ⟨hz, hθ0, hθ1⟩ := hp
  exact (hsol.1 p.1 hz p.2 hθ0 hθ1).symm

/-- **Joint measurability of the source pairing `F · g`.**  On the product measure the joint
integrand is a.e. equal to the continuous function `(z,θ) ↦ bslOp α Ψ z θ · g z θ` times the
jointly measurable weight `(z,θ) ↦ w z² · σ θ`. -/
private theorem aesm_prod_F_mul' (α : ℝ) (F Ψ g : ℝ → ℝ → ℝ)
    (hsol : Work.Elliptic.IsBslSol α F Ψ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hgc : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => F p.1 p.2 * g p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hbsl : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp α Ψ hsm
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Ψ p.1 p.2 * g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hbsl.continuousOn.mul hgc
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Ψ p.1 p.2 * g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    ((measurable_w2.comp measurable_fst).mul
      (Work.FTS.EllipticEst.AngSecond.measurable_sig.comp measurable_snd)).aestronglyMeasurable
  refine (h1.mul h2).congr ?_
  filter_upwards [ae_F_eq_bslOp_prod hsol] with p hp
  show (fun p' : ℝ × ℝ => Work.Elliptic.bslOp α Ψ p'.1 p'.2 * g p'.1 p'.2) p
      * (fun p' : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p'.1
          * Work.FTS.EllipticEst.AngSecond.sig p'.2) p
    = F p.1 p.2 * g p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
      * Work.FTS.EllipticEst.AngSecond.sig p.2
  rw [hp]
  ring

/-! ## The assembly -/

/-- A function smooth on a neighbourhood of the closed quadrant is continuous on the open
quadrant. -/
theorem continuousOn_uncurry_of_smoothNbhd {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g) :
    ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  unfold Work.Spaces.SmoothNbhd at hg
  refine hg.continuousOn.mono ?_
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  simp only [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioi] at hz hθ ⊢
  exact ⟨by linarith, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- **Honesty of the mixed pairing from the two diagonal honesties.**

Pointwise `|F g| ≤ F² + g²`, so the diagonal honesties `IPMem F F` and `IPMem g g` give both
the slicewise integrability of `F g w²σ` and the domination of the `z`-integrand by the sum
of the two honest diagonal `z`-integrands; the only missing ingredient is measurability, which
is supplied as the two hypotheses `haesm_slice` and `haesm_prod` (for the elliptic source `F`
these are `aesm_slice_F_mul` and `aesm_prod_F_mul`, the latter being the joint measurability
used by Fubini `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`). -/
theorem IPMem_of_diag_aesm {F g : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.AngSecond.IPMem F F)
    (hg : Work.FTS.EllipticEst.AngSecond.IPMem g g)
    (haesm_slice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.AEStronglyMeasurable
        (fun θ => F z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) (volume.restrict Work.Spaces.Iθ))
    (haesm_prod : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => F p.1 p.2 * g p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    Work.FTS.EllipticEst.AngSecond.IPMem F g := by
  constructor
  · intro z hz
    refine ((hF.1 z hz).add (hg.1 z hz)).mono' (haesm_slice z hz) ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    have hw2 : 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z :=
      Work.FTS.EllipticEst.AngSecond.w2_nonneg z
    have hs : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
    have hkey : |F z θ| * |g z θ| ≤ F z θ * F z θ + g z θ * g z θ := by
      nlinarith [sq_nonneg (|F z θ| - |g z θ|), sq_abs (F z θ), sq_abs (g z θ)]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hw2, abs_of_nonneg hs]
    calc |F z θ| * |g z θ| * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ (F z θ * F z θ + g z θ * g z θ) * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hw2) hs
      _ = F z θ * F z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ
          + g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ := by ring
  · refine ((hF.2).add (hg.2)).mono' haesm_prod.integral_prod_right' ?_
    refine ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    rw [Real.norm_eq_abs]
    have hsum_int : IntegrableOn
        (fun θ => (F z θ * F z θ + g z θ * g z θ) * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
      ((hF.1 z hz).add (hg.1 z hz)).congr
        (Eventually.of_forall (fun θ => by simp only [Pi.add_apply]; ring))
    have hmono : (∫ θ in Work.Spaces.Iθ,
          |F z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, (F z θ * F z θ + g z θ * g z θ)
            * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ := by
      refine integral_mono_of_nonneg (Eventually.of_forall (fun θ => abs_nonneg _))
        hsum_int (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_))
      have hw2 : 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z :=
        Work.FTS.EllipticEst.AngSecond.w2_nonneg z
      have hs : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
        Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
      have hkey : |F z θ| * |g z θ| ≤ F z θ * F z θ + g z θ * g z θ := by
        nlinarith [sq_nonneg (|F z θ| - |g z θ|), sq_abs (F z θ), sq_abs (g z θ)]
      show |F z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ|
          ≤ (F z θ * F z θ + g z θ * g z θ) * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hw2, abs_of_nonneg hs]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hw2) hs
    have hlin : (∫ θ in Work.Spaces.Iθ, (F z θ * F z θ + g z θ * g z θ)
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
        = (∫ θ in Work.Spaces.Iθ, F z θ * F z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)
          + ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ := by
      rw [show (∫ θ in Work.Spaces.Iθ, (F z θ * F z θ + g z θ * g z θ)
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
          = ∫ θ in Work.Spaces.Iθ, (F z θ * F z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ
              + g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) from
        setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
      exact integral_add (hF.1 z hz) (hg.1 z hz)
    calc |∫ θ in Work.Spaces.Iθ, F z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |F z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ| := abs_integral_le_integral_abs
      _ ≤ ∫ θ in Work.Spaces.Iθ, (F z θ * F z θ + g z θ * g z θ)
            * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ := hmono
      _ = (∫ θ in Work.Spaces.Iθ, F z θ * F z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)
          + ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ := hlin

/-- **Honesty of the pairing `IPMem F Φ`** (`F` paired with `Φ = ∂_θθΨ`).

`IPMem F Φ` is one of the six honesty inputs of `Work.FTS.EllipticEst.AngSecond.I_identity`
(the Step 2 integral identity `Σ I_i = -IP F Φ`), so it must be discharged for a datum
`(F,Ψ) ∈ EllHyp α 0` — where **`F` is not assumed smooth** (only `HkMem α 0 F`), which is the
point of the statement.

Route.
* *Slicewise honesty* is immediate from the two diagonal honesties: pointwise
  `|F Φ| ≤ (F² + Φ²)/2`, so `IntegrableOn (θ ↦ F z θ·Φ z θ·w²z·σθ) Iθ` for every `z ∈ Iz`.
* *The `z`-integrand.*  The polar equation (`Work.Elliptic.IsBslSol`) gives, for every `z > 0`
  and every `θ ∈ (0,π/2)`,
  `F = α² z²∂_zzΨ + α(5+α) z∂_zΨ + ∂_θθΨ - ∂_θ(tan θ·Ψ) + 6Ψ`,
  so the two `θ`-integrands `F·Φ·w²σ` and `C·Φ·w²σ` agree a.e. in `θ` (endpoints of `Iθ` are
  null) for every `z ∈ Iz` (for `z = 0` both are `0` because `w 0 = 0`); both slices are honest,
  so the slice integrals agree.  The right-hand combination `C` is *smooth* (each of its five
  summands is smooth on a neighbourhood of the closed quadrant), hence each of the five slice
  integrals `z ↦ ∫_θ C_j z θ·Φ z θ·w²z·σθ` is a.e. strongly measurable
  (`Work.Spaces.aesm_of_continuousOn_Qd` + `AEStronglyMeasurable.integral_prod_right`) and
  integrable (from the corresponding diagonal honesty).  Finally
  `|∫_θ F Φ w²σ| ≤ (1/2)(∫_θ F²w²σ + ∫_θ Φ²w²σ)`, and the right-hand side is integrable, so
  `IntegrableOn (z ↦ ∫_θ F Φ w²σ) Iz` by `Integrable.mono'` + a.e. measurability.
  `SmoothNbhd Ψ` is needed here for the joint measurability of the summands of `C`.

`hG` (`IPMem (∂_θ(tan θ·Ψ)) Φ`) is taken as an input: it is the same statement for the other
singular object of the equation, proved separately in `AngClean/IPMem_G_Phi.lean`. -/
theorem IPMem_F_Phi (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hsol : Work.Elliptic.IsBslSol α F Ψ)
    (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hF : Work.FTS.EllipticEst.AngSecond.IPMem F F)
    (hQ : Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hU : Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => z * Work.Spaces.pz Ψ z θ)
      (fun z θ => z * Work.Spaces.pz Ψ z θ))
    (hPhi : Work.FTS.EllipticEst.AngSecond.IPMem (Work.Spaces.pthIter 2 Ψ) (Work.Spaces.pthIter 2 Ψ))
    (hPsi : Work.FTS.EllipticEst.AngSecond.IPMem Ψ Ψ)
    (hG : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ)) :
    Work.FTS.EllipticEst.AngSecond.IPMem F (Work.Spaces.pthIter 2 Ψ) := by
  have hΦsm : Work.Spaces.SmoothNbhd (Work.Spaces.pthIter 2 Ψ) :=
    Work.Spaces.SmoothNbhd.pth (Work.Spaces.SmoothNbhd.pth hsm)
  have hΦc : ContinuousOn (Function.uncurry (Work.Spaces.pthIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    continuousOn_uncurry_of_smoothNbhd hΦsm
  exact IPMem_of_diag_aesm hF hPhi
    (fun z hz => aesm_slice_F_mul' α F Ψ (Work.Spaces.pthIter 2 Ψ) hsol hsm hΦc hz)
    (aesm_prod_F_mul' α F Ψ (Work.Spaces.pthIter 2 Ψ) hsol hsm hΦc)

end Work.FTS.EllipticEst.AngClean
