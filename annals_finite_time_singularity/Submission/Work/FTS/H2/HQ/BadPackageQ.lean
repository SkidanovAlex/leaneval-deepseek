import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.FTS.H2.HQ.BadMemQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## Two elementary angular facts

The hypotheses of `BadPackageQ` are stated on the *open* interval (the two Hardy inequalities
are only available there, because the weights degenerate at the endpoints) while the assembly
works almost everywhere on the closed interval `Iθ`; and the second Hardy hypothesis has to be
recovered at the endpoints of `Iθ` from the fact that `sin(2θ)` vanishes there. -/

/-- A property that holds on the open interval `(0, π/2)` holds almost everywhere on
`Iθ = [0, π/2]` for the restricted Lebesgue measure (the two endpoints are null). -/
theorem ae_restrict_Iθ_of_Ioo_qd {P : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo 0 (π / 2), P θ) :
    ∀ᵐ θ ∂(volume.restrict Iθ), P θ := by
  rw [Iθ, ← MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := volume) (a := (0 : ℝ))
    (b := π / 2)]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => h θ hθ)

/-- On `Iθ`, `sin(2θ) > 0` forces `θ ∈ (0, π/2)` (the two endpoints are the only zeros of
`sin(2θ)` on `[0, π/2]`). -/
theorem mem_Ioo_of_mem_Iθ_of_sin_two_pos {θ : ℝ} (hθ : θ ∈ Iθ)
    (h : 0 < Real.sin (2 * θ)) : θ ∈ Set.Ioo 0 (π / 2) := by
  rw [Iθ, Set.mem_Icc] at hθ
  constructor
  · by_contra hc
    have h0 : θ = 0 := le_antisymm (le_of_not_gt hc) hθ.1
    rw [h0] at h
    simp at h
  · by_contra hc
    have hp : θ = π / 2 := le_antisymm hθ.2 (le_of_not_gt hc)
    rw [hp] at h
    have hsin : Real.sin (2 * (π / 2)) = 0 := by
      rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    rw [hsin] at h
    exact lt_irrefl _ h

/-- **The bad-term package of the interior product rule `HProdQ`.**

For `f, g` smooth in the interior (`SmoothQuad`) and of class `HkMem α 4`, given the two
one-dimensional Hardy trade-offs of the exceptional slot
`Work.Spaces.HProductRule_bad_term` (the `θ`-Hardy bound for `D_z^3 f`, pointwise in `θ`, and
the radial Hardy bound for `D_θ g`, which needs the slice-integrability of
`(mixed 1 1 g · Wt)²`), the weighted product `D_z³f · D_θg · Wt` is square integrable with

  `L2Sq (D_z³f · D_θg · Wt) ≤ 100/(γ-1)·|f|²_{ℋ⁴}·|g|²_{ℋ⁴}`.

This is `Work.Spaces.BadTermSqBound` (proved) with `Spaces.SmoothNbhd` (analyticity on a
neighbourhood of the closed quadrant) replaced by `SmoothQuad`.  It returns `L2Mem` (both the
angular slice integrability and the integrability of the outer integral) together with the
`L2Sq` bound, exactly as `Work.Spaces.BadTermSqBound` does.

Route: copy the proof of `Submission/Work/Spaces/HProductRule_bad_term.lean`, i.e. `badU`,
`badV`, `badU_int`, `badV_int` and the assembly `bt_assembly`.  Warning: `bt_assembly`'s
*signature* still asks for `Spaces.SmoothNbhd`/`VanishTheta`/`DecayInZ`, which are not available
here, so it cannot be called literally — copy its proof body (which never uses those hypotheses)
or re-prove the same intermediate goal.  Supply
* the product-measure integrability of `(mixed 3 1 f · Wt)²` and `(mixed 1 1 g · Wt)²` with
  their values from `Work.FTS.H2.HQ.bt_prod_integrable_quad` (proved in `HQ/Glue.lean`);
* `badU α f z = 100/(γ-1)∫_{Iθ}(mixed 3 1 f z · · Wt)²` and
  `badV α g θ = ∫_{Iz}(mixed 1 1 g z' θ · Wt)²`, integrable by
  `Integrable.integral_prod_left/right` from that product integrability;
* the second Hardy hypothesis converted into the a.e.-in-`θ` form used by the assembly: the
  slice `∫_{Iz}(mixed 1 1 g · Wt)²` is integrable for a.e. `θ` (`Integrable.prod_left_ae`),
  which is exactly the extra premise of the second hypothesis here;
* the first Hardy hypothesis at `θ ∈ Ioo 0 (π/2)`, extended a.e. to `Iθ` (the two endpoints are
  null).
The final domination of the bad-term integrand by `badU α f z · badV α g θ` and the passage to
the double integral are verbatim as in `BadTermSqBound`, with the `100/(γ-1)` constant. -/
theorem BadPackageQ : ∀ (α : ℝ) (f g : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
    Work.FTS.LocData.SmoothQuad f → Work.Spaces.HkMem α 4 f →
    Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem α 4 g →
    (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      (Work.Spaces.DzIter 3 f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 ≤
        (100 / (Work.Spaces.gam α - 1)) * MeasureTheory.integral
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (fun s => (Work.Spaces.mixed 3 1 f z s * Work.Spaces.Wt α z s) ^ 2)) →
    (∀ θ ∈ Work.Spaces.Iθ,
      MeasureTheory.IntegrableOn
        (fun z' => (Work.Spaces.mixed 1 1 g z' θ * Work.Spaces.Wt α z' θ) ^ 2)
        Work.Spaces.Iz →
      ∀ z ∈ Work.Spaces.Iz,
        (Work.Spaces.Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤
          MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iz)
            (fun z' => (Work.Spaces.mixed 1 1 g z' θ * Work.Spaces.Wt α z' θ) ^ 2)) →
    Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ
        * Work.Spaces.Wt α z θ)
    ∧ Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ
        * Work.Spaces.Wt α z θ)
      ≤ 100 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
  intro α f g hα hα1 hfsq hmemf hgsq hmemg hA1 hA2
  have hγ : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hcpos : (0 : ℝ) < 100 / (gam α - 1) := div_pos (by norm_num) hγ
  -- the product-measure integrability of the two weighted mixed slots
  obtain ⟨hF1, _hF1val⟩ :=
    bt_prod_integrable_quad α f hfsq hmemf 3 1 (by norm_num) (by norm_num)
  obtain ⟨hF2, hF2val⟩ :=
    bt_prod_integrable_quad α g hgsq hmemg 1 1 (le_refl 1) (by norm_num)
  -- the two dominating functions are integrable
  have hUint : Integrable (badU α f) (volume.restrict Iz) :=
    hF1.integral_prod_left.const_mul (100 / (gam α - 1))
  have hVint : Integrable (badV α g) (volume.restrict Iθ) :=
    hF2.integral_prod_right
  have hUnn : ∀ z, 0 ≤ badU α f z := fun z =>
    mul_nonneg hcpos.le (integral_nonneg fun s => sq_nonneg _)
  have hVnn : ∀ θ, 0 ≤ badV α g θ := fun θ => integral_nonneg fun z => sq_nonneg _
  -- the `θ`-Hardy bound for `D_z^3 f`, a.e. on `Iθ` (the hypothesis is on `(0,π/2)`)
  have hfdom : ∀ᵐ θ ∂(volume.restrict Iθ), ∀ z ∈ Iz,
      (DzIter 3 f z θ) ^ 2 * (w z) ^ 2 ≤ badU α f z := by
    refine ae_restrict_Iθ_of_Ioo_qd (fun θ hθ => ?_)
    intro z hz
    exact hA1 z hz θ hθ
  -- the radial Hardy bound for `D_θ g`, a.e. on `Iθ` (the endpoints are recovered from `sin = 0`)
  have hgdom : ∀ᵐ θ ∂(volume.restrict Iθ), ∀ z ∈ Iz,
      (Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) ≤ badV α g θ := by
    filter_upwards [hF2.prod_left_ae, ae_restrict_mem measurableSet_Icc] with θ hslice hθ
    intro z hz
    by_cases hzero : Real.sin (2 * θ) = 0
    · have hDth : Dth g z θ = 0 := by
        show Real.sin (2 * θ) * pth g z θ = 0
        rw [hzero, zero_mul]
      rw [hDth]
      simp only [zero_pow (show (2 : ℕ) ≠ 0 by norm_num), zero_mul]
      exact hVnn θ
    · have hθmem : θ ∈ Set.Ioo 0 (π / 2) :=
        mem_Ioo_of_mem_Iθ_of_sin_two_pos hθ
          (lt_of_le_of_ne (bt_sin_nonneg hθ) (Ne.symm hzero))
      exact hA2 θ hθ hslice z hz
  -- the a.e. domination of the bad-term integrand by `badU z · badV θ`
  have hdom : ∀ᵐ θ ∂(volume.restrict Iθ), ∀ z ∈ Iz,
      ‖(DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2‖ ≤ badU α f z * badV α g θ := by
    filter_upwards [hfdom, hgdom, ae_restrict_mem measurableSet_Icc] with θ hf hg hθ
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), bt_factor α z θ hα hθ f g]
    exact mul_le_mul (hf z hz) (hg z hz)
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bt_sin_nonneg hθ) _)) (hUnn z)
  -- the value and the bound for `∫ badV`
  have hVval : ∫ θ, badV α g θ ∂(volume.restrict Iθ)
      = L2Sq (fun z θ => mixed 1 1 g z θ * Wt α z θ) := by
    have key : ∫ θ, badV α g θ ∂(volume.restrict Iθ)
        = ∫ z, (∫ θ, (mixed 1 1 g z θ * Wt α z θ) ^ 2 ∂(volume.restrict Iθ))
            ∂(volume.restrict Iz) := by
      have h1 : (∫ θ, badV α g θ ∂(volume.restrict Iθ))
          = ∫ θ, (∫ z', (mixed 1 1 g z' θ * Wt α z' θ) ^ 2 ∂(volume.restrict Iz))
              ∂(volume.restrict Iθ) := rfl
      rw [h1]
      exact (MeasureTheory.integral_integral_swap
        (f := fun z θ => (mixed 1 1 g z θ * Wt α z θ) ^ 2) hF2).symm
    rw [key, ← MeasureTheory.integral_prod
      (fun p : ℝ × ℝ => (mixed 1 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2) hF2, hF2val]
  have hVle : ∫ θ, badV α g θ ∂(volume.restrict Iθ) ≤ HkSq α 4 g := by
    rw [hVval]
    exact L2Sq_mixed_le_HkSq α 4 g hmemg 1 1 (le_refl 1) (by norm_num)
  -- the value and the bound for `∫ badU`
  have hUval : ∫ z, badU α f z ∂(volume.restrict Iz)
      = 100 / (gam α - 1) * L2Sq (fun z θ => mixed 3 1 f z θ * Wt α z θ) := by
    have h1 : (∫ z, badU α f z ∂(volume.restrict Iz))
        = ∫ z, (100 / (gam α - 1)
            * ∫ s, (mixed 3 1 f z s * Wt α z s) ^ 2 ∂(volume.restrict Iθ))
          ∂(volume.restrict Iz) := rfl
    rw [h1, MeasureTheory.integral_const_mul]
    congr 1
  have hUle : ∫ z, badU α f z ∂(volume.restrict Iz) ≤ 100 / (gam α - 1) * HkSq α 4 f := by
    rw [hUval]
    exact mul_le_mul_of_nonneg_left
      (L2Sq_mixed_le_HkSq α 4 f hmemf 1 3 (by norm_num) (by norm_num)) hcpos.le
  -- the inner (`θ`-)estimate
  have hinner : ∀ z ∈ Iz, ∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2
      ≤ badU α f z * ∫ θ in Iθ, badV α g θ := by
    intro z hz
    calc ∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2
        = ∫ θ in Iθ, ((DzIter 3 f z θ) ^ 2 * (w z) ^ 2)
            * ((Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
          exact bt_factor α z θ hα hθ f g
      _ ≤ ∫ θ in Iθ, badU α f z * badV α g θ := by
          apply MeasureTheory.integral_mono_of_nonneg
          · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
            exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
              (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bt_sin_nonneg hθ) _))
          · exact hVint.const_mul _
          · filter_upwards [hdom, ae_restrict_mem measurableSet_Icc] with θ hb hθ
            have hbz := hb z hz
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hbz
            rw [bt_factor α z θ hα hθ f g] at hbz
            exact hbz
      _ = badU α f z * ∫ θ in Iθ, badV α g θ := MeasureTheory.integral_const_mul _ _
  -- the outer (`z`-)estimate
  have houter : ∫ z in Iz, (∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2)
      ≤ (∫ θ in Iθ, badV α g θ) * ∫ z in Iz, badU α f z := by
    calc ∫ z in Iz, (∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2)
        ≤ ∫ z in Iz, badU α f z * (∫ θ in Iθ, badV α g θ) := by
          apply MeasureTheory.integral_mono_of_nonneg
          · filter_upwards with z
            exact integral_nonneg fun θ => sq_nonneg _
          · exact hUint.mul_const _
          · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
            exact hinner z hz
      _ = (∫ z in Iz, badU α f z) * (∫ θ in Iθ, badV α g θ) := by
          rw [MeasureTheory.integral_mul_const]
      _ = (∫ θ in Iθ, badV α g θ) * ∫ z in Iz, badU α f z := by ring
  refine ⟨?_, ?_⟩
  · exact BadMemQ α f g hfsq hgsq hUint hVint hdom
  · calc L2Sq (fun z θ => DzIter 3 f z θ * Dth g z θ * Wt α z θ)
        = ∫ z in Iz, (∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2) := rfl
      _ ≤ (∫ θ in Iθ, badV α g θ) * ∫ z in Iz, badU α f z := houter
      _ ≤ HkSq α 4 g * (100 / (gam α - 1) * HkSq α 4 f) :=
          mul_le_mul hVle hUle (integral_nonneg hUnn) (HkSq_nonneg α 4 g)
      _ = 100 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring

end Work.FTS.H2.HQ
