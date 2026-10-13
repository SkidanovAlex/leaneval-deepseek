/-
# `Work.FTS.StrongEps.H5.Atoms.QangSq5` — the level-five weighted `L²`-bound for `Qang`

The angular moment of a datum `g` of the open quadrant is

  `Qang g j z = ∫_θ Kθ(θ)·(D_z^j g)(z,θ) dθ`,

and its contribution to the norm of the first-order elliptic corrector `L₁₂(g)` is the weighted
`z`-integral `∫_z (Qang g j z)² w(z)² dz`.  This module proves the level-five bound

  `∫_z (Qang g i z)² w(z)² dz ≤ (∫_θ Kθ(θ)² dθ) · |g|²_{ℋ⁵}`     (`i ≤ 5`),

for a datum which is `C^∞` on the *open* quadrant (`SmoothOpen g`) and lies in the weighted
space `ℋ⁵` (`HkMem α 5 g`).  It is the level-five counterpart of
`Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open` (`i ≤ 4`, `|g|²_{ℋ⁴}`) — the atom the
level-five `L₁₂`-bundle needs — obtained by the same route with `4 ↦ 5`:

* **Cauchy–Schwarz in `θ`**, in the level-general form
  `Work.FTS.OpenPkg.Qang_sq_leQ_gen_open`: `(Qang g i z)² ≤ (∫_θ Kθ²)·∫_θ (D_z^i g)²`.  Both
  `θ`-slices are measured on the *open* interval `(0,π/2)` (the two endpoints are null), where
  the slice of `D_z^i g` is continuous by `SmoothOpen.curry_θ`; square-integrability comes from
  the pointwise domination `(D_z^i g)² ≤ HkIntegrand α 5 g` (`i ≤ 5`), transported across the
  null set from `hmem.1`.
* **Absorbing the weight** `w(z)²` into the `θ`-integral gives the pointwise (in `z > 0`) bound
  `(Qang g i z)² w(z)² ≤ (∫_θ Kθ²)·∫_θ HkIntegrand α 5 g z θ`, since
  `(D_z^i g)² w² ≤ HkIntegrand α 5 g`
  (`Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq`).
* **Integrating in `z`**: the dominating function `z ↦ (∫_θ Kθ²)·∫_θ HkIntegrand α 5 g z θ` is
  integrable on `Iz` by `hmem.2`, the left-hand side is a.e. strongly measurable
  (`AEStronglyMeasurable.integral_prod_right'` applied to the jointly continuous
  `(z,θ) ↦ Kθ(θ)·D_z^i g z θ`), and `∫_z ∫_θ HkIntegrand α 5 g z θ = HkSq α 5 g` by definition.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.OpenPkg.Qang_sq_leQ_gen_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Null-set bookkeeping (the two ends of `Iz`, the two angular endpoints) -/

private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- `w²` is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

/-! ## The weighted slot, with the full weight `w²`, at level `5` -/

/-- On the open quadrant, `(D_z^i g)²·w²` is dominated by the `ℋ⁵`-integrand (`i ≤ 5`).
Immediate from `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` (which gives
`(D_z^i g)² ≤ HkIntegrand/w²`) after multiplying by `w² > 0`. -/
private theorem DzIter_sq_w_sq_le_HkIntegrand_five (α : ℝ) (g : ℝ → ℝ → ℝ) {i : ℕ}
    (hi : i ≤ 5) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 5 g i hi hz hθ
  have hw : 0 < (Work.Spaces.w z) ^ 2 := pow_pos (Work.FTS.H2.w_pos hz) 2
  rw [le_div_iff₀ hw] at h1
  exact h1

/-! ## A.e. strong measurability of the angular moment -/

/-- `z ↦ Qang g i z` is a.e. strongly measurable on `Iz` (no integrability needed): it is the
`θ`-integral of the jointly continuous `(z,θ) ↦ Kθ(θ)·D_z^i g z θ` on the open quadrant
(`AEStronglyMeasurable.integral_prod_right'`). -/
private theorem aesm_Qang (i : ℕ) {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) :
    AEStronglyMeasurable (fun z : ℝ => Work.Elliptic.Qang g i z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h := (Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i g p.1 p.2)
    (Work.FTS.OpenPkg.QangOpen.continuousOn_Ktheta_DzIter_open hO i)).integral_prod_right'
  simpa only [Work.Elliptic.Qang] using h

/-! ## The level-five bound -/

/-- Level-`5` weighted `L²`-bound for the angular moment `Qang g i z = ∫_θ Ktheta θ · D_z^i g (z,θ) dθ`. -/
theorem QangSq5 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 5 g) :
    ∀ i : ℕ, i ≤ 5 →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 5 g := by
  intro i hi
  have hK0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  -- ## the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 g z θ) := by
    intro z hz
    have hCS := Work.FTS.OpenPkg.Qang_sq_leQ_gen_open α g hO hmem i hi hz
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 g z θ := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => DzIter_sq_w_sq_le_HkIntegrand_five α g hi hz hθ)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 z (le_of_lt hz)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    calc (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hCS (sq_nonneg _)
      _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 g z θ) :=
          mul_le_mul_of_nonneg_left hslice hK0
  -- ## the bound holds almost everywhere on `Iz`
  have hle : (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 g z θ)) := by
    rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt
  -- ## a.e. strong measurability
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hQ := aesm_Qang i hO
    have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
      exact continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi
    exact (hQ.pow 2).mul hw
  -- ## the dominating function is integrable
  have hdom : MeasureTheory.Integrable
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul _
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [hle] with z hz
    rwa [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  · have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      hdom hle
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono.trans (le_of_eq rfl)

end Work.FTS.StrongEps.H5.Atoms
