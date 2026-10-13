/-
# `Work.FTS.StrongPersist.QangSq6` — the level-six weighted `L²`-bound for `Qang`

The angular moment of a datum `g` of the open quadrant is
`Qang g j z = ∫_θ Kθ(θ)·(D_z^j g)(z,θ) dθ`, and its contribution to the norm of the
first-order elliptic corrector `L₁₂(g)` is the weighted `z`-integral
`∫_z (Qang g j z)² w(z)² dz`.  This module proves the level-six bound

  `∫_z (Qang g i z)² w(z)² dz ≤ (∫_θ Kθ(θ)² dθ) · |g|²_{ℋ⁶}`     (`i ≤ 5`),

for a datum which is `C^∞` on the *open* quadrant (`SmoothOpen g`) and lies in the weighted
space `ℋ⁶` (`HkMem α 6 g`).  It is the level-six counterpart of
`Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open` (`i ≤ 4`, `|g|²_{ℋ⁴}`), and one of the
two inputs of the `L₁₂`-clause `N6_L12H` (the other being the `z`-differentiation
`QangDiff6`).

Route (identical to the level-four sibling, with `4 ↦ 6`):

* **Cauchy–Schwarz in `θ`** (`Qang_sq_le_k` below, the `k`-general form of
  `Work.FTS.H2.Qang_sq_leQ`): `(Qang g i z)² ≤ (∫_θ Kθ²)·∫_θ (D_z^i g)²`.  Both `θ`-slices are
  measured on the *open* interval `(0,π/2)` (the two endpoints are null), where the slice of
  `D_z^i g` is continuous by `SmoothOpen.curry_θ`; square-integrability comes from the
  pointwise domination `(D_z^i g)² ≤ HkIntegrand α k g` (`i ≤ k`), transported across the null
  set from `hmem.1`.
* **Absorbing the weight** `w(z)²` into the `θ`-integral gives the pointwise (in `z > 0`) bound
  `(Qang g i z)² w(z)² ≤ (∫_θ Kθ²)·∫_θ HkIntegrand α 6 g z θ`, since
  `(D_z^i g)² w² ≤ HkIntegrand α 6 g` (`Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq`).
* **Integrating in `z`**: the dominating function `z ↦ (∫_θ Kθ²)·∫_θ HkIntegrand α 6 g z θ` is
  integrable on `Iz` by `hmem.2`, the left-hand side is a.e. strongly measurable
  (`AEStronglyMeasurable.integral_prod_right'` applied to the jointly continuous
  `(z,θ) ↦ Kθ(θ)·D_z^i g z θ`), and `∫_z ∫_θ HkIntegrand α 6 g z θ = HkSq α 6 g` by definition.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.H2.Qang_sq_leQ
import Submission.Work.FTS.H2.QangAux
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

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

/-! ## The pointwise slot domination at an arbitrary order `k` -/

/-- **A single pure `D_z`-slot of the `ℋ^k`-integrand dominates the square of the iterate, on
the open quadrant.**  On `z > 0` and `0 < θ < π/2` one has `w(z) ≥ 1` and
`sin(2θ)^{-η} ≥ 1`, so the weighted slot `(D_z^j g · w/sin(2θ)^{η/2})²` of the integrand
dominates the unweighted square: `(D_z^j g)² ≤ HkIntegrand α k g` for `j ≤ k`.

This is `Work.Elliptic.sq_DzIter_le_HkIntegrand_Qd` (the case `k = 4`) with `4 ↦ k`. -/
private theorem sq_DzIter_le_HkIntegrand_k (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) {j : ℕ}
    (hj : j ≤ k) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw := Work.Elliptic.one_le_w hz
  have hsinp := Work.Elliptic.one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
  have hstep : (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    calc (Work.Spaces.DzIter j g z θ) ^ 2
        = (Work.Spaces.DzIter j g z θ) ^ 2 * 1 * 1 := by ring
      _ ≤ (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)) hsinp ?_ (by positivity)
          positivity
  have heq : (Work.Spaces.DzIter j g z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
    have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      norm_num
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
    ring
  rw [← heq] at hstep
  exact le_trans hstep (Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hj)

/-! ## The weighted slot, with the full weight `w²` -/

/-- On the open quadrant, `(D_z^i g)²·w²` is dominated by the `ℋ^k`-integrand (`i ≤ k`).
Immediate from `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` (which gives
`(D_z^i g)² ≤ HkIntegrand/w²`) after multiplying by `w² > 0`. -/
private theorem DzIter_sq_w_sq_le_HkIntegrand_k (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) {i : ℕ}
    (hi : i ≤ k) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α k g i hi hz hθ
  have hw : 0 < (Work.Spaces.w z) ^ 2 := pow_pos (Work.FTS.H2.w_pos hz) 2
  rw [le_div_iff₀ hw] at h1
  exact h1

/-! ## Cauchy–Schwarz in `θ` at an arbitrary order `k` -/

/-- **Cauchy–Schwarz in `θ` for the angular moment, at an arbitrary order `k`.**  For a datum
which is `C^∞` on the open quadrant and lies in `ℋ^k`, and for `j ≤ k` and `z > 0`,

  `(Qang g j z)² ≤ (∫_θ Kθ(θ)² dθ)·∫_θ (D_z^j g z θ)² dθ`,

with the `α`-independent constant `∫_θ Kθ²`.

This is `Work.FTS.H2.Qang_sq_leQ` / `Work.FTS.OpenPkg.QangOpen.Qang_sq_leQ_open` with the fixed
order `4` replaced by `k`: the `θ`-integrals are taken over the open interval `(0,π/2)` (the
endpoints are null), where both factors are continuous and square-integrable, and the standard
`L²`-Cauchy–Schwarz (`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`) applies. -/
private theorem Qang_sq_le_k (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) {k : ℕ} (hmem : Work.Spaces.HkMem α k g)
    (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Qang g j z) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
  have hIoo : (Set.Icc (0 : ℝ) (π / 2)) =ᵐ[volume] (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hQeq : Work.Elliptic.Qang g j z
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.setIntegral_congr_set hIoo
  have hKeq : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  have hAeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  -- the `θ`-slice of `D_z^j g` at `z > 0` is continuous on `(0,π/2)`
  have hAcont : ContinuousOn (fun θ => Work.Spaces.DzIter j g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hO.DzIter j).curry_θ hz).continuousOn
  have hKcont : Continuous (fun θ => Work.Elliptic.Ktheta θ) := by
    unfold Work.Elliptic.Ktheta
    fun_prop
  have hK2int : IntegrableOn (fun θ => Work.Elliptic.Ktheta θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hKcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  -- integrability of `HkIntegrand α k g z ·`, transported from `hmem` to the open interval
  have hHkint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    change Integrable (fun θ => Work.Spaces.HkIntegrand α k g z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    simpa only [Work.Spaces.Iθ, IntegrableOn] using hmem.1 z (le_of_lt hz)
  have hAesm : AEStronglyMeasurable (fun θ => |Work.Spaces.DzIter j g z θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using (hAcont.aestronglyMeasurable measurableSet_Ioo).norm
  have hA2int : IntegrableOn (fun θ => |Work.Spaces.DzIter j g z θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine hHkint.mono' (hAesm.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    exact sq_DzIter_le_HkIntegrand_k α k g hj hz hθ.1 hθ.2
  have hKesm : AEStronglyMeasurable (fun θ => |Work.Elliptic.Ktheta θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using hKcont.aestronglyMeasurable.norm
  have hKabs : IntegrableOn (fun θ => |Work.Elliptic.Ktheta θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    simpa only [sq_abs] using hK2int
  have hKmem : MemLp (fun θ => |Work.Elliptic.Ktheta θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hKesm).mpr hKabs
  have hAmem : MemLp (fun θ => |Work.Spaces.DzIter j g z θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hAesm).mpr hA2int
  have hcs := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    (p := 2) (q := 2) (f := fun θ => |Work.Elliptic.Ktheta θ|)
    (g := fun θ => |Work.Spaces.DzIter j g z θ|)
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun θ => abs_nonneg _)
    (Filter.Eventually.of_forall fun θ => abs_nonneg _) hKmem hAmem
  have hnQ : |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
    simpa only [Real.norm_eq_abs, abs_mul] using h
  have hKIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Elliptic.Ktheta θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hAIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hK0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hA0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hmain : (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
    calc (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
        = |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
            Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ| ^ 2 := by rw [sq_abs]
      _ ≤ (Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
            * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                (Work.Spaces.DzIter j g z θ) ^ 2)) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          calc |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
              ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                  |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := hnQ
            _ ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Elliptic.Ktheta θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
                * (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hcs
            _ = Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
                * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    (Work.Spaces.DzIter j g z θ) ^ 2) := by
                rw [hKIsq, hAIsq, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      _ = (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt hA0]
  rw [hQeq, hKeq, hAeq]
  exact hmain

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

/-! ## The level-six bound -/

theorem QangSq6 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    ∀ i : ℕ, i ≤ 5 →
      MeasureTheory.IntegrableOn (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 6 g := by
  intro i hi
  have hi6 : i ≤ 6 := by omega
  have hK0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  -- ## the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := by
    intro z hz
    have hCS := Qang_sq_le_k α g hO hmem i hi6 hz
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => DzIter_sq_w_sq_le_HkIntegrand_k α 6 g hi6 hz hθ)
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
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) :=
          mul_le_mul_of_nonneg_left hslice hK0
  -- ## the bound holds almost everywhere on `Iz`
  have hle : (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ)) := by
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
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ))
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

end Work.FTS.StrongPersist
