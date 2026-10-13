/-
Copyright: work module for the Elgindi finite-time singularity project.

# The level-`n` weighted `L²`-bound for the angular moment `Qang g i`

For `SmoothQuad g` and `HkMem α n g`, every angular moment `Qang g i` with `i ≤ n`
satisfies

  `Qang g i z = ∫_θ Ktheta θ · D_z^i g (z,θ) dθ`,
  `∫_z (Qang g i z)² w(z)² dz ≤ (∫_θ Ktheta θ²) · HkSq α n g`,

with the honest `IntegrableOn` statement on `Iz = [0,∞)`.

This is the level-`n` version of `Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral`
(which is stated at level `4`), and of the level-`4` Cauchy–Schwarz statement
`Work.FTS.H2.Qang_sq_leQ`.  The only ingredient that is genuinely tied to the level is the
Cauchy–Schwarz step in `θ`, which in `Work.FTS.H2.Qang_sq_leQ` is stated with `HkMem α 4 g`
and `j ≤ 4`; here it is reproved in the general form `Qang_sq_leQ_gen` (the level `4` in that
proof is only the level at which the angular slice of the `ℋ^k`-integrand happens to be
named; the domination lemma `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` is already
general in `k`).

The assembly is the one of `Qang_sq_w_sq_integral`: pointwise in `z > 0` the
Cauchy–Schwarz bound in `θ` is composed with the slicewise domination
`(D_z^i g z θ)² w² ≤ HkIntegrand α n g z θ`, and both `z = 0` and the two angular endpoints
are null sets.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.Qang_sq_leQ
import Submission.Work.FTS.H2.QangAux
import Submission.Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

open MeasureTheory
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Null sets and the weight `w` -/

/-- The `z = 0`-slice of `Iz = [0,∞)` is null, so every almost-everywhere statement on
`Iz` may be proved on the open half-line. -/
private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- The two angular endpoints of `Iθ = [0,π/2]` are null. -/
private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- The radial weight `w` squared is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

/-! ## The general-level Cauchy–Schwarz bound in `θ` -/

/-- **Cauchy–Schwarz in `θ` at level `k`.**  For `SmoothQuad g`, `HkMem α k g`, `j ≤ k` and
`z > 0`,

  `(Qang g j z)² ≤ (∫_θ Ktheta θ²)·(∫_θ (D_z^j g z θ)²)`.

Exactly as in `Work.FTS.H2.Qang_sq_leQ` (which is the case `k = 4`), the two hypotheses are
used only through the integrability of the `θ`-slice of the `ℋ^k`-integrand and the
pointwise domination `(D_z^j g z θ)² ≤ HkIntegrand α k g z θ / w²`
(`Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq`, which together with `w ≥ 1` gives the
domination by the integrand itself).  Both `θ`-slices are continuous on the *open* interval
`(0,π/2)` — `SmoothQuad` gives smoothness only on the open quadrant — which is harmless
because the two endpoints are null. -/
theorem Qang_sq_leQ_gen (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g)
    {k : ℕ} (hmem : Work.Spaces.HkMem α k g) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Qang g j z) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
  -- `Iθ = Icc 0 (π/2)` and the open interval `Ioo 0 (π/2)` differ by the two endpoints, a null
  -- set: every integral below can be taken over the open interval, where the `θ`-slice of
  -- `D_z^j g` is continuous.
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
  have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hAcont : ContinuousOn (fun θ => Work.Spaces.DzIter j g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hsm.DzIter j).curry_θ hzIoi).continuousOn
  -- `Ktheta` is continuous everywhere (hence on `Iθ` and on `Ioo 0 (π/2)`)
  have hKcont : Continuous (fun θ => Work.Elliptic.Ktheta θ) := by
    unfold Work.Elliptic.Ktheta
    fun_prop
  -- integrability of `Ktheta²` on the open interval (continuity on the compact closure)
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
  -- a.e. strong measurability of the `θ`-slice
  have hAesm : AEStronglyMeasurable (fun θ => |Work.Spaces.DzIter j g z θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using (hAcont.aestronglyMeasurable measurableSet_Ioo).norm
  -- integrability of `(D_z^j g z ·)²`: dominated by the `ℋ^k`-integrand on the open interval
  have hA2int : IntegrableOn (fun θ => |Work.Spaces.DzIter j g z θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine hHkint.mono' (hAesm.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    -- the pure `D_z`-slot is dominated by the whole `ℋ^k`-integrand (the radial weight
    -- `w` is `≥ 1` on `(0,∞)`)
    have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α k g j hj hz hθ
    exact le_trans h1 (div_le_self (Work.Spaces.HkIntegrand_nonneg α k g z θ)
      (one_le_pow₀ (Work.Elliptic.one_le_w hz)))
  have hKesm : AEStronglyMeasurable (fun θ => |Work.Elliptic.Ktheta θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using hKcont.aestronglyMeasurable.norm
  have hKabs : IntegrableOn (fun θ => |Work.Elliptic.Ktheta θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    simpa only [sq_abs] using hK2int
  -- `L²`-membership of the two factors (`p = q = 2`)
  have hKmem : MemLp (fun θ => |Work.Elliptic.Ktheta θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hKesm).mpr hKabs
  have hAmem : MemLp (fun θ => |Work.Spaces.DzIter j g z θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hAesm).mpr hA2int
  -- Cauchy–Schwarz for the Bochner integral (`p = q = 2`, both factors nonnegative)
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

/-! ## The slicewise domination by the `ℋ^k`-integrand -/

/-- For `z > 0` and `0 < θ < π/2` the square of the weighted pure `D_z`-iterate is
dominated by the `ℋ^k`-integrand, `(D_z^i g z θ)² w(z)² ≤ HkIntegrand α k g z θ` (`i ≤ k`).
This is `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` multiplied by `w² > 0`. -/
private theorem DzIter_sq_w_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {k i : ℕ} (hi : i ≤ k)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α k g i hi hz hθ
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Work.Spaces.w z))
  rwa [div_mul_cancel₀ _
    (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hz)))] at h2

/-! ## The target -/

theorem Qang_sq_w_sq_le_HkSq (n : ℕ) :
    ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.LocData.SmoothQuad g →
      Work.Spaces.HkMem α n g → ∀ i : ℕ, i ≤ n →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n g := by
  intro α g hα hα1 hsm hmem i hi
  -- the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) := by
    intro z hz
    -- Cauchy–Schwarz in `θ`, at level `n`
    have hCS := Qang_sq_leQ_gen α g hsm hmem i hi hz
    -- the `θ`-slice domination, with the weight `w z` on the left
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α n g z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => DzIter_sq_w_sq_le_HkIntegrand α g hi hz hθ)
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
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) :=
          mul_le_mul_of_nonneg_left hslice
            (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
  -- the bound holds almost everywhere on `Iz`
  have hle : (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ)) := by
    rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt
  -- a.e. strong measurability of the left-hand side
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hQ : AEStronglyMeasurable (fun z => Work.Elliptic.Qang g i z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h := (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i g p.1 p.2)
        (Work.FTS.H2.continuousOn_Ktheta_DzIter hsm i)).integral_prod_right'
      simpa only [Work.Elliptic.Qang] using h
    have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
      exact continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi
    exact (hQ.pow 2).mul hw
  -- the dominating function is integrable
  have hdom : MeasureTheory.Integrable
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ))
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

end Work.FTS.CoercivityFix.Transfer.E1Norm
