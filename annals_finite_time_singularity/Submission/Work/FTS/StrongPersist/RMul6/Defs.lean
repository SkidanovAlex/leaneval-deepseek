/-
# `Submission/Work/FTS/StrongPersist/RMul6/Defs.lean`

Definitions and elementary facts for the level-six radial product estimate
(`Work.FTS.StrongPersist.radialMul6`).

The level-four analogue of all of this is `Submission/Work/FTS/OpenPkg/radialMul_field.lean`
(together with `Submission/Work/FTS/Nonlinear/RadialProd/radial_prod.lean`); here every
statement is the `k = 6` instance.  The two quantities are

* `Rint6 r z = Σ_{i ≤ 6} (D_z^i r z)² w(z)²`, `Rr6 r = ∫_z Rint6 r z` — the radial density and
  its integral.  `HkSq α 6 (fun z θ => r z) = Rr6 r * K_θ` with `K_θ = ∫_θ sin(2θ)^{-η} ≥ 1`,
  so `Rr6 r ≤ HkSq α 6 (radial r)`;
* the radial Hardy inequality `(D_z^b r z)² ≤ Rr6 r` for `b ≤ 5` (`dzdIter_sq_le_Rr6_open`),
  which is what makes the pointwise product bound work.

All the facts here are `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.H2.HQ.HardyZQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.RMul6

open Work.FTS.EllipticEst (SmoothOpen Q0)
open Work.FTS.Nonlinear.RadialProd (Qg smE PsiZ psiZ Kth)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The radial density of the level-six norm -/

/-- `Rint6 r z = Σ_{i ≤ 6} (D_z^i r z)² w(z)²`: the radial density of the `ℋ⁶`-norm of the
radial lift of `r`. -/
def Rint6 (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 7, (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2

/-- `Rr6 r = ∫_z Σ_{i ≤ 6} (D_z^i r z)² w(z)² dz`. -/
def Rr6 (r : ℝ → ℝ) : ℝ := ∫ z in Work.Spaces.Iz, Rint6 r z

theorem Rint6_nonneg (r : ℝ → ℝ) (z : ℝ) : 0 ≤ Rint6 r z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem Rr6_nonneg (r : ℝ → ℝ) : 0 ≤ Rr6 r :=
  integral_nonneg fun z => Rint6_nonneg r z

/-- A single slot of the radial density. -/
theorem slot_le_Rint6 (r : ℝ → ℝ) {i : ℕ} (hi : i ≤ 6) (z : ℝ) :
    (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ Rint6 r z :=
  Finset.single_le_sum
    (f := fun a => (Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2)
    (fun a _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

/-! ## `Rr6` against the level-six norm of the radial lift -/

/-- The inner `θ`-integral of the `ℋ⁶`-integrand of a radial function. -/
theorem integral_HkIntegrand_rad6 (α : ℝ) (r : ℝ → ℝ) (z : ℝ) :
    ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z _ => r z) z θ
      = Rint6 r z * Kth := by
  have hkey : (fun θ => Work.Spaces.HkIntegrand α 6 (fun z _ => r z) z θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] (fun θ => Rint6 r z * smE θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Work.Elliptic.HkIntegrand_rad α 6 r z hθ]
    simp only [Rint6, Finset.sum_mul, smE]
  rw [MeasureTheory.integral_congr_ae hkey, MeasureTheory.integral_const_mul]
  rfl

/-- The exact value of `HkSq` of a radial function at level six. -/
theorem HkSq_rad6 (α : ℝ) (r : ℝ → ℝ) :
    Work.Spaces.HkSq α 6 (fun z _ => r z) = Rr6 r * Kth := by
  rw [Work.Elliptic.HkSq_rad α 6 r]
  simp only [Rr6, Rint6, Kth, smE]

/-- `Rr6` is dominated by the `ℋ⁶`-norm of the radial lift (via `K_θ ≥ 1`). -/
theorem Rr6_le_HkSq6 (α : ℝ) (r : ℝ → ℝ) :
    Rr6 r ≤ Work.Spaces.HkSq α 6 (fun z _ => r z) := by
  rw [HkSq_rad6]
  nlinarith [Rr6_nonneg r, Work.FTS.Nonlinear.RadialProd.one_le_Kth]

/-! ## Integrability -/

/-- `Rr6` is finite whenever the radial lift is in `ℋ⁶`. -/
theorem integrable_Rint6 (α : ℝ) (r : ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α 6 (fun z _ => r z)) :
    MeasureTheory.IntegrableOn (Rint6 r) Work.Spaces.Iz := by
  have h := hmem.2
  rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (fun z _ => r z) z θ)
      = fun z => Rint6 r z * Kth from funext fun z => integral_HkIntegrand_rad6 α r z] at h
  have hK : Kth ≠ 0 := by linarith [Work.FTS.Nonlinear.RadialProd.one_le_Kth]
  refine h.mul_const Kth⁻¹ |>.congr (Filter.Eventually.of_forall fun z => ?_)
  show Rint6 r z * Kth * Kth⁻¹ = Rint6 r z
  rw [mul_assoc, mul_inv_cancel₀ hK, mul_one]

/-- A single radial slot is integrable over `Iz` when the radial lift is in `ℋ⁶`. -/
theorem integrable_slot6 (α : ℝ) (r : ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z))
    (hrm : Work.Spaces.HkMem α 6 (fun z _ => r z)) (b : ℕ) (hb : b ≤ 6) :
    MeasureTheory.IntegrableOn
      (fun s => (Work.Elliptic.DzdIter b r s) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz := by
  refine MeasureTheory.Integrable.mono' (integrable_Rint6 α r hrm)
    (Work.FTS.OpenPkg.aesm_DzdIter_sq_w_sq_open r hr b) ?_
  filter_upwards with s
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact slot_le_Rint6 r hb s

/-! ## The radial Hardy bound at level six -/

/-- **The radial Hardy bound.**  For `b ≤ 5` and `z > 0`, `(D_z^b r z)² ≤ Rr6 r`: `HardyZQ`
applied to the `z`-slice `D_z^b r`, whose Hardy integrand `(D_z^{b+1} r)²w²` is a slot of
the radial density. -/
theorem dzdIter_sq_le_Rr6_open (α : ℝ) (r : ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z))
    (hrm : Work.Spaces.HkMem α 6 (fun z _ => r z))
    (hdec : ∀ b : ℕ, b ≤ 6 → Filter.Tendsto (Work.Elliptic.DzdIter b r) Filter.atTop (nhds 0))
    {b : ℕ} (hb : b ≤ 5) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr6 r := by
  have hb6 : b + 1 ≤ 6 := by omega
  have hcd : ContDiffOn ℝ 1 (Work.Elliptic.DzdIter b r) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.OpenPkg.contDiffOn_DzdIter_open r hr b).of_le (by simp [Work.Stability.smoothOrder])
  have hint : MeasureTheory.IntegrableOn
      (fun s => (s * deriv (Work.Elliptic.DzdIter b r) s) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz := by
    have h := integrable_slot6 α r hr hrm (b + 1) hb6
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
  have hH := Work.FTS.H2.HQ.HardyZQ (Work.Elliptic.DzdIter b r) hcd (hdec b (by omega)) hint z
    (Set.mem_Ioi.mpr hz)
  refine le_trans hH ?_
  rw [show MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun s => (s * deriv (Work.Elliptic.DzdIter b r) s) ^ 2 * (Work.Spaces.w s) ^ 2)
      = MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun s => (Work.Elliptic.DzdIter (b + 1) r s) ^ 2 * (Work.Spaces.w s) ^ 2) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => by
      simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd])]
  rw [Rr6]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (integrable_Rint6 α r hrm)
    (Filter.Eventually.of_forall fun s => ?_)
  exact slot_le_Rint6 r hb6 s

/-! ## The `Qg`-slots -/

/-- `PsiZ g z θ ≤ HkIntegrand α 6 g z θ` on `Iθ`. -/
theorem PsiZ_le_HkIntegrand6 (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    PsiZ g z θ ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  rcases lt_or_eq_of_le (Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ) with
    hpos | heq
  · have h1 : PsiZ g z θ
        = (Work.Spaces.DzIter 1 g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [PsiZ, psiZ, Work.FTS.Nonlinear.RadialProd.light_sq (Work.Spaces.DzIter 1 g z θ) z θ hpos]
      ring
    rw [h1]
    exact Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ 1 (by norm_num)
  · rw [PsiZ, psiZ, smE, ← heq,
      Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : -(Work.Spaces.eta) ≠ 0), zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 6 g z θ

/-- The `θ`-slice form of the previous bound (at an interior angle, so `sin(2θ) > 0`). -/
theorem psiZ_le_HkIntegrand6_of_Ioo (α : ℝ) (g : ℝ → ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (s : ℝ) :
    psiZ g s θ ≤ Work.Spaces.HkIntegrand α 6 g s θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_pos_of_mem_Ioo hθ
  have h1 : psiZ g s θ * smE θ
      = (Work.Spaces.DzIter 1 g s θ
          * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [psiZ, Work.FTS.Nonlinear.RadialProd.light_sq (Work.Spaces.DzIter 1 g s θ) s θ hsin]
  calc psiZ g s θ = psiZ g s θ * 1 := by ring
    _ ≤ psiZ g s θ * smE θ :=
        mul_le_mul_of_nonneg_left (Work.FTS.Nonlinear.RadialProd.one_le_smE hθ)
          (Work.FTS.Nonlinear.RadialProd.psiZ_nonneg g s θ)
    _ = _ := h1
    _ ≤ Work.Spaces.HkIntegrand α 6 g s θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 6 g s θ 1 (by norm_num)

end Work.FTS.StrongPersist.RMul6
