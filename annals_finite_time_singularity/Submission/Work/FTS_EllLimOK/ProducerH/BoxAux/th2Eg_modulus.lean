-- ABANDONED SCAFFOLDING (2026-10-11): this file still contains an unfinished `sorry`; it is NOT
-- in the proof cone of any delivered theorem of this area (see `NOTES.md` §12 and the axiom checks
-- in `_wip/axfinal_h.lean`).  Kept only as the record of the producer workstreams.
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2Ident
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.cos_inv_cube_mul_integral_le
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_package_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The rate of `Lzero (E g) z`**: the source `g` contributes the class-`C` rate `m^{α/20}`, the
radial terms `D_z^j Ψ` the rate `m`. -/
theorem lzero_rate {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Fn →ₗ[ℝ] Fn}
    (hE : ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo 0 (π / 2),
        |Work.Elliptic.Lzero (E g) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g
            * (min θ (π / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨Cg, hCgpos, hCg⟩ := classCSinRate hα hα1
  obtain ⟨Cψ, hCψpos, hCψ⟩ := psiDz_rate hα hα4 hE ha₀ hab
  refine ⟨Cg + 2 * α ^ 2 * Cψ + α * (5 + α) * Cψ + 1, by positivity, ?_⟩
  intro g hg z hz θ hθ
  have hz0 : 0 < z := lt_of_lt_of_le ha₀ hz.1
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  have hβ1 : (Work.Spaces.gam α - 1) / 2 ≤ 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hmβ : min θ (π / 2 - θ) ≤ (min θ (π / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2) :=
    min_rpow_ge_self hβ1 hθ
  have hm0 : 0 ≤ min θ (π / 2 - θ) := le_of_lt (lt_min hθ.1 (by linarith [hθ.2]))
  -- the decomposition `Lzero Ψ = g + α²D_z²Ψ + (α(5+α) − α²)D_zΨ`
  have hsol : Work.Elliptic.bslOp α (E g) z θ = g z θ := (hE g hg).1.1.1 z hz0 θ hθ.1 hθ.2
  have hL := Work.FTS_EllLimOK.ProducerH.SecondDeriv.Lzero_eq_bslOp_add α (E g) z θ
  have hslice : ∀ θ' ∈ Set.Ioo 0 (π / 2),
      ContDiffOn ℝ 2 (fun z' => (E g) z' θ') (Set.Ioi 0) :=
    fun θ' hθ' => (((hE g hg).1.2.1).curry_z hθ').of_le (by simp [Work.Stability.smoothOrder])
  have hzsq := Work.FTS_EllLimOK.ProducerH.SecondDeriv.zsq_pzIter_two_eq (h := E g) hslice hz0 hθ
  have hmain : Work.Elliptic.Lzero (E g) z θ
      = g z θ + α ^ 2 * Work.Spaces.DzIter 2 (E g) z θ
        + (α * (5 + α) - α ^ 2) * Work.Spaces.DzIter 1 (E g) z θ := by
    rw [hL, hsol]
    simp only [Work.Spaces.mixed_zero_right] at hzsq
    rw [hzsq]
    have hz1 : α * (5 + α) * z * Work.Spaces.pz (E g) z θ
        = (α * (5 + α)) * Work.Spaces.DzIter 1 (E g) z θ := by
      rw [show Work.Spaces.DzIter 1 (E g) z θ
          = z * Work.Spaces.pz (E g) z θ from rfl]
      ring
    rw [hz1]
    ring
  rw [hmain]
  have hcoef : α * (5 + α) - α ^ 2 = 5 * α := by ring
  have hA := hCg g hg z hz0 θ hθ
  have hB := hCψ g hg 2 (by norm_num) z hz θ hθ
  have hC := hCψ g hg 1 (by norm_num) z hz θ hθ
  have hBβ : |Work.Spaces.DzIter 2 (E g) z θ|
      ≤ Cψ * Work.FTS.StrongGlobal.Xn6 α g
        * (min θ (π / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2) :=
    le_trans hB (mul_le_mul_of_nonneg_left hmβ (mul_nonneg hCψpos.le hX0))
  have hCβ : |Work.Spaces.DzIter 1 (E g) z θ|
      ≤ Cψ * Work.FTS.StrongGlobal.Xn6 α g
        * (min θ (π / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2) :=
    le_trans hC (mul_le_mul_of_nonneg_left hmβ (mul_nonneg hCψpos.le hX0))
  have h5α : (0 : ℝ) ≤ 5 * α := by linarith
  rw [hcoef]
  have hP : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g
      * (min θ (π / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2) :=
    mul_nonneg hX0 (Real.rpow_nonneg hm0 _)
  have hU1 : (0 : ℝ) ≤ Cg * Work.FTS.StrongGlobal.Xn6 α g
      * (min θ (π / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2) :=
    mul_nonneg (mul_nonneg hCgpos.le hX0) (Real.rpow_nonneg hm0 _)
  have hU2 : (0 : ℝ) ≤ Cψ * Work.FTS.StrongGlobal.Xn6 α g
      * (min θ (π / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2) :=
    mul_nonneg (mul_nonneg hCψpos.le hX0) (Real.rpow_nonneg hm0 _)
  have h1 : |g z θ + α ^ 2 * Work.Spaces.DzIter 2 (E g) z θ|
      ≤ Cg * Work.FTS.StrongGlobal.Xn6 α g
          * (min θ (π / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2)
        + α ^ 2 * (Cψ * Work.FTS.StrongGlobal.Xn6 α g
          * (min θ (π / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2)) := by
    refine le_trans (abs_add_le _ _) (add_le_add hA ?_)
    rw [abs_mul, abs_of_nonneg (sq_nonneg α)]
    exact mul_le_mul_of_nonneg_left hBβ (sq_nonneg α)
  have h2 : |5 * α * Work.Spaces.DzIter 1 (E g) z θ|
      ≤ 5 * α * (Cψ * Work.FTS.StrongGlobal.Xn6 α g
          * (min θ (π / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2)) := by
    rw [abs_mul, abs_of_nonneg h5α]
    exact mul_le_mul_of_nonneg_left hCβ h5α
  refine le_trans (le_trans (abs_add_le _ _) (add_le_add h1 h2)) ?_
  nlinarith [hP, hU1, hU2, hCgpos, hCψpos, hα]


theorem th2Eg_modulus {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.ClassC.ClassC α g → ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo 0 (π / 2),
        |deriv (deriv (fun θ' => (E g) z θ')) θ|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (min θ (π / 2 - θ)) ^ β := by sorry


end Work.FTS_EllLimOK.ProducerH.BoxAux
