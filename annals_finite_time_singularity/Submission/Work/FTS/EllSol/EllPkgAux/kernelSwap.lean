/-
# `Work.FTS.EllSol.EllPkgAux.kernelSwap` — Fubini for the mollification kernel

The kernel `KJ ε θ s` is nonnegative, jointly continuous and globally bounded
(`KJ_nonneg`, `KJ_le`, `continuous_KJ` in `KernelDefs`), while the angular weight
`θ ↦ sin(2θ)^{-η}` is integrable on `Iθ` (`EllipticEst.integrableOn_thEta`).  Hence for
every `g` whose square is integrable on `Iθ` the *whole* double integrand

  `(θ, s) ↦ thEta θ * (KJ ε θ s * g s ^ 2)`

is integrable on the product `Iθ × Iθ`: it is dominated by
`3 (ε · sMass)⁻¹ · thEta θ · g s ^ 2`, a product of two integrable functions.  Fubini's
theorem then gives `kernelSwap`: the iterated integral can be computed in either order,
and both iterated integrands are integrable.

The dominating function is used only on the box `Iθ × Iθ` (the weight `thEta` is not
integrable on the whole line), which is exactly the support of the product measure
`(volume.restrict Iθ).prod (volume.restrict Iθ)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

open MeasureTheory Filter

/-- `KJ ε · ·` is bounded by `3 (ε · sMass)⁻¹` (it is nonnegative, so its norm is itself). -/
theorem norm_KJ_le {ε : ℝ} (hε : 0 < ε) (θ s : ℝ) :
    ‖KJ ε θ s‖ ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ := by
  rw [Real.norm_of_nonneg (KJ_nonneg hε θ s)]
  exact KJ_le hε θ s

/-- The double integrand of `kernelSwap` is integrable on the product `Iθ × Iθ`. -/
theorem integrable_uncurry_kernel {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hgi : MeasureTheory.IntegrableOn (fun s : ℝ => g s ^ 2) Work.Spaces.Iθ) :
    Integrable (Function.uncurry (fun θ s : ℝ =>
        Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2)))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hgi' : Integrable (fun s : ℝ => g s ^ 2) (volume.restrict Work.Spaces.Iθ) := hgi
  have hσ : Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1
  -- the dominating function, a product of two integrable factors
  have hdom : Integrable (fun p : ℝ × ℝ =>
      (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ * Work.FTS.EllipticEst.thEta p.1)
        * g p.2 ^ 2)
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) :=
    (hσ.const_mul _).mul_prod hgi'
  -- almost everywhere strong measurability of the integrand
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.EllipticEst.thEta p.1 * (KJ ε p.1 p.2 * g p.2 ^ 2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.1)
        ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) :=
      hσ.aestronglyMeasurable.comp_fst
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => KJ ε p.1 p.2)
        ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) :=
      (continuous_KJ ε).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2 ^ 2)
        ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) :=
      hgi'.aestronglyMeasurable.comp_snd
    exact h1.mul (h2.mul h3)
  refine Integrable.mono' hdom hmeas ?_
  rw [MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.ae_restrict_of_forall_mem
    ((measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (Real.pi / 2))).prod
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (Real.pi / 2)))) ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hσnn : 0 ≤ Work.FTS.EllipticEst.thEta p.1 :=
    Work.FTS.EllipticEst.thEta_nonneg hp1
  have hKJnn : 0 ≤ KJ ε p.1 p.2 := KJ_nonneg hε p.1 p.2
  have hKJle : KJ ε p.1 p.2 ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ :=
    KJ_le hε p.1 p.2
  have hgnn : 0 ≤ g p.2 ^ 2 := sq_nonneg _
  rw [show Function.uncurry (fun θ s : ℝ =>
        Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2)) p
      = Work.FTS.EllipticEst.thEta p.1 * (KJ ε p.1 p.2 * g p.2 ^ 2) from rfl]
  rw [Real.norm_of_nonneg (mul_nonneg hσnn (mul_nonneg hKJnn hgnn))]
  calc Work.FTS.EllipticEst.thEta p.1 * (KJ ε p.1 p.2 * g p.2 ^ 2)
      ≤ Work.FTS.EllipticEst.thEta p.1
          * ((3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * g p.2 ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKJle hgnn) hσnn
    _ = (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * Work.FTS.EllipticEst.thEta p.1) * g p.2 ^ 2 := by
        ring

theorem kernelSwap {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hgi : MeasureTheory.IntegrableOn (fun s : ℝ => g s ^ 2) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
        (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * g s ^ 2))
      = ∫ s in Work.Spaces.Iθ, g s ^ 2 *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.EllPkgAux.KJ ε θ s)
    ∧ MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ *
          (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * g s ^ 2))
        Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn
        (fun s : ℝ => g s ^ 2 *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.EllPkgAux.KJ ε θ s))
        Work.Spaces.Iθ := by
  have hInt := integrable_uncurry_kernel (g := g) hε hgi
  have hswap := integral_integral_swap hInt
  -- the two one-variable factorisations of the integrand
  have keyA : ∀ θ : ℝ, (∫ s in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2))
      = Work.FTS.EllipticEst.thEta θ * ∫ s in Work.Spaces.Iθ, KJ ε θ s * g s ^ 2 :=
    fun θ => integral_const_mul _ _
  have keyB : ∀ s : ℝ, (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2))
      = g s ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * KJ ε θ s) := by
    intro s
    have h1 : (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2))
        = ∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.thEta θ * KJ ε θ s) * g s ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      ring
    rw [h1, integral_mul_const (g s ^ 2)
      (fun θ => Work.FTS.EllipticEst.thEta θ * KJ ε θ s)]
    exact mul_comm _ _
  refine ⟨?_, ?_, ?_⟩
  · calc (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
          (∫ s in Work.Spaces.Iθ, KJ ε θ s * g s ^ 2))
        = ∫ θ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          exact (keyA θ).symm
      _ = ∫ s in Work.Spaces.Iθ, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2) := hswap
      _ = ∫ s in Work.Spaces.Iθ, g s ^ 2 *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * KJ ε θ s) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          exact keyB s
  · have h := hInt.integral_prod_left
    refine h.congr (Filter.Eventually.of_forall fun θ => ?_)
    exact keyA θ
  · have h := hInt.integral_prod_right
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    exact keyB s

end Work.FTS.EllSol.EllPkgAux
