import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassCHon.sliceMass_continuous
import Submission.Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Local-in-`z` bound for the mode coefficients `cmode m F ·`

For `F` which is `C^∞` on the open quadrant, whose level-`0` `ℋ`-integrand is honest
(`HkMem α 0 F`) and whose radial derivative `z ∂_z F` is honest as well, the mode coefficients
`cmode m F t` are `O(1/√(eNorm m))` **uniformly on every compact `z`-interval**: for each `z > 0`
there is `L ≥ 0` with

  `|cmode m F t| ≤ L / √(eNorm m)`   for all `m : ℕ`, `t ∈ [z/2, 2z]`.

**Proof.** The sharp per-mode Bessel bound
`eNorm m * (cmode m F t)² ≤ ∫_θ (F t θ)² sin(2θ)^{-η}` (the sibling
`eNorm_mul_cmode_sq_le_sliceMass`) reduces everything to controlling the angular slice mass

  `mFun t := ∫_θ (F t θ)² · sEta θ`

on the interval `[z/2, 2z]`.  That slice mass is *continuous* on `(0,∞)` by
`sliceMass_continuous` (the honest radial derivative is what makes the `z`-FTC + Cauchy–Schwarz
argument work), and the interval is compact and contained in `(0,∞)` since `z > 0`; so `mFun` is
bounded there by `M := mFun x` at a point `x` where its maximum is attained.  The per-slice
integrability needed to apply the Bessel bound is `integrableOn_sq_sEta_of_HkMem`, available for
every `t > 0`.  Taking `L := √M` (nonnegative because `M` is an integral of a nonnegative
integrand) gives the claim after `√(M / eNorm m) = √M / √(eNorm m)` and `eNorm m > 0`.
-/

open MeasureTheory Set

namespace Work.FTS.ClassCHon.Hcoef

theorem cmode_slice_bound {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF0 : Work.Spaces.HkMem α 0 F)
    (hDz : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz F z θ)) :
    ∀ z : ℝ, 0 < z → ∃ L : ℝ, 0 ≤ L ∧ ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (z / 2) (2 * z) →
      |Work.FTS.PhiStar.Series.cmode m F t|
        ≤ L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
  intro z hz
  -- the angular slice mass is continuous on `(0,∞)`
  have hcont : ContinuousOn (fun t : ℝ => ∫ θ in Work.Spaces.Iθ,
      (F t θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.ClassCHon.sliceMass_continuous hsm hF0 hDz
  -- the interval `[z/2, 2z]` sits inside `(0,∞)` and is nonempty
  have hsub : Set.Icc (z / 2) (2 * z) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    simp only [Set.mem_Ioi]
    linarith [ht.1, hz]
  have hne : (Set.Icc (z / 2) (2 * z)).Nonempty :=
    ⟨z, by simp only [Set.mem_Icc]; constructor <;> linarith [hz]⟩
  -- a point where the slice mass is maximal on the interval
  obtain ⟨x, _hxmem, hxmax⟩ := isCompact_Icc.exists_isMaxOn hne (hcont.mono hsub)
  have hxmax' : ∀ y ∈ Set.Icc (z / 2) (2 * z),
      (∫ θ in Work.Spaces.Iθ, (F y θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (F x θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    isMaxOn_iff.mp hxmax
  -- `sEta` is nonnegative on the angular interval
  have hsEta_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.sEta θ := fun θ hθ => by
    simpa only [Work.FTS.EllipticEst.sEta, Work.FTS.EllipticEst.AngSecond.sig]
      using Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
  -- the maximising slice mass is nonnegative
  have hMnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (F x θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    integral_nonneg_of_ae <| by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ)
  refine ⟨Real.sqrt (∫ θ in Work.Spaces.Iθ,
      (F x θ) ^ 2 * Work.FTS.EllipticEst.sEta θ), Real.sqrt_nonneg _, ?_⟩
  intro m t ht
  have htpos : 0 < t := by
    simp only [Set.mem_Icc] at ht
    linarith [ht.1, hz]
  -- per-slice integrability of the `η`-weighted square
  have hint : IntegrableOn
      (fun θ : ℝ => (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem (F := F) hF0 htpos
  -- the sharp per-mode Bessel bound
  have hslice := Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
    (m := m) (F := F) (z := t) hint
  -- the slice mass at `t` is dominated by the maximal one at `x`
  have hbound : (∫ θ in Work.Spaces.Iθ,
        (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ ∫ θ in Work.Spaces.Iθ, (F x θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    hxmax' t ht
  have hcm2 : (Work.FTS.PhiStar.Series.cmode m F t) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F x θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        / Work.EllipticEst.ModalSolution.eNorm m := by
    rw [le_div_iff₀ (Work.EllipticEst.ModalSolution.eNorm_pos m), mul_comm]
    exact le_trans hslice hbound
  have habs := Real.abs_le_sqrt hcm2
  rwa [Real.sqrt_div hMnn] at habs

end Work.FTS.ClassCHon.Hcoef
