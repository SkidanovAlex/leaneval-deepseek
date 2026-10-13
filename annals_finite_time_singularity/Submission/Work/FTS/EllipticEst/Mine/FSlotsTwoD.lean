/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Mine.FSlotsTwoD`: the two angular slots of level `2`

For `1 ≤ γ ≤ 3/2` and any `F` with `HkMem α 2 F`, the two *plain* angular slots of
level `2`,
`w²·∫_θ (∂_θ²F)² sin(2θ)^{4-γ}`  and  `w²·∫_θ (∂_θF)² sin(2θ)^{2-γ}`,
are bounded by a universal multiple of `HkSq α 2 F`.

The two mixed slots `(D_θF·W)²` and `(D_θ²F·W)²` of the integrand of `HkSq` already
control them: `D_θ = sin(2θ)·∂_θ` supplies the missing powers of `sin(2θ)`, and the
hypothesis `γ ≤ gam α` together with `sin(2θ) ≤ 1` on `Iθ` says that *increasing* the
exponent of the angular weight only makes the slot smaller, so the slot at exponent
`γ` is bounded by the slot at exponent `gam α` (which is the one occurring in `HkSq`).

Concretely, on `Iθ` (with `s = sin(2θ)`, `g = gam α`, `A = D_θ²F`, `P₁ = D_θF`):

* `w²((∂_θF)² s^{2-γ}) ≤ w²((∂_θF)² s^{2-g}) = (D_θF·W)²`;
* `w²((∂_θ²F)² s^{4-γ}) ≤ w²((∂_θ²F)² s^{4-g}) = (s²∂_θ²F)²·W²`
  and, where `∂_θF` is differentiable, the product rule `A = 2 s cos(2θ) P₁ + s² ∂_θ²F`
  gives `(s²∂_θ²F)² ≤ 2A² + 8(s P₁)²`, hence the bound `2(D_θ²F·W)² + 8(D_θF·W)²`.

The remaining point (and the only place where the junk values of `deriv` are used) is
that when `∂_θF` is *not* differentiable at `θ` the Lean value of `pthIter 2 F z θ` is
`0`, so the trivial bound `0 ≤ …` applies.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false

/-! ## Elementary facts about the angular weights -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem gam_pos_of_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

theorem sig2_nonneg_of_mem_Iθ {γ θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig2 γ θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

theorem sig4_nonneg_of_mem_Iθ {γ θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig4 γ θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- The square of the angular weight `W = w·sin(2θ)^{-γ/2}` of `HkSq`. -/
theorem Wt_sq (α z θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hg : Work.Spaces.gam α ≠ 0 := ne_of_gt (gam_pos_of_pos hα)
  have hne : -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2) ≠ 0 := fun h => hg (by linarith)
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  congr 1
  rw [sq, ← Real.rpow_add' hs hne]
  congr 1
  ring

/-! ## The two pointwise slot bounds on `Iθ` -/

theorem sig2_slot_pointwise (α : ℝ) (hα : 0 < α) (γ : ℝ) (hγ2 : γ ≤ 3 / 2)
    (hγg : γ ≤ Work.Spaces.gam α) (F : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth F z θ) ^ 2 * sig2 γ θ)
      ≤ Work.Spaces.HkIntegrand α 2 F z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hkI : 0 ≤ Work.Spaces.HkIntegrand α 2 F z θ :=
    Work.Spaces.HkIntegrand_nonneg α 2 F z θ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · have h2γ : (2 : ℝ) - γ ≠ 0 := by linarith
    have hz : sig2 γ θ = 0 := by rw [sig2, ← hs0]; exact Real.zero_rpow h2γ
    simp only [hz, mul_zero]
    linarith [hkI]
  · have hexp : sig2 γ θ ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
      show (Real.sin (2 * θ)) ^ (2 - γ) ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      exact Real.rpow_le_rpow_of_exponent_ge hspos hs1 (by linarith)
    have hstep : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth F z θ) ^ 2 * sig2 γ θ)
        ≤ (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (sq_nonneg _)) (sq_nonneg _)
    have hsp : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      have h : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          = (Real.sin (2 * θ)) ^ (2 : ℝ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        have h2 := Real.rpow_add hspos (2 : ℝ) (-(Work.Spaces.gam α))
        rw [show (2 : ℝ) + -(Work.Spaces.gam α) = 2 - Work.Spaces.gam α by ring] at h2
        exact h2
      simpa using h
    have halg : (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        = (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hsp, mul_pow, Wt_sq α z θ hα hθ]
      ring
    have hslot : (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 2 F z θ := by
      have h := Work.Spaces.sq_le_HkIntegrand_mixed α 2 F z θ 1 0 (by norm_num) (by norm_num)
      exact h
    calc (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth F z θ) ^ 2 * sig2 γ θ)
        ≤ (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := hstep
      _ = (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := halg
      _ ≤ Work.Spaces.HkIntegrand α 2 F z θ := hslot

theorem sig4_slot_pointwise (α : ℝ) (hα : 0 < α) (γ : ℝ) (hγ2 : γ ≤ 3 / 2)
    (hγg : γ ≤ Work.Spaces.gam α) (F : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 *
        ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2 * sig4 γ θ)
      ≤ 10 * Work.Spaces.HkIntegrand α 2 F z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hkI : 0 ≤ Work.Spaces.HkIntegrand α 2 F z θ :=
    Work.Spaces.HkIntegrand_nonneg α 2 F z θ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · have h4γ : (4 : ℝ) - γ ≠ 0 := by linarith
    have hz : sig4 γ θ = 0 := by rw [sig4, ← hs0]; exact Real.zero_rpow h4γ
    simp only [hz, mul_zero]
    linarith [hkI]
  · have hexp : sig4 γ θ ≤ (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
      show (Real.sin (2 * θ)) ^ (4 - γ) ≤ (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
      exact Real.rpow_le_rpow_of_exponent_ge hspos hs1 (by linarith)
    have hstep : (Work.Spaces.w z) ^ 2 *
          ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2 * sig4 γ θ)
        ≤ (Work.Spaces.w z) ^ 2 *
          ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (sq_nonneg _)) (sq_nonneg _)
    have hsp : (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
        = (Real.sin (2 * θ)) ^ 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      have h : (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
          = (Real.sin (2 * θ)) ^ (4 : ℝ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        have h2 := Real.rpow_add hspos (4 : ℝ) (-(Work.Spaces.gam α))
        rw [show (4 : ℝ) + -(Work.Spaces.gam α) = 4 - Work.Spaces.gam α by ring] at h2
        exact h2
      simpa using h
    have halg : (Work.Spaces.w z) ^ 2 *
          ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α))
        = (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hsp, Wt_sq α z θ hα hθ]
      ring
    have hslot1 : (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 2 F z θ := by
      have h := Work.Spaces.sq_le_HkIntegrand_mixed α 2 F z θ 1 0 (by norm_num) (by norm_num)
      exact h
    have hslot2 : (Work.Spaces.DthIter 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 2 F z θ := by
      have h := Work.Spaces.sq_le_HkIntegrand_mixed α 2 F z θ 2 0 (by norm_num) (by norm_num)
      exact h
    have hmain : (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
          * (Work.Spaces.Wt α z θ) ^ 2
        ≤ 2 * (Work.Spaces.DthIter 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
          + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      by_cases hd : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pth F z t) θ
      · have hderiv : deriv (fun t : ℝ => Real.sin (2 * t) * Work.Spaces.pth F z t) θ
            = 2 * Real.cos (2 * θ) * Work.Spaces.pth F z θ
              + Real.sin (2 * θ) * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ := by
          have h1 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
            simpa [Function.comp_def, mul_comm] using
              (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
          have hd' : HasDerivAt (fun t : ℝ => Work.Spaces.pth F z t)
              (deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) θ := hd.hasDerivAt
          exact (h1.mul hd').deriv
        have hArec : Work.Spaces.DthIter 2 F z θ
            = 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pth F z θ
              + Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ := by
          have h0 : Work.Spaces.DthIter 2 F z θ
              = Real.sin (2 * θ)
                * deriv (fun t : ℝ => Real.sin (2 * t) * Work.Spaces.pth F z t) θ := rfl
          rw [h0, hderiv]
          ring
        have hs2p2 : Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ
            = Work.Spaces.DthIter 2 F z θ
              - 2 * Real.sin (2 * θ) * (Real.cos (2 * θ) * Work.Spaces.pth F z θ) := by
          rw [hArec]; ring
        have hkey : (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            ≤ 2 * (Work.Spaces.DthIter 2 F z θ) ^ 2
              + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2 := by
          have hA2 : (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
              ≤ 2 * (Work.Spaces.DthIter 2 F z θ) ^ 2
                + 2 * (2 * Real.sin (2 * θ)
                    * (Real.cos (2 * θ) * Work.Spaces.pth F z θ)) ^ 2 := by
            rw [hs2p2]
            nlinarith [sq_nonneg (Work.Spaces.DthIter 2 F z θ
              + 2 * Real.sin (2 * θ) * (Real.cos (2 * θ) * Work.Spaces.pth F z θ))]
          have hB2 : 2 * (2 * Real.sin (2 * θ)
                * (Real.cos (2 * θ) * Work.Spaces.pth F z θ)) ^ 2
              ≤ 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2 := by
            have hc : (Real.cos (2 * θ)) ^ 2 ≤ 1 := Real.cos_sq_le_one (2 * θ)
            have hsp1 : 0 ≤ (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2 := sq_nonneg _
            have hprod : (Real.cos (2 * θ)) ^ 2
                  * (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2
                ≤ (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2 := by
              simpa using mul_le_mul_of_nonneg_right hc hsp1
            nlinarith [hprod]
          linarith [hA2, hB2]
        calc (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
              * (Work.Spaces.Wt α z θ) ^ 2
            ≤ (2 * (Work.Spaces.DthIter 2 F z θ) ^ 2
                + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2)
              * (Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
          _ = 2 * (Work.Spaces.DthIter 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
              + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
              ring
      · have hp2 : deriv (fun t : ℝ => Work.Spaces.pth F z t) θ = 0 :=
          deriv_zero_of_not_differentiableAt hd
        have hzero : (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Work.Spaces.Wt α z θ) ^ 2 = 0 := by rw [hp2]; ring
        rw [hzero]
        have hnn : (0 : ℝ) ≤ 2 * (Work.Spaces.DthIter 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
            + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          positivity
        linarith [hnn]
    calc (Work.Spaces.w z) ^ 2 *
          ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2 * sig4 γ θ)
        ≤ (Work.Spaces.w z) ^ 2 *
          ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) := hstep
      _ = (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Work.Spaces.Wt α z θ) ^ 2 := halg
      _ ≤ 2 * (Work.Spaces.DthIter 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
          + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := hmain
      _ ≤ 2 * Work.Spaces.HkIntegrand α 2 F z θ + 8 * Work.Spaces.HkIntegrand α 2 F z θ := by
          linarith [hslot1, hslot2]
      _ = 10 * Work.Spaces.HkIntegrand α 2 F z θ := by ring

/-! ## The two-dimensional statement -/

theorem FSlotsTwoD (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α →
      γ ≤ Work.Spaces.gam α →
      Work.Spaces.HkMem α 2 F →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 F z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig4 γ θ))
        + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 F z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig2 γ θ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  refine ⟨11, by norm_num, ?_⟩
  intro α F hα hγg hmem
  show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2 *
            sig4 γ θ))
        + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth F z θ) ^ 2 * sig2 γ θ))
        ≤ 11 * Work.Spaces.HkSq α 2 F
  have hθmem : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hzmem : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hB : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth F z θ) ^ 2 * sig2 γ θ))
      ≤ Work.Spaces.HkSq α 2 F := by
    have hpt : ∀ z ∈ Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth F z θ) ^ 2 * sig2 γ θ)
          ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F z θ := by
      intro z hz
      rw [(MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
        (fun θ => (Work.Spaces.pth F z θ) ^ 2 * sig2 γ θ)).symm]
      exact MeasureTheory.integral_mono_of_nonneg
        (by filter_upwards [ae_restrict_mem hθmem] with θ hθ
            exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sig2_nonneg_of_mem_Iθ hθ)))
        (hmem.1 z hz)
        (by filter_upwards [ae_restrict_mem hθmem] with θ hθ
            exact sig2_slot_pointwise α hα γ hγ2 hγg F z θ hθ)
    calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth F z θ) ^ 2 * sig2 γ θ))
        ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F z θ :=
          MeasureTheory.integral_mono_of_nonneg
            (by filter_upwards [ae_restrict_mem hzmem] with z hz
                exact mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
                  (by filter_upwards [ae_restrict_mem hθmem] with θ hθ
                      exact mul_nonneg (sq_nonneg _) (sig2_nonneg_of_mem_Iθ hθ))))
            hmem.2
            (ae_restrict_of_forall_mem hzmem hpt)
      _ = Work.Spaces.HkSq α 2 F := rfl
  have hA : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2 *
          sig4 γ θ))
      ≤ 10 * Work.Spaces.HkSq α 2 F := by
    have hpt : ∀ z ∈ Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2 * sig4 γ θ)
          ≤ 10 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F z θ) := by
      intro z hz
      rw [(MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
            (fun θ => (deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2 * sig4 γ θ)).symm,
          (MeasureTheory.integral_const_mul (10 : ℝ)
            (fun θ => Work.Spaces.HkIntegrand α 2 F z θ)).symm]
      exact MeasureTheory.integral_mono_of_nonneg
        (by filter_upwards [ae_restrict_mem hθmem] with θ hθ
            exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sig4_nonneg_of_mem_Iθ hθ)))
        ((hmem.1 z hz).const_mul 10)
        (by filter_upwards [ae_restrict_mem hθmem] with θ hθ
            exact sig4_slot_pointwise α hα γ hγ2 hγg F z θ hθ)
    calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2 * sig4 γ θ))
        ≤ ∫ z in Work.Spaces.Iz,
            10 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F z θ) :=
          MeasureTheory.integral_mono_of_nonneg
            (by filter_upwards [ae_restrict_mem hzmem] with z hz
                exact mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
                  (by filter_upwards [ae_restrict_mem hθmem] with θ hθ
                      exact mul_nonneg (sq_nonneg _) (sig4_nonneg_of_mem_Iθ hθ))))
            (hmem.2.const_mul 10)
            (ae_restrict_of_forall_mem hzmem hpt)
      _ = 10 * Work.Spaces.HkSq α 2 F := by
          rw [Work.Spaces.HkSq, MeasureTheory.integral_const_mul]
  linarith [hA, hB]

end Work.FTS.EllipticEst.Mine
