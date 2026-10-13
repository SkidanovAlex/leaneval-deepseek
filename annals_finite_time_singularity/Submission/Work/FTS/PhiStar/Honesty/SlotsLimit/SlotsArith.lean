/-
# Plumbing for the two honest repairs of `slot_aPriori`

Small arithmetic facts about `HkNorm = √(HkSq)` and the linearity of `D_z` on a difference of
smooth functions, used by `slot_aPriori_of_source` / `slot_aPriori_smooth`.

* `HkNorm_sq_eq` — `HkNorm α l u ^ 2 = HkSq α l u`;
* `HkSq_le_of_HkNorm_le` — squaring a bound `HkNorm u ≤ c·HkNorm v` (`c ≥ 0`);
* `Dz_pthIter2_sub` — on the open quadrant the third slot of a difference is the `D_z` of the
  second slot of the difference: `z ∂_z∂_θθ u − z ∂_z∂_θθ v = z ∂_z(∂_θθ(u − v))`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.GalBasis.FamEAux.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false

/-- `HkNorm` is the square root of `HkSq`, so squaring inverts it. -/
theorem HkNorm_sq_eq (α : ℝ) (l : ℕ) (u : ℝ → ℝ → ℝ) :
    Work.Spaces.HkNorm α l u ^ 2 = Work.Spaces.HkSq α l u := by
  rw [Work.Spaces.HkNorm]
  exact Real.sq_sqrt (Work.Spaces.HkSq_nonneg α l u)

/-- Squaring the bound `HkNorm u ≤ c · HkNorm v` (with `c ≥ 0`). -/
theorem HkSq_le_of_HkNorm_le (α : ℝ) {l : ℕ} {u v : ℝ → ℝ → ℝ} {c : ℝ} (_hc : 0 ≤ c)
    (h : Work.Spaces.HkNorm α l u ≤ c * Work.Spaces.HkNorm α l v) :
    Work.Spaces.HkSq α l u ≤ c ^ 2 * Work.Spaces.HkSq α l v := by
  have h1 : Work.Spaces.HkNorm α l u ^ 2 ≤ (c * Work.Spaces.HkNorm α l v) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [mul_pow, HkNorm_sq_eq, HkNorm_sq_eq] at h1
  exact h1

/-- On the open quadrant, the third slot of a difference is the `D_z` of the second slot of the
difference.  (`D_z = z ∂_z`; the two `∂_z`'s are applied to functions agreeing on the open
quadrant.) -/
theorem Dz_pthIter2_sub {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.Dz (Work.Spaces.pthIter 2 u) z θ - Work.Spaces.Dz (Work.Spaces.pthIter 2 v) z θ
        = Work.Spaces.Dz (Work.Spaces.pthIter 2 (fun z θ => u z θ - v z θ)) z θ := by
  intro z θ hz hθ hθ2
  have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
  have h1 : Work.Spaces.pz (fun z θ => Work.Spaces.pthIter 2 u z θ
        - Work.Spaces.pthIter 2 v z θ) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ
        - Work.Spaces.pz (Work.Spaces.pthIter 2 v) z θ := by
    simpa only [Function.uncurry, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
      using Work.FTS.GalBasis.pzIter_sub_eqOn (V := Work.FTS.EllipticEst.Q0)
        Work.FTS.EllipticEst.isOpen_Q0 1
        ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hu 2).forall 2)
        ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hv 2).forall 2) hpt
  have h2 : Work.Spaces.pz (fun z θ => Work.Spaces.pthIter 2 u z θ
        - Work.Spaces.pthIter 2 v z θ) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 (fun z θ => u z θ - v z θ)) z θ := by
    refine Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ?_ hpt
    intro p hp
    exact (Work.FTS.GalBasis.pthIter_sub_eqOn (V := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0 2 (hu.forall 3) (hv.forall 3) hp).symm
  simp only [Work.Spaces.Dz]
  rw [← mul_sub, ← h1, h2]

end Work.FTS.PhiStar.Honesty.SlotsLimit
