/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.BoxDataH.wJet_lip` — Lipschitz continuity of the first within-partials

If `F` is `C²` within the closed box `cbox a b = [a,b] × [0,π/2]` (`a < b`) and the operator norm
of its second within-derivative is bounded by `K` on the box, then the two first within-partials
`wPz`, `wPth` (the entries `iteratedFDerivWithin ℝ 1 F · p (dir1 dz)`, `… (dir1 dth)` of the
first within-derivative) are `K`-Lipschitz on the box.

This is just the two-step mean value inequality on the convex box, applied to the first
within-derivative `D := iteratedFDerivWithin ℝ 1 F (cbox a b)`, together with the norm identity
`‖fderivWithin ℝ D s x‖ = ‖iteratedFDerivWithin ℝ 2 F s x‖`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_EllLimOK.BoxDataH.WithinVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS_EllLimOK.BoxDataH

open Work.FTS_EllLimOK.BoxRegAux (dz dth dir1 prod_dir1_le_one norm_dz_le_one norm_dth_le_one)

theorem wJet_lip {a b K : ℝ} {F : ℝ × ℝ → ℝ} (hab : a < b)
    (hsm : ContDiffOn ℝ 2 F (Work.FTS_EllLimOK.cbox a b))
    (hb : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      ‖iteratedFDerivWithin ℝ 2 F (Work.FTS_EllLimOK.cbox a b) p‖ ≤ K) :
    (∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) F p
        - Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) F q| ≤ K * ‖p - q‖) ∧
    (∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) F p
        - Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) F q| ≤ K * ‖p - q‖) := by
  have hs : UniqueDiffOn ℝ (cbox a b) := uniqueDiffOn_cbox hab
  have hconv : Convex ℝ (cbox a b) := by
    rw [cbox]
    exact (convex_Icc a b).prod (convex_Icc 0 (π / 2))
  -- the first within-derivative is differentiable on the box, being `C¹` there
  have hD : DifferentiableOn ℝ (iteratedFDerivWithin ℝ 1 F (cbox a b)) (cbox a b) :=
    hsm.differentiableOn_iteratedFDerivWithin (m := 1) (by norm_num) hs
  -- its within-derivative has operator norm bounded by `K`
  have hbound : ∀ x ∈ cbox a b,
      ‖fderivWithin ℝ (iteratedFDerivWithin ℝ 1 F (cbox a b)) (cbox a b) x‖ ≤ K := by
    intro x hx
    rw [norm_fderivWithin_iteratedFDerivWithin]
    exact hb x hx
  have hmem : (a, 0) ∈ cbox a b := by
    rw [mem_cbox]
    exact ⟨⟨le_rfl, le_of_lt hab⟩, ⟨le_rfl, by positivity⟩⟩
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hb _ hmem)
  -- the componentwise Lipschitz bound for an arbitrary direction of norm `≤ 1`
  have key : ∀ (v : ℝ × ℝ), ‖v‖ ≤ 1 → ∀ p ∈ cbox a b, ∀ q ∈ cbox a b,
      |iteratedFDerivWithin ℝ 1 F (cbox a b) p (dir1 v)
        - iteratedFDerivWithin ℝ 1 F (cbox a b) q (dir1 v)| ≤ K * ‖p - q‖ := by
    intro v hv p hp q hq
    have hM : ‖iteratedFDerivWithin ℝ 1 F (cbox a b) p
        - iteratedFDerivWithin ℝ 1 F (cbox a b) q‖ ≤ K * ‖p - q‖ :=
      hconv.norm_image_sub_le_of_norm_fderivWithin_le hD hbound hq hp
    have h1 : ‖(iteratedFDerivWithin ℝ 1 F (cbox a b) p
        - iteratedFDerivWithin ℝ 1 F (cbox a b) q) (dir1 v)‖
        ≤ ‖iteratedFDerivWithin ℝ 1 F (cbox a b) p
            - iteratedFDerivWithin ℝ 1 F (cbox a b) q‖ * ∏ i : Fin 1, ‖dir1 v i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    have h2 : ∏ i : Fin 1, ‖dir1 v i‖ ≤ 1 := prod_dir1_le_one v hv
    have h4 : (0 : ℝ) ≤ ∏ i : Fin 1, ‖dir1 v i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs] at h1
    calc |iteratedFDerivWithin ℝ 1 F (cbox a b) p (dir1 v)
          - iteratedFDerivWithin ℝ 1 F (cbox a b) q (dir1 v)|
        = |(iteratedFDerivWithin ℝ 1 F (cbox a b) p
            - iteratedFDerivWithin ℝ 1 F (cbox a b) q) (dir1 v)| := rfl
      _ ≤ ‖iteratedFDerivWithin ℝ 1 F (cbox a b) p
            - iteratedFDerivWithin ℝ 1 F (cbox a b) q‖ * ∏ i : Fin 1, ‖dir1 v i‖ := h1
      _ ≤ (K * ‖p - q‖) * ∏ i : Fin 1, ‖dir1 v i‖ :=
          mul_le_mul_of_nonneg_right hM h4
      _ ≤ (K * ‖p - q‖) * 1 :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0 (norm_nonneg _))
      _ = K * ‖p - q‖ := mul_one _
  constructor
  · intro p hp q hq
    rw [wPz]
    exact key dz norm_dz_le_one p hp q hq
  · intro p hp q hq
    rw [wPth]
    exact key dth norm_dth_le_one p hp q hq

end Work.FTS_EllLimOK.BoxDataH
