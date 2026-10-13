import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open Set

/-- The box `[a,b] × [c,d]` with `0 < a` and `0 < c ≤ d < π/2` sits inside the open
quadrant `Q0 = (0,∞) × (0,π/2)` on which `SmoothOpen` grants smoothness. -/
theorem box_subset_Q0 {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < Real.pi / 2) :
    Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  simp only [Set.mem_Icc] at hz hθ
  exact Work.FTS.EllipticEst.mem_Q0.mpr
    ⟨by linarith [hz.1], by linarith [hθ.1], by linarith [hθ.2]⟩

/-- **The `ℋ^k`-integrand is bounded on a compact box contained in the open quadrant.**
`Work.Spaces.HkIntegrand α k G` is a finite sum of squares of weighted derivatives
(`D_z^i G · w/sin(2θ)^{η/2}` and `D_z^jD_θ^i G · W`), all of which are continuous on `Q0`
when `SmoothOpen G`; the weights are continuous and non-singular on the box because the box
stays away from `z = 0` and from `θ = 0, π/2`. -/
theorem hkIntegrand_bound_on_box {α : ℝ} {G : ℝ → ℝ → ℝ} {k : ℕ} {a b c d : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) (hd : d < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z θ : ℝ, z ∈ Set.Icc a b → θ ∈ Set.Icc c d →
      Work.Spaces.HkIntegrand α k G z θ ≤ C := by
  have hsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 :=
    box_subset_Q0 ha hc hd
  have hcomp : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k G p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (hsm.continuousOn_HkIntegrand α k).mono hsub
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
  have hpt : ((a, c) : ℝ × ℝ) ∈ Set.Icc a b ×ˢ Set.Icc c d :=
    ⟨⟨le_refl a, hab⟩, ⟨le_refl c, hcd⟩⟩
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC _ hpt)
  refine ⟨C, hCnn, fun z θ hz hθ => ?_⟩
  have hb := hC (z, θ) ⟨hz, hθ⟩
  rw [Real.norm_eq_abs] at hb
  exact le_trans (le_abs_self _) hb

end Work.FTS.PhiStar.Honesty
