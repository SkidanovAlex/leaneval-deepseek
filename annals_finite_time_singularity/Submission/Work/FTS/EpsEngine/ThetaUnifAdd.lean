/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/ThetaUnifAdd.lean`

`Work.FTS.EpsEngine.ThetaUnifAdd`: the **uniform angular flatness** `ThetaUnif α k` is
closed under addition of smooth profiles.

`ThetaUnif α k f` is the two `ε`-`δ` conditions (`UnifTraceDefs`)

  `∀ θ → 0⁺, ∀ z > 0,  sin(2θ)^{1-γ} · (D_z^b D_θ^a f z θ)² ≤ ε'`,
  `∀ θ → (π/2)⁻, ∀ z > 0,  sin(2θ)^{1-γ} · (D_z^b D_θ^a f z θ)² ≤ ε'`,

*uniform in `z`*, for every slot `a + b ≤ k`.

The only mathematical input is the **additivity of the mixed blocks**

  `D_z^b D_θ^a (f + g) = D_z^b D_θ^a f + D_z^b D_θ^a g`   on the open quadrant

(`Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn`, which uses the differentiability
supplied by the `ContDiffOn` hypotheses), together with the elementary estimate
`(A + B)² ≤ 2A² + 2B²` and the nonnegativity of `sin(2θ)^{1-γ}` for `θ ∈ (0,π/2)`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EpsEngine.UnifTraceDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The angular weight `sin(2θ)^{1-γ}` is nonnegative on the open angular interval. -/
private lemma sinTwo_rpow_nonneg {α θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi / 2) :
    0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])) _

/-- **The uniform angular flatness `ThetaUnif` is closed under addition** (of profiles smooth on
the open quadrant).  This is the `ε`-`δ` bookkeeping of the mollifier: the angular traces of a sum
are the sums of the traces, and `(A + B)² ≤ 2A² + 2B²` splits the tolerance `ε'` into the two
halves `ε'/2`. -/
theorem ThetaUnifAdd {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h1 : Work.FTS.EpsEngine.ThetaUnif α k f) (h2 : Work.FTS.EpsEngine.ThetaUnif α k g) :
    Work.FTS.EpsEngine.ThetaUnif α k (fun z θ => f z θ + g z θ) := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hFG : (fun z θ => f z θ + g z θ) = (f + g) := by
    funext z θ
    simp only [Pi.add_apply]
  rw [hFG]
  refine ⟨?_, ?_⟩
  · -- the `θ → 0⁺` end
    intro a b hab ε' hε'
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h1.t0 a b hab (ε' / 4) (by linarith)
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := h2.t0 a b hab (ε' / 4) (by linarith)
    refine ⟨min (min δ₁ δ₂) (Real.pi / 4),
      lt_min (lt_min hδ₁pos hδ₂pos) (by linarith [Real.pi_pos]), ?_⟩
    intro θ hθ hθδ z hz
    have hθπ : θ < Real.pi / 2 := by
      have h : θ < Real.pi / 4 := lt_of_lt_of_le hθδ (min_le_right _ _)
      linarith [Real.pi_pos]
    have hθ₁ : θ < δ₁ :=
      lt_of_lt_of_le hθδ (le_trans (min_le_left _ _) (min_le_left _ _))
    have hθ₂ : θ < δ₂ :=
      lt_of_lt_of_le hθδ (le_trans (min_le_left _ _) (min_le_right _ _))
    have hadd := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn hV
      (hf (a + b)) (hg (a + b)) a b le_rfl (z, θ) ⟨hz, hθ, hθπ⟩
    have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      sinTwo_rpow_nonneg hθ hθπ
    have hsq : (Work.Spaces.mixed b a (f + g) z θ) ^ 2
        ≤ 2 * (Work.Spaces.mixed b a f z θ) ^ 2
          + 2 * (Work.Spaces.mixed b a g z θ) ^ 2 := by
      rw [hadd]
      nlinarith [sq_nonneg (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a g z θ)]
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a (f + g) z θ) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (2 * (Work.Spaces.mixed b a f z θ) ^ 2
              + 2 * (Work.Spaces.mixed b a g z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hs
      _ = 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2) := by ring
      _ ≤ 2 * (ε' / 4) + 2 * (ε' / 4) := by
          linarith [hδ₁ θ hθ hθ₁ z hz, hδ₂ θ hθ hθ₂ z hz]
      _ = ε' := by ring
  · -- the `θ → (π/2)⁻` end
    intro a b hab ε' hε'
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h1.t1 a b hab (ε' / 4) (by linarith)
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := h2.t1 a b hab (ε' / 4) (by linarith)
    refine ⟨min (min δ₁ δ₂) (Real.pi / 4),
      lt_min (lt_min hδ₁pos hδ₂pos) (by linarith [Real.pi_pos]), ?_⟩
    intro θ hθπ hθδ z hz
    have hδle₁ : min (min δ₁ δ₂) (Real.pi / 4) ≤ δ₁ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hδle₂ : min (min δ₁ δ₂) (Real.pi / 4) ≤ δ₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hθ₁ : Real.pi / 2 - δ₁ < θ :=
      lt_of_le_of_lt (by linarith [hδle₁]) hθδ
    have hθ₂ : Real.pi / 2 - δ₂ < θ :=
      lt_of_le_of_lt (by linarith [hδle₂]) hθδ
    have hθpos : 0 < θ := by
      have h' : Real.pi / 2 - Real.pi / 4
          ≤ Real.pi / 2 - min (min δ₁ δ₂) (Real.pi / 4) := by
        linarith [min_le_right (min δ₁ δ₂) (Real.pi / 4)]
      linarith [Real.pi_pos]
    have hadd := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn hV
      (hf (a + b)) (hg (a + b)) a b le_rfl (z, θ) ⟨hz, hθpos, hθπ⟩
    have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      sinTwo_rpow_nonneg hθpos hθπ
    have hsq : (Work.Spaces.mixed b a (f + g) z θ) ^ 2
        ≤ 2 * (Work.Spaces.mixed b a f z θ) ^ 2
          + 2 * (Work.Spaces.mixed b a g z θ) ^ 2 := by
      rw [hadd]
      nlinarith [sq_nonneg (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a g z θ)]
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a (f + g) z θ) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (2 * (Work.Spaces.mixed b a f z θ) ^ 2
              + 2 * (Work.Spaces.mixed b a g z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hs
      _ = 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2) := by ring
      _ ≤ 2 * (ε' / 4) + 2 * (ε' / 4) := by
          linarith [hδ₁ θ hθπ hθ₁ z hz, hδ₂ θ hθπ hθ₂ z hz]
      _ = ε' := by ring

end Work.FTS.EpsEngine
